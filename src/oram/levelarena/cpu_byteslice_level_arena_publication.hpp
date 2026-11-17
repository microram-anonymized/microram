#pragma once

// PUBLICATION: how a finished table becomes probeable, and when the buffer it
// replaced may be written again.  DESIGN.md "Publication, readers and
// progress" summarizes the protocol; this header states its invariants and
// the arguments for them.
//
// A publication is ONE TRANSACTION over the live set: it removes the sources
// the completed operation consumed and adds the table it produced, in a single
// immutable plan that replaces the previous one with one atomic store.  There
// is never a plan in which the sources are gone and the output is not yet
// there, which is what keeps a key from being briefly invisible.
//
// THE LIVE SET IS THE TRUTH, AND THE PLAN IS ITS PICTURE.  A delta is applied
// to `live_` under the mutex and the plan is composed from the RESULT, never
// from a snapshot the caller took before it started work: two owners finishing
// independently must both land, and the second must see the first.  That is
// why a removal names an IMMUTABLE IDENTITY -- a table id and the slot
// occupancy it was published from -- rather than a position in some plan the
// caller once read.  A removal that does not match the live set is
// refused before anything is installed.
//
// WHAT MAY NOT BE PUBLISHED, and why the refusals are here.  A plan is the
// object the request thread probes without a lock, so every invariant it
// relies on has to be established BEFORE the store and never after:
//
//   - the live windows are a laminar family, in probe order (PlanWindowsLaminar);
//   - at most one member of a nonce family is live, so no key is ever really
//     probed twice under one nonce (PlanHasAtMostOneMemberPerFamily);
//   - a mixed-radix table's public shape is r << index_bits buckets;
//   - the plan fits the reserved scratch, so no reader can outgrow it.
//
// THE EPOCH PROTOCOL is spelled out in exactly one place, Commit():
// seq_cst store of the new plan, then seq_cst sample of the reader epoch, then
// `e + (e & 1)` stamped on the old plan and on everything the delta removed.
// Reclamation compares against an OBSERVED epoch, never against this
// threshold and never against a publication count -- the two accessors of
// ReaderEpoch are named apart for that reason.
//
// THE POOL IS BOUNDED, AND THE BOUND IS AN ARGUMENT.  A plan record is
// recycled, not allocated, so the pool has to be big enough that an owner can
// always publish:
//
//     records = physical slots + dense prefix slots + current + staging
//
// Publication k installs plan k and retires plan k-1 with threshold t.  It
// also retires AT LEAST ONE physical slot -- an arena slot or a dense prefix
// slot -- with the same threshold t, and no other publication retires that
// same occupancy.  That does not pair every pending plan with a pending slot:
// plans and slots are reclaimed by different calls, each with its own sample
// of the reader epoch (an owner's poll reclaims plans first, its levels'
// drains reclaim slots later), so a slot can be freed, leased and retired
// again while the plan retired with its previous occupancy still waits.  The
// bound comes from counting publications instead:
//
//   - a plan whose threshold the epoch has not reached was retired inside
//     the open reader epoch.  Each such publication retired a different
//     slot, because a slot retired against the open epoch comes back only
//     after the reader leaves it.  So they are at most what the levels can
//     retire in one epoch: about two per level above the first (one per
//     inbox carry) and one per dense prefix slot at level one;
//   - a plan whose threshold has been reached waits only for the next
//     ReclaimPlans, which every owner poll and every inline sweep runs
//     before it steps a level, so about one more per level is pending.
//
// That is about 3L + q records, inside the physical slots plus the staging
// records, with the current plan on top.  The count has slack, but it is an
// argument and not a checked invariant: an owner that finds no free record
// parks on kPlanRecords (CanPublish), and Publish's locked check throws
// rather than overrun the pool.
//
// The premise of that argument is load bearing, so it is CHECKED: a
// publication that removes nothing is refused unless it is the first one
// (initialization, which has no plan to retire either).  Without the check the
// bound would silently be a statement about the deltas somebody happened to
// write.
//
// WHAT IS NOT HERE.  Who may retire which slot: a slot's lifecycle belongs to
// its arena and its recipient (cpu_byteslice_level_arena_slots.hpp), and this
// class only hands back the threshold to stamp.  A publisher may update the
// global plan under its mutex; it may not reclaim another owner's slots there.

#include <algorithm>
#include <atomic>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <mutex>
#include <stdexcept>
#include <string>
#include <vector>

#ifdef MICRORAM_BYTESLICE_PROBE_AUDIT
#include <set>
#include <unordered_map>
#endif

#include "src/oram/table/cpu_byteslice_probe_plan.hpp"
#include "src/core/release_guard.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_epoch.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_family.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_slots.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/table/cpu_byteslice_stored_key.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

// ---------------------------------------------------------------------------
// PublishedTable
// ---------------------------------------------------------------------------
//
// One live hashed table AND its second tier, as the engine knows it: the
// public identity the probe plan needs, plus the physical occupancy the owner
// has to retire when this table leaves.  Immutable from the moment it is
// published until its last reader is gone.
//
// The storage pointers are captured at publication and never re-resolved: the
// arena's accessors ask a slot's lifecycle state, and a plan entry outlives
// the state it was published under -- a retired table is still probed by
// whoever snapshotted the plan that names it.
struct PublishedTable {
  uint64_t table_id = 0;       // unique over the run; never reused
  uint64_t tier_table_id = 0;  // the tier's own, in the same sequence
  Family family;               // the nonce coordinate (canonical family)
  uint64_t family_id = 0;      // FamilyId(family), or the empty top's
  uint64_t window_begin = 0;   // half-open, in ACCESS POSITIONS
  uint64_t window_end = 0;

  // The occupancy this table lives in.  `owner` is the level whose arena holds
  // the slot, which is the level that will retire it -- the producer at
  // `owner - 1` wrote it, but it never owned it.
  unsigned owner = 0;
  unsigned slot = kNoSlot;
  uint64_t generation = 0;

  // Public geometry, in the probe plan's own terms: `r << index_bits` buckets.
  size_t main_buckets = 0;
  unsigned index_bits = 0;
  unsigned radix = 1;

  RebuildNonce nonce;

  // Captured storage.  `tier_*` is the slot's tier stash as the cascade scans
  // it -- built from the stash, whose inline occupancy array IS the tier's
  // mask (see LevelArena::PublishedTierTable).
  uint8_t* data = nullptr;
  uint64_t* masks = nullptr;
  uint8_t* tier_data = nullptr;
  uint64_t* tier_masks = nullptr;
  size_t tier_buckets = 0;

  bool valid() const { return table_id != 0; }
};

// ---------------------------------------------------------------------------
// PublicationDelta
// ---------------------------------------------------------------------------
//
// What one completed operation changes.  Fixed-size, because the publication
// path may not allocate: the widest delta in this design removes two sources
// (an older partial and a consumed carry, or the top's A and its carry) and
// adds one table.
//
// `consume_prefixes` is the DENSE PREFIX VISIBILITY UPDATE: level 1's
// publication is what takes its source prefix out of the probe cascade, and it
// does so by raising the plan's consumption mark, not by removing an entry the
// request thread owns.  It is a removal for every purpose the pool bound cares
// about, which is why it counts below.
struct PublicationDelta {
  static constexpr size_t kMaxRemovals = 2;
  static constexpr size_t kMaxAdditions = 1;

  uint64_t remove[kMaxRemovals] = {0, 0};  // table ids
  size_t removals = 0;
  PublishedTable add[kMaxAdditions];
  size_t additions = 0;
  // The number of complete dense prefixes whose hashed replacement is now
  // published.  Monotone; 0 means "unchanged" only because prefix 0 is the
  // state a fresh engine starts in.
  uint64_t prefixes_consumed = 0;
  bool consume_prefixes = false;

  void Remove(uint64_t table_id) {
    if (removals == kMaxRemovals) {
      throw std::logic_error(
          "level arena: a publication removes at most two sources");
    }
    remove[removals++] = table_id;
  }
  void Add(const PublishedTable& table) {
    if (additions == kMaxAdditions) {
      throw std::logic_error(
          "level arena: a publication adds at most one table");
    }
    add[additions++] = table;
  }
  void ConsumePrefixes(uint64_t through) {
    prefixes_consumed = through;
    consume_prefixes = true;
  }
  // Whether this delta takes something out of the plan, which is what the
  // pool bound's argument needs of every publication but the first.
  bool retires_something() const { return removals != 0 || consume_prefixes; }
};

// ---------------------------------------------------------------------------
// The probe audit's family bookkeeping
// ---------------------------------------------------------------------------
//
// The security invariant is "at most one REAL probe per (nonce family, key)"
// over a family's whole life, and a family here outlives any one of its
// tables: a full carry is published by its producer, adopted by its consumer
// and folded into that consumer's own full table, all under one nonce.  So the
// state is refcounted by family and only the LAST member's retirement clears
// it -- and a member is ADDED before the one it replaces is dropped, so a
// same-family swap never passes through a count of zero.
//
// Compiled out entirely without MICRORAM_BYTESLICE_PROBE_AUDIT; every test
// that publishes tables should define it, so the invariant is checked.
class ProbeFamilyAudit {
 public:
  static constexpr bool Enabled() {
#ifdef MICRORAM_BYTESLICE_PROBE_AUDIT
    return true;
#else
    return false;
#endif
  }

  void AddMember(uint64_t family_id) {
#ifdef MICRORAM_BYTESLICE_PROBE_AUDIT
    std::lock_guard<std::mutex> lock(mutex_);
    ++live_[family_id];
#else
    (void)family_id;
#endif
  }

  void DropMember(uint64_t family_id) {
#ifdef MICRORAM_BYTESLICE_PROBE_AUDIT
    std::lock_guard<std::mutex> lock(mutex_);
    const auto it = live_.find(family_id);
    if (it == live_.end()) return;
    if (--it->second == 0) {
      live_.erase(it);
      probed_.erase(family_id);
    }
#else
    (void)family_id;
#endif
  }

  // One real probe of `key` in `family_id`.  A repeat is the violation.
  void RecordRealProbe(uint64_t family_id, KeyWords key) {
#ifdef MICRORAM_BYTESLICE_PROBE_AUDIT
    std::lock_guard<std::mutex> lock(mutex_);
    ++real_probes_;
    if (!probed_[family_id].insert(key).second) ++violations_;
#else
    (void)family_id;
    (void)key;
#endif
  }

  uint64_t violations() const {
#ifdef MICRORAM_BYTESLICE_PROBE_AUDIT
    std::lock_guard<std::mutex> lock(mutex_);
    return violations_;
#else
    return 0;
#endif
  }
  uint64_t real_probes() const {
#ifdef MICRORAM_BYTESLICE_PROBE_AUDIT
    std::lock_guard<std::mutex> lock(mutex_);
    return real_probes_;
#else
    return 0;
#endif
  }

 private:
#ifdef MICRORAM_BYTESLICE_PROBE_AUDIT
  mutable std::mutex mutex_;
  std::unordered_map<uint64_t, uint64_t> live_;
  std::unordered_map<uint64_t, std::set<KeyWords>> probed_;
  uint64_t violations_ = 0;
  uint64_t real_probes_ = 0;
#endif
};

// ---------------------------------------------------------------------------
// LevelArenaPublisher
// ---------------------------------------------------------------------------

class LevelArenaPublisher {
 public:
  // `prefix_slots` is the reserved dense-prefix half of every plan -- the
  // entries the REQUEST thread writes (ProbePlan).  `arena_slots` and
  // `dense_slots` are the two halves of the "physical slots" the pool bound
  // above is stated over: every arena slot, and every dense prefix slot.
  struct Config {
    size_t prefix_slots = 0;
    size_t arena_slots = 0;
    size_t dense_slots = 0;
    // One staging record per owner thread.  The inline executor (the
    // requester driving rebuilds at flush boundaries) has one; grouped owner
    // threads have one each.
    size_t owner_threads = 1;
  };

  explicit LevelArenaPublisher(const Config& config) : config_(config) {
    if (config_.prefix_slots == 0) {
      throw std::invalid_argument(
          "level arena: a plan reserves at least the current dense unit");
    }
    // A live hashed table occupies a distinct physical slot, and contributes
    // its main and its tier to the plan, so this is exact rather than
    // generous.
    max_tables_ = MaxTablesFor(config_);
    pool_slots_ = PoolSlotsFor(config_);
    free_.reserve(pool_slots_);
    for (size_t i = 0; i < pool_slots_; ++i) {
      free_.push_back(MakePlan());
    }
    free_count_.store(free_.size(), std::memory_order_relaxed);
    live_.reserve(config_.arena_slots);
    retired_.reserve(pool_slots_);
    bytes_.AddPlain(ByteRole::kPlans, PlanRecordBytes(max_tables_),
                    pool_slots_);
    bytes_.AddPlain(ByteRole::kPlans,
                    pool_slots_ * sizeof(std::unique_ptr<ProbePlan>));
    bytes_.AddPlain(ByteRole::kBookkeeping,
                    config_.arena_slots * sizeof(PublishedTable));
    bytes_.AddPlain(ByteRole::kBookkeeping, pool_slots_ * sizeof(RetiredPlan));
    ExpectPredictedBytes(bytes_, Bytes(config_), "the probe-plan pool");
  }

  // THE LONGEST CASCADE this hierarchy can present: the reserved dense
  // prefix, plus a main and a tier for every physical arena slot.  Exact
  // rather than generous -- a live hashed table occupies a distinct slot --
  // and it is what every plan record is sized for.
  static size_t MaxTablesFor(const Config& config) {
    return config.prefix_slots + 2 * config.arena_slots;
  }

  // The plan-record pool: one record per physical slot that a publication can
  // retire, one per dense prefix slot, the current plan, and one staging
  // record per publishing thread.  The bound's argument is in the class
  // comment above; this is its one spelling.
  static size_t PoolSlotsFor(const Config& config) {
    return config.arena_slots + config.dense_slots + 1 /*current*/ +
           config.owner_threads;
  }

  // What the pool costs.  Every record is reserved at the longest cascade, so
  // this is a fixed cost of the hierarchy and not a function of how many
  // tables happen to be live.  Mirrors the constructor and is checked against
  // it there.
  static LevelArenaByteBill Bytes(const Config& config) {
    const size_t pool_slots = PoolSlotsFor(config);
    LevelArenaByteBill bill;
    bill.AddPlain(ByteRole::kPlans, PlanRecordBytes(MaxTablesFor(config)),
                  pool_slots);
    bill.AddPlain(ByteRole::kPlans,
                  pool_slots * sizeof(std::unique_ptr<ProbePlan>));
    bill.AddPlain(ByteRole::kBookkeeping,
                  config.arena_slots * sizeof(PublishedTable));
    bill.AddPlain(ByteRole::kBookkeeping, pool_slots * sizeof(RetiredPlan));
    return bill;
  }

  const LevelArenaByteBill& bytes() const { return bytes_; }

  LevelArenaPublisher(const LevelArenaPublisher&) = delete;
  LevelArenaPublisher& operator=(const LevelArenaPublisher&) = delete;

  // ---- the reader's side --------------------------------------------------

  ReaderEpoch& epoch() { return epoch_; }
  const ReaderEpoch& epoch() const { return epoch_; }
  ProbeFamilyAudit& audit() { return audit_; }
  const ProbeFamilyAudit& audit() const { return audit_; }

  // The plan this access probes.  Loaded with seq_cst INSIDE the reader epoch,
  // which is the reader's half of the Dekker pair in
  // cpu_byteslice_level_arena_epoch.hpp; a load outside it may name a plan
  // that is already being recycled.
  ProbePlan* CurrentPlan() const {
    return plan_.load(std::memory_order_seq_cst);
  }

  size_t prefix_slots() const { return config_.prefix_slots; }
  size_t max_tables() const { return max_tables_; }
  size_t pool_slots() const { return pool_slots_; }

  // ---- the owner's side ---------------------------------------------------

  // Whether a plan record is available, which is the one fallible resource a
  // publication needs and cannot wait for inside the mutex: pool exhaustion
  // parks an owner outside the mutex.  An owner asks this BEFORE
  // it commits to publishing and reports a blocked reason otherwise.
  //
  // It reads the relaxed mirror, not `free_`, so a publication takes the
  // mutex once.  A locked read would be a snapshot too -- another owner could publish between it and this
  // owner's Publish -- so a stale mirror adds no case a locked read would
  // not have.  What keeps that case out of reach is the pool bound (see the
  // header): the plans that can be pending are counted to stay below the
  // pool by at least the staging records, one per owner thread.  The count
  // is argued, not checked.  A stale ZERO is one more poll of kPlanRecords; a
  // stale nonzero, were the count ever exceeded, reaches Publish's own locked
  // check and throws.
  bool CanPublish() const {
    return free_count_.load(std::memory_order_relaxed) != 0;
  }

  size_t free_records() const {
    std::lock_guard<std::mutex> lock(mutex_);
    return free_.size();
  }
  size_t retired_records() const {
    std::lock_guard<std::mutex> lock(mutex_);
    return retired_.size();
  }
  uint64_t publications() const {
    std::lock_guard<std::mutex> lock(mutex_);
    return publications_;
  }
  uint64_t prefixes_consumed() const {
    std::lock_guard<std::mutex> lock(mutex_);
    return prefixes_consumed_;
  }

  // Two table identities, main and tier, from the one never-reused sequence.
  // Taken BEFORE a publication commits, like every other piece of its
  // bookkeeping.  Lock-free: nothing orders identities against publications
  // (nothing compares them but for equality), and the one check that reads
  // the counter -- ValidateAdditionLocked's "never allocated" -- runs on the
  // thread that allocated, after its own increment.
  void AllocateTableIds(uint64_t* main_id, uint64_t* tier_id) {
    uint64_t next = next_table_id_.load(std::memory_order_relaxed);
    do {
      // Bit 63 belongs to dense-table IDs. Reserve the whole pair before
      // changing the counter, keeping both domains disjoint at exhaustion.
      if (next > (uint64_t{1} << 63) - 2) {
        throw std::runtime_error(
            "level arena: table identities exhausted; refusing to reuse one");
      }
    } while (!next_table_id_.compare_exchange_weak(
        next, next + 2, std::memory_order_relaxed));
    *main_id = next;
    *tier_id = next + 1;
  }

  // APPLY ONE COMPLETED OPERATION.  Returns the retirement threshold to stamp
  // on every slot the delta removed -- `e + (e & 1)` sampled after the
  // installing store (the epoch protocol in the header).
  //
  // Everything that can refuse happens before the store: the record is taken,
  // the removals are matched against the LATEST live set, the composed plan is
  // validated and the retirement record's room is reserved.  After the store
  // nothing throws, because after it there is nothing to roll back to -- the
  // table is probeable and its sources are gone from the cascade.
  uint64_t Publish(const PublicationDelta& delta) {
    std::lock_guard<std::mutex> lock(mutex_);
    FreeCountSync sync{this};
    if (free_.empty()) {
      throw std::logic_error(
          "level arena: no plan record; an owner must park outside the "
          "publication mutex until reclamation returns one");
    }
    // THE POOL BOUND'S PREMISE, checked rather than assumed (see the header).
    // The first publication has no plan to retire, so it is the one that may
    // add without removing -- which is exactly initialization.
    if (!delta.retires_something() && current_ != nullptr) {
      throw std::logic_error(
          "level arena: an add-only publication retires no slot, so it is not "
          "covered by the plan-record bound");
    }
    if (delta.consume_prefixes) {
      if (delta.prefixes_consumed < prefixes_consumed_) {
        throw std::logic_error(
            "level arena: the dense consumption mark may not go backwards");
      }
      if (delta.prefixes_consumed == prefixes_consumed_ &&
          delta.removals == 0) {
        throw std::logic_error(
            "level arena: this publication consumes no prefix and removes no "
            "source");
      }
    }
    // Removals are validated against the live set as it is NOW, so two
    // independently completed deltas cannot lose one another.
    size_t index[PublicationDelta::kMaxRemovals];
    for (size_t i = 0; i < delta.removals; ++i) {
      index[i] = FindLiveLocked(delta.remove[i]);
      for (size_t j = 0; j < i; ++j) {
        if (index[j] == index[i]) {
          throw std::logic_error(
              "level arena: a publication removes one table twice");
        }
      }
    }
    // Descending, so that erasing one cannot move a member a later removal
    // still names by position.
    for (size_t i = 0; i < delta.removals; ++i) {
      for (size_t j = i + 1; j < delta.removals; ++j) {
        if (index[j] > index[i]) std::swap(index[i], index[j]);
      }
    }
    for (size_t i = 0; i < delta.additions; ++i) {
      ValidateAdditionLocked(delta.add[i], index, delta.removals);
    }

    // Apply to the live set: removals first, then the additions at the end,
    // which is the order RollbackLocked walks back.
    for (size_t i = 0; i < delta.removals; ++i) {
      removed_[i] = live_[index[i]];
      live_.erase(live_.begin() + static_cast<std::ptrdiff_t>(index[i]));
    }
    for (size_t i = 0; i < delta.additions; ++i) live_.push_back(delta.add[i]);
    const uint64_t previous_prefixes = prefixes_consumed_;
    if (delta.consume_prefixes) prefixes_consumed_ = delta.prefixes_consumed;

    // Compose and validate.  A refusal here must leave the live set as it was,
    // because the caller's sources are still published and its output is not.
    std::unique_ptr<ProbePlan> plan;
    try {
      plan = ComposeLocked();
    } catch (...) {
      RollbackLocked(delta, index, previous_prefixes);
      throw;
    }
    // The retirement record's room, taken before the store for the same reason
    // the plan record was: after it, the old plan's only owner is that record.
    if (retired_.size() == retired_.capacity()) {
      try {
        retired_.reserve(retired_.capacity() + 1);
      } catch (...) {
        RollbackLocked(delta, index, previous_prefixes);
        free_.push_back(std::move(plan));
        throw;
      }
    }
    // The audit's family history must cover the swap, so the new member is
    // counted BEFORE the one it replaces is dropped: a same-family removal and
    // addition (a full carry and the table that absorbs it) would
    // otherwise pass through a count of zero and forget what was probed.
    for (size_t i = 0; i < delta.additions; ++i) {
      audit_.AddMember(delta.add[i].family_id);
    }

    // ---- commit: nothing below may throw ---------------------------------
    ProbePlan* const installed = plan.get();
    plan_.store(installed, std::memory_order_seq_cst);
    const uint64_t threshold = epoch_.RetirementThreshold();
    if (current_ != nullptr) {
      retired_.push_back(RetiredPlan{std::move(current_), threshold});
      pending_retired_.store(retired_.size(), std::memory_order_relaxed);
    }
    current_ = std::move(plan);
    ++publications_;
    // ---- end of the non-throwing commit ----------------------------------

    for (size_t i = 0; i < delta.removals; ++i) {
      audit_.DropMember(removed_[i].family_id);
    }
    return threshold;
  }

  // Retired plans whose readers are gone go back to the pool.  `safe_epoch` is
  // ReaderEpoch::Observed() -- what an acquire load has ACTUALLY reached --
  // and never a threshold this caller expects to be reached later.
  //
  // IT DOES NOT TAKE THE PUBLICATION MUTEX WHEN THERE IS NOTHING TO RECLAIM,
  // and that is a requirement of grouped owner threads, not a
  // micro-optimisation.  Every owner runs this once
  // per poll and every requester once per flush, and `mutex_` is the one lock
  // the whole hierarchy publishes under: an unconditional acquire here puts a
  // contended cross-core RMW on the path a spinning owner runs most often, for
  // a queue that is empty almost always.
  //
  // THE RELAXED COUNT IS SAFE TO BE STALE IN ONE DIRECTION ONLY, and it is the
  // harmless one: `retired_` grows only inside Publish, so a reader that sees
  // a stale zero misses a plan that has just been retired and reclaims it on
  // its next pass -- one poll of delay.  A stale NONZERO merely takes the lock
  // and finds nothing.  What could not be tolerated is a reclamation that
  // never happens, and nothing here can produce one: the count is stored under
  // the mutex after the push, so every publication's increment is visible to
  // the next acquirer of that mutex, and the pool bound (see the header) is
  // stated over pending retirements rather than over how promptly they are
  // noticed.
  size_t ReclaimPlans(uint64_t safe_epoch) {
    if (pending_retired_.load(std::memory_order_relaxed) == 0) return 0;
    std::lock_guard<std::mutex> lock(mutex_);
    FreeCountSync sync{this};
    size_t reclaimed = 0;
    for (size_t i = 0; i < retired_.size();) {
      if (retired_[i].threshold <= safe_epoch) {
        free_.push_back(std::move(retired_[i].plan));
        retired_[i] = std::move(retired_.back());
        retired_.pop_back();
        ++reclaimed;
      } else {
        ++i;
      }
    }
    if (reclaimed != 0) {
      pending_retired_.store(retired_.size(), std::memory_order_relaxed);
    }
    return reclaimed;
  }

  // ---- diagnostics --------------------------------------------------------
  //
  // A synchronized snapshot rather than a reference: the live set is the
  // publisher's, and an unsynchronized diagnostic read from another thread
  // would be a data race.

  std::vector<PublishedTable> LiveTables() const {
    std::lock_guard<std::mutex> lock(mutex_);
    return live_;
  }
  size_t live_count() const {
    std::lock_guard<std::mutex> lock(mutex_);
    return live_.size();
  }
  bool IsLive(uint64_t table_id) const {
    std::lock_guard<std::mutex> lock(mutex_);
    for (const PublishedTable& t : live_) {
      if (t.table_id == table_id) return true;
    }
    return false;
  }

 private:
  struct RetiredPlan {
    std::unique_ptr<ProbePlan> plan;
    uint64_t threshold = 0;
  };

  // One record, at the reservations MakePlan below makes.
  static size_t PlanRecordBytes(size_t max_tables) {
    return sizeof(ProbePlan) + max_tables * sizeof(TableEntry) +
           2 * max_tables * sizeof(uint32_t) +
           ProbeAddressing::ReservedBytes(max_tables);
  }

  std::unique_ptr<ProbePlan> MakePlan() const {
    auto plan = std::make_unique<ProbePlan>();
    // Exact: ComposeLocked refuses anything longer, so the reservation is
    // never wasted and a composition never reallocates.
    plan->tables.reserve(max_tables_);
    plan->hashed.reserve(max_tables_);
    plan->dense.reserve(max_tables_);
    plan->addressing.Reserve(max_tables_);
    return plan;
  }

  size_t FindLiveLocked(uint64_t table_id) const {
    if (table_id == 0) {
      throw std::logic_error("level arena: a removal names no table");
    }
    for (size_t i = 0; i < live_.size(); ++i) {
      if (live_[i].table_id == table_id) return i;
    }
    throw std::logic_error(
        "level arena: a publication removes a table the latest plan does not "
        "hold");
  }

  // `removing` are the (descending) live indices this same delta takes out, so
  // an addition may reuse an identity or a slot the delta itself frees.
  void ValidateAdditionLocked(const PublishedTable& t, const size_t* removing,
                              size_t removals) const {
    if (t.table_id == 0 || t.tier_table_id == 0 ||
        t.table_id == t.tier_table_id) {
      throw std::logic_error(
          "level arena: a published table needs two distinct identities");
    }
    const uint64_t next = next_table_id_.load(std::memory_order_relaxed);
    if (t.table_id >= next || t.tier_table_id >= next) {
      throw std::logic_error(
          "level arena: a published table carries an identity this publisher "
          "never allocated");
    }
    if (t.family_id == 0) {
      throw std::logic_error(
          "level arena: a hashed table needs a nonce family (0 is the dense "
          "reservation)");
    }
    // A table may have NO tier; one that has one needs its storage.
    if (t.data == nullptr || t.masks == nullptr ||
        (t.tier_buckets != 0 &&
         (t.tier_data == nullptr || t.tier_masks == nullptr))) {
      throw std::logic_error("level arena: a published table needs storage");
    }
    if (t.main_buckets == 0) {
      throw std::logic_error("level arena: a published table is empty");
    }
    // Reject empty or inverted windows before composing the plan. Even the
    // empty top owns [0, 1), so no published table needs an exemption.
    if (t.window_end <= t.window_begin) {
      throw std::logic_error("level arena: a published window is empty");
    }
    if (t.slot == kNoSlot || t.generation == 0) {
      throw std::logic_error(
          "level arena: a published table names no slot occupancy, so nothing "
          "can retire it");
    }
    for (size_t i = 0; i < live_.size(); ++i) {
      bool leaving = false;
      for (size_t j = 0; j < removals; ++j) leaving |= removing[j] == i;
      if (leaving) continue;
      const PublishedTable& live = live_[i];
      if (live.table_id == t.table_id ||
          live.tier_table_id == t.tier_table_id) {
        throw std::logic_error("level arena: that identity is already live");
      }
      if (live.owner == t.owner && live.slot == t.slot) {
        throw std::logic_error(
            "level arena: two live tables in one physical slot");
      }
    }
  }

  // Undo the live-set edit of a delta whose composition was refused.  The
  // additions were appended and the removals erased, both in the order above,
  // so this walks them back.
  void RollbackLocked(const PublicationDelta& delta, const size_t* index,
                      uint64_t previous_prefixes) {
    // The additions were appended last, so they come off first; `index` is
    // descending, so re-inserting in reverse restores each removed member at
    // the position it held.
    live_.resize(live_.size() - delta.additions);
    for (size_t i = delta.removals; i-- > 0;) {
      live_.insert(live_.begin() + static_cast<std::ptrdiff_t>(index[i]),
                   removed_[i]);
    }
    prefixes_consumed_ = previous_prefixes;
  }

  std::unique_ptr<ProbePlan> ComposeLocked() {
    std::unique_ptr<ProbePlan> plan = std::move(free_.back());
    free_.pop_back();
    // The reserved dense prefix: placeholders the REQUEST thread overwrites at
    // its next access (ProbePlan, and FillDensePrefix in the engine).  They are
    // dense, zero-bucket and family-free, which every check and count below
    // reads as nothing.
    TableEntry placeholder;
    placeholder.kind = TableKind::kDense;
    plan->prefix_slots = config_.prefix_slots;
    plan->tables.assign(config_.prefix_slots, placeholder);
    plan->hashed.clear();
    plan->dense.clear();
    plan->small_dense = 0;
    plan->ClearAddressing();
    plan->first_live = config_.prefix_slots;
    plan->prefix_buckets = 0;
    plan->heads_consumed = prefixes_consumed_;
    const size_t suffix = config_.prefix_slots;
    for (const PublishedTable& t : live_) {
      plan->tables.push_back(MainEntry(t));
      // A tier-less table is probed in its main alone.
      if (t.tier_buckets != 0) plan->tables.push_back(TierEntry(t));
    }
    // Probe order: newest window first, and a window's main before its tier.
    std::sort(plan->tables.begin() + static_cast<std::ptrdiff_t>(suffix),
              plan->tables.end(),
              [](const TableEntry& a, const TableEntry& b) {
                if (a.window_end != b.window_end) {
                  return a.window_end > b.window_end;
                }
                return a.tier < b.tier;
              });
    try {
      ValidatePlan(*plan, suffix);
    } catch (...) {
      free_.push_back(std::move(plan));
      throw;
    }
    for (uint32_t i = static_cast<uint32_t>(suffix);
         i < plan->tables.size(); ++i) {
      (plan->tables[i].kind == TableKind::kHashed ? plan->hashed : plan->dense)
          .push_back(i);
    }
    BuildProbePlanAddressing(*plan);
    plan->epoch = ++plan_epoch_;
    return plan;
  }

  void ValidatePlan(const ProbePlan& plan, size_t suffix) const {
    if (plan.tables.size() > max_tables_) {
      throw std::logic_error(
          "level arena: the probe plan outgrew its reserved scratch");
    }
    // The publication boundary is the last point at which all windows are
    // visible together, so the laminar-family proof runs here and not only in
    // a test.  The dense prefix's windows are the newest and nest in nothing,
    // so the composed order is laminar iff the worker's half is.
    if (!PlanWindowsLaminar(plan, suffix)) {
      throw std::logic_error(
          "level arena: the published probe windows are not laminar");
    }
    for (size_t i = suffix; i < plan.tables.size(); ++i) {
      const TableEntry& t = plan.tables[i];
      if (t.radix <= 1) continue;
      if (t.index_bits >= 64 ||
          t.radix > (~size_t{0} >> t.index_bits) ||
          t.num_buckets != (static_cast<size_t>(t.radix) << t.index_bits)) {
        throw std::logic_error(
            "level arena: a mixed-radix table's public shape is not r blocks "
            "of 2^index_bits buckets");
      }
    }
    // At most one member of a nonce family is live, so no two live tables
    // are probed at congruent positions in one access.
    if (!PlanHasAtMostOneMemberPerFamily(plan)) {
      throw std::logic_error(
          "level arena: the probe plan holds two tables of one nonce family");
    }
  }

  TableEntry MainEntry(const PublishedTable& t) const {
    TableEntry e;
    e.window_begin = t.window_begin;
    e.window_end = t.window_end;
    e.tier = 0;
    e.kind = TableKind::kHashed;
    e.removable = false;
    e.table_id = t.table_id;
    e.nonce_family_id = t.family_id;
    e.num_buckets = t.main_buckets;
    e.index_bits = t.index_bits;
    e.radix = t.radix;
    e.data = t.data;
    e.masks = t.masks;
    e.nonce_lo = t.nonce.real_lo;
    e.nonce_hi = t.nonce.real_hi;
    e.real_high = t.nonce.real_high;
    e.dummy_high = t.nonce.dummy_high;
    return e;
  }

  // The tier as the cascade sees it: a fixed-address dense table sharing its
  // main's window, probed right after it.  It carries NO family -- it is
  // scanned in full, issues no dummy and leaks no position -- which is also
  // why it does not count against the one-member-per-family rule.
  TableEntry TierEntry(const PublishedTable& t) const {
    TableEntry e;
    e.window_begin = t.window_begin;
    e.window_end = t.window_end;
    e.tier = 1;
    e.kind = TableKind::kDense;
    e.removable = false;
    e.table_id = t.tier_table_id;
    e.nonce_family_id = 0;
    e.num_buckets = t.tier_buckets;
    e.index_bits = 0;
    e.radix = 1;
    e.data = t.tier_data;
    e.masks = t.tier_masks;
    return e;
  }

  Config config_;
  size_t max_tables_ = 0;
  size_t pool_slots_ = 0;
  LevelArenaByteBill bytes_;

  mutable std::mutex mutex_;
  std::vector<PublishedTable> live_;
  std::vector<std::unique_ptr<ProbePlan>> free_;
  std::vector<RetiredPlan> retired_;
  // `retired_.size()`, published for readers that have not taken `mutex_`.
  // Written only under the mutex; see ReclaimPlans for why a stale read is
  // one poll of delay and never a missed reclamation.
  std::atomic<size_t> pending_retired_{0};
  // `free_.size()`, likewise, for CanPublish.  Stored by every locked scope
  // that can change `free_` (FreeCountSync), on every path out of it.
  std::atomic<size_t> free_count_{0};
  struct FreeCountSync {
    LevelArenaPublisher* self;
    ~FreeCountSync() {
      self->free_count_.store(self->free_.size(), std::memory_order_relaxed);
    }
  };
  std::unique_ptr<ProbePlan> current_;
  PublishedTable removed_[PublicationDelta::kMaxRemovals];
  std::atomic<uint64_t> next_table_id_{1};  // 0 is "no table"
  uint64_t plan_epoch_ = 0;
  uint64_t publications_ = 0;
  uint64_t prefixes_consumed_ = 0;

  // The installed plan.  seq_cst on both sides: this store and the reader's
  // epoch entry are the Dekker pair the retirement threshold rests on.
  std::atomic<ProbePlan*> plan_{nullptr};
  ReaderEpoch epoch_;
  ProbeFamilyAudit audit_;
};

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
