#pragma once

// THE REQUESTER'S DENSE SIDE: the online stash, the ring of prefixes it
// assembles, what level 1 takes off it, and how a consumed prefix's slot comes
// back.  DESIGN.md ("Geometry and storage bound") describes the ring, and
// the ownership contract is its threading rule 7: level 1 reports a consumed
// prefix's retirement threshold, and only the requester frees the slot.
//
// ONE RING, THREE UNITS OF COUNTING, and mixing them is the mistake this file
// exists to prevent:
//
//   ACCESS POSITIONS  every access inserts one entry; windows are half-open
//                     ranges of these, as ProbePlan's are.
//   FLUSHES           64s positions.  One online-stash flush, i.e. one UNIT.
//   PREFIXES          r0 flushes.  What level 1 consumes, and what `q` counts.
//
// The current online stash is NOT a separate allocation: it is the current
// UNIT inside the prefix being assembled, s buckets at offset u*s of
// that prefix's ring slot.  A flush is therefore a cursor move, and a prefix
// becomes complete when the cursor leaves its last unit.
//
// WHY THE WHOLE RING SLOT IS ONE PROBE ENTRY.  A complete prefix is r0*s
// contiguous buckets in unit order, oldest first, and the cascade's run scan
// takes the LAST match in a run -- which is exactly "the newest occurrence of
// this key in this prefix".  So a prefix costs one plan entry rather than r0,
// and the same holds for the frozen part of the prefix still being assembled.
// The current unit is its own entry because it is the one REMOVABLE source: a
// probe may clear its match there and nowhere else, since every other dense
// table is a rebuild source (and the merge would then be reading a table
// somebody is writing).
//
// WHAT COUNTS AGAINST q.  A prefix keeps its slot from the moment it starts
// assembling until its hashed replacement is published AND the readers of the
// old plan are gone: a taken prefix remains in the dense probe cascade and
// continues to count against q until the replacing hashed table is published
// and readers of the old prefix finish.  So there are three marks, and
// they are three different numbers:
//
//   taken_      level 1 has started merging this prefix.  It is still probed.
//   consumed_   its replacement is PUBLISHED.  It leaves the cascade here, and
//               that is the plan's own consumption mark (ProbePlan::heads_consumed).
//   reclaimed_  its retirement threshold has been observed.  Only now is the
//               slot free, and only the REQUESTER may say so.
//
// WHO WRITES WHAT.  The requester writes the assembling prefix and nothing
// else; level 1 reads complete prefixes and never writes one.  The one thing
// that crosses the boundary is the retirement notification -- level 1 knows the
// threshold, because it is the publisher that sampled it, and the requester
// owns the slot -- and it crosses through a bounded SPSC ring, sized by the
// prefix slots, exactly like a boundary credit.  A generation on each
// occupancy is what rejects a stale one.
//
// AND WITH OWNER THREADS THE TWO ARE TWO THREADS, so the sentence above
// is an ordering obligation and not only an ownership one.  Exactly two words
// are read by the side that does not write them, and each carries a whole
// half of the ring behind it:
//
//   assembling_  the requester advances it when a prefix COMPLETES, and it is
//                the last thing that flush does, with release.  Level 1 reads
//                it with acquire, and that pair is what carries the prefix's
//                payload, its mask words and the generation of the slot the
//                NEXT prefix starts in.  Nothing else orders them: the buckets
//                are plain memory that one thread filled and the other reads.
//   reclaimed_   the requester advances it; level 1 reads it only to refuse a
//                view of a prefix that has been freed, and a stale (smaller)
//                value there is permissive in the safe direction -- it can
//                never reject a prefix that is still live.
//
// The reverse direction -- the requester writing a slot level 1 has finished
// reading -- is ordered by the retirement ring itself: level 1's read precedes
// its release push, the requester's acquire pop precedes the advance of
// reclaimed_, and only that advance lets CanFreezeUnit hand the slot out
// again.

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <memory>
#include <stdexcept>
#include <vector>

#include "src/oram/table/cpu_byteslice_probe_plan.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_boundary.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_family.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/table/cpu_byteslice_meta.hpp"
#include "src/oram/table/cpu_byteslice_probe.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

// What level 1 sends back when it publishes the table that replaces a prefix
// (threading rule 7).  It names the occupancy, not the storage: the requester owns
// the slot and is the only one that may free it.
struct PrefixRetirement {
  uint64_t prefix = 0;      // the prefix index, zero-based
  uint64_t generation = 0;  // the ring slot's occupancy number
  uint64_t threshold = 0;   // ReaderEpoch::RetirementThreshold() of the publication
};

// The dense table identities live in their own range so that they can never
// collide with a hashed table's, which come from the publisher's counter.
// The publisher refuses pairs reaching bit 63. Engine lifetime validation
// keeps the counters shifted below within the remaining 55 bits.
inline constexpr uint64_t kDenseTableIdBit = uint64_t{1} << 63;

class DensePrefixRing {
 public:
  DensePrefixRing(const LevelArenaGeometry& geometry, const Layout& layout)
      : geometry_(&geometry), layout_(layout),
        unit_buckets_(geometry.StashBuckets()),
        prefix_buckets_(geometry.DensePrefixBuckets()),
        units_per_prefix_(geometry.PrefixFlushes()),
        ring_slots_(size_t{geometry.DensePrefixes()} + 1),
        unit_entries_(geometry.OnlineStashEntries()),
        prefix_positions_(geometry.PrefixPositions()),
        retirements_(size_t{geometry.DensePrefixes()} + 1) {
    const size_t buckets = geometry.DenseRingBuckets();
    if (buckets != ring_slots_ * prefix_buckets_) {
      throw std::logic_error(
          "level arena: the dense ring is not q+1 whole prefixes");
    }
    const size_t data_bytes = CheckedTableBytes(buckets, layout_);
    data_ = AllocateTallied(data_bytes,
                            ByteRole::kDense, &bytes_);
    // The bytes are don't-care until an entry is written over them, but the
    // MASKS are not: a probe reads every mask word of every live entry, and a
    // slot the access counter says is empty must read as empty.
    std::memset(data_.get(), 0, data_bytes);
    masks_.assign(buckets, 0);
    bytes_.AddPlain(ByteRole::kDenseMasks, CheckedSizeMul(buckets, sizeof(uint64_t), "dense masks"));
    generations_.assign(ring_slots_, 0);
    thresholds_.assign(ring_slots_, kNoThreshold);
    bytes_.AddPlain(ByteRole::kBookkeeping, ring_slots_ * sizeof(uint64_t), 2);
    bytes_.AddPlain(ByteRole::kBookkeeping,
                    retirements_.Capacity() * sizeof(PrefixRetirement));
    ExpectPredictedBytes(bytes_, Bytes(*geometry_, layout_),
                         "the dense prefix ring");
    generations_[0] = 1;  // prefix 0 is assembling from the start
    // PartialTableId packs the frozen unit count in the six bits below its
    // 0x40 flag, so r0 above 64 would give two different partials one
    // identity.  The geometry admits r0 in {2, 4, 8}; the encoding says so
    // itself rather than inheriting it.
    if (units_per_prefix_ > 0x40u) {
      throw std::logic_error(
          "level arena: r0 is wider than the unit-count field of a partial "
          "prefix's table identity");
    }
  }

  DensePrefixRing(const DensePrefixRing&) = delete;
  DensePrefixRing& operator=(const DensePrefixRing&) = delete;

  // ---- public geometry ----------------------------------------------------

  // What the ring costs: (q+1) whole prefixes of buckets, one occupancy word
  // each, and three per-slot arrays -- the generations, the retirement
  // thresholds and the notification ring back to the requester.  Mirrors the
  // constructor above and is checked against it there.
  static LevelArenaByteBill Bytes(const LevelArenaGeometry& geometry,
                                  const Layout& layout) {
    const size_t buckets = geometry.DenseRingBuckets();
    const size_t slots = size_t{geometry.DensePrefixes()} + 1;
    LevelArenaByteBill bill;
    bill.AddAligned64(ByteRole::kDense, CheckedTableBytes(buckets, layout));
    bill.AddPlain(ByteRole::kDenseMasks, CheckedSizeMul(buckets, sizeof(uint64_t), "dense masks"));
    bill.AddPlain(ByteRole::kBookkeeping, slots * sizeof(uint64_t), 2);
    bill.AddPlain(ByteRole::kBookkeeping, slots * sizeof(PrefixRetirement));
    return bill;
  }

  const LevelArenaByteBill& bytes() const { return bytes_; }

  size_t unit_buckets() const { return unit_buckets_; }
  size_t unit_entries() const { return unit_entries_; }
  size_t prefix_buckets() const { return prefix_buckets_; }
  size_t ring_slots() const { return ring_slots_; }
  // The reserved dense half of every plan: the current unit, the frozen part
  // of the prefix being assembled, and at most q complete prefixes.
  size_t plan_prefix_slots() const { return geometry_->DensePrefixes() + 2; }

  uint64_t flushes() const { return flushes_; }
  uint64_t positions() const { return positions_; }
  uint64_t complete_prefixes() const { return AssemblingPublished(); }
  // Level 1's two marks.  Relaxed atomics for the same reason the level's own
  // report counters are (LevelState): `BlockedDiagnosis` reads them from the
  // requester's thread when a wait hits its deadlock bound, and there is no
  // drain to synchronize with at that moment.
  uint64_t taken() const { return taken_.load(std::memory_order_relaxed); }
  uint64_t consumed() const {
    return consumed_.load(std::memory_order_relaxed);
  }
  uint64_t reclaimed() const {
    return reclaimed_.load(std::memory_order_relaxed);
  }
  size_t stash_size() const { return in_unit_; }

  // ---- the request thread -------------------------------------------------

  // One access's entry, at the current unit's next position.  Every byte is
  // written whatever the flags say; only the occupancy bit is conditional
  // (WriteDenseStashEntry), because `real` and `erased` are secret.
  template <bool Values = true>
  void Insert(KeyWords key, const uint8_t* value, bool real, bool erased,
              bool unshadowed) {
    // REFUSED, not clamped, like everything else here.  The engine flushes the
    // moment a unit fills, but its flush can fail for a real reason (no free
    // prefix slot and no level able to progress), and a caller that caught
    // that and issued another access would otherwise write at
    // `UnitBase() + s` -- the first bucket of the NEXT ring slot, and one past
    // the allocation when this is the last one.  The engine retries such a
    // flush at the START of the next access, before its probe removes
    // anything, so this refusal is an engine bug when it fires.
    if (in_unit_ == unit_entries_) {
      throw std::logic_error(
          "level arena: the current online-stash unit is full and must be "
          "frozen before another entry is inserted");
    }
    const size_t bucket = UnitBase() + in_unit_ / kBucketCapacity;
    WriteDenseStashEntry<Values>(BucketAt(bucket), &masks_[bucket],
                         in_unit_ % kBucketCapacity, layout_, key, value, real,
                         erased, unshadowed);
    ++in_unit_;
    ++positions_;
  }

  uint8_t* NextInsertBucket() const {
    return BucketAt(UnitBase() + in_unit_ / kBucketCapacity);
  }
  size_t NextInsertSlot() const { return in_unit_ % kBucketCapacity; }

  bool UnitFull() const { return in_unit_ == unit_entries_; }
  // Whether `entries` more inserts fill the current unit, or it is full
  // already: the only case in which they can complete a prefix.  One compare
  // of the cursor, for the access path (LevelArenaEngine::BeginAccess).
  bool UnitFillsWithin(size_t entries) const {
    return in_unit_ + entries >= unit_entries_;
  }

  // ---- direct initialization ---------------------------------------------
  //
  // THE STATE A DIRECT INITIALIZATION LEAVES THE RING IN is the one an
  // ordinary run reaches after H complete prefixes have been assembled,
  // handed to level 1, consumed by it and reclaimed: the ring holds nothing,
  // and every counter continues from H rather than from zero.  After this the
  // requester's next access opens prefix H's first unit and level 1's next
  // carry is ordinal H + 1, with no special case anywhere.
  //
  // IT TAKES THE WHOLE SEED and not the prefix count, because the three
  // numbers it sets are in three different units -- prefixes, stash flushes
  // and access positions -- and InitialSeed exists to keep them from being
  // mixed up (see its comment).  Recomputing two of them from the third here
  // would be exactly that mistake, one spelling later.
  void SeedDirectInitialization(const InitialSeed& seed) {
    if (flushes_ != 0 || positions_ != 0 || in_unit_ != 0 ||
        units_in_prefix_ != 0 || AssemblingHere() != 0 || taken() != 0) {
      throw std::logic_error(
          "level arena: this dense ring has already been written");
    }
    if (seed.prefixes == 0) return;
    // The assembling occupancy moves from slot 0 to H's, with its masks
    // cleared, because a slot's first unit would otherwise share buckets with
    // whatever the previous occupancy left -- the same reason FreezeUnit
    // clears them.  At H a multiple of the ring size the two slots coincide,
    // which the ++ below handles without a special case.
    generations_[0] = 0;
    const size_t slot = RingSlot(seed.prefixes);
    std::fill_n(&masks_[slot * prefix_buckets_], prefix_buckets_, uint64_t{0});
    ++generations_[slot];
    taken_.store(seed.prefixes, std::memory_order_relaxed);
    consumed_.store(seed.prefixes, std::memory_order_relaxed);
    reclaimed_.store(seed.prefixes, std::memory_order_relaxed);
    pending_through_ = seed.prefixes;
    flushes_ = seed.stash_flushes;
    positions_ = seed.access_offset;
    // LAST, and a release store, for FreezeUnit's reason: everything level 1
    // may read behind it -- the slot's cleared masks and its generation -- is
    // written first.
    assembling_.store(seed.prefixes, std::memory_order_release);
  }

  // Clear this key from the CURRENT unit alone.  The dense builder requires
  // each unit to be internally unique, and an unprobed write is the one
  // path that could otherwise put a key in twice; every older copy, frozen or
  // published, is resolved by the merge's own deduplication.
  void ClearFromCurrentUnit(KeyWords key) {
    const size_t base = UnitBase();
    for (size_t b = 0; b < unit_buckets_; ++b) {
      uint64_t& mask = masks_[base + b];
      mask &= ~MatchMaskByteSliced(BucketAt(base + b), mask, layout_, key);
    }
  }

  // Whether the unit that is full may be frozen, i.e. whether the prefix it
  // completes (if it does) has a ring slot to leave behind.  False is the
  // requester's backpressure: it may wait, but only with its reader epoch
  // CLOSED, which is why this is asked from the insert path and never from
  // inside a probe.
  bool CanFreezeUnit() const {
    // A unit that is not its prefix's last one takes no new slot.
    if (units_in_prefix_ + 1 != units_per_prefix_) return true;
    // It is, so the prefix completes and the next one starts assembling in a
    // slot of its own; the complete prefixes then outstanding, consumed-but-
    // pinned ones included, must still be at most q.
    return HasPrefixSlots(1);
  }

  // How many prefixes `entries` more inserts would complete from the cursor
  // as it stands.  Zero entries asks about the unit already there: one when
  // it is full and is its prefix's last, zero otherwise.  A public count,
  // like every other number on this side of the ring.
  uint64_t PrefixesCompletedBy(size_t entries) const {
    const uint64_t filled =
        uint64_t{units_in_prefix_} * unit_entries_ + in_unit_;
    return (filled + entries) / (uint64_t{units_per_prefix_} * unit_entries_);
  }

  // Whether `completions` more prefixes could complete without taking a slot
  // that is still occupied.  CanFreezeUnit is this at one; a batch asks it
  // for everything its inserts will complete BEFORE its probes remove
  // anything (LevelArenaEngine::BeginBatchJob).  Only a reclamation, which is
  // the requester's, can turn it from false to true.
  bool HasPrefixSlots(uint64_t completions) const {
    return AssemblingHere() + completions - reclaimed() <= MaxOutstanding();
  }

  // The full unit becomes immutable and the cursor moves on; when it was the
  // last unit of its prefix, that prefix becomes complete and level 1 may take
  // it.  Refuses rather than overwriting a slot that is still live.
  //
  // RETURNS WHETHER A PREFIX COMPLETED, which is the only thing level 1 can
  // act on: it consumes prefixes, not units, so with the default r0 = 8 seven
  // flushes out of eight give it nothing to do.  A caller that signalled its
  // owner on every flush would send eight times the cross-thread wakeups the
  // work needs, each a seq_cst read-modify-write on a line another core owns.
  bool FreezeUnit() {
    if (!UnitFull()) {
      throw std::logic_error("level arena: freezing a unit that is not full");
    }
    if (!CanFreezeUnit()) {
      throw std::logic_error(
          "level arena: no free dense prefix slot; the requester must wait "
          "for one with its reader epoch closed");
    }
    ++flushes_;
    in_unit_ = 0;
    if (units_in_prefix_ + 1 == units_per_prefix_) {
      // THE PREFIX COMPLETES, and the store that says so is the LAST thing
      // this function does.  Everything level 1 will read behind it is written
      // first -- the finished prefix's own buckets, already there, and the new
      // occupancy's cleared masks and generation -- and the release store is
      // what makes all of it visible to the acquire load level 1 reads
      // `assembling_` with.  Ordering it the other way round publishes a
      // prefix whose slot metadata a consumer may not see.
      const uint64_t next = AssemblingHere() + 1;
      const size_t slot = RingSlot(next);
      // A new occupancy, and an empty one: the previous prefix's masks are
      // still in this slot until something clears them, and the first unit
      // written here would otherwise share its buckets with them.
      std::fill_n(&masks_[slot * prefix_buckets_], prefix_buckets_,
                  uint64_t{0});
      ++generations_[slot];
      units_in_prefix_ = 0;
      if (!completed_ns_.empty()) {
        completed_ns_[RingSlot(next - 1)] = static_cast<uint64_t>(
            std::chrono::duration_cast<std::chrono::nanoseconds>(
                std::chrono::steady_clock::now().time_since_epoch())
                .count());
      }
      assembling_.store(next, std::memory_order_release);
      return true;
    }
    // The next unit of the same prefix.
    ++units_in_prefix_;
    std::fill_n(&masks_[UnitBase()], unit_buckets_, uint64_t{0});
    return false;
  }

  // ---- the plan's dense half ----------------------------------------------
  //
  // Written by the REQUEST THREAD into the slots the publisher reserved, from
  // ring state only this thread changes, and from the plan's own consumption
  // mark.  Filled from the back, so the newest entry ends up first and the
  // unused leading slots stay placeholders no reader dereferences.
  void FillDensePrefix(ProbePlan* plan) const {
    const uint64_t consumed = plan->heads_consumed;
    const uint64_t assembling = AssemblingHere();
    if (consumed > assembling || assembling - consumed > MaxOutstanding()) {
      throw std::logic_error(
          "level arena: more dense prefixes are live than q allows");
    }
    const size_t live = 1 + (units_in_prefix_ != 0 ? 1 : 0) +
                        static_cast<size_t>(assembling - consumed);
    if (live > plan->prefix_slots) {
      throw std::logic_error(
          "level arena: the dense prefix does not fit its reserved slots");
    }
    TableEntry* const slots = plan->tables.data();
    size_t at = plan->prefix_slots;
    size_t buckets = 0;
    // Oldest first, so that the downward fill leaves probe order.
    for (uint64_t p = consumed; p < assembling; ++p) {
      TableEntry e;
      e.window_begin = p * prefix_positions_;
      e.window_end = (p + 1) * prefix_positions_;
      e.kind = TableKind::kDense;
      e.removable = false;
      e.table_id = PrefixTableId(p);
      e.num_buckets = prefix_buckets_;
      e.data = BucketAt(RingSlot(p) * prefix_buckets_);
      e.masks = MaskAt(RingSlot(p) * prefix_buckets_);
      slots[--at] = e;
      buckets += e.num_buckets;
    }
    const uint64_t prefix_base = assembling * prefix_positions_;
    if (units_in_prefix_ != 0) {
      TableEntry e;
      e.window_begin = prefix_base;
      e.window_end = prefix_base + units_in_prefix_ * unit_entries_;
      e.kind = TableKind::kDense;
      e.removable = false;
      e.table_id = PartialTableId(assembling, units_in_prefix_);
      e.num_buckets = units_in_prefix_ * unit_buckets_;
      e.data = BucketAt(RingSlot(assembling) * prefix_buckets_);
      e.masks = MaskAt(RingSlot(assembling) * prefix_buckets_);
      slots[--at] = e;
      buckets += e.num_buckets;
    }
    TableEntry current;
    current.window_begin = flushes_ * unit_entries_;
    current.window_end = current.window_begin + unit_entries_;
    current.kind = TableKind::kDense;
    current.removable = true;  // the one dense table a probe may clear
    current.table_id = UnitTableId(flushes_);
    current.num_buckets = unit_buckets_;
    current.data = BucketAt(UnitBase());
    current.masks = MaskAt(UnitBase());
    slots[--at] = current;
    buckets += current.num_buckets;
    plan->first_live = at;
    plan->prefix_buckets = buckets;
  }

  // ---- completion stamps (the per-merge log) -------------------------------
  //
  // Off unless enabled before the first access: one steady_clock read per
  // COMPLETED PREFIX on the requester, written into the prefix's ring slot
  // before the release store that publishes it, so level 1 reads it behind
  // its acquire load of `assembling_` like the prefix's other metadata.
  void EnableCompletionStamps() { completed_ns_.assign(ring_slots_, 0); }
  // When `prefix` completed (steady_clock ns), or zero without stamps.  Level
  // 1's, for a prefix it has taken and not yet released.
  uint64_t PrefixCompletedNs(uint64_t prefix) const {
    return completed_ns_.empty() ? 0 : completed_ns_[RingSlot(prefix)];
  }

  // ---- level 1 ------------------------------------------------------------

  // The next prefix level 1 has not started, if it is complete.  Prefixes are
  // taken in order, which is what makes the consumption mark one number.
  bool PrefixReady() const { return taken() < AssemblingPublished(); }

  // The prefix `taken_` as an immutable table of Z/2 buckets, and the
  // occupancy it lives in.  Taking it does NOT free the slot and does not take
  // it out of the cascade: only the publication that replaces it does that.
  TableView TakePrefix(uint64_t* prefix, uint64_t* generation) {
    if (!PrefixReady()) {
      throw std::logic_error("level arena: no complete dense prefix to take");
    }
    const uint64_t p = taken();
    taken_.store(p + 1, std::memory_order_relaxed);
    *prefix = p;
    *generation = generations_[RingSlot(p)];
    return PrefixView(p);
  }

  // A prefix level 1 took but could not use (cancellation, shutdown): it goes
  // back at the head of the queue, since nothing else has looked at it.
  void UntakePrefix(uint64_t prefix) {
    const uint64_t taken = taken_.load(std::memory_order_relaxed);
    if (taken == 0 || prefix != taken - 1) {
      throw std::logic_error(
          "level arena: only the prefix just taken can be given back");
    }
    taken_.store(taken - 1, std::memory_order_relaxed);
  }

  TableView PrefixView(uint64_t prefix) const {
    if (prefix >= AssemblingPublished() || prefix < reclaimed()) {
      throw std::out_of_range("level arena: that dense prefix is not live");
    }
    TableView v;
    v.layout = layout_;
    v.num_buckets = prefix_buckets_;
    v.data = BucketAt(RingSlot(prefix) * prefix_buckets_);
    v.masks = MaskAt(RingSlot(prefix) * prefix_buckets_);
    return v;
  }

  // The publisher's consumption mark, which is what takes the prefix out of
  // the cascade.  Raised by level 1's publication; the requester reads it from
  // the plan, so this is the engine's own copy for FillDensePrefix's bound.
  void NoteConsumed(uint64_t through) {
    if (!TryNoteConsumed(through)) {
      throw std::logic_error(
          "level arena: a dense consumption mark outside [consumed, taken]");
    }
  }

  // The same, NONTHROWING, for the one caller that is standing past its plan
  // install and so has nothing to unwind to (LevelState::Publish, threading
  // rule 4).
  bool TryNoteConsumed(uint64_t through) {
    if (through < consumed() || through > taken()) return false;
    consumed_.store(through, std::memory_order_relaxed);
    return true;
  }

  // Level 1's end of the retirement channel (threading rule 7).  Bounded by the
  // prefix slots, and it cannot fill: one notification per occupancy, and an
  // occupancy ends only when the requester has taken the notification that
  // freed it.
  bool SendRetirement(const PrefixRetirement& message) {
    return retirements_.TryPush(message);
  }

  // The requester's end.  `safe_epoch` is ReaderEpoch::Observed(); a
  // notification whose threshold it has not reached is kept.  Returns how many
  // slots came free.
  //
  // IT RETURNS BEFORE IT TOUCHES ANYTHING when no prefix is retired and none
  // is announced, the second of the two quiet-path early-outs (the plan
  // pool's is the first).  This is the cheaper of
  // the pair -- there is no lock here to avoid, only the work itself -- and
  // what it saves is still real: the one word another thread writes is the
  // ring's tail, level 1 writes it only when it really does retire a prefix,
  // and between two retirements that line stays Shared in this core.  So the
  // quiet call is two loads and a branch rather than a pop attempt, a stale
  // reject test and a walk over the threshold table.
  size_t ReclaimPrefixes(uint64_t safe_epoch) {
    uint64_t reclaimed = reclaimed_.load(std::memory_order_relaxed);
    if (reclaimed == pending_through_ && retirements_.Empty()) return 0;
    PrefixRetirement message;
    while (retirements_.TryPop(&message)) {
      const size_t slot = RingSlot(message.prefix);
      if (message.prefix < reclaimed ||
          message.generation != generations_[slot]) {
        ++rejected_;  // a stale notification: the occupancy has ended
        continue;
      }
      if (message.prefix >= pending_through_) {
        pending_through_ = message.prefix + 1;
      }
      thresholds_[slot] = message.threshold;
    }
    size_t freed = 0;
    // In order: level 1 takes prefixes in order, so it publishes their
    // replacements in order and the thresholds are nondecreasing.
    //
    // A slot with NO threshold recorded reads as kNoThreshold rather than 0,
    // so it stops this loop instead of passing it.  With one producer and one
    // FIFO ring a gap cannot arise today; if one ever did -- a reordered or
    // dropped notification -- a zero default would free a prefix slot whose
    // readers are still inside it, silently, which is the one failure this
    // channel exists to prevent.
    while (reclaimed < pending_through_ &&
           thresholds_[RingSlot(reclaimed)] <= safe_epoch) {
      thresholds_[RingSlot(reclaimed)] = kNoThreshold;
      ++reclaimed;
      ++freed;
    }
    if (freed != 0) reclaimed_.store(reclaimed, std::memory_order_relaxed);
    return freed;
  }

  uint64_t rejected() const { return rejected_; }

  // "No retirement threshold recorded for this slot."  Chosen so that the
  // reclaim scan's `<= safe_epoch` is false for it at every epoch.
  static constexpr uint64_t kNoThreshold = ~uint64_t{0};

  // The identities a dense entry publishes under.  Never reused, disjoint from
  // the hashed ones, and disjoint from each other: a prefix, the frozen part
  // of an assembling one, and a current unit are three different tables.
  static uint64_t PrefixTableId(uint64_t prefix) {
    return kDenseTableIdBit | (prefix << 8);
  }
  static uint64_t PartialTableId(uint64_t prefix, unsigned units) {
    return kDenseTableIdBit | (prefix << 8) | 0x40u | units;
  }
  static uint64_t UnitTableId(uint64_t flush) {
    return kDenseTableIdBit | (flush << 8) | 0x80u;
  }

 private:
  size_t MaxOutstanding() const { return geometry_->DensePrefixes(); }

  // The two sides of the one counter that crosses the thread boundary; see
  // WHO WRITES WHAT at the top of this file.  Two names rather than one, so
  // that which side a call is on -- and therefore which memory order it is
  // entitled to -- is visible at the call site.
  uint64_t AssemblingHere() const {  // the requester, which writes it
    return assembling_.load(std::memory_order_relaxed);
  }
  uint64_t AssemblingPublished() const {  // level 1, with the prefix behind it
    return assembling_.load(std::memory_order_acquire);
  }
  size_t RingSlot(uint64_t prefix) const {
    return static_cast<size_t>(prefix % ring_slots_);
  }
  // The first bucket of the unit being written.  The requester's, always.
  size_t UnitBase() const {
    return RingSlot(AssemblingHere()) * prefix_buckets_ +
           units_in_prefix_ * unit_buckets_;
  }
  uint8_t* BucketAt(size_t bucket) const {
    return data_.get() + bucket * layout_.BucketBytes();
  }
  uint64_t* MaskAt(size_t bucket) const {
    return const_cast<uint64_t*>(masks_.data()) + bucket;
  }

  const LevelArenaGeometry* geometry_;
  Layout layout_;
  size_t unit_buckets_;
  size_t prefix_buckets_;
  unsigned units_per_prefix_;
  size_t ring_slots_;
  size_t unit_entries_;
  uint64_t prefix_positions_;

  LevelArenaByteBill bytes_;
  Aligned64Ptr data_;
  std::vector<uint64_t> masks_;
  std::vector<uint64_t> generations_;  // per ring slot
  std::vector<uint64_t> thresholds_;   // per ring slot, while retired
  std::vector<uint64_t> completed_ns_;  // per ring slot; EnableCompletionStamps

  uint64_t positions_ = 0;   // accesses inserted
  uint64_t flushes_ = 0;     // completed units
  size_t in_unit_ = 0;       // entries in the current unit
  unsigned units_in_prefix_ = 0;
  // The two that cross to level 1's thread.  Everything around them is one
  // side's alone: flushes_/in_unit_/units_in_prefix_/thresholds_/
  // pending_through_/rejected_ are the requester's, taken_/consumed_ are level
  // 1's.
  std::atomic<uint64_t> assembling_{0};  // prefix being assembled; release
  std::atomic<uint64_t> reclaimed_{0};   // freed through; relaxed both ways
  std::atomic<uint64_t> taken_{0};
  std::atomic<uint64_t> consumed_{0};
  uint64_t pending_through_ = 0;  // prefixes with a threshold recorded
  uint64_t rejected_ = 0;

  SpscRing<PrefixRetirement> retirements_;  // level 1 -> requester
};

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
