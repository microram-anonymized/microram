#pragma once

// One level's arena: the allocation its fixed buffers are carved from, and the
// lifecycle that decides who may write each one.  DESIGN.md "Geometry and
// storage bound" lists the buffers (odd banks, inboxes, top banks) and
// "Publication, readers and progress" the credit and retirement protocol.
//
// THE PROBLEM THIS SOLVES.  A level's full table is built by the level BELOW
// it, directly into a buffer the level above owns.  So a buffer has two
// writers over its life (the producer that fills it and the recipient that
// eventually retires it) and an unbounded number of readers (any access that
// snapshotted a plan naming it).  Three things must never happen:
//
//   1. the producer writing a buffer it has not been given;
//   2. the recipient reading a buffer the producer has not finished;
//   3. anyone reusing a buffer a reader can still reach.
//
// The state machine below is exactly those three rules.
//
// (1) ACQUIRING a writable view goes through the lifecycle: a credit and a
// lease name a slot and an extent but carry no pointer, and the only things
// that turn one into a writable table or stash are WritableMain and
// WritableTier, which check the slot is kWriting under this exact generation.
// So there is no way to write a slot you were not given.  RETAINING one past
// publication is a different thing and is a rule rather than a type -- a
// TableView is two raw pointers and nothing can revoke it -- which is why the
// producer is required to drop them when it publishes.  (Putting the views in
// the credit itself would make the lifecycle check decorative: the holder
// would already have the pointers.)
//
// (2) is the kReady -> kInUse handover, with the producer's release store and
// the recipient's acquire load carrying the written bytes.  (3) is the
// retirement epoch -- a slot returns to kFree only when the reader epoch that
// could have snapshotted it has passed.
//
// GENERATIONS.  Every occupancy of a physical slot has a number, and every
// message about that slot carries it.  A credit that was already consumed, a
// Ready that arrives after its slot was retired and re-leased, a slot returned
// twice: all of them present a generation the slot has moved past, and all of
// them are REJECTED rather than acted on.  The alternative -- trusting message
// order across four asynchronous transitions -- is the kind of invariant that
// holds until the first time an owner is descheduled at the wrong moment.
//
// THE TIER IS PART OF THE SLOT.  A table is its main plus its second tier, and
// they retire together.  Giving each physical slot a dedicated tier is what
// makes "this buffer is free" one question instead of two, and is why an old
// tier can never be recycled while its main is still pinned.
//
// A TIER IS A ResidualStash, NOT A TABLE, and the difference is not cosmetic:
// the rebuild drains into it through ctx.tier_out, and a ResidualStash keeps
// its occupancy in an INLINE array of kMaxResidualStashBuckets words rather
// than in a mask array someone else owns.  So a slot's tier is a stash whose
// DATA points into its permanent pool slice (the arena for standalone users)
// and whose MASKS live in the slot's runtime. The arena's own tier payload
// and mask regions stay reserved but unused when a pool supplies the tiers.
// PublishedTierTable() is the TableView the probe plan wants, built from the
// stash so the two cannot disagree.
// The inline array is also why the geometry caps tier_buckets at
// kMaxResidualStashBuckets.
//
// ONE EXCEPTION TO "A SLOT IS ONE BUFFER": the run bank (SlotKind::kRunBank;
// the bank-first run in DESIGN.md "Carries and preparation") is a second
// lifecycle, with its own tier, over the odd
// bank's main.  This machine does not know the two share buckets.  The level
// that owns both keeps them apart -- the carry plan puts consecutive tables
// in disjoint parts of the bank, and a lease on one waits while the other is
// retired (LevelState::AcquireDestination), since a retired table may lie
// anywhere a new one is about to be written.
//
// WHO MAY CALL WHAT.  The transitions below are ATOMIC-FREE OF EACH OTHER: each
// one reads the state word, decides, and writes it back in separate operations,
// not as one compare-and-exchange.  That is sound for the roles this design
// gives a slot and for no others, so the roles are part of the API and not a
// convention:
//
//   PRODUCER (the level below, for an inbox; the level itself, for its own
//     bank) -- exactly one thread per slot.  It alone calls TryLease,
//     WritableMain/WritableTier, Publish and AbandonLease.
//   RECIPIENT (the level that owns the arena) -- exactly one thread per slot.
//     It alone calls MakeCredit, TryAccept, Retire and Reclaim, and it alone
//     reads RetireEpoch, which is a plain field for that reason.
//
// CREDITS ARE ISSUED ONLY BY THE RECIPIENT, where Reclaim makes a slot free
// (MakeCredit), so there is exactly ONE credit per free occupancy, which is
// what keeps a bounded credit queue bounded.  The one other way a slot becomes
// free, AbandonLease at shutdown, issues none on purpose: see AbandonLease.
//
// The generation check REJECTS A STALE MESSAGE -- a credit already consumed, a
// Ready from an occupancy that has ended -- which is a question about ORDER,
// asked by the one actor of that role.  It is NOT a lock: two threads racing
// TryLease on one credit can both read kFree at the same generation and both
// come away with a lease, and nothing here would notice.  Do not describe the
// rejection as protection against arbitrary concurrent callers, and if a slot
// ever needs more than one actor per role, make state and generation one
// serialized operation rather than adjusting memory orders.
//
// What the atomics ARE for is the HANDOFF between the two roles: the release
// store that ends each actor's turn publishes everything it wrote, and the
// acquire load that begins the other's observes it.  That is a
// one-writer-at-a-time relay, which is exactly what separate loads and stores
// can carry.

#include <atomic>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_family.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp"
#include "src/oram/rebuild/cpu_byteslice_residual_stash.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

class LevelArena;

// The lifecycle of one physical buffer.  Partial banks and inboxes run the
// SAME machine; the difference is only who performs which transition.  For an
// inbox the producer does Lease/Publish and the recipient does Accept/Retire;
// for a level's own bank one owner does all four.  Keeping it one machine is
// what lets the retirement rule be stated once.
enum class SlotState : uint8_t {
  kFree,     // nobody owns it; a credit may be issued
  kWriting,  // leased for exclusive writing (an inbox: to the producer)
  kReady,    // written and published; the recipient has not taken it yet
  kInUse,    // the recipient's own immutable table (adoption stays here)
  kRetired,  // replaced; its bytes are held for readers until `retire_epoch`
};

inline const char* SlotStateName(SlotState state) {
  switch (state) {
    case SlotState::kFree: return "free";
    case SlotState::kWriting: return "writing";
    case SlotState::kReady: return "ready";
    case SlotState::kInUse: return "in-use";
    case SlotState::kRetired: return "retired";
  }
  return "?";
}

// One spelling, shared with the geometry's slot lookups.
inline constexpr unsigned kNoSlot = LevelPlan::kNoSlot;

// A recipient's statement that one of its slots is free, and how big it is.
// The producer learns nothing else about the recipient's arena: no base
// pointer, no plan, no neighbouring slot -- and no pointer to this slot
// either, which it gets only by consuming this credit for a lease.
struct SlotCredit {
  LevelArena* arena = nullptr;
  unsigned level = 0;
  unsigned slot = kNoSlot;
  uint64_t generation = 0;  // the slot's generation WHILE FREE
  size_t main_buckets = 0;  // the slot's full extent, enough to plan against
  size_t tier_buckets = 0;

  bool valid() const { return arena != nullptr && slot != kNoSlot; }
};

// Exclusive write access to one slot for one occupancy.  Holding this is the
// only way to obtain a writable view, and publishing consumes it -- after
// which the producer must retain no pointer into the slot.
struct SlotLease {
  LevelArena* arena = nullptr;
  unsigned level = 0;
  unsigned slot = kNoSlot;
  uint64_t generation = 0;  // the occupancy's number; >= 1
  size_t main_buckets = 0;
  size_t tier_buckets = 0;

  bool valid() const { return arena != nullptr && slot != kNoSlot; }
};

// What a producer sends when it has published a full carry into a leased
// inbox.  It names an IMMUTABLE table by its public identity; it carries no
// pointer into the producer's own storage, which is the rule that keeps a
// consumer from reading a stash the producer is about to reset.
struct ReadyMessage {
  unsigned level = 0;  // the RECEIVING level
  unsigned slot = kNoSlot;
  uint64_t generation = 0;
  uint64_t ordinal = 0;   // this carry's one-based ordinal at the receiver
  uint64_t table_id = 0;  // unique over the run
  Family family;
  uint64_t window_begin = 0;
  uint64_t window_end = 0;
  size_t main_buckets = 0;
  size_t tier_buckets = 0;
  // Diagnostic stamps for the top merge log (TopMergeLog), steady_clock ns;
  // written only for a carry addressed to the top and zero otherwise.
  // ready_ns: the producer's commit; accept_ns: the receiver's owner took it
  // from the ring.
  uint64_t ready_ns = 0;
  uint64_t accept_ns = 0;

  bool valid() const { return slot != kNoSlot; }
};

// ---------------------------------------------------------------------------
// LevelArena
// ---------------------------------------------------------------------------
//
// One main allocation and one slot directory per level, with optional tier
// payload supplied by the owning set. There is no interval
// allocator and no placement search: a slot's offset is fixed by the geometry,
// so the only thing that varies at runtime is WHO OWNS IT.

class LevelArena {
 public:
  LevelArena(const LevelPlan& plan, const Layout& layout)
      : LevelArena(plan, layout, nullptr) {}

 private:
  friend class LevelArenaSet;
  // Geometry describes the embedded layout (each slot's tier inside the
  // arena), which standalone arenas use.  With pooled tiers, reclassify those
  // tier regions as holes without changing geometry or rounding.
  static void AddStorageBytes(LevelArenaByteBill* bill, const LevelPlan& plan,
                              const Layout& layout, bool external_tiers) {
    LevelArenaByteBill embedded;
    AddLevelArenaBytes(&embedded, plan, layout);
    if (!external_tiers) {
      bill->Add(embedded);
      return;
    }
    bill->AddAligned64Split({
        {ByteRole::kMains, embedded.At(ByteRole::kMains)},
        {ByteRole::kRetainedTierHoles, embedded.At(ByteRole::kTiers)}});
  }

  // Only the owning set supplies external storage. It reserves exactly the
  // sum of these slots' tier extents and outlives all of its arenas.
  LevelArena(const LevelPlan& plan, const Layout& layout, uint8_t* tier_data)
      : plan_(plan), layout_(layout) {
    if (plan_.slots.empty()) {
      throw std::invalid_argument("level arena: a level needs at least one slot");
    }
    // Preserve every main offset and the allocation's size/alignment. With
    // external tiers the embedded tier regions are retained physical holes.
    AddStorageBytes(&bytes_, plan_, layout_, tier_data != nullptr);
    data_ = AllocateAligned64(
        CheckedTableBytes(plan_.arena_buckets, layout_));
    masks_ = MakeTalliedArray<uint64_t>(plan_.arena_buckets, ByteRole::kMasks,
                                        &bytes_);
    slots_ = MakeTalliedArray<SlotRuntime>(plan_.slots.size(),
                                           ByteRole::kBookkeeping, &bytes_);
    ExpectPredictedBytes(bytes_, Bytes(plan_, layout_, tier_data != nullptr),
                         "a level arena");
    for (size_t i = 0; i < plan_.slots.size(); ++i) {
      const SlotSpec& s = plan_.slots[i];
      if (s.tier_buckets > kMaxResidualStashBuckets) {
        throw std::invalid_argument(
            "level arena: a tier is wider than a residual stash's occupancy "
            "array");
      }
      ResidualStash& tier = slots_[i].tier;
      tier.data = tier_data != nullptr
                      ? tier_data
                      : data_.get() + s.tier_offset * layout_.BucketBytes();
      if (tier_data != nullptr) {
        tier_data += CheckedTableBytes(s.tier_buckets, layout_);
      }
      tier.num_buckets = s.tier_buckets;
      tier.entry_bytes = layout_.EntryBytes();
    }
  }

 public:
  LevelArena(const LevelArena&) = delete;
  LevelArena& operator=(const LevelArena&) = delete;

  // External payload is charged by the owning set, once. Its retained holes
  // still cost bytes here; standalone arenas use those regions for live tiers.
  static LevelArenaByteBill Bytes(const LevelPlan& plan, const Layout& layout,
                                  bool external_tiers = false) {
    LevelArenaByteBill bill;
    AddStorageBytes(&bill, plan, layout, external_tiers);
    bill.AddPlain(ByteRole::kMasks, CheckedSizeMul(plan.arena_buckets, sizeof(uint64_t), "arena masks"));
    bill.AddPlain(ByteRole::kBookkeeping,
                  plan.slots.size() * sizeof(SlotRuntime));
    return bill;
  }

  const LevelArenaByteBill& bytes() const { return bytes_; }

  const LevelPlan& plan() const { return plan_; }
  const Layout& layout() const { return layout_; }
  unsigned level() const { return plan_.level; }
  size_t num_slots() const { return plan_.slots.size(); }
  const SlotSpec& spec(unsigned slot) const { return plan_.At(slot); }

  SlotState State(unsigned slot) const {
    return static_cast<SlotState>(
        Runtime(slot).state.load(std::memory_order_acquire));
  }
  uint64_t Generation(unsigned slot) const {
    return Runtime(slot).generation.load(std::memory_order_relaxed);
  }
  uint64_t RetireEpoch(unsigned slot) const { return Runtime(slot).retire_epoch; }

  // Messages rejected for a stale generation or a wrong state.  A nonzero
  // count is not by itself a bug -- rejection is what generations are FOR --
  // but a test that expects a clean run checks it, and the owner loop reports
  // it.
  uint64_t rejected() const {
    return rejected_.load(std::memory_order_relaxed);
  }

  // ---- views --------------------------------------------------------------

  // Writable views require a live lease, so "the producer may not write a slot
  // it was not given" is a fact about the API rather than a comment.
  // `buckets` is the table's ACTUAL extent, which for a partial is j*U_l and
  // never the whole bank; the rest of a bank is not a table and is not
  // probeable.
  TableView WritableMain(const SlotLease& lease, size_t buckets) const {
    return WritableMain(lease, 0, buckets);
  }
  // A table that starts `offset` buckets into the slot: a bank-first run puts
  // some of a bank's partials at its top (LevelArenaGeometry::BankOffset).
  TableView WritableMain(const SlotLease& lease, size_t offset,
                         size_t buckets) const {
    RequireLease(lease, SlotState::kWriting);
    return MainViewOf(lease.slot, offset, buckets);
  }
  // The rebuild's drain destination (RebuildStepContext::tier_out).
  ResidualStash* WritableTier(const SlotLease& lease) const {
    RequireLease(lease, SlotState::kWriting);
    return const_cast<ResidualStash*>(&Runtime(lease.slot).tier);
  }

  // A view of a slot that has been published: readable by the recipient, and
  // immutable by contract until the recipient retires it.
  TableView PublishedMain(unsigned slot, size_t buckets) const {
    return PublishedMain(slot, 0, buckets);
  }
  TableView PublishedMain(unsigned slot, size_t offset, size_t buckets) const {
    RequirePublished(slot);
    return MainViewOf(slot, offset, buckets);
  }
  // Immutable by contract until the recipient retires the slot.  A consumer
  // that means to run a pool dedup, a reset or a drain over it must copy it
  // into job-owned storage first: those write the stash.
  const ResidualStash* PublishedTier(unsigned slot) const {
    RequirePublished(slot);
    return &Runtime(slot).tier;
  }

  // The same tier as the probe cascade sees it.  Derived from the stash rather
  // than from the arena, because the stash's inline array IS the occupancy.
  TableView PublishedTierTable(unsigned slot) const {
    RequirePublished(slot);
    const ResidualStash& tier = Runtime(slot).tier;
    TableView v;
    v.layout = layout_;
    v.num_buckets = tier.num_buckets;
    v.data = tier.data;
    v.masks = const_cast<uint64_t*>(&tier.masks[0]);
    return v;
  }

  // ---- the state machine --------------------------------------------------

  // A credit for a free slot, with the extents it names.  Issuing one does not
  // change the slot's state: the credit is a message, and a message that is
  // lost must not strand the buffer.  RECIPIENT ONLY.
  //
  // Two credits for one occupancy are not a correctness hazard for the single
  // producer -- it consumes one and the other then presents a generation the
  // slot has moved past -- but they are not free either: duplicate messages
  // fill a bounded queue, and the capacity accounting counts occupancies, not
  // messages.  Issue one per free occupancy, not one per scan.
  SlotCredit MakeCredit(unsigned slot) {
    const SlotRuntime& r = Runtime(slot);
    if (static_cast<SlotState>(r.state.load(std::memory_order_acquire)) !=
        SlotState::kFree) {
      throw std::logic_error("level arena: credit for a slot that is not free");
    }
    SlotCredit credit;
    credit.arena = this;
    credit.level = plan_.level;
    credit.slot = slot;
    credit.generation = r.generation.load(std::memory_order_relaxed);
    credit.main_buckets = spec(slot).main_buckets;
    credit.tier_buckets = spec(slot).tier_buckets;
    return credit;
  }

  // Consume a credit: kFree -> kWriting, one occupancy later.  False means the
  // credit was stale (already consumed, or from a previous occupancy).
  // PRODUCER ONLY, and one producer: see the roles at the top of this file.
  bool TryLease(const SlotCredit& credit, SlotLease* out) {
    if (credit.arena != this || credit.slot >= num_slots()) {
      throw std::logic_error("level arena: credit belongs to another arena");
    }
    SlotRuntime& r = Runtime(credit.slot);
    if (static_cast<SlotState>(r.state.load(std::memory_order_acquire)) !=
            SlotState::kFree ||
        r.generation.load(std::memory_order_relaxed) != credit.generation) {
      Reject();
      return false;
    }
    // Exhaustion is refused BEFORE the slot is touched, like the nonce
    // ordinal's (FamilyId).  A wrapped generation would hand this occupancy
    // the number of an occupancy that has ended, which is precisely the state
    // every stale-message check here tests against.
    if (credit.generation == ~uint64_t{0}) {
      throw std::runtime_error("level arena: slot generation exhausted; "
                               "refusing to reuse an occupancy number");
    }
    const uint64_t generation = credit.generation + 1;
    // A NEW OCCUPANCY STARTS WITH AN EMPTY TIER.  Reclamation returns the
    // slot's bytes, not its meaning, and the tier stash's occupancy words
    // survive it -- so without this the first thing a producer's drain does is
    // add to the previous table's leftovers.  It belongs here rather than in
    // whatever writes the slot, because adoption and a cancelled lease write
    // nothing and would each have to remember.
    r.tier.Reset();
    r.generation.store(generation, std::memory_order_relaxed);
    r.state.store(static_cast<uint8_t>(SlotState::kWriting),
                  std::memory_order_release);
    SlotLease lease;
    lease.arena = this;
    lease.level = plan_.level;
    lease.slot = credit.slot;
    lease.generation = generation;
    lease.main_buckets = credit.main_buckets;
    lease.tier_buckets = credit.tier_buckets;
    *out = lease;
    return true;
  }

  // The owner's own bank: credit and lease in one step.  Same machine, no
  // message in between, because there is no second party.
  bool TryLeaseOwn(unsigned slot, SlotLease* out) {
    if (State(slot) != SlotState::kFree) return false;
    return TryLease(MakeCredit(slot), out);
  }

  // The producer is done writing: kWriting -> kReady.  PRODUCER ONLY.  The
  // release store is what publishes the written bytes to the recipient's
  // acquire load, so this must be the LAST thing the producer does to the
  // slot.
  bool Publish(const SlotLease& lease) {
    if (lease.arena != this) {
      throw std::logic_error("level arena: lease belongs to another arena");
    }
    SlotRuntime& r = Runtime(lease.slot);
    if (static_cast<SlotState>(r.state.load(std::memory_order_relaxed)) !=
            SlotState::kWriting ||
        r.generation.load(std::memory_order_relaxed) != lease.generation) {
      Reject();
      return false;
    }
    r.state.store(static_cast<uint8_t>(SlotState::kReady),
                  std::memory_order_release);
    return true;
  }

  // The recipient takes ownership: kReady -> kInUse.  RECIPIENT ONLY.  A stale
  // Ready -- one naming an occupancy that has already been retired and
  // replaced -- is rejected here.  The recipient learns that a slot is ready
  // from the ready channel and not by scanning states; this is where it
  // validates what it was told.
  bool TryAccept(unsigned slot, uint64_t generation) {
    if (slot >= num_slots()) {
      throw std::logic_error("level arena: no such slot");
    }
    SlotRuntime& r = Runtime(slot);
    if (static_cast<SlotState>(r.state.load(std::memory_order_acquire)) !=
            SlotState::kReady ||
        r.generation.load(std::memory_order_relaxed) != generation) {
      Reject();
      return false;
    }
    r.state.store(static_cast<uint8_t>(SlotState::kInUse),
                  std::memory_order_relaxed);
    return true;
  }

  // The table has been replaced in the published plan: kInUse -> kRetired,
  // pinned until readers of that plan are gone.  RECIPIENT ONLY.  `epoch` is the retirement
  // epoch of the publication that replaced it -- the same number the retired
  // plan record gets, which is why the two can never be reclaimed out of step.
  bool Retire(unsigned slot, uint64_t generation, uint64_t epoch) {
    SlotRuntime& r = Runtime(slot);
    if (static_cast<SlotState>(r.state.load(std::memory_order_relaxed)) !=
            SlotState::kInUse ||
        r.generation.load(std::memory_order_relaxed) != generation) {
      Reject();
      return false;
    }
    r.retire_epoch = epoch;
    r.state.store(static_cast<uint8_t>(SlotState::kRetired),
                  std::memory_order_relaxed);
    return true;
  }

  // Every retired slot whose readers are gone: kRetired -> kFree.  RECIPIENT
  // ONLY, and `safe_epoch` is an OBSERVED reader epoch -- what an acquire load
  // of the reader counter has actually reached -- never a publication id or a
  // threshold the caller expects to be reached later.  The
  // generation does NOT advance here -- it advanced when the occupancy began
  // -- so the credit issued next carries the number a stale message from the
  // occupancy just ended cannot present. Visit each freed slot immediately
  // and return the count, without retaining an intermediate list.
  template <class OnFreed>
  size_t ReclaimEach(uint64_t safe_epoch, OnFreed&& on_freed) {
    size_t count = 0;
    for (unsigned slot = 0; slot < num_slots(); ++slot) {
      SlotRuntime& r = Runtime(slot);
      if (static_cast<SlotState>(r.state.load(std::memory_order_relaxed)) !=
          SlotState::kRetired) {
        continue;
      }
      if (r.retire_epoch > safe_epoch) continue;
      r.retire_epoch = 0;
      r.state.store(static_cast<uint8_t>(SlotState::kFree),
                    std::memory_order_release);
      on_freed(slot);
      ++count;
    }
    return count;
  }

  size_t Reclaim(uint64_t safe_epoch, std::vector<unsigned>* freed = nullptr) {
    return ReclaimEach(safe_epoch, [&](unsigned slot) {
      if (freed != nullptr) freed->push_back(slot);
    });
  }

  // A slot that was leased but whose merge will never run: terminal
  // shutdown.  PRODUCER ONLY.  Returns the buffer without publishing anything.
  // Not a normal-path transition: the normal path always publishes.
  //
  // NO CREDIT IS ISSUED for the occupancy this leaves free, so the slot stays
  // free and unreachable until the arena is destroyed -- what a shutdown
  // wants, and a lost inbox for any engine that continued.  The recipient
  // cannot credit it either: it credits on RECLAMATION, and an abandoned slot
  // was never retired.  A recipient that instead SCANNED for
  // free slots would mint duplicates, which is the hazard MakeCredit's comment
  // is about.
  //
  // The generation is not rolled back, so the credit that BOUGHT this lease
  // stays spent: occupancy numbers only ever increase, here as everywhere else
  // in this file.
  bool AbandonLease(const SlotLease& lease) {
    if (lease.arena != this) {
      throw std::logic_error("level arena: lease belongs to another arena");
    }
    SlotRuntime& r = Runtime(lease.slot);
    if (static_cast<SlotState>(r.state.load(std::memory_order_relaxed)) !=
            SlotState::kWriting ||
        r.generation.load(std::memory_order_relaxed) != lease.generation) {
      Reject();
      return false;
    }
    r.state.store(static_cast<uint8_t>(SlotState::kFree),
                  std::memory_order_release);
    return true;
  }

 private:
  // One atomic state word per slot.  `state` is the handoff: whoever owns the
  // slot writes `generation` before the release store that hands it on, and the
  // next owner reads it after the matching acquire load, so the release
  // sequence carries it.  `generation` is atomic anyway -- the cost is nil, and
  // a plain field read across a handoff is exactly the sort of thing a
  // sanitizer has to be argued with rather than shown.
  //
  // `retire_epoch` is NOT atomic and does not need to be: only the recipient
  // ever writes it (Retire) or reads it (Reclaim), and a producer never sees a
  // retired slot -- it only ever holds a credit for a free one.  That is also
  // why RetireEpoch() is a recipient-side accessor: a diagnostic read from
  // another thread is a race, and needs a synchronized snapshot instead.
  struct SlotRuntime {
    std::atomic<uint8_t> state{static_cast<uint8_t>(SlotState::kFree)};
    std::atomic<uint64_t> generation{0};
    uint64_t retire_epoch = 0;
    // Fixed at construction and never re-pointed: the tier of a slot is the
    // slot's, for the same reason its main is: physical extents are fixed by
    // the public geometry at construction.  Only its masks and bytes
    // change, and only under the lifecycle above.
    ResidualStash tier;
  };

  void Reject() const { rejected_.fetch_add(1, std::memory_order_relaxed); }

  SlotRuntime& Runtime(unsigned slot) {
    if (slot >= num_slots()) throw std::out_of_range("level arena: no such slot");
    return slots_[slot];
  }
  const SlotRuntime& Runtime(unsigned slot) const {
    if (slot >= num_slots()) throw std::out_of_range("level arena: no such slot");
    return slots_[slot];
  }

  void RequireLease(const SlotLease& lease, SlotState expected) const {
    if (lease.arena != this) {
      throw std::logic_error("level arena: lease belongs to another arena");
    }
    const SlotRuntime& r = Runtime(lease.slot);
    if (static_cast<SlotState>(r.state.load(std::memory_order_relaxed)) !=
            expected ||
        r.generation.load(std::memory_order_relaxed) != lease.generation) {
      throw std::logic_error("level arena: writing a slot without a live lease");
    }
  }

  void RequirePublished(unsigned slot) const {
    const SlotState state = State(slot);
    if (state != SlotState::kReady && state != SlotState::kInUse &&
        state != SlotState::kRetired) {
      throw std::logic_error("level arena: reading a slot that is not published");
    }
  }

  // "Of" and not "Unchecked": the slot index and the extent ARE checked here.
  // What these skip is the LIFECYCLE check -- who is allowed to hold this view
  // -- which is the caller's (WritableMain, PublishedMain, MakeCredit).
  TableView MainViewOf(unsigned slot, size_t offset, size_t buckets) const {
    const SlotSpec& s = spec(slot);
    if (buckets == 0 || offset > s.main_buckets ||
        buckets > s.main_buckets - offset) {
      throw std::invalid_argument("level arena: table does not fit its slot");
    }
    return MakeView(s.main_offset + offset, buckets);
  }
  TableView MakeView(size_t offset, size_t buckets) const {
    TableView v;
    v.layout = layout_;
    v.num_buckets = buckets;
    v.data = data_.get() + offset * layout_.BucketBytes();
    v.masks = masks_.get() + offset;
    return v;
  }

  LevelPlan plan_;
  Layout layout_;
  LevelArenaByteBill bytes_;
  Aligned64Ptr data_;
  std::unique_ptr<uint64_t[]> masks_;
  std::unique_ptr<SlotRuntime[]> slots_;
  // Incremented by BOTH parties -- the producer rejects a stale credit or a
  // double publish, the recipient a stale Ready or retire -- so it is atomic.
  // It is pure diagnostics and orders nothing, hence relaxed.
  mutable std::atomic<uint64_t> rejected_{0};
};

// ---------------------------------------------------------------------------
// The hierarchy's storage
// ---------------------------------------------------------------------------
//
// One LevelArena per hashed level, in one place, so the owner of level l can
// be handed exactly two things: its own arena and the credit ring of level
// l+1.  Nothing else in the engine needs a base pointer.

class LevelArenaSet {
 public:
  LevelArenaSet(const LevelArenaGeometry& geometry, const Layout& layout)
      : geometry_(geometry),
        tiers_(AllocateTallied(TierPayloadBytes(geometry, layout),
                              ByteRole::kTiers, &bytes_)) {
    arenas_.resize(geometry.Levels() + 1);
    size_t offset = 0;
    for (unsigned l = 1; l <= geometry.Levels(); ++l) {
      const LevelPlan& plan = geometry.storage().At(l);
      arenas_[l].reset(new LevelArena(plan, layout, tiers_.get() + offset));
      bytes_.Add(arenas_[l]->bytes());
      for (const SlotSpec& slot : plan.slots) {
        offset = CheckedSizeAdd(offset, CheckedTableBytes(slot.tier_buckets, layout),
                                "tier pool offset");
      }
    }
    if (offset != TierPayloadBytes(geometry, layout)) {
      throw std::logic_error("level arena: tier slices do not span the pool");
    }
    ExpectPredictedBytes(bytes_, Bytes(geometry, layout), "the arena set");
  }

  // Bucket bytes include every routing-tag line and are a multiple of 64.
  // Concatenating the physical slot extents needs no padding between slices.
  static size_t TierPayloadBytes(const LevelArenaGeometry& geometry,
                                 const Layout& layout) {
    return CheckedTableBytes(geometry.storage().tier_buckets, layout);
  }

  static LevelArenaByteBill Bytes(const LevelArenaGeometry& geometry,
                                  const Layout& layout) {
    LevelArenaByteBill bill;
    bill.AddAligned64(ByteRole::kTiers, TierPayloadBytes(geometry, layout));
    for (unsigned l = 1; l <= geometry.Levels(); ++l) {
      bill.Add(LevelArena::Bytes(geometry.storage().At(l), layout, true));
    }
    return bill;
  }

  const LevelArenaByteBill& bytes() const { return bytes_; }
  const LevelArenaGeometry& geometry() const { return geometry_; }
  LevelArena& At(unsigned level) {
    if (level < 1 || level >= arenas_.size() || arenas_[level] == nullptr) {
      throw std::out_of_range("level arena: no such level");
    }
    return *arenas_[level];
  }
  const LevelArena& At(unsigned level) const {
    return const_cast<LevelArenaSet*>(this)->At(level);
  }

 private:
  LevelArenaGeometry geometry_;
  LevelArenaByteBill bytes_;
  // Declared before arenas so every stash is destroyed before its payload.
  // The engine destroys jobs, plans and workers before this owning set.
  Aligned64Ptr tiers_;
  std::vector<std::unique_ptr<LevelArena>> arenas_;
};

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
