#pragma once

// ONE LEVEL'S STATE MACHINE: what it owns, what it is waiting for, and the one
// nonblocking step that moves it.  DESIGN.md, "Carries and preparation" and
// "Publication, readers and progress", describes the design; the publication
// transaction a level performs is threading rule 4 and the pinning rule it
// obeys is threading rule 6 (DESIGN.md, "Threading rules", numbers them).
//
// THE STEP, in this order:
//
//     collect ready carries and reader-safe retirements; return credits
//     if the carry plan selects adoption and a sparse carry is ready:
//         adopt it in place and advance the ordinal
//     else if the destination is available and a carry is ready:
//         prepare if necessary, install the carry, finish, publish
//     else if an older partial exists and the destination is available:
//         prepare that destination once, under the next ordinal's family
//     else:
//         report the dependency and yield
//
// and every branch of it is a function of PUBLIC counters: the level's carry
// ordinal, the digit that ordinal implies, and whether a physical slot is
// free.  Nothing here reads occupancy, a key, a match or a shed count.
//
// ONE PENDING JOB (threading rule 6).  A level has at most one outstanding
// ordinal.  Preparation pins its logical source -- the older partial it routed,
// the destination lease it routed into, and the family it routed under -- and
// nothing may advance the ordinal or replace that source while it is pending.
// The carry then ARRIVES and is VALIDATED against what was prepared; a
// mismatch is refused rather than re-planned, because re-planning the nonce
// now would leave the already-routed older half under the old one.
//
// FIFO CARRIES.  A receiving level accepts carries only in ordinal order:
// `ordinal_ + 1` next, then `+ 2`.  That is not a convenience -- the window
// arithmetic, the family coordinate and the digit odometer are all functions
// of the ordinal, so a carry taken out of order would be merged under another
// carry's nonce and placed by the wrong hash.
//
// ADOPTION IS NOT A PUBLICATION.  At digit 1 a level that adopts
// (LevelArenaGeometry::AdoptsFirstCarry: every level above 1 whose fanout
// exceeds 2, and a binary one only in the compact layout) takes the ready
// inbox table AS its P_1: same bytes, same tier, same table identity, same
// nonce family, same window.  Nothing is copied and nothing is swapped, so the
// plan does not change and no plan record is spent.  The inbox slot simply
// stays occupied -- through the merge that consumes it at digit 2 and through
// that merge's reader retirement -- which is the whole reason a level has two
// of them.  A binary level in the default layout instead installs P_1 into its
// odd bank as an ordinary digit-1 merge and publishes it, which frees the
// inbox at once.
//
// WHAT THIS FILE DOES NOT DO.  It does not wait.  Every path either makes
// progress or returns a reason, because a level that blocked inside its step
// would hold up every other level its thread drives, and because the
// reasons are reported (LevelBlock) rather than collapsed into "the
// rebuild is slow".  The WAITING is
// cpu_byteslice_level_arena_owner.hpp's; what a level does is the other half
// of that protocol -- it SIGNALS, at the three points where it makes something
// visible that another actor may be parked on (Wiring::wake_*, threading
// rule 8), and
// always after the thing itself is visible rather than before.

#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <stdexcept>
#include <string>

#include "src/oram/levelarena/cpu_byteslice_level_arena_boundary.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_dense.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_event.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_job.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_merge_log.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_pause.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_publication.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_slots.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_stash.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_top_log.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

// Why a level did not move.  Reported per step and accumulated per
// level, so that "the hierarchy is behind" can be attributed rather than
// assumed to be a level-1 merge delay.
enum class LevelBlock : uint8_t {
  kNone,             // it progressed
  kIdle,             // nothing to do and nothing to wait for
  kNoCarry,          // no ready carry, or no complete dense prefix
  kNoOutputCredit,   // the receiving level has no free inbox slot
  kBankRetirement,   // its own destination bank is still pinned by readers
  kInboxRetirement,  // an inbox it needs is still pinned by readers
  kPlanRecords,      // the bounded plan pool is exhausted (LevelArenaPublisher)
  // The next two are reportable reasons that the owner-thread engine does
  // not produce.  That is a design outcome rather than an omission, and both
  // are kept because the report is a public contract and another scheduler
  // could produce them:
  //
  //   kPublishLock   a publication takes `mutex_` and BLOCKS on it.  The
  //                  critical section is a bounded compose-and-validate over
  //                  the live set with no allocation and no I/O, so the wait
  //                  is short and bounded; a try-lock that yielded instead
  //                  would turn a short wait into a spin and buy nothing.
  //   kGroupBusy     a group runs one member's step at a time, so a member is
  //                  never asked to run while another is running (threading
  //                  rule 2).
  //                  The reason would exist only for a scheduler that could
  //                  offer a level to a busy thread.
  kPublishLock,      // another owner holds the publication mutex
  kGroupBusy,        // another member of this thread's group is running
  // The running phase's every unfinished lane is held by a helper thread
  // (LevelHelpers, cpu_byteslice_level_arena_owner.hpp).  The helper that
  // finishes the phase signals the owner; until then the owner has nothing to
  // do for this level.
  kHelpersBusy,
};

// One past the last reason.  LevelStats indexes an array by the enum, so the
// two have to move together; derived here rather than written twice.
inline constexpr size_t kLevelBlockCount =
    static_cast<size_t>(LevelBlock::kHelpersBusy) + 1;

inline const char* LevelBlockName(LevelBlock block) {
  switch (block) {
    case LevelBlock::kNone: return "progressed";
    case LevelBlock::kIdle: return "idle";
    case LevelBlock::kNoCarry: return "no-carry";
    case LevelBlock::kNoOutputCredit: return "no-output-credit";
    case LevelBlock::kBankRetirement: return "bank-retirement";
    case LevelBlock::kInboxRetirement: return "inbox-retirement";
    case LevelBlock::kPlanRecords: return "plan-records";
    case LevelBlock::kPublishLock: return "publish-lock";
    case LevelBlock::kGroupBusy: return "group-busy";
    case LevelBlock::kHelpersBusy: return "helpers-busy";
  }
  return "?";
}

// Whether a level a waiting owner is blocked on is waiting for READERS, which
// is the one dependency no other owner can discharge: a retired bank, a
// retired inbox and an exhausted plan pool all come back when the requester's
// reader epoch passes their threshold and at no other moment.  A group with
// one of these registers as an epoch waiter before it parks (threading
// rule 8).
//
// The reason alone is NOT the whole test.  A kNoOutputCredit producer waits
// on the owner above for a credit, and that owner issues it only by
// reclaiming a retired inbox -- which needs the epoch, while the owner itself
// may be parked on kNoCarry.  So a group also registers when a member merely
// HOLDS a retired inbox (LevelState::WaitsOnReaders); every other reason has
// an awake owner or the requester behind it, and that actor signals.
inline bool LevelBlockWaitsOnReaders(LevelBlock block) {
  return block == LevelBlock::kBankRetirement ||
         block == LevelBlock::kInboxRetirement ||
         block == LevelBlock::kPlanRecords;
}

// What one step did: whether the level moved at all, and -- whether or not it
// did -- what it is waiting for next.  The two are separate because draining a
// retirement IS progress and says nothing about why the merge did not run;
// collapsing them is how "the hierarchy is behind" stops being attributable.
struct LevelStepResult {
  bool progressed = false;
  LevelBlock block = LevelBlock::kIdle;
  // The step stopped a phase between two pieces because its yield asked it
  // to.  The level holds the phase and resumes it at a later step; the caller
  // may run something more urgent first.
  bool paused = false;
};

// WHEN A RUNNING PHASE STOPS, asked after every piece.
//
//   An OWNER GROUP asks once its event has been signalled since
//   `generation` was read.  Every cross-group wake -- the requester's
//   completed prefix, a neighbour's carry or credit, a reader epoch's close
//   -- bumps that event, so "something may have become runnable" costs one
//   load per piece and no lock.  A signal is not yet a reason to stop: with
//   `should_stop` set, the phase stops only if that test finds a more urgent
//   member able to run (LevelGroup::ShouldStop), and otherwise re-arms on the
//   generation it read BEFORE testing, so a signal after that read is tested
//   at a later piece and none is passed over.  Without the test, any signal
//   stops the phase.
//
//   The INLINE EXECUTOR stops when its flush has spent its share of the
//   rebuild: every piece's estimated touches (PieceTouches) are added to
//   `*touches`, and the phase stops once they reach `touch_limit`.
//
// The default, with neither, never stops: a whole-phase step.
struct PhaseYield {
  const OwnerEvent* event = nullptr;
  // Mutable because a declined signal re-arms it: a step's yield is its own
  // copy (LevelGroup::Sweep), so this is that step's state and no one else's.
  mutable uint64_t generation = 0;
  uint64_t* touches = nullptr;
  uint64_t touch_limit = ~uint64_t{0};
  bool (*should_stop)(void* context) = nullptr;
  void* context = nullptr;
  bool operator()(const Subtask& piece) const {
    if (touches != nullptr) {
      *touches += PieceTouches(piece);
      if (*touches >= touch_limit) return true;
    }
    if (event == nullptr || !event->ChangedSince(generation)) return false;
    if (should_stop == nullptr) return true;
    // Read, THEN test: the event's own rule (read the generation, then poll).
    generation = event->Generation();
    return should_stop(context);
  }
};

// What one step is ALLOWED to start, which is the whole of the owner loop's
// rule "prefer ready merges over new speculative preparation".  A grouped owner
// sweeps its members in `kMergeFirst` and only sweeps again in `kAny` when no
// member could merge, so preparation never delays a ready merge.
enum class LevelStepMode : uint8_t {
  kMergeFirst,  // adopt, merge and publish; do not begin a new preparation
  kAny,         // and, failing that, get ahead on the older half
};

// The engine-side handle on a published table this level will consume and then
// retire.  It is the occupancy, not the storage: the views are fetched from
// the arena, which checks the slot is still published, and the identity is
// what a publication's removal names.
struct LevelSource {
  uint64_t table_id = 0;
  // The level whose ARENA holds `slot` (PublishedTable::owner).  This level's
  // own for a bank or an adopted inbox; the level above's for an even partial
  // built inside the forwarding lease, whose bytes are read through that
  // lease and whose retirement is the lease's.
  unsigned owner = 0;
  unsigned slot = kNoSlot;
  uint64_t generation = 0;
  size_t main_buckets = 0;
  // Where the table starts inside its slot's main, in buckets: nonzero only
  // for a bank table a bank-first run put at the bank's top
  // (LevelArenaGeometry::BankOffset; DESIGN.md, "Carries and preparation").
  size_t offset = 0;

  bool valid() const { return table_id != 0; }
};

// One writer (the level owner), arbitrary diagnostic readers. Load/store
// increments avoid locked RMW instructions on the hot polling path. These
// counters publish numbers only; they do not synchronize level state.
class LevelCounter {
 public:
  operator uint64_t() const { return value_.load(std::memory_order_relaxed); }
  void operator++() { Add(1); }
  void Add(uint64_t n) {
    value_.store(value_.load(std::memory_order_relaxed) + n,
                 std::memory_order_relaxed);
  }
  void StoreMax(uint64_t n) {
    if (n > value_.load(std::memory_order_relaxed)) {
      value_.store(n, std::memory_order_relaxed);
    }
  }

 private:
  std::atomic<uint64_t> value_{0};
};

// The largest digit a job can have: B below the top, D at it, both at most 8.
inline constexpr unsigned kMaxLevelDigit = LevelArenaGeometry::kMaxTopDigit;

// Per-level counters, all public: they count steps and slots, never entries.
// The public uint64_t specialization is a value snapshot; the owner stores
// atomic counters. A snapshot is race-free but fields may span several steps.
// Drain settles productive work totals; idle step/block counts still advance.
template <class Counter>
struct LevelStatsValues {
  Counter steps{};
  Counter merges{};
  Counter adoptions{};
  Counter preparations{};
  Counter publications{};
  Counter forwards{};
  // Publications of an even partial INTO the forwarding lease: the path a
  // fixture has to see taken before it may claim to have exercised it.
  Counter inbox_partials{};
  Counter blocked[kLevelBlockCount] = {};  // indexed by LevelBlock

  // PER-OWNER PHASE TIME, per level rather than per thread, because a
  // grouped owner runs several levels and "which level is the limiting one"
  // is the question the grouping decision turns on.  Each is the wall time
  // inside the phase's own call and nothing around it -- not the poll that
  // chose it, not the lease it needed -- so the three sum to the work and
  // never to the waiting.
  //
  Counter prepare_nanos{};  // routing the older half, speculative or not
  Counter merge_nanos{};    // installing the carry and finishing
  Counter publish_nanos{};  // the publication transaction
  // THE PREPARATION HIT RATE's numerator: merges whose older half was
  // already routed when the carry arrived.  `merges - prepared_merges` is
  // what the split path failed to get ahead of, and `preparations -
  // prepared_merges` is preparation that was done and then not used by the
  // time the counter was read -- at most one per level, since a level holds
  // one job.
  Counter prepared_merges{};
  // THE PER-DIGIT JOB COST.  A job is one carry absorbed
  // at one digit: its preparation, its install and finish, and its
  // publication, recorded when it publishes.  Indexed by digit, which at the
  // top is always D.  Grouping and scheduling are judged on these rather than
  // on the phase totals above, because a middle level's digit-j work is
  // linear in j, so its heaviest carry costs about twice its mean.  An
  // adoption is not a job and is not counted.
  Counter job_count[kMaxLevelDigit + 1] = {};
  Counter job_nanos[kMaxLevelDigit + 1] = {};
  Counter job_max_nanos[kMaxLevelDigit + 1] = {};

  void Note(LevelBlock block) {
    ++blocked[static_cast<size_t>(block)];
  }
  uint64_t blocked_on(LevelBlock block) const {
    return blocked[static_cast<size_t>(block)];
  }
};

using LevelStats = LevelStatsValues<uint64_t>;

// One phase's wall time, added to its counter when the phase returns.  A
// scope guard rather than two calls, because the phases below throw: a
// failed merge's time still belongs to the merge, and a counter that were
// only updated on the success path would quietly under-report exactly the
// runs somebody is profiling.
// `job`, when given, also accumulates the time into the level's current
// job, whose total is recorded per digit when it publishes.
class PhaseTimer {
 public:
  // `phase`, when given, is the top's current merge record's field for this
  // phase (TopMergeRecord, cpu_byteslice_level_arena_top_log.hpp).
  explicit PhaseTimer(LevelCounter* nanos, uint64_t* job = nullptr,
                      uint64_t* phase = nullptr)
      : nanos_(nanos), job_(job), phase_(phase),
        start_(std::chrono::steady_clock::now()) {}
  ~PhaseTimer() {
    const uint64_t elapsed = static_cast<uint64_t>(
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            std::chrono::steady_clock::now() - start_)
            .count());
    nanos_->Add(elapsed);
    if (job_ != nullptr) *job_ += elapsed;
    if (phase_ != nullptr) *phase_ += elapsed;
  }
  PhaseTimer(const PhaseTimer&) = delete;
  PhaseTimer& operator=(const PhaseTimer&) = delete;

 private:
  LevelCounter* nanos_;
  uint64_t* job_;
  uint64_t* phase_;
  std::chrono::steady_clock::time_point start_;
};

// ---------------------------------------------------------------------------
// What a publication says about a table
// ---------------------------------------------------------------------------
//
// One spelling for LevelState and the synchronous mode
// (cpu_byteslice_level_arena_synchronous.hpp), which publish the same tables
// from different storage.

// The access positions one carry into `level` covers.
inline uint64_t LevelCarryPositions(const LevelArenaGeometry& geometry,
                                    unsigned level) {
  return CheckedMul(geometry.PrefixProduct(level), geometry.PrefixPositions(),
                    "carry positions");
}

// The public half of a table `level` publishes at `digit` under `family` --
// its nonce, window and probe shape.  Identity, occupancy and storage are the
// caller's.
inline void DescribeLevelTable(const LevelArenaGeometry& geometry,
                               unsigned level, const Family& family,
                               unsigned digit, const MergeShape& shape,
                               PublishedTable* out) {
  out->family = family;
  out->family_id = FamilyId(family);
  out->nonce = FamilyNonce(family);
  out->window_end = FamilyWindowEnd(geometry, family);
  // The top compacts everything it has ever accepted, so its window begins
  // at 0; every other table owns the `digit` carries it merged.
  out->window_begin =
      level == geometry.TopLevel()
          ? 0
          : out->window_end - digit * LevelCarryPositions(geometry, level);
  out->index_bits = shape.block_bits;
  out->radix = shape.odd_part;
}

// THE EMPTY TOP.  A fresh engine publishes one, because a hierarchy
// with no table at all has no floor for the probe cascade: the oldest live
// window must begin at 0 (PlanWindowsLaminar), and the top is the only table
// that ever does.
//
// Its family id is L -- below 1 << 15, and so disjoint from every regular
// family, all of which have a one-based ordinal in the field above the level
// (EmptyTopFamilyId).  Its window is [0, 1): ONE access position, which is
// fewer than any real table can own (the smallest is a whole prefix, 64 s r0
// positions), so it sorts last and nests inside everything.  Zero is not
// available, because a laminar window may not be empty.
inline void DescribeEmptyTop(const LevelArenaGeometry& geometry,
                             PublishedTable* table) {
  const unsigned top = geometry.TopLevel();
  table->family = Family{top, 0};
  table->family_id = EmptyTopFamilyId(top);
  table->nonce = EmptyTopNonce(top);
  table->window_begin = 0;
  table->window_end = 1;
  table->main_buckets = geometry.TopBuckets();
  // The top's public shape is its merge shape's, like every merge's
  // publication: (K + e, 1) for a binary top.
  const MergeShape shape =
      MakeTopMergeShape(geometry.CarryBuckets(top), geometry.TopDigit());
  table->index_bits = shape.block_bits;
  table->radix = shape.odd_part;
}

// The storage a publication captures: the main and the tier's stash, whose
// inline occupancy array IS the tier's mask.
inline void FillTableStorage(PublishedTable* table, TableView main,
                             const ResidualStash* tier) {
  table->data = main.data;
  table->masks = main.masks;
  table->tier_data = tier->data;
  table->tier_masks = const_cast<uint64_t*>(&tier->masks[0]);
  table->tier_buckets = tier->num_buckets;
}

// ---------------------------------------------------------------------------
// LevelState
// ---------------------------------------------------------------------------

class LevelState {
 public:
  // Everything a level is wired to.  `receiver` is its own inbox boundary
  // (absent at level 1, which takes dense prefixes instead) and `producer` is
  // its end of the level ABOVE's boundary (absent at the top, which forwards
  // nothing).  `scratch` is this level's own transient range table (5),
  // attached for one residual pass at a time.
  struct Wiring {
    const LevelArenaGeometry* geometry = nullptr;
    const LevelArenaStashSizing* sizing = nullptr;
    LevelArenaPublisher* publisher = nullptr;
    LevelArena* arena = nullptr;
    BoundaryReceiver* receiver = nullptr;
    BoundaryProducer* producer = nullptr;
    DensePrefixRing* dense = nullptr;  // level 1 only
    LevelMergeScratch* scratch = nullptr;
    const AesTagKeys* aes_keys = nullptr;
    Layout layout;
    SubtaskBudget budget = WholeLevelMergeBudget();
    // The most lanes this level's stages run at (LevelLaneCount).
    size_t lanes = 1;
    // The engine's top merge lifecycle log (TopMergeLog): written by the top
    // level, and by level L-1 for the carry's ready stamp.  Null records
    // nothing.
    TopMergeLog* top_log = nullptr;
    // The engine's per-merge log of every level (the deamortization
    // microbenchmark).  Null records nothing and takes no stamp.
    LevelMergeLog* merge_log = nullptr;
    // PRE-ROUTING: whether a level may prepare its next job's older half before
    // that job's carry is available (the step's speculative branch).  False
    // starts every preparation only once the carry is there, inside the install
    // (LevelMergeJob::ContinueInstall); the kernels, the slots and the
    // published bytes are the same, and only WHEN the preparation runs moves.
    // A measurement's control, never a production setting.
    bool preroute = true;

    // WHOM THIS LEVEL WAKES (threading rule 8).  Each is the event of the actor
    // that may be parked waiting for the thing this level has just made
    // visible, and each is signalled only AFTER it is visible:
    //
    //   wake_receiver   the owner of level + 1, after CommitReady put a Ready
    //                   in its ring;
    //   wake_producer   the owner of level - 1, after reclamation put a credit
    //                   for one of this level's inboxes in its ring;
    //   wake_requester  at level 1 only, after the retirement notification that
    //                   lets the requester free a dense prefix slot
    //                   (threading rule 7).
    //
    // A null pointer is "nobody to tell": the inline executor has all three
    // null.  A same-group neighbour gets the group's own event -- not to wake
    // it, since a thread that is running cannot be asleep, but so that a
    // phase running later in the round stops for it (LevelGroup::ShouldStop).
    OwnerEvent* wake_receiver = nullptr;
    OwnerEvent* wake_producer = nullptr;
    OwnerEvent* wake_requester = nullptr;
  };

  // `CheckedWiring` runs FIRST -- it is the initializer of the first member --
  // because every initializer after it dereferences the wiring, and a check in
  // the constructor BODY would run after the undefined behaviour it was
  // written to prevent.  `sizing` and `aes_keys` are in it for the same
  // reason, and `aes_keys` is the one the instance's whole routing schedule
  // hangs on: every hashed placement and probe address derives from it.
  LevelState(unsigned level, const Wiring& wiring)
      : w_(CheckedWiring(wiring)), level_(level),
        top_(level == w_.geometry->Levels()),
        dense_(level == 1),
        job_(*w_.geometry, *w_.sizing, w_.layout, level, *w_.aes_keys,
             w_.lanes) {
    if (dense_ != (w_.dense != nullptr)) {
      throw std::invalid_argument(
          "level arena: level 1 takes dense prefixes and no other level does");
    }
    if ((level >= 2) != (w_.receiver != nullptr)) {
      throw std::invalid_argument(
          "level arena: every level but the first owns an inbox boundary");
    }
    if (top_ != (w_.producer == nullptr)) {
      throw std::invalid_argument(
          "level arena: every level but the top forwards to the one above");
    }
    carry_positions_ = LevelCarryPositions(*w_.geometry, level);
  }

  LevelState(const LevelState&) = delete;
  LevelState& operator=(const LevelState&) = delete;

  unsigned level() const { return level_; }
  bool top() const { return top_; }
  // THE REPORTED STATE, and why these four are atomic while the rest of
  // this object is not.  Everything else a level owns is touched by its own
  // thread alone; these are what `LevelArenaEngine::BlockedDiagnosis` reads
  // from the REQUESTER's thread when a wait hits its deadlock bound -- a
  // hierarchy that has stopped is by definition not quiescent, so there is no
  // drain to synchronize with, and a plain word read across threads is a race
  // whatever its consequences (threading rule 2).  Relaxed: a report wants the
  // numbers, not an ordering, and each of them is a single word.
  uint64_t ordinal() const { return ordinal_.load(std::memory_order_relaxed); }
  unsigned next_digit() const {
    return top_ ? w_.geometry->TopDigit()
                : w_.geometry->CarryDigit(level_, ordinal() + 1);
  }
  bool has_partial() const { return partial_.valid(); }
  const LevelSource& partial() const { return partial_; }
  size_t ready_carries() const { return ready_count_; }
  // A relaxed mirror of `job_.bound()`, restamped at the end of every step.
  // The job itself is its owner thread's, so the report reads the mirror.
  bool has_pending_job() const {
    return pending_job_.load(std::memory_order_relaxed);
  }

  bool prepared() const { return job_.bound() && job_.prepared(); }

  // ---- for the group's preemption test (LevelGroup::ShouldStop) ----------
  //
  // Asked from the owner's own thread, of members that are not running.  A
  // yes may still find the destination or a plan record missing, which costs
  // a stop that buys nothing -- as every stop did before the test existed --
  // but a no has to be right, or a phase runs on while a more urgent merge
  // waits behind it.
  //
  // Whether this level holds its next job's carry: a ready carry, or the
  // dense prefix.  It stays held until the publication, so a merge that was
  // stopped between two pieces still has it.  Of the RUNNING member, whether
  // its phase is a merge or a speculative preparation.
  bool HasCarry() const { return CarryAvailable(); }
  // Whether a step here might now start or resume a merge: a carry held or
  // still in the ring, or a completed dense prefix -- and, for a phase whose
  // every lane a helper held, a lane back or the phase ended.
  bool MayMerge() const {
    if (job_.waiting_on_helpers()) return job_.OwnerHasSharedWork();
    if (CarryAvailable()) return true;
    return w_.receiver != nullptr && w_.receiver->HasReady();
  }
  // Whether a step here might start a speculative preparation: its next
  // digit has an older half and none is prepared.  Blind to the destination.
  bool MayPrepare() const {
    return w_.preroute && MergeHasOlderHalf(top_, next_digit()) &&
           !prepared();
  }
  // Whether a step's Drain would now return an inbox credit: an inbox of this
  // level retired and past its readers at `safe_epoch`.  Asked of EVERY
  // member, the running one included: the producer below -- in this group or
  // another -- cannot publish again without the credit, and only a step of
  // this level issues it, so a phase that ran on would hold it for as long as
  // the phase lasts.  Exact, unlike the two above.
  bool OwesCredit(uint64_t safe_epoch) const {
    if (w_.receiver == nullptr) return false;
    const LevelBoundary& boundary = w_.receiver->boundary();
    for (size_t i = 0; i < boundary.slot_count(); ++i) {
      const unsigned slot = boundary.slot(i);
      if (w_.arena->State(slot) == SlotState::kRetired &&
          w_.arena->RetireEpoch(slot) <= safe_epoch) {
        return true;
      }
    }
    return false;
  }
  // The job, for the engine to attach helper threads to (LevelHelpers).
  // Helpers reach it only through LevelMergeJob::HelpOnce, which never
  // crosses a phase boundary.
  LevelMergeJob& job() { return job_; }
  const LevelMergeJob& job() const { return job_; }

  // THE DEADLINE OF THIS LEVEL'S NEXT JOB, in completed dense prefixes:
  // the requester's prefix count by which the job must
  // have published, or the requester waits.  A function of the public
  // ordinal alone, so an order by it does not depend on the request rate.
  //
  //   level 1, prefix v:     due at v + q -- the ring holds q prefixes;
  //   level l, carry v:      released when the level below published it, at
  //                          v P(l) prefixes, and due when that level next
  //                          needs the inbox the carry occupies: s P(l-1)
  //                          later at digit 1 or 2, when both inboxes may be
  //                          full, and (b_(l-1) + s) P(l-1) later otherwise
  //                          and at the top, where s is the digit at which
  //                          the level below first takes the forwarding
  //                          lease -- 2, or r + 1 after a bank-first run of
  //                          r digits (LevelArenaGeometry::ForwardingLeaseDigit).
  //
  // THE TOP IS NEVER THE SHORT CASE, whatever D is.  The short window is a
  // middle level holding an adopted P_1 in one inbox while the carry takes
  // the other; the top keeps its table in a bank and has both inboxes for
  // carries.  Its digit is D, so testing the digit alone would give D = 1
  // and 2 the middle level's window -- 96 prefixes where the top has 160 at
  // B = 8, L = 3, D = 2.
  //
  // Saturating, because the product of a large ordinal and a tall ladder's
  // prefix count is a deadline no run reaches.
  uint64_t NextJobDeadline() const {
    const uint64_t v = ordinal() + 1;
    const LevelArenaGeometry& g = *w_.geometry;
    if (dense_) return SaturatingAdd(v, g.DensePrefixes());
    const unsigned digit = top_ ? g.TopDigit() : g.CarryDigit(level_, v);
    const uint64_t below = g.PrefixProduct(level_ - 1);
    const uint64_t lease = g.ForwardingLeaseDigit(level_ - 1);
    const uint64_t spans = !top_ && digit <= 2
                               ? lease
                               : uint64_t{g.Fanout(level_ - 1)} + lease;
    return SaturatingAdd(SaturatingMul(v, g.PrefixProduct(level_)),
                         SaturatingMul(spans, below));
  }
  // 5's PERSISTENT storage for this level, as its job actually allocated it.
  const LevelArenaByteBill& job_bytes() const { return job_.bytes(); }
  LevelStats stats() const {
    LevelStats out;
    out.steps = stats_.steps;
    out.merges = stats_.merges;
    out.adoptions = stats_.adoptions;
    out.preparations = stats_.preparations;
    out.publications = stats_.publications;
    out.forwards = stats_.forwards;
    out.inbox_partials = stats_.inbox_partials;
    out.prepare_nanos = stats_.prepare_nanos;
    out.merge_nanos = stats_.merge_nanos;
    out.publish_nanos = stats_.publish_nanos;
    out.prepared_merges = stats_.prepared_merges;
    for (size_t i = 0; i < kLevelBlockCount; ++i) out.blocked[i] = stats_.blocked[i];
    for (unsigned d = 0; d <= kMaxLevelDigit; ++d) {
      out.job_count[d] = stats_.job_count[d];
      out.job_nanos[d] = stats_.job_nanos[d];
      out.job_max_nanos[d] = stats_.job_max_nanos[d];
    }
    return out;
  }
  // The reason the LAST step's Advance() stopped, which is kNone when it did
  // work.  kIdle is only ever the value before the first step.
  LevelBlock last_block() const {
    return static_cast<LevelBlock>(last_block_.load(std::memory_order_relaxed));
  }

  // Whether only reader progress can move this level, or the producer below
  // it: its last step stopped on a reader wait, or it holds an inbox whose
  // credit only its own reclamation can issue.  The second is what a parked
  // producer on kNoOutputCredit is really waiting for, and nobody else will
  // wake this level to reclaim it (LevelBlockWaitsOnReaders).  Its owner's
  // thread only; at most two acquire loads on top of the reason.
  bool WaitsOnReaders() const {
    return LevelBlockWaitsOnReaders(last_block()) || HoldsRetiredInbox();
  }

  bool HoldsRetiredInbox() const {
    if (w_.receiver == nullptr) return false;
    const LevelBoundary& boundary = w_.receiver->boundary();
    for (size_t i = 0; i < boundary.slot_count(); ++i) {
      if (w_.arena->State(boundary.slot(i)) == SlotState::kRetired) {
        return true;
      }
    }
    return false;
  }

  // ---- initialization -----------------------------------------------------

  // THE EMPTY TOP (DescribeEmptyTop says what it is).
  void PublishEmptyTop() {
    if (!top_) {
      throw std::logic_error("level arena: only the top starts out empty");
    }
    if (partial_.valid()) {
      throw std::logic_error("level arena: the top already has a table");
    }
    const unsigned bank = w_.arena->plan().top_bank[0];
    SlotLease lease;
    if (!w_.arena->TryLeaseOwn(bank, &lease)) {
      throw std::logic_error("level arena: the empty top's bank is not free");
    }
    const size_t buckets = w_.geometry->TopBuckets();
    TableView main = w_.arena->WritableMain(lease, buckets);
    // The MASKS and nothing else.  An arena is not cleared when it is
    // allocated and should not be -- a dummy lane's bytes are don't-care -- but
    // an EMPTY table has to read as empty, and occupancy is the only thing
    // that says so.  (Every later occupancy of this bank has its masks written
    // in full by the copy that fills it; see CopyAndRetagRange.)
    std::fill_n(main.masks, buckets, uint64_t{0});

    PublishedTable table;
    w_.publisher->AllocateTableIds(&table.table_id, &table.tier_table_id);
    DescribeEmptyTop(*w_.geometry, &table);
    table.owner = level_;
    table.slot = bank;
    table.generation = lease.generation;
    FillTableStorage(&table, main, w_.arena->WritableTier(lease));

    PublicationDelta delta;
    delta.Add(table);
    // The one publication that adds without removing, and the one that has no
    // plan to retire: see LevelArenaPublisher's pool bound.
    w_.publisher->Publish(delta);
    Handover(lease);
    partial_ = SourceOf(table);
    ++stats_.publications;
  }

  // ---- direct initialization (DESIGN.md, "Direct initialization") --------
  //
  // THE CARRIES THIS LEVEL IS TO HAVE ACCEPTED ALREADY.  A direct
  // initialization publishes a full top and nothing else, then continues as
  // if the hierarchy had reached that state by ordinary insertion; what makes
  // that possible is that the state IS reachable.  After H = D B^(L-1)
  // complete prefixes an ordinary run stands exactly here: level l has
  // accepted H / B^(l-1) carries, which below the top is a multiple of B, so
  // every non-top digit is zero and no level holds a partial.
  //
  // Seeding the counter rather than the storage is the whole of it -- the
  // windows, the families and the odometer are all functions of the ordinal,
  // and the canonical family coordinate (CanonicalFamily, which names a
  // nonce by public level and ordinal) makes them agree without anyone being
  // told.
  void SeedAcceptedCarries(uint64_t carries) {
    if (top_) {
      throw std::logic_error(
          "level arena: the top's carries are seeded by the publication that "
          "installs its table (PublishInitialTop)");
    }
    if (ordinal() != 0 || partial_.valid() || job_.bound() ||
        ready_count_ != 0) {
      throw std::logic_error(
          "level arena: only an untouched level can be seeded");
    }
    if (carries % w_.geometry->Fanout(level_) != 0) {
      throw std::logic_error(
          "level arena: a seeded non-top level holds no partial, so its carry "
          "count must be a whole number of full tables");
    }
    ordinal_.store(carries, std::memory_order_relaxed);
  }

  // THE INITIALIZED TOP.  `scatter(main)` writes the caller's records over
  // the destination at the load the geometry gives it and sets its occupancy;
  // everything after that is the top's ORDINARY PREPARATION, run in place
  // (LevelMergeJob::RouteInitialTop), and then one publication that swaps the
  // empty top for it.
  //
  // The publication is the same transaction every other one is (threading rule
  // 4), in the same order, with two things it alone does: it consumes the H
  // prefixes the seeded ring says are already behind it, so the composed plan
  // and the ring agree about what is live; and it removes a table -- the empty
  // top -- rather than being the one add-only publication, which is what keeps
  // the plan-record bound's argument intact.
  //
  // AN ITERATOR THAT THROWS LEAVES NOTHING PUBLISHED.  The scatter and the
  // route touch the leased bank alone, and a lease is given back by Cancel();
  // the empty top is still live and this level is still pristine, so a retry
  // is legal.
  template <class Scatter>
  void PublishInitialTop(Scatter&& scatter) {
    if (!top_) {
      throw std::logic_error(
          "level arena: direct initialization builds the top");
    }
    if (!partial_.valid()) {
      throw std::logic_error(
          "level arena: the empty top is what an initialized one replaces");
    }
    if (ordinal() != 0 || job_.bound()) {
      throw std::logic_error("level arena: this top has already run a merge");
    }
    // The bank the empty top is NOT in.  Its identity is an identity and not a
    // role (SlotSpec::index), so it is found rather than assumed.
    const unsigned empty = partial_.slot;
    const unsigned bank = w_.arena->plan().top_bank[0] == empty
                              ? w_.arena->plan().top_bank[1]
                              : w_.arena->plan().top_bank[0];
    if (!w_.arena->TryLeaseOwn(bank, &lease_)) {
      throw std::logic_error(
          "level arena: the top's other bank is not free on an untouched "
          "engine");
    }
    const size_t buckets = w_.geometry->TopBuckets();
    const unsigned digit = w_.geometry->TopDigit();
    TableView main = w_.arena->WritableMain(lease_, buckets);
    // Declared out here because the handoff below the try needs them: the
    // transaction's fallible half -- the scatter, the route and the
    // publication -- is inside, and what it produced has to outlive it.
    PublishedTable out;
    uint64_t threshold = 0;
    try {
      scatter(main);
      LevelMergeBinding binding;
      binding.ordinal = digit;  // the top has accepted D carries' worth
      binding.out = main;
      binding.out_tier = w_.arena->WritableTier(lease_);
      binding.destination_generation = lease_.generation;
      // THE SOURCE IS THE OUTPUT: the records are already where they belong
      // and only their tags and their order are missing.
      binding.older_main = main;
      binding.older_tier = nullptr;
      job_.RouteInitialTop(binding, w_.scratch, w_.budget);

      w_.publisher->AllocateTableIds(&out.table_id, &out.tier_table_id);
      DescribeLevelTable(
          *w_.geometry, level_, Family{level_, digit}, digit,
          MakeTopMergeShape(w_.geometry->CarryBuckets(level_), digit), &out);
      out.owner = level_;
      out.slot = bank;
      out.generation = lease_.generation;
      out.main_buckets = buckets;
      FillTableStorage(&out, main, w_.arena->WritableTier(lease_));

      PublicationDelta delta;
      delta.Add(out);
      delta.Remove(partial_.table_id);
      // The seeded ring says H prefixes are behind this table; the plan has
      // to say the same, or the composed view would show the requester H
      // dense prefixes that no longer exist.  Same function the engine seeds
      // the ring from, called twice rather than passed, because it is a pure
      // function of the geometry and two callers of one function cannot
      // disagree.
      delta.ConsumePrefixes(DirectInitializationSeed(*w_.geometry).prefixes);

      threshold = w_.publisher->Publish(delta);
    } catch (...) {
      // An input that threw, a route that overflowed, or a publication that
      // could not reserve what it needed.  Publish is a transaction, so
      // nothing it refused is half installed; the bank goes back -- half
      // written, which is why the lease and not just the job has to be
      // released -- the empty top is still live, and this level is still
      // pristine, so a retry is legal.
      Cancel();
      throw;
    }
    // ---- the handoff: nothing below may throw ----------------------------
    Handover(lease_);
    // ---- end of the handoff ----------------------------------------------
    if (!RetireSource(partial_.slot, partial_.generation, threshold)) {
      PublicationInvariantFailed(
          "the empty top's bank was not this level's to retire");
    }
    partial_ = SourceOf(out);
    ordinal_.store(digit, std::memory_order_relaxed);
    ++stats_.publications;
  }

  // ---- the step -----------------------------------------------------------

  // The nonblocking step.  Never waits, never takes another level's lock,
  // and returns why it stopped.  A phase it runs asks `yield` between pieces
  // and, told to, stops there; the level then holds the phase and the next
  // step resumes it (result.paused).
  LevelStepResult Step(LevelStepMode mode = LevelStepMode::kAny,
                       const PhaseYield& yield = PhaseYield{}) {
    ++stats_.steps;
    LevelStepResult result;
    paused_ = false;
    result.progressed = Drain();
    result.block = Advance(mode, yield);
    result.paused = paused_;
    result.progressed |= result.block == LevelBlock::kNone;
    last_block_.store(static_cast<uint8_t>(result.block),
                      std::memory_order_relaxed);
    pending_job_.store(job_.bound(),
                       std::memory_order_relaxed);
    stats_.Note(result.block);
    return result;
  }

  // Shutdown: give back an unpublished destination so the slot is not
  // stranded.  A prepared job's sources stay published and its output is simply
  // never announced.
  void Cancel() {
    job_nanos_ = 0;
    merge_started_ = false;
    if (job_.bound()) job_.Cancel();
    if (lease_.valid()) {
      w_.arena->AbandonLease(lease_);
      lease_ = SlotLease{};
    }
    if (w_.producer != nullptr && w_.producer->holds_lease()) {
      w_.producer->DiscardLease();
    }
    if (dense_ && took_prefix_) {
      w_.dense->UntakePrefix(prefix_index_);
      took_prefix_ = false;
    }
  }

 private:
  // Every pointer a level cannot run without, checked where the check still
  // has meaning.  Returns the wiring so it can be the first member's
  // initializer; see the constructor.
  static const Wiring& CheckedWiring(const Wiring& wiring) {
    if (wiring.geometry == nullptr || wiring.sizing == nullptr ||
        wiring.publisher == nullptr || wiring.arena == nullptr ||
        wiring.aes_keys == nullptr) {
      throw std::invalid_argument("level arena: a level needs its wiring");
    }
    // Every level's passes build a range table.
    if (wiring.scratch == nullptr) {
      throw std::invalid_argument(
          "level arena: a level's range scratch is missing");
    }
    return wiring;
  }

  // ---- draining -----------------------------------------------------------

  // Reader-safe retirements first, then ready carries (the step's first line).
  // Reclaiming before accepting is what lets a level that has just freed an
  // inbox issue the credit its producer is waiting for in the same step.
  bool Drain() {
    bool progressed = false;
    const uint64_t safe = w_.publisher->epoch().Observed();
    size_t reclaimed = 0;
    if (w_.receiver != nullptr) {
      // THE LEVEL'S ONE RECLAMATION SITE.  It reclaims every retired slot of
      // this arena -- banks as well as inboxes, since a level's arena has one
      // owner -- and credits the inbox ones back to the producer below.
      ArenaPauseAt(ArenaPause::kBeforeCreditReturn, level_);
      const size_t credited = w_.receiver->ReclaimAndCredit(safe, nullptr, &reclaimed);
      // The credit is in the producer's ring before its owner is told, which
      // is threading rule 8's signalling order applied to the one message a
      // receiving level ever sends downwards.
      if (credited != 0 && w_.wake_producer != nullptr) {
        w_.wake_producer->Signal();
      }
      if (credited != 0) ArenaPauseAt(ArenaPause::kAfterCreditReturn, level_);
    } else {
      reclaimed = w_.arena->Reclaim(safe);
    }
    progressed |= reclaimed != 0;
    // Top log: the replaced top table's storage is reclaimed once its slot
    // leaves kRetired -- this is the level's one reclamation site, so the
    // first drain that finds it past kRetired is when it came back.
    if (retire_pending_ && w_.arena->State(retire_slot_) != SlotState::kRetired) {
      w_.top_log->StampRetire(retire_cell_, retire_ordinal_, TopLogNowNanos());
      retire_pending_ = false;
    }
    if (w_.receiver != nullptr) {
      ReadyMessage message;
      while (w_.receiver->PollReady(&message)) {
        AcceptCarry(message);
        progressed = true;
      }
    }
    return progressed;
  }

  // FIFO, checked.  With one producer per boundary a carry cannot really
  // arrive out of order, so a violation here is an engine invariant break and
  // not an input; it is refused rather than absorbed, because every coordinate
  // this level derives -- digit, family, nonce, window -- is a function of the
  // ordinal.
  void AcceptCarry(const ReadyMessage& message) {
    const uint64_t expected = ordinal() + 1 + ready_count_;
    if (message.ordinal != expected) {
      throw std::logic_error(
          "level arena: a carry arrived out of order at level " +
          std::to_string(level_) + " (expected ordinal " +
          std::to_string(expected) + ", got " +
          std::to_string(message.ordinal) + ")");
    }
    if (message.main_buckets != w_.geometry->CarryBuckets(level_)) {
      throw std::logic_error(
          "level arena: an incoming carry is not U_l buckets");
    }
    if (message.family != CanonicalFamily(*w_.geometry, level_,
                                          message.ordinal)) {
      throw std::logic_error(
          "level arena: an incoming carry's nonce family is not the one its "
          "ordinal names");
    }
    if (message.window_end != CarryWindowEnd(message.ordinal) ||
        message.window_begin != message.window_end - carry_positions_) {
      throw std::logic_error(
          "level arena: an incoming carry's window is not its ordinal's");
    }
    if (ready_count_ == kMaxReady) {
      throw std::logic_error(
          "level arena: more ready carries than this level has inboxes");
    }
    ready_[ready_count_] = message;
    if ((top_ && w_.top_log != nullptr) || w_.merge_log != nullptr) {
      ready_[ready_count_].accept_ns = TopLogNowNanos();
    }
    ++ready_count_;
  }

  // ---- the three branches -------------------------------------------------

  LevelBlock Advance(LevelStepMode mode, const PhaseYield& yield) {
    // "Prefer ready merges over new speculative preparation": a
    // merge-first pass holds speculation off
    // for the duration of one pass, and nothing else about the step changes.
    // Without pre-routing nothing is ever speculative: a level with no carry
    // stops here, and its merge prepares inside the install once it has one.
    const bool speculative = mode == LevelStepMode::kAny && w_.preroute;
    const uint64_t next = ordinal() + 1;
    const CarryPlan carry = w_.geometry->PlanCarry(level_, next);

    // 1. Zero-copy adoption.  No destination, no kernel, no plan record.
    if (carry.outcome == CarryOutcome::kAdopt) {
      if (ready_count_ == 0) return LevelBlock::kNoCarry;
      Adopt();
      return LevelBlock::kNone;
    }

    const bool have_carry = CarryAvailable();
    // Nothing to run and nothing to get ahead on: an older half is what a
    // preparation routes, and a digit with none (level 1's digit 1) has no
    // work that does not need the carry.  Taking the destination anyway would
    // pin a slot -- an inbox credit of the level above, at digit B -- for a
    // merge that cannot start.
    if (!have_carry && (!speculative ||
                        !MergeHasOlderHalf(top_, carry.digit) ||
                        job_.prepared())) {
      return LevelBlock::kNoCarry;
    }

    // 2/3. Both a merge and a speculative preparation need the destination.
    const LevelBlock acquired = AcquireDestination(carry);
    if (acquired != LevelBlock::kNone) return acquired;
    if (!job_.bound()) {
      BeginJob(carry);
      if (top_ && w_.top_log != nullptr) {
        // Top log: preparation may start here (speculative) or inside the
        // install (no carry-ahead); the record starts with the job.
        cur_ = TopMergeRecord{};
        cur_.ordinal = carry.ordinal;
        cur_.prepare_start_ns = TopLogNowNanos();
        fold_at_begin_ = job_.fold_nanos();
      }
      if (w_.merge_log != nullptr) {
        mrec_ = LevelMergeRecord{};
        mrec_.prepare_start_ns = TopLogNowNanos();
        cost_at_begin_ = job_.cost();
      }
    }

    if (!have_carry) {
      // 3. Prepare this destination once, under the next ordinal's family.
      // The early return above left only a speculative step with an older
      // half and no finished preparation: a new one, or one that stopped
      // between two pieces and resumes here.
      bool done = false;
      {
        PhaseTimer timer(&stats_.prepare_nanos, &job_nanos_, PhaseSink(&cur_.prepare_active_ns));
        done = job_.ContinuePrepare(w_.budget, w_.scratch, yield);
      }
      if (!done) {
        if (job_.waiting_on_helpers()) return LevelBlock::kHelpersBusy;
        paused_ = true;
        return LevelBlock::kNone;
      }
      ++stats_.preparations;
      return LevelBlock::kNone;
    }

    // 2. The plan record is the one resource a publication cannot wait for
    // inside the mutex, so it is asked for BEFORE the merge runs rather
    // than after: a finished merge that cannot publish would hold its sources
    // and its destination for as long as the pool stayed empty.
    if (!w_.publisher->CanPublish()) return LevelBlock::kPlanRecords;
    if (!RunMerge(carry, yield)) {
      if (job_.waiting_on_helpers()) return LevelBlock::kHelpersBusy;
      paused_ = true;
    }
    return LevelBlock::kNone;
  }

  // A prefix already taken is still this level's carry (see RunMerge).
  bool CarryAvailable() const {
    return dense_ ? took_prefix_ || w_.dense->PrefixReady()
                  : ready_count_ != 0;
  }

  void Adopt() {
    const ReadyMessage message = ready_[0];
    PopReady();
    // The table stays exactly where it is, under its own identity, family and
    // window.  What changes is only who will retire it.
    partial_.table_id = message.table_id;
    partial_.owner = level_;  // its inbox is this level's arena
    partial_.slot = message.slot;
    partial_.generation = message.generation;
    partial_.main_buckets = message.main_buckets;
    ordinal_.store(message.ordinal, std::memory_order_relaxed);
    ++stats_.adoptions;
    if (w_.merge_log != nullptr) {
      LevelMergeRecord r;
      r.level = level_;
      r.digit = 1;
      r.ordinal = message.ordinal;
      r.output_buckets = message.main_buckets;
      r.adoption = true;
      r.carry_ready_ns = message.ready_ns;
      r.carry_accept_ns = message.accept_ns;
      r.merge_start_ns = r.publish_ns = TopLogNowNanos();
      w_.merge_log->Store(r);
    }
  }

  // ---- the destination ----------------------------------------------------

  // Whether this level's current partial lives inside the producer's lease
  // on the level above's inbox (an even partial) rather than in a slot of
  // this arena.  Its bytes are then read through the
  // lease and its retirement is PinUntil rather than LevelArena::Retire.
  bool PartialInLease() const {
    return partial_.valid() && partial_.owner != level_;
  }

  LevelBlock AcquireDestination(const CarryPlan& carry) {
    if (UsesForwardingLease(carry)) {
      // An inbox lease from the level above.  It may be taken before the
      // incoming carry exists: it is the same slot this merge will publish, and
      // only this producer can spend its credit.  The lease is taken at digit 2
      // and outlives the partials published inside it, so a held lease is not
      // yet a writable one: the last partial removed from it stays pinned until
      // every reader of the plan that named it has left
      // (BoundaryProducer::PinUntil, threading rule 5) -- the same wait a bank
      // has, reported under the inbox's name.  Checked every step until it
      // clears; the epoch only advances.
      if (!HasDestination(carry) && !w_.producer->TryAcquire()) {
        return LevelBlock::kNoOutputCredit;
      }
      if (!w_.producer->WritableAt(w_.publisher->epoch().Observed())) {
        return LevelBlock::kInboxRetirement;
      }
      return LevelBlock::kNone;
    }
    if (HasDestination(carry)) return LevelBlock::kNone;
    const unsigned slot = OwnDestinationSlot(carry);
    const LevelBlock shared = BankSiblingBlock(carry, slot);
    if (shared != LevelBlock::kNone) return shared;
    return AcquireOwnSlot(slot);
  }

  // Leases `slot` of this level's own arena into `lease_`, or says why not.
  LevelBlock AcquireOwnSlot(unsigned slot) {
    if (lease_.valid()) return LevelBlock::kNone;
    if (!w_.arena->TryLeaseOwn(slot, &lease_)) {
      // A destination of this level's own is either free or still pinned by
      // the readers of the plan that removed its last occupant: nothing else
      // can hold it, because the merge that filled it published and retired it
      // in one transaction.
      const SlotState state = w_.arena->State(slot);
      if (state != SlotState::kRetired) {
        throw std::logic_error(
            std::string("level arena: this level's destination is ") +
            SlotStateName(state) + ", which no lifecycle of its own reaches");
      }
      return w_.arena->spec(slot).kind == SlotKind::kInbox
                 ? LevelBlock::kInboxRetirement
                 : LevelBlock::kBankRetirement;
    }
    return LevelBlock::kNone;
  }

  // A BANK WITH TWO LIFECYCLES (the bank-first run).  The odd bank and the run
  // bank are one set of buckets, and neither's slot machine knows about the
  // other, so leasing one waits here while the other is RETIRED: its table
  // has left the plan but may still be read, and it may lie anywhere the new
  // one is about to be written.  The other may also hold this level's LIVE
  // partial -- the table this merge reads, which the placement put in
  // disjoint buckets -- and that is checked rather than trusted.
  LevelBlock BankSiblingBlock(const CarryPlan& carry, unsigned slot) const {
    const LevelPlan& plan = w_.arena->plan();
    if (plan.run_bank == kNoSlot) return LevelBlock::kNone;
    unsigned sibling = kNoSlot;
    if (slot == plan.odd_bank) sibling = plan.run_bank;
    if (slot == plan.run_bank) sibling = plan.odd_bank;
    if (sibling == kNoSlot) return LevelBlock::kNone;
    const SlotState state = w_.arena->State(sibling);
    if (state == SlotState::kRetired) return LevelBlock::kBankRetirement;
    if (state == SlotState::kFree) return LevelBlock::kNone;
    const bool live_partial = state == SlotState::kInUse &&
                              partial_.valid() && partial_.owner == level_ &&
                              partial_.slot == sibling;
    if (!live_partial) {
      throw std::logic_error(
          std::string("level arena: the other occupancy of this level's "
                      "bank is ") +
          SlotStateName(state) + " and holds no table this level reads");
    }
    if (partial_.offset < carry.destination_offset + carry.output_buckets &&
        carry.destination_offset < partial_.offset + partial_.main_buckets) {
      throw std::logic_error(
          "level arena: a bank table would be written over the live partial "
          "beside it");
    }
    return LevelBlock::kNone;
  }

  unsigned OwnDestinationSlot(const CarryPlan& carry) const {
    const LevelPlan& plan = w_.arena->plan();
    if (carry.outcome == CarryOutcome::kCompact) {
      // C is whichever top bank A is not.  The two alternate, which is why
      // SlotSpec::index is an identity and not a role.
      if (!partial_.valid()) {
        throw std::logic_error(
            "level arena: the top has no A, so it has no C either; a fresh "
            "engine publishes an empty one");
      }
      const unsigned a = partial_.slot;
      return plan.top_bank[0] == a ? plan.top_bank[1] : plan.top_bank[0];
    }
    // Every partial this level builds in its OWN arena is in its bank: an
    // odd digit in the odd bank and a bank-first run's even digit in the run
    // bank.  The other even ones are built in the lease on the level above's inbox and
    // never reach here (PlanCarry).
    unsigned slot = kNoSlot;
    switch (carry.destination_kind) {
      case SlotKind::kOddBank: slot = plan.odd_bank; break;
      case SlotKind::kRunBank: slot = plan.run_bank; break;
      default: break;
    }
    if (slot == kNoSlot) {
      throw std::logic_error(
          std::string("level arena: a destination of this level's own that "
                      "it does not have: ") +
          SlotKindName(carry.destination_kind));
    }
    return slot;
  }

  // WHICH LEASE IS THE DESTINATION IS A FUNCTION OF THE DIGIT, not of which
  // lease this level happens to be holding.  A level owns two lease-shaped
  // things -- its own bank and an inbox of the level above -- and the
  // forwarding lease DOES outlive its merges: it is held from digit 2 to
  // digit b_l while odd digits go to the bank.  Inferring
  // the destination from "whichever is live" would then write an odd partial
  // into the level above's inbox.  The carry plan says which one it is
  // (UsesForwardingLease), so it is asked.
  bool HasDestination(const CarryPlan& carry) const {
    if (UsesForwardingLease(carry)) {
      return w_.producer != nullptr && w_.producer->holds_lease();
    }
    return lease_.valid();
  }
  const SlotLease& DestinationLease(const CarryPlan& carry) const {
    return UsesForwardingLease(carry) ? w_.producer->lease() : lease_;
  }
  TableView WritableOut(const CarryPlan& carry, size_t buckets) const {
    return UsesForwardingLease(carry)
               ? w_.producer->WritableMain(buckets)
               : w_.arena->WritableMain(lease_, carry.destination_offset,
                                        buckets);
  }
  ResidualStash* WritableOutTier(const CarryPlan& carry) const {
    return UsesForwardingLease(carry) ? w_.producer->WritableTier()
                                      : w_.arena->WritableTier(lease_);
  }

  // ---- the merge ----------------------------------------------------------

  void BeginJob(const CarryPlan& carry) {
    LevelMergeBinding binding;
    binding.ordinal = carry.ordinal;
    binding.out = WritableOut(carry, carry.output_buckets);
    binding.out_tier = WritableOutTier(carry);
    binding.destination_generation = DestinationLease(carry).generation;
    if (MergeHasOlderHalf(top_, carry.digit)) {
      if (!partial_.valid()) {
        throw std::logic_error(
            "level arena: this digit absorbs an older partial and there is "
            "none");
      }
      if (PartialInLease()) {
        // P_(j-1) is an even partial inside the forwarding lease: this
        // level's own published table, in a slot that is kWriting to its
        // recipient, so it is read through the lease and not through the
        // arena's published-slot accessors.  The destination of THIS digit is
        // this level's bank (consecutive digits alternate), so the two views
        // never alias.
        binding.older_main = w_.producer->WritableMain(partial_.main_buckets);
        binding.older_tier = w_.producer->WritableTier();
      } else {
        binding.older_main = w_.arena->PublishedMain(
            partial_.slot, partial_.offset, partial_.main_buckets);
        binding.older_tier = w_.arena->PublishedTier(partial_.slot);
      }
    }
    job_.Begin(binding);
  }

  // Returns false when a phase stopped between two pieces; the next step
  // re-enters here and resumes it.  Everything before the phases is
  // idempotent for that reason: the prefix take, the carry views, the lease
  // check.
  bool RunMerge(const CarryPlan& carry, const PhaseYield& yield) {
    LevelCarry incoming;
    incoming.ordinal = carry.ordinal;
    ReadyMessage message;
    if (dense_) {
      // IDEMPOTENT.  A step that took its prefix and then threw -- a declared
      // overflow in the install or the finish, the destination check below, a
      // publication refused before its install -- still holds it, and only
      // the publication that consumes it or Cancel() lets it go.  Taking again
      // would skip it: the next prefix passes ValidateArrival, which checks
      // the ordinal and not the prefix, and its publication's
      // ConsumePrefixes(p + 2) would take prefix p out of the probe cascade
      // without its entries ever being merged.
      if (!took_prefix_) {
        (void)w_.dense->TakePrefix(&prefix_index_, &prefix_generation_);
        took_prefix_ = true;
        if (w_.merge_log != nullptr) {
          message.ready_ns = w_.dense->PrefixCompletedNs(prefix_index_);
          message.accept_ns = TopLogNowNanos();
          dense_stamps_ = message;
        }
      }
      // The stamps of the prefix taken, which a resumed step reads again.
      if (w_.merge_log != nullptr) message = dense_stamps_;
      incoming.dense_prefix = w_.dense->PrefixView(prefix_index_);
    } else {
      message = ready_[0];
      incoming.family = message.family;
      incoming.main =
          w_.arena->PublishedMain(message.slot, message.main_buckets);
      incoming.tier = w_.arena->PublishedTier(message.slot);
    }
    // The destination this job was bound to must still be the one held: a
    // lease that changed between the preparation and now would publish this
    // merge's bytes under another occupancy's descriptor (threading rule 6).
    // The job cannot check it -- it holds views, not the lease -- so the
    // owner does.
    if (job_.destination_generation() != DestinationLease(carry).generation) {
      throw std::logic_error(
          "level arena: the destination lease changed under a prepared job");
    }
    // A merge that arrives at a job already prepared is what speculative
    // preparation bought; one that does not routes its older half here, and
    // the install's own "preparation runs first if it has not" is where that
    // time lands.  Counted once, when the merge starts, since the install
    // clears the flag.
    if (!merge_started_) {
      if (job_.prepared()) ++stats_.prepared_merges;
      merge_started_ = true;
      if (top_ && w_.top_log != nullptr) {
        // Top log: the carry-dependent phases begin.  The carry stamps come
        // with its Ready message.
        cur_.merge_start_ns = TopLogNowNanos();
        cur_.prepared_ahead = job_.prepared();
        cur_.carry_ready_ns = message.ready_ns;
        cur_.carry_accept_ns = message.accept_ns;
      }
      if (w_.merge_log != nullptr) {
        mrec_.merge_start_ns = TopLogNowNanos();
        mrec_.prepared_ahead = job_.prepared();
        mrec_.carry_ready_ns = message.ready_ns;
        mrec_.carry_accept_ns = message.accept_ns;
      }
    }
    {
      PhaseTimer timer(&stats_.merge_nanos, &job_nanos_, PhaseSink(&cur_.merge_active_ns));
      if (!job_.installed() &&
          !job_.ContinueInstall(incoming, w_.budget, w_.scratch, yield)) {
        return false;
      }
      if (!job_.ContinueFinish(w_.scratch, w_.budget, yield)) return false;
    }
    merge_started_ = false;
    ++stats_.merges;
    {
      PhaseTimer timer(&stats_.publish_nanos, &job_nanos_, PhaseSink(&cur_.publish_active_ns));
      const uint64_t publish_begin =
          w_.merge_log != nullptr ? TopLogNowNanos() : 0;
      Publish(carry, message);
      if (w_.merge_log != nullptr) {
        mrec_.publish_active_ns = TopLogNowNanos() - publish_begin;
      }
    }
    if (top_ && w_.top_log != nullptr) {
      // Top log: the record is complete but for the retirement, which the
      // next drains that reclaim the replaced bank stamp.
      cur_.fold_ns = job_.fold_nanos() - fold_at_begin_;
      retire_cell_ = w_.top_log->Store(cur_);
      retire_ordinal_ = cur_.ordinal;
      retire_pending_ = true;
    }
    if (w_.merge_log != nullptr) {
      mrec_.level = level_;
      mrec_.digit = carry.digit;
      mrec_.ordinal = carry.ordinal;
      mrec_.output_buckets = carry.output_buckets;
      mrec_.prepare_end_ns = job_.prepare_end_ns();
      mrec_.cost = job_.cost().Since(cost_at_begin_);
      mrec_.job_call_ns = job_nanos_;
      w_.merge_log->Store(mrec_);
    }
    NoteJobCost(carry.digit);
    if (!dense_) PopReady();
    return true;
  }

  void NoteJobCost(unsigned digit) {
    if (digit > kMaxLevelDigit) {
      throw std::logic_error("level arena: a job's digit exceeds kMaxLevelDigit");
    }
    ++stats_.job_count[digit];
    stats_.job_nanos[digit].Add(job_nanos_);
    stats_.job_max_nanos[digit].StoreMax(job_nanos_);
    job_nanos_ = 0;
  }

  // THE PUBLICATION TRANSACTION (threading rule 4), in its one valid order:
  //
  //   validate and reserve everything fallible -- identities, the outgoing
  //     Ready's ring cell, the plan record;
  //   apply the delta to the LATEST plan and install it;
  //   complete the slot handoff and enqueue Ready;
  //   stamp the retirement threshold on every source.
  //
  // There is no allocation and no throwing validation after the install,
  // because after it the output is probeable and its sources are out of the
  // cascade: there is nothing to roll back to.
  void Publish(const CarryPlan& carry, const ReadyMessage& consumed) {
    PublishedTable out;
    w_.publisher->AllocateTableIds(&out.table_id, &out.tier_table_id);
    // FamilyNonce(job_.family()) is the job's own nonce by construction.
    DescribeLevelTable(*w_.geometry, level_, job_.family(), carry.digit,
                       job_.shape(), &out);
    out.owner = carry.destination_level;
    out.slot = DestinationLease(carry).slot;
    out.generation = DestinationLease(carry).generation;
    out.main_buckets = carry.output_buckets;
    // Captured from the WRITABLE view, which is the only one there is until
    // the handoff below -- and the handoff may not precede the install.  The
    // bytes are final: the merge has finished.
    FillTableStorage(&out, WritableOut(carry, carry.output_buckets),
                     WritableOutTier(carry));

    PublicationDelta delta;
    delta.Add(out);
    if (dense_) {
      // THE DENSE PREFIX VISIBILITY UPDATE: this is what takes the
      // source prefix out of the probe cascade.
      delta.ConsumePrefixes(prefix_index_ + 1);
    } else {
      delta.Remove(consumed.table_id);
    }
    if (partial_.valid()) delta.Remove(partial_.table_id);

    // The outgoing Ready's ring cell, reserved before the commit for the same
    // reason the plan record was: a published table with no Ready is a carry
    // the receiver never hears about, holding an inbox for the rest of the run.
    const bool forwarding = carry.outcome == CarryOutcome::kForward;
    if (forwarding) {
      ReadyMessage announce;
      announce.ordinal = carry.ordinal / w_.geometry->Fanout(level_);
      announce.table_id = out.table_id;
      announce.family = out.family;
      announce.window_begin = out.window_begin;
      announce.window_end = out.window_end;
      announce.main_buckets = out.main_buckets;
      announce.tier_buckets = out.tier_buckets;
      w_.producer->PrepareReady(announce);
    }

    ArenaPauseAt(ArenaPause::kBeforePlanInstall, level_);
    const uint64_t threshold = w_.publisher->Publish(delta);
    if (w_.merge_log != nullptr) mrec_.publish_ns = TopLogNowNanos();
    // Top log.  The top's new table is probeable here, and the table it
    // replaced (partial_, the top's A) has left the plan and is retired below
    // under this publication's threshold.  Level L-1 stamps the carry as
    // available to the top once its plan install is done.
    if (top_ && w_.top_log != nullptr) {
      cur_.publish_ns = TopLogNowNanos();
      retire_slot_ = partial_.slot;
    } else if (forwarding &&
               (w_.merge_log != nullptr ||
                (w_.top_log != nullptr &&
                 level_ + 1 == w_.geometry->TopLevel()))) {
      w_.producer->StampPendingReady(TopLogNowNanos());
    }
    // The output is probeable HERE, and its sources are already out of the
    // cascade -- but the destination slot has not been handed over and no
    // Ready has been sent.  That is the window threading rule 4 orders, and a
    // fixture that means to check it has to be able to stand in it.
    ArenaPauseAt(ArenaPause::kAfterPlanInstall, level_);

    // ---- the handoff: nothing below may throw ----------------------------
    if (forwarding) {
      w_.producer->CommitReady();
      ++stats_.forwards;
    } else if (PartialInInbox(carry)) {
      // An even partial inside the forwarding lease: no handover and no
      // Ready.  The slot stays kWriting to its recipient and the table is
      // this level's; the lease now records that the plan names it.
      w_.producer->NotePartialPublished();
      ++stats_.inbox_partials;
    } else {
      Handover(lease_);
    }
    // ---- end of the handoff ----------------------------------------------

    // The carry is in the receiver's ring and its slot is kReady, so the
    // receiving owner has everything it needs before it is told there is
    // anything (threading rule 8).  Signalling inside the handoff would
    // announce a table whose slot has not been published yet.
    if (forwarding && w_.wake_receiver != nullptr) w_.wake_receiver->Signal();
    if (forwarding) ArenaPauseAt(ArenaPause::kAfterReadyEnqueue, level_);

    if (dense_) {
      if (!w_.dense->TryNoteConsumed(prefix_index_ + 1)) {
        PublicationInvariantFailed(
            "the dense consumption mark this publication installed is outside "
            "[consumed, taken]");
      }
      // Only the REQUESTER may free a prefix slot (threading rule 7), so what
      // crosses is the threshold this publication sampled.
      if (!w_.dense->SendRetirement(
              PrefixRetirement{prefix_index_, prefix_generation_, threshold})) {
        PublicationInvariantFailed(
            "the dense retirement ring filled, though it is sized for every "
            "prefix slot and holds one notification per occupancy");
      }
      took_prefix_ = false;
      // The notification carries the threshold the requester needs, and it is
      // in the ring before the requester is woken.  A requester parked on
      // backpressure on the dense prefix ring has no other way to learn that
      // a prefix slot can come back, because only it may free one.
      if (w_.wake_requester != nullptr) w_.wake_requester->Signal();
    } else if (!RetireSource(consumed.slot, consumed.generation, threshold)) {
      PublicationInvariantFailed(
          "the consumed carry's slot was not this level's to retire");
    }
    if (PartialInLease()) {
      // The absorbed partial lived inside the forwarding lease, whose slot
      // this level may not retire (its actor is the recipient, threading
      // rule 2).
      // Its bytes are pinned in the lease instead, under this publication's
      // threshold, until the readers of the plan that named it have left.
      w_.producer->PinUntil(threshold);
    } else if (partial_.valid() &&
               !RetireSource(partial_.slot, partial_.generation, threshold)) {
      PublicationInvariantFailed(
          "the absorbed partial's slot was not this level's to retire");
    }

    ordinal_.store(carry.ordinal, std::memory_order_relaxed);
    // A forwarded table belongs to the level above from here on, so this
    // level's partial state resets; anything else IS this level's new partial
    // (and at the top, its new A).
    partial_ = forwarding ? LevelSource{}
                          : SourceOf(out, carry.destination_offset);
    ++stats_.publications;
  }

  bool RetireSource(unsigned slot, uint64_t generation, uint64_t threshold) {
    return w_.arena->Retire(slot, generation, threshold);
  }

  // A slot this level wrote itself: it is both roles, so the publish and the
  // accept are one step with no message in between.
  void Handover(SlotLease& lease) {
    if (!w_.arena->Publish(lease) ||
        !w_.arena->TryAccept(lease.slot, lease.generation)) {
      PublicationInvariantFailed(
          "a level could not take over the slot it just wrote");
    }
    lease = SlotLease{};
  }

  static uint64_t SaturatingAdd(uint64_t a, uint64_t b) {
    return a > ~uint64_t{0} - b ? ~uint64_t{0} : a + b;
  }
  static uint64_t SaturatingMul(uint64_t a, uint64_t b) {
    return b != 0 && a > ~uint64_t{0} / b ? ~uint64_t{0} : a * b;
  }

  static LevelSource SourceOf(const PublishedTable& table, size_t offset = 0) {
    LevelSource source;
    source.table_id = table.table_id;
    source.owner = table.owner;
    source.slot = table.slot;
    source.generation = table.generation;
    source.main_buckets = table.main_buckets;
    source.offset = offset;
    return source;
  }

  uint64_t CarryWindowEnd(uint64_t ordinal) const {
    return CheckedMul(ordinal, carry_positions_, "carry window");
  }

  // Aborting rather than throwing, for BoundaryProducer::CommitFailed's
  // reason: every condition here was established before the plan was
  // installed, and a caller standing past the install has nothing to unwind
  // to.
  [[noreturn]] static void PublicationInvariantFailed(const char* what) {
    std::fprintf(stderr,
                 "level arena: %s -- a publication broke an invariant its "
                 "reservation had established, after the plan naming its "
                 "output was installed. There is nothing to roll back to.\n",
                 what);
    std::abort();
  }

  void PopReady() {
    for (size_t i = 1; i < ready_count_; ++i) ready_[i - 1] = ready_[i];
    --ready_count_;
  }

  static constexpr size_t kMaxReady = 2;  // one per inbox slot

  Wiring w_;
  unsigned level_;
  bool top_;
  bool dense_;
  uint64_t carry_positions_ = 0;  // access positions in one carry at this level

  LevelMergeJob job_;
  // The current job's time so far, preparation included (NoteJobCost).
  uint64_t job_nanos_ = 0;
  // The top log's state, the top only: the merge in flight, the job's fold
  // counter when it began, and the replaced table's retirement still to
  // observe.
  uint64_t* PhaseSink(uint64_t* field) { return top_ && w_.top_log != nullptr ? field : nullptr; }
  TopMergeRecord cur_;
  uint64_t fold_at_begin_ = 0;
  bool retire_pending_ = false;
  unsigned retire_slot_ = kNoSlot;
  size_t retire_cell_ = 0;
  uint64_t retire_ordinal_ = 0;
  // The per-merge log's record in flight (Wiring::merge_log), the job's cost
  // when it was bound, and level 1's stamps of the prefix it took.
  LevelMergeRecord mrec_;
  LevelMergeCost cost_at_begin_;
  ReadyMessage dense_stamps_;
  // A merge whose phases have started and not finished: counted once
  // (prepared_merges) however many steps it takes.
  bool merge_started_ = false;
  // Set by the step that stopped a phase between two pieces.
  bool paused_ = false;
  std::atomic<uint64_t> ordinal_{0};
  LevelSource partial_;
  // At most one accepted message per physical inbox, in carry order.
  std::array<ReadyMessage, kMaxReady> ready_{};
  size_t ready_count_ = 0;
  SlotLease lease_;                  // this level's own destination, if any
  // Level 1's taken prefix, pinned from TakePrefix to the publication that
  // replaces it.
  uint64_t prefix_index_ = 0;
  uint64_t prefix_generation_ = 0;
  bool took_prefix_ = false;
  std::atomic<uint8_t> last_block_{static_cast<uint8_t>(LevelBlock::kIdle)};
  std::atomic<bool> pending_job_{false};
  LevelStatsValues<LevelCounter> stats_;
};

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
