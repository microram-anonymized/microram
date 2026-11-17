#pragma once

// OWNER THREADS AND ADJACENT-LEVEL GROUPING: who drives which levels, how a
// thread with nothing to do stops burning a core, and how the whole hierarchy
// is brought to a stop.  DESIGN.md, "Publication, readers and progress",
// describes the protocol; "Threading rules" there numbers the rules the
// comments below cite as "threading rule N".
//
// WHAT A GROUP IS.  One thread drives a contiguous run of levels.  The levels
// themselves are unchanged -- `LevelState::Step` is the same nonblocking step
// the inline executor (no owner threads; the requester drives every level at
// flush boundaries) runs -- and nothing here executes two steps for one level
// at once, which is threading rule 2's requirement that grouping preserve the
// logical roles.  What a group adds is three things and no more:
//
//   1. EARLIEST DEADLINE FIRST.  A round visits its members in order of
//      their next job's deadline on the requester's prefix clock
//      (LevelState::NextJobDeadline), ties to the lower level,
//      and every phase stops between two pieces when the group's event is
//      signalled.  So a member whose deadline is near waits for one piece of
//      whatever the thread was running, never for a whole phase, which at
//      large sizes is the difference between a requester stall of a whole
//      top phase and one of a single piece.
//   2. MERGES BEFORE SPECULATION.  A round is two sweeps: the first in
//      `kMergeFirst`, which adopts, merges and publishes but starts no new
//      preparation, and the second -- only if the first moved nothing -- in
//      `kAny`.  So a member never routes an older half while another member
//      has a carry in hand.
//   3. PARKING.  A round that moves nothing parks the thread on this group's
//      event, and never inside a member's step: a level yields its reason and
//      the group decides what to do with it (a blocked level yields to the
//      other group members; it never waits inside its step).
//
// WHICH LEVELS SHARE A THREAD is not decided here: `PlanLevelGroups` in
// cpu_byteslice_level_arena_rebuild_params.hpp divides them by a load model,
// and what this file owes is that any contiguous division from one group to
// one per level is correct.
//
// WHAT AN OWNER WAITS FOR, AND WHO WAKES IT.  Every blocked reason has exactly
// one actor behind it, and that actor signals this group's event after it has
// made the thing visible (the signalling half is in LevelState, the event is
// cpu_byteslice_level_arena_event.hpp):
//
//   kNoCarry at level 1        the requester, when a dense prefix completes
//   kNoCarry above level 1     the owner below, after CommitReady
//   kNoOutputCredit            the owner above, after it credits an inbox --
//                              which it can do only by reclaiming a retired
//                              inbox, so behind it stands the reader epoch
//   kBankRetirement            }  the REQUESTER's reader epoch, and nothing
//   kInboxRetirement           }  else: these come free when the epoch passes
//   kPlanRecords               }  a threshold and at no other moment
//
// The last three have no message to wait for, so the group registers as an
// epoch waiter before its final recheck and the requester signals every owner
// when it leaves an epoch with waiters registered (threading rule 8).
// kNoOutputCredit is the same wait one owner removed: the owner above may
// itself be parked on kNoCarry while it holds the retired inbox, and nothing
// but the epoch would wake it to reclaim.  So a group ALSO registers while any
// member holds a retired inbox (LevelState::WaitsOnReaders), whatever that
// member's own reason.  That registration is not kept in the steady state: it
// is entered only by a round that ended on one of those reasons or with a
// retired inbox outstanding, so a hierarchy that is merely busy pays nothing
// for it.
//
// QUIESCENCE. Each drain round has a ticket sampled BEFORE polling. A group
// acknowledges that ticket only on entering idle after a no-work poll, after
// recording all earlier progress. The requester checks acknowledgements, idle
// state and the round's progress baseline together under the runtime mutex.
// A productive round is repeated: a late producer may have supplied work to an
// already-idle consumer. In a round with no progress, every group looked after
// the request and none supplied new work. The requester is serialized and does
// not supply work while draining. Thus a successful round has no remaining
// producer, and subsequent idle retries cannot change the drained work state.
// Poll counts are diagnostic only; they are not quiescence acknowledgements.
//
// FAILURE AND SHUTDOWN.  A throwing step, a throwing worker-init hook
// and a stop request are one mechanism: a flag every wait's predicate tests,
// plus a wake of every event, so no wait hangs silently.  The first failure is
// kept, with its exception, and re-raised on the requester's next call; later
// ones are counted and dropped, because the first is the one that explains the
// rest.  Shutdown stops new work, wakes everything, joins every thread that
// was started -- including when construction failed partway -- and only then
// may leases be cancelled and storage released.

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <condition_variable>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <functional>
#include <mutex>
#include <stdexcept>
#include <string>
#include <thread>
#include <utility>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_epoch.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_event.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_level.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_pause.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_publication.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

// ---------------------------------------------------------------------------
// Calibration knobs
// ---------------------------------------------------------------------------

// HOW LONG AN IDLE OWNER SPINS BEFORE IT SLEEPS, in microseconds.
//
// WHY SPIN AT ALL: waking a SLEEPING owner costs a futex wake and a
// reschedule, far more than an access that does not flush, and it is paid ON
// THE REQUEST THREAD'S CRITICAL PATH whenever the requester hands a carry to
// a parked level-1 owner -- it dominates the service time of an access that
// flushes.  With no
// spin window the consumer of a boundary slot parks once per table handed
// up, which also costs rebuild capacity; a window of about a millisecond
// keeps owners awake across the gaps of a steady request stream.
//
// WHAT THE SPIN COSTS is the owner's otherwise-idle core and nothing else: it
// reads its own event word and, only while it is waiting on a retirement, the
// requester's epoch word.  No lock, no scan, no DRAM.  And the window
// restarts at every wake, so a request stream that keeps the hierarchy busy
// keeps its owners awake for as long as it flows, while an idle ORAM sleeps
// after one window.
//
// This is a calibration default, not a result: each target should screen its
// own window through the `owner_spin_ns` option.
inline constexpr unsigned kLevelArenaOwnerSpinMicros = 1000;

// ---------------------------------------------------------------------------
// The division of levels among threads
// ---------------------------------------------------------------------------

// One thread's levels: the contiguous run [first, last].
struct LevelGroupPlan {
  unsigned first = 0;
  unsigned last = 0;

  unsigned size() const { return last + 1 - first; }
  bool holds(unsigned level) const { return level >= first && level <= last; }
};

// A DIVISION OF THE LEVELS AMONG THREADS, checked: contiguous groups over
// levels 1..L, highest first, covering every level exactly once.  Whoever
// chose it -- the load heuristic (PlanLevelGroups), a tuner, a fixture -- the
// engine takes nothing else.  There are never more groups than levels: an
// owner thread with no level to drive would park forever and count against
// the plan pool's per-thread staging record for nothing.
inline void ValidateLevelGroups(unsigned levels,
                                const std::vector<LevelGroupPlan>& groups) {
  if (levels == 0) {
    throw std::invalid_argument("level arena: a hierarchy has levels");
  }
  if (groups.empty() || groups.size() > levels) {
    throw std::invalid_argument(
        "level arena: owner threads must be between one and the number of "
        "levels; a thread with no level to drive would park forever");
  }
  unsigned next = levels;  // the highest level not yet covered
  for (const LevelGroupPlan& group : groups) {
    if (group.last != next || group.first < 1 || group.first > group.last) {
      throw std::invalid_argument(
          "level arena: groups must be contiguous runs of levels, highest "
          "first, covering every level once");
    }
    next = group.first - 1;
  }
  if (next != 0) {
    throw std::invalid_argument(
        "level arena: the groups do not reach level 1");
  }
}

// ---------------------------------------------------------------------------
// Slice budgets
// ---------------------------------------------------------------------------
//
// A group that preempts cuts its members' phases into pieces, and a member
// with a nearer deadline waits for at most one piece.  How long a piece may be
// is therefore set by the most urgent member's WINDOW: how long, after its job
// becomes runnable, the requester can go on before it has to wait for that
// job.  Windows are counted in completed dense PREFIXES, the requester's own
// clock, and become time only at a request rate.

// The window of a level's tightest job, in prefixes.  Level 1 has q: the
// dense ring holds q complete prefixes, so prefix p must be consumed before
// the requester completes prefix p + q.  Level l >= 2 is tightest at digit 2,
// when both of its inboxes are full -- the adopted P_1 in one, this carry in
// the other -- and the level below needs one back as soon as it takes the
// forwarding lease again: after 2 more carries when its digit-2 partial is
// built in the lease, and after r + 1 when a bank-first run builds digits
// 2..r in its own bank (LevelArenaGeometry::ForwardingLeaseDigit), s P(l-1)
// prefixes either way.  The top has no adopted P_1 and both inboxes for
// carries, so every one of its jobs has (b_(l-1) + s) P(l-1), whatever D is
// (LevelState::NextJobDeadline says the same).
inline uint64_t LevelTightestWindowPrefixes(const LevelArenaGeometry& geometry,
                                            unsigned level) {
  if (level == 1) return geometry.DensePrefixes();
  uint64_t spans = geometry.ForwardingLeaseDigit(level - 1);
  if (level == geometry.TopLevel()) spans += geometry.Fanout(level - 1);
  return CheckedMul(spans, geometry.PrefixProduct(level - 1), "window");
}

// THE SLICE LIMIT of a group at `rate` accesses per second, in nanoseconds:
// half the tightest window among its members.  A job that becomes runnable
// while the group is busy waits for at most one piece; the other half of the
// window is left for the job itself and for members whose deadlines are
// nearer still.  The smallest level sets it -- level 1's window is only q
// prefixes -- which is why grouping neighbours keeps fine pieces confined to
// the groups that hold small levels.
inline double GroupSliceLimitNanos(const LevelArenaGeometry& geometry,
                                   const LevelGroupPlan& group, double rate) {
  if (!(rate > 0.0) || !std::isfinite(rate)) {
    throw std::invalid_argument(
        "level arena: a slice limit needs a finite positive rate");
  }
  uint64_t window = ~uint64_t{0};
  for (unsigned l = group.first; l <= group.last; ++l) {
    window = std::min(window, LevelTightestWindowPrefixes(geometry, l));
  }
  return 0.5 * double(window) * double(geometry.PrefixPositions()) / rate *
         1e9;
}

// WHAT A BUCKET TOUCH COSTS, for turning a slice limit into a budget, in
// nanoseconds per 64-byte line of the bucket.  A calibration constant: the
// cost of routing buckets that live in DRAM, fitted on one development host.
// A level that fits in cache costs less per touch, which only makes its
// pieces shorter than the limit.  It is the WORST line cost, not the average,
// since a piece that costs more than it was budgeted overruns its window; a
// target's comes from the tuner (LevelArenaRebuildCost::slice_line_picos,
// refitted by `python -m analysis.oram_bench fit-rebuild`), and this is its
// default.
inline constexpr double kSliceNanosPerTouchLine = 1.5;

// Conversion must precede neither the range check nor the finite check:
// floating-to-integer conversion outside [0, 2^64) is undefined. The upper
// bound is exact; converting UINT64_MAX to double rounds it up to 2^64.
inline size_t CheckedTouchBudget(double touches) {
  if (!(touches >= 0.0) || !std::isfinite(touches) || touches >= 0x1p64) {
    throw std::invalid_argument(
        "level arena: the rebuild touch budget must be finite and below 2^64");
  }
  return touches < 1.0 ? size_t{1} : static_cast<size_t>(touches);
}

inline size_t SliceTouches(double slice_nanos, const Layout& layout,
                           double nanos_per_line = kSliceNanosPerTouchLine) {
  if (!(slice_nanos >= 0.0) || !std::isfinite(slice_nanos) ||
      !(nanos_per_line > 0.0) || !std::isfinite(nanos_per_line)) {
    throw std::invalid_argument(
        "level arena: slice duration and line cost must be finite, with a "
        "nonnegative duration and positive line cost");
  }
  const double lines = double(layout.BucketBytes()) / 64.0;
  const double touches = slice_nanos / (lines * nanos_per_line);
  return CheckedTouchBudget(touches);
}

// ---------------------------------------------------------------------------
// The inline executor's share
// ---------------------------------------------------------------------------

// ONE LEVEL'S AVERAGE ROUTING WORK PER DENSE PREFIX, in bucket touches: its
// jobs over a whole cycle of its digits, spread over the prefixes that cycle
// spans.  Counted from the routing planners -- the older blocks' copy and
// route, the carry's install, the cross levels and the radix pass; the top's
// route, fixed merge and drop -- which are the work that grows with a level.
// The residual passes are counted apart (LevelArenaResidualPrefixTouches):
// the inline share and the rebuild cost model add them.
inline double LevelArenaPrefixTouches(const LevelArenaGeometry& geometry,
                                      const Layout& layout, unsigned level) {
  if (level < 1 || level > geometry.Levels()) {
    throw std::invalid_argument("level arena: that level is not in this "
                                "hierarchy");
  }
  const SubtaskBudget whole = WholeLevelMergeBudget();
  const size_t bucket_bytes = layout.BucketBytes();
  if (level == geometry.Levels()) {
    const auto route = [&](size_t buckets, unsigned levels) {
      SubtaskTouchCounter counter;
      PlanCopyThenRoute(0, buckets, levels, bucket_bytes, whole, &counter);
      return double(counter.touches);
    };
    const MergeShape shape =
        MakeTopMergeShape(geometry.CarryBuckets(level), geometry.TopDigit());
    // The route stops one level short and the last level runs with the
    // preparation's offers: two touches per bucket.
    double job = route(shape.out_buckets, shape.block_bits - 1) +
                 2.0 * double(shape.out_buckets);
    job += double(FixedMergeUnitTouches(shape.digit)) *
               double(shape.carry_buckets) +
           double(shape.out_buckets);  // the fixed merge and the tombstone drop
    return job / double(geometry.PrefixProduct(level));
  }
  // The direct B build deduplicates, hashes each prefix bucket, selects
  // every home, and drains rejected winners.
  const size_t z = geometry.RoutedPrefixBuckets();
  const size_t m = geometry.DensePrefixBuckets();
  const double dense =
      double(DensePrefixDedupPairs(geometry)) + 2.0 * double(m) +
      double(DenseSelectHomeTouches(static_cast<unsigned>(m))) * double(z);
  const size_t carry = geometry.CarryBuckets(level);
  const unsigned k = Log2Exact(carry);
  double cycle = 0;
  for (unsigned d = 1; d <= geometry.Fanout(level); ++d) {
    const CarryPlan plan = geometry.PlanCarry(level, d);
    if (plan.outcome == CarryOutcome::kAdopt) {
      continue;  // no copy at all
    }
    // The install: the dense build, a plain copy at digit 1, a fused
    // copy-and-retag otherwise.
    const bool separated = SeparatedSources(geometry, level, d);
    // Separated preparation installs nothing (B's region is publicly blank
    // and is not even cleared); the terminal insertion is additional work.
    // A continuation has the same pair/tuple touch counts as the original
    // routing stages.
    if (level == 1) cycle += dense;
    if (separated)
      cycle += double(FixedMergeUnitTouches(d)) * double(carry);
    else if (level != 1)
      cycle += (d == 1 ? 1.0 : 2.0) * double(carry);
    if (d == 1) continue;
    const unsigned r = d >> static_cast<unsigned>(_tzcnt_u32(d));
    const unsigned e = Log2Exact(d / r);
    SubtaskTouchCounter older;
    PlanMergeOlderBlocks(k, r, e, bucket_bytes, whole, &older);
    cycle += double(older.touches);
    for (unsigned c = k; c < k + e; ++c) {
      cycle += 2.0 * double(size_t{1} << c);  // a cross level's pairs
    }
    if (r > 1) {
      cycle += double(RadixTupleTouches(r)) * double(size_t{1} << (k + e));
    }
  }
  return cycle / (double(geometry.Fanout(level)) *
                  double(geometry.PrefixProduct(level)));
}

// ONE LEVEL'S AVERAGE RESIDUAL WORK PER DENSE PREFIX, in bucket touches: the
// passes LevelArenaPrefixTouches leaves out (LevelMergeResidualTouches), over
// the same cycle of digits.  They are not stash-sized: a DFS partition, a
// stacked leaf table's offers grow with the main.  The split form keeps the
// offers apart, for the rebuild cost model.
namespace owner_detail {
// One cycle's residual touches and the prefixes it spans.  Integer-valued
// sums, so the total below is exactly the sum of the jobs' totals.
inline std::pair<ResidualTouchSplit, double> ResidualCycle(
    const LevelArenaGeometry& geometry, const Layout& layout,
    const LevelArenaStashSizing& sizing, unsigned level) {
  if (level == geometry.Levels()) {
    return {LevelMergeResidualTouchSplit(geometry, layout, sizing, level,
                                         geometry.TopDigit(),
                                         /*top_prepare_offers=*/false),
            double(geometry.PrefixProduct(level))};
  }
  ResidualTouchSplit cycle;
  for (unsigned d = 1; d <= geometry.Fanout(level); ++d) {
    cycle += LevelMergeResidualTouchSplit(geometry, layout, sizing, level, d);
  }
  return {cycle, double(geometry.Fanout(level)) *
                     double(geometry.PrefixProduct(level))};
}
}  // namespace owner_detail

inline ResidualTouchSplit LevelArenaResidualPrefixTouchSplit(
    const LevelArenaGeometry& geometry, const Layout& layout,
    const LevelArenaStashSizing& sizing, unsigned level) {
  const auto [cycle, prefixes] =
      owner_detail::ResidualCycle(geometry, layout, sizing, level);
  return {cycle.passes / prefixes, cycle.offers / prefixes};
}

inline double LevelArenaResidualPrefixTouches(
    const LevelArenaGeometry& geometry, const Layout& layout,
    const LevelArenaStashSizing& sizing, unsigned level) {
  const auto [cycle, prefixes] =
      owner_detail::ResidualCycle(geometry, layout, sizing, level);
  return cycle.total() / prefixes;
}

// THE REBUILD'S AVERAGE WORK PER FLUSH, in bucket touches: every level's
// routing (LevelArenaPrefixTouches) and residual passes
// (LevelArenaResidualPrefixTouches), and a prefix is r0 flushes.  This is
// what the inline executor's share is a multiple of.
inline double LevelArenaFlushTouches(const LevelArenaGeometry& geometry,
                                     const Layout& layout,
                                     const LevelArenaStashSizing& sizing) {
  double per_prefix = 0;
  for (unsigned l = 1; l <= geometry.Levels(); ++l) {
    per_prefix += LevelArenaPrefixTouches(geometry, layout, l) +
                  LevelArenaResidualPrefixTouches(geometry, layout, sizing, l);
  }
  return per_prefix / double(geometry.PrefixFlushes());
}

// THE INLINE EXECUTOR'S DEFAULT SHARE, as a multiple of LevelArenaFlushTouches.
// Above 1 so that it keeps up on average, with room for the backlog a top
// compaction leaves.  Without owner threads the requester runs this much
// rebuild work at each flush instead of settling every flush, which bounds
// its worst call at a piece of work rather than a whole top compaction.  The
// count includes the residual passes, which a DFS or direct finish makes
// several times larger than the route's, so a small margin over 1 suffices.
// A calibration default; `FlushPolicy::kSettle` drives each flush to
// quiescence instead.
inline constexpr double kLevelArenaInlineWorkFactor = 1.1;

// ---------------------------------------------------------------------------
// OwnerRuntime -- cancellation, failure and quiescence, shared by every thread
// ---------------------------------------------------------------------------

class OwnerRuntime {
 public:
  // `events` is every event this runtime may have to wake: one per group, plus
  // the requester's.  It is fixed at construction because a wake-everything on
  // failure may not allocate or take a lock a failing thread might hold.
  OwnerRuntime(size_t groups, std::vector<OwnerEvent*> events)
      : groups_(groups), events_(std::move(events)), acknowledged_(groups, 0) {}

  OwnerRuntime(const OwnerRuntime&) = delete;
  OwnerRuntime& operator=(const OwnerRuntime&) = delete;

  size_t groups() const { return groups_; }

  // ---- cancellation -------------------------------------------------------

  bool stopping() const { return stopping_.load(std::memory_order_acquire); }
  bool failed() const { return failed_.load(std::memory_order_acquire); }
  // The one predicate every wait in this engine includes (threading rule 8:
  // failure wakes every requester and owner wait, so none hangs silently).
  bool cancelled() const { return stopping() || failed(); }

  void Stop() {
    {
      // Under the mutex, so that a requester already in the drain wait
      // cannot miss the store between its predicate check and its sleep.
      std::lock_guard<std::mutex> lock(mutex_);
      stopping_.store(true, std::memory_order_release);
    }
    idle_changed_.notify_all();
    WakeAll();
  }

  // THE FIRST FAILURE IS THE ONE THAT IS KEPT.  Later ones are almost always
  // consequences -- an owner whose neighbour died blocks, times out and
  // reports something about credits -- and reporting the last would name the
  // symptom instead of the cause.
  void Fail(std::exception_ptr error, const std::string& what) {
    {
      std::lock_guard<std::mutex> lock(mutex_);
      ++failures_;
      if (!first_error_) {
        first_error_ = error;
        first_what_ = what;
      }
      failed_.store(true, std::memory_order_release);
    }
    idle_changed_.notify_all();
    WakeAll();
  }

  uint64_t failures() const {
    std::lock_guard<std::mutex> lock(mutex_);
    return failures_;
  }
  std::string first_failure() const {
    std::lock_guard<std::mutex> lock(mutex_);
    return first_what_;
  }

  // Re-raise an owner's failure on the calling (requester's) thread.  The
  // original exception, not a description of it: a caller that knows what
  // `std::overflow_error` means should still be able to catch it.
  //
  // The requester calls this on every threaded access, so the healthy case is
  // one acquire load and never the mutex.  Fail() raises the flag under the
  // mutex after storing the error, so a set flag always finds it.
  void RethrowIfFailed() const {
    if (!failed()) return;
    std::exception_ptr error;
    {
      std::lock_guard<std::mutex> lock(mutex_);
      error = first_error_;
    }
    if (error) std::rethrow_exception(error);
  }

  void WakeAll() {
    for (OwnerEvent* event : events_) {
      if (event != nullptr) event->Signal();
    }
  }

  // ---- quiescence ---------------------------------------------------------

  // Recorded by the owner before it can acknowledge a no-work poll.
  void NoteProgress() { progress_.fetch_add(1, std::memory_order_release); }
  uint64_t progress() const {
    return progress_.load(std::memory_order_acquire);
  }

  struct DrainRound {
    uint64_t ticket;
    uint64_t progress;
  };

  DrainRound BeginDrainRound() {
    std::lock_guard<std::mutex> lock(mutex_);
    const uint64_t before = progress();
    const uint64_t ticket = drain_round_.fetch_add(1, std::memory_order_release) + 1;
    return {ticket, before};
  }
  uint64_t drain_round() const {
    return drain_round_.load(std::memory_order_acquire);
  }

  void EnterIdle(unsigned group, uint64_t round) {
    {
      std::lock_guard<std::mutex> lock(mutex_);
      ++idle_;
      acknowledged_[group] = round;
    }
    idle_changed_.notify_all();
  }
  void LeaveIdle() {
    std::lock_guard<std::mutex> lock(mutex_);
    --idle_;
  }

  // Return false on a productive round or deadline; cancellation is rethrown
  // by the requester. Both the predicate and validation share the lock with
  // EnterIdle/LeaveIdle, so an earlier idle observation cannot be reused.
  bool AwaitDrainRound(DrainRound round,
                       std::chrono::steady_clock::time_point deadline) {
    std::unique_lock<std::mutex> lock(mutex_);
    const bool ready = idle_changed_.wait_until(lock, deadline, [&] {
      if (cancelled()) return true;
      if (idle_ != groups_) return false;
      for (uint64_t ack : acknowledged_) {
        if (ack < round.ticket) return false;
      }
      return true;
    });
    return ready && !cancelled() && progress() == round.progress;
  }

  // ---- epoch waiters (threading rule 8) ------------------------------------
  //
  // An owner whose only remaining dependency is a reader retirement registers
  // here before its final recheck, and the requester wakes every owner when it
  // leaves an epoch with a registration outstanding.  Both halves are seq_cst
  // so that they are a Dekker pair; see ReaderEpoch::ObservedForWaiter.

  void RegisterEpochWaiter() {
    epoch_waiters_.fetch_add(1, std::memory_order_seq_cst);
  }
  void UnregisterEpochWaiter() {
    epoch_waiters_.fetch_sub(1, std::memory_order_seq_cst);
  }
  // THE REQUESTER'S SIDE, on the path of every access, which is why it is one
  // load of a line nobody writes in the steady state.
  bool HasEpochWaiters() const {
    return epoch_waiters_.load(std::memory_order_seq_cst) != 0;
  }

 private:
  const size_t groups_;
  std::vector<OwnerEvent*> events_;

  std::atomic<bool> stopping_{false};
  std::atomic<bool> failed_{false};
  alignas(64) std::atomic<uint64_t> progress_{0};
  alignas(64) std::atomic<unsigned> epoch_waiters_{0};

  // Its own line: owners lock it on every idle transition, and the requester
  // reads `epoch_waiters_` above on every access.
  alignas(64) mutable std::mutex mutex_;
  std::condition_variable idle_changed_;
  std::atomic<uint64_t> drain_round_{0};
  std::vector<uint64_t> acknowledged_;  // mutex_; one entry per group
  size_t idle_ = 0;  // mutex_
  uint64_t failures_ = 0;
  std::exception_ptr first_error_;
  std::string first_what_;
};

// ---------------------------------------------------------------------------
// LevelGroup -- one thread's levels and the loop that drives them
// ---------------------------------------------------------------------------

// What one round of polling did.
struct LevelGroupPoll {
  bool progressed = false;
  // Some member ended on a reason only the reader epoch can discharge, or
  // holds a retired inbox its producer needs back, so the park must register
  // as an epoch waiter.
  bool waits_on_readers = false;
  // A member stopped a phase between two pieces because the group's event was
  // signalled, and the round ended there.
  bool preempted = false;
  // Some member's running phase is held entirely by helper threads.  The
  // group is then not idle, whatever else it found: it must not acknowledge a
  // drain round, or Drain could return with the phase still running.
  bool helpers_busy = false;
};

class LevelGroup {
 public:
  struct Wiring {
    unsigned index = 0;  // which group this is, for the pause hook and reports
    LevelGroupPlan levels;
    std::vector<LevelState*> members;
    LevelArenaPublisher* publisher = nullptr;
    OwnerRuntime* runtime = nullptr;
    OwnerEvent* event = nullptr;
    // How long a parked owner spins before it sleeps, and how long it sleeps
    // before it looks again anyway.  The spin is a latency knob (0 is a pure
    // park, which is what a fixture observing a sleeping owner wants); the
    // retry is the safety net of cpu_byteslice_level_arena_event.hpp, and its
    // use is COUNTED so that a wake this design lost is visible.
    uint64_t spin_nanos = 0;
    std::chrono::microseconds park_retry{1000};
  };

  explicit LevelGroup(const Wiring& wiring) : w_(wiring), index_(wiring.index) {
    if (w_.publisher == nullptr || w_.runtime == nullptr ||
        w_.event == nullptr || w_.members.empty()) {
      throw std::invalid_argument("level arena: a level group needs its wiring");
    }
    if (w_.members.size() != w_.levels.size()) {
      throw std::invalid_argument(
          "level arena: a group's members are exactly its levels");
    }
    order_.resize(w_.members.size());
    deadlines_.resize(w_.members.size());
  }

  LevelGroup(const LevelGroup&) = delete;
  LevelGroup& operator=(const LevelGroup&) = delete;

  const LevelGroupPlan& levels() const { return w_.levels; }
  const OwnerWaitStats& waits() const { return waits_; }
  // THE WAIT-REASON REPORT: how many parks this group took
  // while a member was blocked on each reason, and how long they lasted.
  //
  // WHY THE REASON IS A SET AND NOT A CHOICE.  A group parks when NO member
  // can proceed, so what it is waiting on is every member's reason at once --
  // three levels blocked on three different things is one park with three
  // reasons, and picking one of them would hide the other two.  So a park
  // counts against each distinct reason its members report, the counts sum to
  // more than the parks, and that is the honest shape rather than an
  // accounting error.  The park's whole duration is charged to each, for the
  // same reason: it really did wait that long on each of them.
  uint64_t parks_blocked_on(LevelBlock block) const {
    return parks_by_reason_[static_cast<size_t>(block)].get();
  }
  uint64_t park_nanos_blocked_on(LevelBlock block) const {
    return park_nanos_by_reason_[static_cast<size_t>(block)].get();
  }
  // THE GROUP'S IDLE TIME: the wall time of every wait it entered because a
  // whole round moved nothing -- the spin and the sleep together, which
  // park_nanos alone is not -- and how many such waits there were.  A group
  // is idle exactly when none of its members has a merge or a preparation
  // it can run.
  uint64_t idle_nanos() const { return idle_nanos_.get(); }
  uint64_t idle_waits() const { return idle_waits_.get(); }
  // Completed polls, for diagnostics only.
  uint64_t polls() const { return polls_.load(std::memory_order_acquire); }
  // Rounds that ended because a member stopped a phase between two pieces.
  uint64_t preemptions() const {
    return preemptions_.load(std::memory_order_relaxed);
  }
  // What the preemption test (ShouldStop) answered, over the group's life.
  // It is asked once per step per signal, so one signal the round's steps
  // all see is counted by each of them.  Declined: no member more urgent than
  // the running one could run, and the phase went on.  For a credit: a
  // member owed its producer a credit that only its own step returns.
  uint64_t preemptions_declined() const {
    return declined_.load(std::memory_order_relaxed);
  }
  uint64_t stops_for_credit() const {
    return credit_stops_.load(std::memory_order_relaxed);
  }

  // ONE ROUND over this group's members, as Run takes it.  (The inline
  // executor has its own deadline-ordered loop in the engine, SweepInline and
  // RunFlushShare, over the same LevelState::Step.)
  //
  // `yield` is what a member's phase asks between two pieces.  A member told
  // to stop ends the round at once (out.preempted), and the next round orders
  // the members by deadline afresh, so whatever became runnable with a nearer
  // deadline than the stopped phase runs before it resumes.
  LevelGroupPoll PollOnce(const PhaseYield& yield = PhaseYield{}) {
    LevelGroupPoll out;
    // The plan pool is global and its records come back with the reader epoch,
    // so reclaiming them is every owner's business.  It is first because a
    // member can be blocked on exactly this (kPlanRecords), and it is cheap to
    // call on nothing -- see ReclaimPlans' early-out, which returns at once
    // when no plan record is retired.
    const uint64_t safe = w_.publisher->epoch().Observed();
    if (w_.publisher->ReclaimPlans(safe) != 0) out.progressed = true;
    out.progressed |= Sweep(LevelStepMode::kMergeFirst, yield, &out);
    // Nobody gets ahead while somebody could merge.
    if (!out.progressed) {
      out.progressed |= Sweep(LevelStepMode::kAny, yield, &out);
    }
    if (out.preempted) preemptions_.fetch_add(1, std::memory_order_relaxed);
    for (const LevelState* level : w_.members) {
      out.waits_on_readers |= level->WaitsOnReaders();
      out.helpers_busy |= level->last_block() == LevelBlock::kHelpersBusy;
    }
    // Diagnostic readers can observe the completed poll, but this count
    // alone does not establish quiescence.
    polls_.fetch_add(1, std::memory_order_release);
    return out;
  }

  // THE OWNER LOOP.  Poll, and park when a whole round moved nothing.
  void Run() {
    while (!w_.runtime->cancelled()) {
      // Read BEFORE the poll, always: this is the registration half of the
      // lost-wake argument in cpu_byteslice_level_arena_event.hpp, and reading
      // it after would leave the window that argument exists to close.
      const uint64_t generation = w_.event->Generation();
      const uint64_t round = w_.runtime->drain_round();
      // Sample before any retirement predicate can fail. A close between
      // that failure and waiter registration must force another poll.
      const uint64_t seen = w_.publisher->epoch().ObservedForWaiter();
      // The phases compare against the generation read ABOVE, so a signal
      // that arrived after it -- one this poll might not otherwise look at
      // until its phase ends -- stops the phase at its next piece.
      const LevelGroupPoll poll = PollOnce(PhaseYield{w_.event, generation});
      ArenaPauseAt(ArenaPause::kAfterGroupPoll, index_);
      if (poll.progressed) {
        w_.runtime->NoteProgress();
        continue;
      }
      if (w_.runtime->cancelled()) break;
      Park(generation, poll.waits_on_readers, seen, round,
           /*idle=*/!poll.helpers_busy);
    }
  }

 private:
  // The members in the order this round visits them: earliest deadline
  // first.  The deadlines are read once per sweep: stepping a member moves
  // its own, but a sweep visits each member once, so only the next sweep can
  // use that.
  void OrderMembers() {
    const size_t n = w_.members.size();
    for (size_t i = 0; i < n; ++i) {
      order_[i] = i;
      deadlines_[i] = w_.members[i]->NextJobDeadline();
    }
    // Members are stored lowest level first, so a stable sort by deadline
    // breaks ties to the lower level.  An insertion sort, in place: n is the
    // group's level count, and a poll must not allocate.
    for (size_t i = 1; i < n; ++i) {
      const size_t m = order_[i];
      size_t j = i;
      while (j > 0 && deadlines_[order_[j - 1]] > deadlines_[m]) {
        order_[j] = order_[j - 1];
        --j;
      }
      order_[j] = m;
    }
  }

  // Each step gets its own copy of the round's yield, armed with this group's
  // preemption test, because a declined signal re-arms the copy: the next
  // member tests the round's signals afresh, against members whose deadlines
  // this step may have moved.
  bool Sweep(LevelStepMode mode, const PhaseYield& yield,
             LevelGroupPoll* out) {
    bool progressed = false;
    const size_t n = w_.members.size();
    OrderMembers();
    for (size_t i = 0; i < n; ++i) {
      running_ = order_[i];
      PhaseYield step_yield = yield;
      if (step_yield.event != nullptr && step_yield.should_stop == nullptr) {
        step_yield.should_stop = &LevelGroup::ShouldStop;
        step_yield.context = this;
      }
      LevelState& level = *w_.members[running_];
      const LevelStepResult step = level.Step(mode, step_yield);
      progressed |= step.progressed;
      if (step.paused) {
        out->preempted = true;
        return true;
      }
    }
    return progressed;
  }

  // THE PREEMPTION TEST (stop a phase only when a member with an EARLIER
  // deadline can run, not on every signal), which the
  // running member's phase asks once the group's event has moved.  A stop
  // costs a whole round, and it buys something only if that round runs
  // another member before the stopped phase resumes -- which is what this
  // predicts, from the rules the round itself applies:
  //
  //   - a MERGE stops for another member that sorts before it as
  //     OrderMembers sorts -- earlier deadline, ties to the lower level --
  //     and may merge now (LevelState::MayMerge);
  //   - a SPECULATIVE preparation (its level holds no carry) stops for any
  //     member that may merge, since no one gets ahead while someone could
  //     merge, and for an earlier one that may prepare;
  //   - and either stops when a member the next round would DRAIN owes its
  //     producer a credit it can now return (LevelState::OwesCredit).  Every
  //     step drains first, so the rounds this test saves were also what
  //     returned those credits, and without it a group that holds one level
  //     runs whole phases -- long ones at the large levels -- on a credit
  //     the level below, in another group, may be blocked on.  The
  //     next round steps the running member and every member before it;
  //     after a speculative phase, which its merge-first sweep does not
  //     resume, every member.  A credit owed by one it would not reach is no
  //     reason to stop, since the round would resume the phase first;
  //   - and anything stops for cancellation.
  //
  // Deadlines are read live rather than from the round's order: only this
  // thread moves its members' ordinals, and a member that published earlier
  // in this round may have moved behind the running one.
  static bool ShouldStop(void* group) {
    return static_cast<LevelGroup*>(group)->MoreUrgentMemberMayRun();
  }

  bool MoreUrgentMemberMayRun() {
    if (w_.runtime->cancelled()) return true;
    const uint64_t safe = w_.publisher->epoch().Observed();
    const LevelState& running = *w_.members[running_];
    const uint64_t deadline = running.NextJobDeadline();
    const bool speculative = !running.HasCarry();
    for (size_t i = 0; i < w_.members.size(); ++i) {
      const LevelState& member = *w_.members[i];
      const bool self = i == running_;
      const uint64_t d = member.NextJobDeadline();
      // Members are stored lowest level first, so the index breaks ties.
      const bool earlier =
          !self && (d < deadline || (d == deadline && i < running_));
      if ((self || earlier || speculative) && member.OwesCredit(safe)) {
        credit_stops_.fetch_add(1, std::memory_order_relaxed);
        return true;
      }
      if (self) continue;
      if ((earlier || speculative) && member.MayMerge()) return true;
      if (earlier && speculative && member.MayPrepare()) return true;
    }
    declined_.fetch_add(1, std::memory_order_relaxed);
    return false;
  }

  // `idle` false parks without entering idle: the group is waiting for its
  // helpers, not out of work, so it does not acknowledge the drain round.
  void Park(uint64_t generation, bool waits_on_readers, uint64_t seen,
            uint64_t round, bool idle = true) {
    // Register, then recheck the epoch sampled BEFORE the failed poll. With
    // both sides seq_cst, either this sees a close and retries or the requester
    // sees the registration and signals. No subsequent access is required.
    if (waits_on_readers) {
      ArenaPauseAt(ArenaPause::kBeforeEpochWaiterRegistered, index_);
      w_.runtime->RegisterEpochWaiter();
      ArenaPauseAt(ArenaPause::kAfterEpochWaiterRegistered, index_);
      if (w_.publisher->epoch().ObservedForWaiter() != seen) {
        w_.runtime->UnregisterEpochWaiter();
        return;
      }
    }
    if (idle) w_.runtime->EnterIdle(index_, round);
    ArenaPauseAt(ArenaPause::kBeforeGroupPark, index_);
    // The reasons sampled BEFORE the wait, which is where they are still the
    // ones that caused it: a member woken during the wait overwrites its own
    // last_block, and a report taken afterwards would name what unblocked the
    // group rather than what held it.
    const std::chrono::steady_clock::time_point parked =
        std::chrono::steady_clock::now();
    w_.event->Wait(generation, w_.spin_nanos, w_.park_retry,
                   [&] {
                     return w_.runtime->cancelled() ||
                            (waits_on_readers &&
                             w_.publisher->epoch().Observed() != seen);
                   },
                   &waits_);
    NoteWaitReasons(parked);
    ArenaPauseAt(ArenaPause::kAfterGroupPark, index_);
    if (idle) w_.runtime->LeaveIdle();
    if (waits_on_readers) w_.runtime->UnregisterEpochWaiter();
  }

  // One park against each distinct reason its members reported; see
  // parks_blocked_on.  `kNone` is skipped -- a member that had just done work
  // is not why the group stopped -- and so is `kIdle`, which is the value
  // before a level's first step.
  void NoteWaitReasons(std::chrono::steady_clock::time_point parked) {
    const uint64_t nanos = static_cast<uint64_t>(
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            std::chrono::steady_clock::now() - parked)
            .count());
    idle_nanos_.Add(nanos);
    idle_waits_.Bump();
    bool seen_reason[kLevelBlockCount] = {};
    for (const LevelState* level : w_.members) {
      const size_t reason = static_cast<size_t>(level->last_block());
      if (reason == static_cast<size_t>(LevelBlock::kNone) ||
          reason == static_cast<size_t>(LevelBlock::kIdle) ||
          seen_reason[reason]) {
        continue;
      }
      seen_reason[reason] = true;
      parks_by_reason_[reason].Bump();
      park_nanos_by_reason_[reason].Add(nanos);
    }
  }

  Wiring w_;
  const unsigned index_;
  std::vector<size_t> order_;
  std::vector<uint64_t> deadlines_;
  OwnerWaitStats waits_;
  WaitCounter parks_by_reason_[kLevelBlockCount];
  WaitCounter park_nanos_by_reason_[kLevelBlockCount];
  WaitCounter idle_nanos_;
  WaitCounter idle_waits_;
  std::atomic<uint64_t> polls_{0};
  std::atomic<uint64_t> preemptions_{0};
  std::atomic<uint64_t> declined_{0};
  std::atomic<uint64_t> credit_stops_{0};
  size_t running_ = 0;  // the member the current step runs (Sweep)
};

// ---------------------------------------------------------------------------
// LevelHelpers -- the helper threads of one group
// ---------------------------------------------------------------------------
//
// A group may own threads beyond its owner.  A HELPER runs lanes of whatever
// shared phase of the group's jobs has one open -- lowest level first -- and
// nothing else: it never binds, installs, publishes or retires, which stay
// the owner's, and it keeps no level state of its own.  It parks on its own
// event, which a shared job signals whenever a stage opens or a lane is put
// back, and every helper of a group runs this same loop over one of these.
class LevelHelpers {
 public:
  struct Wiring {
    unsigned group = 0;
    std::vector<LevelMergeJob*> jobs;  // the group's shared jobs, lowest first
    OwnerRuntime* runtime = nullptr;
    OwnerEvent* event = nullptr;
    uint64_t spin_nanos = 0;
    std::chrono::microseconds park_retry{1000};
  };

  explicit LevelHelpers(const Wiring& wiring) : w_(wiring) {
    if (w_.runtime == nullptr || w_.event == nullptr) {
      throw std::invalid_argument("level arena: helpers need their wiring");
    }
  }

  LevelHelpers(const LevelHelpers&) = delete;
  LevelHelpers& operator=(const LevelHelpers&) = delete;

  unsigned group() const { return w_.group; }
  // Lanes the helpers ran, for reports and for the tests that must know the
  // helpers did work at all.
  uint64_t lanes_run() const {
    return lanes_run_.load(std::memory_order_relaxed);
  }
  const OwnerWaitStats& waits() const { return waits_; }

  // ONE HELPER'S LOOP.  Read the generation, look for a lane, wait for the
  // generation to change: the owners' lost-wake argument, with a stage
  // opening or a lane being put back as the signal.
  void Run() {
    while (!w_.runtime->cancelled()) {
      const uint64_t generation = w_.event->Generation();
      bool ran = false;
      for (LevelMergeJob* job : w_.jobs) {
        if (job->HelpOnce()) {
          lanes_run_.fetch_add(1, std::memory_order_relaxed);
          ran = true;
          break;
        }
      }
      if (ran) continue;
      w_.event->Wait(generation, w_.spin_nanos, w_.park_retry,
                     [&] { return w_.runtime->cancelled(); }, &waits_);
    }
  }

 private:
  Wiring w_;
  std::atomic<uint64_t> lanes_run_{0};
  OwnerWaitStats waits_;
};

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
