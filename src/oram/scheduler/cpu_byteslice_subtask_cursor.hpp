#pragma once

// RESUMING A PHASE: the cursor that preemption (stopping a level's rebuild
// so a more urgent level can run) and intra-level parallelism (several
// threads running lanes of one stage) share (src/oram/scheduler/DESIGN.md).
//
// A phase is planned once, at the whole budget, into a list of COARSE tasks:
// what the planners emit when no width binds, which is one task per range and
// one per butterfly block.  A PhaseCursor then runs that list piece by piece.
// It can stop after any piece and resume later from where it stopped, on the
// same thread or on another one.  The piece widths come from a SubtaskBudget,
// so an owner that must answer an urgent level within some time runs the same
// phase in pieces no longer than the budget allows.
//
// A PIECE IS NOT A DIFFERENT ALGORITHM, which is the property the planners
// already rest on (cpu_byteslice_subtask.hpp).  A range task cut into
// sub-ranges and run in order is the same computation.  A butterfly block is
// cut by walking the kernel's own recursion -- PlanSubnetwork's split and
// leaf rules, in PlanSubnetwork's order -- and running the leaves in order,
// which issues exactly the MergeSplit sequence the whole block would.  So the
// output is byte-identical at every budget and at every stopping point.
//
// WHY THE POSITION IS AN OBJECT AND NOT A STACK FRAME.  A phase left half
// done has to be resumable after the thread that started it has returned: to
// the requester at the end of a flush's work budget, or to a group loop that
// ran a more urgent level first.  A planner recursing on the executing
// thread's stack cannot be left and re-entered, and a second thread could not
// reach its tasks at all.  The cursor is a task index plus, inside a butterfly
// block, the recursion's position -- O(depth) frames -- so it can live in the
// job that owns the phase.

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <stdexcept>

#include "src/oram/scheduler/cpu_byteslice_subtask.hpp"
#include "src/oram/scheduler/cpu_byteslice_subtask_cost.hpp"
#include "src/oram/scheduler/cpu_byteslice_subtask_plan.hpp"

namespace microram {
namespace byteslice {

// ---------------------------------------------------------------------------
// The butterfly's recursion, resumable
// ---------------------------------------------------------------------------

// PlanSubnetwork's walk over ONE sub-network, one leaf at a time.  The split
// and leaf rules are SplitSubnetwork and SubnetworkIsLeaf, the ones the
// planner and the kernel use, and the order is the planner's: the 2^high
// contiguous low-half children, then the 2^low strided high-half ones.
//
// The stack holds one frame per recursion level.  A child always has fewer
// levels than its parent (a non-leaf has at least five, so both halves are at
// least two and at most levels - 2), so the depth is below the root's level
// count, and 64 frames cover any sub-network a size_t can address.
class SubnetworkWalk {
 public:
  // Begins the walk at `budget_touches`.  The first leaf is current() at once,
  // unless the sub-network is empty.
  void Start(size_t base, unsigned log2_stride, unsigned levels,
             size_t budget_touches) {
    budget_ = budget_touches;
    depth_ = 0;
    Push(base, log2_stride, levels);
    Advance();
  }

  bool done() const { return done_; }
  const Subtask& current() const { return current_; }

  // Moves current() to the next leaf, or sets done().
  void Advance() {
    while (depth_ > 0) {
      Frame& f = stack_[depth_ - 1];
      if (!f.expanded) {
        if (f.levels == 0) {
          --depth_;
          continue;
        }
        if (SubnetworkIsLeaf(f.levels, budget_)) {
          current_ = MakeButterflyLeafSubtask(f.base, f.log2_stride, f.levels);
          --depth_;
          done_ = false;
          return;
        }
        f.split = SplitSubnetwork(f.levels);
        f.expanded = true;
        f.high_half = false;
        f.index = 0;
      }
      if (!f.high_half) {
        if (f.index < (size_t{1} << f.split.high)) {
          const size_t child =
              f.base + (f.index++ << (f.log2_stride + f.split.low));
          Push(child, f.log2_stride, f.split.low);
          continue;
        }
        f.high_half = true;
        f.index = 0;
      }
      if (f.index < (size_t{1} << f.split.low)) {
        const size_t child = f.base + (f.index++ << f.log2_stride);
        Push(child, f.log2_stride + f.split.low, f.split.high);
        continue;
      }
      --depth_;
    }
    done_ = true;
  }

 private:
  struct Frame {
    size_t base = 0;
    unsigned log2_stride = 0;
    unsigned levels = 0;
    SubnetworkSplit split{};
    bool expanded = false;
    bool high_half = false;
    size_t index = 0;
  };

  void Push(size_t base, unsigned log2_stride, unsigned levels) {
    if (depth_ == kMaxDepth) {
      throw std::logic_error(
          "butterfly walk: a sub-network recursed deeper than 64 frames");
    }
    Frame& f = stack_[depth_++];
    f = Frame{};
    f.base = base;
    f.log2_stride = log2_stride;
    f.levels = levels;
  }

  static constexpr unsigned kMaxDepth = 64;
  Frame stack_[kMaxDepth];
  unsigned depth_ = 0;
  size_t budget_ = 0;
  Subtask current_;
  bool done_ = true;
};

// ---------------------------------------------------------------------------
// Piece widths
// ---------------------------------------------------------------------------

// How many units of a RANGE task one piece may cover at `budget`, in the
// task's own units.  These are the widths the planners pass for each kind
// (cpu_byteslice_subtask_plan.hpp), so a phase cut here runs the pieces a
// planner at this budget would have emitted.  Nothing depends on that
// agreement: any cut of a range, run in order, is the same computation.  What
// it buys is that one budget means one thing to both.
//
// kButterflySubnetwork has no width -- it is cut by SubnetworkWalk -- and
// kResidualReset is never cut: it is a loop over a handful of stash slots.
inline size_t PieceUnits(const Subtask& task, const SubtaskBudget& budget) {
  switch (task.kind) {
    case Subtask::kCopyFresher:
    case Subtask::kResidualDrain:
    case Subtask::kDropErasedTier:
    case Subtask::kDropErased:
      return budget.copy_buckets;
    case Subtask::kRetagRange:
    case Subtask::kCopyAndRetagRange:
    case Subtask::kCopyAndRetagTile:
    case Subtask::kCopyAndRetagFresher:
      return budget.copy_retag_buckets;
    case Subtask::kResidualRetag:
      return budget.retag_buckets;
    case Subtask::kRouteLevelRange:
    case Subtask::kCrossLevelRange:
      return budget.cross_pairs;
    case Subtask::kCrossLevelOffers:
    case Subtask::kButterflyLevelOffers:
      return CrossOffersPairSlice(budget, task.levels);
    case Subtask::kFixedMergeRange:
      return FixedMergePairSlice(budget, task.bit);
    case Subtask::kFixedMergeOffers:
      return FixedMergeOffersUnitSlice(budget, task.bit, task.levels);
    case Subtask::kRadixPassRange:
      return RadixDedupTupleSlice(budget, task.bit);
    case Subtask::kRadixRouteRange:
      return RadixRouteTupleSlice(budget, task.bit);
    case Subtask::kRadixPassOffers:
      return RadixOffersTupleSlice(budget, task.bit, task.levels,
                                   /*dedup=*/true);
    case Subtask::kRadixRouteOffers:
      return RadixOffersTupleSlice(budget, task.bit, task.levels,
                                   /*dedup=*/false);
    case Subtask::kResidualPoolDedup:
    case Subtask::kPrefixLogDedup:
      return budget.intersect_units;
    case Subtask::kResidualScatter:
      return ScatterGroupSlice(budget, task.bit);
    case Subtask::kResidualScatterRetag:
      return ResidualBuildGroupSlice(budget, task.bit);
    case Subtask::kResidualDfsGather:
      return ResidualBuildGroupSlice(budget, 1);
    case Subtask::kResidualDfsPartition:
      return DfsPartitionUnitSlice(task, budget.copy_buckets);
    case Subtask::kResidualSweep:
      return budget.fixed_merge_pairs;
    case Subtask::kResidualLeftoverDedup:
      return LeftoverDedupPairSlice(budget, task.levels);
    case Subtask::kDenseHomes:
      return budget.retag_buckets;
    case Subtask::kDenseSelect:
      return DenseSelectHomeSlice(budget, task.levels);
    case Subtask::kDenseDrain:
      return budget.copy_buckets;
    case Subtask::kResidualReset:
    case Subtask::kButterflySubnetwork:
      return SIZE_MAX;
  }
  return 1;
}

// What a piece costs, in the bucket touches SubtaskBudgetForTouches budgets
// in: its units times the touches of one unit of its kind.  An estimate of
// work, used to meter a budget of it (an inline flush's share of the
// rebuild), never a measurement.
inline size_t PieceTouches(const Subtask& piece) {
  const size_t units = piece.end - piece.begin;
  const size_t r = SubtaskRadixOf(piece.bit);
  switch (piece.kind) {
    case Subtask::kButterflySubnetwork:
      return SubnetworkTouches(piece.levels);
    case Subtask::kCopyAndRetagRange:
    case Subtask::kCopyAndRetagTile:
    case Subtask::kCopyAndRetagFresher:
    case Subtask::kRouteLevelRange:
    case Subtask::kCrossLevelRange:
    case Subtask::kResidualSweep:
      return 2 * units;
    case Subtask::kCrossLevelOffers:
    case Subtask::kButterflyLevelOffers:
      return (2 + 2 * size_t{piece.levels}) * units;
    case Subtask::kFixedMergeRange:
      return FixedMergeUnitTouches(piece.bit) * units;
    case Subtask::kFixedMergeOffers:
      return (FixedMergeUnitTouches(piece.bit) + r * piece.levels) * units;
    case Subtask::kRadixPassRange:
    case Subtask::kRadixRouteRange:
      return RadixTupleTouches(piece.bit) * units;
    case Subtask::kRadixPassOffers:
    case Subtask::kRadixRouteOffers:
      return (RadixTupleTouches(piece.bit) + r * piece.levels) * units;
    case Subtask::kResidualScatter:
      return ScatterFanoutTouches(piece.bit) * units;
    case Subtask::kResidualScatterRetag:
      return 2 * ScatterFanoutTouches(piece.bit) * units;
    case Subtask::kResidualDfsGather:
      return 2 * units;
    case Subtask::kResidualDfsPartition:
      return DfsPartitionPieceTouches(piece);
    case Subtask::kResidualLeftoverDedup:
      return size_t{piece.levels < 1 ? 1u : piece.levels} * units;
    case Subtask::kDenseSelect:
      return DenseSelectHomeTouches(piece.levels) * units;
    default:
      return units;
  }
}

// ---------------------------------------------------------------------------
// The planned phase: tasks, stages and lane units
// ---------------------------------------------------------------------------

// One stage of a planned phase (StageMark, in cpu_byteslice_subtask_plan.hpp):
// where its tasks and its lane units begin.  It ends where the next stage
// begins.
struct PlannedStage {
  size_t first_task = 0;
  size_t first_unit = 0;
  StageMark mark;
};

// A planned phase as the cursor reads it.  `unit_starts` holds, in order, the
// task index at which each lane unit of a by-task stage begins.
struct PhasePlanView {
  const Subtask* tasks = nullptr;
  size_t num_tasks = 0;
  const PlannedStage* stages = nullptr;
  size_t num_stages = 0;
  const size_t* unit_starts = nullptr;
  size_t num_units = 0;

  size_t StageEndTask(size_t s) const {
    return s + 1 < num_stages ? stages[s + 1].first_task : num_tasks;
  }
  size_t StageEndUnit(size_t s) const {
    return s + 1 < num_stages ? stages[s + 1].first_unit : num_units;
  }
};

// How many lanes a stage runs at, given at most `max_lanes`: one for an
// ordered stage, else no more than it has units -- whole units by task,
// individual range units by range.  A PUBLIC function of the
// plan and the configuration, never of the thread count or of occupancy.
inline size_t StageLanes(const PhasePlanView& plan, size_t s,
                         size_t max_lanes) {
  const StageMark& mark = plan.stages[s].mark;
  if (!mark.lanes || max_lanes <= 1) return 1;
  size_t units = 0;
  if (mark.by_range) {
    const Subtask& task = plan.tasks[plan.stages[s].first_task];
    units = task.end - task.begin;
  } else {
    units = plan.StageEndUnit(s) - plan.stages[s].first_unit;
  }
  return std::max<size_t>(1, std::min(max_lanes, units));
}

// ---------------------------------------------------------------------------
// One lane's position
// ---------------------------------------------------------------------------

// Where one lane of one stage has got: its next coarse task and, inside it,
// the next unit of a range or the butterfly walk's position.  It holds no
// pointer into the plan, so it can live in the job and be resumed by any
// thread that holds the lane.
class LaneCursor {
 public:
  // Puts the cursor at the start of lane `lane` of `lanes` of stage `s`: a
  // run of whole units, or a contiguous sub-range of the stage's one task.
  void Open(const PhasePlanView& plan, size_t s, size_t lanes, size_t lane) {
    const PlannedStage& st = plan.stages[s];
    const size_t stage_end = plan.StageEndTask(s);
    inside_ = false;
    lo_ = 0;
    hi_ = ~size_t{0};
    if (lanes == 1) {
      task_ = st.first_task;
      end_task_ = stage_end;
      return;
    }
    if (st.mark.by_range) {
      const Subtask& task = plan.tasks[st.first_task];
      const size_t n = task.end - task.begin;
      lo_ = task.begin + lane * n / lanes;
      hi_ = task.begin + (lane + 1) * n / lanes;
      task_ = st.first_task;
      end_task_ = st.first_task + 1;
      return;
    }
    const size_t units_end = plan.StageEndUnit(s);
    const size_t units = units_end - st.first_unit;
    const size_t u0 = st.first_unit + lane * units / lanes;
    const size_t u1 = st.first_unit + (lane + 1) * units / lanes;
    task_ = plan.unit_starts[u0];
    end_task_ = u1 < units_end ? plan.unit_starts[u1] : stage_end;
  }

  // Runs the lane's pieces in order through `run(piece)`, asking
  // `yield(piece)` after each.  Returns true once the lane is done, false
  // when `yield` said to stop with work left in the lane; `*stop` is set
  // when `yield` said to stop at all, the lane's last piece included, so a
  // caller with more lanes behind this one can stop there too.
  template <class Run, class Yield>
  bool Resume(const PhasePlanView& plan, const SubtaskBudget& budget,
              Run&& run, Yield&& yield, bool* stop) {
    *stop = false;
    while (Settle(plan, budget)) {
      const Subtask piece = Current(plan, budget);
      run(piece);
      Advance(plan, piece);
      const bool more = Settle(plan, budget);
      if (yield(piece)) {
        *stop = true;
        if (more) return false;
      }
      if (!more) return true;
    }
    return true;
  }

 private:
  // Skips exhausted tasks; false once the lane has no piece left.
  bool Settle(const PhasePlanView& plan, const SubtaskBudget& budget) {
    while (task_ < end_task_) {
      const Subtask& task = plan.tasks[task_];
      if (!inside_) Enter(task, budget);
      const bool exhausted = task.kind == Subtask::kButterflySubnetwork
                                 ? walk_.done()
                                 : at_ >= in_end_;
      if (!exhausted) return true;
      inside_ = false;
      ++task_;
    }
    return false;
  }

  void Enter(const Subtask& task, const SubtaskBudget& budget) {
    inside_ = true;
    if (task.kind == Subtask::kButterflySubnetwork) {
      walk_.Start(task.begin, task.log2_stride, task.levels,
                  budget.butterfly_touches);
    } else {
      at_ = std::max(task.begin, lo_);
      in_end_ = std::min(task.end, hi_);
    }
  }

  Subtask Current(const PhasePlanView& plan, const SubtaskBudget& budget) {
    const Subtask& task = plan.tasks[task_];
    if (task.kind == Subtask::kButterflySubnetwork) return walk_.current();
    size_t width = PieceUnits(task, budget);
    if (width == 0) width = 1;
    // `end - at > width`, not `at + width < end`: a saturated width is a
    // legal request and adding it would wrap (PlanTaggedRange's rule).
    const size_t stop = in_end_ - at_ > width ? at_ + width : in_end_;
    Subtask piece = task;
    piece.begin = at_;
    piece.end = stop;
    return piece;
  }

  void Advance(const PhasePlanView& plan, const Subtask& piece) {
    if (plan.tasks[task_].kind == Subtask::kButterflySubnetwork) {
      walk_.Advance();
    } else {
      at_ = piece.end;
    }
  }

  size_t task_ = 0;
  size_t end_task_ = 0;
  size_t lo_ = 0;
  size_t hi_ = ~size_t{0};
  bool inside_ = false;
  size_t at_ = 0;
  size_t in_end_ = 0;
  SubnetworkWalk walk_;
};

// ---------------------------------------------------------------------------
// The cursor, on one thread
// ---------------------------------------------------------------------------

// Where a phase has got: the stage, the lane within it, and the lane's own
// position.  LANES ON ONE THREAD run one after another, lane 0 first, and
// their tasks in order, so the pieces run are exactly those a one-lane stage
// runs, in exactly that order; only where each piece sheds differs, which is
// `run`'s business (it is told the lane).  A stage with several lanes calls
// `open(stage, lanes, lane)` before each lane's first piece and
// `fold(stage, lanes)` when it ends, before anything later runs.
class PhaseCursor {
 public:
  // The lane `run` is told for a piece of a one-lane stage: the phase's own
  // stashes, and nothing to fold.
  static constexpr size_t kNoLane = ~size_t{0};

  void Reset() {
    stage_ = 0;
    open_ = false;
  }

  size_t stage() const { return stage_; }

  // Runs pieces from where the cursor stands, in order, each through
  // `run(piece, lane)`, until the phase is done (returns true) or
  // `yield(piece)` answers true after a piece (returns false).  `yield` sees
  // every piece -- a caller metering work counts the last one too -- but its
  // answer after the phase's final piece is ignored.  `open`, `run` and
  // `fold` report failure by throwing; the cursor is then left where it was
  // and the phase may not be resumed.
  template <class Open, class Run, class Fold, class Yield>
  bool Resume(const PhasePlanView& plan, size_t max_lanes,
              const SubtaskBudget& budget, Open&& open, Run&& run,
              Fold&& fold, Yield&& yield) {
    bool stop = false;
    while (stage_ < plan.num_stages) {
      if (!open_) {
        lanes_ = StageLanes(plan, stage_, max_lanes);
        lane_ = 0;
        lane_cursor_.Open(plan, stage_, lanes_, lane_);
        if (lanes_ > 1) open(plan.stages[stage_], lanes_, lane_);
        open_ = true;
      } else if (stop) {
        return false;
      }
      const size_t tag = lanes_ > 1 ? lane_ : kNoLane;
      if (!lane_cursor_.Resume(
              plan, budget, [&](const Subtask& piece) { run(piece, tag); },
              yield, &stop)) {
        return false;
      }
      if (++lane_ < lanes_) {
        lane_cursor_.Open(plan, stage_, lanes_, lane_);
        open(plan.stages[stage_], lanes_, lane_);
      } else {
        if (lanes_ > 1) fold(plan.stages[stage_], lanes_);
        ++stage_;
        open_ = false;
      }
      if (stop && stage_ < plan.num_stages) return false;
    }
    return true;
  }

 private:
  size_t stage_ = 0;
  bool open_ = false;
  size_t lanes_ = 1;
  size_t lane_ = 0;
  LaneCursor lane_cursor_;
};

// The yield that never asks a phase to stop: a whole-phase run.
struct NeverYield {
  bool operator()(const Subtask&) const { return false; }
};

}  // namespace byteslice
}  // namespace microram
