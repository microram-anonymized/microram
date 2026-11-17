#pragma once

// Planning: turning one rebuild step into the sequence of subtasks that
// performs it.
//
// Each Plan* function emits the slices for one phase, in issue order, at
// whatever granularity the budget asks for.  Two of them are worth knowing
// about:
//
//   - PlanSubnetwork mirrors the butterfly kernel's own split rule and its leaf
//     stopping rule rather than inventing a cut of its own.  That is the whole
//     reason a sliced butterfly and a monolithic one produce identical tables:
//     the plan is walking the same recursion the kernel walks.
//
//   - PlanAbsorbStep handles the step where a carry's chain temporary meets a
//     level that is already at its target size.  Rather than routing into a
//     double-sized staging table and folding, it merges in place against the
//     resident table's r blocks.  The level arena plans the same shape through
//     PlanMergeOlderBlocks and PlanMergeFinish; PlanAbsorbStep itself is the
//     tests' reference.
//
// Every composite planner is ONE template over its sink, selected by overload
// resolution on the primitives below: the engine's runner, which executes each
// subtask as it is emitted, or a std::vector, which the tests compare against.
// The order the planner emits in IS the order the kernels run in, so the two
// sinks cannot disagree about the algorithm.

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <vector>

#include "src/core/release_guard.hpp"
#include "src/oram/scheduler/cpu_byteslice_subtask.hpp"
#include "src/oram/scheduler/cpu_byteslice_subtask_cost.hpp"
#include "src/oram/scheduler/cpu_byteslice_subtask_run.hpp"

namespace microram {
namespace byteslice {

// ---------------------------------------------------------------------------
// Stages
// ---------------------------------------------------------------------------
//
// A STAGE is a run of a phase's tasks that lanes may divide.  A LANE is a
// fixed, contiguous run of a stage's units that touches disjoint main buckets
// and private range-table masks (see StageMark::offer_passes), so that it can
// shed into a private stash and
// the private stashes can be folded, in lane order, into the phase's own when
// the stage ends.  The planners say where stages begin, because only they
// know what a stage's tasks share.  A sink that keeps stages (the level arena
// job's task list) records the marks; every other sink ignores them, which is
// why the planners stay templates over the sink.
struct StageMark {
  // Whether lanes may divide the stage.  False for the ORDERED stages -- the
  // residual passes, a dense builder, an initialization's retag -- whose
  // tasks append to or clear one stash, drain or range table in order.
  bool lanes = false;
  // How lanes divide it: by TASK, where each unit is a run of tasks starting
  // at a MarkLaneUnit (a copy tile with the sub-networks that route it, or
  // one sub-network), or by RANGE, where the stage is ONE task whose range
  // lanes divide into contiguous runs of units.
  bool by_range = false;
  // The residual passes (bit p for ctx.residual[p]) whose range-table
  // occupancy the stage's offers clear.  An executor dividing this stage
  // MUST give each lane a private copy, taken when the lane opens and ANDed
  // back when the stage ends.  A range entry is a candidate for exactly one
  // main bucket, lanes write disjoint main buckets, and offers only clear
  // bits, so the AND is exactly the one-lane result.  The payload stays
  // shared -- nothing writes it during an offer stage.
  uint8_t offer_passes = 0;
  // What the stage may shed into, which is what its lanes' stashes fold back
  // into: level_stashes[shed_lo, shed_hi), and the radix and merge stashes.
  unsigned shed_lo = 0;
  unsigned shed_hi = 0;
  bool radix_shed = false;
  bool merge_shed = false;
#ifdef MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER
  // OCCUPANCY OBSERVER ONLY (cpu_byteslice_level_arena_occupancy.hpp): bit p
  // names ctx.residual[p].  At the stage's first piece the job reports the
  // swept pool slots (final: nothing sheds into them any more, and no pool
  // dedup has run), the drain-only slots (final: the ridden routing pass has
  // ended) and the freshly built range table (before any offer clears it).
  uint8_t observe_swept = 0;
  uint8_t observe_drain = 0;
  uint8_t observe_range = 0;
#endif
};

inline StageMark OrderedStage() { return StageMark{}; }

// OCCUPANCY OBSERVER marks: a no-op without the macro (the arguments are
// dropped and the mark is returned unchanged), so a plan is identical to the
// unobserved one.  `PassBitsAtSite` is the active passes fused at `site`.
inline uint8_t PassBitsAtSite(const RebuildStepContext& ctx,
                              ResidualFuseSite site) {
#ifdef MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER
  uint8_t bits = 0;
  for (unsigned pass = 0; pass < kResidualPasses; ++pass) {
    const ResidualPass& rp = ctx.residual[pass];
    if (rp.active && rp.fuse == site) bits |= static_cast<uint8_t>(1u << pass);
  }
  return bits;
#else
  (void)ctx;
  (void)site;
  return 0;
#endif
}

inline StageMark ObservedMark(StageMark mark, uint8_t swept, uint8_t drain,
                              uint8_t range) {
#ifdef MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER
  mark.observe_swept = static_cast<uint8_t>(mark.observe_swept | swept);
  mark.observe_drain = static_cast<uint8_t>(mark.observe_drain | drain);
  mark.observe_range = static_cast<uint8_t>(mark.observe_range | range);
#else
  (void)swept;
  (void)drain;
  (void)range;
#endif
  return mark;
}

// Units run as a unit: `lo`/`hi` are the butterfly bits its sub-networks
// route, which are the level stashes they shed into.
inline StageMark ButterflyStage(unsigned lo, unsigned hi) {
  StageMark mark;
  mark.lanes = true;
  mark.shed_lo = lo;
  mark.shed_hi = hi;
  return mark;
}

// One task divided into contiguous ranges of units.
inline StageMark RangeStage() {
  StageMark mark;
  mark.lanes = true;
  mark.by_range = true;
  return mark;
}

namespace plan_detail {
template <typename PlanOut>
auto MarkStage(PlanOut* out, const StageMark& mark, int)
    -> decltype(out->BeginStage(mark), void()) {
  out->BeginStage(mark);
}
template <typename PlanOut>
void MarkStage(PlanOut*, const StageMark&, long) {}
template <typename PlanOut>
auto MarkLaneUnit(PlanOut* out, int) -> decltype(out->BeginLaneUnit(), void()) {
  out->BeginLaneUnit();
}
template <typename PlanOut>
void MarkLaneUnit(PlanOut*, long) {}
}  // namespace plan_detail

template <typename PlanOut>
inline void MarkStage(PlanOut* out, const StageMark& mark) {
  plan_detail::MarkStage(out, mark, 0);
}
template <typename PlanOut>
inline void MarkLaneUnit(PlanOut* out) {
  plan_detail::MarkLaneUnit(out, 0);
}

// ---------------------------------------------------------------------------
// The four sink primitives
// ---------------------------------------------------------------------------

// A synchronous phase has no need to retain its emitted tasks. This sink
// shares the vector planner's traversal and overflow behavior, with constant
// task storage even at a one-bucket budget.
template <bool CheckOverflow>
struct ImmediateSubtaskRunner {
  const RebuildStepContext& context;
  Subtask::Kind* overflowed = nullptr;
  bool ok = true;

  void push_back(const Subtask& task) {
    if (RunSubtask<CheckOverflow>(context, task)) return;
    if (ok && overflowed != nullptr) *overflowed = task.kind;
    ok = false;
  }
};

// Flat [begin, end) split into slices of at most `width`, every slice stamped
// from `prototype` (which carries any attributes beyond the range: `bit`,
// `levels`, `pass`).
template <typename PlanOut>
inline void PlanTaggedRange(Subtask prototype, size_t begin, size_t end,
                            size_t width, PlanOut* out) {
  if (width == 0) width = 1;
  size_t at = begin;
  while (at < end) {
    // `end - at > width`, not `at + width < end`: an unbounded width is a legal
    // request ("one slice, whatever it costs") and adding it would wrap.
    const size_t stop = (end - at > width) ? at + width : end;
    prototype.begin = at;
    prototype.end = stop;
    out->push_back(prototype);
    at = stop;
  }
}

// The attribute-free form.
template <typename PlanOut>
inline void PlanRange(Subtask::Kind kind, size_t begin, size_t end,
                      size_t width, PlanOut* out) {
  Subtask task;
  task.kind = kind;
  PlanTaggedRange(task, begin, end, width, out);
}

// One node of the cache-oblivious butterfly recursion, cut when it fits the
// budget.  The split and leaf rules are RouteSubnetworkRecursive's, taken from
// the same SplitSubnetwork/SubnetworkIsLeaf it uses rather than restated:
// cutting the SAME recursion tree at a frontier and running the frontier left
// to right issues exactly the leaf calls the whole call would, in exactly the
// same order, so a sliced butterfly is byte-identical to a monolithic one and
// not merely equivalent.
//
// A leaf cannot be cut further here (its flat loop interleaves two levels as
// fused quads), so a leaf that exceeds the budget is emitted anyway -- 16
// buckets over <= 4 levels, 64 bucket touches, which bounds the smallest
// piece a cursor can stop after.
template <typename PlanOut>
inline void PlanSubnetwork(size_t base, unsigned log2_stride, unsigned levels,
                           size_t budget_touches, PlanOut* out) {
  if (levels == 0) return;
  if (SubnetworkIsLeaf(levels, budget_touches)) {
    out->push_back(MakeButterflyLeafSubtask(base, log2_stride, levels));
    return;
  }
  const SubnetworkSplit split = SplitSubnetwork(levels);
  for (size_t h = 0; h < (size_t{1} << split.high); ++h) {
    PlanSubnetwork(base + (h << (log2_stride + split.low)), log2_stride,
                   split.low, budget_touches, out);
  }
  for (size_t l = 0; l < (size_t{1} << split.low); ++l) {
    PlanSubnetwork(base + (l << log2_stride), log2_stride + split.low,
                   split.high, budget_touches, out);
  }
}

// The block loop of ButterflyRouteStashCacheOblivious: route_levels below
// log2(num_buckets) splits the span into independent contiguous blocks.
// With log2_stride > 0, num_buckets counts the strided buckets, not the span.
template <typename PlanOut>
inline void PlanButterfly(size_t base, size_t num_buckets,
                          unsigned route_levels, size_t budget_touches,
                          PlanOut* out,
                          unsigned log2_stride = 0) {
  if (num_buckets <= 1 || route_levels == 0) return;
  const size_t block = size_t{1} << route_levels;
  for (size_t at = 0; at < num_buckets; at += block) {
    PlanSubnetwork(base + (at << log2_stride), log2_stride, route_levels,
                   budget_touches, out);
  }
}

// ---------------------------------------------------------------------------
// Planning
// ---------------------------------------------------------------------------

// Copy each first-phase tile group immediately before routing it, so the
// butterfly can consume the copy out of cache.  These are exactly the root's
// two child loops in RouteSubnetworkRecursive, in its order, so the output
// and the stash order are the kernel's own at any budget.  Only a KERNEL leaf
// is left untiled: its flat loop interleaves two levels as fused quads and has
// no root split to tile by.  The choice must not read the budget: the
// arena plans at a whole-phase (saturated) budget, under which the budget's
// leaf rule would call every root a leaf and silently disable the tiling.
//
// All decisions use public geometry.  Copies touch disjoint destination
// buckets; the second phase starts only after every first-phase tile has
// been copied and routed.  No kernel, stash order or touch total changes.
//
// A block is copied and re-tagged out of `older` (kCopyAndRetagRange, and
// kCopyAndRetagTile for a tile routed while it is cached).
template <typename PlanOut>
inline void PlanCopyThenRoute(
    size_t base, size_t num_buckets, unsigned route_levels,
    size_t bucket_bytes, const SubtaskBudget& budget, PlanOut* out,
    size_t max_bytes = CPU_BYTESLICE_FUSED_TILE_MAX_BYTES) {
  assert(bucket_bytes != 0);
  const Subtask::Kind whole_kind = Subtask::kCopyAndRetagRange;
  const Subtask::Kind tile_kind = Subtask::kCopyAndRetagTile;
  if (num_buckets == 0) return;
  const size_t block = size_t{1} << route_levels;
  assert(num_buckets % block == 0);
  const SubnetworkSplit split = SplitSubnetwork(route_levels);
  const size_t tile = size_t{1} << split.low;
  // Divide before multiplying so even an oversized layout cannot wrap the
  // residency check.  A zero cap always selects this fallback.
  const size_t max_buckets = max_bytes / bucket_bytes;
  if (route_levels <= kButterflyLeafLevels || tile > max_buckets) {
    // Untiled: the whole arrival, then the route.  A route past a kernel
    // leaf is spelled out one split deep -- the root's two halves, each a
    // stage of independent sub-networks, exactly the children
    // RouteSubnetworkRecursive would visit in the same order -- so that lanes
    // can divide it; a leaf route is a stage of independent blocks.
    MarkStage(out, RangeStage());
    PlanRange(whole_kind, base, base + num_buckets,
              budget.copy_retag_buckets, out);
    if (route_levels <= kButterflyLeafLevels) {
      MarkStage(out, ButterflyStage(0, route_levels));
      for (size_t at = 0; at < num_buckets; at += block) {
        MarkLaneUnit(out);
        PlanSubnetwork(base + at, 0, route_levels, budget.butterfly_touches,
                       out);
      }
      return;
    }
    for (size_t at = 0; at < num_buckets; at += block) {
      const size_t root = base + at;
      MarkStage(out, ButterflyStage(0, split.low));
      for (size_t h = 0; h < (size_t{1} << split.high); ++h) {
        MarkLaneUnit(out);
        PlanSubnetwork(root + (h << split.low), 0, split.low,
                       budget.butterfly_touches, out);
      }
      MarkStage(out, ButterflyStage(split.low, route_levels));
      for (size_t l = 0; l < tile; ++l) {
        MarkLaneUnit(out);
        PlanSubnetwork(root + l, split.low, split.high,
                       budget.butterfly_touches, out);
      }
    }
    return;
  }
  const size_t group_buckets =
      std::min(block / tile, max_buckets / tile) * tile;
  for (size_t at = 0; at < num_buckets; at += block) {
    const size_t root = base + at;
    if (group_buckets == block) {
      // The whole root fits the cap.  Keep its compact descriptor as well
      // as its frontier; spelling out the children buys no extra locality.
      // One unit, so no lane divides it.
      MarkStage(out, ButterflyStage(0, route_levels));
      MarkLaneUnit(out);
      PlanRange(tile_kind, root, root + block,
                budget.copy_retag_buckets, out);
      PlanButterfly(root, block, route_levels, budget.butterfly_touches, out);
      continue;
    }
    // The root's low half, a unit per tile group: its copy, then the
    // sub-networks that route it while it is in cache.
    MarkStage(out, ButterflyStage(0, split.low));
    for (size_t first = 0; first < block; first += group_buckets) {
      const size_t count = std::min(group_buckets, block - first);
      MarkLaneUnit(out);
      PlanRange(tile_kind, root + first, root + first + count,
                budget.copy_retag_buckets, out);
      PlanButterfly(root + first, count, split.low, budget.butterfly_touches,
                    out);
    }
    // Its high half, a unit per strided sub-network.
    MarkStage(out, ButterflyStage(split.low, route_levels));
    for (size_t l = 0; l < tile; ++l) {
      MarkLaneUnit(out);
      PlanButterfly(root + l, size_t{1} << split.high, split.high,
                    budget.butterfly_touches, out, split.low);
    }
  }
}

// One residual second chance, sliced.  The phases are strictly ordered --
// nothing can route before the scatter, and the sweep cannot start before the
// last range bucket is deduplicated -- so this emits them back to back; a
// cursor may stop between pieces, but never reorders phases of one pass.
//
// The sweep is the phase that has to be sliced: it is one pass over the MAIN
// table, i.e. the same order of work as the cross-source level it follows.
// Leaving it atomic would put an O(2^t) uninterruptible block back into the
// rebuild, whose preemption bound is the longest piece.
//
// The three helpers below are the pass's phases in the pieces a FUSED step
// needs them in -- build before the cross level, pool dedup and finish after
// it -- and PlanResidualSecondChance composes them into the standalone shape
// every other site plans.

// A slice emitter bound to one pass.
template <typename PlanOut>
inline void PlanResidualPhaseRange(unsigned pass, Subtask::Kind kind,
                                   size_t begin, size_t end, size_t width,
                                   PlanOut* out, unsigned levels = 0,
                                   unsigned bit = 0) {
  Subtask task;
  task.kind = kind;
  task.levels = levels;
  task.bit = bit;
  task.pass = static_cast<uint8_t>(pass);
  PlanTaggedRange(task, begin, end, width, out);
}

// The pool dedup alone, over the pairs one EMISSION covers.  The
// window is a public function of where in the pass this emission sits -- see
// ResidualDedupWindow -- and rides to the runner on `task.bit`, a field this
// kind does not otherwise use.  Only a pass that mixes freshness classes inside
// the window needs the phase at all; when every pair in it ranks equal the
// kernel skips them all, so emitting it would dispatch subtasks that provably
// do nothing.
template <typename PlanOut>
inline void PlanResidualPoolDedup(const RebuildStepContext& ctx,
                                  const SubtaskBudget& budget, unsigned pass,
                                  ResidualDedupWindow window, PlanOut* out) {
  const ResidualPass& rp = ctx.residual[pass];
  if (!rp.active) return;
  if (!ResidualPoolDedupNeeded(rp.rank, rp.pool_slots, rp.drain_only, window)) {
    return;
  }
  PlanResidualPhaseRange(
      pass, Subtask::kResidualPoolDedup, 0,
      ResidualPoolDedupPairs(rp.pool, rp.rank, rp.pool_slots, rp.drain_only,
                             window),
      budget.intersect_units, out, /*levels=*/0,
      /*bit=*/static_cast<unsigned>(window));
}

// Everything that turns the swept suffix of the pool into a range table: the
// DFS distributor, or a direct (or empty) plan's scatter and retag.  A pass
// whose swept capacity is zero (public) has no range table and skips all of
// it.
template <typename PlanOut>
inline void PlanResidualBuildPhases(const RebuildStepContext& ctx,
                                    const SubtaskBudget& budget, unsigned pass,
                                    PlanOut* out) {
  const ResidualPass& rp = ctx.residual[pass];
  if (!rp.active || !rp.sweep_active) return;
  const TableView distributed = DistributedResidualRange(rp);
  if (rp.direct_slots) {
    // levels=1 selects the private B tail; bit=1 prices one copy+retag.
    PlanResidualPhaseRange(pass, Subtask::kResidualScatterRetag, 0,
                           rp.direct_buckets, ResidualBuildGroupSlice(budget, 1),
                           out, /*levels=*/1, /*bit=*/1);
  }
  if (rp.dfs != nullptr || rp.dfs_price.units != 0) {
    // The DFS distributor: gather the swept pool, then its public unit list,
    // in order.  Planned from the pass's price, so a pass that is only priced
    // plans exactly what a configured one would.
    PlanResidualPhaseRange(pass, Subtask::kResidualDfsGather, 0,
                           ResidualPoolBuckets(rp.pool + rp.drain_only,
                                               DistributedPoolSlots(rp)),
                           ResidualBuildGroupSlice(budget, 1), out);
    // Charged by DfsPartitionPieceTouches: `levels` is the pass's whole
    // estimate, `bit` its unit count.
    Subtask partition;
    partition.kind = Subtask::kResidualDfsPartition;
    partition.pass = static_cast<uint8_t>(pass);
    partition.levels = static_cast<unsigned>(
        std::min<size_t>(rp.dfs_price.touches, ~0u));
    partition.bit = static_cast<unsigned>(rp.dfs_price.units);
    PlanTaggedRange(partition, 0, rp.dfs_price.units,
                    DfsPartitionUnitSlice(partition, budget.copy_buckets),
                    out);
    return;
  }
  // Not DFS: only a direct or empty plan, which routes nothing.
  if (rp.plan.range_bits != 0) {
    throw std::logic_error(
        "a residual pass whose range plan routes needs a DFS workspace");
  }
  const unsigned fanout =
      static_cast<unsigned>(ResidualScatterFanout(rp.plan));
  PlanResidualPhaseRange(pass, Subtask::kResidualScatter, 0,
                         ResidualScatterGroups(distributed, rp.plan),
                         ScatterGroupSlice(budget, fanout), out,
                         /*levels=*/0, fanout);
  PlanResidualPhaseRange(pass, Subtask::kResidualRetag, 0,
                         distributed.num_buckets, budget.retag_buckets, out);
}

// The offer WEIGHT of one pass: touches per output bucket -- two for a
// class-marked set (its two masked compare nests over one transpose), one for
// any single rule -- times the plan's GROUPS (a direct or stacked plan offers
// each bucket one candidate set per group; 1 everywhere else).
inline unsigned ResidualOfferWeight(const ResidualPass& rp) {
  const unsigned rule = rp.rule == ResidualDedupRule::kClassMark ? 2u : 1u;
  return rp.direct_slots ? static_cast<unsigned>(rp.plan.groups + rp.direct_buckets)
                         : rule * static_cast<unsigned>(rp.plan.groups);
}

// Whether the pass's finish phases include the leftover dedup
// (ResidualLeftoverDedupRange): a drain-only slot outranks a swept one, and
// there is a range table whose leftovers drain ahead of the drain-only slots.
inline bool ResidualPassHasLeftoverDedup(const ResidualPass& rp) {
  return rp.active && rp.sweep_active && rp.drain != nullptr &&
         ResidualLeftoverDedupNeeded(rp.rank, rp.pool_slots, rp.drain_only);
}

// The drain -- range leftovers first, then the drain-only slots' stash
// buckets -- and the reset.  A pass whose drain-only prefix outranks a swept
// slot puts the leftover dedup between the two halves of the drain: the
// range leftovers are then in the drain and the drain-only slots still in
// their stashes, which is where the two can meet (ResidualLeftoverDedupRange).
// No standalone pass today has such a prefix, so for them this is the one
// drain it always was.
template <typename PlanOut>
inline void PlanResidualFinishPhases(const RebuildStepContext& ctx,
                                     const SubtaskBudget& budget,
                                     unsigned pass, PlanOut* out) {
  const ResidualPass& rp = ctx.residual[pass];
  if (!rp.active) return;
  const size_t range_units = rp.sweep_active ? rp.range.num_buckets : 0;
  const size_t units = range_units + ResidualPoolBuckets(rp.pool, rp.drain_only);
  if (ResidualPassHasLeftoverDedup(rp)) {
    PlanResidualPhaseRange(pass, Subtask::kResidualDrain, 0, range_units,
                           budget.copy_buckets, out);
    const unsigned weight =
        rp.rule == ResidualDedupRule::kClassMark ? 2u : 1u;  // per class
    PlanResidualPhaseRange(
        pass, Subtask::kResidualLeftoverDedup, 0,
        ResidualLeftoverDedupUnits(*rp.drain, rp.pool, rp.drain_only),
        LeftoverDedupPairSlice(budget, weight), out, /*levels=*/weight);
    PlanResidualPhaseRange(pass, Subtask::kResidualDrain, range_units, units,
                           budget.copy_buckets, out);
  } else {
    PlanResidualPhaseRange(pass, Subtask::kResidualDrain, 0, units,
                           budget.copy_buckets, out);
  }
  if (rp.reset_slots != 0) {
    PlanResidualPhaseRange(pass, Subtask::kResidualReset, 0, rp.reset_slots,
                           rp.reset_slots, out);
  }
}

template <typename PlanOut>
inline void PlanResidualSecondChance(const RebuildStepContext& ctx,
                                     const SubtaskBudget& budget,
                                     unsigned pass, PlanOut* out) {
  const ResidualPass& rp = ctx.residual[pass];
  if (!rp.active) return;
#ifdef MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER
  // Occupancy observer: every slot is final at this pass's start, and the
  // range table is final when the build ends.  Extra stage boundaries in an
  // ordered section; they change no task and no order.
  const uint8_t pass_bit = static_cast<uint8_t>(1u << pass);
  MarkStage(out, ObservedMark(OrderedStage(), pass_bit, pass_bit, 0));
#endif
  // One emission, before the scatter, so every stash mask is still live: the
  // full square.
  PlanResidualPoolDedup(ctx, budget, pass, ResidualDedupWindow::kFull, out);
  PlanResidualBuildPhases(ctx, budget, pass, out);
#ifdef MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER
  if (rp.sweep_active) {
    MarkStage(out, ObservedMark(OrderedStage(), 0, 0, pass_bit));
  }
#endif
  if (rp.sweep_active) {
    // (main bucket, group) units: plan.groups is 1 unless the range table is
    // direct (the pool itself, one group per pool bucket) or stacked, where
    // one main bucket has a residual bucket in each sub-table.
    PlanResidualPhaseRange(pass, Subtask::kResidualSweep, 0,
                           rp.main.num_buckets * rp.plan.groups,
                           budget.fixed_merge_pairs, out);
  }
  PlanResidualFinishPhases(ctx, budget, pass, out);
}

// The two halves of a pass FUSED into some routing pass, for every pass fused
// at `site` (in pass order): the build before the routing pass -- its pool
// dedup over the swept slots alone, since the drain-only prefix is publicly
// empty until the pass runs -- and, after it, the post-pass emission over
// (anything) x drain-only and the finish phases (the drain, with the leftover
// dedup between its halves where the ranks call for one, and the reset).  A
// pass fused at `site` with NO swept capacity still gets both halves: it has
// nothing to offer, but its drain-only slots still drain and reset here.
//
// `shed` is the stash the ridden pass sheds into -- the one its runner arm
// hands the kernel.  Every fused site sheds, so a null one (a context that
// names no such stash) refuses any pass with a drain-only slot, which
// BuildResidualPassFields requires of every fused pass: a site that forgets
// its stash is refused, not waved through.  BuildResidualPassFields requires a fused pass
// to lead with a drain-only slot but cannot see WHICH stash that must be: it
// is the context's, and at a cross level it depends on the bit.  So it is
// checked here, by a throw rather than an assert, because the arena's
// contexts point into storage where a wrong slot loses records and assert()
// is not in the Release build that runs.  A shed the pass does not lead with
// is reset unread if it is swept, and never drained or reset if it is not
// listed; and only ONE pass may lead with it, since two would drain it twice.
//
// ONE PASS PER SITE is also what keeps the range tables apart.  A fused pass's range table is live from
// its prologue to its epilogue, and two passes at one site would hold theirs
// at once, so views that overlapped would corrupt each other.  Passes at
// different sites, and standalone passes, hold theirs one after another --
// each epilogue drains and resets before the next prologue builds -- so they
// may share scratch, as every arena thread's single range table does.  The
// count is therefore unconditional, not only where the site has a shed.
inline void ExpectFusedShedLeads(const RebuildStepContext& ctx,
                                 ResidualFuseSite site,
                                 const ResidualStash* shed) {
  unsigned fused = 0;
  for (unsigned pass = 0; pass < kResidualPasses; ++pass) {
    const ResidualPass& rp = ctx.residual[pass];
    if (!rp.active || rp.fuse != site) continue;
    const bool leads = shed == nullptr
                           ? rp.drain_only == 0
                           : rp.drain_only != 0 && rp.pool[0] == shed;
    if (!leads) {
      throw std::logic_error(
          "a fused residual pass does not lead with the stash the pass it "
          "rides sheds into");
    }
    if (++fused > 1) {
      throw std::logic_error(
          "two residual passes are fused at one site: they would drain the "
          "same shed and hold their range tables at once");
    }
  }
}

template <typename PlanOut>
inline void PlanFusedPassPrologue(const RebuildStepContext& ctx,
                                  const SubtaskBudget& budget,
                                  ResidualFuseSite site, PlanOut* out,
                                  const ResidualStash* shed) {
  ExpectFusedShedLeads(ctx, site, shed);
  MarkStage(out, ObservedMark(OrderedStage(), PassBitsAtSite(ctx, site), 0, 0));
  for (unsigned pass = 0; pass < kResidualPasses; ++pass) {
    const ResidualPass& rp = ctx.residual[pass];
    if (!rp.active || rp.fuse != site) continue;
    PlanResidualPoolDedup(ctx, budget, pass, ResidualDedupWindow::kSweptOnly,
                          out);
    PlanResidualBuildPhases(ctx, budget, pass, out);
  }
}

template <typename PlanOut>
inline void PlanFusedPassEpilogue(const RebuildStepContext& ctx,
                                  const SubtaskBudget& budget,
                                  ResidualFuseSite site, PlanOut* out) {
  MarkStage(out, ObservedMark(OrderedStage(), 0, PassBitsAtSite(ctx, site), 0));
  for (unsigned pass = 0; pass < kResidualPasses; ++pass) {
    const ResidualPass& rp = ctx.residual[pass];
    if (!rp.active || rp.fuse != site) continue;
    PlanResidualPoolDedup(ctx, budget, pass, ResidualDedupWindow::kDrainOnly,
                          out);
    PlanResidualFinishPhases(ctx, budget, pass, out);
  }
}

// Whether any active pass is fused at `site`.  Distinct from a nonzero
// FusedOfferWeight: a fused pass with no swept capacity offers nothing but
// still has drain-only slots to drain, so the fused planners key the
// prologue/epilogue off this and the pass KIND off the weight.
inline bool HasFusedPass(const RebuildStepContext& ctx,
                         ResidualFuseSite site) {
  for (unsigned pass = 0; pass < kResidualPasses; ++pass) {
    const ResidualPass& rp = ctx.residual[pass];
    if (rp.active && rp.fuse == site) return true;
  }
  return false;
}

// A range stage whose lanes must privatize the active fused offers' masks.
inline StageMark OfferStage(const RebuildStepContext& ctx,
                            ResidualFuseSite site) {
  static_assert(kResidualPasses <= 8, "offer_passes is one byte");
  StageMark mark = RangeStage();
  for (unsigned pass = 0; pass < kResidualPasses; ++pass) {
    const ResidualPass& rp = ctx.residual[pass];
    if (!rp.active || rp.fuse != site || !rp.sweep_active) continue;
    mark.offer_passes = static_cast<uint8_t>(mark.offer_passes | (1u << pass));
  }
#ifdef MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER
  mark.observe_range = mark.offer_passes;  // the table the prologue just built
#endif
  return mark;
}

// The passes NOT fused anywhere, planned standalone in pass order.
template <typename PlanOut>
inline void PlanStandalonePasses(const RebuildStepContext& ctx,
                                 const SubtaskBudget& budget, PlanOut* out) {
  MarkStage(out, OrderedStage());
  for (unsigned pass = 0; pass < kResidualPasses; ++pass) {
    if (ctx.residual[pass].fuse == ResidualFuseSite::kNone) {
      PlanResidualSecondChance(ctx, budget, pass, out);
    }
  }
}

// The WEIGHT of one pass's offer riding its own butterfly's last level:
// touches per output bucket, which is what kButterflyLevelOffers carries in
// `levels`.  A direct or stacked plan offers each bucket one candidate set
// per GROUP -- the standalone sweep's (bucket, group) unit space, folded per
// bucket -- so the group count multiplies, exactly as it does in
// CrossOfferWeight.
inline unsigned OwnLevelOfferWeight(const ResidualPass& rp) {
  return ResidualOfferWeight(rp);
}

// HOW THE OLDER SOURCE ARRIVES, and then its route.  Ordinarily it is copied
// into the workspace and re-tagged in one fused pass (kCopyAndRetagRange,
// tiled against the butterfly that consumes it).  A DIRECT INITIALIZATION has
// already scattered its records into that workspace, so there is nothing to
// copy and only the tags are written -- see
// RebuildStepContext::source_in_place.  Everything after the arrival is the
// same butterfly either way, which is the point of putting the choice here
// rather than in a planner of its own.
template <typename PlanOut>
inline void PlanArriveThenRoute(const RebuildStepContext& ctx, size_t base,
                                size_t num_buckets, unsigned route_levels,
                                const SubtaskBudget& budget, PlanOut* out) {
  if (!ctx.source_in_place) {
    PlanCopyThenRoute(base, num_buckets, route_levels,
                      ctx.out.layout.BucketBytes(), budget, out);
    return;
  }
  // A direct initialization's route, once: ordered, whole blocks.
  MarkStage(out, OrderedStage());
  PlanRange(Subtask::kRetagRange, base, base + num_buckets,
            budget.copy_retag_buckets, out);
  PlanButterfly(base, num_buckets, route_levels, budget.butterfly_touches,
                out);
}

// The half of a step that does not depend on T_j: copy `older` into place and
// re-tag it under the rebuild's nonce -- ONE fused pass, see
// kCopyAndRetagRange -- then run its own butterfly.  (The unfused twin,
// PrepareIncrementalUpperHalf, keeps the two passes separate; it is the test
// oracle the fused pass is checked against byte for byte, and nothing but the
// tests calls it.)  Also the fixed level's C <- A workspace preparation, with
// upper_offset = 0 -- same phases, same order, one call.
//
// Residual pass 0 belongs here.  The block's own butterfly is the one place a
// shed entry's freshness class is ambiguous at the end of the network, so it is
// offered back to its own block right away -- where the block, holding each key
// at most once, cannot contain a duplicate of it and kNoDedup is exact.  The
// same pass absorbs the SOURCE table's own second tier, which is how a finished
// level's residuals rejoin the rebuild that consumes it, with no reserved
// buckets needed: they are duplicate-free against the block for the same
// reason.
template <typename PlanOut>
inline void PlanPrepareOlderHalf(const RebuildStepContext& ctx,
                                 const SubtaskBudget& budget, PlanOut* out) {
  const size_t n = ctx.older.num_buckets;
  const size_t begin = ctx.upper_offset;
  const ResidualPass& rp0 = ctx.residual[0];
  const bool fuse_last = rp0.active &&
      rp0.fuse == ResidualFuseSite::kOwnLastLevel && rp0.sweep_active;
  const unsigned levels = Log2Exact(n);
  // The fused last level sheds into its own bit's stash, which the pass must
  // lead with (see ExpectFusedShedLeads).  Checked before anything is emitted.
  if (fuse_last) {
    ExpectFusedShedLeads(ctx, ResidualFuseSite::kOwnLastLevel,
                         levels == 0 || ctx.level_stashes == nullptr
                             ? nullptr
                             : &ctx.level_stashes[levels - 1]);
  }
  const unsigned own_levels = levels - static_cast<unsigned>(fuse_last);
  PlanArriveThenRoute(ctx, begin, n, own_levels, budget, out);
  if (fuse_last) {
    // The FUSED pass 0 (residual-offer fusion, src/oram/rebuild/DESIGN.md):
    // the butterfly
    // stops one level short -- levels [0, l-1) split into two independent
    // half-blocks, exactly PlanButterfly's own decomposition -- the range
    // table is then built from THOSE levels' sheds plus the tier, and the
    // last level runs flat with the offer fused in, replacing the standalone
    // sweep, as the cross level's offers do for the chain step.  The
    // last level's own sheds are the pass's drain-only prefix (provably
    // unabsorbable; see ButterflyLevelOffersRange) and go straight to the
    // drain the finish phases plan.  The pool dedup is planned for symmetry
    // with the standalone shape and emits nothing: pass 0's slots all rank
    // equal.
    MarkStage(out, ObservedMark(OrderedStage(),
                                PassBitsAtSite(ctx, ResidualFuseSite::kOwnLastLevel),
                                0, 0));
    PlanResidualPoolDedup(ctx, budget, /*pass=*/0, ResidualDedupWindow::kFull,
                          out);
    PlanResidualBuildPhases(ctx, budget, /*pass=*/0, out);
    Subtask level;
    level.kind = Subtask::kButterflyLevelOffers;
    level.bit = levels - 1;
    level.levels = OwnLevelOfferWeight(rp0);
    level.pass = 0;
    StageMark last = OfferStage(ctx, ResidualFuseSite::kOwnLastLevel);
    last.shed_lo = levels - 1;
    last.shed_hi = levels;
    MarkStage(out, last);
    PlanTaggedRange(level, 0, n / 2,
                    CrossOffersPairSlice(budget, level.levels), out);
    MarkStage(out, ObservedMark(OrderedStage(), 0,
                                PassBitsAtSite(ctx, ResidualFuseSite::kOwnLastLevel),
                                0));
    PlanResidualFinishPhases(ctx, budget, /*pass=*/0, out);
    return;
  }
  MarkStage(out, OrderedStage());
  PlanResidualSecondChance(ctx, budget, /*pass=*/0, out);
}

// The WEIGHT of the offers riding the cross level: touches per output bucket,
// which is what kCrossLevelOffers carries in `levels` and what the pair slice
// narrows by.  A single-rule set is one touch per GROUP; the merged
// class-marked set is two (its two masked compare nests over one transpose).
// The group factor is 1 everywhere but the DIRECT plans of the smallest steps
// (outputs of <= 2^kResidualDirectMaxLevels buckets), whose range table is
// the pool itself and offers each bucket one candidate set per pool bucket --
// chain-step pools are too small to reach the stacked regime.  Lockstep: the
// runner's fused arms assert it against the sets GatherFusedOffers
// assembles.
inline unsigned FusedOfferWeight(const RebuildStepContext& ctx,
                                 ResidualFuseSite site) {
  unsigned weight = 0;
  for (unsigned pass = 0; pass < kResidualPasses; ++pass) {
    const ResidualPass& rp = ctx.residual[pass];
    if (rp.active && rp.fuse == site && rp.sweep_active) {
      weight += ResidualOfferWeight(rp) + TopResolveOfferWeight(ctx, site, rp);
    }
  }
  return weight;
}

inline unsigned CrossOfferWeight(const RebuildStepContext& ctx) {
  return FusedOfferWeight(ctx, ResidualFuseSite::kCrossLevel);
}

#ifndef CPU_BYTESLICE_PRUNE_FRESHER_COPY
#define CPU_BYTESLICE_PRUNE_FRESHER_COPY 1
#endif

// These callers copy an already-routed power-of-two prefix under the SAME
// nonce and map. Its depth, not the future chain's route_levels, says which
// low tag bytes are dead. A default/hand-built kCopyFresher keeps all bytes.
template <typename PlanOut>
inline void PlanCopyFresherPrefix(size_t buckets, const SubtaskBudget& budget,
                                 PlanOut* out) {
  Subtask copy;
  copy.kind = Subtask::kCopyFresher;
  copy.levels = CPU_BYTESLICE_PRUNE_FRESHER_COPY ? Log2Exact(buckets) : 0;
  PlanTaggedRange(copy, 0, buckets, budget.copy_buckets, out);
}

// The tombstone drop over the item's output tier, planned wherever the drop
// over the main table is (PlanFixedMerge) and never anywhere else: it is legal
// at exactly the points kDropErased is.  Ranged over the tier's public capacity -- its
// occupancy is secret -- and a context without an output tier (a head, load
// 0.25, a test fixture) plans nothing.  Copy-priced, like kDropErased.
template <typename PlanOut>
inline void PlanDropErasedTier(const RebuildStepContext& ctx,
                               const SubtaskBudget& budget, PlanOut* out) {
  if (ctx.tier_out == nullptr) return;
  PlanRange(Subtask::kDropErasedTier, 0, ctx.tier_out->num_buckets,
            budget.copy_buckets, out);
}

// The fixed level's direct dedup-and-merge sweep of (B[i], C[i]) into C[i].
//
// The odd part r of the fixed level's own digit, read off the two operand
// sizes: C is r * 2^K buckets and B is 2^K.  It is 1 at B = 2, where C and B
// are the same size and the mixed-radix sweep collapses to the binary one.
inline unsigned FixedMergeRadix(const RebuildStepContext& ctx) {
  if (ctx.fresher.num_buckets == 0) return 1;
  return static_cast<unsigned>(ctx.out.num_buckets / ctx.fresher.num_buckets);
}

template <typename PlanOut>
inline void PlanFixedMerge(const RebuildStepContext& ctx,
                           const SubtaskBudget& budget, PlanOut* out) {
  Subtask merge;
  merge.bit = FixedMergeRadix(ctx);
  if (HasFusedPass(ctx, ResidualFuseSite::kFixedMerge)) {
    // The FUSED merge (residual-offer fusion, src/oram/rebuild/DESIGN.md):
    // one class-marked pass carries the preparation's carry (kTableWins class --
    // C is A merged with the fresher B, so every duplicate a carry entry can
    // meet is fresher) and B's tier (kResidualWins class -- never a duplicate
    // of B, fresher than everything of A's), built before the merge and
    // offered to each C bucket the moment B's entries have merged into it.
    // The merge shed is drain-only and B-class, so its one conflict is with
    // a carry-class leftover of the same key, which the epilogue's leftover
    // dedup resolves in the shed's favour.
    PlanFusedPassPrologue(ctx, budget, ResidualFuseSite::kFixedMerge, out,
                          ctx.merge_stash);
    const unsigned weight = FusedOfferWeight(ctx, ResidualFuseSite::kFixedMerge);
    merge.kind = weight > 0 ? Subtask::kFixedMergeOffers
                            : Subtask::kFixedMergeRange;
    merge.levels = weight;
    StageMark sweep = OfferStage(ctx, ResidualFuseSite::kFixedMerge);
    sweep.merge_shed = true;
    MarkStage(out, sweep);
    PlanTaggedRange(merge, 0, ctx.fresher.num_buckets,
                    weight > 0 ? FixedMergeOffersUnitSlice(budget, merge.bit,
                                                           weight)
                               : FixedMergePairSlice(budget, merge.bit),
                    out);
    PlanFusedPassEpilogue(ctx, budget, ResidualFuseSite::kFixedMerge, out);
    PlanStandalonePasses(ctx, budget, out);
  } else {
    merge.kind = Subtask::kFixedMergeRange;
    StageMark sweep = RangeStage();
    sweep.merge_shed = true;
    MarkStage(out, sweep);
    PlanTaggedRange(merge, 0, ctx.fresher.num_buckets,
                    FixedMergePairSlice(budget, merge.bit), out);
    MarkStage(out, OrderedStage());
    // Pass 1: the carry the PREPARATION left -- what C's butterfly (i.e. A's
    // contents) shed and could not put back.  C now holds A merged with B,
    // and B is the fresher operand, so every duplicate it can meet is fresher
    // and kTableWins is exact, exactly as at an ordinary step.
    PlanResidualSecondChance(ctx, budget, /*pass=*/1, out);
    // Pass 2: the merge sheds from B, the FRESHER operand, and C has already
    // had every duplicate of a B key cleared -- so a shed entry is the only
    // surviving copy of its key, and kResidualWins is exact for it as well.
    PlanResidualSecondChance(ctx, budget, /*pass=*/2, out);
  }
  if (!ctx.drop_unshadowed) return;
  // Last: forget the tombstones.  This is the only rebuild allowed to,
  // and this is the only point in it where nothing older than a tombstone can
  // still be looking for it -- the sweeps above drop a kTableWins duplicate
  // whether or not it fits and free the slot a kResidualWins one needs, so
  // every leftover they leave behind provably has no duplicate in the table.
  // Where the item may forget tombstones (`drop_unshadowed`) and its pass
  // rides the sweep -- the level arena's top -- ResolveTopDestination has
  // already removed every tombstone, main and tier, before each bucket's
  // capacity decisions, so this drop finds nothing (the checked build
  // asserts it) and stays as public work; no slot it frees is counted.
  MarkStage(out, RangeStage());
  PlanRange(Subtask::kDropErased, 0, ctx.out.num_buckets, budget.copy_buckets,
            out);
  // ...in the tier published beside C as well as in C: pass 2 drained its
  // leftovers there, tombstones included, and the tier is part of the same
  // window, so a tombstone in it is exactly as legal to forget here and, kept,
  // would ride every later rebuild as occupancy.
  MarkStage(out, OrderedStage());
  PlanDropErasedTier(ctx, budget, out);
}

// The odd radix a carry's own index map routes on; kRaw is r = 1.  One
// spelling, because the absorb and the fixed preparation must read the SAME
// rule off the map or their plans drift.
inline unsigned CarryRadix(const RoutingIndexMap& map) {
  return map.kind == TagMapKind::kRadixDigit ? map.modulus : 1u;
}

// ---------------------------------------------------------------------------
// The two emissions every digit-m merge shares
// ---------------------------------------------------------------------------
//
// PlanAbsorbStep below and the level-arena engine's phase planners
// (src/oram/levelarena/cpu_byteslice_level_arena_merge.hpp) differ in exactly
// one thing: how the FRESHER operand is installed -- a verbatim copy of a
// prefix this rebuild just wrote, or a fused copy-and-re-tag of a carry that
// was published under its own family, or the dense prefix builder.  What runs
// before the install and what runs after it is the same work in the same
// order, so it lives here once instead of in two copies that drift.
//
// `carry_bits` is K, `odd_part` r and `power` e: the output is r blocks of
// 2^(K+e) buckets.  Neither helper validates them -- the absorb asserts its
// shape, and the arena merge REFUSES its own, because its operands are views
// into another level's arena and assert() is not compiled into the build that
// runs.  Passing a shape neither caller checked is the caller's bug.

// Phase 1, every older source block's own butterfly: the pure blocks first and
// then block 0's older spans largest-first, which is
// RouteBinarySourcesDedup's order.  They are disjoint destination spans, so
// only "before the cross levels" is load bearing about the order.
template <typename PlanOut>
inline void PlanMergeOlderBlocks(unsigned carry_bits, unsigned odd_part,
                                 unsigned power, size_t bucket_bytes,
                                 const SubtaskBudget& budget, PlanOut* out) {
  const unsigned block_bits = carry_bits + power;
  const size_t block = size_t{1} << block_bits;
  for (unsigned q = 1; q < odd_part; ++q) {
    PlanCopyThenRoute(static_cast<size_t>(q) * block, block,
                              block_bits, bucket_bytes, budget, out);
  }
  for (unsigned u = power; u-- > 0;) {
    const size_t offset = size_t{1} << (carry_bits + u);
    PlanCopyThenRoute(offset, offset, carry_bits + u,
                              bucket_bytes, budget, out);
  }
}

// Phase 3, the finish: block 0's cross-source levels ascending, the ordered
// radix pass when r > 1, and the standalone residual passes.
//
// A residual pass rides the pass that ENDS the route -- the radix pass when
// r > 1, the last cross level when the digit is a power of two (r = 1,
// e >= 1); m = 1 has no route at all and keeps its standalone tier sweep.
// Both fusion sites are the same shape: the prologue right before the final
// pass, so every earlier level's shed is already in the range table, and the
// epilogue right after it.  What the final pass itself sheds is drain-only.
//
// The standalone passes come last, pass 1 before pass 2, for the usual reason:
// kTableWins DROPS a residual whose key the table already holds, so pass 1's
// survivors arrive at pass 2 already known to have no duplicate in the output
// and kResidualWins is exact for them in turn.  A fused pass was planned above
// and is skipped there.
template <typename PlanOut>
inline void PlanMergeFinish(const RebuildStepContext& ctx, unsigned carry_bits,
                            unsigned odd_part, unsigned power,
                            const SubtaskBudget& budget, PlanOut* out) {
  const unsigned block_bits = carry_bits + power;
  const bool fuse_cross = HasFusedPass(ctx, ResidualFuseSite::kCrossLevel);
  const bool fuse_radix = HasFusedPass(ctx, ResidualFuseSite::kRadixPass);
  for (unsigned c = carry_bits; c < block_bits; ++c) {
    Subtask cross;
    cross.bit = c;
    if (fuse_cross && c + 1 == block_bits) {
      PlanFusedPassPrologue(
          ctx, budget, ResidualFuseSite::kCrossLevel, out,
          ctx.level_stashes == nullptr ? nullptr : &ctx.level_stashes[c]);
      const unsigned weight = CrossOfferWeight(ctx);
      cross.kind = weight > 0 ? Subtask::kCrossLevelOffers
                              : Subtask::kCrossLevelRange;
      cross.levels = weight;
      StageMark level = OfferStage(ctx, ResidualFuseSite::kCrossLevel);
      level.shed_lo = c;
      level.shed_hi = c + 1;
      MarkStage(out, level);
      PlanTaggedRange(cross, 0, size_t{1} << c,
                      weight > 0 ? CrossOffersPairSlice(budget, weight)
                                 : budget.cross_pairs,
                      out);
      PlanFusedPassEpilogue(ctx, budget, ResidualFuseSite::kCrossLevel, out);
      continue;
    }
    cross.kind = Subtask::kCrossLevelRange;
    StageMark level = RangeStage();
    level.shed_lo = c;
    level.shed_hi = c + 1;
    MarkStage(out, level);
    PlanTaggedRange(cross, 0, size_t{1} << c, budget.cross_pairs, out);
  }
  if (odd_part > 1) {
    Subtask radix;
    radix.bit = odd_part;
    if (fuse_radix) {
      PlanFusedPassPrologue(ctx, budget, ResidualFuseSite::kRadixPass, out,
                            ctx.radix_stash);
      const unsigned weight =
          FusedOfferWeight(ctx, ResidualFuseSite::kRadixPass);
      radix.kind = weight > 0 ? Subtask::kRadixPassOffers
                              : Subtask::kRadixPassRange;
      // `levels` is the offer weight on the fused kind and the block width
      // on the plain one (the fused kernel reads the block off the output).
      radix.levels = weight > 0 ? weight : block_bits;
      StageMark pass = OfferStage(ctx, ResidualFuseSite::kRadixPass);
      pass.radix_shed = true;
      MarkStage(out, pass);
      PlanTaggedRange(radix, 0, size_t{1} << block_bits,
                      weight > 0 ? RadixOffersTupleSlice(budget, odd_part,
                                                         weight, /*dedup=*/true)
                                 : RadixDedupTupleSlice(budget, odd_part),
                      out);
      PlanFusedPassEpilogue(ctx, budget, ResidualFuseSite::kRadixPass, out);
    } else {
      radix.kind = Subtask::kRadixPassRange;
      radix.levels = block_bits;
      StageMark pass = RangeStage();
      pass.radix_shed = true;
      MarkStage(out, pass);
      PlanTaggedRange(radix, 0, size_t{1} << block_bits,
                      RadixDedupTupleSlice(budget, odd_part), out);
    }
  }
  PlanStandalonePasses(ctx, budget, out);
}

// ---------------------------------------------------------------------------
// The absorb
// ---------------------------------------------------------------------------
//
// The last item of a base-B carry into t, and the one place a level absorbs its
// own old table.  Unlike a chain step it is not a two-operand merge with a
// power-of-two output: the target takes digit m and holds m * 2^K buckets.
//
//   fresher = T_t, 2^K buckets, the chain's output, already routed on [0, K)
//   older   = L_t^old, (m-1) * 2^K buckets, the level's own table at digit m-1
//   out     = the digit-m table, m * 2^K buckets, m = r * 2^e
//
// `out` is laid out [ T_t | L_t^old ] contiguously, which puts the pieces
// exactly where the map wants them with no gather:
//
//   block 0    [0, 2^(K+e))         [ T_t | 2^K | 2^(K+1) | ... | 2^(K+e-1) ]
//                                   a binary-source layout whose blocks
//                                   continue T_t's prefix-doubling sequence, so
//                                   it is e ordinary dedup cross levels
//   block q>0  [q*2^(K+e), ...)     pure L_t^old, one full butterfly, no dedup
//   then       one radix-r pass with the dedup prologue
//
// e = 0 for m in {1,3,5,7}: block 0 IS T_t and there is no cross level at all.
// r = 1 for m in {1,2,4}: no radix pass, and the whole thing is a plain
// continuation of the binary chain into one buffer.  m = 1 is both, i.e. a bare
// copy of T_t into the resident slab.
//
// Why the two dedups above are ALL of them.  A duplicate is always (T_t copy,
// L_t^old copy) -- L_t^old holds each key at most once.  Both copies carry the
// same tag, so after the block butterflies they sit at the same offset within
// their blocks: same block, and the binary cross level at the right bit pairs
// them; different blocks, and only block 0 can hold the T_t copy, which is the
// radix prologue's (bucket 0, bucket q) clear.
//
// Two residual passes, and BOTH at the very end, after the radix
// pass: the second chance pairs a residual with its FINAL bucket, and until the
// radix pass has run an entry of block q is not yet where idx(T) puts it.  That
// costs the absorb pass 0 -- there is no instant at which a block's own shed
// could be offered back to that block alone -- but nothing else, because
//
//   pass 1  kTableWins     every block butterfly and every cross level sheds
//                          from L_t^old (a MergeSplit sheds its second operand
//                          only), and L_t^old holds each key once, so the only
//                          duplicate such an entry can meet is the T_t copy --
//                          strictly fresher.  L_t^old's own second tier joins
//                          it: same class, and disjoint from L_t^old itself.
//   pass 2  kResidualWins  the radix pass's shed, T_t's second tier, and pass
//                          1's survivors.  The radix shed is the one the
//                          absorb left
//                          open, and the prologue closes it: it clears every
//                          block-q copy of a block-0 key BEFORE the MergeSplit,
//                          and two copies of a key always share a tuple, so
//                          every entry the pass sheds -- from block 0 or from
//                          block q, T_t-class or L_t^old-class -- provably has
//                          no surviving copy left in the table.
//
// The one place that needs three ranks rather than two is pass 2's pool, since
// the radix slot holds both classes at once.
template <typename PlanOut>
inline void PlanAbsorbStep(const RebuildStepContext& ctx,
                           const SubtaskBudget& budget, PlanOut* out) {
  const size_t prefix = ctx.fresher.num_buckets;  // 2^K
  const unsigned k = Log2Exact(prefix);
  const size_t total = ctx.out.num_buckets;  // m * 2^K
  const unsigned m = static_cast<unsigned>(total / prefix);
  assert(total == static_cast<size_t>(m) * prefix);
  assert(ctx.upper_offset == prefix);
  // The shape comes from the carry's own index map, not from AbsorbShape(m):
  // the two agree at every level below the top, and at the TOP level
  // the map forces e = 0 and r = m at the top level, so the
  // absorb ends in one radix-m pass instead of e binary cross levels plus a
  // radix-(odd part) one.  kRaw is r = 1, and then 2^e is the whole digit.
  const unsigned r = CarryRadix(ctx.map);
  assert(m % r == 0);
  const unsigned e = Log2Exact(m / r);
  assert((size_t{1} << e) * r == m);

  // T_t's tags are already this rebuild's -- the chain wrote them under the
  // carry's map and its full route_levels -- so the prefix is copied, never
  // re-tagged, exactly as a chain step copies its fresher half.
  PlanCopyFresherPrefix(prefix, budget, out);
  PlanMergeOlderBlocks(k, r, e, ctx.out.layout.BucketBytes(), budget, out);
  // The FUSED absorb (residual-offer fusion, src/oram/rebuild/DESIGN.md):
  // one class-marked pass -- L_t^old's butterfly and cross sheds and its tier as
  // the kTableWins class, T_t's tier as the kResidualWins class -- rides the
  // pass that ends the route.  PlanMergeFinish is where that lands; these two
  // assertions are the absorb's own statement of which site its shape offers.
  assert(!HasFusedPass(ctx, ResidualFuseSite::kCrossLevel) ||
         (r == 1 && e >= 1));
  assert(!HasFusedPass(ctx, ResidualFuseSite::kRadixPass) || r > 1);
  PlanMergeFinish(ctx, k, r, e, budget, out);
}

}  // namespace byteslice
}  // namespace microram
