#pragma once

// Slice widths: how many units of its own kind one subtask may cover.
//
// A planner takes a width per phase because the phases are not commensurable --
// a re-tag is 64 AES blocks, a cross-source pair is a MergeSplit plus a 64x64
// all-pairs intersect, a copy is pure bandwidth -- so one bucket count could
// never mean the same amount of work in two of them.  The helpers below derive
// each phase's width from the others it is expressed in terms of, which is what
// keeps a radix pass and the fixed merge consistent: an r-way MergeSplit is not
// r/2 pair MergeSplits, and only these functions know that.
//
// THE LEVEL ARENA PLANS AT SATURATED WIDTHS AND RUNS AT FINITE ONES.  Every
// phase is planned at `WholeLevelMergeBudget` -- each field SIZE_MAX, one
// subtask per range -- and then run by a PhaseCursor that cuts each subtask
// into pieces at the executing group's budget (cpu_byteslice_subtask_cursor.hpp).
// So the helpers below must stay exact at SIZE_MAX as well as at a one-unit
// width.  Every group's budget comes from SubtaskBudgetForTouches below, an
// analytical count of bucket touches rather than a measured time per kind.

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <cstdint>

#include "src/oram/scheduler/cpu_byteslice_subtask.hpp"

namespace microram {
namespace byteslice {

// A step runs three residual passes, one per freshness class: the block's own
// butterfly shed under kNoDedup, its leftovers under kTableWins, and everything
// a cross-source level or the fixed merge shed under kResidualWins.
inline constexpr unsigned kResidualPasses = 3;

// A radix-r MergeSplit tuple, in bucket touches.
//
// The r-way kernel is QUADRATIC in r, which is the one thing about base B that
// the touch currency does not get for free.  MergeSplitRadixStashFixed chains
// `r(r-1) + r` permutes per byte line over its r buckets -- r permutes per
// bucket -- against a binary MergeSplit's 4 over two, i.e. 2 per bucket.  So a
// bucket of an r-way pass is r/2 binary bucket touches and a tuple of r of them
// is r^2/2 (charging r would undercount the radix pass by a factor r/2).
// Rounded up, because a slice width derived from this is a bound and the
// honest direction to miss in is conservative.
//
// It agrees with the binary currency where the two meet: at r = 2 this is 2,
// which is what a one-level butterfly over two buckets already charges.
inline size_t RadixTupleTouches(unsigned r) {
  const size_t rr = static_cast<size_t>(r);
  return (rr * rr + 1) / 2;
}

// One bucket of the fresher table B dedup-and-merged into each of its r
// destinations in C, so r dedups and r merges per B bucket -- 2r touches
// in the same "a pair costs two" currency MergeFixedLevelSourcesRange is
// charged in.  At r = 1 this is 2, the binary sweep unchanged.
inline size_t FixedMergeUnitTouches(unsigned r) {
  return 2 * static_cast<size_t>(r < 1 ? 1 : r);
}

// THE DFS PARTITION'S CHARGE (kResidualDfsPartition).  Its units are child
// compactions of different sizes -- a direct child compacts the whole pool,
// each split below it half of its parent -- so no constant per unit prices
// them, and charging every unit the largest one's touches overstated a pass
// 1.6 to 5.4 times at levels two to five.  The task carries the pass's whole
// estimate in `levels`, every unit at its own parent's size
// (DfsResidualWorkspace::Touches), and its unit count in `bit`.  A piece is
// charged its units' share, floor(T * end / U) - floor(T * begin / U), so the
// pieces of any cut of a pass sum to T exactly; one piece's share is the
// pass's mean per unit, not its own units' touches. The planner caps T at
// UINT_MAX to fit Subtask::levels; a larger estimate is therefore undercharged.
// These counts guide scheduling and do not bound elapsed time.
inline size_t DfsPartitionPieceTouches(const Subtask& piece) {
  const uint64_t t = piece.levels;
  const uint64_t u = piece.bit;
  if (u == 0) return piece.end - piece.begin;
  return static_cast<size_t>(t * piece.end / u - t * piece.begin / u);
}

// How many of the partition's units one piece may cover at `budget_touches`:
// the whole pass when it fits, else at least one unit (units are indivisible).
inline size_t DfsPartitionUnitSlice(const Subtask& task,
                                    size_t budget_touches) {
  const uint64_t t = task.levels;
  const uint64_t u = task.bit;
  if (u == 0 || t <= budget_touches) return std::max<size_t>(1, u);
  return std::max<size_t>(1, static_cast<size_t>(budget_touches * u / t));
}


// One scatter GROUP is one pool bucket fanned over `fanout` consecutive range
// buckets, and ScatterDenseBucket writes every one of them -- so a group is
// `fanout` bucket touches, not one.  Charging it as one would let a slice
// sized at copy_buckets groups move up to 8x that many buckets, i.e. escape
// its budget by the fanout (the same unit rule as kResidualPoolDedup in
// cpu_byteslice_subtask.hpp).
//
// The fanout rides on `task.bit`, the field kRadixPassRange and
// kFixedMergeRange already use for their own multiplicity.  A zero means an
// unset field from a hand-built Subtask; treat it as the binary 1 rather than
// as free work.
inline size_t ScatterFanoutTouches(unsigned fanout) {
  return static_cast<size_t>(fanout < 1 ? 1 : fanout);
}

// The radix a mixed-radix subtask's `bit` carries, with an unset 0 (a
// hand-built Subtask) read as the binary 1.
inline size_t SubtaskRadixOf(unsigned bit) {
  return static_cast<size_t>(bit < 1 ? 1 : bit);
}

// Slice widths, in the units each planner counts in.  Saturated
// (`WholeLevelMergeBudget`) a width only has to exceed any single phase's work,
// and that is what every phase is planned at; finite, it is how long a piece
// of a running phase may be before the group that runs it may stop it.
struct SubtaskBudget {
  size_t copy_buckets = 1;
  size_t retag_buckets = 1;
  // Buckets per slice of the fused copy-and-retag.  Kept separate from the two
  // above because the fusion changes what a touch costs; it is charged two
  // touches per bucket (SubtaskBudgetForTouches).
  size_t copy_retag_buckets = 1;
  size_t butterfly_touches = 1;  // levels * 2^levels of a sub-network
  size_t cross_pairs = 1;
  size_t fixed_merge_pairs = 1;
  // Destination buckets per slice of the residual scatter.  ScatterGroupSlice
  // turns it into GROUPS by dividing by the plan's fanout
  // (ScatterFanoutTouches).
  size_t residual_scatter_buckets = 1;
  // Units per slice of the intersect-only phase: ordered pool-bucket
  // pairs for kResidualPoolDedup.  One unit is one CrossBucketDuplicateMask =
  // one touch.  It has its own width because cross_pairs is sized for
  // TWO-touch units and would halve every slice of the phase.
  size_t intersect_units = 1;
  // UNITS per slice of each mixed-radix phase, per radix: tuples for the two
  // radix passes, B buckets for the fixed level's sweep.  Indexed rather than
  // divided, because the per-unit cost is not a fixed multiple of a binary
  // constant (RadixTupleTouches, FixedMergeUnitTouches).  A zero entry reads
  // as a one-unit width.
  size_t radix_dedup_tuples[kMaxRadix + 1] = {};
  size_t radix_route_tuples[kMaxRadix + 1] = {};
  // To the SWEEP's fan-in, not the radix pass's: the level arena's binary top
  // sweeps 8 ways with no radix-8 pass anywhere (kMaxFixedMergeWays).
  size_t radix_merge_units[kMaxFixedMergeWays + 1] = {};
  // Destination buckets per fused residual build slice, priced for BOTH
  // scatter and retag. Zero in hand-built budgets falls back to half the
  // smaller of the unfused scatter and retag widths (ResidualBuildGroupSlice).
  size_t residual_build_buckets = 0;
};

// One B home of level one's direct build visits every prefix bucket once: a
// source bucket's candidates permuted into the home, one touch each.  An
// unset 0 (a hand-built Subtask) is read as one source.
inline size_t DenseSelectHomeTouches(unsigned sources) {
  return static_cast<size_t>(sources < 1 ? 1 : sources);
}

inline size_t DenseSelectHomeSlice(const SubtaskBudget& budget,
                                   unsigned sources) {
  const size_t width = budget.copy_buckets / DenseSelectHomeTouches(sources);
  return width == 0 ? 1 : width;
}

// Units per slice of each mixed-radix phase.  Split out into named accessors
// so every planner reads the same entry: a slice width is only a bound on a
// slice's cost if the planner sizes on the number the cost is charged by;
// a planner that sized on a different number would silently emit slices
// over its bound.
inline size_t RadixDedupTupleSlice(const SubtaskBudget& budget, unsigned r) {
  if (r <= 1 || r > kMaxRadix) return 1;
  const size_t width = budget.radix_dedup_tuples[r];
  return width == 0 ? 1 : width;
}

inline size_t RadixRouteTupleSlice(const SubtaskBudget& budget, unsigned r) {
  if (r <= 1 || r > kMaxRadix) return 1;
  const size_t width = budget.radix_route_tuples[r];
  return width == 0 ? 1 : width;
}

// B buckets per slice of the fixed level's sweep.  At r = 1 this is
// fixed_merge_pairs
// unchanged, which is the binary path byte for byte.
inline size_t FixedMergePairSlice(const SubtaskBudget& budget, unsigned r) {
  if (r <= 1) return budget.fixed_merge_pairs;
  if (r > kMaxFixedMergeWays) return 1;
  const size_t width = budget.radix_merge_units[r];
  return width == 0 ? 1 : width;
}

// Pairs per slice of the fused cross level: a pair is 2 + 2*weight touches
// against the plain pair's 2, so the width narrows by the same factor the
// touch count grew by.  `weight` is the offers' touch count per output bucket
// (a class-marked set is 2, a single-rule set 1); at 0 it is cross_pairs
// unchanged.
inline size_t CrossOffersPairSlice(const SubtaskBudget& budget,
                                   unsigned weight) {
  const size_t width = budget.cross_pairs / (1 + static_cast<size_t>(weight));
  return width == 0 ? 1 : width;
}

// `width * num / den`, at least 1, without wrapping.  A saturated width
// (SIZE_MAX) times a unit's touches would wrap and send a large finite
// width to a tiny slice; dividing first keeps it saturated.  Below the
// overflow point the result is the exact product, so small widths are
// unchanged.
inline size_t ScaleSliceWidth(size_t width, size_t num, size_t den) {
  const size_t scaled = width > SIZE_MAX / num ? width / den * num
                                               : width * num / den;
  return scaled == 0 ? 1 : scaled;
}

// Units per slice of the fused finalizers: the unfused width narrowed by the
// factor a fused unit's touches grow by, so the slice keeps the unfused
// slice's cost at the pass's own rate.  `weight` is the offers' touch count
// per output bucket; at 0 each is its unfused width unchanged.
inline size_t RadixOffersTupleSlice(const SubtaskBudget& budget, unsigned r,
                                    unsigned weight, bool dedup) {
  const size_t base = dedup ? RadixDedupTupleSlice(budget, r)
                            : RadixRouteTupleSlice(budget, r);
  const size_t tuple = RadixTupleTouches(r);
  return ScaleSliceWidth(
      base, tuple, tuple + SubtaskRadixOf(r) * static_cast<size_t>(weight));
}

inline size_t FixedMergeOffersUnitSlice(const SubtaskBudget& budget, unsigned r,
                                        unsigned weight) {
  const size_t base = FixedMergePairSlice(budget, r);
  const size_t unit = FixedMergeUnitTouches(r);
  return ScaleSliceWidth(
      base, unit, unit + SubtaskRadixOf(r) * static_cast<size_t>(weight));
}

// Pairs per slice of the leftover dedup: one intersect per class per pair.
inline size_t LeftoverDedupPairSlice(const SubtaskBudget& budget,
                                     unsigned weight) {
  const size_t width =
      budget.intersect_units / static_cast<size_t>(weight < 1 ? 1 : weight);
  return width == 0 ? 1 : width;
}

// Scatter GROUPS per slice.  The budget is in bucket touches and a group is
// `fanout` of them (ScatterFanoutTouches), so the group width is the bucket
// width divided down by exactly that number.
inline size_t ScatterGroupSlice(const SubtaskBudget& budget, unsigned fanout) {
  const size_t f = ScatterFanoutTouches(fanout);
  const size_t width = budget.residual_scatter_buckets / f;
  return width == 0 ? 1 : width;
}

inline size_t ResidualBuildGroupSlice(const SubtaskBudget& budget,
                                      unsigned fanout) {
  const size_t buckets = budget.residual_build_buckets != 0
      ? budget.residual_build_buckets
      : std::min(budget.residual_scatter_buckets, budget.retag_buckets) / 2;
  return std::max(size_t{1}, buckets / ScatterFanoutTouches(fanout));
}

// A budget in which every width is about `touches` bucket touches of its own
// kind: the unit conversions above, applied to one number, so that a piece of
// any phase cut at this budget costs about the same.  A copy is one touch per
// bucket, a fused copy-and-re-tag two, a pair two, a fused residual route
// quad eight, a radix tuple RadixTupleTouches(r) and a fixed-merge unit
// FixedMergeUnitTouches(r).  Rounded down and floored at one unit, so an
// indivisible unit (a kernel leaf, one tuple) may still exceed the budget.
inline SubtaskBudget SubtaskBudgetForTouches(size_t touches) {
  const auto per = [touches](size_t unit) {
    return std::max<size_t>(1, touches / unit);
  };
  SubtaskBudget b;
  b.copy_buckets = per(1);
  b.retag_buckets = per(1);
  b.copy_retag_buckets = per(2);
  b.butterfly_touches = per(1);
  b.cross_pairs = per(2);
  b.fixed_merge_pairs = per(2);
  b.residual_scatter_buckets = per(1);
  b.intersect_units = per(1);
  b.residual_build_buckets = per(2);
  for (unsigned r = 0; r <= kMaxRadix; ++r) {
    b.radix_dedup_tuples[r] = per(RadixTupleTouches(r < 2 ? 2 : r));
    b.radix_route_tuples[r] = per(RadixTupleTouches(r < 2 ? 2 : r));
  }
  for (unsigned r = 0; r <= kMaxFixedMergeWays; ++r) {
    b.radix_merge_units[r] = per(FixedMergeUnitTouches(r));
  }
  return b;
}

}  // namespace byteslice
}  // namespace microram
