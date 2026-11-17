#pragma once

// THE PASS SHAPES of every merge: which stashes and tiers each residual pass
// pools, in what ranks, how big the pool is, and the range or DFS plan it
// offers from.  Pure functions of the geometry, the stash sizing, the level
// and the digit; LevelMergeJob (cpu_byteslice_level_arena_job.hpp) binds
// these lists to its storage and runs them.
//
// Kept apart from the job because the certification hashes the files that
// decide job shapes and stash sizes, and the job's execution machinery is not
// one of them (analysis/bound_certification/code/source_scope.py).  A pass
// shape added to the job instead of here would escape that check.

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_merge.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_stash.hpp"
#include "src/oram/rebuild/cpu_byteslice_dfs_residual.hpp"
#include "src/oram/rebuild/cpu_byteslice_residual_range.hpp"
#include "src/oram/rebuild/cpu_byteslice_residual_stash.hpp"
#include "src/oram/scheduler/cpu_byteslice_residual_pass.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

// ---------------------------------------------------------------------------
// The pools, as public lists
// ---------------------------------------------------------------------------
//
// Every pass here is a pool of the job's own stashes, and its shape is a
// function of the level and the digit alone.  That is what lets a thread's
// range scratch be sized before any merge exists (MaxLevelMergeRangeBuckets)
// -- and it is why each shape is written ONCE, as a list of slots, and both
// the sizing and the building walk that same list: the sizing counts the
// buckets of its swept slots, the job binds each slot to its stash, and the
// two cannot disagree about which slots a pass has.

// Where in the job a slot's stash lives.
enum class PoolSlotStorage : uint8_t {
  kOlderShed,  // the older operand's route sheds, and the radix, merge and
               // retained-carry stashes past them (kLevelMerge*StashOffset)
  kOlderTier,  // the older operand's tier, through the job's private view
  kCarryTier,  // the carry's tier, likewise
};

struct PoolSlot {
  PoolSlotStorage storage = PoolSlotStorage::kOlderShed;
  unsigned index = 0;  // into the older sheds; 0 for a tier
  uint8_t rank = 0;
  bool tier_class = false;
  // Skips the range table and goes straight to the drain.  Drain-only slots
  // lead the list (ResidualPassSpec::drain_only_slots).
  bool drain_only = false;
};

// What a pass is besides its slots.
struct PoolRecipe {
  ResidualFuseSite fuse = ResidualFuseSite::kNone;
  ResidualDedupRule rule = ResidualDedupRule::kNoDedup;
  size_t shed_slots = 0;
  bool force_active = false;
};

// The class ranks of a fused residual pass, named.  Lower is fresher: when two
// copies of a key meet, the lower rank's copy is the live one.
inline constexpr uint8_t kLevelMergeFresherRank = 0;  // the carry's class
inline constexpr uint8_t kLevelMergeOlderRank = 2;    // the older operand's
// The top's preparation has ONE class -- A's -- so its rank is arbitrary and
// named rather than left as a literal 0 that looks like the fresher rank.
inline constexpr uint8_t kLevelMergePrepRank = 0;

inline PoolSlot OlderShedSlot(unsigned index, uint8_t rank,
                              bool drain_only = false) {
  return PoolSlot{PoolSlotStorage::kOlderShed, index, rank, false, drain_only};
}

// Completed A route, including its last binary/radix losses. The only
// drain-only source is the subsequent B insertion's shed. A is routed alone,
// never against B's main, so no swept record was selected using B's main
// prefix and A's range event does not depend on B.
template <typename Visit>
inline PoolRecipe SeparatedFinishPoolSlots(const MergeShape& shape,
                                           Visit&& visit) {
  PoolRecipe recipe;
  recipe.fuse = ResidualFuseSite::kFixedMerge;
  recipe.rule = ResidualDedupRule::kClassMark;
  visit(OlderShedSlot(shape.block_bits + kLevelMergeMergeStashOffset,
                      kLevelMergeFresherRank, /*drain_only=*/true));
  for (unsigned b = 0; b < shape.block_bits; ++b)
    visit(OlderShedSlot(b, kLevelMergeOlderRank));
  if (shape.has_radix_pass())
    visit(OlderShedSlot(shape.block_bits + kLevelMergeRadixStashOffset,
                        kLevelMergeOlderRank));
  visit(PoolSlot{PoolSlotStorage::kOlderTier, 0, kLevelMergeOlderRank});
  visit(PoolSlot{PoolSlotStorage::kCarryTier, 0, kLevelMergeFresherRank, true});
  recipe.shed_slots = shape.block_bits + 1 + shape.has_radix_pass();
  return recipe;
}

// Ordinary digits above one use separated sources; sparse digit one drains
// its carry tier. Level one's digit one runs no finish pass.
template <typename Visit>
inline PoolRecipe FinishPoolSlotsOf(const MergeShape& shape, Visit&& visit) {
  if (shape.digit > 1) return SeparatedFinishPoolSlots(shape, visit);
  PoolRecipe recipe;
  recipe.rule = ResidualDedupRule::kNoDedup;
  visit(PoolSlot{PoolSlotStorage::kCarryTier, 0, kLevelMergeFresherRank,
                 false, /*drain_only=*/true});
  return recipe;
}

// ---------------------------------------------------------------------------
// The TOP's two pools (DESIGN.md "Top compaction and residuals")
// ---------------------------------------------------------------------------
//
// The top runs two passes where every other level runs one, and the reason is
// that its route FINISHES IN THE PREPARATION: A's last butterfly level puts
// every entry of A in its final bucket before the carry is even looked at,
// so A's sheds can be offered back right then -- into buckets that still
// have the room B is about to take.  Below the top a block-q entry is not
// where the index map puts it until the finish's radix pass has run, which is
// why a non-top preparation holds its sheds instead.
//
// What the preparation cannot place is RETAINED in a stash of its own
// and becomes the merge pass's older class.

// The PREPARATION's: A's route sheds and A's tier, one class and one rank,
// offered back the moment C's route ends.  kNoDedup is exact because A is ONE
// source and holds each key at most once -- its main, its tier and every shed
// are one duplicate-free union -- so an entry offered into its own final
// bucket cannot meet a copy of itself there.
//
// It rides the pass that ends C's route -- A's own last butterfly level, the
// top being binary, exactly as a chunk preparation's does
// (PlanPrepareOlderHalf) -- and that level's own shed leads as the drain-only
// prefix, for the reason every fused pass has one.
template <typename Visit>
inline PoolRecipe TopPreparePoolSlots(const MergeShape& shape, Visit&& visit) {
  PoolRecipe recipe;
  recipe.rule = ResidualDedupRule::kNoDedup;
  recipe.fuse = ResidualFuseSite::kOwnLastLevel;
  visit(OlderShedSlot(shape.block_bits - 1, kLevelMergePrepRank,
                      /*drain_only=*/true));
  for (unsigned b = 0; b + 1 < shape.block_bits; ++b) {
    visit(OlderShedSlot(b, kLevelMergePrepRank));
  }
  visit(PoolSlot{PoolSlotStorage::kOlderTier, 0, kLevelMergePrepRank});
  recipe.shed_slots = shape.block_bits;
  return recipe;
}

// The MERGE's: one class-marked pass over everything the sweep leaves
// unplaced, RIDING the sweep.
//
//   drain-only  the sweep's own shed, from B;
//   rank 2      the preparation's retained carry, A's class;
//   rank 0, tier  B's own second tier, fresher than everything of A's.
//
// LevelMergeJob::BuildTopMergePass says why the drain-only prefix is safe in
// this shape.  Of the slots, the one holding what THIS phase shed is the
// merge stash; the retained carry holds what the preparation's pass already
// counted.
template <typename Visit>
inline PoolRecipe TopMergePoolSlots(const MergeShape& shape, Visit&& visit) {
  PoolRecipe recipe;
  recipe.fuse = ResidualFuseSite::kFixedMerge;
  recipe.rule = ResidualDedupRule::kClassMark;
  visit(OlderShedSlot(shape.block_bits + kLevelMergeMergeStashOffset,
                      kLevelMergeFresherRank, /*drain_only=*/true));
  visit(OlderShedSlot(shape.block_bits + kLevelMergePrepCarryStashOffset,
                      kLevelMergeOlderRank));
  visit(PoolSlot{PoolSlotStorage::kCarryTier, 0, kLevelMergeFresherRank,
                 /*tier_class=*/true});
  recipe.shed_slots = 1;
  return recipe;
}

// ---------------------------------------------------------------------------
// The pool's shape, as public arithmetic
// ---------------------------------------------------------------------------
//
// How many stash buckets a pass sweeps, and over how wide a main: the sum
// over the list's swept slots, every shed `stash_buckets` wide, the older
// operand's tier `older_tier_buckets` and the carry's `carry_tier_buckets`
// (LevelArenaGeometry::OlderTierBuckets and CarryTierBuckets: one width
// unless the geometry has a per-level tier profile).

struct LevelMergePoolShape {
  size_t swept_buckets = 0;   // pool minus the drain-only prefix
  unsigned main_levels = 0;   // index bits of the output the sweep pairs with
  // Whether the pass rides a routing pass rather than sweeping standalone.
  // False at digit 1, which has no route to ride.
  bool fused = false;
  size_t direct_buckets = 0;  // swept suffix kept outside the distributor
};

// The width a slot of this storage holds: a shed's, or one of the two tiers'.
inline size_t PoolSlotBuckets(const PoolSlot& slot, size_t stash_buckets,
                              size_t older_tier_buckets,
                              size_t carry_tier_buckets) {
  switch (slot.storage) {
    case PoolSlotStorage::kOlderTier:
      return older_tier_buckets;
    case PoolSlotStorage::kCarryTier:
      return carry_tier_buckets;
    default:
      return stash_buckets;
  }
}

template <typename Slots>
inline LevelMergePoolShape PoolShapeOfSlots(const MergeShape& shape,
                                            size_t stash_buckets,
                                            size_t older_tier_buckets,
                                            size_t carry_tier_buckets,
                                            Slots&& slots) {
  LevelMergePoolShape out;
  out.main_levels = Log2Exact(shape.out_buckets);
  const PoolRecipe recipe = slots([&](const PoolSlot& slot) {
    if (slot.drain_only) return;
    out.swept_buckets += PoolSlotBuckets(slot, stash_buckets,
                                         older_tier_buckets,
                                         carry_tier_buckets);
  });
  out.fused = recipe.fuse != ResidualFuseSite::kNone;
  return out;
}

// Every ordinary digit above one offers the carry tier directly rather than
// through the distributor.
inline LevelMergePoolShape LevelMergePoolShapeOf(
    const MergeShape& shape, size_t stash_buckets,
    size_t older_tier_buckets, size_t carry_tier_buckets) {
  auto pool = PoolShapeOfSlots(shape, stash_buckets, older_tier_buckets,
                          carry_tier_buckets, [&](auto&& visit) {
                            return FinishPoolSlotsOf(shape, visit);
                          });
  if (shape.digit > 1) pool.direct_buckets = carry_tier_buckets;
  return pool;
}

// The top's preparation sweeps A's tier, the older operand's.
inline LevelMergePoolShape TopPreparePoolShapeOf(const MergeShape& shape,
                                                 size_t stash_buckets,
                                                 size_t older_tier_buckets) {
  return PoolShapeOfSlots(shape, stash_buckets, older_tier_buckets, 0,
                          [&](auto&& visit) {
                            return TopPreparePoolSlots(shape, visit);
                          });
}

// The top's merge sweeps the retained carry and B's tier, and like every
// separated pool offers B's tier directly rather than through the
// distributor: its DFS leaf holds A's class alone.
inline LevelMergePoolShape TopMergePoolShapeOf(const MergeShape& shape,
                                               size_t stash_buckets,
                                               size_t carry_tier_buckets) {
  auto pool = PoolShapeOfSlots(shape, stash_buckets, 0, carry_tier_buckets,
                               [&](auto&& visit) {
                                 return TopMergePoolSlots(shape, visit);
                               });
  pool.direct_buckets = carry_tier_buckets;
  return pool;
}

// ---------------------------------------------------------------------------
// How each pass builds its range table: the certified residual routing
// ---------------------------------------------------------------------------
//
inline constexpr size_t kSeparatedDfsPages = 1;  // A's leaf; B is direct
inline constexpr size_t kTopPrepareDfsPages = 1;

// A DIRECTLY BUILT LEVEL ONE (DESIGN.md "Directly built level one").  B is
// built into U buckets with its leftovers in ONE bucket, and above digit one the finish is the
// separated one every sparse digit runs: A's completed route through a
// one-page DFS leaf, whose only range event is A's complete-home excess on a
// coarse range, and B's tier offered directly.  At digit one B is built
// straight into the output and its tier, and no pass runs.
inline constexpr size_t kDenseDirectTierBuckets = 1;

inline bool DenseDirectLevel(const LevelArenaGeometry&,
                             unsigned level) {
  return level == 1;
}

// Whether the finish of `digit` at `level` has separated sources.
inline bool SeparatedSources(const LevelArenaGeometry& geometry,
                             unsigned level, unsigned digit) {
  return level < geometry.Levels() && digit > 1;
}

// Every finish distributor uses one A page per coarse range.
inline size_t FinishDfsPages(const LevelMergePoolShape&) {
  return kSeparatedDfsPages;
}

// The finish pass's range plan: at one ordinary digit, and at the top's
// merge, whose pool is separated like theirs.
inline ResidualRangePlan LevelFinishRangePlan(const LevelMergePoolShape& pool) {
  return DfsResidualRangePlan(pool.swept_buckets - pool.direct_buckets,
                              pool.main_levels, FinishDfsPages(pool));
}

// The top preparation's.
inline ResidualRangePlan TopPrepareRangePlan(const LevelMergePoolShape& pool) {
  return DfsResidualRangePlan(pool.swept_buckets, pool.main_levels,
                              kTopPrepareDfsPages);
}

// A pass's range builder, as the residual pass spec states it: what a job
// binds and what the pricing plans are one object.
struct PassRange {
  size_t dfs_pages = 0;
  bool separate_direct_tier = false;

  void ApplyTo(ResidualPassSpec* spec) const {
    spec->dfs_pages = dfs_pages;
    spec->separate_direct_tier = separate_direct_tier;
  }
};

inline PassRange FinishPassRange(const LevelMergePoolShape& pool) {
  return {FinishDfsPages(pool), pool.direct_buckets != 0};
}
inline PassRange TopPreparePassRange() {
  return {kTopPrepareDfsPages, false};
}

// THE FINISH OF ONE ORDINARY (level, digit), as every caller binds, sizes and
// prices it: whether it runs a pass, its slots and its pool shape.
inline bool FinishRunsPass(const LevelArenaGeometry& geometry, unsigned level,
                           unsigned digit) {
  return !(DenseDirectLevel(geometry, level) && digit == 1);
}

// THE MERGE STASH'S WIDTH at `level`: a route slot's, except at a directly
// built level one, where it is at least the output tier's.  There B-main
// sheds are distinct survivors at permanently full homes, so they number at
// most the final excess, which the output tier holds; a merge stash that wide
// cannot overflow before the tier does and adds no capacity event of its own.
// Only the merge slot widens; the route slots keep their certified depth.
inline size_t MergeStashBuckets(const LevelArenaGeometry& geometry,
                                size_t stash_buckets, unsigned level) {
  return DenseDirectLevel(geometry, level)
             ? std::max(stash_buckets, geometry.TierBucketsOf(level))
             : stash_buckets;
}

// The carry tier the finish offers: the producer's, or a directly built B's
// one bucket.
inline size_t FinishCarryTierBuckets(const LevelArenaGeometry& geometry,
                                     unsigned level) {
  return DenseDirectLevel(geometry, level) ? kDenseDirectTierBuckets
                                           : geometry.CarryTierBuckets(level);
}

template <typename Visit>
inline PoolRecipe FinishPoolSlotsAt(const LevelArenaGeometry& geometry,
                                    unsigned level, const MergeShape& shape,
                                    Visit&& visit) {
  return FinishPoolSlotsOf(shape, visit);
}

inline LevelMergePoolShape FinishPoolShapeAt(const LevelArenaGeometry& geometry,
                                             size_t stash_buckets,
                                             unsigned level,
                                             const MergeShape& shape) {
  return LevelMergePoolShapeOf(
      shape, stash_buckets,
      geometry.OlderTierBuckets(level, shape.digit),
      FinishCarryTierBuckets(geometry, level));
}

// Visits the finish pool shape of every ordinary digit that runs a merge and
// a pass.
template <typename Visit>
inline void ForEachOrdinaryFinishPool(const LevelArenaGeometry& geometry,
                                      const LevelArenaStashSizing& sizing,
                                      unsigned level, Visit&& visit) {
  const size_t carry = geometry.CarryBuckets(level);
  for (unsigned digit = 1; digit <= geometry.Fanout(level); ++digit) {
    if (geometry.PlanCarry(level, digit).outcome == CarryOutcome::kAdopt)
      continue;
    if (!FinishRunsPass(geometry, level, digit)) continue;
    const unsigned radix = digit >> static_cast<unsigned>(_tzcnt_u32(digit));
    const MergeShape shape = MakeMergeShape(carry, digit, radix);
    visit(FinishPoolShapeAt(geometry, sizing.Buckets(level), level, shape));
  }
}

// THE DFS WORKSPACE A LEVEL NEEDS: the widest pool and the deepest partition
// over its DFS passes, at its page count.  Zero pool when none distributes.
struct LevelDfsAllocation {
  size_t max_pool_buckets = 0;
  unsigned max_coarse_bits = 0;
  size_t pages = 0;
  bool any() const { return max_pool_buckets != 0; }
};

inline LevelDfsAllocation MaxLevelDfsAllocation(
    const LevelArenaGeometry& geometry, const LevelArenaStashSizing& sizing,
    unsigned level) {
  LevelDfsAllocation alloc;
  // One workspace serves every DFS pass of the level, at one page count.
  // That holds because a digit-1 finish above level 1 only drains its carry's
  // tier and never distributes, and both of the top's passes distribute one
  // page; a pool that did not would need a workspace of its own page count.
  const auto take = [&](size_t distributed, unsigned main_levels,
                        size_t pages, const ResidualRangePlan& plan) {
    if (!DfsResidualRangeApplies(distributed, main_levels)) return;
    if (alloc.pages != 0 && alloc.pages != pages) {
      throw std::invalid_argument(
          "level arena: the DFS passes of one level need different page "
          "counts");
    }
    alloc.pages = pages;
    alloc.max_pool_buckets = std::max(alloc.max_pool_buckets, distributed);
    alloc.max_coarse_bits = std::max(alloc.max_coarse_bits, plan.range_bits);
  };
  if (level == geometry.Levels()) {
    const auto shape = MakeTopMergeShape(geometry.CarryBuckets(level), geometry.TopDigit());
    const auto prepare = TopPreparePoolShapeOf(
        shape, sizing.Buckets(level), geometry.OlderTierBuckets(level, 0));
    take(prepare.swept_buckets, prepare.main_levels, kTopPrepareDfsPages,
         TopPrepareRangePlan(prepare));
    const auto merge = TopMergePoolShapeOf(shape, sizing.Buckets(level),
                                           geometry.CarryTierBuckets(level));
    take(merge.swept_buckets - merge.direct_buckets, merge.main_levels,
         FinishDfsPages(merge), LevelFinishRangePlan(merge));
    return alloc;
  }
  if (level > geometry.Levels()) return alloc;
  ForEachOrdinaryFinishPool(geometry, sizing, level,
                            [&](const LevelMergePoolShape& pool) {
    take(pool.swept_buckets - pool.direct_buckets, pool.main_levels,
         FinishDfsPages(pool), LevelFinishRangePlan(pool));
  });
  return alloc;
}

// The widest range table any pass at this level needs.  A thread's scratch is
// sized from the maximum over the levels it may execute -- and, at the top,
// over its two passes, which never hold their range tables at the same time.
// A DFS leaf table is FinishDfsPages stacked pages per coarse range, plus a
// separated pass's direct tier.
inline size_t MaxLevelMergeRangeBuckets(const LevelArenaGeometry& geometry,
                                        const LevelArenaStashSizing& sizing,
                                        unsigned level) {
  const size_t stash_buckets = sizing.Buckets(level);
  size_t widest = 0;
  // A finish's leaf table plus its direct tier.  A pass that sweeps nothing
  // builds no range table.
  const auto finish = [&](const LevelMergePoolShape& pool) {
    if (pool.swept_buckets == 0) return;
    widest = std::max(widest, LevelFinishRangePlan(pool).range_buckets +
                                 pool.direct_buckets);
  };
  if (level == geometry.Levels()) {
    const MergeShape shape = MakeTopMergeShape(geometry.CarryBuckets(level),
                                               geometry.TopDigit());
    const auto prep_pool = TopPreparePoolShapeOf(
        shape, stash_buckets, geometry.OlderTierBuckets(level, 0));
    widest = TopPrepareRangePlan(prep_pool).range_buckets;
    finish(TopMergePoolShapeOf(shape, stash_buckets,
                               geometry.CarryTierBuckets(level)));
    return widest;
  }
  ForEachOrdinaryFinishPool(geometry, sizing, level, finish);
  return widest;
}

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
