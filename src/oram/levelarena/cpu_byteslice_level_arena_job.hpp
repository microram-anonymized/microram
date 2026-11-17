#pragma once

// One merge as an OWNING object: its sources, its destination, its nonce, its
// shed storage, its residual passes and the two halves of its execution.
// DESIGN.md, "Carries and preparation" and "Top compaction and residuals",
// describes the design; "Threading rules" there numbers the rules cited below
// as "threading rule N".
//
// VOCABULARY.  A merge at digit j reads an OLDER operand A (the level's
// partial of j-1 carries, or at the top its current table) and a fresher
// CARRY B (a full table from the level below, or at level 1 a dense prefix),
// and writes the output C, a main table of j*U buckets plus its TIER (the
// bounded residual stash published beside it and probed with it).  A SHED is
// an entry a routing step could not place in its bucket; it waits in a stash
// until a RESIDUAL PASS offers it to a free slot of its final home or drains
// it into the output tier.  Sheds and tiers are RANKED by freshness so that
// the deduplication inside a residual pass keeps a key's newest copy.
//
// ONE JOB FOR EVERY LEVEL, the top included.  A top compaction is a different
// merge -- a full level against a carry, with a fixed digit, no partial of its
// own and no carry install -- but everything a JOB is is the same: the same
// binding and arrival validation, the same three phases, the same shed arena
// sized once, the same private tier masks, the same certified depths, the
// same residual builder and the same refusals.  The differences are named
// `top_` below, and each of them is a sentence.
//
// WHY A JOB AND NOT A FUNCTION.  A merge here is interrupted by construction:
// preparation runs when the destination slot is free, the carry arrives later
// -- possibly much later, from another thread -- and the finish runs then.
// Everything the preparation left behind has to survive that gap, still
// pointed at by nothing that moved:
//
//   - the sheds of every older block it routed, which no pass has resolved
//     yet (preparation retains its output and sheds until the finish);
//   - the ordinal, digit, family and destination generation it was planned
//     under, so that ARRIVAL VALIDATES rather than re-plans (threading
//     rule 6: reject a mismatched Ready instead of changing the prepared
//     nonce);
//   - the contexts themselves, which hold raw pointers into that storage.
//
// A function cannot own any of it, and a job that reallocated its stash
// vectors between the phases would leave the contexts pointing at freed
// memory.  So the storage is sized ONCE, at construction, for the widest merge
// this level can run, and never resized.
//
// THE THREE PHASES ARE THE MERGE HEADER'S, unchanged: this file supplies the
// contexts and the passes, and cpu_byteslice_level_arena_merge.hpp decides
// what runs.  The one thing added here that has no planner is the RESIDUAL
// WIRING:
//
//   THE FRESH CLASS AND THE OLDER CLASS ENTER THE FINISH'S ONE PASS AS TWO
//   RANKS, AND AT DIGIT 1 THERE IS NO ROUTE FOR THEM TO RIDE.
//
// Ordinary digits above one finish with separated sources: A's completed
// route residuals use one DFS leaf per coarse range, B's tier is offered
// directly, and the fixed insertion's own shed is the drain-only prefix.
// A has rank 2 (older); B and the insertion shed have rank 0 (fresher).
//
// Every pool source owns its masks. Input tiers borrow immutable payloads
// from pinned operands, while sheds own both payload and masks. Dedup and
// reset may change source masks; scatter and retag write the separate range
// table. Thus private tier descriptors can participate in the owned reset
// prefix, including the fresher tier class, without copying payloads.
//
// At level one's digit 1 the direct build writes the output and its tier,
// with no finish pass. A sparse digit-one carry drains its tier straight into
// the published tier (FinishPoolSlotsOf).

#include <immintrin.h>

#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_event.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_family.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_merge.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_merge_log.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_occupancy.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_pass_shape.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_stash.hpp"
#include "src/oram/rebuild/cpu_byteslice_residual_stash.hpp"
#include "src/oram/scheduler/cpu_byteslice_residual_pass.hpp"
#include "src/oram/scheduler/cpu_byteslice_subtask_cursor.hpp"
#include "src/oram/scheduler/cpu_byteslice_subtask_run.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/table/cpu_byteslice_tags.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

// ---------------------------------------------------------------------------
// The phase task list
// ---------------------------------------------------------------------------

// A subtask budget that never slices: every width is larger than any phase.
// A phase is PLANNED at this budget, which gives its coarse task list -- one
// task per range and one per butterfly block -- and then RUN at whatever
// budget its caller passes, which cuts each coarse task into pieces
// (PhaseCursor).  Callers that run a whole phase at a time pass this one too.
inline SubtaskBudget WholeLevelMergeBudget() {
  SubtaskBudget budget;
  const size_t all = ~size_t{0};
  budget.copy_buckets = all;
  budget.retag_buckets = all;
  budget.copy_retag_buckets = all;
  budget.butterfly_touches = all;
  budget.cross_pairs = all;
  budget.fixed_merge_pairs = all;
  budget.residual_scatter_buckets = all;
  budget.intersect_units = all;
  budget.residual_build_buckets = all;
  for (unsigned r = 0; r <= kMaxRadix; ++r) {
    budget.radix_dedup_tuples[r] = all;
    budget.radix_route_tuples[r] = all;
  }
  for (unsigned r = 0; r <= kMaxFixedMergeWays; ++r) {
    budget.radix_merge_units[r] = all;
  }
  return budget;
}

// A sink that counts what a planner emits.
struct SubtaskCounter {
  size_t tasks = 0;
  void push_back(const Subtask&) { ++tasks; }
};

// Coarse tasks a phase plans besides its routing, bounded by what the
// planners emit at the whole budget, where every range is one task:
//
//   per residual pass (at most kResidualPasses of them): two pool dedups, a
//     scatter and a retag, one route per two range bits (32 for a 64-bit
//     range), a sweep, a drain split around a leftover dedup (three), and a
//     reset -- 41. DFS substitutes two build tasks (gather and partition)
//     for scatter/retag/routing, so the same reservation covers top preparation;
//   per merge: three cross levels (digit 8), a radix pass, the fixed merge,
//     the two tombstone drops and a fused last butterfly level -- 8;
//   level 1's direct install: prefix dedup, home caching, selection and
//     remainder drain -- 4.
inline constexpr size_t kPhasePlanPassTasks = 41;
// Separated preparation adds one mask-clear and moves at most three binary
// levels plus one radix pass here; these fit the existing eight route tasks.
inline constexpr size_t kPhasePlanOtherTasks = 8 + 4;

// THE MOST COARSE TASKS ONE PHASE OF THIS LEVEL PLANS, which is what the job's
// task list is sized to at construction and never grows past.  The routing
// part -- the only part that grows with the table -- is COUNTED by running the
// routing planners themselves at the whole budget, since they are pure
// functions of the shape, so this bound cannot drift from what they emit.
inline size_t LevelPhasePlanCapacity(const LevelArenaGeometry& geometry,
                                     const Layout& layout, unsigned level) {
  const SubtaskBudget whole = WholeLevelMergeBudget();
  const size_t bucket_bytes = layout.BucketBytes();
  // A block's arrival: the tiled copy-then-route, or a direct
  // initialization's in-place retag and butterfly.
  const auto arrive = [&](size_t buckets, unsigned levels) {
    SubtaskCounter tiled;
    PlanCopyThenRoute(0, buckets, levels, bucket_bytes, whole, &tiled);
    SubtaskCounter in_place;
    PlanRange(Subtask::kRetagRange, 0, buckets, whole.copy_retag_buckets,
              &in_place);
    PlanButterfly(0, buckets, levels, whole.butterfly_touches, &in_place);
    return std::max(tiled.tasks, in_place.tasks);
  };
  size_t routing = 0;
  if (level == geometry.Levels()) {
    const MergeShape shape = MakeTopMergeShape(geometry.CarryBuckets(level),
                                               geometry.TopDigit());
    // The binary top routes all of T, one level short when its pass rides
    // the last level (PlanPrepareOlderHalf).
    routing = arrive(shape.out_buckets, shape.block_bits);
    if (shape.block_bits > 0) {
      routing = std::max(routing,
                         arrive(shape.out_buckets, shape.block_bits - 1));
    }
  } else {
    for (unsigned digit = 2; digit <= geometry.Fanout(level); ++digit) {
      const unsigned radix = digit >> static_cast<unsigned>(_tzcnt_u32(digit));
      const MergeShape shape =
          MakeMergeShape(geometry.CarryBuckets(level), digit, radix);
      SubtaskCounter older;
      PlanMergeOlderBlocks(shape.carry_bits, shape.odd_part, shape.power,
                           bucket_bytes, whole, &older);
      routing = std::max(routing, older.tasks);
    }
  }
  return routing + kResidualPasses * kPhasePlanPassTasks +
         kPhasePlanOtherTasks;
}

// ---------------------------------------------------------------------------
// The residual passes' work, from public shapes
// ---------------------------------------------------------------------------

// A sink that sums what the planned tasks cost (PieceTouches).
struct SubtaskTouchCounter {
  uint64_t touches = 0;
  void push_back(const Subtask& task) { touches += PieceTouches(task); }
};

// ONE RESIDUAL PASS'S WORK, in the touches the meter charges its pieces
// (PieceTouches).  The pass is the one a job binds from `slots` -- the same
// slot list (FinishPoolSlots, TopPreparePoolSlots, TopMergePoolSlots) -- over
// stash descriptors that have sizes and no storage, planned by the real
// residual planners; a DFS pass is priced (DfsResidualWorkspace::PriceOf)
// rather than configured, so nothing but descriptors is allocated.  With
// `offers`, it adds what the pass puts on the routing pass it rides: its
// FusedOfferWeight per output bucket, which the routing counts leave out.
// `drain_buckets` is the width of the pass's drain, and `range` how the pass
// builds its range table (the job's own PassRange for it).
//
// The two parts are returned apart, because they cost differently per touch:
// an offer merges a pool bucket into a main bucket, a planned pass sweeps,
// partitions or drains stash-sized buffers (LevelArenaRebuildCost prices
// them separately).
struct ResidualTouchSplit {
  double passes = 0;  // the planned residual passes
  double offers = 0;  // what they add to the routing pass they ride
  double total() const { return passes + offers; }
  ResidualTouchSplit& operator+=(const ResidualTouchSplit& other) {
    passes += other.passes;
    offers += other.offers;
    return *this;
  }
};

template <typename Slots>
inline ResidualTouchSplit ResidualPassPlannedTouches(const MergeShape& shape,
                                         const Layout& layout,
                                         size_t stash_buckets,
                                         size_t older_tier_buckets,
                                         size_t carry_tier_buckets,
                                         size_t drain_buckets,
                                         const PassRange& range,
                                         bool drop_unshadowed, bool offers,
                                         Slots&& slots,
                                         size_t merge_buckets = 0) {
  if (merge_buckets == 0) merge_buckets = stash_buckets;
  size_t count = 0;
  slots([&](const PoolSlot&) { ++count; });
  // One descriptor per slot and one for the drain, never reallocated: the
  // pass holds pointers into it.
  std::vector<ResidualStash> stashes(count + 1);
  for (ResidualStash& stash : stashes) stash.entry_bytes = layout.EntryBytes();
  ResidualStash& drain = stashes[count];
  drain.num_buckets = drain_buckets;
  ResidualPassSpec spec;
  spec.main = TableView{layout, shape.out_buckets, nullptr, nullptr};
  spec.main_levels = Log2Exact(shape.out_buckets);
  spec.scratch = 0;
  spec.lines = layout.PayloadLines();
  spec.drain = &drain;
  range.ApplyTo(&spec);
  size_t at = 0;
  const PoolRecipe recipe = slots([&](const PoolSlot& slot) {
    ResidualStash& stash = stashes[at++];
    stash.num_buckets = PoolSlotBuckets(slot, stash_buckets,
                                        older_tier_buckets, carry_tier_buckets);
    if (slot.storage == PoolSlotStorage::kOlderShed &&
        slot.index == shape.block_bits + kLevelMergeMergeStashOffset) {
      stash.num_buckets = merge_buckets;
    }
    if (slot.drain_only) ++spec.drain_only_slots;
    if (slot.tier_class) {
      spec.AddOwnedTierClass(&stash, slot.rank);
    } else {
      spec.AddOwned(&stash, slot.rank);
    }
  });
  spec.fuse = recipe.fuse;
  spec.rule = recipe.rule;
  spec.shed_slots = recipe.shed_slots;
  spec.force_active = recipe.force_active;
  RebuildStepContext ctx;
  ctx.drop_unshadowed = drop_unshadowed;
  std::vector<ResidualStash*> pool;
  std::vector<uint8_t> rank;
  const size_t range_buckets =
      BuildResidualPassFields(&ctx, 0, &pool, &rank, spec);
  ResidualPass& rp = ctx.residual[0];
  if (!rp.active) return {};
  if (range_buckets != 0) {
    AttachResidualRange(&rp, TableView{layout, range_buckets, nullptr, nullptr});
  }
  const size_t swept =
      ResidualPoolBuckets(rp.pool + rp.drain_only, DistributedPoolSlots(rp));
  if (rp.sweep_active &&
      DfsResidualRangeApplies(swept, spec.main_levels)) {
    DfsResidualWorkspace::Shape dfs;
    dfs.pool_buckets = swept;
    dfs.coarse_bits = rp.plan.range_bits;
    dfs.index_bits = rp.plan.index_bits;
    dfs.main_buckets = shape.out_buckets;
    rp.dfs_price = DfsResidualWorkspace::PriceOf(dfs, spec.dfs_pages);
  }
  const SubtaskBudget whole = WholeLevelMergeBudget();
  SubtaskTouchCounter counter;
  ResidualTouchSplit split;
  if (rp.fuse == ResidualFuseSite::kNone) {
    PlanResidualSecondChance(ctx, whole, 0, &counter);
  } else {
    PlanFusedPassPrologue(ctx, whole, rp.fuse, &counter,
                          rp.drain_only != 0 ? rp.pool[0] : nullptr);
    PlanFusedPassEpilogue(ctx, whole, rp.fuse, &counter);
    if (offers) {
      split.offers = double(uint64_t{FusedOfferWeight(ctx, rp.fuse)} *
                            shape.out_buckets);
    }
  }
  split.passes = double(counter.touches);
  return split;
}

// ONE JOB'S RESIDUAL WORK, in bucket touches: the passes a merge of `digit`
// at `level` plans -- the finish's one below the top, the preparation's and
// the merge's at the top, whose digit is the geometry's -- with the offers
// they add to the passes they ride.  `top_prepare_offers` false leaves out
// the offers of a top preparation that rides its own last butterfly level,
// which LevelArenaPrefixTouches already counts.  0 for a digit that adopts.
// The split form keeps the offers apart (ResidualTouchSplit).
inline ResidualTouchSplit LevelMergeResidualTouchSplit(
    const LevelArenaGeometry& geometry, const Layout& layout,
    const LevelArenaStashSizing& sizing, unsigned level, unsigned digit,
    bool top_prepare_offers = true) {
  if (level < 1 || level > geometry.Levels()) {
    throw std::invalid_argument("level arena: that level is not in this "
                                "hierarchy");
  }
  const size_t stash = sizing.Buckets(level);
  // A pass drains into the output's tier: this level's own width.
  const size_t out_tier = geometry.TierBucketsOf(level);
  const size_t older_tier = geometry.OlderTierBuckets(level, digit);
  if (level == geometry.Levels()) {
    const size_t carry_tier = geometry.CarryTierBuckets(level);
    const MergeShape shape =
        MakeTopMergeShape(geometry.CarryBuckets(level), geometry.TopDigit());
    // The preparation drains into its retained carry, a stash.
    ResidualTouchSplit split = ResidualPassPlannedTouches(
        shape, layout, stash, older_tier, carry_tier, stash,
        TopPreparePassRange(), /*drop=*/true, top_prepare_offers,
        [&](auto&& visit) { return TopPreparePoolSlots(shape, visit); });
    split += ResidualPassPlannedTouches(
        shape, layout, stash, older_tier, carry_tier, out_tier,
        FinishPassRange(TopMergePoolShapeOf(shape, stash, carry_tier)),
        /*drop=*/true, /*offers=*/true,
        [&](auto&& visit) { return TopMergePoolSlots(shape, visit); });
    return split;
  }
  if (geometry.PlanCarry(level, digit).outcome == CarryOutcome::kAdopt ||
      !FinishRunsPass(geometry, level, digit)) {
    return {};
  }
  const unsigned r = digit >> static_cast<unsigned>(_tzcnt_u32(digit));
  const MergeShape shape = MakeMergeShape(geometry.CarryBuckets(level), digit, r);
  const LevelMergePoolShape pool = FinishPoolShapeAt(geometry, stash, level, shape);
  return ResidualPassPlannedTouches(
      shape, layout, stash, older_tier, FinishCarryTierBuckets(geometry, level),
      out_tier, FinishPassRange(pool), /*drop=*/false, /*offers=*/true,
      [&](auto&& visit) {
        return FinishPoolSlotsAt(geometry, level, shape, visit);
      },
      MergeStashBuckets(geometry, stash, level));
}

inline double LevelMergeResidualTouches(const LevelArenaGeometry& geometry,
                                        const Layout& layout,
                                        const LevelArenaStashSizing& sizing,
                                        unsigned level, unsigned digit,
                                        bool top_prepare_offers = true) {
  return LevelMergeResidualTouchSplit(geometry, layout, sizing, level, digit,
                                      top_prepare_offers)
      .total();
}

// ---------------------------------------------------------------------------
// Lanes
// ---------------------------------------------------------------------------

// HOW MANY LANES A LEVEL'S STAGES RUN AT, from configuration and public sizes
// alone.  A lane costs a private stash array of the full certified depth and
// a fold per stage, and buys only the ability to run a stage's lanes on
// different threads -- so a level gets `lanes` only when its largest table
// reaches `min_buckets`.  Level 1 is no exception: its dense build and its
// residual passes are ordered stages, but its older half's route and its
// finish's fused offers divide like any level's.
struct LevelLaneConfig {
  size_t lanes = 1;
  size_t min_buckets = size_t{1} << 15;
};

// Words of one lane's private range masks at `level`: its widest range table,
// rounded up to a cache line so that lanes never write one line.  The job
// attaches only one residual pass per phase, so the widest table suffices.
// A one-lane job uses the phase's masks directly and needs no private copy.
inline size_t LaneRangeMaskStride(const LevelArenaGeometry& geometry,
                                  const LevelArenaStashSizing& sizing,
                                  unsigned level, size_t lanes) {
  if (lanes <= 1) return 0;
  const size_t words = MaxLevelMergeRangeBuckets(geometry, sizing, level);
  constexpr size_t kLine = 64 / sizeof(uint64_t);
  return (words + kLine - 1) / kLine * kLine;
}

// Folds one lane's stash into the phase's own, bucket after bucket, with the
// CHECKED merge, and empties the lane.  False when the fold would overflow
// `own`: each lane ran against a private stash of the full certified depth, so
// this is the only place their SUM is ever bounded.  Every bucket is merged,
// occupied or not, so the work is public.
inline bool FoldLaneStash(ResidualStash& own, ResidualStash& lane,
                          size_t lines) {
  for (size_t b = 0; b < lane.num_buckets; ++b) {
    if (!MergeBucketIntoResidualStash</*CheckOverflow=*/true>(
            own, lane.Bucket(b), lane.masks[b], lines)) {
      return false;
    }
  }
  lane.Reset();
  return true;
}

inline size_t LevelLaneCount(const LevelArenaGeometry& geometry,
                             unsigned level, const LevelLaneConfig& config) {
  if (config.lanes <= 1) return 1;
  const size_t table =
      level == geometry.Levels()
          ? geometry.TopBuckets()
          : geometry.CarryBuckets(level) * geometry.Fanout(level);
  return table >= config.min_buckets ? config.lanes : 1;
}

// ---------------------------------------------------------------------------
// LevelMergeScratch -- per LEVEL
// ---------------------------------------------------------------------------
//
// The range table a residual pass builds and sweeps.  It is transient -- it
// lives for one pass -- and it is PER LEVEL rather than per executing thread,
// because a phase may stop between two pieces with its range table
// attached while its thread runs another level's phase.  A table per thread
// would be clobbered by that second phase.

class LevelMergeScratch {
 public:
  // `dfs` sizes the level's DFS distributor workspace, which lives here for
  // the reason the range table does: a paused DFS pass keeps its pending
  // siblings in it.  None when no pass of the level distributes.
  LevelMergeScratch(const Layout& layout, size_t range_buckets,
                    const LevelDfsAllocation& dfs = {})
      : layout_(layout), buckets_(range_buckets) {
    if (range_buckets == 0) {
      throw std::invalid_argument("level arena: a finish needs range scratch");
    }
    data_ = AllocateTallied(CheckedTableBytes(range_buckets, layout),
                            ByteRole::kTransientScratch, &bytes_);
    masks_.assign(range_buckets, 0);
    bytes_.AddPlain(ByteRole::kTransientScratch,
                    range_buckets * sizeof(uint64_t));
    if (dfs.any()) {
      dfs_ = std::make_unique<DfsResidualWorkspace>(
          layout, dfs.max_pool_buckets, dfs.max_coarse_bits, dfs.pages);
      const DfsResidualWorkspace::Bytes got = dfs_->Allocated();
      bytes_.AddAligned64(ByteRole::kTransientScratch, got.data_bytes);
      bytes_.AddPlain(ByteRole::kTransientScratch, got.plain_bytes);
    }
    ExpectPredictedBytes(bytes_,
                         Bytes(layout, range_buckets, dfs),
                         "a thread's range scratch");
  }

  LevelMergeScratch(const LevelMergeScratch&) = delete;
  LevelMergeScratch& operator=(const LevelMergeScratch&) = delete;

  // One range table and its occupancy words: the constructor above, and
  // checked against it there.
  static LevelArenaByteBill Bytes(const Layout& layout,
                                  size_t range_buckets,
                                  const LevelDfsAllocation& dfs = {}) {
    LevelArenaByteBill bill;
    bill.AddAligned64(ByteRole::kTransientScratch,
                      CheckedTableBytes(range_buckets, layout));
    bill.AddPlain(ByteRole::kTransientScratch,
                  range_buckets * sizeof(uint64_t));
    if (dfs.any()) {
      const DfsResidualWorkspace::Bytes want = DfsResidualWorkspace::Planned(
          layout, dfs.max_pool_buckets, dfs.max_coarse_bits, dfs.pages);
      bill.AddAligned64(ByteRole::kTransientScratch, want.data_bytes);
      bill.AddPlain(ByteRole::kTransientScratch, want.plain_bytes);
    }
    return bill;
  }

  const LevelArenaByteBill& bytes() const { return bytes_; }
  size_t range_buckets() const { return buckets_; }
  // The level's DFS distributor, or null when none of its passes distributes.
  DfsResidualWorkspace* dfs() const { return dfs_.get(); }

  // A view of exactly `buckets`.  Refused rather than clamped: a range table
  // narrower than the pass was planned for sweeps the wrong extent, and one
  // wider runs off this allocation.
  TableView Range(size_t buckets) {
    if (buckets == 0 || buckets > buckets_) {
      throw std::logic_error(
          "level arena: a residual pass asked for a wider range table than "
          "this thread's scratch was sized for");
    }
    TableView v;
    v.layout = layout_;
    v.num_buckets = buckets;
    v.data = data_.get();
    v.masks = masks_.data();
    return v;
  }

 private:
  Layout layout_;
  size_t buckets_;
  LevelArenaByteBill bytes_;
  Aligned64Ptr data_;
  std::vector<uint64_t> masks_;
  std::unique_ptr<DfsResidualWorkspace> dfs_;
};

// ---------------------------------------------------------------------------
// What a job is bound to, and what arrives later
// ---------------------------------------------------------------------------

// Everything known BEFORE the carry exists.  Preparation runs on this alone.
//
// THE DIGIT, THE FAMILY AND THE NONCE ARE NOT HERE, because they are functions
// of (level, ordinal) and the job computes them itself.  Accepting them as
// well would be accepting redundant state, and redundant state is only ever as
// good as the weakest thing that checks it: a binding that carried a nonce
// would have the job VALIDATE a family it then does not use, and a wrong nonce
// -- one byte of it -- re-tags every entry under a hash the carry was never
// placed by, which the merge then quietly fails to deduplicate.  A digit that
// disagreed with its ordinal would pass any check the extents happened to fit.
// They are read back off the job (digit(), family(), nonce()), which is also
// what an owner should publish under: one source, not two that agree.
struct LevelMergeBinding {
  uint64_t ordinal = 0;  // the carry ordinal this merge will consume

  // The destination: j*U buckets of a slot this job's owner has leased, and
  // that slot's dedicated tier.  The job never takes the lease itself -- who
  // may write a slot is the arena's question
  // (cpu_byteslice_level_arena_slots.hpp) -- it is handed the views.
  TableView out;
  ResidualStash* out_tier = nullptr;
  uint64_t destination_generation = 0;  // the lease's, for arrival validation

  // The older operand and its tier: this level's partial at digit j-1, or --
  // at the top -- the whole of the published bank A.  Empty at digit 1, which
  // has no older half at all (dense build or binary sparse installation).
  TableView older_main;
  const ResidualStash* older_tier = nullptr;

  // THE OLDER OPERAND ALREADY SITS WHERE THE MERGE COPIES IT: `older_main` is
  // exactly `out` past the carry's U buckets (the whole of `out` at the top).
  // The synchronous engine's tables grow downward inside one region
  // (cpu_byteslice_level_arena_synchronous.hpp), so its copies are the
  // identity and CopyAndRetagRange only re-tags.  The plan, and so every
  // output byte, is the one a separate destination gets.  Any other overlap
  // is refused.
  bool in_place = false;
};

// The carry, once it is there.
struct LevelCarry {
  uint64_t ordinal = 0;
  Family family;  // the coordinate the producer published under; unset if dense
  // Sparse (level >= 2, and the top): the published inbox table and its tier.
  // The top never copies it -- its sweep reads the carry where it lies.
  TableView main;
  const ResidualStash* tier = nullptr;
  // Dense (level 1): the complete frozen prefix, Z/2 dense buckets.
  TableView dense_prefix;
};

// ---------------------------------------------------------------------------
// LevelMergeJob
// ---------------------------------------------------------------------------

class LevelMergeJob {
 public:
  // `aes_keys` is THE INSTANCE'S ROUND KEYS, and has no default on purpose.
  //
  // The nonce is public and allocated; the key is the per-ORAM secret, and it
  // is the only thing standing between an adversary and recomputing
  // tag(key) mod |level| -- which is the probe position, read straight off
  // the memory trace.  A job that quietly fell back to
  // DefaultAesTagKeys() would therefore place every entry it routes under a
  // schedule anyone can compute, and it would do so silently: the tags are
  // internally consistent, so a fixture that plants, routes and checks under
  // one key sees nothing wrong.  What it is NOT silent about is MIXING: a
  // carry published under one key and merged under another produces
  // duplicates and misrouted entries, so this parameter is also what keeps a
  // job and its operands on one hash.
  //
  // It is borrowed: the owner outlives its jobs (the keys are one allocation
  // per ORAM, made at construction), and copying an object with __m512i
  // members into every job would need the aligned allocation MakeAesTagKeys
  // exists for.
  //
  // `lanes` is the most LANES a stage of this level's phases may run at:
  // each lane sheds into private stashes of the full
  // certified depth, folded into the job's own in lane order when the stage
  // ends.  One keeps every stage on the job's own stashes.
  //
  // A distributing pass ("How each pass builds its range table") needs the
  // level's scratch to carry a DFS workspace (MaxLevelDfsAllocation).
  LevelMergeJob(const LevelArenaGeometry& geometry,
                const LevelArenaStashSizing& sizing, const Layout& layout,
                unsigned level, const AesTagKeys& aes_keys, size_t lanes = 1)
      : geometry_(&geometry), layout_(layout), level_(level),
        top_(level == geometry.Levels()), dense_(level == 1),
        stash_buckets_(sizing.Buckets(level)),
        merge_buckets_(MergeStashBuckets(geometry, stash_buckets_, level)),
        aes_keys_(&aes_keys),
        lanes_(JobLanes(lanes)) {
    if (level < 1 || level > geometry.Levels()) {
      throw std::out_of_range("level arena: no such level");
    }
    carry_buckets_ = geometry.CarryBuckets(level);
    // The widest block this level can route, taken from the CERTIFICATE that
    // sized its stash rather than recomputed: the depth is only valid for the
    // operation it was bought for, and two spellings of that operation are
    // two chances to buy it for the wrong one.  (Below the top the widest
    // digit is B, whose block is U_(l+1); at the top the map forces e = 0, so
    // the block is U_L whatever D is.)
    max_block_bits_ = sizing.At(level).block_bits;
    // ONE allocation per array, at the widest shape this level can reach, and
    // never resized: the contexts hold raw pointers into these across the
    // pause between preparation and the carry.  The top asks for one
    // slot more, for the preparation carry its own pass retains.
    older_sheds_ = MakeStashes(LevelMergeStashSlots(max_block_bits_, top_),
                                &older_storage_, merge_buckets_);
    if (dense_) AllocateDenseDirect(geometry);
    // The views' masks are inline, so a view holds any width up to the
    // stash's array; ResetStorage gives each its role's width per merge.
    for (auto& tier : tier_views_) {
      tier.num_buckets = geometry.TierBuckets();
      tier.entry_bytes = layout_.EntryBytes();
    }
    if (dense_) {
      dense_masks_.resize(geometry.DensePrefixBuckets());
      AddDenseLogBytes(&bytes_, geometry);
    }
    const size_t slots = PlanningSlots(geometry, sizing, level);
    pool_.reserve(slots);
    rank_.reserve(slots);
    pass_spec_.sources.reserve(slots);
    if (top_) {
      prep_pool_.reserve(slots);
      prep_rank_.reserve(slots);
    }
    bytes_.AddPlain(ByteRole::kPersistentScratch,
                    pass_spec_.sources.capacity() * sizeof(ResidualPassSourceSpec));
    for (const auto* pool : {&pool_, &prep_pool_})
      bytes_.AddPlain(ByteRole::kPersistentScratch,
                      pool->capacity() * sizeof(ResidualStash*));
    for (const auto* rank : {&rank_, &prep_rank_})
      bytes_.AddPlain(ByteRole::kPersistentScratch, rank->capacity());
    const size_t plan_tasks = LevelPhasePlanCapacity(geometry, layout, level);
    plan_.reserve(plan_tasks);
    bytes_.AddPlain(ByteRole::kPersistentScratch,
                    plan_.capacity() * sizeof(Subtask));
    // A stage and a lane unit each begin at a task, so neither outnumbers
    // the tasks (plus the one stage an empty phase still opens).
    stages_.reserve(plan_tasks + 1);
    bytes_.AddPlain(ByteRole::kPersistentScratch,
                    stages_.capacity() * sizeof(PlannedStage));
    unit_starts_.reserve(plan_tasks);
    bytes_.AddPlain(ByteRole::kPersistentScratch,
                    unit_starts_.capacity() * sizeof(size_t));
    if (lanes_ > 1) {
      lane_sheds_ = MakeStashes(lanes_ * older_sheds_.size(), &lane_storage_,
                                merge_buckets_);
      lane_ctx_.resize(lanes_);
      bytes_.AddPlain(ByteRole::kPersistentScratch,
                      lane_ctx_.capacity() * sizeof(RebuildStepContext));
      lane_cursors_.resize(lanes_);
      bytes_.AddPlain(ByteRole::kPersistentScratch,
                      lane_cursors_.capacity() * sizeof(LaneCursor));
      lane_mask_stride_ = LaneRangeMaskStride(geometry, sizing, level, lanes_);
      if (lane_mask_stride_ != 0) {
        const size_t bytes = lanes_ * lane_mask_stride_ * sizeof(uint64_t);
        lane_masks_ =
            AllocateTallied(bytes, ByteRole::kPersistentScratch, &bytes_);
        std::memset(lane_masks_.get(), 0, bytes);
      }
    }
    ExpectPredictedBytes(
        bytes_, StorageBytes(geometry, sizing, layout, level, lanes_),
        "a level's merge job");
  }

  LevelMergeJob(const LevelMergeJob&) = delete;
  LevelMergeJob& operator=(const LevelMergeJob&) = delete;

  // Persistent payload, mask and planning buffers, fixed at construction.
  // Inline descriptors are part of the job object, not separate buffers.
  static LevelArenaByteBill StorageBytes(const LevelArenaGeometry& geometry,
                                         const LevelArenaStashSizing& sizing,
                                         const Layout& layout,
                                         unsigned level, size_t lanes = 1) {
    const bool top = level == geometry.Levels();
    const bool dense = level == 1;
    lanes = JobLanes(lanes);
    const size_t stash_buckets = sizing.Buckets(level);
    const size_t older_slots =
        LevelMergeStashSlots(sizing.At(level).block_bits, top);
    // Each older slot may be a digit's merge slot, so all are allocated at
    // the merge width (MakeStashes).
    const size_t older_width =
        MergeStashBuckets(geometry, stash_buckets, level);
    LevelArenaByteBill bill;
    AddStashBytes(&bill, layout, older_slots, older_width);
    if (dense) AddDenseLogBytes(&bill, geometry);
    if (dense) {
      AddDenseDirectBytes(&bill, geometry, layout);
    }
    const size_t slots = PlanningSlots(geometry, sizing, level);
    bill.AddPlain(ByteRole::kPersistentScratch,
                  slots * sizeof(ResidualPassSourceSpec));
    bill.AddPlain(ByteRole::kPersistentScratch,
                  slots * sizeof(ResidualStash*), top ? 2 : 1);
    bill.AddPlain(ByteRole::kPersistentScratch, slots, top ? 2 : 1);
    const size_t plan_tasks = LevelPhasePlanCapacity(geometry, layout, level);
    bill.AddPlain(ByteRole::kPersistentScratch, plan_tasks * sizeof(Subtask));
    bill.AddPlain(ByteRole::kPersistentScratch,
                  (plan_tasks + 1) * sizeof(PlannedStage));
    bill.AddPlain(ByteRole::kPersistentScratch, plan_tasks * sizeof(size_t));
    if (lanes > 1) {
      AddStashBytes(&bill, layout, lanes * older_slots, older_width);
      bill.AddPlain(ByteRole::kPersistentScratch,
                    lanes * sizeof(RebuildStepContext));
      bill.AddPlain(ByteRole::kPersistentScratch, lanes * sizeof(LaneCursor));
      const size_t stride = LaneRangeMaskStride(geometry, sizing, level, lanes);
      if (stride != 0) {
        bill.AddAligned64(ByteRole::kPersistentScratch,
                          lanes * stride * sizeof(uint64_t));
      }
    }
    return bill;
  }

  const LevelArenaByteBill& bytes() const { return bytes_; }

  unsigned level() const { return level_; }
  size_t lanes() const { return lanes_; }
  // Stages that ran divided into more than one lane, over the job's life.
  // Atomic and relaxed like the stage timings: a report may read them while
  // an owner or a helper folds a stage (the benchmark's --settle snapshot).
  uint64_t laned_stages() const {
    return laned_stages_.load(std::memory_order_relaxed);
  }
  // Of those, the offer stages whose lanes cleared private range masks.
  uint64_t private_mask_stages() const {
    return private_mask_stages_.load(std::memory_order_relaxed);
  }
  bool top() const { return top_; }
  bool dense() const { return dense_; }
  const AesTagKeys& aes_keys() const { return *aes_keys_; }
  // Derived from (level, ordinal) at Begin, and the only spelling of each.
  unsigned digit() const { return digit_; }
  const RebuildNonce& nonce() const { return nonce_; }
  bool bound() const { return bound_; }
  bool prepared() const { return prepared_; }
  bool installed() const { return installed_; }

  // ---- helpers -------------------------------------------------------------
  //
  // A job whose stages run in lanes may SHARE its phases with helper threads:
  // any thread claims the running stage's lanes, and whoever finishes a
  // stage's last lane folds it and opens the next.  Only the owner thread
  // crosses a phase boundary -- binds, installs, starts and ends a phase --
  // and helpers only ever run lanes.  `helpers` is the event the helpers
  // park on, signalled when a stage opens or a lane is paused; `owner` is the
  // owner group's, signalled when a helper opens a stage or finishes a phase,
  // since the owner may have gone to sleep waiting for exactly that.  `budget`
  // is the level's piece budget, which helpers cut their pieces at too.
  // Attach before the helper threads start; a job with one lane has nothing
  // to share.
  void AttachHelpers(OwnerEvent* helpers, OwnerEvent* owner,
                     const SubtaskBudget& budget) {
    if (lanes_ <= 1) return;
    helper_event_ = helpers;
    owner_event_ = owner;
    shared_budget_ = budget;
  }
  bool shared() const { return helper_event_ != nullptr; }
  // The last Continue call stopped because every lane of the running stage
  // was held by a helper -- nothing is wrong, and the owner has nothing to do
  // for this job until the helpers finish (LevelBlock::kHelpersBusy).
  bool waiting_on_helpers() const { return waiting_on_helpers_; }
  // Whether the owner's next Continue call, after one that stopped on
  // waiting_on_helpers(), would find anything: a lane put back or never
  // claimed, or the phase a helper ended.  A snapshot, for the owner group's
  // preemption test.
  bool OwnerHasSharedWork() const {
    if (phase_done_.load(std::memory_order_acquire)) return true;
    if (paused_lanes_.load(std::memory_order_acquire) != 0) return true;
    const uint64_t word = claim_.load(std::memory_order_acquire);
    return ClaimNext(word) < ClaimLanes(word);
  }

  // ---- stage timing --------------------------------------------------------
  //
  // Off by default.  On, every piece's wall time is added to its subtask kind
  // and to its stage's class -- ORDERED, or DIVISIBLE by lanes -- by whichever
  // thread ran it.  The ordered class at one thread is the serial share that
  // bounds what lanes and helpers can buy.  Two clock reads per piece.
  //
  // A laned stage's FOLD is ordered work too -- one thread merges every
  // lane's stash into the phase's, after the last lane -- and it is no piece:
  // it runs outside the piece budget, and nothing but this timer sees it.  So
  // its time is added to the ordered class and kept apart in fold_nanos(),
  // since it grows with lanes, shedding slots, stash depth squared and entry
  // width rather than with the table.
  static constexpr size_t kTimedKinds =
      static_cast<size_t>(Subtask::kDropErased) + 1;
  void EnableStageTiming(bool on) { timing_ = on; }
  uint64_t kind_nanos(Subtask::Kind kind) const {
    return kind_nanos_[static_cast<size_t>(kind)].load(
        std::memory_order_relaxed);
  }
  uint64_t ordered_nanos() const {
    return class_nanos_[0].load(std::memory_order_relaxed);
  }
  uint64_t divisible_nanos() const {
    return class_nanos_[1].load(std::memory_order_relaxed);
  }
  // The folds' share of ordered_nanos().
  uint64_t fold_nanos() const {
    return fold_nanos_.load(std::memory_order_relaxed);
  }
  // Wall time from each phase's start to its end, summed over the job's life,
  // and how many phases of each kind ended -- with timing on.  With helpers
  // this is the phase's elapsed time, which the owner's own time is not.
  // Atomic like the piece timings, because a report may read them while the
  // owner runs (the benchmark's --settle snapshot does); relaxed, because
  // they order nothing, so two of them may describe different instants.
  uint64_t phase_wall_nanos(LevelMergePhase phase) const {
    return phase_wall_[static_cast<size_t>(phase)].load(
        std::memory_order_relaxed);
  }
  uint64_t phases_ended(LevelMergePhase phase) const {
    return phases_ended_[static_cast<size_t>(phase)].load(
        std::memory_order_relaxed);
  }
  // THE SAME PIECE TIME BY PHASE AND CLASS, with each piece's estimated
  // touches (PieceTouches), over the job's life -- with timing on.  The
  // per-merge log (cpu_byteslice_level_arena_merge_log.hpp) takes one merge's
  // share as the difference of two snapshots; read it where the job is
  // between phases or its phase's lanes have all ended.
  LevelMergeCost cost() const {
    LevelMergeCost out;
    for (unsigned p = 0; p < LevelMergeCost::kPhases; ++p) {
      for (unsigned c = 0; c < LevelMergeCost::kClasses; ++c) {
        out.nanos[p][c] = cost_nanos_[p][c].load(std::memory_order_relaxed);
        out.touches[p][c] = cost_touches_[p][c].load(std::memory_order_relaxed);
      }
    }
    return out;
  }
  // When the current job's preparation ended (steady_clock ns), with timing
  // on; zero before it has.  The owner's alone, like the phase it stamps.
  uint64_t prepare_end_ns() const { return prepare_end_ns_; }

  // A HELPER'S TURN: claim one lane of the running stage, run it to its end,
  // and fold and open the next stage if it was the stage's last.  Returns
  // whether it ran anything.  Never crosses a phase boundary.  Safe to call
  // from any number of threads at once, and while the owner is running the
  // same phase's lanes.
  bool HelpOnce() {
    if (!shared_open_.load(std::memory_order_acquire)) return false;
    size_t lane = 0;
    size_t stage = 0;
    size_t lanes = 0;
    if (!ClaimLane(&lane, &stage, &lanes)) return false;
    RunClaimedLane(lane, stage, lanes, /*by_owner=*/false, NeverYield{});
    return true;
  }
  uint64_t ordinal() const { return binding_.ordinal; }
  const Family& family() const { return family_; }
  // The destination occupancy this job was bound to.  The owner compares it
  // against the lease it still holds before it lets the job finish; nothing
  // here can, because a job is handed views and never the lease itself.
  uint64_t destination_generation() const {
    return binding_.destination_generation;
  }
  const MergeShape& shape() const { return shape_; }

  // ---- binding ------------------------------------------------------------

  // Bind the next merge.  Everything here is a function of public counters and
  // of a lease this level's owner already holds; nothing reads the carry.
  void Begin(const LevelMergeBinding& binding) {
    if (bound_) {
      throw std::logic_error(
          "level arena: this level already has a pending job");
    }
    // Derive first, then validate the caller's storage against what the
    // coordinate says it must be.  CarryDigit refuses a zero ordinal, which is
    // the one thing that has to be checked before anything is derived.
    if (binding.ordinal == 0) {
      throw std::invalid_argument("level arena: carry ordinals are one-based");
    }
    NoteOccupancyJob();
    // The top has no odometer: it is always D and always a compaction of A
    // plus the carry into C (PlanCarry says the same).
    digit_ = top_ ? geometry_->TopDigit()
                  : geometry_->CarryDigit(level_, binding.ordinal);
    family_ = CanonicalFamily(*geometry_, level_, binding.ordinal);
    nonce_ = FamilyNonce(family_);
    Validate(binding);
    binding_ = binding;
    // At the top the route is binary (MakeTopMergeShape); below it the
    // radix is the digit's odd part.
    shape_ = LevelMergeShapeOf(*geometry_, level_, digit_);
    if (shape_.block_bits > max_block_bits_) {
      throw std::logic_error(
          "level arena: a merge at this level is wider than its job's "
          "storage");
    }
    ResetStorage();
    BuildContexts();
    // Bind the older payload and snapshot its masks before preparation.
    // The owner pins it through publication. Initialization has no older
    // tier; its zero-masked descriptor keeps the same public pool shape.
    if (HasOlderHalf() && binding_.older_tier != nullptr) {
      BorrowTier(binding_.older_tier, &tier_views_[kOlderTierView]);
    }
    // Checked HERE as well as at every phase, and the difference is where the
    // refusal lands: a layout that cannot hold this merge's tag is a property
    // of the job's construction, not of the phase that happens to run first,
    // and binding is the last moment at which nothing has been written yet.
    ExpectLevelMergeContexts(contexts_, spec_);
    bound_ = true;
    prepared_ = false;
    installed_ = false;
    prepare_end_ns_ = 0;
  }

  // ---- phase 1 ------------------------------------------------------------

  // Copy, re-tag and route every older block.  Touches no carry data, so it
  // may run long before the carry exists -- all it needed was the destination.
  // A digit-1 merge has no older half and this is a no-op that still marks the
  // job prepared, so the two paths converge on one state machine.
  //
  // `scratch` IS REQUIRED AT THE TOP and ignored everywhere else.  The top's
  // preparation ends in a residual pass of its own (it retains its
  // preparation residuals), because its radix pass finishes C's route and so
  // every entry of A is already in its final bucket; a non-top preparation has
  // no such pass and holds its sheds for the finish instead.  The scratch is
  // borrowed for this call only -- the pass is built, swept and drained inside
  // the phase, and what survives it is the retained carry stash.
  void PrepareOlder(const SubtaskBudget& budget,
                    LevelMergeScratch* scratch = nullptr) {
    RunWhole(ContinuePrepare(budget, scratch, NeverYield{}));
  }

  // THE RESUMABLE FORM, which the three phases all have.  Runs the phase in
  // pieces of `budget` and asks `yield()` after every piece that leaves work
  // behind; returns true once the phase has finished, false when it stopped
  // because `yield` said so.  Calling it again resumes where it stopped -- the
  // plan and the position are the job's (PhaseCursor) -- and must pass the
  // same scratch, since a paused pass keeps its range table attached.  The
  // output is byte-identical at every budget and at every stopping point.
  template <class Yield>
  bool ContinuePrepare(const SubtaskBudget& budget, LevelMergeScratch* scratch,
                       Yield&& yield) {
    RequireBound();
    if (!phase_running_) {
      if (prepared_) {
        throw std::logic_error("level arena: this job is already prepared");
      }
      if (top_) {
        if (scratch == nullptr) {
          throw std::invalid_argument(
              "level arena: the top's preparation ends in a residual pass and "
              "needs the level's range scratch");
        }
        BuildTopPreparePass(scratch, PrepCarry());
      } else if (digit_ == 1) {
        prepared_ = true;
        NotePrepared();
        return true;
      }
      StartPhase(LevelMergePhase::kPrepareOlder, scratch);
    }
    if (!ContinuePhase(LevelMergePhase::kPrepareOlder, budget, scratch,
                       yield)) {
      return false;
    }
    prepared_ = true;
    NotePrepared();
    return true;
  }

  // ---- phases 2 and 3 -----------------------------------------------------

  // Phase 2: put the carry into the output's first U buckets -- a fused copy
  // and re-tag, or, at level 1, the dense builder.  ARRIVAL VALIDATES here:
  // a carry that does not match what this job was prepared under is rejected,
  // because re-planning the nonce or the geometry now would leave the
  // already-routed older half under the old one (threading rule 6).
  //
  // Preparation runs first if it has not: the unsplit path calls the same
  // preparation and finish helpers in sequence, so there is one
  // algorithm and one residual wiring whether or not the level got ahead.
  //
  // At the top there is no kernel here at all: the sweep reads the carry from
  // the inbox where it lies, so this phase is where the carry is bound and
  // validated and nothing else.  It stays a phase because one state
  // machine for every level is worth more than a saved call.
  void InstallCarry(const LevelCarry& carry, const SubtaskBudget& budget,
                    LevelMergeScratch* scratch = nullptr) {
    RunWhole(ContinueInstall(carry, budget, scratch, NeverYield{}));
  }

  // Resumable, as ContinuePrepare is.  A preparation still in progress is
  // resumed first, in the same call and under the same yield, and the carry
  // is bound only once it has finished.  The carry must be the same on every
  // call of one install; it is validated on each.
  template <class Yield>
  bool ContinueInstall(const LevelCarry& carry, const SubtaskBudget& budget,
                       LevelMergeScratch* scratch, Yield&& yield) {
    RequireBound();
    if (installed_) {
      throw std::logic_error("level arena: this job already took its carry");
    }
    ValidateArrival(carry);
    if (!prepared_ && !ContinuePrepare(budget, scratch, yield)) return false;
    if (!phase_running_) {
      BindCarry(carry);
      StartPhase(LevelMergePhase::kInstallCarry, scratch);
    }
    if (!ContinuePhase(LevelMergePhase::kInstallCarry, budget, scratch,
                       yield)) {
      return false;
    }
    installed_ = true;
    return true;
  }

  // Phase 3: the deduplicating cross levels, the ordered radix pass and the
  // residual second chance, whose leftovers become the published tier.
  // `scratch` is the executing thread's and is borrowed only for this call.
  void FinishMerge(LevelMergeScratch* scratch, const SubtaskBudget& budget) {
    RunWhole(ContinueFinish(scratch, budget, NeverYield{}));
  }

  // Resumable, as ContinuePrepare is.
  template <class Yield>
  bool ContinueFinish(LevelMergeScratch* scratch, const SubtaskBudget& budget,
                      Yield&& yield) {
    RequireBound();
    if (!installed_) {
      throw std::logic_error(
          "level arena: a merge cannot finish before its carry is installed");
    }
    if (!phase_running_) {
      if (scratch == nullptr) {
        throw std::invalid_argument(
            "level arena: a finish needs range scratch");
      }
      BuildFinishPass(scratch);
      StartPhase(LevelMergePhase::kFinish, scratch);
    }
    if (!ContinuePhase(LevelMergePhase::kFinish, budget, scratch, yield)) {
      return false;
    }
    ObserveFinalTier();
    bound_ = false;
    prepared_ = false;
    installed_ = false;
    return true;
  }

  // The two above, for a caller with nothing to do between them.
  void Finish(const LevelCarry& carry, LevelMergeScratch* scratch,
              const SubtaskBudget& budget) {
    InstallCarry(carry, budget, scratch);
    FinishMerge(scratch, budget);
  }

  // ---- direct initialization (DESIGN.md, "Direct initialization") --------
  //
  // BUILD THE TOP OUT OF RECORDS ALREADY IN ITS BANK.  The caller has
  // scattered `count` records over the destination's T buckets at the load
  // the geometry gives it (ScatterInitialRecords); what is left is to hash
  // them under this family's nonce and route them into their final buckets,
  // which is exactly what an ordinary top PREPARATION does to A.
  //
  // So this runs that preparation, with two differences and no third:
  //
  //   1. the source is already in the workspace, so the fused copy-and-re-tag
  //      becomes a re-tag (RebuildStepContext::source_in_place).  The binding
  //      says so by naming the OUTPUT as the older operand, which is checked;
  //   2. what the residual offer cannot place drains into the PUBLISHED TIER
  //      rather than into the retained carry stash, because there is no
  //      finish to resolve it in.  A residual only fails the offer when its
  //      true bucket is genuinely full, so what survives is bounded by the
  //      tier exactly as an ordinary merge's leftovers are.
  //
  // There is no older tier: nothing preceded this table.  The pool still
  // carries the tier-view slot, empty, so that the pass has the same SHAPE
  // the thread's range scratch was sized for -- a pool that differed would be
  // a second certificate nobody bought.
  //
  // kDistinct is the caller's promise and is what makes kNoDedup exact here,
  // the same way "A holds each key at most once" makes it exact for an
  // ordinary preparation.
  void RouteInitialTop(const LevelMergeBinding& binding,
                       LevelMergeScratch* scratch,
                       const SubtaskBudget& budget) {
    if (!top_) {
      throw std::logic_error(
          "level arena: direct initialization builds the top and nothing "
          "else");
    }
    if (scratch == nullptr) {
      throw std::invalid_argument(
          "level arena: the initialization route ends in a residual pass and "
          "needs the executing thread's range scratch");
    }
    initializing_ = true;
    try {
      Begin(binding);
      prepare_.source_in_place = true;
      BuildTopPreparePass(scratch, binding_.out_tier);
      StartPhase(LevelMergePhase::kPrepareOlder, scratch);
      RunWhole(ContinuePhase(LevelMergePhase::kPrepareOlder, budget, scratch,
                             NeverYield{}));
    } catch (...) {
      initializing_ = false;
      CloseAbandonedPhase();
      Cancel();
      throw;
    }
    initializing_ = false;
    ObserveFinalTier();
    // Nothing follows: the table is routed, its leftovers are in the tier,
    // and the caller publishes.  The job goes back to unbound rather than to
    // "prepared", because there is no carry coming for it.
    Cancel();
  }

  // A phase that failed part-way can leave its stage open, with lanes nobody
  // has claimed yet.  Close it, so that a helper started later finds nothing
  // to run: the shared executor is shut, the claim word names no claimable
  // lane, and the phase reads as ended.  Only where no other thread can be
  // inside the job: a direct initialization runs before any helper starts.
  void CloseAbandonedPhase() {
    shared_open_.store(false, std::memory_order_relaxed);
    paused_lanes_.store(0, std::memory_order_relaxed);
    done_lanes_.store(0, std::memory_order_relaxed);
    claim_.store(PackClaim(++claim_seq_, 0, 0), std::memory_order_release);
    phase_done_.store(true, std::memory_order_release);
  }

  // Give up an unpublished merge (shutdown, cancellation).  The destination is
  // the owner's to hand back; this only forgets the job.
  void Cancel() {
    bound_ = false;
    prepared_ = false;
    installed_ = false;
    phase_running_ = false;
    phase_scratch_ = nullptr;
  }

  // ---- diagnostics --------------------------------------------------------
  //
  // Counts of SHED entries are secret, so nothing in the engine may branch on
  // them.  They are here for checked fixtures, which is also where the
  // uniqueness and freshness checks live.

  const ResidualStash* older_sheds() const { return older_sheds_.data(); }
  size_t older_shed_slots() const { return older_sheds_.size(); }
  const ResidualStash* dense_tier() const {
    return dense_ ? &dense_tier_ : nullptr;
  }

 private:
  // ---- storage ------------------------------------------------------------

  // What one MakeStashes call costs, in the one spelling both it and
  // StorageBytes use.
  static void AddStashBytes(LevelArenaByteBill* bill, const Layout& layout,
                            size_t slots, size_t buckets) {
    bill->AddAligned64(ByteRole::kPersistentScratch,
                       CheckedTableBytes(CheckedSizeMul(slots, buckets, "stash buckets"),
                                         layout));
    bill->AddPlain(ByteRole::kPersistentScratch,
                   slots * sizeof(ResidualStash));
  }

  // A conservative slot bound shared by reservation and buffer accounting.
  // It covers route sheds and both input tiers.
  static size_t PlanningSlots(const LevelArenaGeometry& geometry,
                              const LevelArenaStashSizing& sizing,
                              unsigned level) {
    return LevelMergeStashSlots(sizing.At(level).block_bits,
                                level == geometry.Levels()) + 2;
  }

  static void AddDenseLogBytes(LevelArenaByteBill* bill,
                               const LevelArenaGeometry& geometry) {
    bill->AddPlain(ByteRole::kPersistentScratch,
                   geometry.DensePrefixBuckets() * sizeof(uint64_t));
  }

  // Every older slot at the route depth but this merge's merge slot, in the
  // job's array and in every lane's: which slot that is moves with the
  // digit's block depth.
  void SetStashWidths() {
    const size_t merge = shape_.block_bits + kLevelMergeMergeStashOffset;
    const size_t per_lane = older_sheds_.size();
    for (size_t i = 0; i < older_sheds_.size(); ++i) {
      older_sheds_[i].num_buckets = i == merge ? merge_buckets_ : stash_buckets_;
    }
    for (size_t i = 0; i < lane_sheds_.size(); ++i) {
      lane_sheds_[i].num_buckets =
          i % per_lane == merge ? merge_buckets_ : stash_buckets_;
    }
  }

  // A DIRECTLY BUILT LEVEL ONE's storage: B's main above digit one (U_1
  // buckets and their masks), B's one-bucket tier, and the home cache, two
  // byte lines at most per prefix bucket.  The prefix's private masks are
  // AddDenseLogBytes', as for the butterfly build.
  static size_t DenseHomeBytes(const LevelArenaGeometry& geometry) {
    return CheckedSizeMul(
        CheckedSizeMul(geometry.DensePrefixBuckets(),
                       DenseHomeLines(Log2Exact(geometry.RoutedPrefixBuckets())),
                       "dense home lines"),
        kBucketCapacity, "dense home bytes");
  }

  static void AddDenseDirectBytes(LevelArenaByteBill* bill,
                                  const LevelArenaGeometry& geometry,
                                  const Layout& layout) {
    const size_t homes = geometry.RoutedPrefixBuckets();
    bill->AddAligned64(ByteRole::kPersistentScratch,
                       CheckedTableBytes(homes, layout));
    bill->AddPlain(ByteRole::kPersistentScratch, homes * sizeof(uint64_t));
    bill->AddAligned64(ByteRole::kPersistentScratch,
                       CheckedTableBytes(kDenseDirectTierBuckets, layout));
    bill->AddAligned64(ByteRole::kPersistentScratch, DenseHomeBytes(geometry));
  }

  void AllocateDenseDirect(const LevelArenaGeometry& geometry) {
    const size_t homes = geometry.RoutedPrefixBuckets();
    dense_b_data_ = AllocateTallied(CheckedTableBytes(homes, layout_),
                                    ByteRole::kPersistentScratch, &bytes_);
    dense_b_masks_.assign(homes, 0);
    bytes_.AddPlain(ByteRole::kPersistentScratch, homes * sizeof(uint64_t));
    dense_tier_storage_ = AllocateTallied(
        CheckedTableBytes(kDenseDirectTierBuckets, layout_),
        ByteRole::kPersistentScratch, &bytes_);
    dense_tier_.data = dense_tier_storage_.get();
    dense_tier_.num_buckets = kDenseDirectTierBuckets;
    dense_tier_.entry_bytes = layout_.EntryBytes();
    dense_homes_ = AllocateTallied(DenseHomeBytes(geometry),
                                   ByteRole::kPersistentScratch, &bytes_);
  }

  // B's main above digit one: the job's own U_1 buckets.
  TableView DenseBView() {
    return TableView{layout_, dense_b_masks_.size(), dense_b_data_.get(),
                     dense_b_masks_.data()};
  }

  // `width` is each slot's physical depth, at least the route depth; every
  // slot starts at the route depth and SetStashWidths widens the merge slot.
  std::vector<ResidualStash> MakeStashes(size_t slots, Aligned64Ptr* storage,
                                         size_t width = 0) {
    const size_t buckets = width == 0 ? stash_buckets_ : width;
    if (buckets > kMaxResidualStashBuckets) {
      throw std::invalid_argument(
          "level arena: a stash is deeper than its occupancy array");
    }
    const size_t bytes = CheckedTableBytes(
        CheckedSizeMul(slots, buckets, "stash buckets"), layout_);
    *storage = AllocateTallied(bytes, ByteRole::kPersistentScratch, &bytes_);
    bytes_.AddPlain(ByteRole::kPersistentScratch,
                    slots * sizeof(ResidualStash));
    uint8_t* base = storage->get();
    std::memset(base, 0, bytes);
    std::vector<ResidualStash> stashes(slots);
    for (size_t i = 0; i < slots; ++i) {
      stashes[i].data = base + i * buckets * layout_.BucketBytes();
      stashes[i].num_buckets = stash_buckets_;
      stashes[i].entry_bytes = layout_.EntryBytes();
    }
    return stashes;
  }

  void ResetStorage() {
    for (ResidualStash& s : older_sheds_) s.Reset();
    for (ResidualStash& s : lane_sheds_) s.Reset();
    dense_tier_.Reset();
    SetStashWidths();
    // Each view's width is its role's at this (level, digit), which is what
    // the pool shapes the scratch was sized from assume: the older operand's
    // tier and the carry's (LevelArenaGeometry::OlderTierBuckets and
    // CarryTierBuckets, one width unless the geometry has a tier profile).
    tier_views_[kOlderTierView].num_buckets =
        geometry_->OlderTierBuckets(level_, digit_);
    tier_views_[kCarryTierView].num_buckets =
        geometry_->CarryTierBuckets(level_);
    for (ResidualStash& s : tier_views_) {
      s.Reset();
      // Even empty sources are read by oblivious kernels. The initial top
      // has no tier, so borrow the output tier for zero-masked reads: the
      // top's older view is its own width, the output's, even for a tiny
      // top main.
      s.data = binding_.out_tier->data;
    }
    // AND the destination tier, because a merge writes its WHOLE output and
    // the finish drains into this tier rather than overwriting it.  A slot's
    // tier is also emptied when an occupancy begins (LevelArena::TryLease),
    // but one forwarding lease is one occupancy holding P_2, P_4, ..., P_b in
    // turn: without this, each would be published with its predecessor's
    // leftovers still in it, and a merge that consumes it as a carry ranks
    // the carry's tier freshest, so those stale copies would win.  Safe here
    // for the reason overwriting the main is: the owner binds a job only once
    // the destination is writable (AcquireDestination, WritableAt).  The
    // older operand's tier is never this one (Validate), and the carry's
    // lives in this level's inbox, which is never this level's destination.
    binding_.out_tier->Reset();
    pool_ = {};
    rank_ = {};
    prep_pool_ = {};
    prep_rank_ = {};
  }

  // ---- validation ---------------------------------------------------------

  static void Expect(bool ok, const char* what) {
    if (!ok) throw std::invalid_argument(std::string("level arena: ") + what);
  }

  void RequireBound() const {
    if (!bound_) throw std::logic_error("level arena: this job is not bound");
  }

  // `digit_`, `family_` and `nonce_` are already derived when this runs; what
  // it checks is that the caller's storage matches them.
  void Validate(const LevelMergeBinding& binding) const {
    // Digit 1 uses this same partial pipeline when binary P_1 must leave
    // its inbox. Other receiving levels can still adopt without a job.
    Expect(geometry_->PlanCarry(level_, binding.ordinal).outcome !=
               CarryOutcome::kAdopt,
           "an adopted carry does not run a merge job");
    Expect(!top_ || !dense_, "the top has no dense prefix builder");
    Expect(binding.out.data != nullptr &&
               binding.out.num_buckets == digit_ * carry_buckets_,
           "the destination is not j*U buckets, for the digit this ordinal "
           "has");
    // AND IT IS THIS JOB'S LAYOUT.  A view carries its own, the job derives
    // its map and its stash widths from the one it was constructed with, and
    // nothing downstream compares them: the two would simply read the same
    // bytes at different line offsets.  The per-phase check in
    // ExpectLevelMergeContexts compares the three contexts with each other,
    // which cannot catch this, because all three copy the same wrong view.
    Expect(binding.out.layout == layout_,
           "the destination view is in another entry layout than this job "
           "was built for");
    Expect(binding.out_tier != nullptr, "a merge publishes a tier");
    Expect(binding.out_tier->entry_bytes == layout_.EntryBytes(),
           "the destination tier is in another entry layout");
    // The occupancy the destination views came from.  The job cannot check it
    // -- it holds views, not the lease, and only the owner holds that -- so
    // what it does is RECORD it, and `destination_generation()` is how the
    // owner compares before it hands over a carry (threading rule 6).  A zero
    // is no occupancy at all, which is the one case checkable from here.
    Expect(binding.destination_generation >= 1,
           "the destination was not leased");
    if (!HasOlderHalf()) {
      Expect(binding.older_main.num_buckets == 0,
             "a digit-1 merge has no older half");
    } else {
      // The top compacts the whole of A -- T buckets, the output's own size --
      // where every other level absorbs its partial at digit j-1.
      Expect(binding.older_main.data != nullptr &&
                 binding.older_main.num_buckets ==
                     (top_ ? digit_ : digit_ - 1) * carry_buckets_,
             top_ ? "the top's older operand is not the whole of A"
                  : "the older operand is not (j-1)*U buckets");
      Expect(binding.older_main.layout == layout_,
             "the older operand is in another entry layout");
      if (initializing_) {
        // THE SOURCE IS THE OUTPUT.  Checked rather than assumed, because the
        // planner's in-place arrival writes tags over `out` and routes `out`:
        // pointed at any other buffer it would route the destination and
        // leave the records where they were.
        Expect(binding.older_main.data == binding.out.data &&
                   binding.older_main.num_buckets == binding.out.num_buckets,
               "a direct initialization routes the records where they were "
               "scattered, so its older operand IS its output");
        Expect(binding.older_tier == nullptr,
               "nothing precedes an initialized top, so it has no older tier");
      } else {
        Expect(binding.older_tier != nullptr,
               "the older operand's tier is part of it");
        Expect(binding.older_tier->entry_bytes == layout_.EntryBytes(),
               "the older operand's tier is in another entry layout");
        // ResetStorage empties the destination tier at binding, so the older
        // operand's cannot be it.
        Expect(binding.older_tier != binding.out_tier,
               "the older operand's tier is the destination's");
        // The merge writes its whole output, so an older operand inside it
        // would be overwritten while it is still being read -- unless it
        // sits exactly where the merge copies it, which is the in-place
        // binding.  A bank-first run puts two partials in one bank
        // (LevelArenaGeometry::BankOffset), and the placement that keeps them
        // apart is checked here as well as at construction.
        if (binding.in_place) {
          const size_t offset = top_ ? 0 : carry_buckets_;
          Expect(binding.older_main.data ==
                         binding.out.data + offset * layout_.BucketBytes() &&
                     binding.older_main.masks == binding.out.masks + offset,
                 "an in-place older operand is the output past its first U "
                 "buckets (all of it at the top)");
        } else {
          Expect(!ViewsOverlap(binding.older_main, binding.out,
                               layout_.BucketBytes()),
                 "the older operand overlaps the destination");
        }
      }
    }
  }

  // Whether two views share a payload byte or an occupancy word.  Pointers
  // into unrelated allocations, so compared as integers.
  static bool ViewsOverlap(const TableView& a, const TableView& b,
                           size_t bucket_bytes) {
    const auto overlaps = [](const void* p, size_t pn, const void* q,
                             size_t qn) {
      const uintptr_t p0 = reinterpret_cast<uintptr_t>(p);
      const uintptr_t q0 = reinterpret_cast<uintptr_t>(q);
      return p0 < q0 + qn && q0 < p0 + pn;
    };
    return overlaps(a.data, a.num_buckets * bucket_bytes, b.data,
                    b.num_buckets * bucket_bytes) ||
           overlaps(a.masks, a.num_buckets * sizeof(uint64_t), b.masks,
                    b.num_buckets * sizeof(uint64_t));
  }

  // ARRIVAL VALIDATES; it does not re-plan.  A carry that does not match what
  // this job was prepared under is rejected, because changing the nonce or the
  // geometry now would leave the already-routed older half under the old one
  // (threading rule 6).
  void ValidateArrival(const LevelCarry& carry) const {
    Expect(carry.ordinal == binding_.ordinal,
           "a carry arrived out of order at a prepared job");
    if (dense_) {
      Expect(carry.dense_prefix.data != nullptr &&
                 carry.dense_prefix.num_buckets ==
                     geometry_->DensePrefixBuckets() &&
                 carry.dense_prefix.layout == layout_,
             "level 1's carry is a complete dense prefix in this job's "
             "layout");
      Expect(carry.main.num_buckets == 0 && carry.tier == nullptr,
             "a dense carry is a prefix, not a published table");
      return;
    }
    // AT THE TOP THE FAMILY MATTERS MORE, not less: the sweep does not re-route
    // the carry either, and it recomputes each source bucket's block digit
    // from the key.  Under a foreign nonce that digit names a block the entry
    // was never placed for, and the entry is merged into the wrong one.
    Expect(carry.family == family_,
           "a carry and the merge that consumes it share a nonce family; "
           "re-tagging under any other places every entry wrong");
    Expect(carry.main.data != nullptr &&
               carry.main.num_buckets == carry_buckets_ &&
               carry.main.layout == layout_,
           "the carry is not U buckets in this job's layout");
    Expect(carry.tier != nullptr, "a published carry has a tier (5)");
    Expect(carry.tier->entry_bytes == layout_.EntryBytes(),
           "the carry's tier is in another entry layout");
  }

  // ---- contexts -----------------------------------------------------------
  //
  // THREE CONTEXTS (preparation, install, finish), agreeing on the output,
  // the nonce, the map and the tag depth, differing in what each reads and
  // WHERE IT SHEDS.  Separate shed storage is what keeps each residual pool
  // slot to one freshness rank: a slot holding both the older preparation's
  // sheds and the fresher install's could be ranked neither way without
  // losing a live record.  Preparation and finish share ONE array -- they
  // shed the same class, and the finish's pool is what gives the
  // preparation's sheds their second chance.  The check that the three
  // agree is ExpectLevelMergeContexts, run by every planner call.

  void BuildContexts() {
    map_ = RoutingIndexMap{};
    if (shape_.has_radix_pass()) {
      map_.kind = TagMapKind::kRadixDigit;
      map_.low_bits = shape_.block_bits;
      map_.modulus = shape_.odd_part;
      map_.digit_shift = RoutingDigitShift(layout_);
    }
    RebuildStepContext base;
    base.out = binding_.out;
    base.older = binding_.older_main;
    // Where the older source lands inside the output: after the carry below
    // the top, and at offset zero at the top, which copies A whole.
    base.upper_offset = top_ ? 0 : carry_buckets_;
    base.nonce_lo = nonce_.real_lo;
    base.nonce_hi = nonce_.real_hi;
    base.route_levels = shape_.block_bits;
    base.map = map_;
    // Every phase, and with it every re-tag, every dedup and the finish's
    // residual sweep, which reads the key off the same context
    // (ScatterAndRetagResidualPoolRange, kResidualRetag).  The three copies
    // below are what propagates it; ExpectLevelMergeContexts checks that they
    // still agree, so a later copy path that rebuilt one context cannot put
    // half a merge on another key.
    base.aes_keys = aes_keys_;
    base.level_stashes = older_sheds_.data();
    base.radix_stash = &older_sheds_[shape_.block_bits +
                                     kLevelMergeRadixStashOffset];
    base.merge_stash = &older_sheds_[shape_.block_bits +
                                     kLevelMergeMergeStashOffset];
    // Tombstones below the top still shadow older values.  At the top, FIFO
    // consumption retires every older family, so unshadowed tombstones can be
    // omitted from the output while remaining probeable in the input.
    base.drop_unshadowed = top_;
    // THE CARRY'S WAYS ARE RECOMPUTED AT THE TOP.  Its carry is an
    // inbox table its producer published under a kRaw map over log2(U_L)
    // bits, so nothing in it says which of the top's D blocks an entry belongs
    // to.  The sweep hashes each source bucket's keys under this same nonce,
    // map and key instead -- which is the whole of the top's per-bucket re-tag,
    // since the merge reads no other tag line of its source and moves only
    // payload lines out of it.  At every D > 1, radix pass or binary route
    // alike (ComputeBucketWayLine); at D = 1 there is one way and nothing to
    // recompute.
    base.retag_fresher_digits =
        (top_ || SeparatedSources(*geometry_, level_, digit_)) &&
        shape_.digit > 1;
    prepare_ = base;
    finish_ = base;  // one array with the preparation, by contract (above)
    install_ = base;
    if (dense_) {
      install_.small_log = TableView{layout_, dense_masks_.size(), nullptr,
                                     dense_masks_.data()};
    }
    if (dense_) {
      // B's main and its leftovers: the output itself at digit 1, the job's
      // own table and one-bucket tier above it, which the separated finish
      // then inserts and offers.  The build sheds nothing.
      install_.dense_homes = dense_homes_.get();
      install_.fresher = digit_ > 1 ? DenseBView() : binding_.out;
      install_.dense_tier = digit_ > 1 ? &dense_tier_ : binding_.out_tier;
      if (digit_ > 1) finish_.fresher = DenseBView();
    }
    finish_.tier_out = binding_.out_tier;
    spec_ = LevelMergeSpec{};
    spec_.shape = shape_;
    spec_.dense_direct = dense_ ? geometry_ : nullptr;
    spec_.top = top_;
    spec_.separated_sources = SeparatedSources(*geometry_, level_, digit_);
    contexts_.prepare = &prepare_;
    contexts_.install = &install_;
    contexts_.finish = &finish_;
  }

  void BindCarry(const LevelCarry& carry) {
    if (dense_) {
      install_.small_old = carry.dense_prefix;
      install_.small_log.data = carry.dense_prefix.data;
      std::copy_n(carry.dense_prefix.masks, dense_masks_.size(),
                  dense_masks_.data());
      return;
    }
    install_.fresher = carry.main;
    // The top's SWEEP is the thing that reads the carry, and the sweep is the
    // finish; below it the install is what reads it.  Both contexts get it,
    // so neither phase can be planned against a carry the other bound.
    if (top_ || spec_.separated_sources) finish_.fresher = carry.main;
    // The producer keeps this payload pinned through publication. Only the
    // private descriptor's masks participate in pool dedup and reset.
    BorrowTier(carry.tier, &tier_views_[kCarryTierView]);
  }

  // A descriptor copy owns the inline masks, never the source payload. It
  // may be used only as a pool source, not as a route shed or output drain.
  void BorrowTier(const ResidualStash* source, ResidualStash* into) {
    if (source->num_buckets > into->num_buckets) {
      throw std::logic_error(
          "level arena: an input tier is wider than the job's private view");
    }
    if (source->entry_bytes != into->entry_bytes) {
      throw std::logic_error(
          "level arena: an input tier has another entry width");
    }
    into->data = source->data;
    into->Reset();
    for (size_t b = 0; b < source->num_buckets; ++b) {
      into->masks[b] = source->masks[b];
    }
    into->num_buckets = source->num_buckets;
  }

  // ---- the residual passes ------------------------------------------------

  // The shape every pass here shares: where it offers back to, and the FLAT
  // DESTINATION map it tags its range table with.  The sweep pairs main bucket
  // b with residual bucket b >> index_bits, so a residual carries where it is
  // GOING -- on a power-of-two output that is the merge's own word, on a
  // mixed-radix one the merge's map packed at its block width.
  ResidualPassSpec& BasePassSpec(const LevelMergePoolShape& pool) {
    // Preserve the one source buffer across passes and jobs.
    auto sources = std::move(pass_spec_.sources);
    sources.clear();
    pass_spec_ = ResidualPassSpec{};
    pass_spec_.sources = std::move(sources);
    auto& spec = pass_spec_;
    spec.main = binding_.out;
    spec.main_levels = pool.main_levels;
    spec.scratch = 0;  // one range table at a time, per executing thread
    spec.lines = layout_.PayloadLines();  // post-routing: payload alone
    spec.map = map_;
    if (spec.map.kind == TagMapKind::kRadixDigit) {
      spec.map.digit_shift = spec.map.low_bits;
    }
    return spec;
  }

  // The pool just built and the shape MaxLevelMergeRangeBuckets sized the
  // thread's scratch from walk the same slot list, so what is left to check
  // is the one thing the list cannot say: that every stash bound to a swept
  // slot is as wide as the sizing assumed -- a shed `stash_buckets_`, a tier
  // view its role's width.  A disagreement would either overrun the scratch
  // or, worse, sweep a range table narrower than the pass planned.
  static void ExpectPoolMatchesShape(const ResidualPassSpec& spec,
                                     const LevelMergePoolShape& pool) {
    size_t swept = 0;
    for (size_t i = spec.drain_only_slots; i < spec.sources.size(); ++i) {
      swept += spec.sources[i].stash->num_buckets;
    }
    if (swept != pool.swept_buckets) {
      throw std::logic_error(
          "level arena: a pass's pool is not the shape its range scratch was "
          "sized from");
    }
  }

  ResidualStash* PoolStash(const PoolSlot& slot) {
    switch (slot.storage) {
      case PoolSlotStorage::kOlderShed:
        return &older_sheds_[slot.index];
      case PoolSlotStorage::kOlderTier:
        return &tier_views_[kOlderTierView];
      case PoolSlotStorage::kCarryTier:
        // A directly built B's tier is the job's own, owned like a shed.
        return dense_ ? &dense_tier_ : &tier_views_[kCarryTierView];
    }
    throw std::logic_error("level arena: unknown pool slot storage");
  }

  // Binds a slot list to this job's stashes.  Every slot is owned: the job
  // owns its sheds, and its tier views own private masks over pinned payload.
  template <typename Slots>
  void BindPool(ResidualPassSpec* spec, Slots&& slots) {
    bool swept = false;
    const PoolRecipe recipe = slots([&](const PoolSlot& slot) {
      if (slot.drain_only) {
        if (swept) {
          throw std::logic_error(
              "level arena: a drain-only pool slot follows a swept one");
        }
        ++spec->drain_only_slots;
      } else {
        swept = true;
      }
      if (slot.tier_class) {
        spec->AddOwnedTierClass(PoolStash(slot), slot.rank);
      } else {
        spec->AddOwned(PoolStash(slot), slot.rank);
      }
    });
    spec->fuse = recipe.fuse;
    spec->rule = recipe.rule;
    spec->shed_slots = recipe.shed_slots;
    spec->force_active = recipe.force_active;
  }

  void AttachPass(RebuildStepContext* ctx, unsigned pass,
                  std::vector<ResidualStash*>* pool,
                  std::vector<uint8_t>* rank, const ResidualPassSpec& spec,
                  LevelMergeScratch* scratch) {
    const size_t range_buckets =
        BuildResidualPassFields(ctx, pass, pool, rank, spec);
    if (range_buckets != 0) {
      AttachResidualRange(&ctx->residual[pass], scratch->Range(range_buckets));
    }
  }

  // The finish's one pass below the top (FinishPoolSlotsOf); the top's is its
  // merge pass.
  void BuildFinishPass(LevelMergeScratch* scratch) {
    if (top_) {
      BuildTopMergePass(scratch);
      return;
    }
    // A directly built digit 1 is complete: B is the output and its tier.
    if (!FinishRunsPass(*geometry_, level_, digit_)) return;
    const LevelMergePoolShape pool =
        FinishPoolShapeAt(*geometry_, stash_buckets_, level_, shape_);
    ResidualPassSpec& spec = BasePassSpec(pool);
    spec.drain = binding_.out_tier;
    FinishPassRange(pool).ApplyTo(&spec);
    BindPool(&spec, [&](auto&& visit) {
      return FinishPoolSlotsAt(*geometry_, level_, shape_, visit);
    });
    ExpectPoolMatchesShape(spec, pool);
    AttachPass(&finish_, kFinalPass, &pool_, &rank_, spec, scratch);
    AttachFinishDfs(scratch, spec, pool);
  }

  // A finish pass's DFS workspace, wherever its distributed pool routes: the
  // finish's one pass below the top and the top's merge pass alike.
  void AttachFinishDfs(LevelMergeScratch* scratch,
                       const ResidualPassSpec& spec,
                       const LevelMergePoolShape& pool) {
    if (!DfsResidualRangeApplies(pool.swept_buckets - pool.direct_buckets,
                                 pool.main_levels)) {
      return;
    }
    if (scratch->dfs() == nullptr) {
      throw std::logic_error(
          "level arena: a DFS finish was given scratch without a DFS "
          "workspace (MaxLevelDfsAllocation)");
    }
    AttachResidualDfs(&finish_.residual[kFinalPass], scratch->dfs(),
                      spec.dfs_pages);
  }

  // ---- the top's two passes ------------------------------------------------

  // The PREPARATION's (TopPreparePoolSlots).  What it cannot place drains into
  // `drain`: the RETAINED CARRY for an ordinary compaction, whose finish
  // resolves it against the incoming carry and which is the merge pass's older
  // class below, and the published TIER for a direct initialization, which
  // has no finish to resolve it in.  Everything else about the pass is the
  // same, which is what makes the initialization route the top's own
  // preparation rather than a second spelling of it.  Nothing else survives
  // this phase: its reset empties every route slot.
  void BuildTopPreparePass(LevelMergeScratch* scratch, ResidualStash* drain) {
    const LevelMergePoolShape pool = TopPreparePoolShapeOf(
        shape_, stash_buckets_, geometry_->OlderTierBuckets(level_, digit_));
    ResidualPassSpec& spec = BasePassSpec(pool);
    spec.drain = drain;
    TopPreparePassRange().ApplyTo(&spec);
    BindPool(&spec, [&](auto&& visit) {
      return TopPreparePoolSlots(shape_, visit);
    });
    ExpectPoolMatchesShape(spec, pool);
    AttachPass(&prepare_, kPreparePass, &prep_pool_, &prep_rank_, spec,
               scratch);
    if (DfsResidualRangeApplies(pool.swept_buckets, pool.main_levels)) {
      if (scratch->dfs() == nullptr)
        throw std::logic_error("DFS top preparation needs MaxLevelDfsAllocation scratch");
      AttachResidualDfs(&prepare_.residual[kPreparePass], scratch->dfs(),
                        spec.dfs_pages);
    }
  }

  // The MERGE's (TopMergePoolSlots), riding the sweep.  Its range table is
  // every finish's (FinishPassRange): a one-page DFS leaf of the retained
  // carry, A's class alone, with B's tier offered directly after it, as at a
  // separated ordinary digit (analysis/bound_certification/REPORT.tex,
  // proposition "separated-capacity").
  //
  // WHY THE DRAIN-ONLY PREFIX IS SAFE HERE, which is the thing this shape
  // turns on.  A fused pass builds its range table BEFORE the sweep, so the
  // sweep's own shed cannot be in it; it drains, and its only same-key
  // conflict -- with an A-class RANGE LEFTOVER -- is resolved afterwards by
  // ResidualLeftoverDedupRange.  That backstop reaches a leftover and nothing
  // else, so the shape is correct exactly when an A-class candidate whose B
  // copy shed is guaranteed to BE a leftover.
  //
  // It is, because of two facts that meet:
  //
  //   1. the sweep sheds into a bucket only when that bucket ENDS FULL
  //      (MergeBucketWithResidualOffers: a nonempty shed means alloc was
  //      capped by the free lanes, so the destination filled), and the offer
  //      for that bucket runs in the same visit, right after;
  //   2. the offer allocates its classes IN ORDER, A's first, out of the
  //      lanes that were free before B's tier cleared anything
  //      (PlanResidualOfferMerge).  A full bucket therefore absorbs no
  //      A-class candidate at all.
  //
  // Fact 2 is what the shape rests on, and it is the whole of it: without it
  // a tier-class candidate that resolves a duplicate clears a main lane, and
  // the freed
  // lane goes to the lowest-indexed candidate of the range bucket -- which
  // may be a different, A-class one.  Absorbed, it is past the leftover
  // dedup, and the key is published twice: the staler copy in C's main, the
  // fresher in its tier.  Four of cpu_byteslice_level_arena_top_test's cases
  // reach exactly that, and `DedupBucketDestinations` cannot help -- it
  // clears C's copies of B's keys, and here neither copy was in C.
  //
  // SINCE THE TOP RESOLVES FIRST (ResolveTopDestination) both
  // facts still hold but neither is needed at the top: before a bucket's
  // merge, every A-class candidate whose key B holds is gone and C's copies
  // of B's tier keys are cleared, so no candidate resolves a duplicate, no
  // lane is freed by the offer, and no A-class leftover shares a key with a
  // shed.  The leftover dedup the epilogue plans between the two drains
  // therefore removes nothing here.  It is KEPT, deliberately: it is the one
  // epilogue every fused final pass plans (the absorbs need it), it costs a
  // couple of intersects per item, and a removal it made would only shrink
  // an append prefix the excess already bounds.
  void BuildTopMergePass(LevelMergeScratch* scratch) {
    const LevelMergePoolShape pool = TopMergePoolShapeOf(
        shape_, stash_buckets_, geometry_->CarryTierBuckets(level_));
    ResidualPassSpec& spec = BasePassSpec(pool);
    spec.drain = binding_.out_tier;
    FinishPassRange(pool).ApplyTo(&spec);
    BindPool(&spec, [&](auto&& visit) {
      return TopMergePoolSlots(shape_, visit);
    });
    ExpectPoolMatchesShape(spec, pool);
    AttachPass(&finish_, kFinalPass, &pool_, &rank_, spec, scratch);
    AttachFinishDfs(scratch, spec, pool);
  }

  // The top's retained preparation carry.  A DRAIN, not a shed, which is why
  // it sits past the merge's slot: the route's slots are reset when the
  // preparation's pass ends and this one has to survive that.
  ResidualStash* PrepCarry() {
    return &older_sheds_[shape_.block_bits +
                         kLevelMergePrepCarryStashOffset];
  }

  // ---- execution ----------------------------------------------------------

  // The task list's sink: it refuses to grow past the capacity reserved at
  // construction (LevelPhasePlanCapacity), because a job allocates nothing
  // after it is built and a list that reallocated would be a bill nobody paid.
  //
  // It also KEEPS STAGES (StageMark): a stage begins at the next task, and a
  // mark that follows another with no task between replaces it, so no stage
  // is empty.  Tasks before the first mark are an ordered stage.
  struct BoundedPlanSink {
    std::vector<Subtask>* tasks;
    std::vector<PlannedStage>* stages;
    std::vector<size_t>* unit_starts;
    void push_back(const Subtask& task) {
      if (tasks->size() == tasks->capacity()) {
        throw std::logic_error(
            "level arena: a phase planned more tasks than its job reserved "
            "(LevelPhasePlanCapacity)");
      }
      if (stages->empty()) BeginStage(OrderedStage());
      tasks->push_back(task);
    }
    void BeginStage(const StageMark& mark) {
      if (!stages->empty() && stages->back().first_task == tasks->size()) {
#ifdef MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER
        // A mark that replaces an empty one keeps its observer requests.
        StageMark merged = mark;
        const StageMark& old = stages->back().mark;
        merged.observe_swept |= old.observe_swept;
        merged.observe_drain |= old.observe_drain;
        merged.observe_range |= old.observe_range;
        stages->back().mark = merged;
#else
        stages->back().mark = mark;
#endif
        return;
      }
      Reserve(*stages, "stages");
      stages->push_back(PlannedStage{tasks->size(), unit_starts->size(), mark});
    }
    void BeginLaneUnit() {
      if (stages->empty()) BeginStage(OrderedStage());
      Reserve(*unit_starts, "lane units");
      unit_starts->push_back(tasks->size());
    }
    template <class Vector>
    static void Reserve(const Vector& v, const char* what) {
      if (v.size() == v.capacity()) {
        throw std::logic_error(
            std::string("level arena: a phase planned more ") + what +
            " than its job reserved");
      }
    }
  };

  // The stage rules the cursor divides by, checked once per phase: a
  // by-range stage is one task, and a by-task stage's first unit begins at
  // its first task.  A planner that broke either would give lanes the wrong
  // bounds, which is two lanes on one bucket.
  void ExpectStages() const {
    for (size_t s = 0; s < stages_.size(); ++s) {
      const PlannedStage& st = stages_[s];
      const size_t end = s + 1 < stages_.size() ? stages_[s + 1].first_task
                                                : plan_.size();
      const size_t units_end = s + 1 < stages_.size()
                                   ? stages_[s + 1].first_unit
                                   : unit_starts_.size();
      if (!st.mark.lanes) continue;
      if (st.mark.by_range) {
        if (end - st.first_task != 1) {
          throw std::logic_error(
              "level arena: a stage divided by range holds other than one "
              "task");
        }
      } else if (units_end > st.first_unit &&
                 unit_starts_[st.first_unit] != st.first_task) {
        throw std::logic_error(
            "level arena: a stage's first lane unit is not its first task");
      }
    }
  }

  // Plans `phase` at the whole budget into the job's task list and puts the
  // cursor at its start.  Planning reads public shapes only, so planning the
  // whole phase before running any of it is the same algorithm as running
  // each task as it is emitted.
  void StartPhase(LevelMergePhase phase, LevelMergeScratch* scratch) {
    plan_.clear();
    stages_.clear();
    unit_starts_.clear();
    BoundedPlanSink sink{&plan_, &stages_, &unit_starts_};
    PlanLevelMergePhase(phase, contexts_, spec_, WholeLevelMergeBudget(),
                        &sink);
    ExpectStages();
    // Each lane's context is the phase's own with the shed stashes swapped
    // for the lane's; everything else -- the output, the sources, the range
    // tables its offers read -- is shared, which lanes may do because they
    // touch disjoint parts of it.  (An offer stage's range occupancy words
    // are the exception, swapped for private copies as each lane opens:
    // OpenLane.)
    if (lanes_ > 1) {
      const RebuildStepContext& ctx = contexts_.At(phase);
      for (size_t lane = 0; lane < lanes_; ++lane) {
        RebuildStepContext& lc = lane_ctx_[lane];
        lc = ctx;
        ResidualStash* base = LaneSheds(lane);
        lc.level_stashes = ctx.level_stashes == older_sheds_.data()
                               ? base
                               : nullptr;
        lc.radix_stash = LaneSlot(lane, ctx.radix_stash);
        lc.merge_stash = LaneSlot(lane, ctx.merge_stash);
      }
    }
    cursor_.Reset();
    ResetObservedStage();
    running_phase_ = phase;
    phase_scratch_ = scratch;
    phase_running_ = true;
    if (timing_) phase_started_ = std::chrono::steady_clock::now();
    // LAST: from here helpers may run the phase's lanes, and they read
    // everything above -- the plan, the contexts, `running_phase_` -- through
    // the claim word this publishes.
    if (shared()) OpenSharedStage(0, /*by_owner=*/true);
  }

  template <class Yield>
  bool ContinuePhase(LevelMergePhase phase, const SubtaskBudget& budget,
                     LevelMergeScratch* scratch, Yield&& yield) {
    if (!phase_running_ || running_phase_ != phase) {
      throw std::logic_error(
          std::string("level arena: resuming the ") +
          LevelMergePhaseName(phase) + " phase, which is not the one running");
    }
    // A paused pass keeps its range table attached (AttachPass), so another
    // scratch would sweep a table nobody built.  A phase without a pass
    // attached none, and may be resumed without one.
    if (scratch != phase_scratch_ && phase_scratch_ != nullptr) {
      throw std::logic_error(
          "level arena: a phase was resumed with another range scratch than "
          "the one its pass was attached to");
    }
    waiting_on_helpers_ = false;
    if (shared()) {
      if (!ContinueShared(yield)) return false;
      phase_running_ = false;
      phase_scratch_ = nullptr;
      NotePhaseEnded(phase);
      return true;
    }
    const RebuildStepContext& ctx = contexts_.At(phase);
    // Overflow is a CHECKED failure, never a retry and never a partial
    // publication: a stash that ran out has lost live records, and the only
    // honest response is to say so.  WHICH kind ran out is part of
    // saying so -- a routing level, a radix pass, the fixed merge and the
    // residual route all report "a stash overflowed" and have nothing in
    // common to do about it.
    PhasePlanView view;
    view.tasks = plan_.data();
    view.num_tasks = plan_.size();
    view.stages = stages_.data();
    view.num_stages = stages_.size();
    view.unit_starts = unit_starts_.data();
    view.num_units = unit_starts_.size();
    const bool done = cursor_.Resume(
        view, lanes_, budget,
        [&](const PlannedStage& stage, size_t, size_t lane) {
          OpenLane(stage.mark, lane);
        },
        [&](const Subtask& piece, size_t lane) {
          ObserveStageBegin(cursor_.stage());
          const RebuildStepContext& at =
              lane == PhaseCursor::kNoLane ? ctx : lane_ctx_[lane];
          const PieceClock clock(this, piece, cursor_.stage());
          if (!RunSubtask</*CheckOverflow=*/true>(at, piece)) {
            throw std::runtime_error(
                std::string("level arena: the ") + LevelMergePhaseName(phase) +
                " phase ran out of room at " + SubtaskKindName(piece.kind) +
                "; the certified depth did not hold");
          }
        },
        [&](const PlannedStage& stage, size_t lanes) {
          FoldLanes(ctx, stage.mark, lanes, phase);
        },
        yield);
    if (done) {
      phase_running_ = false;
      phase_scratch_ = nullptr;
      NotePhaseEnded(phase);
    }
    return done;
  }

  void NotePrepared() {
    if (timing_) {
      prepare_end_ns_ = static_cast<uint64_t>(
          std::chrono::duration_cast<std::chrono::nanoseconds>(
              std::chrono::steady_clock::now().time_since_epoch())
              .count());
    }
  }

  // The owner's alone -- only the owner ends a phase -- so each counter has
  // one writer, and a load and a store update it without a locked add.
  void NotePhaseEnded(LevelMergePhase phase) {
    if (!timing_) return;
    const size_t p = static_cast<size_t>(phase);
    const uint64_t nanos = static_cast<uint64_t>(
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            std::chrono::steady_clock::now() - phase_started_)
            .count());
    phase_wall_[p].store(phase_wall_[p].load(std::memory_order_relaxed) + nanos,
                         std::memory_order_relaxed);
    phases_ended_[p].store(phases_ended_[p].load(std::memory_order_relaxed) + 1,
                           std::memory_order_relaxed);
  }

  // ---- occupancy observer (cpu_byteslice_level_arena_occupancy.hpp) -------
  //
  // Empty without MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER.  With it, a stage
  // the planners marked (StageMark::observe_*) reports at its FIRST piece --
  // once per stage, whichever thread runs it, and not again when a paused
  // stage resumes -- the swept slots, the drain-only slots and the freshly
  // built range table of the named passes, and the output tier is reported
  // when the job's last phase ends.  Marked stages are ordered (one lane), so
  // nothing else touches the structures while they are read.
#ifdef MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER
  void NoteOccupancyJob() { ++occupancy_job_; }
  void ResetObservedStage() {
    observed_stage_.store(~size_t{0}, std::memory_order_relaxed);
  }

  void ObserveStageBegin(size_t stage) {
    const StageMark& mark = stages_[stage].mark;
    if ((mark.observe_swept | mark.observe_drain | mark.observe_range) == 0) {
      return;
    }
    if (observed_stage_.exchange(stage, std::memory_order_relaxed) == stage) {
      return;
    }
    const RebuildStepContext& ctx = contexts_.At(running_phase_);
    for (unsigned pass = 0; pass < kResidualPasses; ++pass) {
      const ResidualPass& rp = ctx.residual[pass];
      if (!rp.active) continue;
      const unsigned bit = 1u << pass;
      if ((mark.observe_swept & bit) != 0) {
        for (size_t i = rp.drain_only; i < rp.pool_slots; ++i) {
          ObservePoolStash(*rp.pool[i]);
        }
      }
      if ((mark.observe_drain & bit) != 0) {
        for (size_t i = 0; i < rp.drain_only; ++i) {
          ObservePoolStash(*rp.pool[i]);
        }
      }
      if ((mark.observe_range & bit) != 0) ObserveRangeLeaves(rp, pass);
    }
  }

  void Emit(OccupancyKind kind, unsigned index, size_t occupancy,
            size_t capacity) {
    OccupancyEvent event;
    event.kind = kind;
    event.level = level_;
    event.index = index;
    event.job = occupancy_job_;
    event.occupancy = occupancy;
    event.capacity = capacity;
    ObserveOccupancy(event);
  }

  // The job's own stashes by identity; a borrowed tier view is not one (the
  // tier was observed as a final tier when its producer published it).
  void ObservePoolStash(const ResidualStash& stash) {
    const ResidualStash* first = older_sheds_.data();
    if (&stash >= first && &stash < first + older_sheds_.size()) {
      const size_t i = static_cast<size_t>(&stash - first);
      const size_t block = shape_.block_bits;
      OccupancyKind kind = OccupancyKind::kStageStash;
      unsigned index = static_cast<unsigned>(i);
      if (i >= block) {
        const size_t off = i - block;
        if (off == kLevelMergeRadixStashOffset) {
          kind = OccupancyKind::kRadixStash;
        } else if (off == kLevelMergeMergeStashOffset) {
          kind = OccupancyKind::kMergeStash;
        } else if (off == kLevelMergePrepCarryStashOffset) {
          kind = OccupancyKind::kRetainedCarry;
        } else {
          throw std::logic_error(
              "level arena: the occupancy observer met an unnamed stash");
        }
        index = 0;
      }
      Emit(kind, index, stash.Count(), stash.Capacity());
      return;
    }
  }

  // A DFS pass's range table: leaf l is the stacked pages
  // g * 2^range_bits + l, and "some leaf holds more than 64 * pages
  // candidates" is the one event that covers the whole distributor.  Padding
  // leaves (homes past the main table) are public zeros and are skipped.  A
  // direct or empty plan has no range event.
  void ObserveRangeLeaves(const ResidualPass& rp, unsigned pass) {
    if (rp.dfs == nullptr || !rp.sweep_active) return;
    const size_t leaves = size_t{1} << rp.plan.range_bits;
    const size_t groups = rp.plan.groups;
    for (size_t leaf = 0; leaf < leaves; ++leaf) {
      if ((leaf << rp.plan.index_bits) >= rp.main.num_buckets) continue;
      size_t count = 0;
      for (size_t g = 0; g < groups; ++g) {
        count += Popcount64(rp.range.masks[(g << rp.plan.range_bits) + leaf]);
      }
      Emit(OccupancyKind::kRangeLeaf, pass, count, groups * kBucketCapacity);
    }
  }

  void ObserveFinalTier() {
    if (binding_.out_tier == nullptr) return;
    Emit(OccupancyKind::kFinalTier, 0, binding_.out_tier->Count(),
         binding_.out_tier->Capacity());
  }
#else
  void NoteOccupancyJob() {}
  void ResetObservedStage() {}
  void ObserveStageBegin(size_t) {}
  void ObserveFinalTier() {}
#endif

  // ---- lanes ---------------------------------------------------------------

  // At most 64: a paused lane is one bit of `paused_lanes_`.
  static size_t JobLanes(size_t lanes) {
    if (lanes > 64) {
      throw std::invalid_argument("level arena: at most 64 lanes");
    }
    return lanes == 0 ? 1 : lanes;
  }

  // Lane `lane`'s stash array, laid out slot for slot like `older_sheds_`.
  ResidualStash* LaneSheds(size_t lane) {
    return lane_sheds_.data() + lane * older_sheds_.size();
  }
  // The lane's counterpart of one of the job's own stash slots, or null.
  ResidualStash* LaneSlot(size_t lane, const ResidualStash* own) {
    if (own == nullptr) return nullptr;
    const ResidualStash* first = older_sheds_.data();
    if (own < first || own >= first + older_sheds_.size()) return nullptr;
    return LaneSheds(lane) + (own - first);
  }

  // Lane `lane`'s private range masks: `lane_mask_stride_` words.
  uint64_t* LaneMasks(size_t lane) {
    return reinterpret_cast<uint64_t*>(lane_masks_.get()) +
           lane * lane_mask_stride_;
  }

  // A LANE OPENS on its own copy of the range words its stage's offers clear
  // (StageMark::offer_passes): the phase's current words, into the lane's
  // private masks, and the lane's context pointed at them.  Nothing writes
  // the phase's words while the stage runs -- every lane clears its copy --
  // so each lane copies whenever it opens, on whichever thread holds it.
  // The payload is not copied: offers only read it.
  void OpenLane(const StageMark& mark, size_t lane) {
    if (mark.offer_passes == 0) return;
    const RebuildStepContext& ctx = contexts_.At(running_phase_);
    RebuildStepContext& lc = lane_ctx_[lane];
    uint64_t* words = LaneMasks(lane);
    size_t used = 0;
    for (unsigned pass = 0; pass < kResidualPasses; ++pass) {
      if (((mark.offer_passes >> pass) & 1u) == 0) continue;
      const TableView& range = ctx.residual[pass].range;
      if (range.num_buckets > lane_mask_stride_ - used) {
        throw std::logic_error(
            "level arena: an offer stage's range tables are wider than its "
            "lanes' private masks");
      }
      std::memcpy(words + used, range.masks,
                  range.num_buckets * sizeof(uint64_t));
      lc.residual[pass].range.masks = words + used;
      used += range.num_buckets;
    }
  }

  // ...and the stage ends with their AND in the phase's words.  Offers only
  // clear bits, and each bit is a candidate of one main bucket, which one
  // lane owns, so the AND is every lane's clears together -- the one-lane
  // result.  The lanes' contexts go back to the phase's words.  Every word of
  // every lane is read, so the work is public.
  void FoldLaneRangeMasks(const RebuildStepContext& ctx, const StageMark& mark,
                          size_t lanes) {
    if (mark.offer_passes == 0) return;
    size_t used = 0;
    for (unsigned pass = 0; pass < kResidualPasses; ++pass) {
      if (((mark.offer_passes >> pass) & 1u) == 0) continue;
      const TableView& range = ctx.residual[pass].range;
      for (size_t lane = 0; lane < lanes; ++lane) {
        const uint64_t* words = LaneMasks(lane) + used;
        for (size_t r = 0; r < range.num_buckets; ++r) {
          range.masks[r] &= words[r];
        }
        lane_ctx_[lane].residual[pass].range.masks = range.masks;
      }
      used += range.num_buckets;
    }
    // One folder per stage (the done-lane count orders them), so a load and
    // a store suffice.
    private_mask_stages_.store(
        private_mask_stages_.load(std::memory_order_relaxed) + 1,
        std::memory_order_relaxed);
  }

  // THE FOLD: at the end of a stage its lanes ran, every lane stash the stage
  // could shed into is merged into the phase's own, lane after lane and
  // bucket after bucket, with the CHECKED merge -- which is the capacity
  // check of the whole stage, since each lane ran against a private stash of
  // the full certified depth and nothing else has bounded their sum.  Every
  // bucket is merged whether it holds anything or not, so the work is public.
  //
  // Stash insertion fills the lowest free slots and nothing leaves a stash
  // during a routing stage, so the one-lane stash is its sheds in the order
  // they happened -- and lanes are contiguous runs of that order, so this
  // fold rebuilds it exactly.
  void FoldLanes(const RebuildStepContext& ctx, const StageMark& mark,
                 size_t lanes, LevelMergePhase phase) {
    const FoldClock clock(this);
    const size_t lines = layout_.EntryBytes();
    const auto fold_slot = [&](ResidualStash* own, auto lane_slot) {
      if (own == nullptr) {
        throw std::logic_error(
            "level arena: a stage sheds into a stash its phase does not have");
      }
      for (size_t lane = 0; lane < lanes; ++lane) {
        if (!FoldLaneStash(*own, *lane_slot(lane), lines)) {
          throw std::runtime_error(
              std::string("level arena: the ") + LevelMergePhaseName(phase) +
              " phase's lanes overflowed at their fold; the certified depth "
              "did not hold");
        }
      }
    };
    laned_stages_.store(laned_stages_.load(std::memory_order_relaxed) + 1,
                        std::memory_order_relaxed);
    FoldLaneRangeMasks(ctx, mark, lanes);
    for (unsigned s = mark.shed_lo; s < mark.shed_hi; ++s) {
      fold_slot(ctx.level_stashes == nullptr ? nullptr : &ctx.level_stashes[s],
                [&](size_t lane) { return LaneSheds(lane) + s; });
    }
    if (mark.radix_shed) {
      fold_slot(ctx.radix_stash,
                [&](size_t lane) { return LaneSlot(lane, ctx.radix_stash); });
    }
    if (mark.merge_shed) {
      fold_slot(ctx.merge_stash,
                [&](size_t lane) { return LaneSlot(lane, ctx.merge_stash); });
    }
  }

  // ---- the shared executor -------------------------------------------------
  //
  // THE CLAIM WORD packs the running stage's sequence number, its lane count
  // and the next never-claimed lane, so that one compare-and-swap both claims
  // a lane and proves the stage is still the one the claimer read: a stage
  // cannot end while any of its lanes is unfinished, so a claim that
  // succeeded holds a lane of the stage the word names.  A lane stopped
  // between two pieces goes into `paused_lanes_`, from which ANY thread may
  // take it and resume it where it stopped -- its position is in
  // `lane_cursors_`, not on the stack of the thread that stopped it.
  //
  // ORDER: a thread writes its lane's output and stashes, fences its
  // streaming stores, and then counts the lane done with an acq_rel
  // increment; the increment that completes the stage therefore sees every
  // lane's writes, folds them, and publishes the next stage with a release
  // store of the claim word that every later claimer acquires.

  static constexpr uint64_t kClaimNextBits = 32;
  static constexpr uint64_t kClaimLanesBits = 8;
  static uint64_t PackClaim(uint64_t seq, uint64_t lanes, uint64_t next) {
    return (seq << (kClaimNextBits + kClaimLanesBits)) |
           (lanes << kClaimNextBits) | next;
  }
  static uint64_t ClaimLanes(uint64_t word) {
    return (word >> kClaimNextBits) & ((uint64_t{1} << kClaimLanesBits) - 1);
  }
  static uint64_t ClaimNext(uint64_t word) {
    return word & ((uint64_t{1} << kClaimNextBits) - 1);
  }

  PhasePlanView View() const {
    PhasePlanView view;
    view.tasks = plan_.data();
    view.num_tasks = plan_.size();
    view.stages = stages_.data();
    view.num_stages = stages_.size();
    view.unit_starts = unit_starts_.data();
    view.num_units = unit_starts_.size();
    return view;
  }

  // Makes stage `s` claimable, or ends the phase if there is none.  Called by
  // the owner at a phase's start and by whichever thread finished the last
  // lane of stage s - 1, never by two threads at once.
  //
  // WHO OPENED IT decides who is told.  The helpers always are.  The owner is
  // told when a HELPER opened it: the owner may be parked on kHelpersBusy --
  // every lane of the stage before was held -- and a new stage with lanes it
  // could run, or the end of the phase, is exactly what it is waiting for
  // (LevelBlock::kHelpersBusy).  The signal follows the stores that
  // make the stage claimable, which is the event's rule.  An owner that opened
  // it itself is running and claims a lane or sees the phase end at once; a
  // signal to its own event would only stop the phase it is in at the next
  // piece (PhaseYield).
  void OpenSharedStage(size_t s, bool by_owner) {
    OwnerEvent* const owner = by_owner ? nullptr : owner_event_;
    const PhasePlanView view = View();
    if (s >= view.num_stages) {
      shared_open_.store(false, std::memory_order_relaxed);
      phase_done_.store(true, std::memory_order_release);
      if (owner != nullptr) owner->Signal();
      return;
    }
    const size_t lanes = StageLanes(view, s, lanes_);
    shared_stage_.store(s, std::memory_order_relaxed);
    done_lanes_.store(0, std::memory_order_relaxed);
    paused_lanes_.store(0, std::memory_order_relaxed);
    if (s == 0) phase_done_.store(false, std::memory_order_relaxed);
    claim_.store(PackClaim(++claim_seq_, lanes, 0), std::memory_order_release);
    if (s == 0) shared_open_.store(true, std::memory_order_release);
    if (helper_event_ != nullptr) helper_event_->Signal();
    if (owner != nullptr) owner->Signal();
  }

  // Takes a lane of the running stage: a paused one first, since it was
  // started earlier, else the next never-claimed one.  False when every lane
  // is held or done.
  bool ClaimLane(size_t* lane, size_t* stage, size_t* lanes) {
    uint64_t paused = paused_lanes_.load(std::memory_order_acquire);
    while (paused != 0) {
      const size_t l = static_cast<size_t>(_tzcnt_u64(paused));
      if (paused_lanes_.compare_exchange_weak(
              paused, paused & ~(uint64_t{1} << l),
              std::memory_order_acq_rel, std::memory_order_acquire)) {
        const uint64_t word = claim_.load(std::memory_order_acquire);
        *lane = l;
        *lanes = static_cast<size_t>(ClaimLanes(word));
        *stage = shared_stage_.load(std::memory_order_relaxed);
        return true;
      }
    }
    uint64_t word = claim_.load(std::memory_order_acquire);
    while (ClaimNext(word) < ClaimLanes(word)) {
      if (claim_.compare_exchange_weak(word, word + 1,
                                       std::memory_order_acq_rel,
                                       std::memory_order_acquire)) {
        *lane = static_cast<size_t>(ClaimNext(word));
        *lanes = static_cast<size_t>(ClaimLanes(word));
        *stage = shared_stage_.load(std::memory_order_relaxed);
        lane_cursors_[*lane].Open(View(), *stage, *lanes, *lane);
        if (*lanes > 1) OpenLane(stages_[*stage].mark, *lane);
        return true;
      }
    }
    return false;
  }

  // Runs a claimed lane until it ends or `yield` stops it.  A stopped lane is
  // put back, claimable by anyone.  A lane that ends is counted, and the
  // count that completes the stage folds it and opens the next.  Returns
  // whether the lane ended.  `by_owner` is whether the owner runs it
  // (OpenSharedStage says why that matters).
  template <class Yield>
  bool RunClaimedLane(size_t lane, size_t stage, size_t lanes, bool by_owner,
                      Yield&& yield) {
    const PhasePlanView view = View();
    const RebuildStepContext& ctx = contexts_.At(running_phase_);
    const size_t tag = lanes > 1 ? lane : PhaseCursor::kNoLane;
    bool stop = false;
    const bool ended = lane_cursors_[lane].Resume(
        view, shared_budget_,
        [&](const Subtask& piece) {
          ObserveStageBegin(stage);
          const RebuildStepContext& at =
              tag == PhaseCursor::kNoLane ? ctx : lane_ctx_[tag];
          const PieceClock clock(this, piece, stage);
          if (!RunSubtask</*CheckOverflow=*/true>(at, piece)) {
            throw std::runtime_error(
                std::string("level arena: the ") +
                LevelMergePhaseName(running_phase_) +
                " phase ran out of room at " + SubtaskKindName(piece.kind) +
                "; the certified depth did not hold");
          }
        },
        yield, &stop);
    // Streaming stores are weakly ordered: fence them before the release
    // that hands the lane, or the stage, to another thread.
    _mm_sfence();
    if (!ended) {
      paused_lanes_.fetch_or(uint64_t{1} << lane, std::memory_order_release);
      if (helper_event_ != nullptr) helper_event_->Signal();
      return false;
    }
    if (done_lanes_.fetch_add(1, std::memory_order_acq_rel) + 1 == lanes) {
      if (lanes > 1) {
        FoldLanes(ctx, view.stages[stage].mark, lanes, running_phase_);
      }
      OpenSharedStage(stage + 1, by_owner);
    }
    return true;
  }

  // The owner's share of a shared phase: claim and run lanes until the phase
  // is done (true), `yield` stops one (false), or every lane left is held by
  // a helper (false, with waiting_on_helpers()).
  template <class Yield>
  bool ContinueShared(Yield&& yield) {
    for (;;) {
      if (phase_done_.load(std::memory_order_acquire)) return true;
      size_t lane = 0, stage = 0, lanes = 0;
      if (!ClaimLane(&lane, &stage, &lanes)) {
        if (phase_done_.load(std::memory_order_acquire)) return true;
        waiting_on_helpers_ = true;
        return false;
      }
      bool stopped = false;
      const auto stop_on_yield = [&](const Subtask& piece) {
        if (yield(piece)) stopped = true;
        return stopped;
      };
      const bool ended =
          RunClaimedLane(lane, stage, lanes, /*by_owner=*/true, stop_on_yield);
      if (!ended) return false;
      if (stopped && !phase_done_.load(std::memory_order_acquire)) {
        return false;
      }
    }
  }

  // One piece's wall time, charged when it goes out of scope (a throwing
  // piece's time is still its own).  Nothing at all unless timing is on.
  class PieceClock {
   public:
    PieceClock(LevelMergeJob* job, const Subtask& piece, size_t stage)
        : job_(job->timing_ ? job : nullptr) {
      if (job_ == nullptr) return;
      kind_ = static_cast<size_t>(piece.kind);
      divisible_ = job->stages_[stage].mark.lanes;
      phase_ = static_cast<size_t>(job->running_phase_);
      class_ = CostClassOf(piece.kind);
      job->cost_touches_[phase_][class_].fetch_add(PieceTouches(piece),
                                                   std::memory_order_relaxed);
      start_ = std::chrono::steady_clock::now();
    }
    ~PieceClock() {
      if (job_ == nullptr) return;
      const uint64_t nanos = static_cast<uint64_t>(
          std::chrono::duration_cast<std::chrono::nanoseconds>(
              std::chrono::steady_clock::now() - start_)
              .count());
      job_->kind_nanos_[kind_].fetch_add(nanos, std::memory_order_relaxed);
      job_->class_nanos_[divisible_ ? 1 : 0].fetch_add(
          nanos, std::memory_order_relaxed);
      job_->cost_nanos_[phase_][class_].fetch_add(nanos,
                                                  std::memory_order_relaxed);
    }
    PieceClock(const PieceClock&) = delete;
    PieceClock& operator=(const PieceClock&) = delete;

   private:
    LevelMergeJob* job_;
    size_t kind_ = 0;
    bool divisible_ = false;
    size_t phase_ = 0;
    size_t class_ = 0;
    std::chrono::steady_clock::time_point start_;
  };

  // A piece's class in LevelMergeCost: the fixed merge's sweep, the residual
  // pass, or the routing (copies, re-tags, butterflies, radix passes, the
  // dense builder) that is everything else.
  static size_t CostClassOf(Subtask::Kind kind) {
    switch (kind) {
      case Subtask::kFixedMergeRange:
      case Subtask::kFixedMergeOffers:
        return LevelMergeCost::kSweep;
      case Subtask::kResidualPoolDedup:
      case Subtask::kResidualScatter:
      case Subtask::kResidualScatterRetag:
      case Subtask::kResidualRetag:
      case Subtask::kResidualDfsGather:
      case Subtask::kResidualDfsPartition:
      case Subtask::kResidualSweep:
      case Subtask::kResidualLeftoverDedup:
      case Subtask::kResidualDrain:
      case Subtask::kResidualReset:
        return LevelMergeCost::kResidual;
      default:
        return LevelMergeCost::kRoute;
    }
  }

  // The same for a fold, which is ordered work outside every piece.
  class FoldClock {
   public:
    explicit FoldClock(LevelMergeJob* job) : job_(job->timing_ ? job : nullptr) {
      if (job_ != nullptr) start_ = std::chrono::steady_clock::now();
    }
    ~FoldClock() {
      if (job_ == nullptr) return;
      const uint64_t nanos = static_cast<uint64_t>(
          std::chrono::duration_cast<std::chrono::nanoseconds>(
              std::chrono::steady_clock::now() - start_)
              .count());
      job_->fold_nanos_.fetch_add(nanos, std::memory_order_relaxed);
      job_->class_nanos_[0].fetch_add(nanos, std::memory_order_relaxed);
      job_->cost_nanos_[static_cast<size_t>(job_->running_phase_)]
                       [LevelMergeCost::kFold]
                           .fetch_add(nanos, std::memory_order_relaxed);
    }
    FoldClock(const FoldClock&) = delete;
    FoldClock& operator=(const FoldClock&) = delete;

   private:
    LevelMergeJob* job_;
    std::chrono::steady_clock::time_point start_;
  };

  // A whole-phase call runs under NeverYield, so it cannot stop early.
  static void RunWhole(bool done) {
    if (!done) {
      throw std::logic_error(
          "level arena: a whole-phase call stopped before its phase ended");
    }
  }

  // The finish's one pass is the item's FINAL pass, as it is in the absorb.
  static constexpr unsigned kFinalPass = 2;
  // And the top's preparation is pass 0, which is not a convention:
  // PlanPrepareOlderHalf's fused last butterfly level names pass 0 in the
  // subtask it emits (kButterflyLevelOffers), so the pass has to be there.
  static constexpr unsigned kPreparePass = 0;
  static constexpr size_t kOlderTierView = 0;
  static constexpr size_t kCarryTierView = 1;

  bool HasOlderHalf() const { return MergeHasOlderHalf(top_, digit_); }

  const LevelArenaGeometry* geometry_;
  Layout layout_;
  unsigned level_;
  bool top_;
  bool dense_;
  size_t stash_buckets_;
  size_t merge_buckets_;  // MergeStashBuckets: the merge slot's depth
  const AesTagKeys* aes_keys_;  // the instance's, borrowed
  size_t carry_buckets_ = 0;
  unsigned max_block_bits_ = 0;

  // Fixed at construction, never resized: the contexts point into them.
  LevelArenaByteBill bytes_;
  Aligned64Ptr older_storage_;
  std::vector<ResidualStash> older_sheds_;
  std::array<ResidualStash, 2> tier_views_{};
  std::vector<uint64_t> dense_masks_;
  // A directly built level one (AllocateDenseDirect): B's main above digit
  // 1, its one-bucket tier and the home cache.
  Aligned64Ptr dense_b_data_, dense_tier_storage_, dense_homes_;
  std::vector<uint64_t> dense_b_masks_;
  ResidualStash dense_tier_;

  bool bound_ = false;
  bool prepared_ = false;
  bool installed_ = false;
  // Set only for the duration of RouteInitialTop, which is the one binding
  // whose older operand is its own output and whose older tier is absent.
  bool initializing_ = false;
  LevelMergeBinding binding_;
  // Derived from (level, ordinal), never supplied.
  unsigned digit_ = 0;
  Family family_;
  RebuildNonce nonce_;
  MergeShape shape_;
  RoutingIndexMap map_;
  RebuildStepContext prepare_, install_, finish_;
  LevelMergeContexts contexts_;
  LevelMergeSpec spec_;
  // The pass's pool and ranks: bound into finish_.residual by pointer, so they
  // must outlive every task that refers to them and must not be resized while
  // one does.  BuildResidualPassFields assigns them wholesale, once,
  // before the finish runs.
  std::vector<ResidualStash*> pool_;
  std::vector<uint8_t> rank_;
  // The top's preparation pass, bound into prepare_.residual the same way and
  // outliving the phase that built it for the same reason.
  std::vector<ResidualStash*> prep_pool_;
  std::vector<uint8_t> prep_rank_;
  ResidualPassSpec pass_spec_;
  // The running phase's coarse tasks and how far it has got (StartPhase).
  // Reserved at construction; one phase at a time uses it.
  std::vector<Subtask> plan_;
  std::vector<PlannedStage> stages_;
  std::vector<size_t> unit_starts_;
  PhaseCursor cursor_;
  // Lanes: `lanes_` stash arrays shaped like
  // `older_sheds_`, and one context per lane, rebuilt at every phase start.
  size_t lanes_ = 1;
  Aligned64Ptr lane_storage_;
  std::vector<ResidualStash> lane_sheds_;
#ifdef MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER
  uint64_t occupancy_job_ = 0;  // merge jobs bound so far (OccupancyEvent::job)
  std::atomic<size_t> observed_stage_{~size_t{0}};
#endif
  std::vector<RebuildStepContext> lane_ctx_;
  std::atomic<uint64_t> laned_stages_{0};
  // Private range masks: `lanes_` runs of
  // `lane_mask_stride_` words, none when the stride is zero.
  size_t lane_mask_stride_ = 0;
  Aligned64Ptr lane_masks_;
  std::atomic<uint64_t> private_mask_stages_{0};
  // The shared executor's state; see ClaimLane.
  OwnerEvent* helper_event_ = nullptr;
  OwnerEvent* owner_event_ = nullptr;
  std::vector<LaneCursor> lane_cursors_;
  SubtaskBudget shared_budget_ = WholeLevelMergeBudget();
  uint64_t claim_seq_ = 0;  // the stage opener's; published in the word
  alignas(64) std::atomic<uint64_t> claim_{0};
  alignas(64) std::atomic<uint64_t> paused_lanes_{0};
  alignas(64) std::atomic<uint32_t> done_lanes_{0};
  std::atomic<size_t> shared_stage_{0};
  std::atomic<bool> shared_open_{false};
  std::atomic<bool> phase_done_{false};
  bool waiting_on_helpers_ = false;
  // Stage timing (EnableStageTiming).
  bool timing_ = false;
  std::array<std::atomic<uint64_t>, kTimedKinds> kind_nanos_{};
  std::array<std::atomic<uint64_t>, 2> class_nanos_{};
  std::atomic<uint64_t> fold_nanos_{0};
  std::chrono::steady_clock::time_point phase_started_;
  std::array<std::atomic<uint64_t>, 3> phase_wall_{};    // NotePhaseEnded
  std::array<std::atomic<uint64_t>, 3> phases_ended_{};
  // LevelMergeCost's accumulators (cost()), and the preparation's end stamp.
  std::atomic<uint64_t> cost_nanos_[LevelMergeCost::kPhases]
                                   [LevelMergeCost::kClasses] = {};
  std::atomic<uint64_t> cost_touches_[LevelMergeCost::kPhases]
                                     [LevelMergeCost::kClasses] = {};
  uint64_t prepare_end_ns_ = 0;
  bool phase_running_ = false;
  LevelMergePhase running_phase_ = LevelMergePhase::kPrepareOlder;
  LevelMergeScratch* phase_scratch_ = nullptr;
};

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
