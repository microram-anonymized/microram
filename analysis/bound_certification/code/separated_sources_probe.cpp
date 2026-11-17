// Descriptor-only audit of the native separated topology and allocation bounds.
#include "src/oram/levelarena/cpu_byteslice_level_arena_owner.hpp"
#include <cstdio>
#include <stdexcept>
namespace bs = microram::byteslice;
namespace la = bs::levelarena;
void Require(bool b) { if (!b) throw std::runtime_error("separated source audit"); }
struct Counts {
  size_t tasks = 0, touches = 0, crosses = 0, insertions = 0, installs = 0;
  void push_back(const bs::Subtask& t) {
    ++tasks; touches += bs::PieceTouches(t);
    if (t.kind == bs::Subtask::kCrossLevelRange || t.kind == bs::Subtask::kRadixPassRange)
      crosses += t.end - t.begin;
    if (t.kind == bs::Subtask::kFixedMergeRange) insertions += t.end - t.begin;
    if (t.kind == bs::Subtask::kCopyAndRetagFresher || t.kind == bs::Subtask::kCopyFresher)
      installs += t.end - t.begin;
  }
};
void Audit(const la::LevelArenaGeometry::Params& p, unsigned fanout, unsigned profile) {
  const bs::Layout layout{8, 16, 8};
  {
    const la::LevelArenaGeometry g(p);
    const la::LevelArenaStashSizing sizing(g, uint64_t{1} << 32);
    // The library's one residual routing selects separated sources at every
    // sparse digit above one.
    for (unsigned l = 2; l < g.Levels(); ++l) {
      const auto alloc = la::MaxLevelDfsAllocation(g, sizing, l);
      const size_t scratch = la::MaxLevelMergeRangeBuckets(g, sizing, l);
      for (unsigned d = 1; d <= g.Fanout(l); ++d) {
        const bool selected = la::SeparatedSources(g, l, d);
        if (!selected) continue;
        const auto shape = la::LevelMergeShapeOf(g, l, d);
        const auto pool = la::LevelMergePoolShapeOf(shape, sizing.Buckets(l),
            g.OlderTierBuckets(l, d), g.CarryTierBuckets(l));
        const auto plan = la::LevelFinishRangePlan(pool);
        Require(plan.groups == 1 && pool.direct_buckets == g.CarryTierBuckets(l));
        Require(scratch >= plan.range_buckets + pool.direct_buckets);
        Require(alloc.pages == 1 && alloc.max_coarse_bits >= plan.range_bits &&
                alloc.max_pool_buckets >= pool.swept_buckets - pool.direct_buckets);
        size_t a_slots = 0, direct_slots = 0, drain_slots = 0;
        la::SeparatedFinishPoolSlots(shape, [&](const la::PoolSlot& slot) {
          if (slot.drain_only) {
            ++drain_slots;
            Require(slot.rank == 0 && slot.index == shape.block_bits + la::kLevelMergeMergeStashOffset);
          } else if (slot.tier_class) {
            ++direct_slots; Require(slot.storage == la::PoolSlotStorage::kCarryTier && slot.rank == 0);
          } else { ++a_slots; Require(slot.rank == 2); }
        });
        Require(drain_slots == 1 && direct_slots == 1 &&
                a_slots == shape.block_bits + 1 + shape.has_radix_pass());
        bs::RebuildStepContext ctx;
        ctx.out = {layout, shape.out_buckets, nullptr, nullptr};
        ctx.older = {layout, shape.older_buckets, nullptr, nullptr};
        ctx.fresher = {layout, shape.carry_buckets, nullptr, nullptr};
        ctx.upper_offset = shape.carry_buckets; ctx.route_levels = shape.block_bits;
        ctx.aes_keys = &bs::DefaultAesTagKeys(); ctx.retag_fresher_digits = true;
        if (shape.has_radix_pass()) {
          ctx.map.kind = bs::TagMapKind::kRadixDigit;
          ctx.map.low_bits = shape.block_bits; ctx.map.modulus = shape.odd_part;
          ctx.map.digit_shift = bs::RoutingDigitShift(layout);
        }
        la::LevelMergeSpec spec; spec.shape = shape; spec.separated_sources = true;
        const auto contexts = la::LevelMergeContexts::Shared(ctx);
        const auto budget = la::WholeLevelMergeBudget();
        Counts prep, install, finish;
        la::PlanLevelMergePhase(la::LevelMergePhase::kPrepareOlder, contexts, spec, budget, &prep);
        la::PlanLevelMergePhase(la::LevelMergePhase::kInstallCarry, contexts, spec, budget, &install);
        la::PlanLevelMergePhase(la::LevelMergePhase::kFinish, contexts, spec, budget, &finish);
        Require(prep.crosses == 0 && prep.installs == 0 && finish.crosses == 0 &&
                install.tasks == 0 && finish.insertions == shape.carry_buckets);
        Require(prep.tasks <= la::LevelPhasePlanCapacity(g, layout, l));
        const auto work = la::LevelMergeResidualTouchSplit(g, layout, sizing, l, d);
        Require(work.offers == double(shape.out_buckets * (1 + pool.direct_buckets)));
        std::printf("{\"fanout\":%u,\"profile\":%u,\"level\":%u,\"digit\":%u,"
          "\"carry_buckets\":%zu,\"block_bits\":%u,\"radix\":%u,\"A_pool_pages\":%zu,"
          "\"A_leaf_pages\":%zu,\"index_bits\":%u,\"B_pages\":%zu,\"scratch_pages\":%zu,"
          "\"prepare_main_touches\":%zu,\"finish_main_touches\":%zu,"
          "\"residual_pass_touches\":%.0f,\"offer_touches\":%.0f,"
          "\"old_dedup_pairs\":%zu,\"new_dedup_pairs\":%zu}\n",
          fanout, profile, l, d, shape.carry_buckets, shape.block_bits, shape.odd_part,
          pool.swept_buckets - pool.direct_buckets, plan.range_buckets, plan.index_bits,
          pool.direct_buckets, scratch, prep.touches, finish.touches, work.passes, work.offers,
          (d - 1) * shape.carry_buckets, d * shape.carry_buckets);
      }
    }
  }
}

int main() {
  for (unsigned fanout : {2u, 4u, 8u}) for (unsigned profile : {0u, 1u, 2u}) {
    la::LevelArenaGeometry::Params p;
    p.branching = fanout; p.levels = 4; p.top_digit = 2;
    p.tier_buckets = profile == 0 ? 1 : 2;
    if (profile == 2) {
      p.level_tier_buckets = {1, 1, 1, 2};
      if (fanout == 8) p.level_fanouts = {4, 4, 8};
    }
    Audit(p, fanout, profile);
  }
  // The two selected worked configurations at their resolved tier width:
  // profile 3 is the uniform-eight analysis ladder (six levels), profile 4
  // the default half-fanout ladder at the same capacity (4,4,4,8,8,8).
  for (unsigned profile : {3u, 4u}) {
    la::LevelArenaGeometry::Params p;
    p.branching = 8; p.levels = profile == 3 ? 6 : 7; p.top_digit = 8;
    p.prefix_flushes = 8; p.tier_buckets = 0;
    if (profile == 4) p.level_fanouts = {4, 4, 4, 8, 8, 8};
    p = la::ResolveLevelArenaTierGeometry(p, uint64_t{1} << 32);
    Audit(p, 8, profile);
  }
}
