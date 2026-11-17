// Configuration-driven public planner probe. Does not allocate record tables.
#include "src/oram/levelarena/cpu_byteslice_level_arena_job.hpp"

#include <cstdio>
#include <iostream>
#include <string>

namespace bs = microram::byteslice;
namespace la = bs::levelarena;

// The library has one residual routing (the certified one), so each pass's
// range builder is its kind's, read from the production headers: the top
// preparation's one-page DFS (TopPrepareRangePlan), and every finish's
// (LevelFinishRangePlan) -- an ordinary digit's and the top merge's alike.
// A finish with a direct tier (a separated pool: a sparse digit above one,
// and the top merge) distributes only A's class through its DFS leaf and
// offers the carry's tier directly.
// dense_bits is retained schema metadata for the L1 carry width; it does
// not describe dense butterfly stages. dense_direct identifies the backend.
void PrintPass(const char* kind, unsigned level, unsigned digit,
               const la::MergeShape& shape, const la::LevelMergePoolShape& pool,
               size_t stash, size_t tier, unsigned dense,
               size_t older_tier = 0, size_t carry_tier = 0, bool dense_direct = false, size_t merge_stash = 0) {
  const std::string k = kind;
  const bool top_finish = k == "top_finish";
  const auto plan = k == "top_prepare" ? la::TopPrepareRangePlan(pool)
                                       : la::LevelFinishRangePlan(pool);
  const bool dfs = bs::DfsResidualRangeApplies(
      pool.swept_buckets - pool.direct_buckets, pool.main_levels);
  if (pool.direct_buckets) {
    // The separated source inventory, from the pass's own slot recipe:
    // A's class (the distributed leaf), B's tier (direct) and the one
    // drain-only insertion/merge shed.
    size_t a_pages = 0, direct_pages = 0, drain_pages = 0, retained_pages = 0;
    std::vector<unsigned> binary_writers(shape.block_bits, 0);
    unsigned radix_writers = 0;
    const auto visit = [&](const la::PoolSlot& slot) {
      const size_t pages = slot.drain_only && merge_stash ? merge_stash : la::PoolSlotBuckets(slot, stash, older_tier, carry_tier);
      if (slot.drain_only) {
        if (slot.storage != la::PoolSlotStorage::kOlderShed ||
            slot.index != shape.block_bits + la::kLevelMergeMergeStashOffset)
          throw std::invalid_argument("insertion shed is not separate drain-only storage");
        drain_pages += pages;
      } else if (slot.tier_class) {
        if (slot.storage != la::PoolSlotStorage::kCarryTier)
          throw std::invalid_argument("direct source is not B tier");
        direct_pages += pages;
      } else {
        a_pages += pages;
        if (slot.storage == la::PoolSlotStorage::kOlderShed) {
          if (top_finish &&
              slot.index == shape.block_bits + la::kLevelMergePrepCarryStashOffset)
            retained_pages += pages;
          else if (!top_finish && slot.index < shape.block_bits) ++binary_writers[slot.index];
          else if (!top_finish &&
                   slot.index == shape.block_bits + la::kLevelMergeRadixStashOffset)
            ++radix_writers;
          else throw std::invalid_argument("unexpected A shed slot");
        } else if (top_finish || slot.storage != la::PoolSlotStorage::kOlderTier) {
          throw std::invalid_argument("unexpected A source");
        }
      }
    };
    if (top_finish) la::TopMergePoolSlots(shape, visit);
    else la::SeparatedFinishPoolSlots(shape, visit);
    if (!top_finish)
      for (unsigned count : binary_writers)
        if (count != 1) throw std::invalid_argument("missing or repeated A binary stash");
    // At the top A's class is the preparation's retained carry alone.
    const size_t a_expected = top_finish
        ? stash : older_tier + stash * (shape.block_bits + radix_writers);
    if (radix_writers != unsigned(!top_finish && shape.has_radix_pass()) ||
        drain_pages != (merge_stash ? merge_stash : stash) || direct_pages != carry_tier ||
        pool.direct_buckets != carry_tier || a_pages != a_expected ||
        (top_finish && retained_pages != stash) ||
        pool.swept_buckets != a_pages + direct_pages)
      throw std::invalid_argument("separated source inventory mismatch");
  } else if (top_finish) {
    throw std::invalid_argument("the top merge offers B's tier directly");
  }
  std::printf("{\"kind\":\"%s\",\"level\":%u,\"digit\":%u,"
      "\"carry_bits\":%u,\"block_bits\":%u,\"radix\":%u,"
      "\"out_buckets\":%zu,\"main_bits\":%u,\"pool_buckets\":%zu,"
      "\"stash_buckets\":%zu,\"tier_buckets\":%zu,\"dense_bits\":%u,"
      "\"range_bits\":%u,\"index_bits\":%u,\"range_buckets\":%zu,"
      "\"groups\":%zu,\"scatter_per_bucket\":%zu,"
      "\"separated_sources\":%s,\"dfs\":%s,\"direct_buckets\":%zu,\"older_tier_buckets\":%zu,\"carry_tier_buckets\":%zu,\"dense_direct\":%s,\"merge_stash_buckets\":%zu}\n",
      kind, level, digit, shape.carry_bits, shape.block_bits, shape.odd_part,
      shape.out_buckets, pool.main_levels, pool.swept_buckets, stash, tier,
      dense, plan.range_bits, plan.index_bits, plan.range_buckets, plan.groups,
      plan.scatter_per_bucket, pool.direct_buckets ? "true" : "false",
      dfs ? "true" : "false", pool.direct_buckets, older_tier, carry_tier, dense_direct ? "true" : "false", merge_stash ? merge_stash : stash);
}

int main(int argc, char** argv) {
  try {
    // Eight public parameters, then an optional fanout ladder for levels
    // 1..L-1 ("4,4,4,8,8,8"); none, or "-", is the uniform ladder.
    const bool emit_init = argc == 11 && std::string(argv[10]) == "--init-shape";
    if (argc != 9 && argc != 10 && !emit_init)
      throw std::invalid_argument("expected eight public parameters and an optional fanout ladder");
    la::LevelArenaGeometry::Params p;
    p.branching = std::stoul(argv[1]);
    p.levels = std::stoul(argv[2]);
    p.top_digit = std::stoul(argv[3]);
    p.prefix_flushes = std::stoul(argv[4]);
    p.stash_buckets = std::stoull(argv[5]);
    p.dense_prefixes = std::stoul(argv[6]);
    p.tier_buckets = std::stoull(argv[7]);
    const uint64_t horizon = std::stoull(argv[8]);
    if (argc >= 10 && std::string(argv[9]) != "-") {
      const std::string ladder = argv[9];
      size_t at = 0;
      while (at <= ladder.size()) {
        const size_t comma = std::min(ladder.find(',', at), ladder.size());
        size_t used = 0;
        const std::string item = ladder.substr(at, comma - at);
        const unsigned long fanout = std::stoul(item, &used);
        if (used != item.size()) throw std::invalid_argument("malformed fanout ladder");
        p.level_fanouts.push_back(static_cast<unsigned>(fanout));
        at = comma + 1;
      }
    }
    p = la::ResolveLevelArenaTierGeometry(p, horizon);
    const la::LevelArenaGeometry g(p);
    const la::LevelArenaStashSizing sizing(g, horizon);
    std::printf("{\"kind\":\"geometry\",\"top_buckets\":%zu,"
                "\"tier_buckets\":%zu,\"prefix_positions\":%llu,"
                "\"arena_buckets\":%zu,\"capacity_entries\":%llu}\n",
                g.TopBuckets(), g.TierBuckets(),
                static_cast<unsigned long long>(g.PrefixPositions()),
                g.ArenaBuckets(), static_cast<unsigned long long>(g.CapacityEntries()));
    const auto seed = la::DirectInitializationSeed(g);
    for (unsigned l = 1; l <= g.Levels(); ++l) {
      std::printf("{\"kind\":\"level\",\"level\":%u,\"carry_buckets\":%zu,"
                  "\"carry_positions\":%llu,\"stash_buckets\":%zu,\"tier_buckets\":%zu}\n",
                  l, g.CarryBuckets(l),
                  static_cast<unsigned long long>(la::CheckedMul(32, g.CarryBuckets(l), "carry positions")),
                  sizing.Buckets(l), g.TierBucketsOf(l));
      std::printf("{\"kind\":\"ordinal_seed\",\"level\":%u,\"fanout\":%u,\"seeded_carries\":%llu}\n",
                  l, l < g.Levels() ? g.Fanout(l) : g.TopDigit(),
                  static_cast<unsigned long long>(seed.level_carries[l]));
      if (l == g.Levels()) {
        const auto shape = la::MakeTopMergeShape(g.CarryBuckets(l), g.TopDigit());
        PrintPass("top_prepare", l, g.TopDigit(), shape,
                  la::TopPreparePoolShapeOf(shape, sizing.Buckets(l),
                                            g.OlderTierBuckets(l, 0)),
                  sizing.Buckets(l), g.TierBucketsOf(l), 0);
        // The merge's pool as BuildTopMergePass binds it: the retained
        // carry (A) and B's carry tier, offered directly.
        PrintPass("top_finish", l, g.TopDigit(), shape,
                  la::TopMergePoolShapeOf(shape, sizing.Buckets(l),
                                          g.CarryTierBuckets(l)),
                  sizing.Buckets(l), g.TierBucketsOf(l), 0, 0, g.CarryTierBuckets(l));
        continue;
      }
      for (unsigned d = 1; d <= g.Fanout(l); ++d) {
        if (g.PlanCarry(l, d).outcome == la::CarryOutcome::kAdopt) {
          std::printf("{\"kind\":\"adoption\",\"level\":%u,\"digit\":%u}\n", l, d);
          continue;
        }
        const auto shape = la::LevelMergeShapeOf(g, l, d);
        const unsigned dense = l == 1 ? bs::Log2Exact(g.RoutedPrefixBuckets()) : 0;
        PrintPass("ordinary", l, d, shape,
                  la::FinishPoolShapeAt(g, sizing.Buckets(l), l, shape),
                  sizing.Buckets(l), g.TierBucketsOf(l), dense,
                  g.OlderTierBuckets(l, d), la::FinishCarryTierBuckets(g, l), l == 1,
                  la::MergeStashBuckets(g, sizing.Buckets(l), l));
      }
    }
    if (emit_init) {
      // Shape only: Initialize uses the preparation route but drains to the
      // published top tier, while PrepareOlder drains to the retained carry.
      const unsigned l = g.Levels();
      const auto shape = la::MakeTopMergeShape(g.CarryBuckets(l), g.TopDigit());
      const size_t atier = g.OlderTierBuckets(l, g.TopDigit());
      const auto pool = la::TopPreparePoolShapeOf(shape, sizing.Buckets(l), atier);
      const auto plan = la::TopPrepareRangePlan(pool);
      std::printf("{\"kind\":\"initialization\",\"C\":%zu,\"k\":%u,"
                  "\"stash_pages\":%zu,\"a_tier_pages\":%zu,\"drain_pages\":%zu,"
                  "\"range_bits\":%u,\"I\":%u,\"dfs\":%s}\n",
                  bs::kBucketCapacity, shape.block_bits, sizing.Buckets(l), atier,
                  g.TierBucketsOf(l), plan.range_bits, plan.index_bits,
                  bs::DfsResidualRangeApplies(pool.swept_buckets, pool.main_levels)
                      ? "true" : "false");
    }
    return 0;
  } catch (const std::exception& e) {
    std::cerr << e.what() << '\n';
    return 2;
  }
}
