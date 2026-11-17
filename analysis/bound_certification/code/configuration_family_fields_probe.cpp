// Fixed-geometry layout/bill variations, without allocating record tables.
// Share the production-shape printer with the existing inventory probe.
#include "src/oram/levelarena/cpu_byteslice_level_arena_capacity.hpp"
#define main configuration_probe_main
#include "configuration_probe.cpp"
#undef main

void PrintShapes(const la::LevelArenaGeometry& g,
                 const la::LevelArenaStashSizing& sizing) {
  for (unsigned level = 1; level <= g.Levels(); ++level) {
    if (level == g.Levels()) {
      const auto shape = la::MakeTopMergeShape(g.CarryBuckets(level), g.TopDigit());
      PrintPass("top_prepare", level, g.TopDigit(), shape,
                la::TopPreparePoolShapeOf(shape, sizing.Buckets(level),
                                         g.OlderTierBuckets(level, 0)),
                sizing.Buckets(level), g.TierBucketsOf(level), 0);
      PrintPass("top_finish", level, g.TopDigit(), shape,
                la::TopMergePoolShapeOf(shape, sizing.Buckets(level),
                                       g.CarryTierBuckets(level)),
                sizing.Buckets(level), g.TierBucketsOf(level), 0, 0,
                g.CarryTierBuckets(level));
      const auto pool = la::TopPreparePoolShapeOf(
          shape, sizing.Buckets(level), g.OlderTierBuckets(level, g.TopDigit()));
      const auto plan = la::TopPrepareRangePlan(pool);
      std::printf("{\"kind\":\"initialization\",\"C\":%zu,\"k\":%u,"
                  "\"stash_pages\":%zu,\"a_tier_pages\":%zu,\"drain_pages\":%zu,"
                  "\"range_bits\":%u,\"I\":%u,\"dfs\":%s}\n",
                  bs::kBucketCapacity, shape.block_bits, sizing.Buckets(level),
                  g.OlderTierBuckets(level, g.TopDigit()), g.TierBucketsOf(level),
                  plan.range_bits, plan.index_bits,
                  bs::DfsResidualRangeApplies(pool.swept_buckets, pool.main_levels)
                      ? "true" : "false");
      continue;
    }
    for (unsigned digit = 1; digit <= g.Fanout(level); ++digit) {
      if (g.PlanCarry(level, digit).outcome == la::CarryOutcome::kAdopt) continue;
      const auto shape = la::LevelMergeShapeOf(g, level, digit);
      PrintPass("ordinary", level, digit, shape,
                la::FinishPoolShapeAt(g, sizing.Buckets(level), level, shape),
                sizing.Buckets(level), g.TierBucketsOf(level),
                level == 1 ? bs::Log2Exact(g.RoutedPrefixBuckets()) : 0,
                g.OlderTierBuckets(level, digit), la::FinishCarryTierBuckets(g, level),
                level == 1, la::MergeStashBuckets(g, sizing.Buckets(level), level));
    }
  }
}

int main(int argc, char** argv) {
  try {
    if (argc != 10) throw std::invalid_argument("expected the nine configuration arguments");
    la::LevelArenaGeometry::Params base;
    base.branching = std::stoul(argv[1]);
    base.levels = std::stoul(argv[2]);
    base.top_digit = std::stoul(argv[3]);
    base.prefix_flushes = std::stoul(argv[4]);
    base.stash_buckets = std::stoull(argv[5]);
    base.dense_prefixes = std::stoul(argv[6]);
    base.tier_buckets = std::stoull(argv[7]);
    const uint64_t horizon = std::stoull(argv[8]);
    const std::string ladder = argv[9];
    if (ladder != "-") {
      size_t at = 0;
      while (at <= ladder.size()) {
        const size_t comma = std::min(ladder.find(',', at), ladder.size());
        base.level_fanouts.push_back(std::stoul(ladder.substr(at, comma - at)));
        at = comma + 1;
      }
    }
    const std::vector<std::string> variants = {
        "baseline", "key_1", "key_4", "key_16", "key_64", "value_1", "value_4",
        "value_8", "value_128", "value_1024", "owners_1", "owners_levels",
        "lanes_2", "lanes_4", "participants_4", "bucket_scan", "synchronous", "bank_off"};
    for (const auto& name : variants) {
      auto params = base;
      la::LevelArenaCapacityRequest request;
      if (name.rfind("key_", 0) == 0) request.key_bytes = std::stoul(name.substr(4));
      if (name.rfind("value_", 0) == 0) request.value_bytes = std::stoul(name.substr(6));
      if (name == "owners_1") request.owner_threads = 1;
      if (name == "owners_levels") request.owner_threads = base.levels;
      if (name.rfind("lanes_", 0) == 0) {
        request.lanes.lanes = std::stoul(name.substr(6));
        request.lanes.min_buckets = 1;
      }
      if (name == "participants_4") request.batch_participants = 4;
      if (name == "bucket_scan") request.batch_bucket_scan = true;
      if (name == "synchronous") request.synchronous = true;
      if (name == "bank_off") params.bank_first = la::BankFirst::kOff;
      params = la::ResolveLevelArenaTierGeometry(params, horizon);
      const la::LevelArenaGeometry geometry(params);
      const auto layout = la::LevelArenaStoredLayout(request.key_bytes, request.value_bytes, geometry);
      if (!bs::RoutingDigitFits(layout)) throw std::runtime_error("routing digit does not fit");
      const la::LevelArenaStashSizing sizing(geometry, horizon);
      const auto bill = la::LevelArenaEngineBytes(
          geometry, layout, sizing, std::max(1u, request.owner_threads),
          request.batch_participants, request.batch_bucket_scan, request.lanes, request.synchronous);
      std::printf("{\"kind\":\"variation\",\"name\":\"%s\",\"bill_bytes\":%zu}\n",
                  name.c_str(), bill.requested());
      PrintShapes(geometry, sizing);
    }
    return 0;
  } catch (const std::exception& error) {
    std::cerr << error.what() << '\n';
    return 2;
  }
}
