// Public geometry and scalar map audit. No large tables or secret data.
// Invoked by audit_ordinary_ranges.py; this is not an overflow certificate.
#include "src/oram/levelarena/cpu_byteslice_level_arena_job.hpp"

#include <cstdio>
#include <stdexcept>

namespace bs = microram::byteslice;
namespace la = bs::levelarena;

void Require(bool condition) {
  if (!condition) throw std::runtime_error("ordinary range audit mismatch");
}

void PrintPlan(const bs::ResidualRangePlan& p) {
  std::printf("\"range_bits\":%u,\"index_bits\":%u,\"range_buckets\":%zu,"
              "\"groups\":%zu,\"scatter_per_bucket\":%zu",
              p.range_bits, p.index_bits, p.range_buckets, p.groups,
              p.scatter_per_bucket);
}

// THE DEFAULT HALF-FANOUT LADDER at the worked capacity (4,4,4,8,8,8 under
// an eight-way top, r0 = 8): the library's OWN pools (the certified routing:
// direct level one and separated sources at every later digit) and their DFS
// range plans, with the same scalar map and canonical-family checks as the
// uniform rows, in particular the family forwarding across the fanout-four
// to fanout-eight transition.  Frozen in ordinary_geometry_reference.json's
// half_fanout_passes; no downstream capacity artifact reads these rows.
void AuditLadder(bool half) {
  la::LevelArenaGeometry::Params params;
  params.levels = half ? 7 : 6;
  params.top_digit = 8;
  params.tier_buckets = 0;
  if (half) params.level_fanouts = {4, 4, 4, 8, 8, 8};
  constexpr uint64_t accesses = uint64_t{1} << 32;
  params = la::ResolveLevelArenaTierGeometry(params, accesses);
  const la::LevelArenaGeometry g(params);
  const la::LevelArenaStashSizing sizing(g, accesses);
  for (unsigned level = 1; level < g.Levels(); ++level) {
    const unsigned fanout = g.Fanout(level);
    for (unsigned digit = 1; digit <= fanout; ++digit) {
      if (g.PlanCarry(level, digit).outcome == la::CarryOutcome::kAdopt) {
        std::printf("{\"kind\":\"%sadoption\",\"level\":%u,\"digit\":%u}\n", half ? "half_fanout_" : "", level, digit);
        continue;
      }
      const auto shape = la::LevelMergeShapeOf(g, level, digit);
      const unsigned dense_bits = 0;
      const bool finish_pass = la::FinishRunsPass(g, level, digit);
      auto pool = la::FinishPoolShapeAt(g, sizing.Buckets(level), level, shape);
      if (!finish_pass) {
        pool.swept_buckets = 0;
        pool.direct_buckets = 0;
      }
      const auto plan = la::LevelFinishRangePlan(pool);
      bs::RoutingIndexMap map;
      if (shape.has_radix_pass()) {
        map.kind = bs::TagMapKind::kRadixDigit;
        map.low_bits = shape.block_bits;
        map.modulus = shape.odd_part;
        map.digit_shift = shape.block_bits;
      }
      size_t checks = 0;
      auto check = [&](uint64_t tag) {
        const uint64_t expected = shape.has_radix_pass()
            ? (tag % shape.block_buckets) + shape.block_buckets *
                ((tag / shape.block_buckets) % shape.odd_part)
            : tag;
        const uint64_t mapped = bs::ApplyRoutingIndexMap(map, tag);
        Require(mapped == expected);
        const size_t destination = mapped & bs::LowMask64(pool.main_levels);
        Require(destination < shape.out_buckets);
        Require((destination >> plan.index_bits) < (size_t{1} << plan.range_bits));
        ++checks;
      };
      for (uint64_t t = 0; t < 256; ++t) {
        check(t);
        check(~t);
        check((t << shape.block_bits) - 1);
        check(t << shape.block_bits);
      }
      uint64_t state = 0x4d595df4d0f33173ull;
      for (unsigned i = 0; i < 4096; ++i) {
        state ^= state << 13; state ^= state >> 7; state ^= state << 17;
        check(state);
      }
      // Producer and consumer share a canonical family across every
      // transition, including fanout four under fanout eight; consecutive
      // members at one level differ.
      size_t family_checks = 0;
      for (uint64_t ordinal : {uint64_t{digit}, uint64_t{digit} + fanout,
                               uint64_t{digit} + uint64_t{fanout} * fanout}) {
        const auto family = la::CanonicalFamily(g, level, ordinal);
        if (level > 1) {
          Require(family == la::CanonicalFamily(g, level - 1, ordinal * g.Fanout(level - 1)));
          ++family_checks;
        }
        if (digit > 1) {
          Require(family != la::CanonicalFamily(g, level, ordinal - 1));
          ++family_checks;
        }
      }
      std::printf("{\"kind\":\"%sordinary\",\"level\":%u,\"digit\":%u,"
          "\"fanout\":%u,\"terminal_digit\":%s,\"carry_bits\":%u,\"block_bits\":%u,"
          "\"radix\":%u,\"out_buckets\":%zu,\"main_bits\":%u,\"pool_buckets\":%zu,"
          "\"direct_buckets\":%zu,\"stash_buckets\":%zu,\"older_tier_buckets\":%zu,"
          "\"carry_tier_buckets\":%zu,\"dense_bits\":%u,\"map_checks\":%zu,"
          "\"family_checks\":%zu,",
          half ? "half_fanout_" : "", level, digit, fanout, digit == fanout ? "true" : "false",
          shape.carry_bits, shape.block_bits, shape.odd_part, shape.out_buckets,
          pool.main_levels, pool.swept_buckets, pool.direct_buckets, sizing.Buckets(level),
          g.OlderTierBuckets(level, digit), la::FinishCarryTierBuckets(g, level), dense_bits, checks,
          family_checks);
      std::printf("\"finish_pass\":%s,\"dense_direct\":%s,\"dfs_pages\":1,",
                  finish_pass ? "true" : "false", level == 1 ? "true" : "false");
      PrintPlan(plan);
      std::printf("}\n");
    }
  }
}

int main() {
  AuditLadder(false);
  // Retained planner regimes outside the selected geometry, including empty,
  // direct, packed, and stacked pools. These are map checks only.
  for (unsigned bits = 0; bits <= 12; ++bits) {
    for (size_t pages = 0; pages <= 65; ++pages) {
      std::printf("{\"kind\":\"planner\",\"main_bits\":%u,\"pool_buckets\":%zu,", bits, pages);
      PrintPlan(bs::PlanResidualRange(pages, bits));
      std::printf("}\n");
    }
  }
  AuditLadder(true);
}
