// The capacity planner's candidate space at one capacity, and per-candidate
// map/family checks.  Reads the public planner and geometry only; allocates
// no record tables.
//
//   candidates ENTRIES B s q H
//     Every candidate PlanLevelArenaCapacity would price for a request of
//     ENTRIES entries at branching B, stash unit s, q outstanding prefixes
//     and horizon H: both fanout ladders (the half-fanout prefix of `a`
//     levels and the bottom fanout `b_1`), every L, r0 in {2,4,8} and binary
//     D <= B, filtered EXACTLY as the planner's loop filters them (the
//     capacity, the tier resolution, the geometry, the stored layout's digit
//     room, the stash sizing and the buffer bill must all succeed).  The
//     feasibility filters are re-run at several value widths to show they do
//     not depend on it.  Then the planner itself: its unpinned choice at
//     several value widths, the candidate COUNT it reports under each pinned
//     ladder axis (a cross-check of this enumeration), and its answer under
//     every pin of (r0, D, ladder axis).
//
//   families B L D r0 s q tier H ladder
//     The routing-map and canonical-family checks of ordinary_range_probe's
//     half-fanout rows, at any geometry: every ordinary job's radix map sends
//     each tag to its output and coarse range, producer and consumer share a
//     canonical family across every fanout transition, and consecutive
//     members at one level differ.
#include "src/oram/levelarena/cpu_byteslice_level_arena_capacity.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_family.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_job.hpp"

#include <cstdio>
#include <iostream>
#include <string>
#include <vector>

namespace bs = microram::byteslice;
namespace la = bs::levelarena;

namespace {

void Require(bool value, const char* what) {
  if (!value) throw std::runtime_error(what);
}

const size_t kValueWidths[] = {1, 8, 16, 64, 256, 1024};

void PrintFanouts(const std::vector<unsigned>& fanouts) {
  std::printf("[");
  for (size_t i = 0; i < fanouts.size(); ++i) std::printf("%s%u", i ? "," : "", fanouts[i]);
  std::printf("]");
}

// The planner loop's filters for one candidate, at one value width.  Returns
// false where the planner's loop would `continue`.
bool Feasible(la::LevelArenaGeometry::Params params, uint64_t entries,
              uint64_t horizon, size_t value_bytes,
              la::LevelArenaGeometry::Params* resolved, size_t* bill,
              uint64_t* capacity) {
  try {
    *capacity = la::LevelArenaCapacityOf(params);
  } catch (const std::exception&) {
    return false;
  }
  if (*capacity < entries) return false;
  try {
    params = la::ResolveLevelArenaTierGeometry(params, horizon);
    const la::LevelArenaGeometry geometry(params);
    const bs::Layout layout = la::LevelArenaStoredLayout(8, value_bytes, geometry);
    if (!bs::RoutingDigitFits(layout)) return false;
    const la::LevelArenaStashSizing sizing(geometry, horizon);
    *bill = la::LevelArenaEngineBytes(geometry, layout, sizing, 1, 1, false, {})
                .requested();
    *resolved = params;
  } catch (const std::exception&) {
    return false;
  }
  return true;
}

void PrintChoice(const char* kind, const la::LevelArenaCapacityRequest& r,
                 const la::LevelArenaCapacityChoice& c) {
  std::vector<unsigned> fanouts = c.geometry.level_fanouts;
  if (fanouts.empty()) fanouts.assign(c.geometry.levels - 1, c.geometry.branching);
  std::printf("{\"kind\":\"%s\",\"value_bytes\":%zu,\"pin_prefix_flushes\":%u,"
              "\"pin_top_digit\":%u,\"min_top_digit\":%u,\"half_fanout_prefix_requested\":%s,"
              "\"pin_half_prefix_levels\":%u,\"pin_bottom_fanout\":%u,"
              "\"levels\":%u,\"prefix_flushes\":%u,\"top_digit\":%u,\"level_fanouts\":",
              kind, r.value_bytes, r.prefix_flushes, r.top_digit, r.min_top_digit,
              r.half_fanout_prefix ? "true" : "false", r.half_prefix_levels, r.bottom_fanout,
              c.geometry.levels, c.geometry.prefix_flushes, c.geometry.top_digit);
  PrintFanouts(fanouts);
  std::printf(",\"capacity_entries\":%llu,\"tier_buckets\":%zu,\"bill_requested\":%zu,"
              "\"candidates\":%zu,\"half_fanout_prefix\":%s}\n",
              static_cast<unsigned long long>(c.capacity), c.geometry.tier_buckets,
              c.bill.requested(), c.candidates, c.half_fanout_prefix ? "true" : "false");
}

int Candidates(uint64_t entries, unsigned branching, size_t stash, unsigned q,
               uint64_t horizon) {
  la::LevelArenaCapacityRequest base;
  base.entries = entries;
  base.max_accesses = horizon;
  base.branching = branching;
  base.stash_buckets = stash;
  base.dense_prefixes = q;
  const unsigned max_top = std::min(branching, la::LevelArenaGeometry::kMaxTopDigit);
  const bool prefix_applies = la::UsesHalfFanoutPrefix(base);
  // (ladder, axis) pairs, exactly the two searches' axes.
  std::vector<std::pair<bool, unsigned>> axes;
  if (prefix_applies)
    for (unsigned a = 1; a <= bs::Log2Exact(branching); ++a) axes.push_back({true, a});
  for (unsigned b = 2; b <= branching; b *= 2) axes.push_back({false, b});
  std::vector<size_t> counts(axes.size(), 0);
  for (unsigned levels = 2; levels <= base.max_levels; ++levels) {
    for (unsigned flushes : {2u, 4u, 8u}) {
      for (unsigned digit = 1; digit <= max_top; ++digit) {
        if (!la::LevelArenaGeometry::IsTopDigit(digit)) continue;
        for (size_t x = 0; x < axes.size(); ++x) {
          const auto [half, axis] = axes[x];
          if (half && axis > levels - 1) continue;
          la::LevelArenaGeometry::Params params;
          params.branching = branching;
          params.levels = levels;
          params.top_digit = digit;
          params.prefix_flushes = flushes;
          params.stash_buckets = stash;
          params.dense_prefixes = q;
          params.tier_buckets = 0;
          params.level_fanouts = half ? la::HalfPrefixFanouts(branching, levels, axis)
                                      : la::BottomFanouts(branching, levels, axis);
          la::LevelArenaGeometry::Params resolved;
          size_t bill = 0;
          uint64_t capacity = 0;
          std::string widths;
          bool any = false;
          size_t bill16 = 0;
          for (size_t value : kValueWidths) {
            size_t b = 0;
            if (Feasible(params, entries, horizon, value, &resolved, &b, &capacity)) {
              widths += (any ? "," : "") + std::to_string(value);
              any = true;
              if (value == 16) bill16 = b;
            }
          }
          if (!any) continue;
          // The planner's own count is at its default width, 16 bytes.
          bill = bill16;
          if (bill16 != 0) ++counts[x];
          const la::LevelArenaGeometry g(resolved);
          const la::LevelArenaStashSizing sizing(g, horizon);
          std::printf("{\"kind\":\"candidate\",\"ladder\":\"%s\",\"axis\":%u,\"levels\":%u,"
                      "\"prefix_flushes\":%u,\"top_digit\":%u,\"level_fanouts\":",
                      half ? "half_fanout_prefix" : "bottom_fanout", axis, levels, flushes, digit);
          PrintFanouts(params.level_fanouts);
          std::printf(",\"capacity_entries\":%llu,\"tier_buckets\":%zu,\"bill_requested\":%zu,"
                      "\"feasible_value_bytes\":[%s],\"stash_buckets\":[",
                      static_cast<unsigned long long>(capacity), resolved.tier_buckets, bill,
                      widths.c_str());
          for (unsigned l = 1; l <= g.Levels(); ++l)
            std::printf("%s%zu", l > 1 ? "," : "", sizing.Buckets(l));
          std::printf("],\"level_tier_buckets\":[");
          for (unsigned l = 1; l <= g.Levels(); ++l)
            std::printf("%s%zu", l > 1 ? "," : "", g.TierBucketsOf(l));
          std::printf("],\"carry_buckets\":[");
          for (unsigned l = 1; l <= g.Levels(); ++l)
            std::printf("%s%zu", l > 1 ? "," : "", g.CarryBuckets(l));
          std::printf("]}\n");
        }
      }
    }
  }
  // The planner's own counts, one pinned ladder axis at a time, every D.
  for (size_t x = 0; x < axes.size(); ++x) {
    la::LevelArenaCapacityRequest r = base;
    r.min_top_digit = 1;
    r.half_fanout_prefix = axes[x].first;
    if (axes[x].first) r.half_prefix_levels = axes[x].second;
    else r.bottom_fanout = axes[x].second;
    const auto c = la::PlanLevelArenaCapacity(r);
    std::printf("{\"kind\":\"planner_count\",\"ladder\":\"%s\",\"axis\":%u,"
                "\"planner_candidates\":%zu,\"enumerated\":%zu}\n",
                axes[x].first ? "half_fanout_prefix" : "bottom_fanout", axes[x].second,
                c.candidates, counts[x]);
  }
  // The unpinned default at several value widths, and with the D floor
  // lowered to one.
  for (size_t value : kValueWidths) {
    la::LevelArenaCapacityRequest r = base;
    r.value_bytes = value;
    PrintChoice("planner_default", r, la::PlanLevelArenaCapacity(r));
    r.min_top_digit = 1;
    PrintChoice("planner_min_top_digit_1", r, la::PlanLevelArenaCapacity(r));
  }
  // Every pin: (r0, D, ladder axis).  D below the default floor needs the
  // floor lowered, which the request refuses to do silently.
  for (unsigned flushes : {2u, 4u, 8u}) {
    for (unsigned digit = 1; digit <= max_top; digit *= 2) {
      for (const auto& [half, axis] : axes) {
        la::LevelArenaCapacityRequest r = base;
        r.prefix_flushes = flushes;
        r.top_digit = digit;
        r.min_top_digit = 1;
        r.half_fanout_prefix = half;
        if (half) r.half_prefix_levels = axis;
        else r.bottom_fanout = axis;
        try {
          PrintChoice("planner_pinned", r, la::PlanLevelArenaCapacity(r));
        } catch (const std::exception& e) {
          std::printf("{\"kind\":\"planner_pinned_refused\",\"pin_prefix_flushes\":%u,"
                      "\"pin_top_digit\":%u,\"ladder\":\"%s\",\"axis\":%u}\n",
                      flushes, digit, half ? "half_fanout_prefix" : "bottom_fanout", axis);
        }
      }
    }
  }
  return 0;
}

int Families(char** argv) {
  la::LevelArenaGeometry::Params p;
  p.branching = std::stoul(argv[0]);
  p.levels = std::stoul(argv[1]);
  p.top_digit = std::stoul(argv[2]);
  p.prefix_flushes = std::stoul(argv[3]);
  p.stash_buckets = std::stoull(argv[4]);
  p.dense_prefixes = std::stoul(argv[5]);
  p.tier_buckets = std::stoull(argv[6]);
  const uint64_t horizon = std::stoull(argv[7]);
  const std::string ladder = argv[8];
  if (ladder != "-") {
    size_t at = 0;
    while (at <= ladder.size()) {
      const size_t comma = std::min(ladder.find(',', at), ladder.size());
      p.level_fanouts.push_back(std::stoul(ladder.substr(at, comma - at)));
      at = comma + 1;
    }
  }
  p = la::ResolveLevelArenaTierGeometry(p, horizon);
  const la::LevelArenaGeometry g(p);
  const la::LevelArenaStashSizing sizing(g, horizon);
  size_t map_checks = 0, family_checks = 0, jobs = 0, adoptions = 0;
  for (unsigned level = 1; level < g.Levels(); ++level) {
    const unsigned fanout = g.Fanout(level);
    for (unsigned digit = 1; digit <= fanout; ++digit) {
      for (uint64_t ordinal : {uint64_t{digit}, uint64_t{digit} + fanout,
                               uint64_t{digit} + uint64_t{fanout} * fanout}) {
        const auto family = la::CanonicalFamily(g, level, ordinal);
        if (level > 1) {
          Require(family == la::CanonicalFamily(g, level - 1, ordinal * g.Fanout(level - 1)),
                  "producer and consumer families differ");
          ++family_checks;
        }
        if (digit > 1) {
          Require(family != la::CanonicalFamily(g, level, ordinal - 1),
                  "consecutive members share a family");
          ++family_checks;
        }
      }
      if (g.PlanCarry(level, digit).outcome == la::CarryOutcome::kAdopt) {
        ++adoptions;
        continue;
      }
      ++jobs;
      const auto shape = la::LevelMergeShapeOf(g, level, digit);
      const auto pool = la::LevelMergePoolShapeOf(shape, sizing.Buckets(level),
          g.OlderTierBuckets(level, digit), g.CarryTierBuckets(level));
      const auto plan = la::LevelFinishRangePlan(pool);
      bs::RoutingIndexMap map;
      if (shape.has_radix_pass()) {
        map.kind = bs::TagMapKind::kRadixDigit;
        map.low_bits = shape.block_bits;
        map.modulus = shape.odd_part;
        map.digit_shift = shape.block_bits;
      }
      auto check = [&](uint64_t tag) {
        const uint64_t expected = shape.has_radix_pass()
            ? (tag % shape.block_buckets) + shape.block_buckets *
                ((tag / shape.block_buckets) % shape.odd_part)
            : tag;
        const uint64_t mapped = bs::ApplyRoutingIndexMap(map, tag);
        Require(mapped == expected, "routing map differs from the scalar model");
        const size_t destination = mapped & bs::LowMask64(pool.main_levels);
        Require(destination < shape.out_buckets, "destination outside the output");
        Require((destination >> plan.index_bits) < (size_t{1} << plan.range_bits),
                "destination outside the coarse ranges");
        ++map_checks;
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
    }
  }
  std::printf("{\"kind\":\"families\",\"jobs\":%zu,\"adoptions\":%zu,\"map_checks\":%zu,"
              "\"family_checks\":%zu,\"passed\":true}\n", jobs, adoptions, map_checks,
              family_checks);
  return 0;
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const std::string mode = argc > 1 ? argv[1] : "";
    if (mode == "candidates" && argc == 7)
      return Candidates(std::stoull(argv[2]), std::stoul(argv[3]), std::stoull(argv[4]),
                        std::stoul(argv[5]), std::stoull(argv[6]));
    if (mode == "families" && argc == 11) return Families(argv + 2);
    throw std::invalid_argument(
        "usage: candidates ENTRIES B s q H | families B L D r0 s q tier H ladder");
  } catch (const std::exception& e) {
    std::cerr << e.what() << '\n';
    return 2;
  }
}
