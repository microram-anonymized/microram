// Read production geometry, old-home maps and family coordinates, without
// allocating tables. Full job behavior is checked by the native job tests.
#include "src/oram/levelarena/cpu_byteslice_level_arena_job.hpp"

#include <cstdio>
#include <stdexcept>

namespace bs = microram::byteslice;
namespace la = bs::levelarena;

void Require(bool ok) {
  if (!ok) throw std::runtime_error("preparation contract probe mismatch");
}

int main() {
  la::LevelArenaGeometry::Params p;
  p.levels = 6;
  p.top_digit = 8;
  p.tier_buckets = 0;
  p = la::ResolveLevelArenaTierGeometry(p, uint64_t{1} << 32);
  const la::LevelArenaGeometry g(p);
  for (unsigned level = 1; level < g.Levels(); ++level) {
    Require(g.PrefixPositions() * g.PrefixProduct(level) ==
            32 * g.CarryBuckets(level));
    for (unsigned digit = 2; digit <= g.Fanout(level); ++digit) {
      // A is the completed PREVIOUS digit, not the destination digit.
      const auto old = la::LevelMergeShapeOf(g, level, digit - 1);
      const auto next = la::LevelMergeShapeOf(g, level, digit);
      bs::RoutingIndexMap map;
      if (old.has_radix_pass()) {
        map.kind = bs::TagMapKind::kRadixDigit;
        map.low_bits = old.block_bits;
        map.modulus = old.odd_part;
        map.digit_shift = old.block_bits;  // physical, not stored-tag index
      }
      auto check = [&](uint64_t word) {
        const uint64_t expected = word % old.block_buckets +
            old.block_buckets * ((word / old.block_buckets) % old.odd_part);
        const uint64_t actual = bs::ApplyRoutingIndexMap(map, word) &
            bs::LowMask64(la::ResidualCeilLog2(old.out_buckets));
        Require(actual == expected && actual < old.out_buckets);
      };
      for (uint64_t word = 0; word < 1024; ++word) {
        check(word);
        check(~word);
        check(word << old.block_bits);
      }
      size_t families = 0;
      for (uint64_t cycle = 0; cycle < 256; ++cycle) {
        const uint64_t ordinal = cycle * g.Fanout(level) + digit;
        const auto fresh = la::CanonicalFamily(g, level, ordinal);
        const auto previous = la::CanonicalFamily(g, level, ordinal - 1);
        Require(fresh != previous);
        Require(la::FamilyNonce(fresh).real_high !=
                la::FamilyNonce(previous).real_high);
        if (level > 1) {
          Require(fresh == la::CanonicalFamily(
              g, level - 1, ordinal * g.Fanout(level - 1)));
        }
        ++families;
      }
      std::printf("{\"level\":%u,\"digit\":%u,\"old_digit\":%u,"
                  "\"old_buckets\":%zu,\"old_low_bits\":%u,"
                  "\"old_radix\":%u,\"population_bound\":%zu,"
                  "\"out_buckets\":%zu,\"family_checks\":%zu}\n",
                  level, digit, digit - 1, old.out_buckets, old.block_bits,
                  old.odd_part, 32 * old.out_buckets, next.out_buckets, families);

    }
  }
  const auto seed = la::DirectInitializationSeed(g);
  Require(seed.access_offset == g.CapacityEntries());
  Require(la::EmptyTopNonce(g.Levels()).real_high !=
          la::FamilyNonce(seed.top_family).real_high);
  for (uint64_t ordinal = 2; ordinal < 258; ++ordinal) {
    Require(la::CanonicalFamily(g, g.Levels(), ordinal) !=
            la::CanonicalFamily(g, g.Levels(), ordinal - 1));
    Require(la::CanonicalFamily(g, g.Levels(), ordinal) ==
            la::CanonicalFamily(g, g.Levels() - 1,
                                ordinal * g.Fanout(g.Levels() - 1)));
  }
}
