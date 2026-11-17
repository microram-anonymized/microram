// A deterministic bridge from final bucket occupancy to tier capacity.
// Program destinations at half load, route through the real kernels, then
// offer every shed back. The final tier must contain exactly sum (X_b-64)+.
// This tests a structural identity, not the probability of these tags.

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <random>
#include <set>
#include <vector>

#include "src/oram/rebuild/cpu_byteslice_second_chance.hpp"
#include "tests/oram/cpu_byteslice_rebuild_test_support.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"

namespace {
namespace bs = microram::byteslice;
using bs::test_support::Expect;
using bs::test_support::OwnedLevelStashes;

void Check(const std::array<size_t, 8>& loads, unsigned seed,
           size_t tier_buckets) {
  bs::StashLayout layout;
  layout.value_bytes = 1;
  layout.tag_bytes = 1;
  auto main = bs::Table::Create(8, layout.Base());
  std::memset(main.data.get(), 0, 8 * layout.BucketBytes());
  std::vector<uint64_t> keys;
  size_t excess = 0;
  for (size_t b = 0; b < loads.size(); ++b) {
    excess += loads[b] > 64 ? loads[b] - 64 : 0;
    for (size_t j = 0; j < loads[b]; ++j) {
      keys.push_back((static_cast<uint64_t>(keys.size() + 1) << 3) | b);
    }
  }
  Expect(keys.size() == 256, "fixture must have half load");
  std::mt19937 rng(seed);
  std::shuffle(keys.begin(), keys.end(), rng);
  for (size_t i = 0; i < keys.size(); ++i) {
    const size_t bucket = i / 32, slot = i % 32;
    bs::WriteSlotKey(main.Bucket(bucket), slot, 8, bs::KeyWords{keys[i], 0});
    main.Bucket(bucket)[layout.TagOffset() * 64 + slot] = keys[i] & 7;
    main.masks[bucket] |= uint64_t{1} << slot;
  }
  // Capacity alone makes these routing stashes sufficient for all 256 keys.
  OwnedLevelStashes sheds(3, 4, layout);
  Expect(bs::ButterflyRouteStashCacheOblivious<true>(bs::View(main), 3,
                                                    sheds.ptr()),
         "generous route stash overflowed");
  const bs::ResidualStash* pool[] = {
      &sheds.slots[0], &sheds.slots[1], &sheds.slots[2]};
  const auto plan = bs::PlanResidualRange(12, 3);
  auto range = bs::Table::Create(plan.range_buckets, layout.Base());
  bs::ScatterResidualPoolRange(pool, 3, bs::View(range), plan, 0, 12);
  // Scatter copies payload only. Restore the programmed destination from
  // the key in place of hashing, so this is independent of sampled AES tags.
  for (size_t b = 0; b < range.num_buckets; ++b) {
    for (size_t slot = 0; slot < 64; ++slot) {
      range.Bucket(b)[layout.TagOffset() * 64 + slot] =
          bs::ReadSlotKey(range.Bucket(b), slot, 8).w0 & 7;
    }
  }
  bs::ResidualSecondChanceSweep<bs::ResidualDedupRule::kNoDedup>(
      bs::View(main), bs::View(range), plan, layout.Base().PayloadLines());
  size_t leftovers = 0;
  for (size_t b = 0; b < range.num_buckets; ++b)
    leftovers += bs::Popcount64(range.masks[b]);
  Expect(leftovers == excess, "leftovers differ from final occupancy excess");
  for (size_t b = 0; b < loads.size(); ++b)
    Expect(bs::Popcount64(main.masks[b]) == std::min(size_t{64}, loads[b]),
           "second chance left space in an overfull destination");

  OwnedLevelStashes tier(1, tier_buckets, layout);
  const bool packed = bs::DrainResidualTableRange(
      bs::View(range), tier.slots[0], layout.Base().PayloadLines(), 0,
      range.num_buckets);
  Expect(packed == (excess <= 64 * tier_buckets),
         "tier capacity failure does not match the occupancy threshold");
  if (!packed) return;
  Expect(tier.Count() == excess, "packing changed the number of residuals");
  std::set<uint64_t> found;
  for (size_t b = 0; b < loads.size(); ++b) {
    for (size_t slot = 0; slot < 64; ++slot) {
      if (!(main.masks[b] & (uint64_t{1} << slot))) continue;
      const uint64_t key = bs::ReadSlotKey(main.Bucket(b), slot, 8).w0;
      Expect((key & 7) == b, "main record has the wrong destination");
      Expect(found.insert(key).second, "duplicate main record");
    }
  }
  for (size_t b = 0; b < tier_buckets; ++b) {
    for (size_t slot = 0; slot < 64; ++slot) {
      if (!(tier.slots[0].masks[b] & (uint64_t{1} << slot))) continue;
      const uint64_t key = bs::ReadSlotKey(tier.slots[0].Bucket(b), slot, 8).w0;
      Expect(main.masks[key & 7] == ~uint64_t{0},
             "residual targets a bucket that is not full");
      Expect(found.insert(key).second, "duplicate residual record");
    }
  }
  Expect(found == std::set<uint64_t>(keys.begin(), keys.end()),
         "packing lost or invented a key");
}
}  // namespace

int main() {
  const std::array<size_t, 8> cases[] = {
      {64, 64, 64, 64, 0, 0, 0, 0}, {65, 64, 64, 63, 0, 0, 0, 0},
      {128, 64, 64, 0, 0, 0, 0, 0}, {129, 64, 63, 0, 0, 0, 0, 0},
      {192, 64, 0, 0, 0, 0, 0, 0}, {193, 63, 0, 0, 0, 0, 0, 0},
      {256, 0, 0, 0, 0, 0, 0, 0}};
  for (const auto& loads : cases)
    for (unsigned seed = 0; seed < 3; ++seed)
      for (size_t tiers : {size_t{1}, size_t{2}, size_t{3}})
        Check(loads, seed, tiers);
  std::puts("PASS 63 final occupancy / tier packing cases");
}
