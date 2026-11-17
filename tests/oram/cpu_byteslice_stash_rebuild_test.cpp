// Correctness tests for the load-0.5 byte-sliced rebuild primitives
// (src/oram/rebuild/cpu_byteslice_stash_rebuild.hpp): residual
// emission and oblivious stash merging in MergeSplit, multi-bucket stash
// cascade, bucket contraction/fold, meta-line helpers, and an end-to-end
// overloaded butterfly whose residuals must be conserved in the stash.

#include "src/oram/rebuild/cpu_byteslice_stash_rebuild.hpp"
#include "tests/oram/cpu_byteslice_rebuild_test_support.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <random>
#include <unordered_map>
#include <vector>

namespace {

namespace bs = microram::byteslice;
using microram::byteslice::test_support::Expect;
using microram::byteslice::test_support::OwnedLevelStashes;

std::vector<uint8_t> MakeEntryBytes(const bs::StashLayout& layout,
                                    uint64_t key) {
  std::vector<uint8_t> entry(layout.EntryBytes(), 0);
  for (size_t b = 0; b < layout.key_bytes; ++b) {
    entry[b] = static_cast<uint8_t>(key >> (8 * b));
  }
  std::mt19937_64 rng(key * 0x9E3779B97F4A7C15ull + 1);
  for (size_t b = 0; b < layout.value_bytes; ++b) {
    entry[layout.key_bytes + b] = static_cast<uint8_t>(rng());
  }
  return entry;
}

uint64_t ReadKey(const uint8_t* bucket, size_t slot,
                 const bs::StashLayout& layout) {
  uint64_t key = 0;
  for (size_t b = 0; b < layout.key_bytes; ++b) {
    key |= uint64_t{bucket[b * bs::kBucketCapacity + slot]} << (8 * b);
  }
  return key;
}

void ExpectEntryIntact(const uint8_t* bucket, size_t slot,
                       const bs::StashLayout& layout, const char* what) {
  const uint64_t key = ReadKey(bucket, slot, layout);
  const auto reference = MakeEntryBytes(layout, key);
  std::vector<uint8_t> entry(layout.EntryBytes());
  bs::ReadEntry(bucket, slot, entry.data(), layout.EntryBytes());
  Expect(std::memcmp(entry.data(), reference.data(),
                     layout.key_bytes + layout.value_bytes) == 0,
         what);
}

struct OwnedStash {
  bs::ResidualStash stash;
  bs::Aligned64Ptr data;
  explicit OwnedStash(size_t num_buckets, const bs::StashLayout& layout) {
    data = bs::AllocateAligned64(num_buckets * layout.BucketBytes());
    stash.data = data.get();
    stash.num_buckets = num_buckets;
    stash.entry_bytes = layout.EntryBytes();
  }
};

// Collects every real key in a stash into key -> (bucket, slot).
std::unordered_map<uint64_t, int> StashKeys(const bs::ResidualStash& stash,
                                            const bs::StashLayout& layout) {
  std::unordered_map<uint64_t, int> keys;
  for (size_t b = 0; b < stash.num_buckets; ++b) {
    for (size_t slot = 0; slot < bs::kBucketCapacity; ++slot) {
      if (!((stash.masks[b] >> slot) & 1)) continue;
      keys.emplace(ReadKey(stash.Bucket(b), slot, layout),
                   static_cast<int>(b));
    }
  }
  return keys;
}

// Union of the real keys across every stash in [begin, begin + n).
std::unordered_map<uint64_t, int> StashKeysMulti(const bs::ResidualStash* begin,
                                                 size_t n,
                                                 const bs::StashLayout& layout) {
  std::unordered_map<uint64_t, int> keys;
  for (size_t s = 0; s < n; ++s) {
    for (const auto& kv : StashKeys(begin[s], layout)) keys.emplace(kv);
  }
  return keys;
}

// A zero-capacity stash is the load-0.25 contract used by the side arena: the
// residual path disappears from the kernel entirely, so a route that does not
// overflow must be byte-identical to one with a stash attached, and a route
// that does overflow must be reported instead of silently dropping entries.
void TestZeroCapacityStashContract() {
  bs::StashLayout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 4;
  layout.tag_bytes = 1;
  const size_t entry_bytes = layout.EntryBytes();
  const size_t bucket_bytes = entry_bytes * bs::kBucketCapacity;

  for (int trial = 0; trial < 64; ++trial) {
    const bool overflowing = (trial & 1) != 0;
    auto with = bs::Table::Create(2, layout.Base());
    auto without = bs::Table::Create(2, layout.Base());
    OwnedStash owned(1, layout);
    bs::ResidualStash empty;  // num_buckets == 0
    empty.entry_bytes = entry_bytes;

    std::mt19937_64 rng(4000 + trial);
    uint64_t masks[2] = {0, 0};
    uint64_t next_key = 100000;
    // Load 0.25 normally; both buckets one-directional and full to overflow.
    const int count = overflowing ? 48 : 16;
    for (int bucket = 0; bucket < 2; ++bucket) {
      std::vector<int> slots(64);
      for (int i = 0; i < 64; ++i) slots[i] = i;
      std::shuffle(slots.begin(), slots.end(), rng);
      for (int i = 0; i < count; ++i) {
        auto entry = MakeEntryBytes(layout, next_key++);
        entry[layout.TagOffset()] =
            overflowing ? 0 : static_cast<uint8_t>(rng() & 1);
        bs::WriteEntry(with.Bucket(bucket), slots[i], entry.data(),
                       entry_bytes);
        bs::WriteEntry(without.Bucket(bucket), slots[i], entry.data(),
                       entry_bytes);
        masks[bucket] |= uint64_t{1} << slots[i];
      }
    }

    uint64_t a[2] = {masks[0], masks[1]};
    uint64_t b[2] = {masks[0], masks[1]};
    const bool ok_with = bs::MergeSplitPairStash<true>(
        with.Bucket(0), with.Bucket(1), &a[0], &a[1], entry_bytes,
        layout.TagOffset(), 0, owned.stash);
    const bool ok_without = bs::MergeSplitPairStash<true>(
        without.Bucket(0), without.Bucket(1), &b[0], &b[1], entry_bytes,
        layout.TagOffset(), 0, empty);

    if (overflowing) {
      Expect(!ok_without,
             "zero-capacity stash must reject a shedding MergeSplit");
      Expect(ok_with && owned.stash.Count() > 0,
             "the sized stash should have absorbed the surplus");
    } else {
      Expect(ok_with && ok_without, "no-overflow MergeSplit failed");
      Expect(owned.stash.Count() == 0, "unexpected shed at load 0.25");
      Expect(a[0] == b[0] && a[1] == b[1],
             "zero-capacity stash changed the occupancy masks");
      Expect(std::memcmp(with.Bucket(0), without.Bucket(0), bucket_bytes) == 0 &&
                 std::memcmp(with.Bucket(1), without.Bucket(1),
                             bucket_bytes) == 0,
             "zero-capacity stash changed the routed bytes");
    }
  }
}

// Without overflow the stash variant must behave exactly like the plain
// MergeSplit and leave the stash untouched.
void TestMergeSplitStashNoOverflow() {
  bs::StashLayout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 4;
  layout.tag_bytes = 1;
  const size_t entry_bytes = layout.EntryBytes();

  auto table = bs::Table::Create(2, layout.Base());
  OwnedStash owned(1, layout);
  std::mt19937_64 rng(11);

  std::unordered_map<uint64_t, uint8_t> expected_dir;
  uint64_t masks[2] = {0, 0};
  uint64_t next_key = 5000;
  for (int bucket = 0; bucket < 2; ++bucket) {
    const int count = bucket == 0 ? 30 : 34;  // load 0.5
    std::vector<int> slots(64);
    for (int i = 0; i < 64; ++i) slots[i] = i;
    std::shuffle(slots.begin(), slots.end(), rng);
    for (int i = 0; i < count; ++i) {
      const uint64_t key = next_key++;
      const uint8_t dir = static_cast<uint8_t>(rng() & 1);
      auto entry = MakeEntryBytes(layout, key);
      entry[layout.TagOffset()] = dir;
      bs::WriteEntry(table.Bucket(bucket), slots[i], entry.data(), entry_bytes);
      masks[bucket] |= uint64_t{1} << slots[i];
      expected_dir[key] = dir;
    }
  }

  Expect(bs::MergeSplitPairStash(table.Bucket(0), table.Bucket(1), &masks[0],
                                 &masks[1], entry_bytes, layout.TagOffset(), 0,
                                 owned.stash),
         "no-overflow mergesplit failed");
  Expect(owned.stash.Count() == 0 && owned.stash.masks[0] == 0,
         "stash gained entries without overflow");

  size_t found = 0;
  for (int bucket = 0; bucket < 2; ++bucket) {
    for (int slot = 0; slot < 64; ++slot) {
      if (!((masks[bucket] >> slot) & 1)) continue;
      const uint64_t key = ReadKey(table.Bucket(bucket), slot, layout);
      auto it = expected_dir.find(key);
      Expect(it != expected_dir.end(), "unknown key after stash mergesplit");
      Expect(it->second == bucket, "entry routed to wrong direction");
      ExpectEntryIntact(table.Bucket(bucket), slot, layout,
                        "entry corrupted by stash mergesplit");
      expected_dir.erase(it);
      ++found;
    }
  }
  Expect(found == 64 && expected_dir.empty(),
         "stash mergesplit lost or duplicated entries");
}

// 96 entries all wanting direction 0: the output bucket fills to 64 and the
// remaining 32 must land in the stash, intact.
void TestMergeSplitStashOverflow() {
  bs::StashLayout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 4;
  layout.tag_bytes = 1;
  const size_t entry_bytes = layout.EntryBytes();

  auto table = bs::Table::Create(2, layout.Base());
  OwnedStash owned(1, layout);
  std::mt19937_64 rng(23);

  std::vector<uint64_t> all_keys;
  uint64_t masks[2] = {0, 0};
  uint64_t next_key = 9000;
  for (int bucket = 0; bucket < 2; ++bucket) {
    std::vector<int> slots(64);
    for (int i = 0; i < 64; ++i) slots[i] = i;
    std::shuffle(slots.begin(), slots.end(), rng);
    for (int i = 0; i < 48; ++i) {
      const uint64_t key = next_key++;
      auto entry = MakeEntryBytes(layout, key);
      entry[layout.TagOffset()] = 0;  // everyone wants direction 0
      bs::WriteEntry(table.Bucket(bucket), slots[i], entry.data(), entry_bytes);
      masks[bucket] |= uint64_t{1} << slots[i];
      all_keys.push_back(key);
    }
  }

  Expect(bs::MergeSplitPairStash(table.Bucket(0), table.Bucket(1), &masks[0],
                                 &masks[1], entry_bytes, layout.TagOffset(), 0,
                                 owned.stash),
         "overflowing mergesplit failed outright");
  Expect(masks[0] == ~uint64_t{0}, "overflowed direction is not full");
  Expect(masks[1] == 0, "direction 1 should be empty");
  Expect(owned.stash.Count() == 32,
         "stash should hold the 32 surplus entries");
  Expect(bs::Popcount64(owned.stash.masks[0]) == 32,
         "stash occupancy mask does not match its count");

  std::unordered_map<uint64_t, bool> seen;
  for (uint64_t key : all_keys) seen.emplace(key, false);
  for (int slot = 0; slot < 64; ++slot) {
    const uint64_t key = ReadKey(table.Bucket(0), slot, layout);
    auto it = seen.find(key);
    Expect(it != seen.end() && !it->second, "bucket key unknown or duplicate");
    it->second = true;
    ExpectEntryIntact(table.Bucket(0), slot, layout,
                      "bucket entry corrupted by overflow path");
  }
  for (const auto& kv : StashKeys(owned.stash, layout)) {
    auto it = seen.find(kv.first);
    Expect(it != seen.end() && !it->second, "stash key unknown or duplicate");
    it->second = true;
  }
  for (size_t slot = 0; slot < bs::kBucketCapacity; ++slot) {
    if (!((owned.stash.masks[0] >> slot) & 1)) continue;
    ExpectEntryIntact(owned.stash.Bucket(0), slot, layout,
                      "stash entry corrupted by overflow path");
  }
  for (const auto& kv : seen) {
    Expect(kv.second, "an entry disappeared during the overflow");
  }
}

// Repeated forced overflows must cascade into the second stash bucket and
// finally report failure when the stash itself is exhausted.
void TestStashCascadeAndExhaustion() {
  bs::StashLayout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 2;
  layout.tag_bytes = 1;
  const size_t entry_bytes = layout.EntryBytes();

  OwnedStash owned(2, layout);
  std::mt19937_64 rng(37);
  uint64_t next_key = 40000;
  std::unordered_map<uint64_t, bool> expected;

  auto run_overflowing_pair = [&](bool expect_ok) {
    auto table = bs::Table::Create(2, layout.Base());
    uint64_t masks[2] = {0, 0};
    std::vector<uint64_t> keys;
    for (int bucket = 0; bucket < 2; ++bucket) {
      for (int i = 0; i < 48; ++i) {
        const uint64_t key = next_key++;
        auto entry = MakeEntryBytes(layout, key);
        entry[layout.TagOffset()] = 0;
        bs::WriteEntry(table.Bucket(bucket), i, entry.data(), entry_bytes);
        masks[bucket] |= uint64_t{1} << i;
        keys.push_back(key);
      }
    }
    const bool ok = bs::MergeSplitPairStash<true>(
        table.Bucket(0), table.Bucket(1), &masks[0], &masks[1], entry_bytes,
        layout.TagOffset(), 0, owned.stash);
    Expect(ok == expect_ok, "unexpected stash-capacity outcome");
    if (ok) {
      for (int slot = 0; slot < 64; ++slot) {
        expected.emplace(ReadKey(table.Bucket(0), slot, layout), false);
      }
    }
    return ok;
  };

  // Each run sheds 32 residuals into the 128-slot stash: 4 fit, #5 must fail.
  for (int round = 0; round < 4; ++round) {
    run_overflowing_pair(true);
  }
  Expect(owned.stash.Count() == 128, "stash should be exactly full");
  Expect(bs::Popcount64(owned.stash.masks[0]) == 64 &&
             bs::Popcount64(owned.stash.masks[1]) == 64,
         "residuals did not cascade into the second stash bucket");
  run_overflowing_pair(false);

  const auto stash_keys = StashKeys(owned.stash, layout);
  Expect(stash_keys.size() == 128, "stash key count mismatch");
  for (size_t b = 0; b < 2; ++b) {
    for (size_t slot = 0; slot < bs::kBucketCapacity; ++slot) {
      if (!((owned.stash.masks[b] >> slot) & 1)) continue;
      ExpectEntryIntact(owned.stash.Bucket(b), slot, layout,
                        "cascaded stash entry corrupted");
    }
  }
}

void TestMergeBucketIntoWithStash() {
  bs::StashLayout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 4;
  layout.tag_bytes = 1;
  const size_t entry_bytes = layout.EntryBytes();

  auto table = bs::Table::Create(2, layout.Base());
  OwnedStash owned(1, layout);
  std::mt19937_64 rng(53);

  uint64_t masks[2] = {0, 0};
  uint64_t next_key = 70000;
  std::unordered_map<uint64_t, bool> expected;
  const int counts[2] = {50, 30};  // 80 total: 16 must be shed
  for (int bucket = 0; bucket < 2; ++bucket) {
    std::vector<int> slots(64);
    for (int i = 0; i < 64; ++i) slots[i] = i;
    std::shuffle(slots.begin(), slots.end(), rng);
    for (int i = 0; i < counts[bucket]; ++i) {
      const uint64_t key = next_key++;
      const auto entry = MakeEntryBytes(layout, key);
      bs::WriteEntry(table.Bucket(bucket), slots[i], entry.data(), entry_bytes);
      masks[bucket] |= uint64_t{1} << slots[i];
      expected.emplace(key, false);
    }
  }

  Expect(bs::MergeBucketIntoWithStash(table.Bucket(0), table.Bucket(1),
                                      &masks[0], &masks[1], entry_bytes,
                                      owned.stash),
         "fold failed outright");
  Expect(masks[0] == ~uint64_t{0} && masks[1] == 0,
         "fold masks are inconsistent");
  Expect(owned.stash.Count() == 16, "fold should shed 16 residuals");

  for (int slot = 0; slot < 64; ++slot) {
    const uint64_t key = ReadKey(table.Bucket(0), slot, layout);
    auto it = expected.find(key);
    Expect(it != expected.end() && !it->second, "fold key unknown/duplicate");
    it->second = true;
    ExpectEntryIntact(table.Bucket(0), slot, layout, "fold entry corrupted");
  }
  for (const auto& kv : StashKeys(owned.stash, layout)) {
    auto it = expected.find(kv.first);
    Expect(it != expected.end() && !it->second,
           "fold stash key unknown/duplicate");
    it->second = true;
  }
  for (const auto& kv : expected) {
    Expect(kv.second, "fold lost an entry");
  }
}

void TestScatterDenseBucket() {
  bs::StashLayout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 3;
  layout.tag_bytes = 2;
  const size_t entry_bytes = layout.EntryBytes();
  auto table = bs::Table::Create(4, layout.Base());
  uint64_t source_mask = 0;
  std::mt19937_64 rng(71);
  for (int slot = 0; slot < 64; ++slot) {
    if (rng() & 1) {
      const auto entry = MakeEntryBytes(layout, 90000 + slot);
      bs::WriteEntry(table.Bucket(0), slot, entry.data(), entry_bytes);
      source_mask |= uint64_t{1} << slot;
    }
  }
  const uint64_t original_mask = source_mask;
  // In place: destination bucket 0 aliases the source.
  bs::ScatterDenseBucket(table.Bucket(0), source_mask, table.Bucket(0),
                         table.masks.get(), 16, entry_bytes, entry_bytes);
  size_t found = 0;
  for (int b = 0; b < 4; ++b) {
    Expect((table.masks[b] & ~bs::LowMask64(16)) == 0,
           "scatter mask exceeds per-bucket allotment");
    for (int slot = 0; slot < 16; ++slot) {
      const int source_slot = b * 16 + slot;
      const bool real = (original_mask >> source_slot) & 1;
      Expect(((table.masks[b] >> slot) & 1) == static_cast<uint64_t>(real),
             "scatter mask slot mismatch");
      if (!real) continue;
      const uint64_t key = ReadKey(table.Bucket(b), slot, layout);
      Expect(key == 90000u + source_slot, "scatter moved a key incorrectly");
      ExpectEntryIntact(table.Bucket(b), slot, layout,
                        "scatter corrupted an entry");
      ++found;
    }
  }
  Expect(found == static_cast<size_t>(bs::Popcount64(original_mask)),
         "scatter lost entries");
}

// The fused two-level quad (MergeSplitQuadStash, which both butterfly drivers
// use) must be byte-identical to running the same MergeSplits one level at a
// time.  That is the claim that lets the quad drop the intermediate maskz:
// every byte reaching a real output slot came from a slot that was real on
// entry, so the final maskz zeroes exactly what the intermediate one would
// have.  Retired tag lines are excluded from the comparison -- level b stops
// routing tag byte b/8, and the quad retires the pair's two bytes together
// while the unfused loop retires them one level apart, so those dead lines
// legitimately hold different stale bytes.  Residual slot order inside a
// level stash may differ too (a stash is a set).
// group_levels 0 selects the cache-oblivious recursion instead of the flat
// grouped tiling; the two schedule quads at different absolute bit-levels, so
// both are needed to reach a quad that starts on bit 7 mod 8 (the one case
// where the pair's two tag bits live on different byte lines).
void TestQuadMatchesUnfused(size_t num_buckets, size_t fill,
                            unsigned route_levels, size_t stash_buckets,
                            unsigned group_levels, uint64_t seed) {
  bs::StashLayout layout;
  const bs::Layout base = layout.Base();
  const size_t entry_bytes = base.EntryBytes();
  const size_t bucket_bytes = base.BucketBytes();

  auto fused = bs::Table::Create(num_buckets, base);
  std::mt19937_64 rng(seed);
  for (size_t b = 0; b < num_buckets; ++b) {
    for (size_t i = 0; i < fill; ++i) {
      const auto entry = MakeEntryBytes(layout, rng());
      bs::WriteEntry(fused.Bucket(b), i, entry.data(), entry_bytes);
      fused.masks[b] |= uint64_t{1} << i;
    }
  }
  bs::ComputeRoutingTags(fused, 0xF00D ^ seed, 0xBEEF ^ seed);

  auto plain = bs::Table::Create(num_buckets, base);
  std::memcpy(plain.data.get(), fused.data.get(), num_buckets * bucket_bytes);
  std::memcpy(plain.masks.get(), fused.masks.get(),
              num_buckets * sizeof(uint64_t));

  OwnedLevelStashes fused_stash(route_levels, stash_buckets, layout);
  OwnedLevelStashes plain_stash(route_levels, stash_buckets, layout);

  Expect(group_levels == 0
             ? bs::ButterflyRouteStashCacheOblivious(bs::View(fused),
                                                     route_levels,
                                                     fused_stash.ptr())
             : bs::ButterflyRouteStash(bs::View(fused), route_levels,
                                       fused_stash.ptr(), group_levels),
         "fused route failed");

  // Reference: one level at a time, same MergeSplit set, same pruning.
  for (unsigned lev = 0; lev < route_levels; ++lev) {
    const size_t half = size_t{1} << lev;
    const size_t lines = base.RoutedLines(lev);
    const size_t tag_line = base.TagLine(lev);
    for (size_t i = 0; i < num_buckets; ++i) {
      if (i & half) continue;
      Expect(bs::MergeSplitPairStash(
                 plain.Bucket(i), plain.Bucket(i | half), &plain.masks[i],
                 &plain.masks[i | half], lines, tag_line, lev,
                 plain_stash.slots[lev]),
             "unfused reference route failed");
    }
  }

  size_t placed = 0;
  for (size_t b = 0; b < num_buckets; ++b) {
    placed += bs::Popcount64(fused.masks[b]);
  }
  Expect(placed + fused_stash.total_count() == num_buckets * fill,
         "the stash overflowed: pick a deeper stash for this fill");

  const size_t live_lines = base.RoutedLines(route_levels - 1);
  for (size_t b = 0; b < num_buckets; ++b) {
    Expect(std::memcmp(fused.Bucket(b), plain.Bucket(b),
                       live_lines * bs::kBucketCapacity) == 0,
           "fused quad produced different bucket bytes");
  }
  Expect(std::memcmp(fused.masks.get(), plain.masks.get(),
                     num_buckets * sizeof(uint64_t)) == 0,
         "fused quad produced different masks");
  Expect(fused_stash.total_count() == plain_stash.total_count(),
         "fused quad shed a different residual count");
  const auto a = StashKeysMulti(fused_stash.ptr(), route_levels, layout);
  const auto b = StashKeysMulti(plain_stash.ptr(), route_levels, layout);
  Expect(a.size() == b.size(), "fused quad residual key set sizes differ");
  for (const auto& kv : a) {
    Expect(b.count(kv.first) == 1, "fused quad residual key sets differ");
  }
}

// MergeSplitQuadStash's unfused arm: two MergeSplitPairStash passes over the
// same four buckets, taken when the two levels' stashes have different depths.
// Every DEPTH is fused (see kMaxQuadStashBuckets), so a depth mismatch is
// the only way to reach this path -- and it is the path the fused kernel is
// defined against, so it must keep working even though the hierarchy always
// sizes the two stashes alike.
//
// `MergeSplitQuadStash` on a (deep, shallow) stash pair must equal the same
// two levels run one at a time, which is what the fallback is.  The stashes
// are deliberately given different bucket counts; the shallow one is sized to
// hold the level's whole shed so the comparison is not about capacity.
void TestQuadUnfusedFallback(size_t num_buckets, size_t fill,
                             unsigned route_levels, uint64_t seed) {
  Expect(route_levels >= 2 && (route_levels % 2) == 0,
         "the fallback test routes whole quads");
  bs::StashLayout layout;
  const bs::Layout base = layout.Base();
  const size_t entry_bytes = base.EntryBytes();
  const size_t bucket_bytes = base.BucketBytes();

  auto quad = bs::Table::Create(num_buckets, base);
  std::mt19937_64 rng(seed);
  for (size_t b = 0; b < num_buckets; ++b) {
    for (size_t i = 0; i < fill; ++i) {
      const auto entry = MakeEntryBytes(layout, rng());
      bs::WriteEntry(quad.Bucket(b), i, entry.data(), entry_bytes);
      quad.masks[b] |= uint64_t{1} << i;
    }
  }
  bs::ComputeRoutingTags(quad, 0xD15EA5E ^ seed, 0xC0DE ^ seed);

  auto plain = bs::Table::Create(num_buckets, base);
  std::memcpy(plain.data.get(), quad.data.get(), num_buckets * bucket_bytes);
  std::memcpy(plain.masks.get(), quad.masks.get(),
              num_buckets * sizeof(uint64_t));

  // Alternating depths, so every quad sees a mismatched (lo, hi) pair.
  std::vector<std::unique_ptr<OwnedStash>> quad_stash, plain_stash;
  for (unsigned lev = 0; lev < route_levels; ++lev) {
    const size_t depth = (lev % 2) == 0 ? 4 : 2;
    quad_stash.push_back(std::make_unique<OwnedStash>(depth, layout));
    plain_stash.push_back(std::make_unique<OwnedStash>(depth, layout));
  }

  for (unsigned bit = 0; bit + 1 < route_levels; bit += 2) {
    const size_t step = size_t{1} << bit;
    for (size_t i = 0; i < num_buckets; ++i) {
      if (i & (3 * step)) continue;
      Expect(bs::MergeSplitQuadStash(quad.Bucket(i), &quad.masks[i],
                                     bucket_bytes, base, bit,
                                     quad_stash[bit]->stash,
                                     quad_stash[bit + 1]->stash),
             "mismatched-depth quad failed");
    }
  }

  for (unsigned lev = 0; lev < route_levels; ++lev) {
    const size_t half = size_t{1} << lev;
    const size_t lines = base.RoutedLines(lev);
    const size_t tag_line = base.TagLine(lev);
    for (size_t i = 0; i < num_buckets; ++i) {
      if (i & half) continue;
      Expect(bs::MergeSplitPairStash(
                 plain.Bucket(i), plain.Bucket(i | half), &plain.masks[i],
                 &plain.masks[i | half], lines, tag_line, lev,
                 plain_stash[lev]->stash),
             "unfused reference route failed");
    }
  }

  const size_t live_lines = base.RoutedLines(route_levels - 1);
  for (size_t b = 0; b < num_buckets; ++b) {
    Expect(std::memcmp(quad.Bucket(b), plain.Bucket(b),
                       live_lines * bs::kBucketCapacity) == 0,
           "unfused fallback produced different bucket bytes");
  }
  Expect(std::memcmp(quad.masks.get(), plain.masks.get(),
                     num_buckets * sizeof(uint64_t)) == 0,
         "unfused fallback produced different masks");
  for (unsigned lev = 0; lev < route_levels; ++lev) {
    const auto a = StashKeys(quad_stash[lev]->stash, layout);
    const auto b = StashKeys(plain_stash[lev]->stash, layout);
    Expect(a.size() == b.size(),
           "unfused fallback shed a different residual count");
    for (const auto& kv : a) {
      Expect(b.count(kv.first) == 1,
             "unfused fallback residual key sets differ");
    }
  }
}

// The cache-oblivious recursive order must produce byte-identical buckets
// and masks to the flat grouped order (every MergeSplit's dependency cone is
// the same, and compress zero-fills beyond the packed count so stale bytes
// never propagate), and shed the same residual key set (stash slot order may
// differ).
void TestRecursiveMatchesGrouped(size_t num_buckets, size_t fill,
                                 unsigned route_levels, uint64_t seed) {
  bs::StashLayout layout;
  auto grouped = bs::Table::Create(num_buckets, layout.Base());
  const size_t entry_bytes = layout.EntryBytes();

  std::mt19937_64 rng(seed);
  for (size_t b = 0; b < num_buckets; ++b) {
    for (size_t i = 0; i < fill; ++i) {
      const auto entry = MakeEntryBytes(layout, rng());
      bs::WriteEntry(grouped.Bucket(b), i, entry.data(), entry_bytes);
      grouped.masks[b] |= uint64_t{1} << i;
    }
  }
  bs::ComputeRoutingTags(grouped, 0x5150 ^ seed, 0x1234 ^ seed);

  auto recursive = bs::Table::Create(num_buckets, layout.Base());
  std::memcpy(recursive.data.get(), grouped.data.get(),
              num_buckets * layout.BucketBytes());
  std::memcpy(recursive.masks.get(), grouped.masks.get(),
              num_buckets * sizeof(uint64_t));

  OwnedLevelStashes grouped_stash(route_levels, 4, layout);
  OwnedLevelStashes recursive_stash(route_levels, 4, layout);
  Expect(bs::ButterflyRouteStash(bs::View(grouped), route_levels,
                                 grouped_stash.ptr(), 3),
         "grouped route failed");
  Expect(bs::ButterflyRouteStashCacheOblivious(bs::View(recursive),
                                               route_levels,
                                               recursive_stash.ptr()),
         "recursive route failed");

  Expect(std::memcmp(grouped.data.get(), recursive.data.get(),
                     num_buckets * layout.BucketBytes()) == 0,
         "recursive route produced different bucket bytes");
  Expect(std::memcmp(grouped.masks.get(), recursive.masks.get(),
                     num_buckets * sizeof(uint64_t)) == 0,
         "recursive route produced different masks");
  Expect(grouped_stash.total_count() == recursive_stash.total_count(),
         "recursive route shed a different residual count");
  const auto a = StashKeysMulti(grouped_stash.ptr(), route_levels, layout);
  const auto b = StashKeysMulti(recursive_stash.ptr(), route_levels, layout);
  Expect(a.size() == b.size(), "residual key set sizes differ");
  for (const auto& kv : a) {
    Expect(b.count(kv.first) == 1, "residual key sets differ");
  }
}

// End-to-end butterfly at deliberate overload (fill real entries per bucket,
// well above the design load of 32): residuals are frequent and every input
// key must end up either in its tag-addressed final bucket or in the stash,
// byte-intact.  The seeds are fixed, so the residual counts are
// deterministic.
void TestOverloadedButterflyConservation(size_t num_buckets, size_t fill,
                                         uint64_t seed) {
  bs::StashLayout layout;  // default 8/16/4 plus meta
  auto table = bs::Table::Create(num_buckets, layout.Base());
  const unsigned levels = bs::Log2Exact(num_buckets);
  OwnedLevelStashes owned(levels, 4, layout);
  const size_t entry_bytes = layout.EntryBytes();

  std::mt19937_64 rng(seed);
  std::unordered_map<uint64_t, bool> keys_seen;
  for (size_t b = 0; b < num_buckets; ++b) {
    for (size_t i = 0; i < fill; ++i) {
      uint64_t key;
      do {
        key = rng();
      } while (keys_seen.count(key));
      keys_seen.emplace(key, false);
      const auto entry = MakeEntryBytes(layout, key);
      bs::WriteEntry(table.Bucket(b), i, entry.data(), entry_bytes);
      table.masks[b] |= uint64_t{1} << i;
    }
  }

  const uint64_t nonce_lo = 0xABCD ^ seed;
  const uint64_t nonce_hi = 0x7788 ^ (seed << 8);
  bs::TableView view = bs::View(table);
  bs::ComputeRoutingTags(view, nonce_lo, nonce_hi);
  Expect(bs::ButterflyRouteStash(view, levels, owned.ptr(), 3),
         "overloaded butterfly exhausted the per-level stashes");
  Expect(owned.total_count() > 0,
         "overload test expected at least one residual");

  size_t placed = 0;
  for (size_t b = 0; b < num_buckets; ++b) {
    for (size_t slot = 0; slot < bs::kBucketCapacity; ++slot) {
      if (!((table.masks[b] >> slot) & 1)) continue;
      const uint64_t key = ReadKey(table.Bucket(b), slot, layout);
      auto it = keys_seen.find(key);
      Expect(it != keys_seen.end() && !it->second,
             "unknown or duplicated key after overloaded butterfly");
      it->second = true;
      ExpectEntryIntact(table.Bucket(b), slot, layout,
                        "entry corrupted by overloaded butterfly");
      const uint64_t tag = microram::crypto::AesCtrTagU64WordsHost(
          nonce_lo, nonce_hi, key);
      Expect((tag & (num_buckets - 1)) == b,
             "non-residual entry landed in the wrong bucket");
      ++placed;
    }
  }
  size_t shed = 0;
  for (const auto& stash : owned.slots) {
    for (size_t b = 0; b < stash.num_buckets; ++b) {
      for (size_t slot = 0; slot < bs::kBucketCapacity; ++slot) {
        if (!((stash.masks[b] >> slot) & 1)) continue;
        const uint64_t key = ReadKey(stash.Bucket(b), slot, layout);
        auto it = keys_seen.find(key);
        Expect(it != keys_seen.end() && !it->second,
               "unknown or duplicated key in the stash");
        it->second = true;
        ExpectEntryIntact(stash.Bucket(b), slot, layout,
                          "stash entry corrupted by overloaded butterfly");
        ++shed;
      }
    }
  }
  Expect(placed + shed == keys_seen.size(),
         "overloaded butterfly lost entries");
  Expect(shed == owned.total_count(),
         "stash count disagrees with its masks");
  std::printf("  overload %zu buckets: %zu placed, %zu shed\n", num_buckets,
              placed, shed);
}

// ---------------------------------------------------------------------------
// Mixed-radix routing
// ---------------------------------------------------------------------------
//
// A merge at digit j = r * 2^e with r odd routes its e binary levels with the
// ordinary MergeSplit and then one radix-r pass, whose MergeSplit sends each
// entry of r buckets to the bucket its stored digit names (the digit line of
// the tag).  These check that kernel directly on r = 3 buckets.

// A non-power-of-two table of num_buckets byte-sliced buckets.
struct OwnedTable {
  bs::StashLayout layout;
  size_t num_buckets;
  bs::Aligned64Ptr data;
  std::vector<uint64_t> masks;
  OwnedTable(size_t buckets, const bs::StashLayout& l)
      : layout(l), num_buckets(buckets), masks(buckets, 0) {
    data = bs::AllocateAligned64(buckets * layout.BucketBytes());
  }
  uint8_t* Bucket(size_t b) { return data.get() + b * layout.BucketBytes(); }
  bs::TableView View() {
    return bs::TableView{layout.Base(), num_buckets, data.get(),
                         masks.data()};
  }
};

// Direct radix-r MergeSplit: digits assigned round-robin (no overflow) must
// route every entry to its direction bucket, intact, with an empty stash.
void TestRadixMergeSplitNoOverflow() {
  bs::StashLayout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 4;
  layout.tag_bytes = 2;
  const size_t entry_bytes = layout.EntryBytes();
  const unsigned r = 3;
  OwnedTable table(r, layout);
  OwnedStash owned(1, layout);
  std::mt19937_64 rng(101);

  std::unordered_map<uint64_t, unsigned> expected_dir;
  uint64_t next_key = 300000;
  for (unsigned bkt = 0; bkt < r; ++bkt) {
    std::vector<int> slots(64);
    for (int i = 0; i < 64; ++i) slots[i] = i;
    std::shuffle(slots.begin(), slots.end(), rng);
    for (int i = 0; i < 42; ++i) {
      const uint64_t key = next_key++;
      const unsigned dir = static_cast<unsigned>((bkt + i) % r);
      auto entry = MakeEntryBytes(layout, key);
      entry[layout.Base().DigitLine()] = static_cast<uint8_t>(dir);
      bs::WriteEntry(table.Bucket(bkt), slots[i], entry.data(), entry_bytes);
      table.masks[bkt] |= uint64_t{1} << slots[i];
      expected_dir.emplace(key, dir);
    }
  }

  uint8_t* buckets[3] = {table.Bucket(0), table.Bucket(1), table.Bucket(2)};
  uint64_t* masks[3] = {&table.masks[0], &table.masks[1], &table.masks[2]};
  const size_t digit_line = layout.Base().DigitLine();
  Expect(bs::MergeSplitRadixStash(buckets, masks, r, entry_bytes, digit_line,
                                  layout.Base().digit_bits, owned.stash),
         "radix mergesplit failed without overflow");
  Expect(owned.stash.Count() == 0,
         "radix mergesplit shed without overflow");

  size_t found = 0;
  for (unsigned q = 0; q < r; ++q) {
    for (int slot = 0; slot < 64; ++slot) {
      if (!((table.masks[q] >> slot) & 1)) continue;
      const uint64_t key = ReadKey(table.Bucket(q), slot, layout);
      auto it = expected_dir.find(key);
      Expect(it != expected_dir.end(), "unknown key after radix mergesplit");
      Expect(it->second == q, "radix entry routed to wrong direction");
      ExpectEntryIntact(table.Bucket(q), slot, layout,
                        "entry corrupted by radix mergesplit");
      expected_dir.erase(it);
      ++found;
    }
  }
  Expect(found == 3 * 42 && expected_dir.empty(),
         "radix mergesplit lost or duplicated entries");
}

// 3 x 30 entries all wanting direction 0: 64 placed, 26 shed, everything
// conserved; then the >64-shed staging cap must report failure untouched.
void TestRadixMergeSplitOverflowAndCap() {
  bs::StashLayout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 4;
  layout.tag_bytes = 2;
  const size_t entry_bytes = layout.EntryBytes();
  const size_t digit_line = layout.Base().DigitLine();
  const unsigned r = 3;

  {
    OwnedTable table(r, layout);
    OwnedStash owned(1, layout);
    std::unordered_map<uint64_t, bool> seen;
    uint64_t next_key = 400000;
    for (unsigned bkt = 0; bkt < r; ++bkt) {
      for (int i = 0; i < 30; ++i) {
        const uint64_t key = next_key++;
        auto entry = MakeEntryBytes(layout, key);
        entry[layout.Base().DigitLine()] = 0;
        bs::WriteEntry(table.Bucket(bkt), i, entry.data(), entry_bytes);
        table.masks[bkt] |= uint64_t{1} << i;
        seen.emplace(key, false);
      }
    }
    uint8_t* buckets[3] = {table.Bucket(0), table.Bucket(1), table.Bucket(2)};
    uint64_t* masks[3] = {&table.masks[0], &table.masks[1], &table.masks[2]};
    Expect(bs::MergeSplitRadixStash(buckets, masks, r, entry_bytes,
                                    digit_line, layout.Base().digit_bits,
                                    owned.stash),
           "overflowing radix mergesplit failed outright");
    Expect(table.masks[0] == ~uint64_t{0}, "direction 0 should be full");
    Expect(table.masks[1] == 0 && table.masks[2] == 0,
           "directions 1/2 should be empty");
    Expect(owned.stash.Count() == 26, "expected 26 shed entries");
    for (int slot = 0; slot < 64; ++slot) {
      const uint64_t key = ReadKey(table.Bucket(0), slot, layout);
      auto it = seen.find(key);
      Expect(it != seen.end() && !it->second, "radix overflow key wrong");
      it->second = true;
      ExpectEntryIntact(table.Bucket(0), slot, layout,
                        "radix overflow corrupted a placed entry");
    }
    for (const auto& kv : StashKeys(owned.stash, layout)) {
      auto it = seen.find(kv.first);
      Expect(it != seen.end() && !it->second, "radix stash key wrong");
      it->second = true;
    }
    for (const auto& kv : seen) {
      Expect(kv.second, "radix overflow lost an entry");
    }
  }

  // A tuple may shed more than 64 entries (each source's sheds are permuted
  // straight into the stash buckets); only the aggregate stash capacity is a
  // failure.  3 x 64 entries all in direction 0 shed 128: a four-bucket stash
  // takes them all, a one-bucket stash reports overflow and is left untouched.
  for (const size_t stash_buckets : {size_t{4}, size_t{1}}) {
    OwnedTable table(r, layout);
    OwnedStash owned(stash_buckets, layout);
    std::unordered_map<uint64_t, bool> seen;
    uint64_t next_key = 500000;
    for (unsigned bkt = 0; bkt < r; ++bkt) {
      for (int i = 0; i < 64; ++i) {
        seen[next_key] = false;
        auto entry = MakeEntryBytes(layout, next_key++);
        entry[layout.Base().DigitLine()] = 0;
        bs::WriteEntry(table.Bucket(bkt), i, entry.data(), entry_bytes);
      }
      table.masks[bkt] = ~uint64_t{0};
    }
    uint8_t* buckets[3] = {table.Bucket(0), table.Bucket(1), table.Bucket(2)};
    uint64_t* masks[3] = {&table.masks[0], &table.masks[1], &table.masks[2]};
    const bool ok = bs::MergeSplitRadixStash<true>(
        buckets, masks, r, entry_bytes, digit_line, layout.Base().digit_bits,
        owned.stash);
    if (stash_buckets == 1) {
      Expect(!ok, "a shed beyond the stash capacity did not report failure");
      Expect(owned.stash.Count() == 0, "failed mergesplit touched the stash");
      continue;
    }
    Expect(ok, "a 128-entry shed into a 256-slot stash was refused");
    Expect(owned.stash.Count() == 128, "expected 128 shed entries");
    Expect(table.masks[0] == ~uint64_t{0} && table.masks[1] == 0 &&
               table.masks[2] == 0,
           "direction 0 should be full and the others empty");
    for (int slot = 0; slot < 64; ++slot) {
      auto it = seen.find(ReadKey(table.Bucket(0), slot, layout));
      Expect(it != seen.end() && !it->second, "wide shed placed a wrong key");
      it->second = true;
    }
    for (const auto& kv : StashKeys(owned.stash, layout)) {
      auto it = seen.find(kv.first);
      Expect(it != seen.end() && !it->second, "wide shed stashed a wrong key");
      it->second = true;
    }
    for (const auto& kv : seen) Expect(kv.second, "wide shed lost an entry");
  }
}

}  // namespace

int main() {
  TestZeroCapacityStashContract();
  TestMergeSplitStashNoOverflow();
  TestMergeSplitStashOverflow();
  TestStashCascadeAndExhaustion();
  TestMergeBucketIntoWithStash();
  TestScatterDenseBucket();
  TestOverloadedButterflyConservation(16, 54, 1);
  TestOverloadedButterflyConservation(64, 52, 2);
  // Fused quad vs one level at a time.  route_levels 8 and 9 cross a tag byte
  // boundary (bit 7), which is where the quad's pruning and the unfused
  // loop's diverge on dead lines and where a quad spans two tag lines.
  TestQuadMatchesUnfused(64, 32, 6, 1, 6, 20);     // design load, even levels
  TestQuadMatchesUnfused(64, 52, 6, 2, 6, 21);     // overloaded, 2-bucket stash
  TestQuadMatchesUnfused(128, 50, 5, 1, 6, 22);    // odd level count
  TestQuadMatchesUnfused(256, 50, 8, 1, 6, 23);    // retires a whole tag byte
  TestQuadMatchesUnfused(256, 50, 8, 4, 6, 24);    // deep stash, quad and pair
  TestQuadMatchesUnfused(1024, 32, 10, 4, 5, 25);  // group 5: quad on bit 7
  TestQuadMatchesUnfused(1024, 32, 10, 4, 0, 26);  // recursion: quad on bit 7
  TestQuadMatchesUnfused(1024, 44, 10, 8, 0, 27);  // recursion, overloaded
  // Every stash depth the residual schedule can produce gets its own kernel
  // instantiation of BOTH the quad and the pair, so every depth needs its own
  // comparison against the level-at-a-time reference.  The schedule reaches 3
  // at ~2^30 entries and 8 at ~2^34, which is exactly why they need these
  // direct checks: they are unreachable at any tested ORAM scale.
  for (size_t depth = 1; depth <= bs::kMaxResidualStashBuckets; ++depth) {
    TestQuadMatchesUnfused(256, 50, 8, depth, 6,
                           1200 + static_cast<uint64_t>(depth));
    TestQuadMatchesUnfused(256, 50, 8, depth, 0,
                           1300 + static_cast<uint64_t>(depth));
  }
  // The unfused two-pass path is not reachable by depth -- every depth is
  // fused -- so the mismatched-depth arm is the only thing that reaches it,
  // and it is what this checks.
  TestQuadUnfusedFallback(64, 52, 6, 24);
  TestQuadUnfusedFallback(256, 50, 8, 25);
  TestRecursiveMatchesGrouped(64, 32, 6, 3);    // full route, design load
  TestRecursiveMatchesGrouped(64, 52, 6, 4);    // overloaded, residuals
  TestRecursiveMatchesGrouped(256, 50, 8, 5);   // deeper recursion
  TestRecursiveMatchesGrouped(128, 40, 5, 6);   // partial route (two blocks)
  TestRadixMergeSplitNoOverflow();
  TestRadixMergeSplitOverflowAndCap();
  std::puts("cpu_byteslice_stash_rebuild_test passed");
  return 0;
}
