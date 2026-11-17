// Level one's direct B build (src/oram/rebuild/cpu_byteslice_dense_select.hpp),
// against a scalar reference.  When level one of the hierarchy is rebuilt, the
// deduplicated dense PREFIX (the online stash buckets being flushed, with
// per-lane winner masks marking the freshest copy of each key) goes straight
// into a table B of U buckets, with no butterfly: every entry's B HOME is the
// low log2(U) bits of its routing tag, a full home's excess drains into a
// residual stash (the TIER), and the drain is the build's only capacity check.
//
// THE CLAIM.  For a deduplicated prefix (winner masks), every B home h takes
// the first min(X_h, 64) winners whose home is h, in (prefix bucket, lane)
// order, into lanes 0.. of B[h]; the rest stay in the remaining masks and
// drain, in (prefix bucket, lane) order, into the tier.  Main and tier
// partition the winners, the tier holds exactly sum_h (X_h - 64)_+, and the
// drain fails exactly when that exceeds the tier.  Bytes are compared lane
// for lane, including the zeros of unoccupied payload lanes, at random cuts
// of the home range (a paused build is the same build).
//
// The homes are recomputed independently: ComputeRoutingTags over a copy of
// the prefix, under the same nonce and instance key, low log2(U) bits.

#include <immintrin.h>

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <random>
#include <set>
#include <string>
#include <vector>

#include "src/crypto/hash_primitives.hpp"
#include "src/oram/rebuild/cpu_byteslice_dense_select.hpp"
#include "src/oram/rebuild/cpu_byteslice_rebuild.hpp"
#include "tests/oram/cpu_byteslice_level_arena_test_support.hpp"

namespace {

namespace bs = microram::byteslice;
namespace ts = microram::byteslice::test_support;

int failures = 0;

void Expect(bool value, const std::string& message) {
  if (!value) {
    std::fprintf(stderr, "test failed: %s\n", message.c_str());
    ++failures;
  }
}

struct Shape {
  size_t sources;      // M = r0 s
  unsigned home_bits;  // log2 U
  size_t key_bytes;
  size_t value_bytes;
};

std::string Name(const Shape& s) {
  return "M=" + std::to_string(s.sources) + " U=" +
         std::to_string(size_t{1} << s.home_bits) + " key " +
         std::to_string(s.key_bytes) + " value " +
         std::to_string(s.value_bytes);
}

bs::Layout LayoutOf(const Shape& s) {
  bs::Layout layout;
  layout.key_bytes = s.key_bytes;
  layout.value_bytes = s.value_bytes;
  layout.tag_bytes = 4;
  return layout;
}

// The independent home of every lane, dummies included.
std::vector<uint32_t> ReferenceHomes(const bs::Table& prefix,
                                     const bs::Layout& layout,
                                     unsigned home_bits,
                                     const bs::RebuildNonce& nonce,
                                     const bs::AesTagKeys& keys) {
  bs::Table copy = ts::ZeroedTable(prefix.num_buckets, layout);
  std::memcpy(copy.data.get(), prefix.data.get(),
              prefix.num_buckets * layout.BucketBytes());
  for (size_t b = 0; b < prefix.num_buckets; ++b) copy.masks[b] = ~uint64_t{0};
  bs::TableView view = bs::View(copy);
  bs::ComputeRoutingTags(view, nonce.real_lo, nonce.real_hi,
                         bs::RoutingIndexMap{}, home_bits, keys);
  std::vector<uint32_t> homes;
  for (size_t b = 0; b < prefix.num_buckets; ++b) {
    for (size_t lane = 0; lane < bs::kBucketCapacity; ++lane) {
      homes.push_back(static_cast<uint32_t>(
          ts::SlotTagBitsOf(layout, copy.Bucket(b), lane, home_bits)));
    }
  }
  return homes;
}

struct Built {
  bs::Table main;
  std::vector<uint64_t> remaining;
  bs::Aligned64Ptr tier_storage;
  bs::ResidualStash tier;
  bool drained = false;
};

// The kernels, with the home range cut at random points.
Built RunKernels(const bs::Table& prefix, const std::vector<uint64_t>& winners,
                 const bs::Layout& layout, unsigned home_bits,
                 const bs::RebuildNonce& nonce, const bs::AesTagKeys& keys,
                 size_t tier_buckets, std::mt19937_64* rng,
                 std::vector<uint8_t>* homes_out) {
  const size_t m = prefix.num_buckets;
  const size_t u = size_t{1} << home_bits;
  Built out;
  out.main = ts::ZeroedTable(u, layout);
  // Stale bytes and masks: the build must write every payload line and mask.
  std::memset(out.main.data.get(), 0xA5, u * layout.BucketBytes());
  for (size_t h = 0; h < u; ++h) out.main.masks[h] = 0x5A5A5A5A5A5A5A5Aull;
  out.remaining = winners;
  bs::TableView source{layout, m, prefix.data.get(), out.remaining.data()};
  const size_t lines = bs::DenseHomeLines(home_bits);
  bs::Aligned64Ptr homes = bs::AllocateAligned64(m * lines * bs::kBucketCapacity);
  // Homes in two pieces.
  const size_t cut = (*rng)() % (m + 1);
  bs::ComputeDenseHomesRange(source, homes.get(), home_bits, nonce.real_lo,
                             nonce.real_hi, keys, 0, cut);
  bs::ComputeDenseHomesRange(source, homes.get(), home_bits, nonce.real_lo,
                             nonce.real_hi, keys, cut, m);
  homes_out->assign(homes.get(), homes.get() + m * lines * bs::kBucketCapacity);
  bs::TableView dst = bs::View(out.main);
  for (size_t at = 0; at < u;) {
    const size_t stop = std::min(u, at + 1 + (*rng)() % 7);
    bs::SelectDenseHomesRange(source, homes.get(), home_bits, dst, at, stop);
    at = stop;
  }
  out.tier_storage =
      bs::AllocateAligned64(tier_buckets * layout.BucketBytes());
  std::memset(out.tier_storage.get(), 0, tier_buckets * layout.BucketBytes());
  out.tier.data = out.tier_storage.get();
  out.tier.num_buckets = tier_buckets;
  out.tier.entry_bytes = layout.EntryBytes();
  const size_t dcut = (*rng)() % (m + 1);
  out.drained = bs::DrainDenseRemainderRange<true>(source, out.tier, 0, dcut) &&
                bs::DrainDenseRemainderRange<true>(source, out.tier, dcut, m);
  return out;
}

// One (bucket, lane) of the prefix.
struct Ref {
  size_t bucket;
  size_t lane;
};

void CheckAgainstReference(const Shape& shape, const bs::Table& prefix,
                           const std::vector<uint64_t>& winners,
                           const bs::RebuildNonce& nonce,
                           const bs::AesTagKeys& keys, size_t tier_buckets,
                           std::mt19937_64* rng, const std::string& what) {
  const bs::Layout layout = LayoutOf(shape);
  const size_t m = prefix.num_buckets;
  const size_t u = size_t{1} << shape.home_bits;
  const size_t payload = layout.PayloadLines();
  std::vector<uint8_t> homes;
  Built got = RunKernels(prefix, winners, layout, shape.home_bits, nonce, keys,
                         tier_buckets, rng, &homes);
  const std::vector<uint32_t> want_homes =
      ReferenceHomes(prefix, layout, shape.home_bits, nonce, keys);
  const size_t lines = bs::DenseHomeLines(shape.home_bits);
  size_t wrong_homes = 0;
  for (size_t b = 0; b < m; ++b) {
    for (size_t lane = 0; lane < bs::kBucketCapacity; ++lane) {
      uint32_t home = 0;
      for (size_t j = 0; j < lines; ++j) {
        home |= uint32_t{homes[(b * lines + j) * bs::kBucketCapacity + lane]}
                << (8 * j);
      }
      wrong_homes += home != want_homes[b * bs::kBucketCapacity + lane];
    }
  }
  Expect(wrong_homes == 0, what + ": " + std::to_string(wrong_homes) +
                               " cached homes differ from the key's");

  // The reference selection and drain.
  std::vector<std::vector<Ref>> per_home(u);
  for (size_t b = 0; b < m; ++b) {
    for (size_t lane = 0; lane < bs::kBucketCapacity; ++lane) {
      if ((winners[b] >> lane) & 1) {
        per_home[want_homes[b * bs::kBucketCapacity + lane]].push_back(
            {b, lane});
      }
    }
  }
  std::vector<uint64_t> want_remaining = winners;
  size_t excess = 0;
  size_t main_mismatch = 0;
  for (size_t h = 0; h < u; ++h) {
    const size_t take = std::min(per_home[h].size(), bs::kBucketCapacity);
    excess += per_home[h].size() - take;
    const uint64_t want_mask = bs::LowMask64(static_cast<unsigned>(take));
    main_mismatch += got.main.masks[h] != want_mask;
    for (size_t lane = 0; lane < bs::kBucketCapacity; ++lane) {
      for (size_t line = 0; line < payload; ++line) {
        uint8_t want = 0;
        if (lane < take) {
          const Ref& r = per_home[h][lane];
          want = prefix.Bucket(r.bucket)[line * bs::kBucketCapacity + r.lane];
        }
        main_mismatch +=
            got.main.Bucket(h)[line * bs::kBucketCapacity + lane] != want;
      }
    }
    for (size_t i = 0; i < take; ++i) {
      want_remaining[per_home[h][i].bucket] &=
          ~(uint64_t{1} << per_home[h][i].lane);
    }
  }
  Expect(main_mismatch == 0, what + ": " + std::to_string(main_mismatch) +
                                 " B main masks or payload bytes differ");
  Expect(got.remaining == want_remaining,
         what + ": the remaining masks are not the rejected winners");
  const bool fits = excess <= tier_buckets * bs::kBucketCapacity;
  Expect(got.drained == fits,
         what + ": the drain " + (got.drained ? "fit" : "failed") + " with " +
             std::to_string(excess) + " leftovers for " +
             std::to_string(tier_buckets * bs::kBucketCapacity) + " slots");
  if (!fits || !got.drained) return;
  // The tier: the rejected winners in (bucket, lane) order, lowest slots
  // first.
  std::vector<Ref> order;
  for (size_t b = 0; b < m; ++b) {
    for (size_t lane = 0; lane < bs::kBucketCapacity; ++lane) {
      if ((want_remaining[b] >> lane) & 1) order.push_back({b, lane});
    }
  }
  size_t tier_mismatch = got.tier.Count() != order.size();
  for (size_t i = 0; i < order.size(); ++i) {
    const size_t tb = i / bs::kBucketCapacity;
    const size_t tl = i % bs::kBucketCapacity;
    tier_mismatch += ((got.tier.masks[tb] >> tl) & 1) == 0;
    for (size_t line = 0; line < payload; ++line) {
      tier_mismatch +=
          got.tier.Bucket(tb)[line * bs::kBucketCapacity + tl] !=
          prefix.Bucket(order[i].bucket)[line * bs::kBucketCapacity +
                                         order[i].lane];
    }
  }
  Expect(tier_mismatch == 0, what + ": the tier is not the rejected winners "
                                    "in prefix order");
}

// A prefix of `m` buckets: distinct keys, random payload and tombstones,
// garbage in the dummy lanes, and winner masks with holes.
bs::Table RandomPrefix(const Shape& shape, std::mt19937_64* rng,
                       uint64_t* next_key, std::vector<uint64_t>* winners) {
  const bs::Layout layout = LayoutOf(shape);
  bs::Table prefix = ts::ZeroedTable(shape.sources, layout);
  winners->assign(shape.sources, 0);
  for (size_t b = 0; b < shape.sources; ++b) {
    uint8_t* bucket = prefix.Bucket(b);
    for (size_t i = 0; i < layout.BucketBytes(); ++i) {
      bucket[i] = static_cast<uint8_t>((*rng)());
    }
    for (size_t lane = 0; lane < bs::kBucketCapacity; ++lane) {
      bs::WriteSlotKey(bucket, lane, layout.key_bytes,
                       ts::FixtureKey((*next_key)++, layout.key_bytes));
      if ((*rng)() % 10 < 7) (*winners)[b] |= uint64_t{1} << lane;
    }
    // KEY ZERO is an ordinary key: one winner of the first bucket holds it.
    if (b == 0) {
      bs::WriteSlotKey(bucket, 5, layout.key_bytes, bs::KeyWords{0, 0});
      (*winners)[b] |= uint64_t{1} << 5;
    }
    prefix.masks[b] = ~uint64_t{0};  // the published masks; winners differ
  }
  return prefix;
}

// Exactly `count` winners at each listed home, every other lane a hole.
bs::Table PlantedPrefix(const Shape& shape, const std::vector<size_t>& counts,
                        const bs::RebuildNonce& nonce,
                        const bs::AesTagKeys& keys, uint64_t* next_key,
                        std::vector<uint64_t>* winners) {
  const bs::Layout layout = LayoutOf(shape);
  bs::Table prefix = ts::ZeroedTable(shape.sources, layout);
  winners->assign(shape.sources, 0);
  size_t at = 0;
  for (size_t h = 0; h < counts.size(); ++h) {
    const std::vector<bs::KeyWords> at_home = ts::KeysAtTagIndex(
        layout, nonce.real_lo, nonce.real_hi, bs::RoutingIndexMap{},
        shape.home_bits, shape.home_bits, h, counts[h], next_key, keys);
    for (const bs::KeyWords& key : at_home) {
      const size_t b = at / bs::kBucketCapacity;
      const size_t lane = at % bs::kBucketCapacity;
      ts::PlantEntry(layout, prefix.Bucket(b), lane, key, 2);
      (*winners)[b] |= uint64_t{1} << lane;
      ++at;
    }
  }
  // Filler keys in the holes, so the dummy lanes hash to something.
  for (; at < shape.sources * bs::kBucketCapacity; ++at) {
    bs::WriteSlotKey(prefix.Bucket(at / bs::kBucketCapacity),
                     at % bs::kBucketCapacity, layout.key_bytes,
                     ts::FixtureKey((*next_key)++, layout.key_bytes));
  }
  for (size_t b = 0; b < shape.sources; ++b) prefix.masks[b] = ~uint64_t{0};
  return prefix;
}

}  // namespace

int main() {
  std::printf("level one's direct B build (cpu_byteslice_dense_select)\n");
  const std::unique_ptr<bs::AesTagKeys> keys =
      bs::MakeAesTagKeys(microram::crypto::DeriveAesRoundKeys(
          microram::crypto::SecretKeySeed::Fixed(0xD1EC7B0Bull)));
  bs::RebuildNonce nonce;
  nonce.real_lo = 0x1234;
  nonce.real_hi = 0x77;
  std::mt19937_64 rng(0xB0B);
  uint64_t next_key = 1;

  // Random prefixes with about 70 % winners: at U = 2M (the engine's shape)
  // homes rarely overflow; at U = M/2 every home does, into a deep tier.
  const Shape shapes[] = {
      {8, 4, 8, 8},    {8, 4, 16, 33},  {4, 3, 8, 8},
      {2, 2, 8, 8},    {128, 8, 8, 16}, {256, 9, 8, 8},
      {8, 2, 8, 8},    {16, 3, 4, 4},
  };
  for (const Shape& shape : shapes) {
    for (int round = 0; round < 3; ++round) {
      std::vector<uint64_t> winners;
      bs::Table prefix = RandomPrefix(shape, &rng, &next_key, &winners);
      CheckAgainstReference(shape, prefix, winners, nonce, *keys,
                            /*tier_buckets=*/bs::kMaxResidualStashBuckets, &rng,
                            Name(shape) + " random " + std::to_string(round));
    }
  }

  // THE PRODUCER'S BOUNDARY: one bucket holds 64 leftovers and not 65, and
  // the excess is summed over homes, not taken from the largest.
  const Shape boundary{8, 4, 8, 8};
  struct Planted {
    std::vector<size_t> counts;
    bool fits;
  };
  const Planted planted[] = {
      {{128}, true},           // 64 leftovers: exactly one bucket
      {{129}, false},          // 65
      {{96, 96}, true},        // 32 + 32
      {{86, 86, 86}, false},   // 22 * 3 = 66, no home above 86
      {{0, 64, 0, 64}, true},  // full homes, nothing left over
  };
  for (const Planted& p : planted) {
    std::vector<uint64_t> winners;
    bs::Table prefix =
        PlantedPrefix(boundary, p.counts, nonce, *keys, &next_key, &winners);
    std::string what = Name(boundary) + " planted";
    for (size_t c : p.counts) what += " " + std::to_string(c);
    size_t excess = 0;
    for (size_t c : p.counts) excess += c > 64 ? c - 64 : 0;
    Expect((excess <= 64) == p.fits, what + ": the case itself is wrong");
    CheckAgainstReference(boundary, prefix, winners, nonce, *keys,
                          /*tier_buckets=*/1, &rng, what);
  }

  if (failures != 0) {
    std::fprintf(stderr, "%d direct-build checks failed\n", failures);
    return 1;
  }
  std::printf("direct B build: OK\n");
  return 0;
}
