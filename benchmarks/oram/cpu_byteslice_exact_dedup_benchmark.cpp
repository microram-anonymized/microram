// Full stored-key dedup entry points, including the wide-key paths.
//
// Usage: cpu_byteslice_exact_dedup_benchmark [iterations] [repetitions]
// Pin to one CPU. The fixed seed creates half-occupied L1-resident buckets
// with complete duplicate keys and zero keys. Scalar checks run before timing.
// Rows report ns per helper call; destinations performs four destinations.
// Dense rows use a separate unique-key bucket and 16/64 prepared queries;
// query preparation is outside timing. Dense helpers are measured directly
// even on hosts whose engine dispatch chooses the fallback probe instead.
// This is a kernel throughput measurement, not whole-ORAM performance.

#include "src/oram/rebuild/cpu_byteslice_dedup_masks.hpp"
#include "src/oram/table/cpu_byteslice_dense_match.hpp"

#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <random>
#include <vector>

namespace {
namespace bs = microram::byteslice;
constexpr size_t kBuckets = 8;
constexpr size_t kBytes = bs::kBucketCapacity * bs::kMaxKeyBytes;

struct Fixture {
  alignas(64) uint8_t data[kBuckets][kBytes]{};
  uint64_t real[kBuckets]{};
  uint64_t classes[kBuckets]{};
  alignas(64) uint8_t dense[kBytes]{};
  bs::KeyWords dense_keys[64], dense_query_keys[64];
  bs::DenseMatchQueries dense_queries[3];
  uint64_t dense_real = 0;

  Fixture() {
    std::mt19937_64 rng(0x4e315f6465647570ull);
    std::array<std::array<uint8_t, 16>, 48> keys{};
    for (size_t i = 1; i < keys.size(); ++i) {
      for (uint8_t& b : keys[i]) b = static_cast<uint8_t>(rng());
    }
    for (size_t b = 0; b < kBuckets; ++b) {
      real[b] = rng();
      classes[b] = rng();
      for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
        for (size_t byte = 0; byte < 16; ++byte) {
          data[b][byte * bs::kBucketCapacity + e] =
              keys[(e + 17 * b) % keys.size()][byte];
        }
      }
    }
    dense_real = rng();
    for (size_t e = 0; e < 64; ++e) {
      dense_keys[e] = e == 0 ? bs::KeyWords{0, 0} : bs::KeyWords{rng(), rng()};
      for (size_t byte = 0; byte < 16; ++byte) {
        const uint64_t word = byte < 8 ? dense_keys[e].w0 : dense_keys[e].w1;
        dense[byte * 64 + e] = static_cast<uint8_t>(word >> (8 * (byte % 8)));
      }
    }
    for (size_t e = 0; e < 64; ++e) {
      dense_query_keys[e] = e % 2 == 0 ? dense_keys[e / 2] :
                                          bs::KeyWords{rng(), rng()};
    }
    bs::PrepareDenseMatchQueries<4, 1>(dense_query_keys, 64, dense_queries[0]);
    bs::PrepareDenseMatchQueries<8, 1>(dense_query_keys, 64, dense_queries[1]);
    bs::PrepareDenseMatchQueries<8, 2>(dense_query_keys, 64, dense_queries[2]);
  }
};

uint64_t ScalarMask(const uint8_t* a, uint64_t ar, const uint8_t* b,
                    uint64_t br, size_t width, bool self = false) {
  uint64_t result = 0;
  for (size_t j = 0; j < 64; ++j) {
    if (!((br >> j) & 1)) continue;
    for (size_t i = 0; i < (self ? j : 64); ++i) {
      if (!((ar >> i) & 1)) continue;
      bool same = true;
      for (size_t byte = 0; byte < width; ++byte) {
        same &= a[byte * 64 + i] == b[byte * 64 + j];
      }
      if (same) result |= uint64_t{1} << j;
    }
  }
  return result;
}

// Out-of-line entry points also make the compiled kernel bodies easy to inspect.
__attribute__((noinline)) uint64_t Cross(Fixture& f, size_t i, size_t width) {
  const size_t j = (i + 3) % kBuckets;
  return bs::CrossBucketDuplicateMask(f.data[i], f.real[i], f.data[j],
                                       f.real[j], width);
}

__attribute__((noinline)) uint64_t Self(Fixture& f, size_t i, size_t width) {
  return bs::BucketSelfDuplicateMask(f.data[i], f.real[i], width);
}

__attribute__((noinline)) uint64_t Destinations(Fixture& f, size_t i,
                                               size_t width) {
  uint8_t* destinations[4];
  uint64_t masks[4];
  uint64_t* mask_ptrs[4];
  for (size_t q = 0; q < 4; ++q) {
    const size_t j = (i + q + 1) % kBuckets;
    destinations[q] = f.data[j];
    masks[q] = f.real[j];
    mask_ptrs[q] = &masks[q];
  }
  bs::DedupBucketDestinations(f.data[i], f.real[i], destinations, mask_ptrs,
                              4, width);
  uint64_t digest = 0;
  for (uint64_t mask : masks) digest = digest * 31 + mask;
  return digest;
}

__attribute__((noinline)) uint64_t Class(Fixture& f, size_t i, size_t width) {
  const size_t j = (i + 3) % kBuckets;
  const uint64_t tier = f.real[j] & f.classes[j];
  const uint64_t carry = f.real[j] & ~f.classes[j];
  uint64_t first_dup, carry_dup;
  bs::CrossBucketClassDuplicateMasks(f.data[i], f.real[i], f.data[j], carry,
                                      tier, width, &first_dup, &carry_dup);
  return first_dup * 31 + carry_dup;
}

template <size_t Lanes>
__attribute__((noinline)) uint64_t Dense(Fixture& f, size_t, size_t width) {
  alignas(64) uint8_t slots[64];
  if (width == 4)
    return bs::MatchUniqueDenseSlots<4, 1>(f.dense, f.dense_real,
                                           f.dense_queries[0], Lanes, slots);
  if (width == 8)
    return bs::MatchUniqueDenseSlots<8, 1>(f.dense, f.dense_real,
                                           f.dense_queries[1], Lanes, slots);
  return bs::MatchUniqueDenseSlots<8, 2>(f.dense, f.dense_real,
                                         f.dense_queries[2], Lanes, slots);
}

struct Row {
  const char* name;
  size_t width;
  uint64_t (*call)(Fixture&, size_t, size_t);
  std::vector<double> ns;
  uint64_t digest = 0;
};

bool Validate(Fixture& f, size_t width) {
  for (size_t i = 0; i < kBuckets; ++i) {
    const size_t j = (i + 3) % kBuckets;
    if (Cross(f, i, width) != ScalarMask(f.data[i], f.real[i], f.data[j],
                                          f.real[j], width)) return false;
    if (Self(f, i, width) != ScalarMask(f.data[i], f.real[i], f.data[i],
                                         f.real[i], width, true)) return false;
    const uint64_t tier = f.real[j] & f.classes[j];
    const uint64_t carry = f.real[j] & ~f.classes[j];
    const uint64_t class_expected =
        ScalarMask(f.data[j], tier, f.data[i], f.real[i], width) * 31 +
        ScalarMask(f.data[i], f.real[i], f.data[j], carry, width);
    if (Class(f, i, width) != class_expected) return false;
    uint64_t destinations_expected = 0;
    for (size_t q = 0; q < 4; ++q) {
      const size_t d = (i + q + 1) % kBuckets;
      destinations_expected = destinations_expected * 31 +
          (f.real[d] & ~ScalarMask(f.data[i], f.real[i], f.data[d],
                                    f.real[d], width));
    }
    if (Destinations(f, i, width) != destinations_expected) return false;
  }
  uint64_t dense_expected = 0;
  for (size_t q = 0; q < 64; ++q) {
    for (size_t e = 0; e < 64; ++e) {
      bool same = ((f.dense_real >> e) & 1) != 0;
      for (size_t byte = 0; byte < width; ++byte) {
        const uint64_t word = byte < 8 ? f.dense_query_keys[q].w0 :
                                           f.dense_query_keys[q].w1;
        same &= f.dense[byte * 64 + e] ==
                   static_cast<uint8_t>(word >> (8 * (byte % 8)));
      }
      if (same) dense_expected |= uint64_t{1} << q;
    }
  }
  if (Dense<64>(f, 0, width) != dense_expected ||
      Dense<16>(f, 0, width) != (dense_expected & 0xffff)) return false;
  return true;
}

void Run(Row& row, Fixture& f, long iterations) {
  uint64_t digest = 0;
  const auto start = std::chrono::steady_clock::now();
  for (long n = 0; n < iterations; ++n) {
    digest = digest * 31 + row.call(f, static_cast<size_t>(n) % kBuckets,
                                   row.width);
  }
  const auto end = std::chrono::steady_clock::now();
  row.ns.push_back(std::chrono::duration<double, std::nano>(end - start).count() /
                   static_cast<double>(iterations));
  row.digest = digest;
}
}  // namespace

int main(int argc, char** argv) {
  const long iterations = argc > 1 ? std::atol(argv[1]) : 200000;
  const int reps = argc > 2 ? std::atoi(argv[2]) : 7;
  if (argc > 3 || iterations <= 0 || reps <= 0) {
    std::fprintf(stderr, "usage: %s [iterations] [repetitions]\n", argv[0]);
    return 2;
  }
  static Fixture fixture;
  std::vector<Row> rows;
  for (size_t width : {size_t{4}, size_t{8}, size_t{16}}) {
    if (!Validate(fixture, width)) {
      std::fprintf(stderr, "scalar reference failed at width %zu\n", width);
      return 1;
    }
    rows.push_back({"cross", width, &Cross, {}, 0});
    rows.push_back({"self", width, &Self, {}, 0});
    rows.push_back({"destinations4", width, &Destinations, {}, 0});
    rows.push_back({"class", width, &Class, {}, 0});
    rows.push_back({"dense16", width, &Dense<16>, {}, 0});
    rows.push_back({"dense64", width, &Dense<64>, {}, 0});
  }
  for (Row& row : rows) {
    Run(row, fixture, iterations / 10 + 1);
    row.ns.clear();
  }
  for (int rep = 0; rep < reps; ++rep) {
    for (size_t k = 0; k < rows.size(); ++k) {
      Run(rows[(k + static_cast<size_t>(rep)) % rows.size()], fixture, iterations);
    }
  }
  std::printf("full-key dedup ns/call; %ld iterations x %d reps; VP2INTERSECT=%d; "
              "16-byte segment match=%d\n",
                iterations, reps, MICRORAM_BYTESLICE_USE_VP2INTERSECT,
                int{bs::kWideKeySegmentMatch});
  std::puts("fixed random full keys, approximately half occupancy; scalar checks passed");
  std::puts("bytes helper                 min     median        max digest");
  for (Row& row : rows) {
    std::sort(row.ns.begin(), row.ns.end());
    std::printf("%5zu %-15s %10.2f %10.2f %10.2f %016llx\n", row.width,
                  row.name, row.ns.front(), row.ns[row.ns.size() / 2],
                  row.ns.back(), static_cast<unsigned long long>(row.digest));
  }
}
