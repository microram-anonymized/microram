// The cross-bucket dedup kernel, timed per 64 x 64 bucket pair with every
// all-pairs nest this host can run.  A merge of two buckets must find every
// key present in both (the "all-pairs" match mask); VP2INTERSECT computes it
// directly, but it is absent on many AVX-512 hosts (and may be masked off
// inside confidential VMs), so the library carries a portable fallback:
//
//   native          VP2INTERSECT, when this build compiles it in;
//   xor-min         the fallback the library takes without it
//                   (AllPairsMatchMaskQFallback / DFallback);
//   rotate-compare  a simpler compare-and-rotate nest (one comparison mask
//                   per register pair, widened through a scalar register),
//                   kept as the baseline for the xor-min fallback.
//
// A row is the whole one-field kernel the rebuild calls: load the key lines
// with dummies zeroed, transpose both sides, run the all-pairs nest, repair
// zero keys.  The buckets are L1-resident and successive pairs are
// independent, so it is a throughput per pair.  Key widths 8 (the qword nest)
// and 4 (the dword nest); a 16-byte key is four dword fields.  Rows run in a
// rotated order each repetition, and every kernel's masks are checked
// against the others'.
//
// The `self` rows time the within-bucket dedup of one field per bucket (ns per
// bucket), the other comparison kind a merge makes.
//
// Usage: cpu_byteslice_dedup_kernel_benchmark [pairs_per_rep] [reps]
//        [legacy|half_unique]
// half_unique matches the isolated routing pairs' load 0.5 and distinct-key
// obligation. This key-field-only loop does not load routing tags or values.
// Defaults: 2000000 7.  Pin it (taskset -c N).

#include "src/oram/rebuild/cpu_byteslice_dedup_masks.hpp"
#include "benchmarks/oram/cpu_byteslice_benchmark_support.hpp"

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>

namespace {

namespace bs = microram::byteslice;
using bs::benchmark_support::Clock;
using bs::benchmark_support::SecondsSince;
using bs::benchmark_support::SplitMix64;

// The rotate-compare baseline: a comparison mask per register pair, widened
// through a scalar register into the 64-bit answer.
uint64_t RotateCompareQ(const __m512i* a, const __m512i* b) {
  uint64_t dup = 0;
  const __m512i rot = _mm512_setr_epi64(1, 2, 3, 4, 5, 6, 7, 0);
  for (int i = 0; i < 8; ++i) {
    __m512i ai = a[i];
    for (int r = 0; r < 8; ++r) {
      for (int j = 0; j < 8; ++j) {
        dup |= static_cast<uint64_t>(
                   _cvtmask8_u32(_mm512_cmpeq_epi64_mask(ai, b[j])))
               << (8 * j);
      }
      ai = _mm512_permutexvar_epi64(rot, ai);
    }
  }
  return dup;
}

uint64_t RotateCompareD(const __m512i* a, const __m512i* b) {
  uint64_t dup = 0;
  const __m512i rot =
      _mm512_setr_epi32(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0);
  for (int i = 0; i < 4; ++i) {
    __m512i ai = a[i];
    for (int r = 0; r < 16; ++r) {
      for (int j = 0; j < 4; ++j) {
        dup |= static_cast<uint64_t>(
                   _cvtmask16_u32(_mm512_cmpeq_epi32_mask(ai, b[j])))
               << (16 * j);
      }
      ai = _mm512_permutexvar_epi32(rot, ai);
    }
  }
  return dup;
}

struct Native {
  static constexpr const char* kName = "native";
  static uint64_t Q(const __m512i* a, const __m512i* b) {
    return bs::AllPairsMatchMaskQ(a, b);
  }
  static uint64_t D(const __m512i* a, const __m512i* b) {
    return bs::AllPairsMatchMaskD(a, b);
  }
};
struct XorMin {
  static constexpr const char* kName = "xor-min";
  static uint64_t Q(const __m512i* a, const __m512i* b) {
    return bs::AllPairsMatchMaskQFallback(a, b);
  }
  static uint64_t D(const __m512i* a, const __m512i* b) {
    return bs::AllPairsMatchMaskDFallback(a, b);
  }
};
struct RotateCompare {
  static constexpr const char* kName = "rotate-compare";
  static uint64_t Q(const __m512i* a, const __m512i* b) {
    return RotateCompareQ(a, b);
  }
  static uint64_t D(const __m512i* a, const __m512i* b) {
    return RotateCompareD(a, b);
  }
};

// CrossBucketFieldMatchMaskQ / D with the nest swapped.
template <class Kernel, bool Qwords>
inline uint64_t FieldMatch(const uint8_t* first, uint64_t first_real,
                           const uint8_t* second, uint64_t second_real) {
  constexpr size_t n = Qwords ? 8 : 4;
  __m512i fl[n], sl[n], a[n], b[n];
  const uint64_t zero_first =
      bs::LoadKeyLinesZeroingDummies(first, n, first_real, n, fl);
  const uint64_t zero_second =
      bs::LoadKeyLinesZeroingDummies(second, n, second_real, n, sl);
  uint64_t raw;
  if constexpr (Qwords) {
    bs::TransposeKeyLinesToQwords(fl, a);
    bs::TransposeKeyLinesToQwords(sl, b);
    raw = Kernel::Q(a, b);
  } else {
    bs::TransposeKeyLinesToDwords(fl, a);
    bs::TransposeKeyLinesToDwords(sl, b);
    raw = Kernel::D(a, b);
  }
  return bs::RepairZeroKeyMatches(raw, zero_first, zero_second, second_real);
}

// Sixteen buckets of eight key byte lines, keys drawn from a pool small
// enough that pairs share keys, and random occupancy.
constexpr size_t kBuckets = 16;
constexpr size_t kBucketBytes = 8 * bs::kBucketCapacity;

struct Fixture {
  alignas(64) uint8_t bytes[kBuckets * kBucketBytes];
  uint64_t real[kBuckets];

  const uint8_t* Bucket(size_t i) const { return bytes + i * kBucketBytes; }
};

void FillFixture(Fixture& f) {
  uint64_t state = 0xDEDB0C5ull;
  uint64_t pool[96];
  for (uint64_t& k : pool) k = SplitMix64(state);
  pool[0] = 0;
  for (size_t i = 0; i < kBuckets; ++i) {
    f.real[i] = SplitMix64(state) | SplitMix64(state);  // ~3/4 occupied
    for (size_t slot = 0; slot < bs::kBucketCapacity; ++slot) {
      const uint64_t key = pool[SplitMix64(state) % 96];
      for (size_t l = 0; l < 8; ++l) {
        f.bytes[i * kBucketBytes + l * bs::kBucketCapacity + slot] =
            static_cast<uint8_t>(key >> (8 * l));
      }
    }
  }
}

void FillHalfUniqueFixture(Fixture& f) {
  uint64_t state = 741;
  for (size_t i = 0; i < kBuckets; ++i) {
    uint8_t slots[64];
    for (size_t j = 0; j < 64; ++j) slots[j] = static_cast<uint8_t>(j);
    f.real[i] = 0;
    for (size_t j = 0; j < 32; ++j) {
      const size_t pick = j + SplitMix64(state) % (64 - j);
      std::swap(slots[j], slots[pick]);
      f.real[i] |= uint64_t{1} << slots[j];
    }
    for (size_t slot = 0; slot < 64; ++slot) {
      const uint64_t key = (i * 64 + slot + 1) * uint64_t{0x9E3779B1};
      for (size_t line = 0; line < 8; ++line)
        f.bytes[i * kBucketBytes + line * 64 + slot] = static_cast<uint8_t>(key >> (8 * line));
    }
  }
}

// Public generated fixtures only: an independent scalar oracle outside timing.
uint64_t ReferenceDigest(const Fixture& f, size_t key_bytes, bool self) {
  const auto key = [&](size_t bucket, size_t slot) {
    uint64_t value = 0;
    for (size_t line = 0; line < key_bytes; ++line)
      value |= uint64_t{f.Bucket(bucket)[line * 64 + slot]} << (8 * line);
    return value;
  };
  uint64_t digest = 0;
  for (size_t p = 0; p < kBuckets; ++p) {
    const size_t first = p, second = self ? p : (p * 7 + 3) % kBuckets;
    uint64_t mask = 0;
    for (size_t j = 0; j < 64; ++j) {
      if (!(f.real[second] & (uint64_t{1} << j))) continue;
      for (size_t i = 0; i < (self ? j : 64); ++i) {
        if ((f.real[first] & (uint64_t{1} << i)) && key(first, i) == key(second, j)) {
          mask |= uint64_t{1} << j;
          break;
        }
      }
    }
    digest = digest * 31 + mask;
  }
  return digest;
}

struct Row {
  const char* name;
  size_t key_bytes;
  void (*run)(const Fixture&, long, uint64_t*);
  std::vector<double> ns;
  uint64_t check = 0;
  bool self = false;  // within-bucket rows are checked only against each other
};

// *check receives an order-sensitive digest of every mask.
template <class Kernel, bool Qwords>
void RunPairs(const Fixture& f, long pairs, uint64_t* check) {
  uint64_t digest = 0;
  for (long p = 0; p < pairs; ++p) {
    const size_t i = static_cast<size_t>(p) % kBuckets;
    const size_t j = (static_cast<size_t>(p) * 7 + 3) % kBuckets;
    digest = digest * 31 +
             FieldMatch<Kernel, Qwords>(f.Bucket(i), f.real[i], f.Bucket(j),
                                        f.real[j]);
  }
  *check = digest;
}

// The within-bucket dedup of one key field (BucketSelfFieldMatchMaskQ / D),
// whatever intersect this build compiles: the per-call cost of the `self`
// comparisons a merge counts (the level-arena benchmark's _compare_counted
// build reports how many a window makes).
template <bool Qwords>
void RunSelf(const Fixture& f, long buckets, uint64_t* check) {
  uint64_t digest = 0;
  for (long p = 0; p < buckets; ++p) {
    const size_t i = static_cast<size_t>(p) % kBuckets;
    digest = digest * 31 + (Qwords ? bs::BucketSelfFieldMatchMaskQ(f.Bucket(i), f.real[i], 8)
                                   : bs::BucketSelfFieldMatchMaskD(f.Bucket(i), f.real[i], 4));
  }
  *check = digest;
}

template <class Kernel>
void AddRows(std::vector<Row>& rows) {
  rows.push_back({Kernel::kName, 8, &RunPairs<Kernel, true>, {}, 0});
  rows.push_back({Kernel::kName, 4, &RunPairs<Kernel, false>, {}, 0});
}

}  // namespace

int main(int argc, char** argv) {
  const long pairs = argc > 1 ? std::atol(argv[1]) : 2000000;
  const int reps = argc > 2 ? std::atoi(argv[2]) : 7;
  const char* fixture = argc > 3 ? argv[3] : "legacy";
  if (argc > 4 || pairs <= 0 || reps <= 0 ||
      (std::strcmp(fixture, "legacy") && std::strcmp(fixture, "half_unique"))) {
    std::fprintf(stderr, "usage: %s [pairs_per_rep] [reps] [legacy|half_unique]\n", argv[0]);
    return 2;
  }
  static Fixture f;
  if (std::strcmp(fixture, "half_unique") == 0) FillHalfUniqueFixture(f);
  else FillFixture(f);

  std::vector<Row> rows;
#if MICRORAM_BYTESLICE_USE_VP2INTERSECT
  AddRows<Native>(rows);
#endif
  AddRows<XorMin>(rows);
  AddRows<RotateCompare>(rows);
  rows.push_back({"self", 8, &RunSelf<true>, {}, 0, true});
  rows.push_back({"self", 4, &RunSelf<false>, {}, 0, true});

  for (Row& row : rows) {
    uint64_t check;
    row.run(f, kBuckets, &check);
    if (check != ReferenceDigest(f, row.key_bytes, row.self)) {
      std::fprintf(stderr, "scalar fixture check failed: %zu B %s\n", row.key_bytes, row.name);
      return 1;
    }
  }

  for (Row& row : rows) row.run(f, pairs / 10 + 1, &row.check);  // warm-up
  for (int rep = 0; rep < reps; ++rep) {
    for (size_t k = 0; k < rows.size(); ++k) {
      Row& row = rows[(k + static_cast<size_t>(rep)) % rows.size()];
      const auto t0 = Clock::now();
      uint64_t check;
      row.run(f, pairs, &check);
      row.ns.push_back(SecondsSince(t0) * 1e9 / static_cast<double>(pairs));
      row.check = check;
    }
  }

  std::printf("cpu_byteslice_dedup_kernel_benchmark: ns per 64 x 64 bucket "
              "pair, %ld pairs x %d reps (VP2INTERSECT compiled: %d)\n",
              pairs, reps, MICRORAM_BYTESLICE_USE_VP2INTERSECT);
  std::printf("  fixture: %s (%s); scalar reference passed\n", fixture,
              std::strcmp(fixture, "half_unique") == 0 ? "32 real slots/bucket, unique keys, seed 741" :
                                                        "about 3/4 occupancy, overlapping keys and real zero keys");
  std::printf("  %-4s %-15s %8s %8s %8s\n", "key", "kernel", "min", "median",
              "max");
  bool agree = true;
  for (Row& row : rows) {
    std::sort(row.ns.begin(), row.ns.end());
    std::printf("  %zu B  %-15s %8.1f %8.1f %8.1f\n", row.key_bytes, row.name,
                row.ns.front(), row.ns[row.ns.size() / 2], row.ns.back());
    for (const Row& other : rows) {
      if (other.key_bytes == row.key_bytes && other.self == row.self && other.check != row.check) {
        agree = false;
      }
    }
  }
  std::printf("  masks: %s\n",
              agree ? "all kernels agree" : "KERNELS DISAGREE");
  return agree ? 0 : 1;
}
