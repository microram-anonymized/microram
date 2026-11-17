// Correctness tests for the rebuild's cross-source deduplication
// (src/oram/rebuild/cpu_byteslice_dedup_rebuild.hpp).  A rebuild merges
// several SOURCE tables (the levels being combined, freshest first) through an
// oblivious butterfly routing network; a key may live in more than one source,
// and only its freshest copy may survive, or a later read would return a stale
// value.  Entries a full bucket cannot hold are SHED into a per-level residual
// stash; the pooled residuals are later offered their target bucket again (the
// "second chance"), and whatever still does not fit is published as the
// level's residual TIER, probed right after the main table.
//
// Covered, each against a scalar reference or an independent formulation:
//   * the register duplicate-mask kernels (all-pairs, cross-bucket, self,
//     class-marked) at every stored key width, including dirty dummy slots and
//     the zero key;
//   * the dedup MergeSplit's conservation, and the intra-then-cross routing
//     network -- byte-identical to the flat butterfly when there is nothing to
//     deduplicate, and keeping exactly the freshest copy when there is;
//   * the residual pool's freshness-ranked dedup, its emission windows and its
//     equal-rank contract, all invariant under any slicing of the work (the
//     scheduler may cut a phase at any unit boundary);
//   * the residual range planner and the second-chance sweep, including the
//     invariant that the published (main, tier) pair is duplicate-free;
//   * the incremental chain is a pure reordering of the monolithic network,
//     and the fixed last level's direct merge equals the two-step
//     split-then-fold it replaces and sheds like an ordinary level.

#include "src/oram/rebuild/cpu_byteslice_dedup_rebuild.hpp"
#include "tests/oram/cpu_byteslice_rebuild_test_support.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <random>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace {

namespace bs = microram::byteslice;
using microram::byteslice::test_support::Expect;
using microram::byteslice::test_support::OwnedLevelStashes;

// The narrow form, for the majority of this file: every test but the two
// duplicate-mask kernels below runs at a key width of at most 8 bytes, where
// the stored key IS a uint64.
uint64_t ReadKey(const uint8_t* bucket, size_t slot, size_t key_bytes) {
  return bs::ReadSlotKey(bucket, slot, key_bytes).w0;
}

// Takes a bs::KeyWords, which a uint64 converts to implicitly.
void WriteKey(uint8_t* bucket, size_t slot, size_t key_bytes,
              bs::KeyWords key) {
  bs::WriteSlotKey(bucket, slot, key_bytes, key);
}

// ---------------------------------------------------------------------------
// AllPairsMatchMaskQ / D
// ---------------------------------------------------------------------------
//
// The register kernels under every cross-bucket dedup, checked directly
// against a scalar all-pairs loop.  Both the kernel this build selects and the
// VP2INTERSECT-free fallback run, so a VP2INTERSECT host still tests the path
// hosts without VP2INTERSECT take.  Independent random keys almost never
// collide, so the cases are built:
//
//   * one planted match at each of the 64 x 64 (a lane, b lane) positions, the
//     other b keys near misses of a keys: differing only in the top bit, only
//     in the lowest bit, or only in one half, so sharing the other half (the
//     32-bit halves of an 8-byte key, the 16-bit halves of a 4-byte one);
//   * beside each planted match, an a key differing from it only in the top
//     bit, whose XOR is what a signed minimum would prefer to zero;
//   * zero keys (the value dummy-zeroing collapses onto), all-ones keys, and
//     whole sides of one repeated key;
//   * random draws from a small pool of such values.
template <class Key>
struct AllPairsCase {
  Key a[64], b[64];
};

template <class Key>
uint64_t ReferenceAllPairs(const AllPairsCase<Key>& c) {
  uint64_t dup = 0;
  for (size_t e = 0; e < 64; ++e) {
    for (size_t k = 0; k < 64; ++k) {
      if (c.b[e] == c.a[k]) dup |= uint64_t{1} << e;
    }
  }
  return dup;
}

// Register m holds keys m*K .. m*K+K-1 in lane order (K keys per register),
// which is how the transposes lay out slots.  Returns the reference mask.
template <class Key>
uint64_t ExpectAllPairsAgree(const AllPairsCase<Key>& c) {
  constexpr size_t kRegisters = sizeof(Key);  // 64 keys of sizeof(Key) bytes
  constexpr size_t kPerRegister = 64 / sizeof(Key);
  __m512i a[kRegisters], b[kRegisters];
  for (size_t m = 0; m < kRegisters; ++m) {
    a[m] = _mm512_loadu_si512(c.a + m * kPerRegister);
    b[m] = _mm512_loadu_si512(c.b + m * kPerRegister);
  }
  const uint64_t expected = ReferenceAllPairs(c);
  if constexpr (sizeof(Key) == 8) {
    Expect(bs::AllPairsMatchMaskQ(a, b) == expected,
           "AllPairsMatchMaskQ disagrees with the scalar reference");
    Expect(bs::AllPairsMatchMaskQFallback(a, b) == expected,
           "AllPairsMatchMaskQFallback disagrees with the scalar reference");
  } else {
    Expect(bs::AllPairsMatchMaskD(a, b) == expected,
           "AllPairsMatchMaskD disagrees with the scalar reference");
    Expect(bs::AllPairsMatchMaskDFallback(a, b) == expected,
           "AllPairsMatchMaskDFallback disagrees with the scalar reference");
  }
  return expected;
}

template <class Key>
struct NearMisses {
  static constexpr Key kTop = Key{1} << (8 * sizeof(Key) - 1);
  static constexpr Key kLowHalf =
      static_cast<Key>(~Key{0}) >> (4 * sizeof(Key));
  // XOR masks that turn a key into a near miss of itself.
  static constexpr Key kFlips[5] = {kTop, Key{1}, kLowHalf,
                                    static_cast<Key>(~kLowHalf),
                                    static_cast<Key>(kLowHalf + 1)};
};

template <class Key>
void TestAllPairsKernels(uint64_t seed) {
  using NM = NearMisses<Key>;
  std::mt19937_64 rng(seed);
  Key base[64];
  for (Key& k : base) k = static_cast<Key>(rng());
  AllPairsCase<Key> c;

  for (size_t ea = 0; ea < 64; ++ea) {
    for (size_t eb = 0; eb < 64; ++eb) {
      for (size_t k = 0; k < 64; ++k) {
        c.a[k] = base[k];
        c.b[k] = base[(5 * k + 3) % 64] ^ NM::kFlips[k % 5];
      }
      c.b[eb] = c.a[ea];
      c.a[(ea + 1 + eb % 63) % 64] = c.a[ea] ^ NM::kTop;  // never ea itself
      Expect((ExpectAllPairsAgree(c) >> eb) & 1,
             "the planted match is missing from the reference");
    }
  }

  const Key ones = static_cast<Key>(~Key{0});
  const uint64_t all = ~uint64_t{0};
  std::fill(std::begin(c.a), std::end(c.a), Key{0});
  std::fill(std::begin(c.b), std::end(c.b), Key{0});
  Expect(ExpectAllPairsAgree(c) == all, "all-zero sides must match");
  for (size_t k = 0; k < 64; ++k) c.a[k] = base[k] | 1;
  Expect(ExpectAllPairsAgree(c) == 0, "zero b keys must not match nonzero a");
  for (size_t ea = 0; ea < 64; ++ea) {
    for (size_t k = 0; k < 64; ++k) c.a[k] = base[k] | 1;
    c.a[ea] = 0;
    Expect(ExpectAllPairsAgree(c) == all, "one zero a key must match every "
                                          "zero b key");
  }
  for (Key key : {base[0], Key{0}, ones, NM::kTop}) {
    std::fill(std::begin(c.a), std::end(c.a), key);
    for (Key flip : NM::kFlips) {
      std::fill(std::begin(c.b), std::end(c.b), static_cast<Key>(key ^ flip));
      Expect(ExpectAllPairsAgree(c) == 0,
             "a repeated near miss must not match");
    }
    for (size_t k = 0; k < 64; ++k) {
      c.b[k] = (k % 3 == 0) ? key : static_cast<Key>(key ^ NM::kFlips[k % 5]);
    }
    ExpectAllPairsAgree(c);
  }

  for (int trial = 0; trial < 3000; ++trial) {
    const size_t pool_size = 1 + trial % 16;
    Key pool[16] = {Key{0}, ones};
    for (size_t i = 2; i < pool_size; ++i) {
      pool[i] = (rng() & 1) ? static_cast<Key>(rng())
                            : static_cast<Key>(pool[rng() % i] ^
                                               NM::kFlips[rng() % 5]);
    }
    for (size_t k = 0; k < 64; ++k) {
      c.a[k] = pool[rng() % pool_size];
      c.b[k] = pool[rng() % pool_size];
    }
    ExpectAllPairsAgree(c);
  }
}

void TestAllPairsMatchMasks() {
  TestAllPairsKernels<uint64_t>(0xA11FA1A5ull);
  TestAllPairsKernels<uint32_t>(0xA11FA1A6ull);
  std::printf("  AllPairsMatchMaskQ/D and their fallbacks ok\n");
}

// ---------------------------------------------------------------------------
// CrossBucketDuplicateMask
// ---------------------------------------------------------------------------

// Scalar definition of what the kernel computes: the real slots of `second`
// whose key occurs in some real slot of `first`.  Dummy slots of either bucket
// are ignored no matter what bytes they hold.
uint64_t ReferenceDuplicateMask(const uint8_t* first, uint64_t first_real,
                                const uint8_t* second, uint64_t second_real,
                                size_t key_bytes) {
  std::unordered_set<bs::KeyWords> keys;
  for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
    if ((first_real >> e) & 1) keys.insert(bs::ReadSlotKey(first, e, key_bytes));
  }
  uint64_t dup = 0;
  for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
    if (!((second_real >> e) & 1)) continue;
    if (keys.count(bs::ReadSlotKey(second, e, key_bytes))) {
      dup |= uint64_t{1} << e;
    }
  }
  return dup;
}

// Every copy of a key but the one in the lowest real slot.
uint64_t ReferenceSelfDuplicateMask(const uint8_t* bucket, uint64_t real,
                                    size_t key_bytes) {
  std::unordered_set<bs::KeyWords> seen;
  uint64_t dup = 0;
  for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
    if (!((real >> e) & 1)) continue;
    if (!seen.insert(bs::ReadSlotKey(bucket, e, key_bytes)).second) {
      dup |= uint64_t{1} << e;
    }
  }
  return dup;
}

// The kWideKeySegmentMatch predicate for 16-byte keys: slot e of `second`
// is reported when each 32-bit segment of its key occurs in that segment of
// SOME real slot of `first`, not necessarily the same one.
uint64_t ReferenceSegmentDuplicateMask(const uint8_t* first, uint64_t first_real,
                                       const uint8_t* second,
                                       uint64_t second_real) {
  uint64_t dup = second_real;
  for (size_t off = 0; off < bs::kMaxKeyBytes; off += 4) {
    std::unordered_set<uint32_t> segments;
    for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
      if (!((first_real >> e) & 1)) continue;
      uint32_t v = 0;
      for (size_t b = 0; b < 4; ++b)
        v |= uint32_t{first[(off + b) * bs::kBucketCapacity + e]} << (8 * b);
      segments.insert(v);
    }
    for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
      uint32_t v = 0;
      for (size_t b = 0; b < 4; ++b)
        v |= uint32_t{second[(off + b) * bs::kBucketCapacity + e]} << (8 * b);
      if (!segments.count(v)) dup &= ~(uint64_t{1} << e);
    }
  }
  return dup;
}

// What the build's kernels compute: exact equality, but the segment predicate
// for 16-byte keys under kWideKeySegmentMatch.
uint64_t ReferenceBuildDuplicateMask(const uint8_t* first, uint64_t first_real,
                                     const uint8_t* second,
                                     uint64_t second_real, size_t key_bytes) {
  if (bs::kWideKeySegmentMatch && key_bytes == bs::kMaxKeyBytes) {
    return ReferenceSegmentDuplicateMask(first, first_real, second,
                                         second_real);
  }
  return ReferenceDuplicateMask(first, first_real, second, second_real,
                                key_bytes);
}

// Every supported stored width, including partial final fields.
const size_t kKeyWidths[] = {1, 2, 3, 4, 5, 6, 7, 8,
                             9, 10, 11, 12, 13, 14, 15, 16};

bs::KeyWords PoolKey(std::mt19937_64& rng, size_t key_bytes) {
  return bs::MaskKey(bs::KeyWords{rng(), rng()}, key_bytes);
}

// Both buckets draw from one small key pool, and DUMMY slots draw from the same
// pool: a dummy holding a live key of the other bucket is exactly the case that
// makes the naive "intersect all 64 lanes" wrong, so it has to be common here.
// The pool always contains 0, which is the value the kernel's dummy-zeroing
// collapses onto and then has to repair.
void TestCrossBucketDuplicateMask() {
  std::mt19937_64 rng(0xD3D0F00Dull);
  for (size_t key_bytes : kKeyWidths) {
    bs::StashLayout layout;
    layout.key_bytes = key_bytes;
    layout.value_bytes = 4;
    layout.tag_bytes = 1;
    auto table = bs::Table::Create(2, layout.Base());

    for (int trial = 0; trial < 400; ++trial) {
      // A deliberately small pool so cross-bucket collisions are frequent.
      const size_t pool_size = 1 + (trial % 24);
      std::vector<bs::KeyWords> pool(pool_size);
      pool[0] = bs::KeyWords{};  // the value the zero-key repair exists for
      for (size_t i = 1; i < pool_size; ++i) pool[i] = PoolKey(rng, key_bytes);

      uint64_t real[2];
      // Cover the degenerate occupancies as well as random ones.
      switch (trial % 8) {
        case 0: real[0] = 0; real[1] = rng(); break;
        case 1: real[0] = rng(); real[1] = 0; break;
        case 2: real[0] = ~uint64_t{0}; real[1] = ~uint64_t{0}; break;
        default: real[0] = rng(); real[1] = rng(); break;
      }
      for (int b = 0; b < 2; ++b) {
        for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
          WriteKey(table.Bucket(b), e, key_bytes, pool[rng() % pool_size]);
        }
      }
      const uint64_t expected = ReferenceDuplicateMask(
          table.Bucket(0), real[0], table.Bucket(1), real[1], key_bytes);
      const uint64_t got = bs::CrossBucketDuplicateMask(
          table.Bucket(0), real[0], table.Bucket(1), real[1], key_bytes);
      Expect(got == expected, "CrossBucketDuplicateMask disagrees with the "
                              "scalar reference");
    }

    // A key that lives only in a DUMMY slot of `first` must never mark
    // anything: it is not part of the fresher table's contents.
    const bs::KeyWords one_key = bs::MaskKey(bs::KeyWords{0x2A}, key_bytes);
    for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
      WriteKey(table.Bucket(0), e, key_bytes, one_key);
      WriteKey(table.Bucket(1), e, key_bytes, one_key);
    }
    Expect(bs::CrossBucketDuplicateMask(table.Bucket(0), 0, table.Bucket(1),
                                        ~uint64_t{0}, key_bytes) == 0,
           "dummy-only keys of the fresher bucket must not match");
    Expect(bs::CrossBucketDuplicateMask(table.Bucket(0), 1, table.Bucket(1),
                                        ~uint64_t{0},
                                        key_bytes) == ~uint64_t{0},
           "a real key of the fresher bucket must match every copy");
  }
  std::printf("  CrossBucketDuplicateMask ok\n");
}

// Same shape for the pool's internal (self) dedup, the second kernel whose
// behaviour depends on the stored key width.
void TestBucketSelfDuplicateMask() {
  std::mt19937_64 rng(0x5E1FD00Dull);
  for (size_t key_bytes : kKeyWidths) {
    bs::StashLayout layout;
    layout.key_bytes = key_bytes;
    layout.value_bytes = 4;
    layout.tag_bytes = 1;
    auto table = bs::Table::Create(1, layout.Base());

    for (int trial = 0; trial < 400; ++trial) {
      const size_t pool_size = 1 + (trial % 24);
      std::vector<bs::KeyWords> pool(pool_size);
      pool[0] = bs::KeyWords{};
      for (size_t i = 1; i < pool_size; ++i) pool[i] = PoolKey(rng, key_bytes);

      uint64_t real;
      switch (trial % 4) {
        case 0: real = 0; break;
        case 1: real = ~uint64_t{0}; break;
        default: real = rng(); break;
      }
      for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
        WriteKey(table.Bucket(0), e, key_bytes, pool[rng() % pool_size]);
      }
      Expect(bs::BucketSelfDuplicateMask(table.Bucket(0), real, key_bytes) ==
                 ReferenceSelfDuplicateMask(table.Bucket(0), real, key_bytes),
             "BucketSelfDuplicateMask disagrees with the scalar reference");
    }
  }
  std::printf("  BucketSelfDuplicateMask ok\n");
}

// Each segment can occur in a different donor without any full-key match.
// Rotate the slots through every lane and include zero and half-zero keys:
// dummy bytes equal to the sought key must never supply a real partner.
void TestWideEqualityRequiresSamePartner() {
  auto compose = [](uint32_t s0, uint32_t s1, uint32_t s2, uint32_t s3) {
    return bs::KeyWords{(uint64_t{s1} << 32) | s0,
                        (uint64_t{s3} << 32) | s2};
  };
  const uint32_t victims[][4] = {
      {0x11111111u, 0x22222222u, 0x33333333u, 0x44444444u},
      {0, 0, 0x33333333u, 0x44444444u},
      {0x11111111u, 0x22222222u, 0, 0},
      {0, 0, 0, 0}};
  for (size_t key_bytes = 9; key_bytes <= bs::kMaxKeyBytes; ++key_bytes) {
    // TestSegmentedConflictIsRelaxed covers 16 bytes under the segment match.
    if (bs::kWideKeySegmentMatch && key_bytes == bs::kMaxKeyBytes) continue;
    bs::Layout layout;
    layout.key_bytes = key_bytes;
    auto table = bs::Table::Create(2, layout);
    for (const auto& seg : victims) {
      const bs::KeyWords victim = compose(seg[0], seg[1], seg[2], seg[3]);
      bs::KeyWords donors[4];
      for (size_t d = 0; d < 4; ++d) {
        uint32_t fields[4];
        for (size_t f = 0; f < 4; ++f)
          fields[f] = seg[f] ^ (f == d ? 0 : 0xA5A5A5A5u);
        donors[d] = compose(fields[0], fields[1], fields[2], fields[3]);
      }
      for (size_t rotation = 0; rotation < 64; ++rotation) {
        for (size_t e = 0; e < 64; ++e) {
          WriteKey(table.Bucket(0), e, key_bytes, victim);
          WriteKey(table.Bucket(1), e, key_bytes, victim);
        }
        uint64_t donor_bits[4], real = 0;
        const size_t base_slots[4] = {0, 7, 32, 63};
        for (size_t d = 0; d < 4; ++d) {
          const size_t e = (base_slots[d] + rotation) % 64;
          WriteKey(table.Bucket(0), e, key_bytes, donors[d]);
          donor_bits[d] = uint64_t{1} << e;
          real |= donor_bits[d];
        }
        const uint64_t target = uint64_t{1} << ((17 * rotation + 5) % 64);
        Expect(ReferenceDuplicateMask(table.Bucket(0), real, table.Bucket(1),
                                      target, key_bytes) == 0,
               "donors must be distinct from the complete sought key");
        Expect(bs::CrossBucketDuplicateMask(table.Bucket(0), real,
                                            table.Bucket(1), target,
                                            key_bytes) == 0,
               "segments from different partners must not match");
        // Every donor-class assignment, in multiple physical lane layouts.
        if (rotation % 8 == 0) {
          for (unsigned classes = 0; classes < 16; ++classes) {
            uint64_t tier = 0;
            for (size_t d = 0; d < 4; ++d)
              if ((classes >> d) & 1) tier |= donor_bits[d];
            uint64_t first_dup, carry_dup;
            bs::CrossBucketClassDuplicateMasks(
                table.Bucket(1), target, table.Bucket(0), real & ~tier,
                tier, key_bytes, &first_dup, &carry_dup);
            Expect(first_dup == 0 && carry_dup == 0,
                   "class masks must not combine different donor keys");
          }
        }
        uint64_t first_dup, carry_dup;
        bs::CrossBucketClassDuplicateMasks(
            table.Bucket(0), real, table.Bucket(1), target, 0, key_bytes,
            &first_dup, &carry_dup);
        Expect(first_dup == 0 && carry_dup == 0,
               "carry matches must also use a complete partner key");

        // An actual complete partner must be accepted, including lane 63.
        const uint64_t partner = uint64_t{1} << ((rotation + 11) % 64);
        Expect(bs::CrossBucketDuplicateMask(table.Bucket(0), real | partner,
                                            table.Bucket(1), target,
                                            key_bytes) == target,
               "a complete real partner must match");
        bs::CrossBucketClassDuplicateMasks(
            table.Bucket(1), target, table.Bucket(0), real, partner,
            key_bytes, &first_dup, &carry_dup);
        Expect(first_dup == target && carry_dup == 0,
               "only the complete tier partner may suppress first");
        bs::CrossBucketClassDuplicateMasks(
            table.Bucket(1), target, table.Bucket(0), partner, real,
            key_bytes, &first_dup, &carry_dup);
        Expect(first_dup == 0 && carry_dup == partner,
               "a complete carry partner must be marked in its own lane");

        // Self dedup keeps the earliest real full key. Donors do not qualify,
        // and a preceding dummy with the same bytes does not qualify either.
        const uint64_t duplicate = uint64_t{1} << ((rotation + 19) % 64);
        for (uint64_t self_real : {real | partner, real | partner | duplicate}) {
          Expect(bs::BucketSelfDuplicateMask(table.Bucket(0), self_real,
                                              key_bytes) ==
                     ReferenceSelfDuplicateMask(table.Bucket(0), self_real,
                                                key_bytes),
                 "self dedup must use one earlier real complete partner");
        }
      }
    }
  }
  std::puts("  wide equality requires the same complete partner");
}

// The wide-key conflict test is per 32-bit segment and the four answers are
// ANDed, so a slot whose segments each match a DIFFERENT partner is reported
// even though its key is present nowhere.  That is the documented ~2^-104
// event; building it by hand is the only way to pin the behaviour, and the same
// construction shows it takes all four -- three matching segments is not
// enough.  Runs only under kWideKeySegmentMatch.
void TestSegmentedConflictIsRelaxed() {
  const size_t key_bytes = bs::kMaxKeyBytes;
  bs::StashLayout layout;
  layout.key_bytes = key_bytes;
  layout.value_bytes = 4;
  layout.tag_bytes = 1;
  auto table = bs::Table::Create(2, layout.Base());

  // Four donors, each contributing one segment of the victim's key.
  const uint32_t seg[4] = {0x11111111u, 0x22222222u, 0x33333333u, 0x44444444u};
  auto compose = [&](uint32_t s0, uint32_t s1, uint32_t s2, uint32_t s3) {
    return bs::KeyWords{(uint64_t{s1} << 32) | s0, (uint64_t{s3} << 32) | s2};
  };
  const bs::KeyWords donors[4] = {
      compose(seg[0], 0xA0000001u, 0xA0000002u, 0xA0000003u),
      compose(0xB0000001u, seg[1], 0xB0000002u, 0xB0000003u),
      compose(0xC0000001u, 0xC0000002u, seg[2], 0xC0000003u),
      compose(0xD0000001u, 0xD0000002u, 0xD0000003u, seg[3])};
  const bs::KeyWords victim = compose(seg[0], seg[1], seg[2], seg[3]);

  for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
    WriteKey(table.Bucket(0), e, key_bytes, donors[e % 4]);
    WriteKey(table.Bucket(1), e, key_bytes, victim);
  }
  Expect(bs::CrossBucketDuplicateMask(table.Bucket(0), bs::LowMask64(4),
                                      table.Bucket(1), 1, key_bytes) == 1,
         "four donors covering all four segments must read as a conflict");
  // Drop the donor that owns segment 3: three segments no longer suffice.
  Expect(bs::CrossBucketDuplicateMask(table.Bucket(0), bs::LowMask64(3),
                                      table.Bucket(1), 1, key_bytes) == 0,
         "three of four matching segments must not read as a conflict");
  // The fused class kernel must preserve the segmented predicate, including
  // deliberate false positives, without borrowing donors from the other class.
  for (uint64_t tier = 0; tier < 16; ++tier) {
    uint64_t first_dup, carry_dup;
    bs::CrossBucketClassDuplicateMasks(
        table.Bucket(1), 1, table.Bucket(0), 15 ^ tier, tier, key_bytes,
        &first_dup, &carry_dup);
    Expect(first_dup == static_cast<uint64_t>(tier == 15),
           "wide class conflict must use four donors from the tier class");
    Expect(carry_dup == 0, "partial donor keys must not match the victim");
    bs::CrossBucketClassDuplicateMasks(
        table.Bucket(0), 15, table.Bucket(1), 1, 0, key_bytes,
        &first_dup, &carry_dup);
    Expect(first_dup == 0 && carry_dup == 1,
           "wide carry conflict must preserve the segmented relaxation");
  }
  std::printf("  segmented conflict relaxation ok\n");
}

// All widths, including adversarial fields, zero halves, dirty dummy slots,
// and aliased masks whose updates must take effect before the next destination.
// 16 bytes under kWideKeySegmentMatch is held to the segment predicate.
void TestDedupDestinationsExact() {
  std::mt19937_64 rng(0xD35716);
  for (size_t key_bytes : kKeyWidths) {
    bs::Layout layout;
    layout.key_bytes = key_bytes;
    auto table = bs::Table::Create(8, layout);
    for (unsigned trial = 0; trial < 100; ++trial) {
      for (size_t b = 0; b < 8; ++b) {
        for (size_t slot = 0; slot < 64; ++slot) {
          bs::KeyWords key{rng(), rng()};
          if (trial % 2) {
            key = {(rng() % 5) | ((rng() % 5) << 32),
                   (rng() % 5) | ((rng() % 5) << 32)};
          }
          if (trial % 5 == 0) key.w0 = 0;
          if (trial % 7 == 0) key.w1 = 0;
          WriteKey(table.Bucket(b), slot, key_bytes, key);
        }
      }
      const uint64_t source_real = trial % 7 == 0 ? 0 : rng();
      for (size_t count = 0; count <= 7; ++count) {
        uint8_t* destinations[7];
        uint64_t actual[7], expected[7], *masks[7];
        for (size_t q = 0; q < 7; ++q) {
          actual[q] = expected[q] = trial % 11 == 0 ? ~uint64_t{0} : rng();
          destinations[q] = table.Bucket(trial % 4 == 0 ? q / 2 + 1 : q + 1);
        }
        for (size_t q = 0; q < count; ++q) {
          const size_t index = trial % 3 == 0 ? q / 2 : q;
          masks[q] = &actual[index];
          expected[index] &= ~ReferenceBuildDuplicateMask(
              table.Bucket(0), source_real, destinations[q], expected[index],
              key_bytes);
        }
        bs::DedupBucketDestinations(table.Bucket(0), source_real,
                                     destinations, masks, count, key_bytes);
        for (size_t q = 0; q < 7; ++q)
          Expect(actual[q] == expected[q],
                 "destination dedup must match sequential scalar equality");
      }
    }
  }
  std::puts("  destination dedup agrees with sequential scalar equality");
}

// ---------------------------------------------------------------------------
// MergeSplitPairDedupStash
// ---------------------------------------------------------------------------

// The dedup MergeSplit must conserve exactly first's reals plus second's
// non-duplicate reals, split on the routed tag bit, with any surplus in the
// stash.
void TestMergeSplitPairDedupConserves() {
  bs::StashLayout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 4;
  layout.tag_bytes = 1;
  const size_t lines = layout.Base().EntryBytes();
  const size_t tag_line = layout.Base().TagLine(0);
  std::mt19937_64 rng(0xBEEF1234ull);

  for (int trial = 0; trial < 200; ++trial) {
    auto table = bs::Table::Create(2, layout.Base());
    OwnedLevelStashes stashes(1, 2, layout);
    const unsigned n_first = 20 + (trial % 30);
    const unsigned n_second = 20 + ((trial * 7) % 30);
    const uint64_t first_real = bs::LowMask64(n_first);
    const uint64_t second_real = bs::LowMask64(n_second);

    // Distinct keys within each bucket (that is the source-table invariant);
    // an overlapping window across the two so duplicates are frequent.
    std::vector<uint64_t> first_keys, second_keys;
    for (unsigned i = 0; i < n_first; ++i) first_keys.push_back(100 + i);
    for (unsigned i = 0; i < n_second; ++i) {
      second_keys.push_back(100 + i + (trial % 40));
    }
    for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
      // Dummy slots carry keys from the same range, so a wrong kernel would
      // drop live entries here.
      WriteKey(table.Bucket(0), e,
               layout.key_bytes, e < n_first ? first_keys[e] : 100 + (rng() % 80));
      WriteKey(table.Bucket(1), e, layout.key_bytes,
               e < n_second ? second_keys[e] : 100 + (rng() % 80));
      // Tag byte drives the split; give it a random bit 0.
      table.Bucket(0)[tag_line * bs::kBucketCapacity + e] =
          static_cast<uint8_t>(rng());
      table.Bucket(1)[tag_line * bs::kBucketCapacity + e] =
          static_cast<uint8_t>(rng());
    }
    std::map<uint64_t, unsigned> expected;  // key -> tag bit 0
    for (unsigned e = 0; e < n_first; ++e) {
      expected[first_keys[e]] =
          table.Bucket(0)[tag_line * bs::kBucketCapacity + e] & 1u;
    }
    for (unsigned e = 0; e < n_second; ++e) {
      if (expected.count(second_keys[e])) continue;  // duplicate: first wins
      expected[second_keys[e]] =
          table.Bucket(1)[tag_line * bs::kBucketCapacity + e] & 1u;
    }

    uint64_t masks[2] = {first_real, second_real};
    Expect(bs::MergeSplitPairDedupStash</*CheckOverflow=*/true>(
               table.Bucket(0), table.Bucket(1), &masks[0], &masks[1],
               layout.key_bytes, lines, tag_line, 0, stashes.slots[0]),
           "dedup MergeSplit overflowed its stash");

    std::map<uint64_t, unsigned> got;
    for (int b = 0; b < 2; ++b) {
      for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
        if (!((masks[b] >> e) & 1)) continue;
        const uint64_t key = ReadKey(table.Bucket(b), e, layout.key_bytes);
        Expect(got.emplace(key, static_cast<unsigned>(b)).second,
               "dedup MergeSplit left a duplicate key in the outputs");
      }
    }
    for (size_t sb = 0; sb < stashes.slots[0].num_buckets; ++sb) {
      for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
        if (!((stashes.slots[0].masks[sb] >> e) & 1)) continue;
        const uint64_t key =
            ReadKey(stashes.slots[0].Bucket(sb), e, layout.key_bytes);
        // A shed entry keeps its direction; the stash is checked for presence
        // only, so record it under its known direction.
        Expect(expected.count(key) != 0, "stash holds an unexpected key");
        Expect(got.emplace(key, expected[key]).second,
               "dedup MergeSplit duplicated a key into the stash");
      }
    }
    Expect(got.size() == expected.size(),
           "dedup MergeSplit lost or invented entries");
    for (const auto& kv : expected) {
      Expect(got[kv.first] == kv.second,
             "an entry was routed to the wrong direction");
    }
  }
  std::printf("  MergeSplitPairDedupStash conservation ok\n");
}

// ---------------------------------------------------------------------------
// The routing network
// ---------------------------------------------------------------------------

struct SourceInput {
  bs::StashLayout layout;
  unsigned levels = 7;         // log2(num_buckets)
  unsigned first_block = 1;    // log2 of the smallest source block, in buckets
  size_t per_bucket = 32;      // load 0.5
  uint64_t nonce_lo = 0x1234;
  uint64_t nonce_hi = 0x5678;
};

// Fills the block layout [S_0][S_1]...[S_(n-1)] with `per_bucket` entries per
// bucket.  Block index is stored in value byte 0 (0 = freshest), so the routed
// table shows which source a surviving copy came from.  `dup_rate` in [0, 1)
// makes a block re-use a key already placed in an OLDER block (never in the
// same block: a source table holds each key once).
std::vector<uint64_t> BuildSources(const SourceInput& in, uint8_t* data,
                                   uint64_t* masks, double dup_rate,
                                   std::vector<std::vector<uint64_t>>* by_block) {
  const size_t bucket_bytes = in.layout.BucketBytes();
  const unsigned blocks =
      bs::BinarySourceBlockCount(in.levels, in.first_block);
  std::mt19937_64 rng(0x5EED0011ull);
  std::vector<uint64_t> all_keys;
  by_block->assign(blocks, {});
  uint64_t next_key = 1;
  // Oldest block first, so a fresher block can re-use an older block's key.
  for (int j = static_cast<int>(blocks) - 1; j >= 0; --j) {
    size_t offset, size;
    bs::BinarySourceBlock(in.first_block, static_cast<unsigned>(j), &offset,
                          &size);
    std::unordered_set<uint64_t> in_block;
    // Keys of the OLDER blocks only: a source table holds each key once, so a
    // block may only re-use keys placed before it was started.
    const size_t older = all_keys.size();
    for (size_t b = 0; b < size; ++b) {
      uint8_t* bucket = data + (offset + b) * bucket_bytes;
      for (size_t e = 0; e < in.per_bucket; ++e) {
        uint64_t key;
        const bool reuse =
            older > 0 && std::generate_canonical<double, 32>(rng) < dup_rate;
        do {
          key = reuse ? all_keys[rng() % older] : next_key++;
        } while (in_block.count(key));
        in_block.insert(key);
        if (!reuse) all_keys.push_back(key);
        (*by_block)[j].push_back(key);
        WriteKey(bucket, e, in.layout.key_bytes, key);
        bucket[in.layout.key_bytes * bs::kBucketCapacity + e] =
            static_cast<uint8_t>(j);
        for (size_t vb = 1; vb < in.layout.value_bytes; ++vb) {
          bucket[(in.layout.key_bytes + vb) * bs::kBucketCapacity + e] =
              static_cast<uint8_t>(key >> (8 * vb));
        }
        bucket[in.layout.MetaOffset() * bs::kBucketCapacity + e] = 0;
      }
      // Dummy slots hold stale copies of real keys -- the case the dedup must
      // not be fooled by.
      for (size_t e = in.per_bucket; e < bs::kBucketCapacity; ++e) {
        WriteKey(bucket, e, in.layout.key_bytes,
                 all_keys.empty() ? 0 : all_keys[rng() % all_keys.size()]);
      }
      masks[offset + b] = bs::LowMask64(static_cast<unsigned>(in.per_bucket));
    }
  }
  return all_keys;
}

// Reordering only: with no duplicates anywhere, the intra-then-cross network
// must produce exactly the same bytes and masks as the flat butterfly (same
// MergeSplit set, same input state per MergeSplit), and the same set of shed
// residual keys.
void TestNetworkMatchesFlatButterfly(size_t per_bucket, size_t stash_buckets) {
  SourceInput in;
  in.layout.key_bytes = 8;
  in.layout.value_bytes = 4;
  in.layout.tag_bytes = 1;
  in.per_bucket = per_bucket;
  const size_t num_buckets = size_t{1} << in.levels;
  const size_t bucket_bytes = in.layout.BucketBytes();

  auto flat = bs::Table::Create(num_buckets, in.layout.Base());
  auto network = bs::Table::Create(num_buckets, in.layout.Base());
  std::vector<std::vector<uint64_t>> by_block;
  BuildSources(in, flat.data.get(), flat.masks.get(), 0.0, &by_block);
  std::memcpy(network.data.get(), flat.data.get(), num_buckets * bucket_bytes);
  std::memcpy(network.masks.get(), flat.masks.get(),
              num_buckets * sizeof(uint64_t));

  OwnedLevelStashes flat_stashes(in.levels, stash_buckets, in.layout);
  OwnedLevelStashes net_stashes(in.levels, stash_buckets, in.layout);
  bs::TableView flat_view = bs::View(flat);
  bs::TableView net_view = bs::View(network);
  bs::ComputeRoutingTags(flat_view, in.nonce_lo, in.nonce_hi, {}, in.levels);
  bs::ComputeRoutingTags(net_view, in.nonce_lo, in.nonce_hi, {}, in.levels);
  Expect(bs::ButterflyRouteStashCacheOblivious</*CheckOverflow=*/true>(
             flat_view, in.levels, flat_stashes.ptr()),
         "flat butterfly overflowed");
  Expect(bs::RouteBinarySourcesDedup</*CheckOverflow=*/true>(
             net_view, in.first_block, net_stashes.ptr()),
         "source network overflowed");

  Expect(std::memcmp(flat.data.get(), network.data.get(),
                     num_buckets * bucket_bytes) == 0,
         "source network produced different bucket bytes than the flat "
         "butterfly");
  Expect(std::memcmp(flat.masks.get(), network.masks.get(),
                     num_buckets * sizeof(uint64_t)) == 0,
         "source network produced different occupancy masks");
  // Stash slot assignment inside a bucket depends on the issue order, so the
  // stashes are compared per level as key SETS.
  for (unsigned s = 0; s < in.levels; ++s) {
    auto keys_of = [&](const bs::ResidualStash& stash) {
      std::multiset<uint64_t> keys;
      for (size_t b = 0; b < stash.num_buckets; ++b) {
        for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
          if ((stash.masks[b] >> e) & 1) {
            keys.insert(ReadKey(stash.Bucket(b), e, in.layout.key_bytes));
          }
        }
      }
      return keys;
    };
    Expect(keys_of(flat_stashes.slots[s]) == keys_of(net_stashes.slots[s]),
           "source network shed a different residual set");
  }
  std::printf(
      "  network == flat butterfly, %zu entries/bucket, %zu residuals shed\n",
      per_bucket, flat_stashes.Count());
}

// With duplicates planted across sources, what the network guarantees is:
//
//   1. the routed table holds each key AT MOST once, in the bucket its tag
//      selects;
//   2. the freshest copy of every key survives, in the table or in a stash;
//   3. a staler copy survives only if it was shed into a stash before it could
//      meet a fresher one -- two copies never both stay in the table.
//
// (3) is the load-bearing caveat of the whole scheme: shedding lets a stale
// copy escape the dedup, and the residual dump publishes it as a FRESHER level
// than the table just built, which inverts the freshness-by-level invariant the
// probe cascade relies on.  At the design load (0.5) nothing sheds, so the test
// asserts zero escapes there and only counts them in the deliberately
// overloaded run.  An escaped copy is resolved later, before publication, by
// the residual pool's freshness-ranked dedup and the second-chance offer,
// both tested below.
void TestNetworkKeepsFreshestCopy(size_t per_bucket, size_t stash_buckets) {
  for (double dup_rate : {0.25, 0.5}) {
    SourceInput in;
    in.layout.key_bytes = 8;
    in.layout.value_bytes = 4;
    in.layout.tag_bytes = 1;
    in.per_bucket = per_bucket;
    in.nonce_hi = 0x9911 + static_cast<uint64_t>(dup_rate * 100) + per_bucket;
    const size_t num_buckets = size_t{1} << in.levels;

    auto table = bs::Table::Create(num_buckets, in.layout.Base());
    std::vector<std::vector<uint64_t>> by_block;
    BuildSources(in, table.data.get(), table.masks.get(), dup_rate, &by_block);

    // key -> freshest (smallest) block index holding it.
    std::unordered_map<uint64_t, unsigned> freshest;
    for (unsigned j = 0; j < by_block.size(); ++j) {
      for (uint64_t key : by_block[j]) {
        auto it = freshest.find(key);
        if (it == freshest.end()) {
          freshest.emplace(key, j);
        } else {
          it->second = std::min(it->second, j);
        }
      }
    }

    OwnedLevelStashes stashes(in.levels, stash_buckets, in.layout);
    bs::TableView view = bs::View(table);
    bs::ComputeRoutingTags(view, in.nonce_lo, in.nonce_hi, {}, in.levels);
    Expect(bs::RouteBinarySourcesDedup</*CheckOverflow=*/true>(
               view, in.first_block, stashes.ptr()),
           "source network overflowed");

    // key -> markers of every surviving copy, and whether one is in the table.
    std::unordered_map<uint64_t, std::vector<unsigned>> survivors;
    std::unordered_set<uint64_t> in_table;
    for (size_t b = 0; b < num_buckets; ++b) {
      const uint8_t* bucket = table.Bucket(b);
      for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
        if (!((table.masks[b] >> e) & 1)) continue;
        const uint64_t key = ReadKey(bucket, e, in.layout.key_bytes);
        const unsigned marker =
            bucket[in.layout.key_bytes * bs::kBucketCapacity + e];
        Expect(in_table.insert(key).second,
               "a key survived twice in the routed table");
        survivors[key].push_back(marker);
        const uint64_t tag = microram::crypto::AesCtrTagU64WordsHost(
            in.nonce_lo, in.nonce_hi, key);
        Expect((tag & (num_buckets - 1)) == b,
               "a routed entry is not in the bucket its tag selects");
      }
    }
    size_t shed = 0;
    for (unsigned s = 0; s < in.levels; ++s) {
      const bs::ResidualStash& stash = stashes.slots[s];
      for (size_t b = 0; b < stash.num_buckets; ++b) {
        for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
          if (!((stash.masks[b] >> e) & 1)) continue;
          const uint64_t key =
              ReadKey(stash.Bucket(b), e, in.layout.key_bytes);
          survivors[key].push_back(
              stash.Bucket(b)[in.layout.key_bytes * bs::kBucketCapacity + e]);
          ++shed;
        }
      }
    }

    Expect(survivors.size() == freshest.size(),
           "the routed table plus stashes do not hold every distinct key");
    size_t escaped = 0;
    for (const auto& kv : freshest) {
      auto it = survivors.find(kv.first);
      Expect(it != survivors.end(), "a distinct key vanished");
      const unsigned best =
          *std::min_element(it->second.begin(), it->second.end());
      Expect(best == kv.second,
             "the freshest copy of a key did not survive anywhere");
      escaped += it->second.size() - 1;
    }
    Expect(escaped <= shed, "more escapes than shed entries");
    if (shed == 0) {
      Expect(escaped == 0, "a duplicate survived without any shedding");
    }
    std::printf(
        "  %zu entries/bucket, dup_rate %.2f: %zu distinct keys of %zu slots, "
        "%zu shed, %zu stale copies escaped the dedup\n",
        per_bucket, dup_rate, freshest.size(), num_buckets * in.per_bucket,
        shed, escaped);
  }
}

// ---------------------------------------------------------------------------
// Pool freshness rank
// ---------------------------------------------------------------------------

// The pool dedup is the ONLY thing that resolves two shed copies of one key
// (a dedup by slot position after routing would not do: slot position is not
// a freshness order).  It runs before the scatter, while the copies are still in the stashes whose
// index says which source block they came from.  What must hold:
//
//   1. a staler slot loses every key a fresher slot holds;
//   2. a fresher slot is never touched;
//   3. EQUAL ranks are left alone -- those slots draw from one source table, so
//      a shared key there would be a bug elsewhere, not a freshness question;
//   4. a DUMMY of the fresher slot never drops a real entry of the staler one.
// A fourth property the SCHEDULER needs: the phase is sliced over pair index,
// so any cut must give the same answer.  It does, and not by accident -- a slot
// loses a key only to a STRICTLY fresher one, so the freshest holder never
// loses it whatever order the pairs run in, and every other holder meets that
// slot in some pair.  This checks the argument rather than trusting it.
void TestResidualPoolDedup() {
  bs::StashLayout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 4;
  layout.tag_bytes = 2;
  const uint8_t rank[3] = {0, 1, 1};
  // Slot 0 is the fresher class; slots 1 and 2 share the staler one.  Key 6 is
  // in both staler slots (equal rank, untouched) and key 7 is only a DUMMY of
  // slot 0 (so the staler real copies must survive).
  const std::vector<std::vector<uint64_t>> real = {
      {1, 2, 3}, {2, 4, 6}, {3, 5, 2, 6, 7}};
  const std::vector<std::vector<uint64_t>> dummy = {{7}, {}, {}};

  auto run = [&](size_t slice) {
    OwnedLevelStashes pool(3, 1, layout);
    for (unsigned s = 0; s < 3; ++s) {
      uint8_t* bucket = pool.slots[s].Bucket(0);
      size_t e = 0;
      for (uint64_t key : real[s]) {
        WriteKey(bucket, e, layout.key_bytes, key);
        pool.slots[s].masks[0] |= uint64_t{1} << e;
        ++e;
      }
      for (uint64_t key : dummy[s]) {
        WriteKey(bucket, e, layout.key_bytes, key);  // occupancy left clear
        ++e;
      }
    }
    std::vector<bs::ResidualStash*> ptrs = {&pool.slots[0], &pool.slots[1],
                                            &pool.slots[2]};
    const size_t pairs = bs::ResidualPoolDedupPairs(
        ptrs.data(), rank, ptrs.size(), /*drain_only_slots=*/0,
        bs::ResidualDedupWindow::kFull);
    for (size_t at = 0; at < pairs; at += slice) {
      bs::ResidualPoolDedupRange(ptrs.data(), rank, ptrs.size(),
                                 /*drain_only_slots=*/0,
                                 bs::ResidualDedupWindow::kFull,
                                 layout.key_bytes, at,
                                 std::min(at + slice, pairs));
    }
    std::vector<std::set<uint64_t>> out(3);
    for (unsigned s = 0; s < 3; ++s) {
      for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
        if ((pool.slots[s].masks[0] >> e) & 1) {
          out[s].insert(ReadKey(pool.slots[s].Bucket(0), e, layout.key_bytes));
        }
      }
    }
    return out;
  };

  const std::vector<std::set<uint64_t>> whole = run(64);
  Expect(whole[0] == std::set<uint64_t>({1, 2, 3}),
         "the pool dedup cleared entries from the FRESHER slot");
  Expect(whole[1] == std::set<uint64_t>({4, 6}),
         "the pool dedup did not resolve slot 1 against the fresher slot");
  Expect(whole[2] == std::set<uint64_t>({5, 6, 7}),
         "the pool dedup did not resolve slot 2 against the fresher slot");
  for (size_t slice = 1; slice <= 9; ++slice) {
    Expect(run(slice) == whole,
           "slicing the pool dedup by pair index changed its answer");
  }
  std::printf("  pool rank dedup: staler slots lose the fresher slot's keys, "
              "equal ranks and dummy matches untouched, every slicing agrees\n");
}

// The same three properties with MORE THAN ONE BUCKET per stash, which is what
// the stash schedule produces past a few million accesses
// (PlanStashBuckets returns up to kStashCapMaxBuckets).  Two things only appear
// here:
//
//   1. a duplicate whose two copies sit in DIFFERENT bucket indices of the two
//      slots still meets -- the phase is all-pairs over buckets, not a
//      bucket-aligned zip; and
//   2. the pair space is the bucket product of each ELIGIBLE slot pair, so a
//      slicing that cuts inside one slot pair has to give the same answer.  It does
//      because each unit only clears bits of one staler bucket's occupancy
//      word, which is idempotent and order-independent.
void TestResidualPoolDedupMultiBucket() {
  bs::StashLayout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 4;
  layout.tag_bytes = 2;

  auto check = [&](size_t buckets) {
    const uint8_t rank[3] = {0, 1, 1};
    std::mt19937_64 rng(0xB0CCE7 + buckets);
    // Keys 1..40 spread over the fresher slot's buckets; the two staler slots
    // hold a mix of those (which must die) and their own (which must live), and
    // the placement is randomized so copies rarely share a bucket index.
    std::vector<std::vector<std::vector<uint64_t>>> keys(3);
    std::set<uint64_t> fresher_keys;
    for (unsigned s = 0; s < 3; ++s) keys[s].assign(buckets, {});
    for (uint64_t k = 1; k <= 40; ++k) {
      keys[0][rng() % buckets].push_back(k);
      fresher_keys.insert(k);
    }
    std::set<uint64_t> staler_expect[2];
    for (unsigned s = 1; s < 3; ++s) {
      for (uint64_t k = 1; k <= 60; ++k) {
        if ((rng() & 1) == 0) continue;
        keys[s][rng() % buckets].push_back(k);
        if (fresher_keys.count(k) == 0) staler_expect[s - 1].insert(k);
      }
    }

    auto run = [&](size_t slice) {
      OwnedLevelStashes pool(3, buckets, layout);
      for (unsigned s = 0; s < 3; ++s) {
        for (size_t b = 0; b < buckets; ++b) {
          uint8_t* bucket = pool.slots[s].Bucket(b);
          size_t e = 0;
          for (uint64_t key : keys[s][b]) {
            WriteKey(bucket, e, layout.key_bytes, key);
            pool.slots[s].masks[b] |= uint64_t{1} << e;
            ++e;
          }
        }
      }
      std::vector<bs::ResidualStash*> ptrs = {&pool.slots[0], &pool.slots[1],
                                              &pool.slots[2]};
      const size_t pairs = bs::ResidualPoolDedupPairs(
          ptrs.data(), rank, ptrs.size(), /*drain_only_slots=*/0,
          bs::ResidualDedupWindow::kFull);
      // Ranks {0, 1, 1}: the eligible pairs are slot 0 against each staler
      // slot, `buckets` x `buckets` each; the equal-rank pair is no unit.
      Expect(pairs == 2 * buckets * buckets,
             "the pool pair space is not the eligible slot pairs' bucket "
             "product");
      for (size_t at = 0; at < pairs; at += slice) {
        bs::ResidualPoolDedupRange(ptrs.data(), rank, ptrs.size(),
                                   /*drain_only_slots=*/0,
                                   bs::ResidualDedupWindow::kFull,
                                   layout.key_bytes, at,
                                   std::min(at + slice, pairs));
      }
      std::vector<std::set<uint64_t>> out(3);
      for (unsigned s = 0; s < 3; ++s) {
        for (size_t b = 0; b < buckets; ++b) {
          for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
            if ((pool.slots[s].masks[b] >> e) & 1) {
              out[s].insert(
                  ReadKey(pool.slots[s].Bucket(b), e, layout.key_bytes));
            }
          }
        }
      }
      return out;
    };

    const std::vector<std::set<uint64_t>> whole = run(9 * buckets * buckets);
    Expect(whole[0] == fresher_keys,
           "the multi-bucket pool dedup cleared the FRESHER slot");
    Expect(whole[1] == staler_expect[0] && whole[2] == staler_expect[1],
           "a duplicate in a different BUCKET index of the fresher slot "
           "survived the pool dedup");
    for (size_t slice : {size_t{1}, size_t{2}, size_t{5}, size_t{buckets},
                         size_t{3 * buckets}, size_t{7 * buckets + 1}}) {
      Expect(run(slice) == whole,
             "slicing the multi-bucket pool dedup changed its answer");
    }
    std::printf("  pool rank dedup, %zu buckets/stash: %zu eligible bucket "
                "pairs, cross-bucket duplicates resolved, every slicing "
                "agrees\n",
                buckets, 2 * buckets * buckets);
  };

  check(2);
  check(bs::kMaxResidualStashBuckets);
}

// The EMISSION WINDOWS of the residual pool dedup.
//
// A merged chain step deduplicates its pool twice, bracketing the cross level,
// and each emission is planned over the only rectangle it can act on rather
// than over the whole pool square:
//
//   - kSweptOnly before the scatter, when the drain-only cross shed is still
//     publicly empty, so tier x carry is everything there is to do;
//   - kDrainOnly after the cross level has filled that shed, when the swept
//     slots' content lives in the range table and only the shed still drains
//     from its stash.
//
// What has to hold is that this pair of windows leaves the pool in exactly the
// state two full squares would have, which is what this checks against the
// literal reference schedule -- same pool, same interleaved cross-level fill,
// kFull both times.  The layout is the production one: slot 0 the drain-only
// shed (rank 1), slot 1 the carry (rank 1), slot 2 the borrowed tier (rank 0).
void TestResidualPoolDedupWindows() {
  bs::StashLayout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 4;
  layout.tag_bytes = 2;
  const uint8_t rank[3] = {1, 1, 0};

  // The carry and the shed each hold copies of tier keys (which must go) and
  // keys of their own (which must not).  Key 9 sits in both rank-1 slots: an
  // equal-rank pair, untouched by either window.
  const std::vector<uint64_t> carry = {2, 3, 9, 11};
  const std::vector<uint64_t> shed = {3, 5, 9, 13};
  const std::vector<uint64_t> tier = {2, 3, 5, 7};

  const auto fill = [&](bs::ResidualStash* stash,
                        const std::vector<uint64_t>& keys) {
    size_t e = 0;
    for (uint64_t key : keys) {
      WriteKey(stash->Bucket(0), e, layout.key_bytes, key);
      stash->masks[0] |= uint64_t{1} << e;
      ++e;
    }
  };
  const auto contents = [&](const OwnedLevelStashes& pool) {
    std::vector<std::set<uint64_t>> out(3);
    for (unsigned sl = 0; sl < 3; ++sl) {
      for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
        if ((pool.slots[sl].masks[0] >> e) & 1) {
          out[sl].insert(ReadKey(pool.slots[sl].Bucket(0), e,
                                 layout.key_bytes));
        }
      }
    }
    return out;
  };

  // One run of the schedule: the first emission with the shed still empty, the
  // cross level filling it, then the second emission.  `slice` cuts both.
  const auto run = [&](bs::ResidualDedupWindow first,
                       bs::ResidualDedupWindow second, size_t slice,
                       size_t* planned) {
    OwnedLevelStashes pool(3, 1, layout);
    fill(&pool.slots[1], carry);
    fill(&pool.slots[2], tier);
    std::vector<bs::ResidualStash*> ptrs = {&pool.slots[0], &pool.slots[1],
                                            &pool.slots[2]};
    const auto emit = [&](bs::ResidualDedupWindow window) {
      const size_t pairs = bs::ResidualPoolDedupPairs(
          ptrs.data(), rank, ptrs.size(), /*drain_only_slots=*/1, window);
      for (size_t at = 0; at < pairs; at += slice) {
        bs::ResidualPoolDedupRange(ptrs.data(), rank, ptrs.size(),
                                   /*drain_only_slots=*/1, window,
                                   layout.key_bytes, at,
                                   std::min(at + slice, pairs));
      }
      return pairs;
    };
    const size_t first_pairs = emit(first);
    fill(&pool.slots[0], shed);  // the cross level, between the emissions
    *planned = first_pairs + emit(second);
    return contents(pool);
  };

  size_t reference_pairs = 0, windowed_pairs = 0, sliced_pairs = 0;
  const std::vector<std::set<uint64_t>> reference =
      run(bs::ResidualDedupWindow::kFull, bs::ResidualDedupWindow::kFull, 64,
          &reference_pairs);
  const std::vector<std::set<uint64_t>> windowed =
      run(bs::ResidualDedupWindow::kSweptOnly,
          bs::ResidualDedupWindow::kDrainOnly, 64, &windowed_pairs);
  Expect(reference[2] == std::set<uint64_t>({2, 3, 5, 7}),
         "an emission cleared the fresher tier");
  Expect(reference[1] == std::set<uint64_t>({9, 11}),
         "the reference schedule did not clear the carry against the tier");
  Expect(reference[0] == std::set<uint64_t>({9, 13}),
         "the reference schedule did not clear the shed against the tier");
  Expect(windowed == reference,
         "the bracketed windows left the pool in a different state than two "
         "full squares");
  Expect(windowed_pairs < reference_pairs,
         "the bracketed windows did not plan fewer pairs than two full "
         "squares");
  for (size_t slice = 1; slice <= 10; ++slice) {
    Expect(run(bs::ResidualDedupWindow::kSweptOnly,
               bs::ResidualDedupWindow::kDrainOnly, slice,
               &sliced_pairs) == windowed,
           "slicing a windowed pool dedup changed its answer");
  }

  // The phase gate is window-aware too: with the tier dropped from the window
  // there is no surviving pair, so the planner emits nothing.
  Expect(bs::ResidualPoolDedupNeeded(rank, 3, /*drain_only_slots=*/1,
                                     bs::ResidualDedupWindow::kDrainOnly),
         "kDrainOnly over a tier and a shed found no live pair");
  const uint8_t uniform[3] = {1, 1, 1};
  Expect(!bs::ResidualPoolDedupNeeded(uniform, 3, /*drain_only_slots=*/1,
                                      bs::ResidualDedupWindow::kFull),
         "a uniform-rank pool still asked for a pool dedup");
  const uint8_t tier_is_drain_only[3] = {0, 1, 1};
  Expect(!bs::ResidualPoolDedupNeeded(tier_is_drain_only, 3,
                                      /*drain_only_slots=*/1,
                                      bs::ResidualDedupWindow::kSweptOnly),
         "kSweptOnly asked for a dedup over a uniform-rank swept suffix");

  std::printf("  pool dedup windows: swept-then-drain-only agrees with two "
              "full squares in %zu pairs instead of %zu, every slicing "
              "agrees\n",
              windowed_pairs, reference_pairs);
}

// The pool contract, as a predicate with a NEGATIVE case.
//
// ResidualPoolDedupRange resolves pairs of DIFFERENT rank and skips equal ones,
// on the grounds that equal rank means "one source table" and a source table
// holds each key at most once.  That is what makes the pool duplicate-free,
// and nothing downstream repairs a violation (a stacked range table can place
// two equal-rank copies side by side).  So the contract is asserted at both
// entry points -- and an assertion nobody has watched fail is worth nothing,
// which is why this test makes it fail on purpose.
void TestResidualPoolEqualRankContract() {
  bs::StashLayout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 4;
  layout.tag_bytes = 2;
  const size_t kb = layout.key_bytes;

  // Three slots of two buckets each, initially all empty.
  OwnedLevelStashes stashes(3, 2, layout);
  bs::ResidualStash* pool[3] = {&stashes.slots[0], &stashes.slots[1],
                                &stashes.slots[2]};
  auto put = [&](unsigned slot, size_t bucket, unsigned e, uint64_t key,
                 bool real) {
    WriteKey(stashes.slots[slot].Bucket(bucket), e, kb, key);
    if (real) stashes.slots[slot].masks[bucket] |= uint64_t{1} << e;
  };
  auto disjoint = [&](const uint8_t* rank) {
    return bs::ResidualPoolEqualRanksDisjoint(pool, rank, 3, kb);
  };

  const uint8_t all_equal[3] = {0, 0, 0};
  const uint8_t all_distinct[3] = {0, 1, 2};

  Expect(disjoint(all_equal), "an empty pool was called non-disjoint");

  // Distinct keys everywhere: the well-formed case, at every ranking.
  put(0, 0, 0, 100, true);
  put(0, 1, 0, 101, true);
  put(1, 0, 0, 200, true);
  put(2, 1, 3, 300, true);
  Expect(disjoint(all_equal), "a pool of distinct keys was called non-disjoint");
  Expect(disjoint(all_distinct),
         "a pool of distinct keys was called non-disjoint at distinct ranks");

  // A DUMMY slot holding a repeated key is not a violation: the intersect reads
  // occupancy, and a dummy slot's bytes are don't-care.
  put(1, 1, 5, 100, /*real=*/false);
  Expect(disjoint(all_equal),
         "a dummy slot holding a live key was called a violation");

  // THE NEGATIVE CASE: two slots of EQUAL rank holding one key -- the shape a
  // stacked range table cannot absorb.
  put(1, 1, 6, 100, /*real=*/true);
  Expect(!disjoint(all_equal),
         "two equal-rank stashes sharing a key were accepted");
  // At DIFFERENT ranks the same pool is fine: that pair is the dedup's job, and
  // this predicate deliberately says nothing about it.
  Expect(disjoint(all_distinct),
         "a cross-rank duplicate was reported as an equal-rank violation");

  // A stash that duplicates a key across its OWN buckets is a violation too --
  // the other half of "a source table holds each key at most once".
  OwnedLevelStashes solo(1, 2, layout);
  bs::ResidualStash* one[1] = {&solo.slots[0]};
  const uint8_t rank0[1] = {0};
  WriteKey(solo.slots[0].Bucket(0), 0, kb, 7);
  solo.slots[0].masks[0] |= 1;
  WriteKey(solo.slots[0].Bucket(1), 9, kb, 8);
  solo.slots[0].masks[1] |= uint64_t{1} << 9;
  Expect(bs::ResidualPoolEqualRanksDisjoint(one, rank0, 1, kb),
         "a stash with distinct keys was called non-disjoint");
  WriteKey(solo.slots[0].Bucket(1), 10, kb, 7);
  solo.slots[0].masks[1] |= uint64_t{1} << 10;
  Expect(!bs::ResidualPoolEqualRanksDisjoint(one, rank0, 1, kb),
         "a stash holding one key in two of its own buckets was accepted");

  // ...and a key repeated INSIDE one bucket.  The cross-bucket intersect
  // cannot judge a bucket against itself, so a checker that only compares
  // distinct buckets would miss this shape; the predicate must catch it.
  OwnedLevelStashes same_bucket(1, 1, layout);
  bs::ResidualStash* in_one[1] = {&same_bucket.slots[0]};
  WriteKey(same_bucket.slots[0].Bucket(0), 2, kb, 11);
  same_bucket.slots[0].masks[0] |= uint64_t{1} << 2;
  WriteKey(same_bucket.slots[0].Bucket(0), 5, kb, 12);
  same_bucket.slots[0].masks[0] |= uint64_t{1} << 5;
  WriteKey(same_bucket.slots[0].Bucket(0), 9, kb, 11);  // a dummy copy
  Expect(bs::ResidualPoolEqualRanksDisjoint(in_one, rank0, 1, kb),
         "distinct keys in one bucket (plus a dummy copy) were called a "
         "violation");
  same_bucket.slots[0].masks[0] |= uint64_t{1} << 9;  // now real
  Expect(!bs::ResidualPoolEqualRanksDisjoint(in_one, rank0, 1, kb),
         "a key held twice in one bucket was accepted");

  std::printf("  residual pool contract: equal-rank, intra-stash and "
              "intra-bucket duplicates all rejected, cross-rank ones and "
              "dummy slots ignored\n");
}

// ---------------------------------------------------------------------------
// The range plan, and stacking when one range table is too small
// ---------------------------------------------------------------------------

// A literal transcription of the single-group range planner and of its
// feasibility predicate (the pool fits one range table of 2^range_bits
// buckets).  PlanResidualRange must reproduce it exactly wherever it is
// feasible, and STACK several sub-tables (groups) exactly where it is not.
// It is written out independently rather than expressed through
// PlanResidualRange so that it is a separate statement of that geometry.
// ("Legacy" in the identifiers below means this single-group reference.)
struct LegacyRangePlan {
  unsigned range_bits = 0;
  unsigned index_bits = 0;
  size_t range_buckets = 0;
  size_t scatter_per_bucket = bs::kResidualsPerRange;
  bool feasible = true;  // the single-group feasibility predicate
};

LegacyRangePlan LegacyPlanResidualRange(size_t pool_buckets,
                                        unsigned main_levels) {
  unsigned bits = 0;
  while ((size_t{1} << bits) < pool_buckets * bs::kResidualsPerRange) ++bits;
  if (bits > main_levels) bits = main_levels;
  LegacyRangePlan p;
  p.range_bits = bits;
  p.index_bits = main_levels - bits;
  p.range_buckets = size_t{1} << bits;
  size_t per = bs::kResidualsPerRange;
  while (per < bs::kBucketCapacity &&
         pool_buckets * (bs::kBucketCapacity / per) > p.range_buckets) {
    per *= 2;
  }
  p.scatter_per_bucket = per;
  p.feasible = pool_buckets == 0 ||
               pool_buckets * (bs::kBucketCapacity / per) <= p.range_buckets;
  return p;
}

// What the planner has to satisfy over the whole (pool, main_levels) grid:
//
//   0. main_levels <= kResidualDirectMaxLevels with a nonempty pool is the
//      DIRECT regime: the table is the
//      pool itself, nothing routes (no route means no route-overflow event,
//      which is the whole point at these geometries), and the sweep's
//      index_bits match does all of the selection;
//   1. the pool fits -- every pool bucket has somewhere to be scattered;
//   2. range_buckets is exactly `groups` sub-tables of 2^range_bits;
//   3. the ranges still COVER the main table: 2^range_bits << index_bits is
//      2^main_levels, so every main bucket has a range to pair with;
//   4. stacking implies the degenerate geometry the sweep relies on --
//      index_bits == 0 (one range per main bucket, tag match a no-op) and a
//      saturated scatter;
//   5. an empty pool has one padding group that clears reused scratch;
//   6. AGREEMENT WITH THE REFERENCE, above the direct threshold for nonempty
//      pools: groups == 1 on exactly the pairs the single-group predicate
//      accepts, and on those pairs the plan equals the reference plan.
void TestResidualRangePlanStacks() {
  size_t stacked = 0, flat = 0, direct = 0, empty = 0;
  for (unsigned main_levels = 0; main_levels <= 14; ++main_levels) {
    for (size_t pool = 0; pool <= 96; ++pool) {
      const bs::ResidualRangePlan p = bs::PlanResidualRange(pool, main_levels);
      const size_t sub = size_t{1} << p.range_bits;
      const size_t fanout = bs::kBucketCapacity / p.scatter_per_bucket;
      Expect(p.groups >= 1, "a range plan has no groups");
      Expect(pool * fanout <= p.range_buckets,
             "the scatter does not fit inside the range table");
      Expect(fanout <= p.range_buckets && p.range_buckets % fanout == 0,
             "range buckets do not form complete scatter groups");
      Expect(p.range_buckets == p.groups * sub,
             "range_buckets is not groups sub-tables");
      Expect((sub << p.index_bits) == (size_t{1} << main_levels),
             "the ranges no longer cover the main table");
      if (pool == 0) {
        Expect(p.range_buckets == 1 && fanout == 1 && p.range_bits == 0,
               "empty pool does not have one clearing group");
        ++empty;
        continue;
      }
      if (main_levels <= bs::kResidualDirectMaxLevels) {
        Expect(p.range_bits == 0 && p.index_bits == main_levels,
               "a direct plan still routes");
        Expect(p.groups == pool && p.range_buckets == pool,
               "a direct plan's table is not the pool itself");
        Expect(p.scatter_per_bucket == bs::kBucketCapacity,
               "a direct plan's scatter is not wholesale");
        ++direct;
        continue;
      }
      const LegacyRangePlan l = LegacyPlanResidualRange(pool, main_levels);
      if (p.groups > 1) {
        Expect(p.index_bits == 0,
               "a stacked range plan does not have one range per main bucket");
        Expect(p.scatter_per_bucket == bs::kBucketCapacity,
               "a stacked range plan did not saturate the scatter first");
        ++stacked;
      } else {
        ++flat;
      }
      Expect((p.groups == 1) == l.feasible,
             "stacking does not fire on exactly the pairs the single-group "
             "reference refuses");
      if (!l.feasible) continue;
      Expect(p.range_bits == l.range_bits && p.index_bits == l.index_bits &&
                 p.range_buckets == l.range_buckets &&
                 p.scatter_per_bucket == l.scatter_per_bucket,
             "a feasible pair's range plan changed");
    }
  }
  Expect(stacked != 0, "the grid never reached the stacking regime");
  Expect(direct != 0, "the grid never reached the direct regime");
  std::printf("  range plans: %zu unstacked (bit-identical to the old plan), "
              "%zu stacked (were construction-time refusals), %zu direct "
              "(unrouted, no overflow event), %zu empty (one clearing group)\n",
              flat, stacked, direct, empty);
}

// The range table is sized from the pool's capacity, not from a bound on the
// number of shed entries: shed events across the levels of one butterfly are
// positively correlated, so a per-level tail bound summed as if independent
// would not be sound.

// ---------------------------------------------------------------------------
// Residual second chance
// ---------------------------------------------------------------------------

// A multi-group sweep, sliced -- the DIRECT shape at main_levels <=
// kResidualDirectMaxLevels.  The unit space is (main bucket, group) b-major, so an
// arbitrary [begin, end) is legal only because a unit reads and writes just
// main[b] and range[g * 2^range_bits + b] and the groups of one b stay in
// issue order.  This runs the same pass at several slice widths and demands
// the tables come out BYTE for byte identical -- which is what lets the
// rebuild cut the phase at any slice boundary.  In the direct shape
// the candidates of one range bucket span every destination and the sweep's
// index_bits match does the selection, so this is also the direct offer's
// content coverage under a rule that fires.
//
// The pool deliberately re-offers keys the main table already holds, spread
// across groups, so the rule actually fires and the sweep has real work to
// resolve rather than an empty candidate set at every unit.
void TestStackedSweepSlicingAgrees(unsigned main_levels, size_t pool_buckets,
                                   size_t n_residuals, size_t dup_every,
                                   uint64_t seed) {
  bs::StashLayout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 4;
  layout.tag_bytes = 2;
  const size_t num_buckets = size_t{1} << main_levels;
  const uint64_t nonce_lo = 0xA11Cull + seed;
  const uint64_t nonce_hi = 0xB0B0ull + seed;

  const bs::ResidualRangePlan plan =
      bs::PlanResidualRange(pool_buckets, main_levels);
  Expect(plan.groups > 1, "this shape was supposed to be multi-group");
  Expect((main_levels <= bs::kResidualDirectMaxLevels) ==
             (plan.range_bits == 0),
         "the direct regime does not fire exactly at its threshold");

  // The pool: slots of at most kMaxResidualStashBuckets buckets, filled round
  // robin so every sub-table gets entries.
  const size_t per_slot = bs::kMaxResidualStashBuckets;
  const size_t num_slots = (pool_buckets + per_slot - 1) / per_slot;
  OwnedLevelStashes stashes(static_cast<unsigned>(num_slots), per_slot, layout);
  std::vector<bs::ResidualStash*> pool(num_slots);
  for (size_t s = 0; s < num_slots; ++s) {
    stashes.slots[s].num_buckets =
        std::min(per_slot, pool_buckets - s * per_slot);
    pool[s] = &stashes.slots[s];
  }

  auto main = bs::Table::Create(num_buckets, layout.Base());
  std::memset(main.data.get(), 0, num_buckets * layout.BucketBytes());
  std::mt19937_64 rng(seed);
  std::vector<size_t> fill(num_buckets, 0);
  for (size_t i = 0; i < n_residuals; ++i) {
    const uint64_t key = 1 + rng() % 0xFFFFFFFFull;
    const size_t flat = i % pool_buckets;
    const size_t e = i / pool_buckets;
    Expect(e < bs::kBucketCapacity, "the residual pool is overfull");
    bs::ResidualStash& slot = stashes.slots[flat / per_slot];
    const size_t b = flat % per_slot;
    WriteKey(slot.Bucket(b), e, layout.key_bytes, key);
    slot.masks[b] |= uint64_t{1} << e;
    // Every dup_every-th key also sits in the main table, in the bucket its tag
    // selects, so the sweep's intersect has something to resolve.
    if (dup_every != 0 && i % dup_every == 0) {
      const uint64_t tag =
          microram::crypto::AesCtrTagU64WordsHost(nonce_lo, nonce_hi, key);
      const size_t mb = static_cast<size_t>(tag) & (num_buckets - 1);
      if (fill[mb] < bs::kBucketCapacity) {
        WriteKey(main.Bucket(mb), fill[mb], layout.key_bytes, key);
        main.masks[mb] |= uint64_t{1} << fill[mb];
        ++fill[mb];
      }
    }
  }
  bs::ComputeRoutingTags(bs::View(main), nonce_lo, nonce_hi, {}, 0);

  auto range = bs::Table::Create(plan.range_buckets, layout.Base());
  std::memset(range.data.get(), 0, plan.range_buckets * layout.BucketBytes());
  // A direct plan's range table: the pool itself, scattered and tagged.
  Expect(plan.range_bits == 0, "this fixture builds only a direct plan");
  bs::ScatterResidualPoolRange(pool.data(), num_slots, bs::View(range), plan,
                               0, bs::ResidualScatterGroups(bs::View(range),
                                                            plan));
  bs::ComputeRoutingTags(bs::View(range), nonce_lo, nonce_hi, {}, 0);

  // Snapshot both tables, then replay the sweep at every slicing from the same
  // start state.
  const size_t main_bytes = num_buckets * layout.BucketBytes();
  const size_t range_bytes = plan.range_buckets * layout.BucketBytes();
  const std::vector<uint8_t> main0(main.data.get(),
                                   main.data.get() + main_bytes);
  const std::vector<uint64_t> main_masks0(main.masks.get(),
                                          main.masks.get() + num_buckets);
  const std::vector<uint8_t> range0(range.data.get(),
                                    range.data.get() + range_bytes);
  const std::vector<uint64_t> range_masks0(
      range.masks.get(), range.masks.get() + plan.range_buckets);
  const size_t units = num_buckets * plan.groups;
  const size_t lines = layout.Base().PayloadLines();

  std::vector<uint8_t> ref_main, ref_range;
  std::vector<uint64_t> ref_main_masks, ref_range_masks;
  const size_t widths[] = {units, 1, 2, 3, 5, 7};
  for (size_t width : widths) {
    std::memcpy(main.data.get(), main0.data(), main_bytes);
    std::memcpy(main.masks.get(), main_masks0.data(),
                num_buckets * sizeof(uint64_t));
    std::memcpy(range.data.get(), range0.data(), range_bytes);
    std::memcpy(range.masks.get(), range_masks0.data(),
                plan.range_buckets * sizeof(uint64_t));
    for (size_t at = 0; at < units; at += width) {
      bs::ResidualSecondChanceSweepRange<bs::ResidualDedupRule::kResidualWins>(
          bs::View(main), bs::View(range), plan, lines, at,
          std::min(at + width, units));
    }
    if (width == units) {
      ref_main.assign(main.data.get(), main.data.get() + main_bytes);
      ref_main_masks.assign(main.masks.get(), main.masks.get() + num_buckets);
      ref_range.assign(range.data.get(), range.data.get() + range_bytes);
      ref_range_masks.assign(range.masks.get(),
                             range.masks.get() + plan.range_buckets);
      continue;
    }
    Expect(std::memcmp(main.data.get(), ref_main.data(), main_bytes) == 0 &&
               std::equal(ref_main_masks.begin(), ref_main_masks.end(),
                          main.masks.get()),
           "slicing a stacked sweep changed the main table");
    Expect(std::memcmp(range.data.get(), ref_range.data(), range_bytes) == 0 &&
               std::equal(ref_range_masks.begin(), ref_range_masks.end(),
                          range.masks.get()),
           "slicing a stacked sweep changed the leftovers");
  }

  // The stacked pass still puts every entry where its tag says, once.
  size_t absorbed = 0, left = 0;
  std::unordered_map<uint64_t, unsigned> seen;
  for (size_t b = 0; b < num_buckets; ++b) {
    absorbed += bs::Popcount64(ref_main_masks[b]);
    for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
      if (!((ref_main_masks[b] >> e) & 1)) continue;
      const uint64_t key = ReadKey(main.Bucket(b), e, layout.key_bytes);
      Expect(seen.emplace(key, 0).second,
             "a stacked sweep put a key in the main table twice");
      const uint64_t tag =
          microram::crypto::AesCtrTagU64WordsHost(nonce_lo, nonce_hi, key);
      Expect((static_cast<size_t>(tag) & (num_buckets - 1)) == b,
             "a stacked sweep put an entry in the wrong bucket");
    }
  }
  // THE INVARIANT THE PROBE ORDER RESTS ON.  A pass's leftovers become the
  // published table's second TIER, which the probe cascade reaches immediately
  // after the main table it belongs to (PlanWindowsLaminar orders a tier right
  // behind its main table).  That order returns the freshest copy only because the published
  // (main, tier) pair is duplicate-free -- kResidualWins clears a main-bucket
  // duplicate whether or not the residual then fits.  Stacking makes one main
  // bucket meet `groups` residual buckets in turn, so this is where a group
  // that re-inserted what an earlier group had left behind would show up.
  for (size_t b = 0; b < plan.range_buckets; ++b) {
    left += bs::Popcount64(ref_range_masks[b]);
    for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
      if (!((ref_range_masks[b] >> e) & 1)) continue;
      const uint64_t key = ReadKey(range.Bucket(b), e, layout.key_bytes);
      Expect(seen.find(key) == seen.end(),
             "a stacked sweep left a residual that duplicates a main-table "
             "entry: the published (main, tier) pair would not be "
             "duplicate-free");
    }
  }
  // Nothing is lost: every distinct key is in the main table or in the
  // leftovers, and by the check above never in both.
  Expect(absorbed + left == n_residuals,
         "a stacked sweep lost or duplicated an entry");
  std::printf("  stacked sweep 2^%u buckets, %zu pool buckets -> %zu x 2^%u "
              "ranges, %zu units: %zu absorbed, %zu left over, identical at "
              "every slicing\n",
              main_levels, pool_buckets, plan.groups, plan.range_bits, units,
              absorbed, left);
}


// ---------------------------------------------------------------------------
// The merged class-marked offer
// ---------------------------------------------------------------------------

// The two-answer kernel against the scalar reference: first_dup must be
// exactly "first's real lanes whose key occurs among the TIER lanes", and
// carry_dup "the CARRY lanes whose key occurs in first" -- i.e. the two
// masked single-rule masks, which ReferenceDuplicateMask spells out.  Same
// shared key pool and zero-key planting as TestCrossBucketDuplicateMask;
// every supported width must satisfy the same exact equality predicate.
void TestCrossBucketClassDuplicateMasks() {
  std::mt19937_64 rng(0xC1A55B17ull);
  size_t nontrivial = 0;
  for (size_t key_bytes : kKeyWidths) {
    bs::StashLayout layout;
    layout.key_bytes = key_bytes;
    layout.value_bytes = 4;
    layout.tag_bytes = 1;
    auto table = bs::Table::Create(2, layout.Base());

    for (int trial = 0; trial < 200; ++trial) {
      const size_t pool_size = 1 + (trial % 24);
      std::vector<bs::KeyWords> pool(pool_size);
      pool[0] = bs::KeyWords{};  // the value the zero-key repair exists for
      for (size_t i = 1; i < pool_size; ++i) pool[i] = PoolKey(rng, key_bytes);

      uint64_t real[2];
      for (int b = 0; b < 2; ++b) {
        real[b] = rng();
        for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
          WriteKey(table.Bucket(static_cast<size_t>(b)), e, key_bytes,
                   pool[rng() % pool_size]);
        }
      }
      // The class split of the second bucket's occupancy word: random, so
      // carry-only, tier-only and mixed buckets all occur.
      // Explicit empty/full inputs and single-class candidates complement
      // the random masks: these shapes cannot occur by luck in 200 trials.
      if (trial % 16 == 0) real[0] = 0;
      if (trial % 16 == 1) real[1] = 0;
      if (trial % 16 == 2) real[0] = real[1] = ~uint64_t{0};
      const uint64_t classes = trial % 16 == 3 ? uint64_t{0}
                               : trial % 16 == 4 ? ~uint64_t{0} : rng();
      const uint64_t tier = real[1] & classes;
      const uint64_t carry = real[1] & ~tier;

      uint64_t first_dup = 0, carry_dup = 0;
      bs::CrossBucketClassDuplicateMasks(table.Bucket(0), real[0],
                                         table.Bucket(1), carry, tier,
                                         key_bytes, &first_dup, &carry_dup);
      Expect(first_dup == ReferenceDuplicateMask(table.Bucket(1), tier,
                                                 table.Bucket(0), real[0],
                                                 key_bytes),
             "the class kernel's first-side (tier) mask is wrong");
      Expect(carry_dup == ReferenceDuplicateMask(table.Bucket(0), real[0],
                                                 table.Bucket(1), carry,
                                                 key_bytes),
             "the class kernel's carry-side mask is wrong");
      if (first_dup != 0 && carry_dup != 0) ++nontrivial;
    }
  }
  Expect(nontrivial > 100,
         "the class-mask trials rarely exercised both outputs at once");
  std::printf("  class duplicate masks agree with the scalar reference "
              "(%zu trials with both classes hit)\n",
              nontrivial);
}

// THE INVARIANT EVERY FUSED FINAL PASS RESTS ON, stated on its own:
//
//     A BUCKET THAT IS FULL WHEN THE OFFER RUNS ABSORBS NO CARRY-CLASS
//     CANDIDATE.
//
// A fused pass builds its range table before the pass it rides, so what that
// pass sheds is not in the table; it drains, and its one same-key conflict --
// with a carry-class RANGE LEFTOVER -- is resolved afterwards by
// ResidualLeftoverDedupRange, which reaches a leftover and nothing else.  The
// shed's bucket was full at the shed, and the staler copy of a shed key wants
// that same bucket (same key, same tag), so the shed is resolvable exactly
// when a full bucket cannot absorb a carry-class candidate.
//
// What makes that non-obvious, and what this pins: a TIER-class candidate can
// clear a main lane, and the freed lane goes to the lowest-indexed candidate
// of the range bucket, which need not be the resolver.  Allocate both classes
// together and that lane can go to a carry-class candidate -- past the
// backstop, and the key is then published twice, the staler copy in the main
// table and the fresher in the tier.  (Several cases of
// cpu_byteslice_level_arena_top_test reach this shape end to end.)
//
// The fixture is the minimum that can: one full bucket, one tier candidate
// that resolves a duplicate in it, one carry candidate for the same bucket
// that resolves nothing.
void TestFullBucketAbsorbsNoCarryClass() {
  bs::StashLayout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 4;
  layout.tag_bytes = 2;
  bs::ResidualRangePlan plan;
  plan.range_bits = 0;
  plan.index_bits = 0;
  plan.groups = 1;
  plan.range_buckets = 1;
  plan.scatter_per_bucket = 8;  // unread by the offers

  auto main = bs::Table::Create(1, layout.Base());
  auto range = bs::Table::Create(1, layout.Base());
  // Zeroed, so that the class mark below is the ONLY set class bit: a stray
  // one in the carry candidate's meta byte would make it a tier candidate and
  // the fixture would test the wrong rule.
  for (auto* t : {&main, &range}) {
    std::memset(t->data.get(), 0, t->num_buckets * layout.BucketBytes());
  }
  const size_t lines = layout.Base().EntryBytes();

  // Keys 0x1000.. fill the bucket; the tier candidate duplicates the one at
  // lane 40, and the carry candidate is a key the bucket does not hold.  Lane
  // order matters: the carry candidate sits BELOW the tier one, so a joint
  // allocation hands it the freed lane ("a resolver can be crowded out by a
  // non-resolver").
  for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
    WriteKey(main.Bucket(0), e, layout.key_bytes, 0x1000 + e);
    main.masks[0] |= uint64_t{1} << e;
  }
  const uint64_t carry_key = 0x2000;
  const uint64_t tier_key = 0x1000 + 40;
  WriteKey(range.Bucket(0), 0, layout.key_bytes, carry_key);
  WriteKey(range.Bucket(0), 1, layout.key_bytes, tier_key);
  range.Bucket(0)[layout.MetaOffset() * bs::kBucketCapacity + 1] =
      bs::kMetaResidualClass;
  range.masks[0] = 0x3;

  bs::OfferResidualsToBucket(bs::View(main), bs::View(range), plan,
                             bs::ResidualDedupRule::kClassMark, lines,
                             /*b=*/0, /*g=*/0);

  Expect(bs::Popcount64(main.masks[0]) == bs::kBucketCapacity,
         "the offer left a full bucket below full");
  bool carry_in_main = false, tier_in_main = false;
  for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
    if (!((main.masks[0] >> e) & 1)) continue;
    const uint64_t key = ReadKey(main.Bucket(0), e, layout.key_bytes);
    if (key == carry_key) carry_in_main = true;
    if (key == tier_key) {
      Expect(!tier_in_main, "the tier candidate and its duplicate both stand");
      tier_in_main = true;
    }
  }
  Expect(!carry_in_main,
         "a full bucket absorbed a carry-class candidate: the lane a tier "
         "resolver freed went to the staler class, which is what leaves a "
         "fused pass's drain-only shed unresolvable");
  Expect(tier_in_main, "the tier candidate did not take the lane it freed");
  Expect((range.masks[0] & 1) != 0,
         "the carry candidate was consumed rather than left as a leftover");
  Expect((range.masks[0] & 2) == 0, "the tier candidate was not absorbed");
  std::printf("  a full bucket absorbs no carry-class candidate (the fused "
              "pass's drain-only shed stays resolvable)\n");
}

// The class-marked offer against the split pair it replaces.  BYTE IDENTITY IS
// THE CONTRACT: the merged form allocates per class, the carry's out of the
// lanes free before any clear and the tier's out of the rest plus the lanes it
// freed, which is what running the two single-rule offers in that order does
// (PlanResidualOfferMerge).  Asserted both ways -- lane for lane, and against
// the freshness model both must satisfy: the union of the final main table and
// the leftovers is the freshness-correct key -> value map (a carry candidate
// loses to a main copy, a tier candidate beats one), the main table holds each
// key once, and no leftover duplicates a main entry.
//
// Bucket 1 is planted FULL, which is the shape the ordering exists for.
void TestClassMarkOfferMatchesSplitOffers(uint64_t seed) {
  bs::StashLayout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 4;
  layout.tag_bytes = 2;
  const unsigned index_bits = 3;
  const unsigned range_bits = 2;
  const size_t num_buckets = size_t{1} << (index_bits + range_bits);
  bs::ResidualRangePlan plan;
  plan.range_bits = range_bits;
  plan.index_bits = index_bits;
  plan.groups = 1;
  plan.range_buckets = size_t{1} << range_bits;
  plan.scatter_per_bucket = 8;  // unread by the offers

  auto main_merged = bs::Table::Create(num_buckets, layout.Base());
  auto main_split = bs::Table::Create(num_buckets, layout.Base());
  auto range_merged = bs::Table::Create(plan.range_buckets, layout.Base());
  auto range_carry = bs::Table::Create(plan.range_buckets, layout.Base());
  auto range_tier = bs::Table::Create(plan.range_buckets, layout.Base());
  for (auto* t : {&main_merged, &main_split, &range_merged, &range_carry,
                  &range_tier}) {
    std::memset(t->data.get(), 0, t->num_buckets * layout.BucketBytes());
  }

  const auto value_of = [](uint64_t key, unsigned who) {
    // who: 0 = main original, 1 = carry, 2 = tier.
    return static_cast<uint32_t>((key * 0x9E3779B97F4A7C15ull) >> 32) ^
           (0x11111111u * who);
  };
  const auto write_value = [&](uint8_t* bucket, size_t slot, uint32_t v) {
    for (size_t i = 0; i < 4; ++i) {
      bucket[(layout.key_bytes + i) * bs::kBucketCapacity + slot] =
          static_cast<uint8_t>(v >> (8 * i));
    }
  };
  const auto read_value = [&](const uint8_t* bucket, size_t slot) {
    uint32_t v = 0;
    for (size_t i = 0; i < 4; ++i) {
      v |= static_cast<uint32_t>(
               bucket[(layout.key_bytes + i) * bs::kBucketCapacity + slot])
           << (8 * i);
    }
    return v;
  };

  std::mt19937_64 rng(seed);
  // The main table: bucket 1 FULL (forcing leftovers), the rest at mixed
  // loads.  Keys are unique per bucket by construction of the counter.
  std::vector<std::vector<uint64_t>> main_keys(num_buckets);
  uint64_t next_key = 0x100000;
  std::unordered_map<uint64_t, uint32_t> model;
  for (size_t b = 0; b < num_buckets; ++b) {
    const size_t fill = b == 1 ? bs::kBucketCapacity : rng() % 60;
    for (size_t e = 0; e < fill; ++e) {
      // Bucket 2 slot 0 holds the key 0, so the zero repair runs against a
      // live entry rather than never.
      const uint64_t key = (b == 2 && e == 0) ? 0 : next_key++;
      WriteKey(main_merged.Bucket(b), e, layout.key_bytes, key);
      write_value(main_merged.Bucket(b), e, value_of(key, 0));
      main_merged.masks[b] |= uint64_t{1} << e;
      main_keys[b].push_back(key);
      model[key] = value_of(key, 0);
    }
  }

  // The candidates: per range bucket at most 64 lanes, each naming a main
  // bucket in its range, class chosen at random, and a third of them planted
  // as duplicates of a key already IN their target bucket -- the case each
  // rule exists for.  Candidate keys never repeat across the whole pool,
  // which is the pool-dedup precondition the merged offer rests on.
  std::vector<size_t> lanes(plan.range_buckets, 0);
  std::unordered_set<uint64_t> cand_keys;
  size_t planted = 0, dup_carry = 0, dup_tier = 0;
  for (int i = 0; i < 200; ++i) {
    const size_t d = rng() % num_buckets;
    const size_t r = d >> index_bits;
    if (lanes[r] == bs::kBucketCapacity) continue;
    const bool tier = (rng() & 1) != 0;
    uint64_t key;
    if (i % 3 == 0 && !main_keys[d].empty()) {
      key = main_keys[d][rng() % main_keys[d].size()];
      if (!cand_keys.insert(key).second) {
        continue;  // already a candidate somewhere; keys must be unique
      }
      tier ? ++dup_tier : ++dup_carry;
    } else {
      key = 0x200000 + static_cast<uint64_t>(i);
      cand_keys.insert(key);
    }
    const size_t e = lanes[r]++;
    ++planted;
    uint8_t* bucket = range_merged.Bucket(r);
    WriteKey(bucket, e, layout.key_bytes, key);
    write_value(bucket, e, value_of(key, tier ? 2 : 1));
    // The stored tag: low byte = the destination's index bits (the match
    // reads the low index_bits of it), high byte junk the offers must ignore.
    bucket[(layout.TagOffset() + 1) * bs::kBucketCapacity + e] =
        static_cast<uint8_t>(d);
    bucket[layout.TagOffset() * bs::kBucketCapacity + e] =
        static_cast<uint8_t>(rng());
    // The class mark, where the production stamp puts it: kMetaResidualClass
    // in the meta line, over junk in the byte's other bits.
    bucket[layout.MetaOffset() * bs::kBucketCapacity + e] =
        static_cast<uint8_t>((rng() & ~bs::kMetaResidualClass) |
                             (tier ? bs::kMetaResidualClass : 0u));
    range_merged.masks[r] |= uint64_t{1} << e;
    (tier ? range_tier : range_carry).masks[r] |= uint64_t{1} << e;
    // The model: a tier candidate's value wins over a main copy; a carry
    // candidate's loses to one and is consumed.
    const bool in_main = model.count(key) != 0;
    if (tier) {
      model[key] = value_of(key, 2);
    } else if (!in_main) {
      model[key] = value_of(key, 1);
    }
  }
  Expect(dup_carry > 3 && dup_tier > 3,
         "the trial planted too few duplicates to exercise both rules");
  // The split path's clones share the merged table's bytes; only the
  // occupancy masks differ, split by class.
  std::memcpy(main_split.data.get(), main_merged.data.get(),
              num_buckets * layout.BucketBytes());
  std::memcpy(main_split.masks.get(), main_merged.masks.get(),
              num_buckets * sizeof(uint64_t));
  std::memcpy(range_carry.data.get(), range_merged.data.get(),
              plan.range_buckets * layout.BucketBytes());
  std::memcpy(range_tier.data.get(), range_merged.data.get(),
              plan.range_buckets * layout.BucketBytes());

  const size_t lines = layout.Base().EntryBytes();
  for (size_t b = 0; b < num_buckets; ++b) {
    bs::OfferResidualsToBucket(bs::View(main_merged), bs::View(range_merged),
                               plan, bs::ResidualDedupRule::kClassMark, lines,
                               b, 0);
    // The split offers in production order: the carry's first, the tier's
    // second.
    bs::OfferResidualsToBucket(bs::View(main_split), bs::View(range_carry),
                               plan, bs::ResidualDedupRule::kTableWins, lines,
                               b, 0);
    bs::OfferResidualsToBucket(bs::View(main_split), bs::View(range_tier),
                               plan, bs::ResidualDedupRule::kResidualWins,
                               lines, b, 0);
  }

  // AND THEY ARE THE SAME OFFER, lane for lane.  The merged form allocates its
  // classes in order -- the carry's out of the lanes that were free before any
  // clear, the tier's out of what is left plus the lanes it freed
  // (PlanResidualOfferMerge) -- which is exactly what running the two single
  // rule offers in that order does.  Byte equality is therefore the right
  // assertion, and a stronger one than the freshness model below: it is what
  // says a fused final pass's drain-only shed can still be resolved against
  // the range leftovers afterwards, since a full bucket absorbs no carry-class
  // candidate in either form.
  for (size_t b = 0; b < num_buckets; ++b) {
    Expect(main_merged.masks[b] == main_split.masks[b],
           "the merged offer and the split offers filled different lanes");
    Expect(std::memcmp(main_merged.Bucket(b), main_split.Bucket(b),
                       lines * bs::kBucketCapacity) == 0,
           "the merged offer and the split offers wrote different bytes");
  }
  for (size_t r = 0; r < plan.range_buckets; ++r) {
    Expect(range_merged.masks[r] ==
               (range_carry.masks[r] | range_tier.masks[r]),
           "the merged offer and the split offers consumed different "
           "candidates");
  }

  const auto collect = [&](const bs::Table& main,
                           std::initializer_list<const bs::Table*> ranges) {
    std::unordered_map<uint64_t, uint32_t> out;
    for (size_t b = 0; b < main.num_buckets; ++b) {
      for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
        if (!((main.masks[b] >> e) & 1)) continue;
        const uint64_t key = ReadKey(main.Bucket(b), e, layout.key_bytes);
        Expect(out.emplace(key, read_value(main.Bucket(b), e)).second,
               "an offer path left one key in the main table twice");
      }
    }
    const size_t in_main = out.size();
    for (const bs::Table* range : ranges) {
      for (size_t r = 0; r < range->num_buckets; ++r) {
        for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
          if (!((range->masks[r] >> e) & 1)) continue;
          const uint64_t key = ReadKey(range->Bucket(r), e, layout.key_bytes);
          Expect(out.emplace(key, read_value(range->Bucket(r), e)).second,
                 "a leftover duplicates a main-table entry (the published "
                 "(main, tier) pair would not be duplicate-free)");
        }
      }
    }
    return std::make_pair(out, in_main);
  };
  const auto merged = collect(main_merged, {&range_merged});
  const auto split = collect(main_split, {&range_carry, &range_tier});
  Expect(merged.first.size() == model.size() &&
             split.first.size() == model.size(),
         "an offer path lost or invented a key");
  for (const auto& kv : model) {
    const auto m = merged.first.find(kv.first);
    const auto s = split.first.find(kv.first);
    Expect(m != merged.first.end() && m->second == kv.second,
           "the merged offer resolved a key to the wrong freshness class");
    Expect(s != split.first.end() && s->second == kv.second,
           "the split offers resolved a key to the wrong freshness class");
  }
  std::printf("  class-marked offer == split offers on %zu candidates "
              "(%zu carry dups, %zu tier dups), %zu keys, both match the "
              "freshness model\n",
              planted, dup_carry, dup_tier, model.size());
}

// ---------------------------------------------------------------------------
// The incremental chain
// ---------------------------------------------------------------------------

// The claim that makes the incremental schedule free is that it is a
// REORDERING: T_{j+1} = merge(T_j, L_j) into a fresh [T_j | L_j] buffer issues
// exactly the MergeSplits the monolithic in-place network issues, each with the
// same input state.  So the two must agree bucket for bucket and byte for byte
// -- which is a much sharper statement than "both are valid hash tables", and
// it is the one that fails the moment a step routes the wrong number of levels
// or re-tags a half it should have left alone.
//
// Both sides start from the same bytes: one dense online-stash bucket for
// block 0 (scattered, as a real carry does) and one table per source level.
void TestIncrementalChainMatchesMonolithic(unsigned target, size_t per_bucket) {
  bs::Layout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 4;
  layout.tag_bytes = 2;
  const unsigned s = 2;  // kFirstBlockLog2 at load 0.25: one unit = 4 buckets
  const unsigned m = s + target;
  const size_t total = size_t{1} << m;
  const size_t bucket_bytes = layout.BucketBytes();
  const uint64_t nonce_lo = 0x51DE + target;
  const uint64_t nonce_hi = 0xC0FFEE + per_bucket;
  std::mt19937_64 rng(0xACE0 + target * 31 + per_bucket);

  // Zeroed everywhere, so even the don't-care bytes are comparable: the two
  // sides perform the same writes on the same initial contents.
  auto Zeroed = [&](size_t buckets) {
    auto t = bs::Table::Create(buckets, layout);
    std::memset(t.data.get(), 0, buckets * bucket_bytes);
    return t;
  };

  auto flat = Zeroed(total);
  auto dense = Zeroed(1);
  auto sources = std::vector<bs::Table>{};

  // Block 0: the online stash, one dense bucket scattered 64 -> 4 x 16.
  uint64_t next_key = 1;
  std::vector<uint64_t> planted;
  for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
    const uint64_t key = next_key++;
    WriteKey(dense.Bucket(0), e, layout.key_bytes, key);
    dense.Bucket(0)[layout.key_bytes * bs::kBucketCapacity + e] = 0;
    planted.push_back(key);
  }
  dense.masks[0] = ~uint64_t{0};
  bs::ScatterDenseBucket(dense.Bucket(0), dense.masks[0], flat.data.get(),
                         flat.masks.get(), bs::kBucketCapacity >> s,
                         layout.EntryBytes(), layout.PayloadLines());

  // Blocks 1..target: source level L_{j} at block j+1, of 4 << j buckets.  A
  // fraction of its keys duplicate a key already placed in a FRESHER block, so
  // every cross-source level has something to deduplicate.
  for (unsigned j = 0; j < target; ++j) {
    size_t offset, size;
    bs::BinarySourceBlock(s, j + 1, &offset, &size);
    auto src = Zeroed(size);
    for (size_t b = 0; b < size; ++b) {
      for (size_t e = 0; e < per_bucket; ++e) {
        const bool reuse = (rng() & 3) == 0;
        const uint64_t key =
            reuse ? planted[rng() % planted.size()] : next_key++;
        if (!reuse) planted.push_back(key);
        WriteKey(src.Bucket(b), e, layout.key_bytes, key);
        src.Bucket(b)[layout.key_bytes * bs::kBucketCapacity + e] =
            static_cast<uint8_t>(j + 1);
      }
      // Dummy slots hold stale copies of live keys: the case a dedup that
      // ignores occupancy would silently drop entries over.
      for (size_t e = per_bucket; e < bs::kBucketCapacity; ++e) {
        WriteKey(src.Bucket(b), e, layout.key_bytes,
                 planted[rng() % planted.size()]);
      }
      src.masks[b] = bs::LowMask64(static_cast<unsigned>(per_bucket));
    }
    std::memcpy(flat.data.get() + offset * bucket_bytes, src.data.get(),
                size * bucket_bytes);
    std::memcpy(flat.masks.get() + offset, src.masks.get(),
                size * sizeof(uint64_t));
    sources.push_back(std::move(src));
  }

  // Monolithic: tag the whole input once and route it in place.
  bs::StashLayout stash_layout;
  stash_layout.key_bytes = layout.key_bytes;
  stash_layout.value_bytes = layout.value_bytes - 1;  // Base() adds the meta
  stash_layout.tag_bytes = layout.tag_bytes;
  OwnedLevelStashes flat_stashes(m + 1, 1, stash_layout);
  bs::TableView flat_view = bs::View(flat);
  bs::ComputeRoutingTags(flat_view, nonce_lo, nonce_hi, {}, m);
  Expect(bs::RouteBinarySourcesDedup</*CheckOverflow=*/true>(
             flat_view, s, flat_stashes.ptr()),
         "the monolithic network overflowed");

  // Incremental: the same nonce for the whole chain, each step into a
  // fresh buffer.
  OwnedLevelStashes chain_stashes(m + 1, 1, stash_layout);
  auto cur = Zeroed(size_t{1} << s);
  bs::TableView cur_view = bs::View(cur);
  Expect(bs::BuildIncrementalChainHead</*CheckOverflow=*/true>(
             cur_view, dense.Bucket(0), dense.masks[0], nonce_lo, nonce_hi, m,
             chain_stashes.ptr()),
         "the chain head overflowed");
  for (unsigned j = 0; j < target; ++j) {
    auto next = Zeroed(cur.num_buckets * 2);
    // Every other step exercises the prepared-half hook (an owner may route
    // the next source's half ahead of time), which must be indistinguishable
    // from doing the same work inside the step.
    const bool prepare_first = (j % 2) == 1;
    if (prepare_first) {
      Expect(bs::PrepareIncrementalUpperHalf</*CheckOverflow=*/true>(
                 bs::View(next), bs::View(sources[j]), nonce_lo, nonce_hi, m,
                 chain_stashes.ptr()),
             "the prepared upper half overflowed");
    }
    Expect(bs::IncrementalMergeStep</*CheckOverflow=*/true>(
               bs::View(next), bs::View(cur), bs::View(sources[j]), nonce_lo,
               nonce_hi, m, chain_stashes.ptr(), prepare_first),
           "an incremental step overflowed");
    cur = std::move(next);
  }

  Expect(cur.num_buckets == total, "the chain ended on the wrong table size");
  Expect(std::memcmp(flat.masks.get(), cur.masks.get(),
                     total * sizeof(uint64_t)) == 0,
         "the incremental chain produced different occupancy masks than the "
         "monolithic network");
  Expect(std::memcmp(flat.data.get(), cur.data.get(), total * bucket_bytes) == 0,
         "the incremental chain produced different bucket bytes than the "
         "monolithic network");
  Expect(flat_stashes.Count() == 0 && chain_stashes.Count() == 0,
         "load 0.25 shed a residual");
  size_t live = 0;
  for (size_t b = 0; b < total; ++b) live += bs::Popcount64(cur.masks[b]);
  std::printf("  incremental chain == monolithic, target %u, 2^%u buckets, "
              "%zu/bucket in, %zu live out\n",
              target, m, per_bucket, live);
}

// ---------------------------------------------------------------------------
// The fixed last level's direct merge
// ---------------------------------------------------------------------------

// The two-step reference per pair: one cross-source dedup MergeSplit on an
// extra tag bit, splitting the union over two buckets, then a fold merging
// those two back into one.  MergeFixedLevelSources does the merge directly, and
// the claim is that the routing bit does no work -- so the two must agree
// as SETS (slot order is not part of a table's semantics; a probe scans the
// whole bucket).
std::map<uint64_t, unsigned> BucketContents(const uint8_t* bucket, uint64_t mask,
                                            const bs::Layout& layout) {
  std::map<uint64_t, unsigned> out;
  for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
    if (!((mask >> e) & 1)) continue;
    const uint64_t key = ReadKey(bucket, e, layout.key_bytes);
    Expect(out.emplace(key, bucket[layout.key_bytes * bs::kBucketCapacity + e])
               .second,
           "a bucket holds one key twice");
  }
  return out;
}

// `fresh_count` / `older_count` real entries per bucket, `shared` of the older
// bucket's keys duplicating a fresher one.  Value byte 0 marks the source
// (0 = fresher, 1 = older) so the freshness rule is checkable, and value byte 1
// is a version stamp that differs between the two copies of a shared key.
void TestFixedLevelMerge(size_t num_buckets, size_t fresh_count,
                         size_t older_count, size_t shared, bool expect_ok,
                         uint64_t seed) {
  bs::Layout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 4;
  layout.tag_bytes = 2;
  const size_t bucket_bytes = layout.BucketBytes();
  std::mt19937_64 rng(seed);

  auto fresher = bs::Table::Create(num_buckets, layout);
  auto older = bs::Table::Create(num_buckets, layout);
  std::memset(fresher.data.get(), 0, num_buckets * bucket_bytes);
  std::memset(older.data.get(), 0, num_buckets * bucket_bytes);

  std::vector<std::map<uint64_t, unsigned>> expected(num_buckets);
  for (size_t b = 0; b < num_buckets; ++b) {
    std::vector<uint64_t> fresh_keys;
    for (size_t e = 0; e < fresh_count; ++e) {
      // Key 0 in the first bucket: the value the dedup kernel's dummy-zeroing
      // collapses onto and then has to repair.
      const uint64_t key = (b == 0 && e == 0) ? 0 : (b * 1000 + e + 1);
      fresh_keys.push_back(key);
      WriteKey(fresher.Bucket(b), e, layout.key_bytes, key);
      fresher.Bucket(b)[layout.key_bytes * bs::kBucketCapacity + e] = 0;
      fresher.Bucket(b)[(layout.key_bytes + 1) * bs::kBucketCapacity + e] = 7;
      expected[b][key] = 0;
    }
    fresher.masks[b] = bs::LowMask64(static_cast<unsigned>(fresh_count));
    for (size_t e = 0; e < older_count; ++e) {
      const bool dup = e < shared && !fresh_keys.empty();
      const uint64_t key = dup ? fresh_keys[e % fresh_keys.size()]
                               : (b * 1000 + 500 + e + 1);
      WriteKey(older.Bucket(b), e, layout.key_bytes, key);
      older.Bucket(b)[layout.key_bytes * bs::kBucketCapacity + e] = 1;
      older.Bucket(b)[(layout.key_bytes + 1) * bs::kBucketCapacity + e] = 9;
      // The fresher copy wins outright: a duplicate leaves no trace.
      if (!dup) expected[b][key] = 1;
    }
    older.masks[b] = bs::LowMask64(static_cast<unsigned>(older_count));
    // Stale dummy slots on both sides, holding live keys of the other table.
    for (size_t e = fresh_count; e < bs::kBucketCapacity; ++e) {
      WriteKey(fresher.Bucket(b), e, layout.key_bytes,
               b * 1000 + 500 + (rng() % 64) + 1);
    }
    for (size_t e = older_count; e < bs::kBucketCapacity; ++e) {
      WriteKey(older.Bucket(b), e, layout.key_bytes, b * 1000 + (rng() % 64) + 1);
    }
    // Random tag bytes: the reference splits the union on a tag bit, so the
    // two paths only agree if that bit really is irrelevant.
    for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
      for (size_t tb = 0; tb < layout.tag_bytes; ++tb) {
        fresher.Bucket(b)[(layout.TagOffset() + tb) * bs::kBucketCapacity + e] =
            static_cast<uint8_t>(rng());
        older.Bucket(b)[(layout.TagOffset() + tb) * bs::kBucketCapacity + e] =
            static_cast<uint8_t>(rng());
      }
    }
  }

  // Byte-exact copies, to prove the merge leaves the fresher source alone: it
  // is still in the old probe plan, and MergeBucketIntoWithStash zeroes the
  // mask word it is handed (hence the copy the kernel passes it).
  auto fresh_before = bs::Table::Create(num_buckets, layout);
  std::memcpy(fresh_before.data.get(), fresher.data.get(),
              num_buckets * bucket_bytes);
  std::memcpy(fresh_before.masks.get(), fresher.masks.get(),
              num_buckets * sizeof(uint64_t));

  bs::ResidualStash no_stash;
  no_stash.entry_bytes = layout.EntryBytes();
  const bool ok = bs::MergeFixedLevelSources</*CheckOverflow=*/true>(
      bs::View(older), bs::View(fresher), no_stash);
  Expect(ok == expect_ok, "the fixed merge's overflow verdict is wrong");
  if (!ok) {
    std::printf("  fixed merge refused %zu + %zu (union > 64), as it must\n",
                fresh_count, older_count);
    return;
  }

  Expect(std::memcmp(fresh_before.data.get(), fresher.data.get(),
                     num_buckets * bucket_bytes) == 0,
         "the fixed merge modified the fresher source's bytes");
  Expect(std::memcmp(fresh_before.masks.get(), fresher.masks.get(),
                     num_buckets * sizeof(uint64_t)) == 0,
         "the fixed merge cleared the fresher source's occupancy");

  for (size_t b = 0; b < num_buckets; ++b) {
    const auto got = BucketContents(older.Bucket(b), older.masks[b], layout);
    Expect(got == expected[b],
           "the fixed merge's union is not the deduplicated one, or a stale "
           "copy won a conflict");
  }

  std::printf("  fixed merge %zu buckets, %zu fresher + %zu older (%zu shared) "
              "-> %zu live/bucket\n",
              num_buckets, fresh_count, older_count, shared,
              expected[0].size());
}

// The same set equivalence, against the actual kernels of the two-step
// reference, on randomized pairs: [B | C] joined by one cross-source dedup MergeSplit on
// tag bit `bit`, then bucket 0 folded into bucket 1.
void TestFixedLevelMergeMatchesFold(uint64_t seed) {
  bs::Layout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 4;
  layout.tag_bytes = 2;
  const size_t bucket_bytes = layout.BucketBytes();
  const unsigned bit = 8;  // the extra routing bit the fold immediately undoes
  bs::StashLayout stash_layout;
  stash_layout.key_bytes = layout.key_bytes;
  stash_layout.value_bytes = layout.value_bytes - 1;
  stash_layout.tag_bytes = layout.tag_bytes;
  std::mt19937_64 rng(seed);

  for (int trial = 0; trial < 300; ++trial) {
    const size_t nb = 1 + rng() % 24;   // fresher reals
    const size_t nc = 1 + rng() % 24;   // older reals
    auto fresher = bs::Table::Create(1, layout);
    auto older = bs::Table::Create(1, layout);
    std::memset(fresher.data.get(), 0, bucket_bytes);
    std::memset(older.data.get(), 0, bucket_bytes);
    // A small key pool, so duplicates across and stale dummies are frequent.
    const size_t pool = 1 + rng() % 40;
    for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
      WriteKey(fresher.Bucket(0), e, layout.key_bytes, rng() % pool);
      WriteKey(older.Bucket(0), e, layout.key_bytes, rng() % pool);
      fresher.Bucket(0)[layout.key_bytes * bs::kBucketCapacity + e] = 0;
      older.Bucket(0)[layout.key_bytes * bs::kBucketCapacity + e] = 1;
      for (size_t tb = 0; tb < layout.tag_bytes; ++tb) {
        fresher.Bucket(0)[(layout.TagOffset() + tb) * bs::kBucketCapacity + e] =
            static_cast<uint8_t>(rng());
        older.Bucket(0)[(layout.TagOffset() + tb) * bs::kBucketCapacity + e] =
            static_cast<uint8_t>(rng());
      }
    }
    // Distinct keys inside one bucket: both sources are internally
    // duplicate-free by construction (each is one routed table).
    uint64_t spare = 1000000;  // monotone, so the retry always terminates
    auto Distinct = [&](uint8_t* bucket, size_t n) {
      std::unordered_set<uint64_t> seen;
      for (size_t e = 0; e < n; ++e) {
        uint64_t key = ReadKey(bucket, e, layout.key_bytes);
        while (!seen.insert(key).second) key = ++spare;
        WriteKey(bucket, e, layout.key_bytes, key);
      }
    };
    Distinct(fresher.Bucket(0), nb);
    Distinct(older.Bucket(0), nc);
    fresher.masks[0] = bs::LowMask64(static_cast<unsigned>(nb));
    older.masks[0] = bs::LowMask64(static_cast<unsigned>(nc));

    // Two-step reference, on copies.
    auto pair = bs::Table::Create(2, layout);
    std::memcpy(pair.Bucket(0), fresher.Bucket(0), bucket_bytes);
    std::memcpy(pair.Bucket(1), older.Bucket(0), bucket_bytes);
    pair.masks[0] = fresher.masks[0];
    pair.masks[1] = older.masks[0];
    OwnedLevelStashes fold_stashes(1, 1, stash_layout);
    Expect(bs::MergeSplitPairDedupStash</*CheckOverflow=*/true>(
               pair.Bucket(0), pair.Bucket(1), &pair.masks[0], &pair.masks[1],
               layout.key_bytes, layout.EntryBytes(), layout.TagLine(bit), bit,
               fold_stashes.slots[0]),
           "the reference cross-source MergeSplit overflowed");
    Expect(bs::MergeBucketIntoWithStash</*CheckOverflow=*/true>(
               pair.Bucket(1), pair.Bucket(0), &pair.masks[1], &pair.masks[0],
               layout.PayloadLines(), fold_stashes.slots[0]),
           "the reference fold overflowed");
    Expect(fold_stashes.Count() == 0, "the reference path shed a residual");
    const auto want = BucketContents(pair.Bucket(1), pair.masks[1], layout);

    // Direct merge.
    bs::ResidualStash no_stash;
    no_stash.entry_bytes = layout.EntryBytes();
    Expect(bs::MergeFixedLevelSources</*CheckOverflow=*/true>(
               bs::View(older), bs::View(fresher), no_stash),
           "the direct fixed merge overflowed where the fold did not");
    const auto got = BucketContents(older.Bucket(0), older.masks[0], layout);
    Expect(got == want,
           "the direct fixed merge and cross-level-plus-fold disagree");
  }
  std::printf("  fixed merge == cross level + fold, 300 randomized pairs\n");
}

// ---------------------------------------------------------------------------
// The fixed level is not a special case at load 0.5
// ---------------------------------------------------------------------------

// One butterfly level over `2 * buckets` buckets whose inputs are Poisson(mean)
// (truncated at a bucket's 64 slots, exactly as a real level's inputs are), with
// uniformly random routing bits.  A pair's total is then Poisson(2*mean) and the
// split is Binomial of it, so each output bucket is ~Poisson(mean) -- the
// reference occupancy the fixed merge's union has to look like.  Returns the
// level's total shed.
size_t OrdinaryLevelShed(size_t buckets, size_t mean, uint64_t seed) {
  bs::StashLayout slayout;
  slayout.key_bytes = 8;
  slayout.value_bytes = 16;
  slayout.tag_bytes = 4;
  const bs::Layout layout = slayout.Base();
  const size_t n = 2 * buckets;
  auto table = bs::Table::Create(n, layout);
  std::memset(table.data.get(), 0, n * layout.BucketBytes());
  std::mt19937_64 rng(seed);
  std::poisson_distribution<size_t> poisson(static_cast<double>(mean));
  const unsigned bit = static_cast<unsigned>(bs::Log2Exact(buckets));
  for (size_t b = 0; b < n; ++b) {
    const size_t count = std::min<size_t>(poisson(rng), bs::kBucketCapacity);
    for (size_t e = 0; e < count; ++e) {
      WriteKey(table.Bucket(b), e, layout.key_bytes, rng() | 1);
      // Only the routed bit matters; the rest of the tag is never read here.
      table.Bucket(b)[layout.TagLine(bit) * bs::kBucketCapacity + e] =
          static_cast<uint8_t>(rng());
    }
    table.masks[b] = bs::LowMask64(static_cast<unsigned>(count));
  }
  OwnedLevelStashes stashes(1, bs::kMaxResidualStashBuckets, slayout);
  for (size_t i = 0; i < buckets; ++i) {
    Expect(bs::MergeSplitPairStash</*CheckOverflow=*/true>(
               table.Bucket(i), table.Bucket(i + buckets), &table.masks[i],
               &table.masks[i + buckets], layout.RoutedLines(bit),
               layout.TagLine(bit), bit, stashes.slots[0]),
           "the reference butterfly level overflowed its stash");
  }
  return stashes.Count();
}

// The claim: the fixed level's direct merge is an ORDINARY load-0.5 bucket: the union of (B[i], C[i]) is deduplicated and
// total, so its occupancy has the same mean as every other level built at the
// same load, and overflow is exactly |U_i| > 64 -- no worse for having had two
// physical inputs.
//
// Both halves of that are checked.  The sharp one is exact: the merge must shed
// exactly `sum_i max(|U_i| - 64, 0)` and lose nothing, which is what says the
// two inputs cost nothing.  The distributional one runs an ordinary butterfly
// level at the same mean over the same number of buckets and compares the two
// shed totals.
void TestFixedMergeShedMatchesOrdinaryLevel(unsigned levels, size_t mean,
                                            uint64_t seed) {
  bs::StashLayout slayout;
  slayout.key_bytes = 8;
  slayout.value_bytes = 16;
  slayout.tag_bytes = 4;
  const bs::Layout layout = slayout.Base();
  const size_t buckets = size_t{1} << levels;
  auto fresher = bs::Table::Create(buckets, layout);  // B
  auto older = bs::Table::Create(buckets, layout);    // C
  std::memset(fresher.data.get(), 0, buckets * layout.BucketBytes());
  std::memset(older.data.get(), 0, buckets * layout.BucketBytes());

  std::mt19937_64 rng(seed);
  std::poisson_distribution<size_t> poisson(static_cast<double>(mean));
  std::set<uint64_t> all_keys;
  size_t expected_shed = 0;
  size_t union_total = 0;
  uint64_t next_key = 1;
  for (size_t b = 0; b < buckets; ++b) {
    const size_t want = poisson(rng);
    size_t nb = 0, nc = 0, placed = 0;
    for (size_t i = 0; i < want; ++i) {
      const uint64_t key = next_key++;
      // 20% of keys are in BOTH sources -- the duplicates the merge resolves,
      // and the reason |U_i| is not |B[i]| + |C[i]|.
      const unsigned roll = static_cast<unsigned>(rng() % 10);
      const bool in_b = roll < 6 || roll >= 8;
      const bool in_c = roll >= 6;
      if ((in_b && nb == bs::kBucketCapacity) ||
          (in_c && nc == bs::kBucketCapacity)) {
        continue;  // a source bucket is full; that is not what is being tested
      }
      if (in_b) WriteKey(fresher.Bucket(b), nb++, layout.key_bytes, key);
      if (in_c) WriteKey(older.Bucket(b), nc++, layout.key_bytes, key);
      all_keys.insert(key);
      ++placed;
    }
    fresher.masks[b] = bs::LowMask64(static_cast<unsigned>(nb));
    older.masks[b] = bs::LowMask64(static_cast<unsigned>(nc));
    union_total += placed;
    if (placed > bs::kBucketCapacity) expected_shed += placed - bs::kBucketCapacity;
  }

  OwnedLevelStashes merge_stash(1, bs::kMaxResidualStashBuckets, slayout);
  Expect(bs::MergeFixedLevelSources</*CheckOverflow=*/true>(
             bs::View(older), bs::View(fresher), merge_stash.slots[0]),
         "the fixed merge overflowed its stash at the design load");
  Expect(merge_stash.Count() == expected_shed,
         "the fixed merge shed something other than |U_i| - 64");

  // Nothing may be lost: every distinct key is in the merged table or in the
  // stash, which is what the second chance then puts back.
  std::set<uint64_t> found;
  for (size_t b = 0; b < buckets; ++b) {
    for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
      if ((older.masks[b] >> e) & 1) {
        found.insert(ReadKey(older.Bucket(b), e, layout.key_bytes));
      }
    }
  }
  for (size_t b = 0; b < merge_stash.slots[0].num_buckets; ++b) {
    const uint64_t m = merge_stash.slots[0].masks[b];
    for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
      if ((m >> e) & 1) {
        found.insert(
            ReadKey(merge_stash.slots[0].Bucket(b), e, layout.key_bytes));
      }
    }
  }
  Expect(found == all_keys, "the fixed merge lost or invented an entry");

  const size_t ordinary = OrdinaryLevelShed(buckets / 2, mean, seed ^ 0xA5A5);
  const double observed_mean =
      static_cast<double>(union_total) / static_cast<double>(buckets);
  Expect(observed_mean > 0.9 * mean && observed_mean < 1.1 * mean,
         "the fixed merge's union does not have the load's mean occupancy");
  // Same statistic of the same mean-lambda occupancy, so at the design load
  // both are zero and above it both fire.  Anything sharper would be testing
  // the RNG: the reference level's inputs are truncated at 64 slots (as a real
  // level's are), which clips its upper tail relative to the merge's union.
  Expect((merge_stash.Count() == 0) == (ordinary == 0),
         "the fixed merge and an ordinary level disagree on whether a "
         "load-0.5 bucket at this mean sheds at all");
  std::printf("  fixed merge vs ordinary level, %zu buckets at mean %zu: "
              "union mean %.1f, shed %zu vs %zu\n",
              buckets, mean, observed_mean, merge_stash.Count(), ordinary);
}

}  // namespace

int main() {
  // Unbuffered: the progress lines are the first thing to look at when a run
  // is killed by a CI timeout.
  std::setvbuf(stdout, nullptr, _IONBF, 0);
  std::printf("cpu_byteslice_dedup_rebuild_test (VP2INTERSECT=%d, "
              "16-byte segment match=%d)\n",
              MICRORAM_BYTESLICE_USE_VP2INTERSECT,
              int{bs::kWideKeySegmentMatch});
  TestAllPairsMatchMasks();
  TestCrossBucketDuplicateMask();
  TestBucketSelfDuplicateMask();
  TestWideEqualityRequiresSamePartner();
  if (bs::kWideKeySegmentMatch) TestSegmentedConflictIsRelaxed();
  TestDedupDestinationsExact();
  TestMergeSplitPairDedupConserves();
  // The chain against the network it reorders, at load 0.25 (16 per
  // bucket) and deliberately denser, over a short and a long chain.
  TestIncrementalChainMatchesMonolithic(/*target=*/1, /*per_bucket=*/16);
  TestIncrementalChainMatchesMonolithic(/*target=*/4, /*per_bucket=*/16);
  TestIncrementalChainMatchesMonolithic(/*target=*/7, /*per_bucket=*/16);
  TestIncrementalChainMatchesMonolithic(/*target=*/6, /*per_bucket=*/24);
  // The fixed level's direct merge.  63/64/65 are the boundary unions --
  // a bucket holds 64, so 65 must be refused rather than silently truncated.
  TestFixedLevelMerge(8, 16, 16, 4, true, 0x9101);
  TestFixedLevelMerge(4, 32, 32, 32, true, 0x9102);
  TestFixedLevelMerge(4, 32, 31, 0, true, 0x9103);   // union 63
  TestFixedLevelMerge(4, 32, 32, 0, true, 0x9104);   // union 64
  TestFixedLevelMerge(4, 33, 32, 0, false, 0x9105);  // union 65: refused
  TestFixedLevelMerge(4, 40, 30, 30, true, 0x9106);  // 65 raw, 40 after dedup
  TestFixedLevelMergeMatchesFold(0x9110);
  // The fixed level is an ordinary load-0.5 level.  32 is the design
  // mean (nothing sheds either way); 52 and 58 are overloaded, where both the
  // merge and an ordinary butterfly level shed and the exact
  // sum_i max(|U_i| - 64, 0) equality is what carries the claim.
  TestFixedMergeShedMatchesOrdinaryLevel(/*levels=*/10, /*mean=*/32, 0x9120);
  TestFixedMergeShedMatchesOrdinaryLevel(/*levels=*/10, /*mean=*/52, 0x9121);
  TestFixedMergeShedMatchesOrdinaryLevel(/*levels=*/8, /*mean=*/58, 0x9122);
  // Load 0.5 is the design point and sheds essentially nothing; the
  // deliberately overloaded run is what drives residuals through the
  // cross-source MergeSplits.
  TestNetworkMatchesFlatButterfly(32, 2);
  TestNetworkMatchesFlatButterfly(56, 8);
  TestNetworkKeepsFreshestCopy(32, 2);
  TestNetworkKeepsFreshestCopy(56, 8);
  TestResidualPoolDedup();
  TestResidualPoolDedupMultiBucket();
  TestResidualPoolDedupWindows();
  TestResidualPoolEqualRankContract();
  TestResidualRangePlanStacks();
  // The multi-group sweep's own slice invariance: the (bucket, group) unit
  // space, cut at widths that divide neither the group count nor the bucket
  // count, in the DIRECT shape (unrouted, index_bits match live).
  TestStackedSweepSlicingAgrees(/*main_levels=*/2, /*pool_buckets=*/9,
                                /*n_residuals=*/120, /*dup_every=*/3, 0xA001);
  TestStackedSweepSlicingAgrees(/*main_levels=*/1, /*pool_buckets=*/3,
                                /*n_residuals=*/60, /*dup_every=*/2, 0xA003);
  // Deliberately OVERFLOWING, so leftovers actually exist and the
  // main-vs-leftover disjointness check has something to reject: 200 residuals
  // offered to a 2-bucket (128-slot) main, in 4 direct groups.  This is where
  // a group that re-inserted what an earlier group left behind would be
  // caught.
  TestStackedSweepSlicingAgrees(/*main_levels=*/1, /*pool_buckets=*/4,
                                /*n_residuals=*/200, /*dup_every=*/2, 0xA004);
  TestStackedSweepSlicingAgrees(/*main_levels=*/2, /*pool_buckets=*/12,
                                /*n_residuals=*/400, /*dup_every=*/3, 0xA005);
  // The merged class-marked offer: the two-answer kernel against the
  // scalar reference, and the offer against the split pair it replaces.
  TestCrossBucketClassDuplicateMasks();
  TestFullBucketAbsorbsNoCarryClass();
  TestClassMarkOfferMatchesSplitOffers(0xC1A50001ull);
  TestClassMarkOfferMatchesSplitOffers(0xC1A50002ull);
  TestClassMarkOfferMatchesSplitOffers(0xC1A50003ull);
  std::printf("all cpu_byteslice_dedup_rebuild tests passed\n");
  return 0;
}
