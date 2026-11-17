// Equivalence tests for the rebuild's key-comparison (dedup) kernels in
// src/oram/rebuild/cpu_byteslice_dedup_masks.hpp.  During a rebuild two
// buckets are compared slot against slot so that a stale copy of a key is
// dropped when a fresher copy exists; a missed duplicate resurrects an old
// value, and a spurious one loses an entry.
//
// Oracles.  Namespace `head` below holds a frozen, straightforward reference
// implementation of the same kernels (loaders, transposes, nested compare
// loops).  The narrow (single-field) widths and the register helpers must be
// bit-identical to it.  Wide entry points require exact full-key equality and
// are checked against an independent scalar oracle instead -- except 16-byte
// keys under kWideKeySegmentMatch (the approximate VP2INTERSECT segment match),
// which must equal the segment-wise `head` kernels.
//
// Inputs include dirty dummy slots (stale keys that must be ignored), the zero
// key, sparse and dense occupancies, every width 1..16, and wide keys
// assembled from small segment pools.  Segment-wise false positives are
// counted to show that the inputs actually distinguish the exact contract
// from the segment-wise one.

#include "src/oram/rebuild/cpu_byteslice_dedup_masks.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"

#include <immintrin.h>

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <random>
#include <vector>

namespace {

namespace bs = microram::byteslice;
using bs::kBucketCapacity;
using bs::test_support::Expect;

// ---------------------------------------------------------------------------
// The oracle: frozen reference kernels
// ---------------------------------------------------------------------------
namespace head {

inline void TransposeKeyLinesToQwords(const __m512i* l, __m512i* keys_out) {
  const __m512i b0 = _mm512_unpacklo_epi8(l[0], l[1]);
  const __m512i b1 = _mm512_unpackhi_epi8(l[0], l[1]);
  const __m512i b2 = _mm512_unpacklo_epi8(l[2], l[3]);
  const __m512i b3 = _mm512_unpackhi_epi8(l[2], l[3]);
  const __m512i b4 = _mm512_unpacklo_epi8(l[4], l[5]);
  const __m512i b5 = _mm512_unpackhi_epi8(l[4], l[5]);
  const __m512i b6 = _mm512_unpacklo_epi8(l[6], l[7]);
  const __m512i b7 = _mm512_unpackhi_epi8(l[6], l[7]);
  const __m512i c0 = _mm512_unpacklo_epi16(b0, b2);
  const __m512i c1 = _mm512_unpackhi_epi16(b0, b2);
  const __m512i c2 = _mm512_unpacklo_epi16(b1, b3);
  const __m512i c3 = _mm512_unpackhi_epi16(b1, b3);
  const __m512i c4 = _mm512_unpacklo_epi16(b4, b6);
  const __m512i c5 = _mm512_unpackhi_epi16(b4, b6);
  const __m512i c6 = _mm512_unpacklo_epi16(b5, b7);
  const __m512i c7 = _mm512_unpackhi_epi16(b5, b7);
  const __m512i d0 = _mm512_unpacklo_epi32(c0, c4);
  const __m512i d1 = _mm512_unpackhi_epi32(c0, c4);
  const __m512i d2 = _mm512_unpacklo_epi32(c1, c5);
  const __m512i d3 = _mm512_unpackhi_epi32(c1, c5);
  const __m512i d4 = _mm512_unpacklo_epi32(c2, c6);
  const __m512i d5 = _mm512_unpackhi_epi32(c2, c6);
  const __m512i d6 = _mm512_unpacklo_epi32(c3, c7);
  const __m512i d7 = _mm512_unpackhi_epi32(c3, c7);
  const __m512i e0 = _mm512_shuffle_i64x2(d0, d1, 0x88);
  const __m512i e1 = _mm512_shuffle_i64x2(d0, d1, 0xDD);
  const __m512i e2 = _mm512_shuffle_i64x2(d2, d3, 0x88);
  const __m512i e3 = _mm512_shuffle_i64x2(d2, d3, 0xDD);
  const __m512i e4 = _mm512_shuffle_i64x2(d4, d5, 0x88);
  const __m512i e5 = _mm512_shuffle_i64x2(d4, d5, 0xDD);
  const __m512i e6 = _mm512_shuffle_i64x2(d6, d7, 0x88);
  const __m512i e7 = _mm512_shuffle_i64x2(d6, d7, 0xDD);
  keys_out[0] = _mm512_shuffle_i64x2(e0, e2, 0x88);
  keys_out[2] = _mm512_shuffle_i64x2(e1, e3, 0x88);
  keys_out[4] = _mm512_shuffle_i64x2(e0, e2, 0xDD);
  keys_out[6] = _mm512_shuffle_i64x2(e1, e3, 0xDD);
  keys_out[1] = _mm512_shuffle_i64x2(e4, e6, 0x88);
  keys_out[3] = _mm512_shuffle_i64x2(e5, e7, 0x88);
  keys_out[5] = _mm512_shuffle_i64x2(e4, e6, 0xDD);
  keys_out[7] = _mm512_shuffle_i64x2(e5, e7, 0xDD);
}

inline void TransposeKeyLinesToDwords(const __m512i* l, __m512i* keys_out) {
  const __m512i b0 = _mm512_unpacklo_epi8(l[0], l[1]);
  const __m512i b1 = _mm512_unpackhi_epi8(l[0], l[1]);
  const __m512i b2 = _mm512_unpacklo_epi8(l[2], l[3]);
  const __m512i b3 = _mm512_unpackhi_epi8(l[2], l[3]);
  const __m512i c0 = _mm512_unpacklo_epi16(b0, b2);
  const __m512i c1 = _mm512_unpackhi_epi16(b0, b2);
  const __m512i c2 = _mm512_unpacklo_epi16(b1, b3);
  const __m512i c3 = _mm512_unpackhi_epi16(b1, b3);
  const __m512i e0 = _mm512_shuffle_i64x2(c0, c1, 0x88);
  const __m512i e1 = _mm512_shuffle_i64x2(c0, c1, 0xDD);
  const __m512i e2 = _mm512_shuffle_i64x2(c2, c3, 0x88);
  const __m512i e3 = _mm512_shuffle_i64x2(c2, c3, 0xDD);
  keys_out[0] = _mm512_shuffle_i64x2(e0, e2, 0x88);
  keys_out[2] = _mm512_shuffle_i64x2(e0, e2, 0xDD);
  keys_out[1] = _mm512_shuffle_i64x2(e1, e3, 0x88);
  keys_out[3] = _mm512_shuffle_i64x2(e1, e3, 0xDD);
}

inline uint64_t LoadKeyLinesZeroingDummies(const uint8_t* bucket,
                                           size_t key_bytes, uint64_t real,
                                           size_t lanes, __m512i* lines) {
  const __mmask64 keep = _cvtu64_mask64(real);
  uint64_t zero_key = real;
  for (size_t i = 0; i < lanes; ++i) {
    if (i < key_bytes) {
      const __m512i line = _mm512_maskz_mov_epi8(
          keep, microram::core::obliLoad512(bucket + i * kBucketCapacity));
      lines[i] = line;
      zero_key &= _cvtmask64_u64(_mm512_testn_epi8_mask(line, line));
    } else {
      lines[i] = _mm512_setzero_si512();
    }
  }
  return zero_key;
}

inline uint64_t AllPairsMatchMaskQFallback(const __m512i* a, const __m512i* b) {
  __m512i acc[8];
  for (int j = 0; j < 8; ++j) acc[j] = _mm512_set1_epi64(-1);
  for (int i = 0; i < 8; ++i) {
    __m512i ai = a[i];
    for (int r = 0; r < 8; ++r) {
      for (int j = 0; j < 8; ++j) {
        acc[j] = _mm512_min_epu64(acc[j], _mm512_xor_si512(ai, b[j]));
      }
      ai = _mm512_alignr_epi64(ai, ai, 1);
    }
  }
  uint64_t dup = 0;
  for (int j = 0; j < 8; ++j) {
    dup |= static_cast<uint64_t>(
               _cvtmask8_u32(_mm512_testn_epi64_mask(acc[j], acc[j])))
           << (8 * j);
  }
  return dup;
}

inline uint64_t AllPairsMatchMaskDFallback(const __m512i* a, const __m512i* b) {
  __m512i acc[4];
  for (int j = 0; j < 4; ++j) acc[j] = _mm512_set1_epi32(-1);
  for (int i = 0; i < 4; ++i) {
    __m512i ai = a[i];
    for (int r = 0; r < 16; ++r) {
      for (int j = 0; j < 4; ++j) {
        acc[j] = _mm512_min_epu32(acc[j], _mm512_xor_si512(ai, b[j]));
      }
      ai = _mm512_alignr_epi32(ai, ai, 1);
    }
  }
  uint64_t dup = 0;
  for (int j = 0; j < 4; ++j) {
    dup |= static_cast<uint64_t>(
               _cvtmask16_u32(_mm512_testn_epi32_mask(acc[j], acc[j])))
           << (16 * j);
  }
  return dup;
}

inline uint64_t AllPairsMatchMaskQ(const __m512i* a, const __m512i* b) {
#if MICRORAM_BYTESLICE_USE_VP2INTERSECT
  uint64_t dup = 0;
  for (int j = 0; j < 8; ++j) {
    __mmask8 acc = 0;
    for (int i = 0; i < 8; ++i) {
      acc = _kor_mask8(acc, bs::IntersectSecondMaskQ(a[i], b[j]));
    }
    dup |= static_cast<uint64_t>(_cvtmask8_u32(acc)) << (8 * j);
  }
  return dup;
#else
  return AllPairsMatchMaskQFallback(a, b);
#endif
}

inline uint64_t AllPairsMatchMaskD(const __m512i* a, const __m512i* b) {
#if MICRORAM_BYTESLICE_USE_VP2INTERSECT
  uint64_t dup = 0;
  for (int j = 0; j < 4; ++j) {
    __mmask16 acc = 0;
    for (int i = 0; i < 4; ++i) {
      acc = _kor_mask16(acc, bs::IntersectSecondMaskD(a[i], b[j]));
    }
    dup |= static_cast<uint64_t>(_cvtmask16_u32(acc)) << (16 * j);
  }
  return dup;
#else
  return AllPairsMatchMaskDFallback(a, b);
#endif
}

inline uint64_t RepairZeroKeyMatches(uint64_t raw, uint64_t zero_first,
                                     uint64_t zero_second,
                                     uint64_t second_real) {
  const uint64_t zero_hit = uint64_t{0} - static_cast<uint64_t>(zero_first != 0);
  return ((raw & ~zero_second) | (zero_second & zero_hit)) & second_real;
}

inline uint64_t CrossBucketFieldMatchMaskD(const uint8_t* first,
                                           uint64_t first_real,
                                           const uint8_t* second,
                                           uint64_t second_real,
                                           size_t field_bytes) {
  __m512i fl[4], sl[4];
  const uint64_t zero_first =
      LoadKeyLinesZeroingDummies(first, field_bytes, first_real, 4, fl);
  const uint64_t zero_second =
      LoadKeyLinesZeroingDummies(second, field_bytes, second_real, 4, sl);
  __m512i a[4], b[4];
  TransposeKeyLinesToDwords(fl, a);
  TransposeKeyLinesToDwords(sl, b);
  return RepairZeroKeyMatches(AllPairsMatchMaskD(a, b), zero_first, zero_second,
                              second_real);
}

inline uint64_t CrossBucketFieldMatchMaskQ(const uint8_t* first,
                                           uint64_t first_real,
                                           const uint8_t* second,
                                           uint64_t second_real,
                                           size_t field_bytes) {
  __m512i fl[8], sl[8];
  const uint64_t zero_first =
      LoadKeyLinesZeroingDummies(first, field_bytes, first_real, 8, fl);
  const uint64_t zero_second =
      LoadKeyLinesZeroingDummies(second, field_bytes, second_real, 8, sl);
  __m512i a[8], b[8];
  TransposeKeyLinesToQwords(fl, a);
  TransposeKeyLinesToQwords(sl, b);
  return RepairZeroKeyMatches(AllPairsMatchMaskQ(a, b), zero_first, zero_second,
                              second_real);
}

inline uint64_t CrossBucketDuplicateMask(const uint8_t* first,
                                         uint64_t first_real,
                                         const uint8_t* second,
                                         uint64_t second_real,
                                         size_t key_bytes) {
  if (key_bytes <= 4) {
    return CrossBucketFieldMatchMaskD(first, first_real, second, second_real,
                                      key_bytes);
  }
  if (key_bytes <= 8) {
    return CrossBucketFieldMatchMaskQ(first, first_real, second, second_real,
                                      key_bytes);
  }
  uint64_t dup = second_real;
  for (size_t off = 0; off < key_bytes; off += 4) {
    const size_t field = std::min<size_t>(4, key_bytes - off);
    dup &= CrossBucketFieldMatchMaskD(first + off * kBucketCapacity, first_real,
                                      second + off * kBucketCapacity,
                                      second_real, field);
  }
  return dup;
}

template <bool Qwords>
inline void DedupBucketDestinationsNarrow(
    const uint8_t* first, uint64_t first_real, uint8_t* const* destinations,
    uint64_t* const* masks, size_t count, size_t key_bytes) {
  constexpr size_t n = Qwords ? 8 : 4;
  __m512i lines[n], keys[n];
  const uint64_t zero = LoadKeyLinesZeroingDummies(first, key_bytes,
                                                  first_real, n, lines);
  if constexpr (Qwords) TransposeKeyLinesToQwords(lines, keys);
  else TransposeKeyLinesToDwords(lines, keys);
  for (size_t q = 0; q < count; ++q) {
    __m512i other_lines[n], other_keys[n];
    const uint64_t real = *masks[q];
    const uint64_t other_zero = LoadKeyLinesZeroingDummies(
        destinations[q], key_bytes, real, n, other_lines);
    if constexpr (Qwords) TransposeKeyLinesToQwords(other_lines, other_keys);
    else TransposeKeyLinesToDwords(other_lines, other_keys);
    const uint64_t raw = Qwords ? AllPairsMatchMaskQ(keys, other_keys)
                                : AllPairsMatchMaskD(keys, other_keys);
    *masks[q] &= ~RepairZeroKeyMatches(raw, zero, other_zero, real);
  }
}

inline void DedupBucketDestinationsWide(
    const uint8_t* first, uint64_t first_real, uint8_t* const* destinations,
    uint64_t* const* masks, size_t count) {
  __m512i keys[4][4];
  uint64_t zero[4];
  for (size_t f = 0; f < 4; ++f) {
    __m512i lines[4];
    zero[f] = LoadKeyLinesZeroingDummies(first + f * 4 * kBucketCapacity,
                                         4, first_real, 4, lines);
    TransposeKeyLinesToDwords(lines, keys[f]);
  }
  for (size_t q = 0; q < count; ++q) {
    const uint64_t real = *masks[q];
    uint64_t dup = real;
    for (size_t f = 0; f < 4; ++f) {
      __m512i lines[4], other[4];
      const uint64_t other_zero = LoadKeyLinesZeroingDummies(
          destinations[q] + f * 4 * kBucketCapacity, 4, real, 4, lines);
      TransposeKeyLinesToDwords(lines, other);
      dup &= RepairZeroKeyMatches(AllPairsMatchMaskD(keys[f], other),
                                   zero[f], other_zero, real);
    }
    *masks[q] &= ~dup;
  }
}

inline void DedupBucketDestinations(
    const uint8_t* first, uint64_t first_real, uint8_t* const* destinations,
    uint64_t* const* masks, size_t count, size_t key_bytes) {
  if (count > 1 && key_bytes <= 8) {
    if (key_bytes <= 4)
      DedupBucketDestinationsNarrow<false>(first, first_real, destinations,
                                          masks, count, key_bytes);
    else
      DedupBucketDestinationsNarrow<true>(first, first_real, destinations,
                                         masks, count, key_bytes);
    return;
  }
  if (count > 1 && key_bytes == 16) {
    DedupBucketDestinationsWide(first, first_real, destinations, masks, count);
    return;
  }
  for (size_t q = 0; q < count; ++q) {
    *masks[q] &= ~CrossBucketDuplicateMask(first, first_real, destinations[q],
                                           *masks[q], key_bytes);
  }
}

template <bool Qwords>
inline void CrossBucketClassFieldMasks(const uint8_t* first,
                                       uint64_t first_real,
                                       const uint8_t* second,
                                       uint64_t carry_real, uint64_t tier_real,
                                       size_t field_bytes,
                                       uint64_t* first_dup,
                                       uint64_t* carry_dup) {
  constexpr size_t n = Qwords ? 8 : 4;
  __m512i fl[n], sl[n], a[n], b[n], selected[n];
  const uint64_t zero_first =
      LoadKeyLinesZeroingDummies(first, field_bytes, first_real, n, fl);
  const uint64_t zero_second = LoadKeyLinesZeroingDummies(
      second, field_bytes, carry_real | tier_real, n, sl);
  if constexpr (Qwords) {
    TransposeKeyLinesToQwords(fl, a);
    TransposeKeyLinesToQwords(sl, b);
  } else {
    TransposeKeyLinesToDwords(fl, a);
    TransposeKeyLinesToDwords(sl, b);
  }
  for (size_t i = 0; i < n; ++i) {
    if constexpr (Qwords) {
      selected[i] = microram::core::obliMaskMov64(
          _mm512_setzero_si512(), tier_real >> (8 * i), b[i]);
    } else {
      selected[i] = microram::core::obliMaskMov32(
          _mm512_setzero_si512(), tier_real >> (16 * i), b[i]);
    }
  }
  const uint64_t hit_first = Qwords ? AllPairsMatchMaskQ(selected, a)
                                   : AllPairsMatchMaskD(selected, a);
  *first_dup = RepairZeroKeyMatches(hit_first, zero_second & tier_real,
                                    zero_first, first_real);
  const uint64_t hit_carry = Qwords ? AllPairsMatchMaskQ(a, b)
                                   : AllPairsMatchMaskD(a, b);
  *carry_dup = RepairZeroKeyMatches(hit_carry, zero_first,
                                    zero_second & carry_real, carry_real);
}

inline void CrossBucketClassDuplicateMasks(const uint8_t* first,
                                           uint64_t first_real,
                                           const uint8_t* second,
                                           uint64_t carry_real,
                                           uint64_t tier_real,
                                           size_t key_bytes,
                                           uint64_t* first_dup,
                                           uint64_t* carry_dup) {
  if (key_bytes <= 8) {
    if (key_bytes <= 4) {
      CrossBucketClassFieldMasks<false>(first, first_real, second, carry_real,
                                        tier_real, key_bytes, first_dup,
                                        carry_dup);
    } else {
      CrossBucketClassFieldMasks<true>(first, first_real, second, carry_real,
                                       tier_real, key_bytes, first_dup,
                                       carry_dup);
    }
    return;
  }
  uint64_t first_match = first_real, carry_match = carry_real;
  for (size_t off = 0; off < key_bytes; off += 4) {
    uint64_t first_field, carry_field;
    CrossBucketClassFieldMasks<false>(
        first + off * kBucketCapacity, first_real,
        second + off * kBucketCapacity, carry_real, tier_real,
        std::min<size_t>(4, key_bytes - off), &first_field, &carry_field);
    first_match &= first_field;
    carry_match &= carry_field;
  }
  *first_dup = first_match;
  *carry_dup = carry_match;
}

inline uint64_t BucketSelfFieldMatchMaskD(const uint8_t* bucket, uint64_t real,
                                          size_t field_bytes) {
  __m512i l[4], a[4];
  const uint64_t zero =
      LoadKeyLinesZeroingDummies(bucket, field_bytes, real, 4, l);
  TransposeKeyLinesToDwords(l, a);
  uint64_t dup = 0;
  for (int j = 0; j < 4; ++j) {
    const __m512i conf = _mm512_conflict_epi32(a[j]);
    uint64_t acc = _cvtmask16_u32(_mm512_test_epi32_mask(conf, conf));
    for (int i = 0; i < j; ++i) {
      acc |= _cvtmask16_u32(bs::IntersectSecondMaskD(a[i], a[j]));
    }
    dup |= acc << (16 * j);
  }
  return ((dup & ~zero) | (zero & (zero - 1))) & real;
}

inline uint64_t BucketSelfFieldMatchMaskQ(const uint8_t* bucket, uint64_t real,
                                          size_t field_bytes) {
  __m512i l[8], a[8];
  const uint64_t zero =
      LoadKeyLinesZeroingDummies(bucket, field_bytes, real, 8, l);
  TransposeKeyLinesToQwords(l, a);
  uint64_t dup = 0;
  for (int j = 0; j < 8; ++j) {
    const __m512i conf = _mm512_conflict_epi64(a[j]);
    uint64_t acc = _cvtmask8_u32(_mm512_test_epi64_mask(conf, conf));
    for (int i = 0; i < j; ++i) {
      acc |= _cvtmask8_u32(bs::IntersectSecondMaskQ(a[i], a[j]));
    }
    dup |= acc << (8 * j);
  }
  return ((dup & ~zero) | (zero & (zero - 1))) & real;
}

inline uint64_t BucketSelfDuplicateMask(const uint8_t* bucket, uint64_t real,
                                        size_t key_bytes) {
  if (key_bytes <= 4) return BucketSelfFieldMatchMaskD(bucket, real, key_bytes);
  if (key_bytes <= 8) return BucketSelfFieldMatchMaskQ(bucket, real, key_bytes);
  uint64_t dup = real;
  for (size_t off = 0; off < key_bytes; off += 4) {
    const size_t field = std::min<size_t>(4, key_bytes - off);
    dup &= BucketSelfFieldMatchMaskD(bucket + off * kBucketCapacity, real,
                                     field);
  }
  return dup;
}

}  // namespace head

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

// Byte lines per bucket: the 16 key lines of the widest key plus a few more,
// so the lines past a narrow key's width hold garbage a kernel must not read
// as key bytes.
constexpr size_t kLines = bs::kMaxKeyBytes + 4;
constexpr size_t kBucketBytes = kLines * kBucketCapacity;
constexpr size_t kMaxBuckets = 10;

struct Buckets {
  alignas(64) uint8_t data[kMaxBuckets][kBucketBytes];
  uint8_t* operator[](size_t i) { return data[i]; }
};

// Key byte l of slot e is byte e of line l.
void WriteKey(uint8_t* bucket, size_t slot, size_t key_bytes,
              const uint8_t* key) {
  for (size_t l = 0; l < key_bytes; ++l) {
    bucket[l * kBucketCapacity + slot] = key[l];
  }
}

// A pool of keys of one width.  Entry 0 is the zero key the repair exists
// for.  Wide keys are assembled from a small pool of 4-byte segments, so two
// different keys often share every segment with SOME key of the other bucket
// -- the segment-wise false positive -- and narrow keys differ in few bits.
std::vector<std::vector<uint8_t>> MakePool(std::mt19937_64& rng,
                                           size_t key_bytes, size_t size) {
  std::vector<std::vector<uint8_t>> pool(size,
                                         std::vector<uint8_t>(key_bytes, 0));
  std::vector<uint32_t> segments(1 + rng() % 3);
  for (uint32_t& s : segments) s = static_cast<uint32_t>(rng());
  segments[0] = 0;
  for (size_t k = 1; k < size; ++k) {
    std::vector<uint8_t>& key = pool[k];
    switch (rng() % 4) {
      case 0:  // independent random bytes
        for (uint8_t& b : key) b = static_cast<uint8_t>(rng());
        break;
      case 1:  // a near miss of an earlier key: one bit flipped
        key = pool[rng() % k];
        key[rng() % key_bytes] ^= static_cast<uint8_t>(1u << (rng() % 8));
        break;
      default:  // segments drawn from the shared segment pool
        for (size_t off = 0; off < key_bytes; off += 4) {
          const uint32_t s = segments[rng() % segments.size()];
          for (size_t b = off; b < std::min(key_bytes, off + 4); ++b) {
            key[b] = static_cast<uint8_t>(s >> (8 * (b - off)));
          }
        }
        break;
    }
  }
  return pool;
}

uint64_t Occupancy(std::mt19937_64& rng) {
  switch (rng() % 10) {
    case 0: return 0;
    case 1: return ~uint64_t{0};
    case 2: return uint64_t{1} << (rng() % 64);
    case 3: return ~(uint64_t{1} << (rng() % 64));
    case 4: return rng() & rng() & rng();  // sparse
    case 5: return rng() | rng() | rng();  // dense
    default: return rng();
  }
}

// Fills `bucket` with garbage, then gives every slot, real or dummy, a key
// drawn from the pool, a quarter of the dummies keeping their garbage.  A
// dummy holding a live key of the other bucket is the case dummy zeroing
// exists for, so it must be common.
void FillBucket(std::mt19937_64& rng, uint8_t* bucket, size_t key_bytes,
                const std::vector<std::vector<uint8_t>>& pool, uint64_t real) {
  for (size_t i = 0; i < kBucketBytes; i += 8) {
    const uint64_t g = rng();
    std::memcpy(bucket + i, &g, 8);
  }
  for (size_t e = 0; e < kBucketCapacity; ++e) {
    if (!((real >> e) & 1) && rng() % 4 == 0) continue;
    WriteKey(bucket, e, key_bytes, pool[rng() % pool.size()].data());
  }
}

bool SameBytes(const __m512i* a, const __m512i* b, size_t n) {
  return std::memcmp(a, b, n * sizeof(__m512i)) == 0;
}

size_t g_trials = 0;
size_t g_nonzero = 0;       // trials in which some compared word was nonzero
size_t g_segment_fp = 0;    // 16-byte trials where segments matched spuriously

// Independent full-key equality for all widths; no SIMD helper is reused.
uint64_t ExactDuplicateMask(const uint8_t* first, uint64_t first_real,
                            const uint8_t* second, uint64_t second_real,
                            size_t key_bytes) {
  uint64_t dup = 0;
  for (size_t e = 0; e < kBucketCapacity; ++e) {
    if (!((second_real >> e) & 1)) continue;
    for (size_t f = 0; f < kBucketCapacity; ++f) {
      if (!((first_real >> f) & 1)) continue;
      bool equal = true;
      for (size_t l = 0; l < key_bytes && equal; ++l) {
        equal = first[l * kBucketCapacity + f] ==
                second[l * kBucketCapacity + e];
      }
      if (equal) {
        dup |= uint64_t{1} << e;
        break;
      }
    }
  }
  return dup;
}

uint64_t ExactSelfDuplicateMask(const uint8_t* bucket, uint64_t real,
                                size_t key_bytes) {
  uint64_t dup = 0;
  for (size_t e = 0; e < kBucketCapacity; ++e) {
    const uint64_t bit = uint64_t{1} << e;
    dup |= ExactDuplicateMask(bucket, real & (bit - 1), bucket, real & bit,
                              key_bytes);
  }
  return dup;
}

// ---------------------------------------------------------------------------
// Register kernels: loaders, transposes, nests
// ---------------------------------------------------------------------------

void TestRegisterKernels() {
  std::mt19937_64 rng(0x4E575451ull);
  Buckets buf;
  for (int trial = 0; trial < 4000; ++trial) {
    const size_t key_bytes = 1 + static_cast<size_t>(rng() % bs::kMaxKeyBytes);
    const auto pool = MakePool(rng, key_bytes, 1 + rng() % 24);
    const uint64_t real[2] = {Occupancy(rng), Occupancy(rng)};
    FillBucket(rng, buf[0], key_bytes, pool, real[0]);
    FillBucket(rng, buf[1], key_bytes, pool, real[1]);

    // Loaders, at both lane counts.
    for (size_t lanes : {size_t{4}, size_t{8}}) {
      __m512i want[8], zeroed[8], kept[8];
      const uint64_t zero_want =
          head::LoadKeyLinesZeroingDummies(buf[0], key_bytes, real[0], lanes,
                                           want);
      Expect(bs::LoadKeyLinesZeroingDummies(buf[0], key_bytes, real[0], lanes,
                                            zeroed) == zero_want,
             "zeroing loader: zero-key mask differs from HEAD");
      Expect(SameBytes(zeroed, want, lanes),
             "zeroing loader: lines differ from HEAD");
      Expect(bs::LoadKeyLinesKeepingDummies(buf[0], key_bytes, real[0], lanes,
                                            kept) == zero_want,
             "keeping loader: zero-key mask differs from HEAD");
      for (size_t i = 0; i < lanes; ++i) {
        const __m512i raw =
            i < key_bytes ? _mm512_load_si512(buf[0] + i * kBucketCapacity)
                          : _mm512_setzero_si512();
        Expect(SameBytes(&kept[i], &raw, 1),
               "keeping loader: a line is not the stored line");
      }
    }

    __m512i fl[8], sl[8];
    head::LoadKeyLinesZeroingDummies(buf[0], 8, real[0], 8, fl);
    for (size_t i = 0; i < 8; ++i) {
      sl[i] = _mm512_load_si512(buf[1] + i * kBucketCapacity);
    }

    // Transposes, and the documented slot map of the unpacked forms.
    __m512i want_a[8], want_b[8], got[8], ua[8], ub[8];
    head::TransposeKeyLinesToQwords(fl, want_a);
    head::TransposeKeyLinesToQwords(sl, want_b);
    bs::TransposeKeyLinesToQwords(fl, got);
    Expect(SameBytes(got, want_a, 8), "TransposeKeyLinesToQwords differs");
    bs::UnpackKeyLinesToQwords(fl, ua);
    bs::UnpackKeyLinesToQwords(sl, ub);
    for (size_t j = 0; j < 8; ++j) {
      for (size_t q = 0; q < 4; ++q) {
        for (size_t t = 0; t < 2; ++t) {
          const size_t slot = 16 * q + 2 * j + t;
          Expect(std::memcmp(reinterpret_cast<const uint64_t*>(&ub[j]) +
                                 2 * q + t,
                             reinterpret_cast<const uint64_t*>(want_b) + slot,
                             8) == 0,
                 "UnpackKeyLinesToQwords does not hold slot 16q+2j+t in "
                 "qword 2q+t");
        }
      }
    }
    __m512i want_da[4], want_db[4], dgot[4], da[4], db[4];
    head::TransposeKeyLinesToDwords(fl, want_da);
    head::TransposeKeyLinesToDwords(sl, want_db);
    bs::TransposeKeyLinesToDwords(fl, dgot);
    Expect(SameBytes(dgot, want_da, 4), "TransposeKeyLinesToDwords differs");
    bs::UnpackKeyLinesToDwords(fl, da);
    bs::UnpackKeyLinesToDwords(sl, db);
    for (size_t j = 0; j < 4; ++j) {
      for (size_t q = 0; q < 4; ++q) {
        for (size_t t = 0; t < 4; ++t) {
          const size_t slot = 16 * q + 4 * j + t;
          Expect(std::memcmp(reinterpret_cast<const uint32_t*>(&db[j]) +
                                 4 * q + t,
                             reinterpret_cast<const uint32_t*>(want_db) + slot,
                             4) == 0,
                 "UnpackKeyLinesToDwords does not hold slot 16q+4j+t in "
                 "dword 4q+t");
        }
      }
    }

    // Nests: slot order and unpacked order, native and fallback.
    const uint64_t q_want = head::AllPairsMatchMaskQ(want_a, want_b);
    Expect(head::AllPairsMatchMaskQFallback(want_a, want_b) == q_want,
           "oracle self-check: Q fallback disagrees with the native nest");
    Expect(bs::AllPairsMatchMaskQ(want_a, want_b) == q_want &&
               bs::AllPairsMatchMaskQFallback(want_a, want_b) == q_want,
           "slot-order AllPairsMatchMaskQ differs from HEAD");
    Expect(bs::AllPairsMatchMaskQ<true>(ua, ub) == q_want &&
               bs::AllPairsMatchMaskQFallback<true>(ua, ub) == q_want,
           "unpacked AllPairsMatchMaskQ differs from HEAD");
    const uint64_t d_want = head::AllPairsMatchMaskD(want_da, want_db);
    Expect(head::AllPairsMatchMaskDFallback(want_da, want_db) == d_want,
           "oracle self-check: D fallback disagrees with the native nest");
    Expect(bs::AllPairsMatchMaskD(want_da, want_db) == d_want &&
               bs::AllPairsMatchMaskDFallback(want_da, want_db) == d_want,
           "slot-order AllPairsMatchMaskD differs from HEAD");
    Expect(bs::AllPairsMatchMaskD<true>(da, db) == d_want &&
               bs::AllPairsMatchMaskDFallback<true>(da, db) == d_want,
           "unpacked AllPairsMatchMaskD differs from HEAD");
  }
  std::printf("  loaders, transposes and nests agree with HEAD\n");
}

// ---------------------------------------------------------------------------
// Entry points
// ---------------------------------------------------------------------------

// The `head` reference kernels are the oracle at the widths whose contract
// they share: the single-field ones, and 16 bytes under kWideKeySegmentMatch.
bool HeadIsOracle(size_t key_bytes) {
  return key_bytes <= 8 || (bs::kWideKeySegmentMatch && key_bytes == 16);
}

void TestEntryPoints(size_t key_bytes, int trials, std::mt19937_64& rng) {
  Buckets buf;
  for (int trial = 0; trial < trials; ++trial) {
    ++g_trials;
    const auto pool = MakePool(rng, key_bytes, 1 + rng() % 24);
    uint64_t real[kMaxBuckets];
    for (size_t b = 0; b < kMaxBuckets; ++b) {
      real[b] = Occupancy(rng);
      FillBucket(rng, buf[b], key_bytes, pool, real[b]);
    }
    uint64_t nonzero = 0;

    // CrossBucketDuplicateMask, both directions.
    for (int dir = 0; dir < 2; ++dir) {
      const size_t f = static_cast<size_t>(dir), s = 1 - f;
      // head's (segment-wise) answer; it may report segment-match false
      // positives at 16-byte keys, where `exact` is the oracle.
      const uint64_t historical = head::CrossBucketDuplicateMask(
          buf[f], real[f], buf[s], real[s], key_bytes);
      const uint64_t exact = ExactDuplicateMask(
          buf[f], real[f], buf[s], real[s], key_bytes);
      const uint64_t want = HeadIsOracle(key_bytes) ? historical : exact;
      Expect(bs::CrossBucketDuplicateMask(buf[f], real[f], buf[s], real[s],
                                          key_bytes) == want,
             "CrossBucketDuplicateMask differs from its equality oracle");
      nonzero |= want;
      if (key_bytes == 16 && historical != exact) {
        ++g_segment_fp;
      }
    }

    // The single-field kernels at every width they accept.
    if (key_bytes <= 4) {
      Expect(bs::CrossBucketFieldMatchMaskD(buf[0], real[0], buf[1], real[1],
                                            key_bytes) ==
                 head::CrossBucketFieldMatchMaskD(buf[0], real[0], buf[1],
                                                  real[1], key_bytes),
             "CrossBucketFieldMatchMaskD differs from HEAD");
    }
    if (key_bytes <= 8) {
      Expect(bs::CrossBucketFieldMatchMaskQ(buf[0], real[0], buf[1], real[1],
                                            key_bytes) ==
                 head::CrossBucketFieldMatchMaskQ(buf[0], real[0], buf[1],
                                                  real[1], key_bytes),
             "CrossBucketFieldMatchMaskQ differs from HEAD");
    }

    // DedupBucketDestinations: 0..8 destinations, with aliased destination
    // buckets and aliased mask words in some trials.
    {
      const size_t count = rng() % (kMaxBuckets - 1);
      uint8_t* dests[kMaxBuckets];
      uint64_t want_masks[kMaxBuckets], got_masks[kMaxBuckets];
      uint64_t* want_ptrs[kMaxBuckets];
      uint64_t* got_ptrs[kMaxBuckets];
      const bool alias = rng() % 4 == 0;
      for (size_t q = 0; q < count; ++q) {
        const size_t b = alias && q > 0 && rng() % 2 ? 1 + rng() % q : 1 + q;
        dests[q] = buf[b];
        want_masks[q] = got_masks[q] = real[1 + q];
        const size_t m = alias && q > 0 && rng() % 2 ? rng() % q : q;
        want_ptrs[q] = &want_masks[m];
        got_ptrs[q] = &got_masks[m];
      }
      if (HeadIsOracle(key_bytes)) {
        head::DedupBucketDestinations(buf[0], real[0], dests, want_ptrs, count,
                                      key_bytes);
      } else {
        for (size_t q = 0; q < count; ++q)
          *want_ptrs[q] &= ~ExactDuplicateMask(
              buf[0], real[0], dests[q], *want_ptrs[q], key_bytes);
      }
      bs::DedupBucketDestinations(buf[0], real[0], dests, got_ptrs, count,
                                  key_bytes);
      for (size_t q = 0; q < count; ++q) {
        Expect(got_masks[q] == want_masks[q],
               "DedupBucketDestinations differs from its equality oracle");
        nonzero |= real[1 + q] & ~want_masks[q];
      }
    }

    // CrossBucketClassDuplicateMasks, and the field kernels it wraps.
    {
      const uint64_t classes = rng() % 8 == 0   ? 0
                               : rng() % 8 == 0 ? ~uint64_t{0}
                                                : rng();
      const uint64_t tier = real[1] & classes;
      const uint64_t carry = real[1] & ~classes;
      uint64_t want_first = 0, want_carry = 0, got_first = 0, got_carry = 0;
      if (HeadIsOracle(key_bytes)) {
        head::CrossBucketClassDuplicateMasks(buf[0], real[0], buf[1], carry,
                                             tier, key_bytes, &want_first,
                                             &want_carry);
      } else {
        want_first = ExactDuplicateMask(buf[1], tier, buf[0], real[0], key_bytes);
        want_carry = ExactDuplicateMask(buf[0], real[0], buf[1], carry, key_bytes);
      }
      bs::CrossBucketClassDuplicateMasks(buf[0], real[0], buf[1], carry, tier,
                                         key_bytes, &got_first, &got_carry);
      Expect(got_first == want_first && got_carry == want_carry,
             "CrossBucketClassDuplicateMasks differs from its equality oracle");
      nonzero |= want_first | want_carry;
      if (key_bytes <= 4) {
        head::CrossBucketClassFieldMasks<false>(buf[0], real[0], buf[1], carry,
                                                tier, key_bytes, &want_first,
                                                &want_carry);
        bs::CrossBucketClassFieldMasks<false>(buf[0], real[0], buf[1], carry,
                                              tier, key_bytes, &got_first,
                                              &got_carry);
        Expect(got_first == want_first && got_carry == want_carry,
               "CrossBucketClassFieldMasks<false> differs from HEAD");
      }
      if (key_bytes <= 8) {
        head::CrossBucketClassFieldMasks<true>(buf[0], real[0], buf[1], carry,
                                               tier, key_bytes, &want_first,
                                               &want_carry);
        bs::CrossBucketClassFieldMasks<true>(buf[0], real[0], buf[1], carry,
                                             tier, key_bytes, &got_first,
                                             &got_carry);
        Expect(got_first == want_first && got_carry == want_carry,
               "CrossBucketClassFieldMasks<true> differs from HEAD");
      }
    }

    // The self-dedup shares the loader and the transposes.
    const uint64_t self_expected = HeadIsOracle(key_bytes)
        ? head::BucketSelfDuplicateMask(buf[2], real[2], key_bytes)
        : ExactSelfDuplicateMask(buf[2], real[2], key_bytes);
    Expect(bs::BucketSelfDuplicateMask(buf[2], real[2], key_bytes) == self_expected,
           "BucketSelfDuplicateMask differs from its equality oracle");

    if (nonzero != 0) ++g_nonzero;
  }
}

}  // namespace

int main() {
  std::printf("dedup narrow equivalence and exact wide equality "
              "(16-byte segment match %d)\n", int{bs::kWideKeySegmentMatch});
  TestRegisterKernels();
  std::mt19937_64 rng(0x5E9D0C75ull);
  for (size_t key_bytes = 1; key_bytes <= bs::kMaxKeyBytes; ++key_bytes) {
    const bool specialized =
        key_bytes == 4 || key_bytes == 8 || key_bytes == 16;
    TestEntryPoints(key_bytes, specialized ? 3000 : 600, rng);
  }
  std::printf("  entry points agree with equality oracles at widths 1..16 "
              "(%zu trials, %zu with matches, %zu segment-match false positives)\n",
              g_trials, g_nonzero, g_segment_fp);
  Expect(g_nonzero * 2 > g_trials, "most trials must find some duplicate");
  Expect(g_segment_fp > 100,
         "the wide trials must exercise segment-match false positives");
  std::printf("all dedup nest equivalence tests passed\n");
  return 0;
}
