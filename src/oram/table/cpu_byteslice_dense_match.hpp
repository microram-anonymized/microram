#pragma once

#include <cassert>
#include <cstring>

#include "src/core/mov_intrinsics.hpp"
#include "src/oram/table/cpu_byteslice_batch_layout.hpp"
#include "src/oram/table/cpu_byteslice_key_intersect.hpp"

// Dense direct-slot matching (table DESIGN.md, "Dense direct-slot
// matching").  For a public batch of up to 64 query keys scanned against a
// dense bucket, the bucket's 64 slots are viewed as an 8x8 grid; membership
// of each query in each eight-key row and column (VP2INTERSECT, or rotated
// exact compares for two-qword keys) identifies the query's unique live slot
// directly, instead of building a full 64-slot match mask per query.  Every bucket line is loaded whole at a public address; the
// recovered slot is secret and only indexes registers; the selected slot is
// verified against the complete key and occupancy.  Requires unique live keys
// within a bucket; the generic byte-sliced matcher is the duplicate-preserving
// fallback, and the only path on hosts without VP2INTERSECT.
namespace microram {
namespace byteslice {

#if MICRORAM_BYTESLICE_USE_VP2INTERSECT && \
    !(defined(__MINGW32__) && __GNUC__ <= 13)
inline constexpr bool kNativeDenseCrossMatch = true;
#else
inline constexpr bool kNativeDenseCrossMatch = false;
#endif

// Transient per-cascade scratch, not persistent bucket metadata. Original query
// keys are unchanged across the cascade, including dummy targets.
struct alignas(64) DenseMatchQueries {
  alignas(64) uint8_t packed[1024];
  alignas(64) uint8_t sliced[1024];
};

template<size_t FieldBytes, size_t Fields>
inline void PrepareDenseMatchQueries(const KeyWords* keys, size_t lanes,
                                     DenseMatchQueries& out) {
  assert(lanes <= 64);
  static_assert((FieldBytes == 4 && Fields == 1) ||
                (FieldBytes == 8 && (Fields == 1 || Fields == 2)),
                "one exact D/Q field or two exact Q fields");
  constexpr size_t group = 64 / FieldBytes;
  const size_t padded = (lanes + group - 1) / group * group;
  const __m512i low = _mm512_setr_epi64(0, 2, 4, 6, 8, 10, 12, 14);
  const __m512i high = _mm512_setr_epi64(1, 3, 5, 7, 9, 11, 13, 15);
  size_t j = 0;
  for (; j + 8 <= lanes; j += 8) {
    const __m512i a = _mm512_loadu_si512(keys + j);
    const __m512i b = _mm512_loadu_si512(keys + j + 4);
    const __m512i word = _mm512_permutex2var_epi64(a, low, b);
    if constexpr (FieldBytes == 8) {
      _mm512_store_si512(out.packed + j * 8, word);
      if constexpr (Fields == 2)
        _mm512_store_si512(out.packed + 512 + j * 8,
                           _mm512_permutex2var_epi64(a, high, b));
    } else {
      _mm256_storeu_si256(reinterpret_cast<__m256i*>(out.packed + j * 4),
                          _mm512_cvtepi64_epi32(word));
    }
  }
  // Public tail; never load past the caller's key array.
  for (size_t f = 0; f < Fields; ++f) {
    for (size_t tail = j; tail < padded; ++tail) {
      const uint64_t word = tail < lanes ? (f == 0 ? keys[tail].w0 : keys[tail].w1) : 0;
      if constexpr (FieldBytes == 8) {
        std::memcpy(out.packed + (f * 64 + tail) * 8, &word, 8);
      } else {
        const uint32_t dword = uint32_t(word);
        std::memcpy(out.packed + tail * 4, &dword, 4);
      }
    }
  }
  if constexpr (Fields > 1) {
    // Packed qwords -> byte lines: transpose each 8x8 byte block, then the
    // eight qword blocks. Reuse the packing rather than shifting 1024 bytes.
    const __m512i index = Transpose8x8Index();
    for (size_t f = 0; f < 2; ++f) {
      __m512i blocks[8], lines[8];
      for (size_t g = 0; g < 8; ++g) {
        const __m512i packed = g * 8 < padded
            ? core::obliLoad512(out.packed + f * 512 + g * 64)
            : _mm512_setzero_si512();
        blocks[g] = _mm512_permutexvar_epi8(index, packed);
      }
      TransposeQwords8x8(blocks, lines);
      for (size_t b = 0; b < 8; ++b)
        _mm512_store_si512(out.sliced + (f * 8 + b) * 64, lines[b]);
    }
  }
}

// Slots points to 64 allocated, 64-byte-aligned bytes; only the public lane
// prefix is returned. Queries and slots must not alias the bucket.
// Full-key verification is fixed-address: secret slots only index registers.
inline uint64_t VerifyDenseMatchSlots(const uint8_t* bucket,
                                      const DenseMatchQueries& query,
                                      const uint8_t* slots, uint64_t live,
                                      uint64_t hit) {
  const __m512i index = core::obliLoad512(slots);
  __m512i diff = _mm512_setzero_si512();
  for (size_t b = 0; b < 16; ++b) {
    const __m512i value = _mm512_permutexvar_epi8(index, core::obliLoad512(bucket + b * 64));
    diff = _mm512_ternarylogic_epi64(diff, value,
                                    core::obliLoad512(query.sliced + b * 64), 0xF6);
  }
  const __m512i occupied = _mm512_permutexvar_epi8(index, _mm512_movm_epi8(_cvtu64_mask64(live)));
  return hit & core::obliTestNMask8(diff, diff) &
         _cvtmask64_u64(_mm512_movepi8_mask(occupied));
}

// Exact membership in eight complete 128-bit keys. Both halves rotate together
// so a low-half match cannot borrow a high half from a different partner.
INLINE unsigned IntersectWideDenseSubset(__m512i lo, __m512i hi,
                                         __m512i query_lo, __m512i query_hi) {
  __m512i acc = _mm512_set1_epi64(-1);
  for (int r = 0; r < 8; ++r) {
    const __m512i diff = _mm512_or_si512(_mm512_xor_si512(lo, query_lo),
                                        _mm512_xor_si512(hi, query_hi));
    acc = _mm512_min_epu64(acc, diff);
    lo = _mm512_alignr_epi64(lo, lo, 1);
    hi = _mm512_alignr_epi64(hi, hi, 1);
  }
  return static_cast<unsigned>(core::obliTestNMask64(acc, acc));
}

// Requires unique LIVE full keys in each bucket. Every row/column membership
// uses complete-key equality, including for two-qword stored keys, except
// under kWideKeySegmentMatch, where the two qwords match independently.
// Every bucket/field/subset/query-group is processed regardless of secret data.
template<size_t FieldBytes, size_t Fields>
inline uint64_t MatchUniqueDenseSlots(const uint8_t* bucket, uint64_t live,
                                      const DenseMatchQueries& queries,
                                      size_t lanes, uint8_t* slots) {
  assert(lanes <= 64);
  static_assert((FieldBytes == 4 && Fields == 1) ||
                (FieldBytes == 8 && (Fields == 1 || Fields == 2)),
                "one exact D/Q field or two exact Q fields");
  __m512i subset[Fields][16];
  uint64_t zero[Fields];
  for (size_t f = 0; f < Fields; ++f) {
    __m512i lines[FieldBytes];
    zero[f] = LoadKeyLinesZeroingDummies(bucket + f * FieldBytes * 64,
                                        FieldBytes, live, FieldBytes, lines);
    if constexpr (FieldBytes == 8) {
      TransposeKeyLinesToQwords(lines, subset[f]);
      TransposeQwords8x8(subset[f], subset[f] + 8);
    } else {
      __m512i packed[4];
      TransposeKeyLinesToDwords(lines, packed);
      for (int r = 0; r < 8; ++r) {
        const __m512i idx = _mm512_add_epi32(_mm512_set1_epi32((r % 2) * 8),
            _mm512_setr_epi32(0,1,2,3,4,5,6,7,0,1,2,3,4,5,6,7));
        subset[f][r] = _mm512_permutexvar_epi32(idx, packed[r / 2]);
      }
      for (int c = 0; c < 8; ++c) {
        const __m512i idx = _mm512_add_epi32(_mm512_set1_epi32(c),
            _mm512_setr_epi32(0,8,16,24,0,8,16,24,0,8,16,24,0,8,16,24));
        const __m512i a = _mm512_permutex2var_epi32(packed[0], idx, packed[1]);
        const __m512i b = _mm512_permutex2var_epi32(packed[2], idx, packed[3]);
        subset[f][8 + c] = _mm512_mask_mov_epi32(a, 0xf0f0, b);
      }
    }
  }
  constexpr size_t group = 64 / FieldBytes;
  uint64_t hits = 0;
  _mm512_storeu_si512(slots, _mm512_setzero_si512());
  for (size_t base = 0; base < lanes; base += group) {
    __m512i query[Fields];
    unsigned query_zero[Fields];
    for (size_t f = 0; f < Fields; ++f) {
      query[f] = core::obliLoad512(queries.packed + (f * 64 + base) * FieldBytes);
      query_zero[f] = static_cast<unsigned>(FieldBytes == 8
          ? core::obliTestNMask64(query[f], query[f])
          : core::obliTestNMask32(query[f], query[f]));
    }
    __m512i row = _mm512_setzero_si512(), col = row;
    unsigned found = 0;
    for (size_t s = 0; s < 8; ++s) {
      unsigned rows = 0xffff, cols = 0xffff;
      if constexpr (Fields == 2 && kWideKeySegmentMatch) {
        // Per-qword membership ANDed: the halves may match different
        // partners, so a false candidate can displace a true hit.  The final
        // 128-bit verification still rejects a wrong slot (no false
        // acceptance), but a displaced hit is a lookup false negative.  Width
        // 16 holds only secret-keyed stored hashes, so such a mixed-partner
        // match is a negligible-probability bad event; it is charged in the
        // certified failure and observation bounds
        // (analysis/bound_certification/ERROR_ACCOUNTING.md, "Segment
        // configuration").
        for (size_t f = 0; f < Fields; ++f) {
          unsigned rm = IntersectSecondMaskQ(subset[f][s], query[f]);
          unsigned cm = IntersectSecondMaskQ(subset[f][8 + s], query[f]);
          // Dummy zero repair is PER FIELD AND SUBSET, before ANDing fields.
          rm = (rm & ~query_zero[f]) | (query_zero[f] &
              (0u - unsigned(((zero[f] >> (s * 8)) & 255) != 0)));
          cm = (cm & ~query_zero[f]) | (query_zero[f] &
              (0u - unsigned((zero[f] & (0x0101010101010101ULL << s)) != 0)));
          rows &= rm;
          cols &= cm;
        }
      } else if constexpr (Fields == 2) {
        rows = IntersectWideDenseSubset(subset[0][s], subset[1][s],
                                         query[0], query[1]);
        cols = IntersectWideDenseSubset(subset[0][8 + s], subset[1][8 + s],
                                         query[0], query[1]);
        // Dummy zeroing can invent only a COMPLETE zero key. Its repair
        // must use both zero masks from the same source/query slots.
        const uint64_t full_zero = zero[0] & zero[1];
        const unsigned qz = query_zero[0] & query_zero[1];
        rows = (rows & ~qz) | (qz &
            (0u - unsigned(((full_zero >> (s * 8)) & 255) != 0)));
        cols = (cols & ~qz) | (qz &
            (0u - unsigned((full_zero & (0x0101010101010101ULL << s)) != 0)));
      } else {
        if constexpr (FieldBytes == 8) {
          rows = IntersectSecondMaskQ(subset[0][s], query[0]);
          cols = IntersectSecondMaskQ(subset[0][8 + s], query[0]);
        } else {
          rows = IntersectSecondMaskD(subset[0][s], query[0]);
          cols = IntersectSecondMaskD(subset[0][8 + s], query[0]);
        }
      }
      // `rows`/`cols` are secret: the register-only moves, because with the
      // intrinsic GCC broadcast the constant from memory under them.
      if constexpr (FieldBytes == 8) {
        row = core::obliMaskMov64(row, rows, _mm512_set1_epi64(s * 8));
        col = core::obliMaskMov64(col, cols, _mm512_set1_epi64(s));
      } else {
        row = core::obliMaskMov32(row, rows, _mm512_set1_epi32(s * 8));
        col = core::obliMaskMov32(col, cols, _mm512_set1_epi32(s));
      }
      found |= rows;
    }
    __m512i slot = _mm512_or_si512(row, col);
    if constexpr (Fields == 1) {
      const unsigned qz = query_zero[0];
      const unsigned zs = unsigned(_tzcnt_u64(zero[0]) & 63);
      if constexpr (FieldBytes == 8)
        slot = core::obliMaskMov64(slot, qz, _mm512_set1_epi64(zs));
      else slot = core::obliMaskMov32(slot, qz, _mm512_set1_epi32(zs));
      found = (found & ~qz) | (qz & (0u - unsigned(zero[0] != 0)));
    }
    if constexpr (FieldBytes == 8)
      _mm_storel_epi64(reinterpret_cast<__m128i*>(slots + base), _mm512_cvtepi64_epi8(slot));
    else
      _mm_storeu_si128(reinterpret_cast<__m128i*>(slots + base), _mm512_cvtepi32_epi8(slot));
    hits |= uint64_t(found) << base;
  }
  hits &= LowMask64(unsigned(lanes));
  if constexpr (Fields > 1) hits = VerifyDenseMatchSlots(bucket, queries, slots, live, hits);
  return hits;
}

}  // namespace byteslice
}  // namespace microram
