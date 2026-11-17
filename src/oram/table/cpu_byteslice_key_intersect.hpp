#pragma once

// Shared fixed-address packing and intersection primitives. No AVX512CD dependency.
// They compare the key lines of byte-sliced buckets as whole sets (which
// slots of one side hold a key present on the other side) for dense
// direct-slot matching and the rebuild's cross-bucket dedup.  Every
// load is a whole key line at a public address; secret occupancy only masks
// registers.
#include <immintrin.h>
#include <cstddef>
#include <cstdint>
#include "src/core/mov_intrinsics.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/table/cpu_byteslice_tags.hpp"

// AVX512_VP2INTERSECT: Tiger Lake (microcoded) and Zen 5 (native); not Zen 4
// or the Intel server parts.  GCC defines __AVX512VP2INTERSECT__ when
// -march=native finds it (or under -mavx512vp2intersect).  The emulations are
// correct on any AVX-512 host but slower; without VP2INTERSECT the rebuild's
// cross-bucket dedup costs several times more (cpu_byteslice_dedup_masks.hpp).
#ifndef MICRORAM_BYTESLICE_USE_VP2INTERSECT
#if defined(__AVX512VP2INTERSECT__)
#define MICRORAM_BYTESLICE_USE_VP2INTERSECT 1
#else
#define MICRORAM_BYTESLICE_USE_VP2INTERSECT 0
#endif
#endif

// 16-byte stored keys (user keys of 16 bytes or more, always AES outputs) on
// a VP2INTERSECT host: match four 32-bit segments with VP2INTERSECTD and AND the answers,
// instead of the exact same-partner comparison.  APPROXIMATE -- each segment
// may match a different partner -- so two different keys can be reported
// equal; with secret-hashed stored keys and at most 64 partners that is
// <= 64^4 / 2^128 = 2^-104 per compared slot.  The segment kernels are
// several times faster than the exact ones on a native-VP2INTERSECT host
// (cpu_byteslice_exact_dedup_benchmark compares the two).  CMake option
// CPU_BYTESLICE_ORAM_WIDE_KEY_VP2INTERSECT; no effect without VP2INTERSECT,
// where the exact path is also the faster one.
#ifndef MICRORAM_BYTESLICE_WIDE_KEY_VP2INTERSECT
#define MICRORAM_BYTESLICE_WIDE_KEY_VP2INTERSECT 1
#endif

namespace microram {
namespace byteslice {

inline constexpr bool kWideKeySegmentMatch =
    MICRORAM_BYTESLICE_USE_VP2INTERSECT && MICRORAM_BYTESLICE_WIDE_KEY_VP2INTERSECT;

// 32-bit twin of UnpackKeyLinesToQwords: the two unpack stages alone, which
// leave c[j] lane q holding entries 16q+4j..16q+4j+3 (dword 4q+t of c[j] is
// slot 16q+4j+t).  Enough for a side that is only read as a set, or whose
// answer is placed back in slot order by that map (AllPairsMatchMaskD).
INLINE void UnpackKeyLinesToDwords(const __m512i* l, __m512i* c) {
  // Stage 1: byte pairs (l0,l1) and (l2,l3); lane q covers entries 16q..16q+15,
  // lo taking its first 8 and hi its last 8.
  const __m512i b0 = _mm512_unpacklo_epi8(l[0], l[1]);
  const __m512i b1 = _mm512_unpackhi_epi8(l[0], l[1]);
  const __m512i b2 = _mm512_unpacklo_epi8(l[2], l[3]);
  const __m512i b3 = _mm512_unpackhi_epi8(l[2], l[3]);
  // Stage 2: whole 4-byte keys.
  c[0] = _mm512_unpacklo_epi16(b0, b2);
  c[1] = _mm512_unpackhi_epi16(b0, b2);
  c[2] = _mm512_unpacklo_epi16(b1, b3);
  c[3] = _mm512_unpackhi_epi16(b1, b3);
}

// 32-bit twin of TransposeKeyLinesToQwords: four key byte lines -> four
// registers of sixteen packed keys, keys_out[m] holding entries 16m..16m+15.
// Same lane-local unpack stages plus a 4x4 128-bit-lane transpose; only the
// element width changes.
INLINE void TransposeKeyLinesToDwords(const __m512i* l, __m512i* keys_out) {
  __m512i c[4];
  UnpackKeyLinesToDwords(l, c);
  // The unpacks are lane-local, so a 4x4 lane transpose puts entry 16m+i back
  // in keys_out[m] dword i.
  const __m512i e0 = _mm512_shuffle_i64x2(c[0], c[1], 0x88);
  const __m512i e1 = _mm512_shuffle_i64x2(c[0], c[1], 0xDD);
  const __m512i e2 = _mm512_shuffle_i64x2(c[2], c[3], 0x88);
  const __m512i e3 = _mm512_shuffle_i64x2(c[2], c[3], 0xDD);
  keys_out[0] = _mm512_shuffle_i64x2(e0, e2, 0x88);
  keys_out[2] = _mm512_shuffle_i64x2(e0, e2, 0xDD);
  keys_out[1] = _mm512_shuffle_i64x2(e1, e3, 0x88);
  keys_out[3] = _mm512_shuffle_i64x2(e1, e3, 0xDD);
}

// Loads `lanes` key byte lines of `bucket` with the key bytes of every DUMMY
// slot forced to zero, and returns the slot mask of the bucket's REAL entries
// whose key is exactly 0.
//
// Zeroing is what makes the intersection safe to run over all 64 lanes: a
// dummy slot holds stale bytes that may well be some older real key, and a
// match against one of those would silently drop a live entry.  It happens in
// registers, so the bucket is not written.  Zeroing collapses every dummy onto
// the single value 0, and the returned mask is what lets the caller repair
// that one value (see CrossBucketDuplicateMask).  Only the side an
// intersection reads as a SET needs it; the side whose answer is ANDed with
// its own real mask takes LoadKeyLinesKeepingDummies.
//
// "In registers" is load bearing and has to be enforced, not assumed: `real`
// is SECRET occupancy, and written as a plain load feeding the masked move GCC
// may fuse the two into one VMOVDQU8 zmm{k}{z}, [line] -- a load that fetches
// only the real slots' bytes, and with an empty source fetches nothing at
// all.  A pinned load is not enough either, since
// GCC may spill the pinned line and fold the reload into the move, so the
// move is core::obliMaskMov8, whose source is a register by constraint; the
// memory trace of this loader is the public (bucket, key_bytes) pair.
template <bool ZeroDummies>
INLINE uint64_t LoadKeyLinesMaskingZeros(const uint8_t* bucket,
                                         size_t key_bytes, uint64_t real,
                                         size_t lanes, __m512i* lines) {
  __m512i any = _mm512_setzero_si512();
  for (size_t i = 0; i < lanes; ++i) {
    if (i < key_bytes) {
      const __m512i line = _mm512_load_si512(
          reinterpret_cast<const void*>(bucket + i * kBucketCapacity));
      lines[i] = ZeroDummies
                     ? core::obliMaskMov8(_mm512_setzero_si512(), real, line)
                     : line;
      any = _mm512_or_si512(any, line);
    } else {
      lines[i] = _mm512_setzero_si512();
    }
  }
  // VPTESTNMB of the OR of the lines: the slots whose key bytes are all zero.
  // A dummy slot may pass, but `real` masks it out.
  return real & core::obliTestNMask8(any, any);
}

INLINE uint64_t LoadKeyLinesZeroingDummies(const uint8_t* bucket,
                                           size_t key_bytes, uint64_t real,
                                           size_t lanes, __m512i* lines) {
  return LoadKeyLinesMaskingZeros<true>(bucket, key_bytes, real, lanes, lines);
}

// The same lines and zero-key mask with dummy slots left as stored.
INLINE uint64_t LoadKeyLinesKeepingDummies(const uint8_t* bucket,
                                           size_t key_bytes, uint64_t real,
                                           size_t lanes, __m512i* lines) {
  return LoadKeyLinesMaskingZeros<false>(bucket, key_bytes, real, lanes, lines);
}

#if MICRORAM_BYTESLICE_USE_VP2INTERSECT
inline __mmask8 IntersectSecondMaskQ(__m512i a, __m512i b) {
  __mmask8 k1, k2;
  _mm512_2intersect_epi64(a, b, &k1, &k2);
  (void)k1;  // the a-side mask is not needed: duplicates are dropped from b
  return k2;
}

inline __mmask16 IntersectSecondMaskD(__m512i a, __m512i b) {
  __mmask16 k1, k2;
  _mm512_2intersect_epi32(a, b, &k1, &k2);
  (void)k1;
  return k2;
}
#else
// Single-pair emulation, for the callers that do not sweep a whole 8x8 nest
// (the self-dedup in cpu_byteslice_dedup_masks.hpp).  AllPairsMatchMask* has
// its own fallback, which hoists the rotations out of the inner loop and
// accumulates in vector registers instead.
inline __mmask8 IntersectSecondMaskQ(__m512i a, __m512i b) {
  uint64_t acc = 0;
  const __m512i rot = _mm512_setr_epi64(1, 2, 3, 4, 5, 6, 7, 0);
  for (int r = 0; r < 8; ++r) {
    acc |= core::obliCmpEqMask64(a, b);
    a = _mm512_permutexvar_epi64(rot, a);
  }
  return static_cast<__mmask8>(acc);
}

inline __mmask16 IntersectSecondMaskD(__m512i a, __m512i b) {
  uint64_t acc = 0;
  const __m512i rot =
      _mm512_setr_epi32(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0);
  for (int r = 0; r < 16; ++r) {
    acc |= core::obliCmpEqMask32(a, b);
    a = _mm512_permutexvar_epi32(rot, a);
  }
  return static_cast<__mmask16>(acc);
}
#endif

}  // namespace byteslice
}  // namespace microram
