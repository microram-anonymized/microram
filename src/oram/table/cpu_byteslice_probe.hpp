#pragma once

// Oblivious single-key lookup on a byte-sliced bucket.
//
// A probe compares one key against all 64 slots at once: each key byte line is
// one VPCMPB against a broadcast of that byte of the query, and the AND of
// those masks with the occupancy mask is the hit set.  Extracting the value is
// one VPCOMPRESSB per value line.  Work and memory traffic are identical
// whether the key is present or not, which is the whole point -- a hit and a
// miss have to be indistinguishable from outside.
//
// Batch deduplication, address preparation and forwarding live in
// cpu_byteslice_batch_probe.hpp; the arena cascade shares the match/extract
// primitives below rather than maintaining a separate fixed-size probe.
//
#include <immintrin.h>

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstring>

#include "src/core/mov_intrinsics.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/table/cpu_byteslice_tags.hpp"

namespace microram {
namespace byteslice {

// Exact, duplicate-preserving match over every key byte line. Occupancy and
// per-byte equality intersect only in registers: the register-only compare
// keeps the preceding match from becoming a write mask over a line's load.
// The two loops cover the stored key's low and high words; their lengths are
// public. Value and tag lines are not read here.
inline uint64_t MatchMaskByteSliced(const uint8_t* bucket, uint64_t real_mask,
                                    const Layout& layout, KeyWords key) {
  uint64_t match = real_mask;
  const size_t low_lines = layout.key_bytes < 8 ? layout.key_bytes : 8;
  for (size_t kb = 0; kb < low_lines; ++kb) {
    const __m512i line = _mm512_load_si512(bucket + kb * kBucketCapacity);
    const __m512i probe =
        _mm512_set1_epi8(static_cast<char>(key.w0 >> (8 * kb)));
    match &= core::obliCmpEqMask8(line, probe);
  }
  for (size_t kb = 8; kb < layout.key_bytes; ++kb) {
    const __m512i line = _mm512_load_si512(bucket + kb * kBucketCapacity);
    const __m512i probe =
        _mm512_set1_epi8(static_cast<char>(key.w1 >> (8 * (kb - 8))));
    match &= core::obliCmpEqMask8(line, probe);
  }
  return match;
}
// Finish a probe after its key-line match has been computed.  With
// PrefetchNext=true, all key_bytes + value_bytes lines of the next public
// bucket are prefetched while the current value lines are loaded and
// compressed.
//
// The prefetches go out in line order, key lines first.  In a dependent
// cascade only the next bucket's key lines (plus its mask word, which the
// caller prefetches) gate the match that picks the bucket after it; the value
// lines only feed the output blend, so requesting them first delays the
// critical half for nothing.
template <bool PrefetchNext>
inline void ExtractValueAndClearRealMaskByteSliced(
    uint8_t* bucket, uint64_t* real_mask, const Layout& layout,
    uint64_t match, uint8_t* value_out,
    const uint8_t* next_bucket = nullptr) {
  const __mmask64 match_mask = _cvtu64_mask64(match);
  const uint8_t* value_lines = bucket + layout.key_bytes * kBucketCapacity;
  if constexpr (PrefetchNext) {
    for (size_t kb = 0; kb < layout.key_bytes; ++kb) {
      _mm_prefetch(
          reinterpret_cast<const char*>(next_bucket + kb * kBucketCapacity),
          _MM_HINT_T0);
    }
  }
  for (size_t vb = 0; vb < layout.value_bytes; ++vb) {
    if constexpr (PrefetchNext) {
      _mm_prefetch(reinterpret_cast<const char*>(
                       next_bucket + (layout.key_bytes + vb) * kBucketCapacity),
                   _MM_HINT_T0);
    }
    const __m512i line = _mm512_load_si512(
        reinterpret_cast<const void*>(value_lines + vb * kBucketCapacity));
    const __m512i packed = _mm512_maskz_compress_epi8(match_mask, line);
    value_out[vb] = static_cast<uint8_t>(
        _mm_cvtsi128_si32(_mm512_castsi512_si128(packed)));
  }
  *real_mask &= ~match;
}

// ---------------------------------------------------------------------------
// The cascade forms of the two kernels above.
// ---------------------------------------------------------------------------
//
// Both read exactly the lines their plain counterparts read and produce the
// same hit set; what changes is the instruction stream.  They exist because a
// dependent cascade pays the match's LATENCY (it is the load-to-load round
// trip) and the extract's THROUGHPUT (it hides the next bucket's prefetches),
// and the plain kernels are poor at both in ways an objdump makes obvious:
//
//   - `match &= cmp` compiles to eight VPCMPEQB each masked by the previous
//     result, headed by the occupancy word's load: eight compare latencies in
//     series before the hit set exists.
//   - one VPCOMPRESSB per value line is a multi-cycle instruction on current
//     cores (the instruction, not the loads), and the byte store through
//     `uint8_t*` forces the layout fields to be reloaded every iteration.
//
// The cascade forms shorten the dependent match (a compare tree off the mask
// chain) and cut the extract to two vector uops per line; the trace is
// unchanged.

// Byte-wise `line ^ broadcast(key byte)` over eight consecutive key lines,
// OR-ed in a VPTERNLOG tree: a zero byte is a slot whose eight key bytes all
// matched.  Depth one XOR plus two ternlogs, all eight loads independent.
//
// INLINE (always_inline), not merely inline: GCC left this out of line when
// the 8- and 16-byte branches both called it, and a call on the cascade path
// costs a vzeroupper plus a k-mask and a zmm spill around it under the Win64
// ABI.
INLINE __m512i XorOrTree8(const uint8_t* lines, uint64_t word) {
  __m512i x[8];
  for (int i = 0; i < 8; ++i) {
    const __m512i line = _mm512_load_si512(
        reinterpret_cast<const void*>(lines + i * kBucketCapacity));
    const __m512i probe = _mm512_set1_epi8(static_cast<char>(word >> (8 * i)));
    x[i] = _mm512_xor_si512(line, probe);
  }
  const __m512i t0 = _mm512_ternarylogic_epi64(x[0], x[1], x[2], 0xFE);
  const __m512i t1 = _mm512_ternarylogic_epi64(x[3], x[4], x[5], 0xFE);
  const __m512i t2 = _mm512_ternarylogic_epi64(x[6], x[7], t0, 0xFE);
  return _mm512_or_si512(t1, t2);
}

// MatchMaskByteSliced with the compares kept out of the mask-dependency
// chain: the XOR/OR tree above, then ONE VPTESTNMB ANDed with the occupancy
// mask.
// The occupancy word joins at the tail, so its (separately prefetched) load
// does not head the chain. Four-byte keys use the shorter tree below;
// widths other than 4, 8 and 16 take the plain kernel (a public shape).
INLINE uint64_t MatchMaskByteSlicedTree(const uint8_t* bucket,
                                        uint64_t real_mask,
                                        const Layout& layout, KeyWords key) {
  const size_t key_bytes = layout.key_bytes;
  if (key_bytes == 4) {
    __m512i x[4];
    for (size_t i = 0; i < 4; ++i) {
      x[i] = _mm512_xor_si512(_mm512_load_si512(bucket + i * kBucketCapacity),
          _mm512_set1_epi8(static_cast<char>(key.w0 >> (8 * i))));
    }
    const __m512i o = _mm512_or_si512(x[3],
        _mm512_ternarylogic_epi64(x[0], x[1], x[2], 0xFE));
    return real_mask & core::obliTestNMask8(o, o);
  }
  if (key_bytes != 8 && key_bytes != 16) {
    return MatchMaskByteSliced(bucket, real_mask, layout, key);
  }
  __m512i o = XorOrTree8(bucket, key.w0);
  if (key_bytes == 16) {
    o = _mm512_or_si512(o, XorOrTree8(bucket + 8 * kBucketCapacity, key.w1));
  }
  return real_mask & core::obliTestNMask8(o, o);
}

// ExtractValueAndClearRealMaskByteSliced with VPERMT2B in place of
// VPCOMPRESSB: the matched slot index `s = tzcnt(match)` (a secret used only
// as a register permute index) selects byte s of TWO value lines per permute
// -- index vector [s, 64+s, s, 64+s, ...] puts line 2m's byte at output byte
// 2m and line 2m+1's at 2m+1 under a per-pair zero mask -- and four pairs are
// OR-ed into one qword store.  Two vector uops per line instead of a compress,
// a GPR move and a byte store, and no reload of the layout per line.
//
// DIFFERENT CONTRACT, and the reason this is a separate kernel: on a MISS
// (match == 0) `value_out` receives unspecified bytes, not zeros -- tzcnt
// yields 64 and the permute reads byte 0 of some line.  Every caller must
// blend under its own take gate, which the cascades already do
// (obliAssignBytes under `take`, TakeTombstoneFlags under `take`).  The plain
// kernel keeps its zero-on-miss contract for the callers that rely on it.
//
// Writes exactly value_bytes bytes: qwords for whole groups of eight lines,
// a 16-bit store per remaining pair, one byte for an odd tail.  With
// PrefetchNext, the next bucket's key lines go out first and its value lines
// one per line consumed, as in the plain kernel.
// INLINE (always_inline), not merely inline, for the reason XorOrTree8 above
// records: with plain `inline` GCC may leave it out of line at some call
// sites, and a call on a probe path costs a vzeroupper and spills the zmm and
// k registers the Win64 ABI clobbers across it.
template <bool PrefetchNext>
INLINE void ExtractValueAndClearRealMaskByteSlicedPermute(
    uint8_t* bucket, uint64_t* real_mask, const Layout& layout,
    uint64_t match, uint8_t* value_out,
    const uint8_t* next_bucket = nullptr) {
  // Locals on purpose: a store through `uint8_t*` may alias any object, so a
  // loop that reads `layout.value_bytes` reloads it after every byte stored.
  const size_t key_bytes = layout.key_bytes;
  const size_t value_bytes = layout.value_bytes;
  const unsigned slot = static_cast<unsigned>(_tzcnt_u64(match));
  const __m512i idx = _mm512_add_epi8(_mm512_set1_epi16(0x4000),
                                      _mm512_set1_epi8(static_cast<char>(slot)));
  const uint8_t* value_lines = bucket + key_bytes * kBucketCapacity;
  const uint8_t* next_value_lines =
      PrefetchNext ? next_bucket + key_bytes * kBucketCapacity : nullptr;
  if constexpr (PrefetchNext) {
    for (size_t kb = 0; kb < key_bytes; ++kb) {
      _mm_prefetch(
          reinterpret_cast<const char*>(next_bucket + kb * kBucketCapacity),
          _MM_HINT_T0);
    }
  }
  size_t vb = 0;
  for (; vb + 8 <= value_bytes; vb += 8) {
    const uint8_t* g = value_lines + vb * kBucketCapacity;
    if constexpr (PrefetchNext) {
      const uint8_t* ng = next_value_lines + vb * kBucketCapacity;
      for (int i = 0; i < 8; ++i) {
        _mm_prefetch(reinterpret_cast<const char*>(ng + i * kBucketCapacity),
                     _MM_HINT_T0);
      }
    }
    const __m512i l0 = _mm512_load_si512(reinterpret_cast<const void*>(g));
    const __m512i l1 = _mm512_load_si512(
        reinterpret_cast<const void*>(g + 1 * kBucketCapacity));
    const __m512i l2 = _mm512_load_si512(
        reinterpret_cast<const void*>(g + 2 * kBucketCapacity));
    const __m512i l3 = _mm512_load_si512(
        reinterpret_cast<const void*>(g + 3 * kBucketCapacity));
    const __m512i l4 = _mm512_load_si512(
        reinterpret_cast<const void*>(g + 4 * kBucketCapacity));
    const __m512i l5 = _mm512_load_si512(
        reinterpret_cast<const void*>(g + 5 * kBucketCapacity));
    const __m512i l6 = _mm512_load_si512(
        reinterpret_cast<const void*>(g + 6 * kBucketCapacity));
    const __m512i l7 = _mm512_load_si512(
        reinterpret_cast<const void*>(g + 7 * kBucketCapacity));
    const __m512i r0 = _mm512_maskz_permutex2var_epi8(0x03, l0, idx, l1);
    const __m512i r1 = _mm512_maskz_permutex2var_epi8(0x0C, l2, idx, l3);
    const __m512i r2 = _mm512_maskz_permutex2var_epi8(0x30, l4, idx, l5);
    const __m512i r3 = _mm512_maskz_permutex2var_epi8(0xC0, l6, idx, l7);
    const __m512i o =
        _mm512_or_si512(_mm512_ternarylogic_epi64(r0, r1, r2, 0xFE), r3);
    const uint64_t q = static_cast<uint64_t>(
        _mm_cvtsi128_si64(_mm512_castsi512_si128(o)));
    std::memcpy(value_out + vb, &q, 8);
  }
  for (; vb + 2 <= value_bytes; vb += 2) {
    if constexpr (PrefetchNext) {
      _mm_prefetch(reinterpret_cast<const char*>(next_value_lines +
                                                 vb * kBucketCapacity),
                   _MM_HINT_T0);
      _mm_prefetch(reinterpret_cast<const char*>(next_value_lines +
                                                 (vb + 1) * kBucketCapacity),
                   _MM_HINT_T0);
    }
    const __m512i l0 = _mm512_load_si512(
        reinterpret_cast<const void*>(value_lines + vb * kBucketCapacity));
    const __m512i l1 = _mm512_load_si512(reinterpret_cast<const void*>(
        value_lines + (vb + 1) * kBucketCapacity));
    const __m512i p = _mm512_permutex2var_epi8(l0, idx, l1);
    const uint32_t w = static_cast<uint32_t>(
        _mm_cvtsi128_si32(_mm512_castsi512_si128(p)));
    std::memcpy(value_out + vb, &w, 2);
  }
  if (vb < value_bytes) {
    if constexpr (PrefetchNext) {
      _mm_prefetch(reinterpret_cast<const char*>(next_value_lines +
                                                 vb * kBucketCapacity),
                   _MM_HINT_T0);
    }
    const __m512i line = _mm512_load_si512(
        reinterpret_cast<const void*>(value_lines + vb * kBucketCapacity));
    // idx byte 0 is `slot`, so the one-source permute reads the same byte.
    const __m512i p = _mm512_permutexvar_epi8(idx, line);
    value_out[vb] = static_cast<uint8_t>(
        _mm_cvtsi128_si32(_mm512_castsi512_si128(p)));
  }
  *real_mask &= ~match;
}

// ExtractValueAndClearRealMaskByteSlicedPermute with the value left in
// REGISTERS: value line j's byte `slot` lands in lane j % 64 of v[j / 64]
// instead of being stored to a scratch buffer, so a caller that blends
// several candidates (the joint cascade's main and tier) does it with
// register moves and reads and writes its output once.  Same lines read in
// the same order, same prefetches, same permutes; every write mask is a
// public constant.  value_bytes <= 128; lanes past value_bytes are zero.
// The miss contract is the permute kernel's: on match == 0 the lanes hold
// unspecified bytes, and the caller blends under its own gate.
template <bool PrefetchNext>
INLINE void ExtractValueToRegistersAndClearRealMaskByteSlicedPermute(
    const uint8_t* bucket, uint64_t* real_mask, const Layout& layout,
    uint64_t match, __m512i v[2], const uint8_t* next_bucket = nullptr) {
  const size_t key_bytes = layout.key_bytes;
  const size_t value_bytes = layout.value_bytes;
  assert(value_bytes <= 128);
  const unsigned slot = static_cast<unsigned>(_tzcnt_u64(match));
  const __m512i idx = _mm512_add_epi8(_mm512_set1_epi16(0x4000),
                                      _mm512_set1_epi8(static_cast<char>(slot)));
  const uint8_t* value_lines = bucket + key_bytes * kBucketCapacity;
  const uint8_t* next_value_lines =
      PrefetchNext ? next_bucket + key_bytes * kBucketCapacity : nullptr;
  if constexpr (PrefetchNext) {
    for (size_t kb = 0; kb < key_bytes; ++kb) {
      _mm_prefetch(
          reinterpret_cast<const char*>(next_bucket + kb * kBucketCapacity),
          _MM_HINT_T0);
    }
  }
  // Two named accumulators and a branch on the public line index, not an
  // array indexed by it: a runtime index would put the array on the stack.
  __m512i lo = _mm512_setzero_si512(), hi = _mm512_setzero_si512();
  size_t vb = 0;
  for (; vb + 8 <= value_bytes; vb += 8) {
    const uint8_t* g = value_lines + vb * kBucketCapacity;
    if constexpr (PrefetchNext) {
      const uint8_t* ng = next_value_lines + vb * kBucketCapacity;
      for (int i = 0; i < 8; ++i) {
        _mm_prefetch(reinterpret_cast<const char*>(ng + i * kBucketCapacity),
                     _MM_HINT_T0);
      }
    }
    __m512i l[8];
    for (int i = 0; i < 8; ++i) {
      l[i] = _mm512_load_si512(
          reinterpret_cast<const void*>(g + i * kBucketCapacity));
    }
    // A group of eight never straddles the two registers: vb % 8 == 0.
    const uint64_t pair = uint64_t{0x03} << (vb & 63);
    const __m512i r0 =
        _mm512_maskz_permutex2var_epi8(_cvtu64_mask64(pair), l[0], idx, l[1]);
    const __m512i r1 = _mm512_maskz_permutex2var_epi8(
        _cvtu64_mask64(pair << 2), l[2], idx, l[3]);
    const __m512i r2 = _mm512_maskz_permutex2var_epi8(
        _cvtu64_mask64(pair << 4), l[4], idx, l[5]);
    const __m512i r3 = _mm512_maskz_permutex2var_epi8(
        _cvtu64_mask64(pair << 6), l[6], idx, l[7]);
    const __m512i o =
        _mm512_or_si512(_mm512_ternarylogic_epi64(r0, r1, r2, 0xFE), r3);
    if (vb < 64) lo = _mm512_or_si512(lo, o); else hi = _mm512_or_si512(hi, o);
  }
  for (; vb + 2 <= value_bytes; vb += 2) {
    if constexpr (PrefetchNext) {
      _mm_prefetch(reinterpret_cast<const char*>(next_value_lines +
                                                 vb * kBucketCapacity),
                   _MM_HINT_T0);
      _mm_prefetch(reinterpret_cast<const char*>(next_value_lines +
                                                 (vb + 1) * kBucketCapacity),
                   _MM_HINT_T0);
    }
    const __m512i l0 = _mm512_load_si512(
        reinterpret_cast<const void*>(value_lines + vb * kBucketCapacity));
    const __m512i l1 = _mm512_load_si512(reinterpret_cast<const void*>(
        value_lines + (vb + 1) * kBucketCapacity));
    const __m512i p = _mm512_maskz_permutex2var_epi8(
        _cvtu64_mask64(uint64_t{0x03} << (vb & 63)), l0, idx, l1);
    if (vb < 64) lo = _mm512_or_si512(lo, p); else hi = _mm512_or_si512(hi, p);
  }
  if (vb < value_bytes) {
    if constexpr (PrefetchNext) {
      _mm_prefetch(reinterpret_cast<const char*>(next_value_lines +
                                                 vb * kBucketCapacity),
                   _MM_HINT_T0);
    }
    const __m512i line = _mm512_load_si512(
        reinterpret_cast<const void*>(value_lines + vb * kBucketCapacity));
    // Every idx byte names byte `slot` in a one-source permute.
    const __m512i p = _mm512_maskz_permutexvar_epi8(
        _cvtu64_mask64(uint64_t{1} << (vb & 63)), idx, line);
    if (vb < 64) lo = _mm512_or_si512(lo, p); else hi = _mm512_or_si512(hi, p);
  }
  v[0] = lo;
  v[1] = hi;
  *real_mask &= ~match;
}

}  // namespace byteslice
}  // namespace microram
