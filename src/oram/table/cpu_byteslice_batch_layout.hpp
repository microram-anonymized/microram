#pragma once

// The batch result layouts' shared kernels (table DESIGN.md, "Share
// extraction and dense scans across lanes").
//
// A chunk's dense results are accumulated SLICED -- one 64-byte line per
// value byte, lane j at column j -- because a dense bucket is extracted for
// all lanes at once (ExtractDenseWave).  Under the default layout
// (kSlicedPlaceAtLane) the hashed extract also places each lane's byte at its
// own column, so nothing has to be reconciled at all.  Under kRows, the
// reference layout, a hashed result is a contiguous ROW per lane and
// MergeSlicedIntoRowsScalar folds the dense accumulator into those rows.
//
// TRACE.  Every load and store below is a whole 64-byte line at an address
// that depends only on public quantities: the lane range, the value width,
// the row stride.  The secret per-lane "which layout holds lane j's answer"
// bits are folded into k-registers that drive VPBLENDMB on registers; loads
// are pinned (core::obliLoad512) and blend results pinned before the store so
// the compiler cannot fuse either into a masked memory operation.  A public
// lane mask, such as the active lane range, may drive a masked store.

#include <immintrin.h>

#include <cassert>
#include <cstddef>
#include <cstdint>

#include "src/core/mov_intrinsics.hpp"
#include "src/oram/table/cpu_byteslice_batch_config.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/table/cpu_byteslice_tags.hpp"

namespace microram {
namespace byteslice {

// 8x8 qword transpose across eight registers: c[g].q[v] = r[v].q[g].
// Three stages of two-source shuffles, 24 instructions, nothing in memory.
INLINE void TransposeQwords8x8(const __m512i* r, __m512i* c) {
  const __m512i t0 = _mm512_unpacklo_epi64(r[0], r[1]);
  const __m512i t1 = _mm512_unpackhi_epi64(r[0], r[1]);
  const __m512i t2 = _mm512_unpacklo_epi64(r[2], r[3]);
  const __m512i t3 = _mm512_unpackhi_epi64(r[2], r[3]);
  const __m512i t4 = _mm512_unpacklo_epi64(r[4], r[5]);
  const __m512i t5 = _mm512_unpackhi_epi64(r[4], r[5]);
  const __m512i t6 = _mm512_unpacklo_epi64(r[6], r[7]);
  const __m512i t7 = _mm512_unpackhi_epi64(r[6], r[7]);
  // 128-bit lane i of t0 holds [r0.q(2i), r1.q(2i)]; pair the (r0,r1) and
  // (r2,r3) halves so a lane holds four consecutive rows of one column pair.
  const __m512i s0 = _mm512_shuffle_i64x2(t0, t2, 0x88);  // cols 0,4
  const __m512i s1 = _mm512_shuffle_i64x2(t0, t2, 0xDD);  // cols 2,6
  const __m512i s2 = _mm512_shuffle_i64x2(t1, t3, 0x88);  // cols 1,5
  const __m512i s3 = _mm512_shuffle_i64x2(t1, t3, 0xDD);  // cols 3,7
  const __m512i s4 = _mm512_shuffle_i64x2(t4, t6, 0x88);
  const __m512i s5 = _mm512_shuffle_i64x2(t4, t6, 0xDD);
  const __m512i s6 = _mm512_shuffle_i64x2(t5, t7, 0x88);
  const __m512i s7 = _mm512_shuffle_i64x2(t5, t7, 0xDD);
  c[0] = _mm512_shuffle_i64x2(s0, s4, 0x88);
  c[4] = _mm512_shuffle_i64x2(s0, s4, 0xDD);
  c[2] = _mm512_shuffle_i64x2(s1, s5, 0x88);
  c[6] = _mm512_shuffle_i64x2(s1, s5, 0xDD);
  c[1] = _mm512_shuffle_i64x2(s2, s6, 0x88);
  c[5] = _mm512_shuffle_i64x2(s2, s6, 0xDD);
  c[3] = _mm512_shuffle_i64x2(s3, s7, 0x88);
  c[7] = _mm512_shuffle_i64x2(s3, s7, 0xDD);
}

// The kRows reference merge, also the test oracle for the sliced path:
// rows[j][v] = dense[j] ? sliced[v][j] : rows[j][v]
// for lanes [lo, hi) and every value line, one byte CMOV each.
inline void MergeSlicedIntoRowsScalar(const uint8_t* sliced, size_t value_lines,
                                      const uint64_t* dense_taken, size_t lo,
                                      size_t hi, uint8_t* rows,
                                      size_t row_stride) {
  for (size_t j = lo; j < hi; ++j) {
    uint8_t* const row = rows + j * row_stride;
    const bool dense = dense_taken[j] != 0;
    for (size_t v = 0; v < value_lines; ++v) {
      row[v] = static_cast<uint8_t>(core::obliSelectU64(
          row[v], sliced[v * kMaxBatchLanes + j], dense));
    }
  }
}

// Zeroes value_lines sliced lines.  Public shape; whole-line stores.
inline void ClearSliced(uint8_t* sliced, size_t value_lines) {
  const __m512i z = _mm512_setzero_si512();
  for (size_t v = 0; v < value_lines; ++v) {
    _mm512_store_si512(reinterpret_cast<void*>(sliced + v * kMaxBatchLanes), z);
  }
}


// Writes a 64-byte line whose byte j is (flags[j] & 1) for j in [0, lanes)
// and 0 past it: the batch's found flags as the sliced found line a
// parallel probe bank publishes.  `lanes` is public.
inline void StoreFlagLine(const uint64_t* flags, size_t lanes, uint8_t* line) {
  alignas(64) uint8_t bytes[kMaxBatchLanes] = {};
  for (size_t j = 0; j < lanes; ++j) bytes[j] = static_cast<uint8_t>(flags[j] & 1u);
  _mm512_store_si512(reinterpret_cast<void*>(line),
                     _mm512_load_si512(reinterpret_cast<const void*>(bytes)));
}

// ---------------------------------------------------------------------------
// Hashed extraction straight into the sliced accumulator ("place at lane")
// ---------------------------------------------------------------------------
//
// The alternative to extracting rows and transposing them once: for a group
// of eight lanes, one VPERMT2B per PAIR of lanes puts lane j0's matched byte
// of value line v at byte j0 and lane j1's at byte j1 (the index vector's
// byte j0 is slot_j0, byte j1 is 64 + slot_j1, the two-source select), the
// four pair results are OR-ed (they are zero elsewhere) and the group's
// eight bytes are blended into the accumulator line under the lanes' take
// bits.  Per line: eight loads, four permutes, two logic ops and one
// accumulator read-modify-write, against the row extractor's half a permute
// per line plus one final transpose per chunk.  Avoiding the transpose and
// the per-lane rows is the cheaper of the two in practice.
//
// `buckets[j]`, `matches[j]` and `takes[j]` are the lane arrays for lanes
// [lo, hi); entries outside the range may belong to another helper and are
// never read: a pair whose second (or both) lane falls past `hi` aliases the
// group's first lane for its loads, a public choice, and the blend mask
// excludes it.  `slots` is the split piece width (kSplit) or ignored; the
// value lines of lane j start `key_bytes` lines into its bucket at that
// stride, as in the permute extractors.
template <bool kSplit>
INLINE void ExtractHashedWaveIntoSliced(const uint8_t* const* buckets,
                                        const uint64_t* matches,
                                        const uint64_t* takes, size_t lo,
                                        size_t hi, size_t key_bytes,
                                        size_t value_lines, unsigned slots,
                                        uint8_t* sliced) {
  const size_t stride = kSplit ? slots : kBucketCapacity;
  const __mmask64 lane_bits = _cvtu64_mask64(
      kSplit ? LowMask64(slots) : ~uint64_t{0});
  for (size_t g = lo; g < hi; g += 8) {
    __m512i idx[4];
    __mmask64 pair_mask[4];
    const uint8_t* a[4];
    const uint8_t* b[4];
    uint64_t take_bits = 0;
    for (size_t p = 0; p < 4; ++p) {
      const size_t j0 = g + 2 * p, j1 = j0 + 1;
      const bool in0 = j0 < hi, in1 = j1 < hi;  // public
      const size_t l0 = in0 ? j0 : g, l1 = in1 ? j1 : g;
      const unsigned slot0 = static_cast<unsigned>(_tzcnt_u64(matches[l0]) & 63u);
      const unsigned slot1 = static_cast<unsigned>(_tzcnt_u64(matches[l1]) & 63u);
      // Secret slots in a register; public byte positions j0, j1.
      __m512i v = _mm512_mask_mov_epi8(
          _mm512_setzero_si512(), _cvtu64_mask64(uint64_t{1} << (j0 & 63)),
          _mm512_set1_epi8(static_cast<char>(slot0)));
      v = _mm512_mask_mov_epi8(
          v, _cvtu64_mask64(uint64_t{1} << (j1 & 63)),
          _mm512_set1_epi8(static_cast<char>(64 + slot1)));
      idx[p] = v;
      pair_mask[p] = _cvtu64_mask64(
          (static_cast<uint64_t>(in0) << (j0 & 63)) |
          (static_cast<uint64_t>(in1) << (j1 & 63)));
      a[p] = buckets[l0] + key_bytes * stride;
      b[p] = buckets[l1] + key_bytes * stride;
      take_bits |= (takes[l0] & static_cast<uint64_t>(in0)) << (j0 & 63);
      take_bits |= (takes[l1] & static_cast<uint64_t>(in1)) << (j1 & 63);
    }
    const __mmask64 take = _cvtu64_mask64(take_bits);
    for (size_t v = 0; v < value_lines; ++v) {
      __m512i r[4];
      for (size_t p = 0; p < 4; ++p) {
        // The piece-width load mask (kSplit) and the pair mask are public.
        // Both lines are pinned so the permute's second source is not folded
        // into a masked memory operand, which keeps the audit unambiguous:
        // every value line is read whole.
        __m512i la, lb;
        if constexpr (kSplit) {
          la = core::obliPin512(_mm512_maskz_loadu_epi8(lane_bits, a[p] + v * stride));
          lb = core::obliPin512(_mm512_maskz_loadu_epi8(lane_bits, b[p] + v * stride));
        } else {
          la = core::obliLoad512(a[p] + v * stride);
          lb = core::obliLoad512(b[p] + v * stride);
        }
        r[p] = _mm512_maskz_permutex2var_epi8(pair_mask[p], la, idx[p], lb);
      }
      const __m512i merged = _mm512_or_si512(
          _mm512_ternarylogic_epi64(r[0], r[1], r[2], 0xFE), r[3]);
      uint8_t* const acc = sliced + v * kMaxBatchLanes;
      const __m512i cur = core::obliLoad512(acc);
      _mm512_store_si512(reinterpret_cast<void*>(acc),
                         core::obliPin512(_mm512_mask_mov_epi8(cur, take, merged)));
    }
  }
}

}  // namespace byteslice
}  // namespace microram
