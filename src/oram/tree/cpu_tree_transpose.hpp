#pragma once

// The transposition between a path's stored buckets and the byte lines of
// the working set (src/oram/tree/DESIGN.md, "Storage formats"), and the
// loads and stores of a path's chunks.
//
// THE TILE.  One 64-byte chunk from each of 16 buckets -- register i is the
// bucket at path position i -- holds bytes 16t..16t+15 of the bucket's four
// slots, interleaved: position q = 4c + z is byte 16t + c of slot z.  The
// byte line for entry byte 16t + c is output register c, holding path lane
// 4i + z at position 4i + z.  So the transpose swaps the four bits of the
// register index with the four bits c = bits 2..5 of the position, and
// leaves position bits 0..1 (the slot) alone.  Had the four slots been
// stored one after the other this would be a 64x64 byte transpose in six
// stages; the interleaved storage IS its first two, done once at rest.
//
// THE NETWORK.  Four stages, stage k swapping register-index bit k with
// position bit k + 2:
//
//     X'[r][q] = X[ r with bit k := q_{k+2} ][ q with bit k+2 := r_k ]
//
// Each output register draws from the two inputs that differ in bit k, so a
// stage is one VPERMT2B per output register with a constant index vector
// (one per stage and per value of r_k -- eight in all).  Stages commute and
// each is an involution, so the same tables run the inverse transposition,
// byte lines back to interleaved chunks for the write-back.  Sixteen
// registers are the whole network, so a chunk never leaves the register
// file between the two directions.

#include <immintrin.h>

#include <cstddef>
#include <cstdint>
#include <type_traits>

#include "src/core/mov_intrinsics.hpp"
#include "src/oram/tree/cpu_tree_layout.hpp"

namespace microram {
namespace tree {

inline constexpr unsigned kTransposeStages = 4;

struct TransposeTables4 {
  __m512i idx[kTransposeStages][2];
};

inline TransposeTables4 MakeTransposeTables4() {
  TransposeTables4 t;
  constexpr unsigned kShift = 2;  // log2 of the bucket's slots
  alignas(64) uint8_t bytes[64];
  for (unsigned k = 0; k < kTransposeStages; ++k) {
    for (unsigned rk = 0; rk < 2; ++rk) {
      for (unsigned q = 0; q < 64; ++q) {
        // Source register: the one whose bit k equals this position's bit
        // k + 2 (bit 6 of a VPERMT2B index selects the second table).
        const unsigned from_second = (q >> (k + kShift)) & 1u;
        // Source position: this position with that bit replaced by r_k.
        const unsigned src = (q & ~(1u << (k + kShift))) | (rk << (k + kShift));
        bytes[q] = static_cast<uint8_t>((from_second << 6) | src);
      }
      t.idx[k][rk] = _mm512_load_si512(reinterpret_cast<const void*>(bytes));
    }
  }
  return t;
}

inline const TransposeTables4& DefaultTransposeTables4() {
  static const TransposeTables4 tables = MakeTransposeTables4();
  return tables;
}

// Stage k on the pair (a: r_k = 0, b: r_k = 1).
template <unsigned K>
INLINE void TransposeStagePair(const TransposeTables4& t, __m512i& a,
                               __m512i& b) {
  const __m512i a2 = _mm512_permutex2var_epi8(a, t.idx[K][0], b);
  const __m512i b2 = _mm512_permutex2var_epi8(a, t.idx[K][1], b);
  a = a2;
  b = b2;
}

// Stage k on a pair whose SECOND source is known to be all zeros: the same
// two permutes, with a zero register in place of a load.
template <unsigned K>
INLINE void TransposeStagePairZeroHigh(const TransposeTables4& t, __m512i a,
                                       __m512i* out_lo, __m512i* out_hi) {
  const __m512i z = _mm512_setzero_si512();
  *out_lo = _mm512_permutex2var_epi8(a, t.idx[K][0], z);
  *out_hi = _mm512_permutex2var_epi8(a, t.idx[K][1], z);
}

// ---------------------------------------------------------------------------
// The network pruned to the EXACT path length
// ---------------------------------------------------------------------------
//
// A path of P buckets fills only P of the 16 input registers, and the rest
// transpose zeros into lanes 4P..63 that every later kernel ignores.  The
// pruning is exact, not heuristic.  Going FORWARD, after stages 0..k the
// nonzero registers are exactly the prefix `[0, ceil(P / 2^(k+1)) 2^(k+1))`
// -- flipping bits 0..k of an index below P cannot reach past that bound,
// and reaches everything below it -- so stage k pairs `(i, i + 2^k)` with
// both inputs live compute two outputs, a pair whose partner is past the
// prefix computes both from one live input and a zero (the ZeroHigh form,
// same two shuffles, no load), and a pair wholly past it does not exist.
// Going BACKWARD only outputs `[0, P)` are stored, and inverse stage k needs
// its inputs on the same prefix, so a pair whose second output is past the
// prefix computes only its first: ONE shuffle.
//
// Shuffles per chunk, both directions, against the network rounded up to
// 8 or 16 registers:
//
//     P          8    9   10   11   12   13   14   15   16
//     rounded   72  128  128  128  128  128  128  128  128
//     exact     72  101  102  107  108  121  122  127  128
//
// (`ExactNetworkShuffles` is the formula; the test pins these values.)  The
// forward and inverse are templated on P and a runtime P is dispatched once
// per pass through `WithPathBuckets`, so the load and store loops unroll to
// exactly P as well.

inline constexpr unsigned kZ4Registers = 16;

// The registers that can be nonzero after forward stage k of a path of P
// buckets -- equivalently the inputs inverse stage k needs: the smallest
// multiple of 2^(k+1) at or above P, capped at the group.
inline constexpr unsigned ExactPrefix(unsigned P, unsigned k) {
  const unsigned w = 1u << (k + 1);
  const unsigned n = ((P + w - 1) / w) * w;
  return n < kZ4Registers ? n : kZ4Registers;
}

// Shuffles the exact network spends on a path of P buckets, both directions:
// forward stage k writes ExactPrefix(P, k) outputs; inverse stage k writes
// ExactPrefix(P, k - 1) outputs, and P itself at k = 0.
inline constexpr unsigned ExactNetworkShuffles(unsigned P) {
  unsigned s = P;
  for (unsigned k = 0; k < 4; ++k) s += ExactPrefix(P, k);
  for (unsigned k = 1; k < 4; ++k) s += ExactPrefix(P, k - 1);
  return s;
}

// Forward stage K on a group whose nonzero registers are `[0, Live)`.
// Writes `[0, ExactPrefix(Live, K))`; reads only `[0, Live)`.
template <unsigned K, unsigned Live>
INLINE void ForwardStageExact(const TransposeTables4& t, __m512i* r) {
  constexpr unsigned s = 1u << K;
  static_assert(Live >= 1 && Live <= kZ4Registers, "live prefix out of range");
  // Every pair base below Live is a live first input; a pair base at or
  // above Live would be a pair of zeros, and there is none below the next
  // prefix: for K >= 1 `Live` is a multiple of 2^K, so the registers between
  // it and the next prefix all have bit K set, i.e. they are second inputs.
  for (unsigned i = 0; i < Live; ++i) {
    if ((i & s) != 0) continue;
    if (i + s < Live) {
      TransposeStagePair<K>(t, r[i], r[i + s]);
    } else {
      TransposeStagePairZeroHigh<K>(t, r[i], &r[i], &r[i + s]);
    }
  }
}

// Inverse stage K producing outputs `[0, Need)`; reads `[0, ExactPrefix(Need, K))`.
template <unsigned K, unsigned Need>
INLINE void InverseStageExact(const TransposeTables4& t, __m512i* r) {
  constexpr unsigned s = 1u << K;
  static_assert(Need >= 1 && Need <= kZ4Registers, "needed prefix out of range");
  for (unsigned i = 0; i < Need; ++i) {
    if ((i & s) != 0) continue;
    if (i + s < Need) {
      TransposeStagePair<K>(t, r[i], r[i + s]);
    } else {
      // Only the first output of the pair is wanted: one shuffle.
      r[i] = _mm512_permutex2var_epi8(r[i], t.idx[K][0], r[i + s]);
    }
  }
}

// Interleaved chunks -> byte lines for a path of exactly P buckets.  Reads
// registers `[0, P)` ONLY -- the rest need not hold anything -- and writes
// all sixteen byte lines.
template <unsigned P>
INLINE void TransposeGroupForwardExact(const TransposeTables4& t, __m512i* r) {
  static_assert(P >= 1 && P <= kZ4Registers, "P must be 1..16");
  ForwardStageExact<0, P>(t, r);
  ForwardStageExact<1, ExactPrefix(P, 0)>(t, r);
  ForwardStageExact<2, ExactPrefix(P, 1)>(t, r);
  ForwardStageExact<3, ExactPrefix(P, 2)>(t, r);
}

// Byte lines -> interleaved chunks for a path of exactly P buckets.  Reads
// all sixteen lines; writes `[0, P)` and leaves the rest unspecified.
template <unsigned P>
INLINE void TransposeGroupInverseExact(const TransposeTables4& t, __m512i* r) {
  static_assert(P >= 1 && P <= kZ4Registers, "P must be 1..16");
  InverseStageExact<3, ExactPrefix(P, 2)>(t, r);
  InverseStageExact<2, ExactPrefix(P, 1)>(t, r);
  InverseStageExact<1, ExactPrefix(P, 0)>(t, r);
  InverseStageExact<0, P>(t, r);
}

// The tile forms: chunk 0 of a pass is transposed in the tile so the planner
// can read its sixteen meta lines in memory.
template <unsigned P>
inline void TransposeToLines4Exact(__m512i* x, const TransposeTables4& t) {
  __m512i r[kZ4Registers];
  for (unsigned i = 0; i < P; ++i) r[i] = _mm512_load_si512(x + i);
  for (unsigned i = P; i < kZ4Registers; ++i) r[i] = _mm512_setzero_si512();
  TransposeGroupForwardExact<P>(t, r);
  for (unsigned i = 0; i < kZ4Registers; ++i) _mm512_store_si512(x + i, r[i]);
}
template <unsigned P>
inline void TransposeToChunks4Exact(__m512i* x, const TransposeTables4& t) {
  __m512i r[kZ4Registers];
  for (unsigned i = 0; i < kZ4Registers; ++i) r[i] = _mm512_load_si512(x + i);
  TransposeGroupInverseExact<P>(t, r);
  for (unsigned i = 0; i < P; ++i) _mm512_store_si512(x + i, r[i]);
}

// Dispatch a runtime path length (1..16) to a kernel templated on it:
// `f(std::integral_constant<unsigned, P>{})`.  P is public -- it is the
// geometry -- so the switch leaks nothing, and it runs once per pass, not per
// chunk.  A value outside the range is the full network.
template <class F>
INLINE decltype(auto) WithPathBuckets(unsigned P, F&& f) {
#define MICRORAM_TREE_P_CASE(N) \
  case N:                       \
    return f(std::integral_constant<unsigned, N>{});
  switch (P) {
    MICRORAM_TREE_P_CASE(1)
    MICRORAM_TREE_P_CASE(2)
    MICRORAM_TREE_P_CASE(3)
    MICRORAM_TREE_P_CASE(4)
    MICRORAM_TREE_P_CASE(5)
    MICRORAM_TREE_P_CASE(6)
    MICRORAM_TREE_P_CASE(7)
    MICRORAM_TREE_P_CASE(8)
    MICRORAM_TREE_P_CASE(9)
    MICRORAM_TREE_P_CASE(10)
    MICRORAM_TREE_P_CASE(11)
    MICRORAM_TREE_P_CASE(12)
    MICRORAM_TREE_P_CASE(13)
    MICRORAM_TREE_P_CASE(14)
    MICRORAM_TREE_P_CASE(15)
    default:
      return f(std::integral_constant<unsigned, 16>{});
  }
#undef MICRORAM_TREE_P_CASE
}

// Scalar reference, for tests: in[i][4 c + z] -> out[c][4 i + z], over 16
// columns and 64 lanes.
inline void TransposeInterleavedReference(const uint8_t* in, uint8_t* out) {
  constexpr unsigned z = kBucketSlots;
  constexpr unsigned cols = 64 / z;
  for (unsigned i = 0; i < cols; ++i) {
    for (unsigned c = 0; c < cols; ++c) {
      for (unsigned k = 0; k < z; ++k) {
        out[c * 64 + z * i + k] = in[i * 64 + z * c + k];
      }
    }
  }
}

// ---------------------------------------------------------------------------
// A path's chunks in and out of a tile
// ---------------------------------------------------------------------------
//
// Chunk `t` of every bucket of the path into the tile, plus the prefetch of
// the chunk `ahead` further on.  `t` is an index into the ARENA's chunks --
// a plane's own, not the entry's -- because that is what the stride is.
// Registers [P, Live) are zeroed for the network that reads them.
template <unsigned Live>
INLINE void LoadChunkInto(__m512i* tile, uint8_t* const* bucket, unsigned P,
                          size_t t, size_t stored_chunks, unsigned ahead) {
  const size_t off = t * kChunkBytes;
  const bool more = t + ahead < stored_chunks;
  const size_t poff = (t + ahead) * kChunkBytes;
  for (unsigned i = 0; i < P; ++i) {
    tile[i] = _mm512_load_si512(reinterpret_cast<const void*>(bucket[i] + off));
    if (more) {
      _mm_prefetch(reinterpret_cast<const char*>(bucket[i] + poff), _MM_HINT_T0);
    }
  }
  for (unsigned i = P; i < Live; ++i) tile[i] = _mm512_setzero_si512();
}

INLINE void StoreChunkFrom(const __m512i* tile, uint8_t* const* bucket,
                           unsigned P, size_t t) {
  const size_t off = t * kChunkBytes;
  for (unsigned i = 0; i < P; ++i) {
    _mm512_store_si512(reinterpret_cast<void*>(bucket[i] + off), tile[i]);
  }
}

}  // namespace tree
}  // namespace microram
