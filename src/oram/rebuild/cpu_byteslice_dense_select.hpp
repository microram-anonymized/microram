#pragma once

// LEVEL ONE'S DIRECT B BUILD: the deduplicated dense prefix goes straight
// into a U-bucket table, with no butterfly and no bounded intermediate stash.
// A dense prefix is the online requester's unhashed buffer of recent accesses;
// level one is the smallest hashed level; B is the hashed table of U buckets
// the prefix becomes before level one's merge consumes it.  The level-arena
// design ("Directly built level one" in src/oram/levelarena/DESIGN.md) places
// this build in the hierarchy and gives its cost and capacity accounting.
//
//   1. ComputeDenseHomesRange hashes every prefix bucket ONCE and caches each
//      lane's B home, the low log2(U) bits of its raw tag, as byte lines.
//      Dummy lanes are hashed too: the work is a function of the layout.
//   2. SelectDenseHomesRange visits, for every B home h, every prefix bucket
//      in public order, and takes the remaining winners whose home is h into
//      the lowest free lanes of B[h], in source-lane order, until B[h] is
//      full.  Taken lanes leave the private remaining masks; rejected ones
//      stay there.  B is globally unique after the prefix dedup, so nothing
//      is compared against what B[h] already holds.
//   3. DrainDenseRemainderRange appends what is left, in source-bucket and
//      lane order, to one residual stash: B's one-bucket tier above digit
//      one, the output tier at digit one.  It is the build's only capacity
//      check, and its occupancy is exactly sum_h (X_h - 64)_+.
//
// Every destination writes all of its payload lines and its mask, so a
// destination with stale bytes needs no clearing; tag lines are left alone,
// since whoever consumes B re-hashes the key (the fixed insertion recomputes
// each entry's way, a consumer of a published table re-tags it).
//
// THE HOMES AGREE WITH THE FINAL MAP.  The merge's index map keeps the low
// K + e >= K = log2(U) raw tag bits verbatim (kRaw, or kRadixDigit with
// low_bits = K + e), so final_home mod U is B's home and destination v of the
// fixed insertion reads B[v mod U].  That holds only under the job's own
// nonce and key, which is why both are the merge's.
//
// Secret: occupancy, homes, candidate masks, the taken and used lanes.  They
// enter only register compares, pdep/popcnt, the merge index's expand and
// masked permutes of unmasked loads.  Loop bounds and addresses are public.

#include <immintrin.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>

#include "src/core/mov_intrinsics.hpp"
#include "src/crypto/hash_primitives.hpp"
#include "src/oram/rebuild/cpu_byteslice_mergesplit.hpp"
#include "src/oram/rebuild/cpu_byteslice_mergesplit_stash.hpp"
#include "src/oram/rebuild/cpu_byteslice_residual_stash.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/table/cpu_byteslice_routing_map.hpp"

namespace microram {
namespace byteslice {

// Byte lines of one prefix bucket's cached homes: one per started byte of
// the home.
inline size_t DenseHomeLines(unsigned home_bits) {
  return home_bits <= 8 ? 1 : (home_bits + 7) / 8;
}

inline void ComputeDenseHomesRange(const TableView& prefix, uint8_t* homes,
                                   unsigned home_bits, uint64_t nonce_lo,
                                   uint64_t nonce_hi,
                                   const AesTagKeys& aes_keys, size_t begin,
                                   size_t end) {
  const uint64_t high_word = crypto::PackAesCtrHighWord(nonce_lo, nonce_hi);
  const size_t key_bytes = prefix.layout.key_bytes;
  const bool wide_key = key_bytes > 8;
  const size_t lines = DenseHomeLines(home_bits);
  const __m512i keep =
      _mm512_set1_epi64(static_cast<long long>(LowMask64(home_bits)));
  for (size_t b = begin; b < end; ++b) {
    __m512i tags[8];
    HashBucketKeys(prefix.data + b * prefix.layout.BucketBytes(), key_bytes,
                   wide_key, high_word, aes_keys, tags);
    for (int i = 0; i < 8; ++i) tags[i] = _mm512_and_si512(tags[i], keep);
    for (size_t j = 0; j < lines; ++j) {
      __m512i words[8];
      for (int i = 0; i < 8; ++i) {
        words[i] = _mm512_srli_epi64(tags[i], static_cast<unsigned>(8 * j));
      }
      _mm512_store_si512(
          reinterpret_cast<void*>(homes + (b * lines + j) * kBucketCapacity),
          LowByteLine(words));
    }
  }
}

// The remaining lanes of one prefix bucket whose cached home is `home`.
inline uint64_t DenseHomeCandidates(const uint8_t* home_lines, size_t lines,
                                    uint64_t remaining, size_t home) {
  uint64_t cand = remaining;
  for (size_t j = 0; j < lines; ++j) {
    cand &= core::obliCmpEqMask8(
        core::obliLoad512(home_lines + j * kBucketCapacity),
        _mm512_set1_epi8(static_cast<char>(home >> (8 * j))));
  }
  return cand;
}

// Sources are planned this many at a time, so that each destination line is
// loaded and stored once per chunk rather than once per source.
inline constexpr size_t kDenseSelectChunk = 8;

// `prefix` is the borrowed payload with the PRIVATE remaining masks; `dst`
// is B's main, U buckets; `homes` the cache above.  Cannot overflow: what does
// not fit stays in the remaining masks for the drain.
inline void SelectDenseHomesRange(const TableView& prefix,
                                  const uint8_t* homes, unsigned home_bits,
                                  const TableView& dst, size_t begin,
                                  size_t end) {
  const size_t sources = prefix.num_buckets;
  const size_t bucket_bytes = prefix.layout.BucketBytes();
  const size_t payload = prefix.layout.PayloadLines();
  const size_t lines = DenseHomeLines(home_bits);
  for (size_t h = begin; h < end; ++h) {
    uint8_t* const out = dst.data + h * bucket_bytes;
    uint64_t occupied = 0;
    for (size_t first = 0; first < sources; first += kDenseSelectChunk) {
      const size_t n = std::min(kDenseSelectChunk, sources - first);
      __m512i index[kDenseSelectChunk];
      uint64_t keep[kDenseSelectChunk];
      for (size_t i = 0; i < n; ++i) {
        const size_t s = first + i;
        const uint64_t cand = DenseHomeCandidates(
            homes + s * lines * kBucketCapacity, lines, prefix.masks[s], h);
        const unsigned alloc =
            std::min(Popcount64(cand),
                     static_cast<unsigned>(kBucketCapacity) -
                         Popcount64(occupied));
        const uint64_t used = _pdep_u64(LowMask64(alloc), ~occupied);
        const uint64_t taken = _pdep_u64(LowMask64(alloc), cand);
        index[i] = BuildMergeIndex(used, taken);
        occupied |= used;
        keep[i] = occupied;
        prefix.masks[s] &= ~taken;
      }
      for (size_t line = 0; line < payload; ++line) {
        const size_t off = line * kBucketCapacity;
        __m512i acc = first == 0 ? _mm512_setzero_si512()
                                 : core::obliLoad512(out + off);
        for (size_t i = 0; i < n; ++i) {
          acc = _mm512_maskz_permutex2var_epi8(
              _cvtu64_mask64(keep[i]), core::obliPin512(acc), index[i],
              core::obliLoad512(prefix.data + (first + i) * bucket_bytes +
                                off));
        }
        _mm512_store_si512(reinterpret_cast<void*>(out + off), acc);
      }
    }
    dst.masks[h] = occupied;
  }
}

// The rejected winners of prefix buckets [begin, end), appended to `tier` in
// bucket order.  False when the tier would overflow (a declared failure).
template <bool CheckOverflow>
inline bool DrainDenseRemainderRange(const TableView& prefix,
                                     ResidualStash& tier, size_t begin,
                                     size_t end) {
  const size_t payload = prefix.layout.PayloadLines();
  for (size_t s = begin; s < end; ++s) {
    if (!MergeBucketIntoResidualStash<CheckOverflow>(
            tier, prefix.data + s * prefix.layout.BucketBytes(),
            prefix.masks[s], payload)) {
      return false;
    }
  }
  return true;
}

}  // namespace byteslice
}  // namespace microram
