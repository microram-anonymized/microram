#pragma once

// A 512-slot MergeSplit, for cpu_byteslice_stash_rebuild_benchmark's
// comparison against the 64-slot kernels (`--arm slot512` and
// `--network butterfly512`).  Benchmark-only: nothing in src/ includes it.
//
// WHAT IT IS.  The buckets are 512 slots (the byte-sliced layout with a
// 512-byte line, eight ZMM registers per byte line).  Two buckets, `first` and
// `second`, are split in place on one tag bit with the SAME contract as the
// 64-slot MergeSplitPairStash: the records of `first` stay at their slot on the
// side their tag bit selects (side 0 is `first`'s memory, side 1 is `second`'s),
// and the records of `second` of a direction fill that side's free slots in slot
// order.  The surplus (a suffix of `second`'s records of that direction) cannot
// be shed: there is no residual stash at this bucket size, so a surplus is an
// overflow, and the call returns false BEFORE touching anything.  At load 0.5 a
// 512-slot bucket overflows with negligible probability, which is what the large
// bucket buys.  Output slots that hold no record are zero.
//
// HOW.  The 64-slot kernels do a merge as one VPERMT2B per output line, or as a
// VPCOMPRESSB + VPEXPANDB per direction.  A compress cannot cross a register, so
// at 512 slots each ZMM register of `second` is compressed on its own, and its
// run of selected bytes is expanded into the free slots of the output register(s)
// that its ranks reach.  Source register i's records are ranks [O_i, O_i + k_i) of
// the dense run of selected records, output register j's free slots take ranks
// [R_j, R_j + m_j), so the pair (i, j) moves the overlap of those two intervals:
// one VPCOMPRESSB under a mask and one masked VPEXPANDB.  Which pairs overlap is
// secret, so all 8 x 8 pairs run for each side and each byte line, with masks
// that are zero where the intervals do not meet.  All masks are planned once per
// MergeSplit with scalar mask arithmetic (popcount, PDEP, min/max), exactly as the
// 64-slot planners do, and no branch or memory index depends on a tag or an
// occupancy bit.  Per byte line the work is 2 sides x 64 pairs x (compress +
// expand) = 256 vector operations, against 2 VPERMT2B for 64 slots; that ratio, and
// what a 512-slot bucket saves in stash handling, is what the comparison measures.
// (A shared two-source-permute plan, like the 64-slot kernel's, would cut the
// per-line work to about 64 VPERMT2B for a more expensive plan; it is not
// implemented here.)
//
// STATE.  A bucket's occupancy is eight 64-bit words, word w holding slots
// [64 w, 64 w + 64).  Byte line L of a bucket is the 512 bytes at L * 512.

#include <immintrin.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>

#include "src/oram/rebuild/cpu_byteslice_stash_rebuild.hpp"

namespace microram {
namespace byteslice {
namespace slot512 {

constexpr size_t kSlots = 512;
constexpr size_t kWords = kSlots / 64;

// Everything the byte lines need: planned once, applied to every line.
struct Plan {
  uint64_t keep[2][kWords];           // `first`'s records that stay, by side
  uint64_t out_mask[2][kWords];       // each side's occupancy afterwards
  uint64_t dest[2][kWords][kWords];   // [side][j][i]: output lanes of j fed by i
  uint64_t take[2][kWords][kWords];   // [side][j][i]: second register i's slots
};

// The planners are scalar mask arithmetic on eight words.  Left alone, GCC
// SLP-vectorizes those words into 512-bit logic, including VPANDNQ, a form the
// timing test does not certify (and a vector form nothing here needs); the plan is
// a small fraction of the work, so it is kept scalar.
#define MICRORAM_SLOT512_SCALAR \
  __attribute__((optimize("no-tree-vectorize", "no-tree-slp-vectorize")))

namespace detail {

MICRORAM_SLOT512_SCALAR inline unsigned CountWords(const uint64_t* w) {
  unsigned n = 0;
  for (size_t i = 0; i < kWords; ++i) n += Popcount64(w[i]);
  return n;
}

// The first `count` set bits of the 512-bit set `in`, in slot order.
MICRORAM_SLOT512_SCALAR inline void FirstSet(const uint64_t* in, unsigned count, uint64_t* out) {
  int rest = static_cast<int>(count);
  for (size_t w = 0; w < kWords; ++w) {
    const int here = static_cast<int>(Popcount64(in[w]));
    const int take = std::min(std::max(rest, 0), here);
    out[w] = _pdep_u64(LowMask64(static_cast<unsigned>(take)), in[w]);
    rest -= here;
  }
}

}  // namespace detail

// Plans one side: `keep` is first's records of this direction, `want` second's.
// Returns the number of second's records that do not fit (0 = fits).
MICRORAM_SLOT512_SCALAR inline unsigned PlanSide(const uint64_t* keep, const uint64_t* want, uint64_t* out_mask,
                         uint64_t dest[kWords][kWords], uint64_t take[kWords][kWords]) {
  uint64_t free_slots[kWords], used[kWords], source[kWords];
  for (size_t w = 0; w < kWords; ++w) free_slots[w] = ~keep[w];
  const unsigned nfree = detail::CountWords(free_slots);
  const unsigned nwant = detail::CountWords(want);
  const unsigned alloc = std::min(nwant, nfree);
  detail::FirstSet(free_slots, alloc, used);
  detail::FirstSet(want, alloc, source);
  // Ranks: output register j takes [R_j, R_j + m_j), source register i holds
  // [O_i, O_i + k_i) of the dense run of the alloc records that fit.
  int rank_out[kWords], count_out[kWords], rank_src[kWords], count_src[kWords];
  int r = 0, o = 0;
  for (size_t w = 0; w < kWords; ++w) {
    count_out[w] = static_cast<int>(Popcount64(used[w]));
    count_src[w] = static_cast<int>(Popcount64(source[w]));
    rank_out[w] = r;
    rank_src[w] = o;
    r += count_out[w];
    o += count_src[w];
  }
  for (size_t j = 0; j < kWords; ++j) {
    for (size_t i = 0; i < kWords; ++i) {
      const int lo = std::max(rank_src[i], rank_out[j]);
      const int hi = std::min(rank_src[i] + count_src[i], rank_out[j] + count_out[j]);
      const int len = std::max(hi - lo, 0);
      // len > 0 puts both offsets below 64; len = 0 makes both masks empty, and
      // & 63 only keeps the shift defined.
      const uint64_t run = LowMask64(static_cast<unsigned>(len));
      const unsigned x = static_cast<unsigned>(lo - rank_out[j]) & 63u;
      const unsigned y = static_cast<unsigned>(lo - rank_src[i]) & 63u;
      dest[j][i] = _pdep_u64(run << x, used[j]);
      take[j][i] = _pdep_u64(run << y, source[i]);
    }
  }
  for (size_t w = 0; w < kWords; ++w) out_mask[w] = keep[w] | used[w];
  return nwant - alloc;
}

// Reads the tag bit `bit & 7` of byte line `tag_line` of both buckets and plans
// both sides.  Returns false iff either side would overflow (nothing is written).
MICRORAM_SLOT512_SCALAR inline bool PlanMergeSplit(const uint8_t* first, const uint8_t* second,
                           const uint64_t* first_mask, const uint64_t* second_mask,
                           size_t tag_line, unsigned bit, Plan* plan) {
  const __m512i probe = _mm512_set1_epi8(static_cast<char>(uint8_t{1} << (bit & 7)));
  uint64_t first_one[kWords], second_one[kWords];
  for (size_t w = 0; w < kWords; ++w) {
    const __m512i ft = _mm512_load_si512(
        reinterpret_cast<const void*>(first + tag_line * kSlots + 64 * w));
    const __m512i st = _mm512_load_si512(
        reinterpret_cast<const void*>(second + tag_line * kSlots + 64 * w));
    first_one[w] = core::obliTestMask8(ft, probe) & first_mask[w];
    second_one[w] = core::obliTestMask8(st, probe) & second_mask[w];
  }
  uint64_t keep[2][kWords], want[2][kWords];
  for (size_t w = 0; w < kWords; ++w) {
    keep[0][w] = first_mask[w] & ~first_one[w];
    keep[1][w] = first_one[w];
    want[0][w] = second_mask[w] & ~second_one[w];
    want[1][w] = second_one[w];
  }
  unsigned surplus = 0;
  for (int s = 0; s < 2; ++s) {
    for (size_t w = 0; w < kWords; ++w) plan->keep[s][w] = keep[s][w];
    surplus |= PlanSide(keep[s], want[s], plan->out_mask[s], plan->dest[s], plan->take[s]);
  }
  return surplus == 0;
}

// Applies a plan to `lines` byte lines (bucket bytes are lines * 512).
inline void ApplyPlan(uint8_t* first, uint8_t* second, size_t lines, const Plan& plan) {
  for (size_t line = 0; line < lines; ++line) {
    uint8_t* fp = first + line * kSlots;
    uint8_t* sp = second + line * kSlots;
    __m512i f[kWords], v[kWords], out[2][kWords];
    for (size_t w = 0; w < kWords; ++w) {
      f[w] = _mm512_load_si512(reinterpret_cast<const void*>(fp + 64 * w));
      v[w] = _mm512_load_si512(reinterpret_cast<const void*>(sp + 64 * w));
    }
    for (int s = 0; s < 2; ++s) {
      for (size_t j = 0; j < kWords; ++j) {
        out[s][j] = _mm512_maskz_mov_epi8(_cvtu64_mask64(plan.keep[s][j]), f[j]);
      }
      for (size_t j = 0; j < kWords; ++j) {
        for (size_t i = 0; i < kWords; ++i) {
          out[s][j] = _mm512_mask_expand_epi8(
              out[s][j], _cvtu64_mask64(plan.dest[s][j][i]),
              _mm512_maskz_compress_epi8(_cvtu64_mask64(plan.take[s][j][i]), v[i]));
        }
      }
    }
    for (size_t w = 0; w < kWords; ++w) {
      _mm512_store_si512(reinterpret_cast<void*>(fp + 64 * w), out[0][w]);
      _mm512_store_si512(reinterpret_cast<void*>(sp + 64 * w), out[1][w]);
    }
  }
}

// MergeSplit of two 512-slot buckets: `first` becomes side 0, `second` side 1;
// the masks follow.  `lines` is how many byte lines to route
// (Layout::RoutedLines(bit)); `tag_line` is read whether or not it is among them.
// False (nothing modified) iff a side would exceed 512 records.
inline bool MergeSplit(uint8_t* first, uint8_t* second, uint64_t* first_mask,
                       uint64_t* second_mask, size_t lines, size_t tag_line,
                       unsigned bit) {
  Plan plan;
  if (!PlanMergeSplit(first, second, first_mask, second_mask, tag_line, bit, &plan)) {
    return false;
  }
  ApplyPlan(first, second, lines, plan);
  for (size_t w = 0; w < kWords; ++w) {
    first_mask[w] = plan.out_mask[0][w];
    second_mask[w] = plan.out_mask[1][w];
  }
  return true;
}

}  // namespace slot512
}  // namespace byteslice
}  // namespace microram
