#pragma once

// MergeSplit: the two-bucket primitive every routing network here is built
// from.
//
// One MergeSplit takes two 64-slot buckets and one tag bit, and rewrites them
// so the first holds every entry whose bit is 0 and the second every entry
// whose bit is 1.  Splitting needs no data movement at all -- two VPTESTMB
// compares against the tag line give the direction masks.  The merge is the
// part that moves bytes.
//
// The classical formulation compresses the second bucket's survivors and
// expands them into the first's free slots: two vector operations per byte
// line per output.  The observation that collapses it is that the first
// bucket's entries never move, and the second's land on free slots in
// ASCENDING order -- so both endpoints of every movement are a function of the
// direction masks alone, one PDEP each.  The permutation is therefore fixed
// for the whole entry: BuildMergeIndex constructs the index vector once per
// MergeSplit and every byte line reuses it, so one VPERMT2B replaces each
// compress/expand pair.
//
// The case rests on instruction throughput, not on operation count: on Zen 5
// one VPERMT2B has a higher throughput than either VPCOMPRESSB or VPEXPANDB.
// The ratio differs between microarchitectures, and the choice hinges on it,
// so re-check it before porting the kernel to another one.
//
// The butterfly built out of it is log2(num_buckets) levels of MergeSplits,
// level `lev` pairing buckets (i, i + 2^lev) on tag bit `lev`.  LSB-first is
// what makes it in place and in natural order: after every level the entry with
// tag t sits in bucket t mod num_buckets, so the routed array IS the final hash
// table and no separate hash-placement pass exists.  The butterfly itself lives
// in cpu_byteslice_butterfly_stash.hpp: the hierarchy runs at load 0.5, where
// every level needs somewhere to shed to, so there is no stashless butterfly in
// the library.
//
// A MergeSplit overflows iff more than 64 entries want one direction.  At load
// 0.5 a pair holds 64 real entries on average, which is why a rebuild routes
// through MergeSplitPairStash and not through the bare pair below.  The bare
// pair serves the blank-first separated continuation, whose two buckets are
// bounded by construction rather than by a tail bound.

#include <immintrin.h>

#include <cassert>
#include <cstddef>
#include <cstdint>

#include "src/core/mov_intrinsics.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"

namespace microram {
namespace byteslice {

// ---------------------------------------------------------------------------
// MergeSplit
// ---------------------------------------------------------------------------

// [0..63] and [64..127]. _mm512_permutex2var_epi8 reads the low 7 bits of
// each index byte, so 0..63 selects the first source and 64..127 the second.
inline __m512i IotaBytes() {
  return _mm512_setr_epi64(0x0706050403020100LL, 0x0F0E0D0C0B0A0908LL,
                           0x1716151413121110LL, 0x1F1E1D1C1B1A1918LL,
                           0x2726252423222120LL, 0x2F2E2D2C2B2A2928LL,
                           0x3736353433323130LL, 0x3F3E3D3C3B3A3938LL);
}
inline __m512i IotaBytesHigh() {
  return _mm512_setr_epi64(0x4746454443424140LL, 0x4F4E4D4C4B4A4948LL,
                           0x5756555453525150LL, 0x5F5E5D5C5B5A5958LL,
                           0x6766656463626160LL, 0x6F6E6D6C6B6A6968LL,
                           0x7776757473727170LL, 0x7F7E7D7C7B7A7978LL);
}

// The same, layered ONTO an index some earlier round already built: lanes
// outside `dest_slots` keep whatever `base` says, and each round pairs its own
// dest and source slots in ascending order independently of the others.  The
// rounds must claim disjoint `dest_slots`, which every caller gets for free by
// allocating out of the occupancy the previous round left.
//
// Two rounds is what the merged offer needs (PlanResidualOfferMerge): its two
// freshness classes allocate separately, and their pairings interleave, so one
// BuildMergeIndex over the union would pair the wrong slots.
//
// The expand is the register-only core form: `dest_slots` is secret, and an
// expand whose source GCC had spilled read only popcount(dest_slots) bytes of
// the spill slot.
inline __m512i BuildMergeIndexOnto(__m512i base, uint64_t dest_slots,
                                   uint64_t source_slots) {
  const __m512i packed = _mm512_maskz_compress_epi8(
      _cvtu64_mask64(source_slots), IotaBytesHigh());
  return core::obliMaskExpand8(base, dest_slots, packed);
}

// Index for "keep the destination's own byte, except at `dest_slots`, which
// take the source line's bytes at `source_slots` in ascending slot order".
// popcount(dest_slots) must equal popcount(source_slots).
inline __m512i BuildMergeIndex(uint64_t dest_slots, uint64_t source_slots) {
  return BuildMergeIndexOnto(IotaBytes(), dest_slots, source_slots);
}

// The scalar plan shared by the plain, residual-stash, and fused-quad
// MergeSplits. A keeps its entries in their original slots. As many of B's
// direction-0 / direction-1 entries as fit are placed in A's free slots, in
// source-slot order; `residual` is the suffix of B that did not fit.
//
// The plain load-0.25 kernel treats a nonempty residual as overflow in checked
// mode. The load-0.5 kernels merge it into their per-level stash instead. The
// policy therefore stays with each caller while this plan fixes the common
// placement and permutation algebra.
struct PairMergePlan {
  __m512i idx_a;  // builds output A from (A_line, B_line)
  __m512i idx_b;  // builds output B from the same two lines
  uint64_t new_a = 0;
  uint64_t new_b = 0;
  uint64_t residual = 0;
};

inline PairMergePlan PlanMergePair(uint64_t a_real, uint64_t b_real,
                                   uint64_t a_one, uint64_t b_one) {
  const uint64_t a_zero = a_real & ~a_one;
  const uint64_t b_zero = b_real & ~b_one;
  const unsigned free_zero =
      static_cast<unsigned>(kBucketCapacity) - Popcount64(a_zero);
  const unsigned free_one =
      static_cast<unsigned>(kBucketCapacity) - Popcount64(a_one);
  const unsigned alloc_zero = std::min(Popcount64(b_zero), free_zero);
  const unsigned alloc_one = std::min(Popcount64(b_one), free_one);
  const uint64_t used_zero = _pdep_u64(LowMask64(alloc_zero), ~a_zero);
  const uint64_t used_one = _pdep_u64(LowMask64(alloc_one), ~a_one);
  const uint64_t src_zero = _pdep_u64(LowMask64(alloc_zero), b_zero);
  const uint64_t src_one = _pdep_u64(LowMask64(alloc_one), b_one);
  PairMergePlan plan;
  plan.idx_a = BuildMergeIndex(used_zero, src_zero);
  plan.idx_b = BuildMergeIndex(used_one, src_one);
  plan.new_a = a_zero | used_zero;
  plan.new_b = a_one | used_one;
  plan.residual = (b_zero & ~src_zero) | (b_one & ~src_one);
  return plan;
}

// Reads the routing bit from a bucket pair and feeds the resulting direction
// masks into the scalar planner above. The plain and stash kernels differ only
// after this point: one treats `residual` as overflow, the other stores it.
inline PairMergePlan PlanMergePairByTagBit(
    const uint8_t* first, const uint8_t* second, uint64_t first_real,
    uint64_t second_real, size_t tag_line, unsigned bit) {
  const size_t tag_off = tag_line * kBucketCapacity;
  const __m512i bit_probe =
      _mm512_set1_epi8(static_cast<char>(uint8_t{1} << (bit & 7)));
  const __m512i first_tags =
      _mm512_load_si512(reinterpret_cast<const void*>(first + tag_off));
  const __m512i second_tags =
      _mm512_load_si512(reinterpret_cast<const void*>(second + tag_off));
  const uint64_t first_one =
      core::obliTestMask8(first_tags, bit_probe) & first_real;
  const uint64_t second_one =
      core::obliTestMask8(second_tags, bit_probe) & second_real;
  return PlanMergePair(first_real, second_real, first_one, second_one);
}

// In-place MergeSplit of two byte-sliced buckets on the tag bit `bit & 7` of
// byte line `tag_line`. On return `first` holds the direction-0 entries of
// both buckets and `second` the direction-1 entries; *first_mask /
// *second_mask are updated to match.
// With CheckOverflow=true, returns false iff either direction would exceed
// 64 entries (the buckets are left unmodified in that case; callers treat it
// as a rebuild failure and restart with a fresh nonce).  Unchecked mode is
// the default and relies on the negligible overflow bound.
//
// `lines` is how many byte lines to route, i.e. Layout::RoutedLines(bit):
// lines past it are tag bytes this and every later level has already retired
// (see the Layout comment on the reversed tag byte order).  `tag_line` is
// read whether or not it falls inside `lines`.
//
// Every output byte is a byte of `first` or of `second` at a position fixed
// by the direction masks, so one two-source byte permute (VPERMT2B) per
// output does the whole merge -- see the MergeSplit section of the file
// header.  The two permutation indices are built once per MergeSplit (one
// VPCOMPRESSB + VPEXPANDB each, on index vectors) and reused across all
// routed byte lines.
//
// BlankFirst: `first` is PUBLICLY empty, which only the caller knows.  Its
// mask is taken as zero without being read -- it may be stale -- and neither
// its tag line nor its byte lines are loaded: both plan indices select only
// second's lanes and maskz zeroes the rest, so a zero register stands in for
// every first line and the output is the same bytes.  Both buckets are still
// written.  It can never shed.
template <bool CheckOverflow = false, bool BlankFirst = false>
inline bool MergeSplitPair(uint8_t* first, uint8_t* second,
                           uint64_t* first_mask, uint64_t* second_mask,
                           size_t lines, size_t tag_line, unsigned bit) {
  const uint64_t second_real = *second_mask;
  PairMergePlan plan;
  if constexpr (BlankFirst) {
    const __m512i second_tags = _mm512_load_si512(
        reinterpret_cast<const void*>(second + tag_line * kBucketCapacity));
    const __m512i bit_probe =
        _mm512_set1_epi8(static_cast<char>(uint8_t{1} << (bit & 7)));
    plan = PlanMergePair(0, second_real, 0,
                         core::obliTestMask8(second_tags, bit_probe) &
                             second_real);
  } else {
    plan = PlanMergePairByTagBit(first, second, *first_mask, second_real,
                                 tag_line, bit);
  }
  if constexpr (CheckOverflow) {
    if (plan.residual != 0) return false;
  }
  const __mmask64 keep_zero = _cvtu64_mask64(plan.new_a);
  const __mmask64 keep_one = _cvtu64_mask64(plan.new_b);

  uint8_t* first_ptr = first;
  uint8_t* second_ptr = second;
  for (size_t line = 0; line < lines; ++line) {
    const __m512i first_line =
        BlankFirst ? _mm512_setzero_si512()
                   : _mm512_load_si512(reinterpret_cast<const void*>(first_ptr));
    const __m512i second_line =
        _mm512_load_si512(reinterpret_cast<const void*>(second_ptr));
    _mm512_store_si512(reinterpret_cast<void*>(first_ptr),
                       _mm512_maskz_permutex2var_epi8(keep_zero, first_line,
                                                      plan.idx_a, second_line));
    _mm512_store_si512(reinterpret_cast<void*>(second_ptr),
                       _mm512_maskz_permutex2var_epi8(keep_one, first_line,
                                                      plan.idx_b, second_line));
    first_ptr += kBucketCapacity;
    second_ptr += kBucketCapacity;
  }

  *first_mask = plan.new_a;
  *second_mask = plan.new_b;
  return true;
}
}  // namespace byteslice
}  // namespace microram
