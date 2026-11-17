#pragma once

// Mixed-radix routing: how a table whose bucket count is not a power of two
// gets routed.
//
// In a hierarchy of fanout B ("base-B": a level's digit m, 1 <= m < B, counts
// the carries it holds, like one digit of a base-B counter; see
// src/oram/table/cpu_byteslice_routing_map.hpp), a level at digit m holds a
// table of m * 2^k buckets.  With
// m = r * 2^e and r odd, an entry's destination is
//
//     idx = (T mod 2^(k+e)) + 2^(k+e) * ((T >> (k+e)) mod r)
//
// so the low field is an ordinary butterfly over 2^(k+e) buckets and the high
// field is one r-way split.  The butterfly runs first, over r independent
// blocks that all route the SAME bit levels; the radix pass is the last step,
// after which no tag line is live and every following kernel moves payload
// only.
//
// The r-way MergeSplit generalizes the pair: output q is built by chaining one
// VPERMT2B per other input bucket, each contributing the entries destined for q
// at positions fixed by the direction masks.  Both the radix and the stash
// bucket count are public, so the kernel is fully specialized on them and the
// R*R permutation indices stay in registers across the byte-line loop instead
// of being rebuilt per line.  r is odd and at most 7, so R*R is at most 49
// index registers' worth of work spread over the line loop, not per line.

#include <immintrin.h>

#include <cassert>
#include <cstddef>
#include <cstdint>

#include "src/core/mov_intrinsics.hpp"
#include "src/oram/rebuild/cpu_byteslice_butterfly_stash.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/rebuild/cpu_byteslice_mergesplit_stash.hpp"
#include "src/oram/rebuild/cpu_byteslice_residual_stash.hpp"

namespace microram {
namespace byteslice {

// ---------------------------------------------------------------------------
// Mixed-radix routing
// ---------------------------------------------------------------------------
//
// A base-B hierarchy level with digit m holds a table of m * 2^k buckets.
// With m = r * 2^e (r odd), the destination index of an entry is
//   idx = (T mod 2^(k+e)) + 2^(k+e) * ((T >> (k+e)) mod r)
// routed as: plain butterfly on the low k+e bits inside each of the r
// contiguous 2^(k+e)-bucket blocks, then one radix-r MergeSplit pass across
// the blocks (stride 2^(k+e)), routed on a digit byte precomputed by the
// kRadixDigit tag map into the last tag byte line.

inline constexpr unsigned kMaxRadix = 7;

// The widest FAN-IN of the fixed level's sweep (MergeRadixSourceBucket): how
// many destination buckets one source bucket may be split across.  It is a
// different bound from kMaxRadix, and the level arena's top is why: a top
// whose digit is a power of two routes A with binary butterfly levels and no
// radix pass at all, so its sweep is D-way with no radix-D kernel behind it.
// D = 8 is the ceiling because the way is packed into the digit's three bits.
inline constexpr unsigned kMaxFixedMergeWays = 8;
static_assert(kMaxFixedMergeWays >= kMaxRadix,
              "every radix pass's fan-in is also a legal sweep fan-in");

// The digit byte line reduced to the digit alone.  The line may also carry the
// top index bits (Layout::digit_bits packs the two into one byte rather than
// reserving a whole tag line for three bits), so shift the digit down and mask
// the rest away before comparing it to a direction.
//
// The shift is 16-bit because AVX-512 has no byte shift: within a 16-bit lane
// the low byte's high bits are filled from the high byte's low bits, and the
// AND then keeps only bits [k, k+3) of each byte -- which is exactly the digit
// as long as k <= 5, and RoutingDigitPacks guarantees that.  At digit_bits ==
// 0 the byte is the digit's alone and this is one AND against a value already
// below 8, i.e. a no-op the compiler still has to issue; it costs two
// instructions per BUCKET against R*R mask builds and `lines` permutes.
inline __m512i NormalizeDigitLine(__m512i line, size_t digit_bits) {
  return _mm512_and_si512(
      _mm512_srli_epi16(line, static_cast<unsigned>(digit_bits)),
      _mm512_set1_epi8(0x7));
}

// r-way MergeSplit over r buckets, routed on the digit byte line (values in
// [0, r)).  Output bucket q keeps its own direction-q entries in their slots
// and receives the other buckets' direction-q streams in ascending input
// order; surplus is shed obliviously into the stash exactly like
// MergeSplitPairStash. In checked mode, returns false if the aggregate stash
// capacity would be exceeded. A tuple may shed more than 64 entries: each
// source's sheds are permuted straight into all available stash buckets.
// Limiting a tuple to 64 would introduce a separate failure even when the
// stash fits; that event can involve several excesses (e.g. 33 + 32).
//
// Output q is built by chaining one VPERMT2B per other input bucket (each
// writes a disjoint slot set, and index s < 64 keeps what the chain already
// holds); the stash merge chains one more permute per source bucket.  That is
// r(r-1) + r permutes per byte line in place of 4r(r-1) compress/expand ops
// plus the staging merge.
//
// The radix and the stash bucket count are both public, so the kernel is
// instantiated per (R, StashBuckets) and dispatched on them: only then do the
// R*R permutation indices stay in registers across the byte-line loop instead
// of being reloaded from the stack on every line.
// An optional final payload transform lets a finalizing residual offer share
// the radix pass's byte loop. The ordinary route instantiates this identity
// and does no extra key work.
//
// BlankFirst: input 0 is PUBLICLY empty (a separated preparation at an odd
// digit, whose block 0 is the carry region B never entered).  Its mask is
// taken as zero without being read, so every route out of it is empty and
// each permute that would take from it is the identity: they are skipped, the
// R-1 output chains and the stash chain one permute shorter each.  Its lines
// are still loaded, because output 0 is built ON them -- a radix output's free
// slots keep whatever its own bucket held -- which keeps the bytes those of
// the general kernel over a zeroed mask.
struct RadixIdentityOutput {
  template <unsigned R, typename Fill>
  void Prepare(uint64_t*, Fill&&) {}
  __m512i Apply(unsigned, __m512i value, size_t) const { return value; }
};

// GCC reports out_idx as maybe uninitialized once this is inlined. The plan
// loop writes every out_idx[q][i] that the line loops read (i != q, from
// the first source on), so the warning is a false positive.
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
template <unsigned R, int StashBuckets, bool CheckOverflow,
          bool BlankFirst = false, typename Finalizer = RadixIdentityOutput>
inline bool MergeSplitRadixStashFixed(uint8_t* const* buckets,
                                      uint64_t* const* bucket_masks,
                                      size_t lines, size_t digit_line_offset,
                                      size_t digit_bits,
                                      ResidualStash& stash,
                                      Finalizer&& finish = {}) {
  const size_t digit_line = digit_line_offset * kBucketCapacity;

  static_assert(!BlankFirst || R >= 2, "a blank input needs a real one");
  uint64_t real[R];
  __m512i digits[R];
  // A blank input 0's mask and digits are never read.
  for (unsigned i = BlankFirst ? 1 : 0; i < R; ++i) {
    real[i] = *bucket_masks[i];
    digits[i] = NormalizeDigitLine(
        _mm512_load_si512(
            reinterpret_cast<const void*>(buckets[i] + digit_line)),
        digit_bits);
  }
  // The register-only compare: with the intrinsic, GCC folded `& real[i]`
  // (secret occupancy) into the compare's write mask and read a spilled digit
  // line or the probe constant from memory under it.
  uint64_t routes[R][R];  // [input i][direction q]
  for (unsigned q = 0; q < R; ++q) {
    const __m512i probe = _mm512_set1_epi8(static_cast<char>(q));
    if constexpr (BlankFirst) routes[0][q] = 0;
    for (unsigned i = BlankFirst ? 1 : 0; i < R; ++i) {
      routes[i][q] = core::obliCmpEqMask8(digits[i], probe) & real[i];
    }
  }

  // Output plan: per (q, i != q), the destination slots in output q and the
  // source slots in input i.  What input i cannot place anywhere is shed.
  __m512i out_idx[R][R];
  uint64_t new_mask[R];
  uint64_t shed[R] = {};
  for (unsigned q = 0; q < R; ++q) {
    uint64_t available = ~routes[q][q];
    unsigned free_count =
        static_cast<unsigned>(kBucketCapacity) - Popcount64(routes[q][q]);
    uint64_t filled = routes[q][q];
    for (unsigned i = BlankFirst ? 1 : 0; i < R; ++i) {
      if (i == q) continue;
      const unsigned alloc = std::min(Popcount64(routes[i][q]), free_count);
      const uint64_t dest = _pdep_u64(LowMask64(alloc), available);
      const uint64_t taken = _pdep_u64(LowMask64(alloc), routes[i][q]);
      out_idx[q][i] = BuildMergeIndex(dest, taken);
      available &= ~dest;
      free_count -= alloc;
      filled |= dest;
      shed[i] |= routes[i][q] & ~taken;
    }
    new_mask[q] = filled;
  }

  unsigned total_shed = 0;
  for (unsigned i = 0; i < R; ++i) total_shed += Popcount64(shed[i]);
  // A zero-capacity stash only makes sense in checked mode; unchecked
  // it would silently drop the surplus instead of shedding it.
  assert(CheckOverflow || stash.num_buckets > 0);
  if constexpr (CheckOverflow) {
    if (stash.Count() + total_shed > stash.Capacity()) {
      return false;
    }
  }

  // Stash plan: one permute per (stash bucket, source bucket).  The first
  // source's permute carries the zeroing mask so free stash slots that
  // receive nothing end up zeroed, exactly as the compress/expand form.
  constexpr size_t kSlots = StashBuckets == kDynamicStashBuckets
                                ? kMaxResidualStashBuckets
                                : static_cast<size_t>(
                                      StashBuckets > 0 ? StashBuckets : 1);
  const size_t stash_buckets = StashBuckets == kDynamicStashBuckets
                                   ? stash.num_buckets
                                   : static_cast<size_t>(
                                         StashBuckets > 0 ? StashBuckets : 0);
  __m512i stash_idx[kSlots][R];
  __mmask64 stash_keep[kSlots];
  uint64_t pending[R];
  for (unsigned i = 0; i < R; ++i) pending[i] = shed[i];
  for (size_t b = 0; b < stash_buckets; ++b) {
    const uint64_t old_mask = stash.masks[b];
    uint64_t available = ~old_mask;
    unsigned free_count =
        static_cast<unsigned>(kBucketCapacity) - Popcount64(old_mask);
    uint64_t filled = old_mask;
    for (unsigned i = BlankFirst ? 1 : 0; i < R; ++i) {
      const unsigned take = std::min(Popcount64(pending[i]), free_count);
      const uint64_t src = _pdep_u64(LowMask64(take), pending[i]);
      const uint64_t dest = _pdep_u64(LowMask64(take), available);
      stash_idx[b][i] = BuildMergeIndex(dest, src);
      available &= ~dest;
      free_count -= take;
      filled |= dest;
      pending[i] &= ~src;
    }
    stash_keep[b] = _cvtu64_mask64(filled);
    stash.masks[b] = filled;
  }

  finish.template Prepare<R>(new_mask, [&](size_t line, __m512i* output) {
    __m512i input[R];
    for (unsigned i = 0; i < R; ++i) {
      input[i] = core::obliLoad512(buckets[i] + line * kBucketCapacity);
    }
    for (unsigned q = 0; q < R; ++q) {
      __m512i value = input[q];
      for (unsigned i = BlankFirst ? 1 : 0; i < R; ++i) {
        if (i != q) {
          value = _mm512_permutex2var_epi8(value, out_idx[q][i], input[i]);
        }
      }
      output[q] = value;
    }
  });

  uint8_t* ptr[R];
  uint8_t* stash_ptr[kSlots];
  for (unsigned i = 0; i < R; ++i) ptr[i] = buckets[i];
  for (size_t b = 0; b < stash_buckets; ++b) stash_ptr[b] = stash.Bucket(b);
  for (size_t line = 0; line < lines; ++line) {
    __m512i in[R];
    for (unsigned i = 0; i < R; ++i) {
      in[i] = _mm512_load_si512(reinterpret_cast<const void*>(ptr[i]));
    }
    // A blank input 0 sheds nothing, so its permute would only apply the
    // keep mask: the next source's permute carries it instead.
    constexpr unsigned first_source = BlankFirst ? 1 : 0;
    for (size_t b = 0; b < stash_buckets; ++b) {
      __m512i acc = _mm512_maskz_permutex2var_epi8(
          stash_keep[b],
          _mm512_load_si512(reinterpret_cast<const void*>(stash_ptr[b])),
          stash_idx[b][first_source], in[first_source]);
      for (unsigned i = first_source + 1; i < R; ++i) {
        acc = _mm512_permutex2var_epi8(acc, stash_idx[b][i], in[i]);
      }
      _mm512_store_si512(reinterpret_cast<void*>(stash_ptr[b]), acc);
      stash_ptr[b] += kBucketCapacity;
    }
    for (unsigned q = 0; q < R; ++q) {
      __m512i out = in[q];
      for (unsigned i = first_source; i < R; ++i) {
        if (i == q) continue;
        out = _mm512_permutex2var_epi8(out, out_idx[q][i], in[i]);
      }
      _mm512_store_si512(reinterpret_cast<void*>(ptr[q]),
                         finish.Apply(q, out, line));
      ptr[q] += kBucketCapacity;
    }
  }
  for (unsigned q = 0; q < R; ++q) {
    *bucket_masks[q] = new_mask[q];
  }
  return true;
}
#pragma GCC diagnostic pop

// How deep a stash the radix kernel is still worth instantiating for.
//
// The butterfly's dispatch table runs the full schedule range because its
// fallback is a cliff (see DispatchStashDepth).  The radix pass is NOT the
// same shape of problem.  Its dynamic form is the
// SAME kernel with a runtime trip count over a stack-resident stash_idx array
// -- not a per-line replan -- so the only thing specialization buys is holding
// R*R + S*R permutation indices in registers, and the R*R term alone is 9 at
// R = 3 and 49 at R = 7.
//
// Below the top level r is ODD (AbsorbShape splits m = r * 2^e), so the
// reachable radices there are 3 at B = 4 and {3,5,7} at B = 8.  The level
// arena's top routes on its whole digit only when that digit is NOT a power of
// two, so of the even radices only 6 reaches here from it; the dispatch below
// covers every r in [2, 7], so any whole-digit radix has a kernel.  R = 3 is
// the one that matters at the default branching factor.  There,
// specialization gains a few percent at shallow depths, breaks even around
// S = 7, and loses at S = 8 -- which is where 9 + 3*S indices stop fitting in
// 32 zmm and the allocator's spill code is slower than the stack-array loop.
// R = 5 and R = 7 already exhaust the register file on the R*R term alone and
// show no difference either way.  So the cap is the last depth at which
// specialization wins, not the last that fits.
inline constexpr size_t kMaxRadixStashBuckets = 6;

template <unsigned R, bool CheckOverflow, bool BlankFirst = false,
          typename Finalizer = RadixIdentityOutput>
inline bool MergeSplitRadixStashByStash(uint8_t* const* buckets,
                                        uint64_t* const* bucket_masks,
                                        size_t lines, size_t digit_line_offset,
                                        size_t digit_bits,
                                        ResidualStash& stash,
                                        Finalizer&& finish = {}) {
  const auto run = [&](auto depth) {
    return MergeSplitRadixStashFixed<R, decltype(depth)::value, CheckOverflow,
                                     BlankFirst>(
        buckets, bucket_masks, lines, digit_line_offset, digit_bits, stash,
        finish);
  };
  return DispatchStashDepth<static_cast<int>(kMaxRadixStashBuckets)>(
      stash.num_buckets, run, [&] {
        return run(std::integral_constant<int, kDynamicStashBuckets>{});
      });
}

template <bool CheckOverflow = false, bool BlankFirst = false,
          typename Finalizer = RadixIdentityOutput>
inline bool MergeSplitRadixStash(uint8_t* const* buckets,
                                 uint64_t* const* bucket_masks, unsigned r,
                                 size_t lines, size_t digit_line_offset,
                                 size_t digit_bits, ResidualStash& stash,
                                 Finalizer&& finish = {}) {
  assert(r >= 2 && r <= kMaxRadix);
  switch (r) {
    case 2:
      return MergeSplitRadixStashByStash<2, CheckOverflow, BlankFirst>(
          buckets, bucket_masks, lines, digit_line_offset, digit_bits,
          stash, finish);
    case 3:
      return MergeSplitRadixStashByStash<3, CheckOverflow, BlankFirst>(
          buckets, bucket_masks, lines, digit_line_offset, digit_bits,
          stash, finish);
    case 4:
      return MergeSplitRadixStashByStash<4, CheckOverflow, BlankFirst>(
          buckets, bucket_masks, lines, digit_line_offset, digit_bits,
          stash, finish);
    case 5:
      return MergeSplitRadixStashByStash<5, CheckOverflow, BlankFirst>(
          buckets, bucket_masks, lines, digit_line_offset, digit_bits,
          stash, finish);
    case 6:
      return MergeSplitRadixStashByStash<6, CheckOverflow, BlankFirst>(
          buckets, bucket_masks, lines, digit_line_offset, digit_bits,
          stash, finish);
    default:
      return MergeSplitRadixStashByStash<7, CheckOverflow, BlankFirst>(
          buckets, bucket_masks, lines, digit_line_offset, digit_bits,
          stash, finish);
  }
}

// The radix-r pass over t = r * 2^block_bits buckets: one radix MergeSplit
// per stride-2^block_bits tuple.  Buckets [begin, end) of the block index p
// only, so disjoint ranges touch disjoint buckets; running them concurrently
// also needs a stash per range, since every tuple sheds into `stash`.
//
// The radix pass is the LAST routing step of a mixed-radix rebuild, so the
// whole tag is dead the moment it has read the digit line: it moves payload
// lines only (the digit line itself is loaded explicitly and never stored).
// BlankFirst: block 0 is publicly empty (MergeSplitRadixStashFixed).
template <bool CheckOverflow = false, bool BlankFirst = false>
inline bool RadixPassStashRange(TableView t, unsigned block_bits, unsigned r,
                                ResidualStash& stash, size_t begin,
                                size_t end) {
  if (r <= 1) return true;
  const size_t block = size_t{1} << block_bits;
  assert(t.num_buckets == block * r);
  const size_t bucket_bytes = t.layout.BucketBytes();
  const size_t digit_line = t.layout.DigitLine();
  const size_t lines = t.layout.PayloadLines();
  uint8_t* bptr[kMaxRadix];
  uint64_t* mptr[kMaxRadix];
  for (size_t p = begin; p < end; ++p) {
    for (unsigned q = 0; q < r; ++q) {
      bptr[q] = t.data + (q * block + p) * bucket_bytes;
      mptr[q] = &t.masks[q * block + p];
    }
    if (!MergeSplitRadixStash<CheckOverflow, BlankFirst>(
            bptr, mptr, r, lines, digit_line, t.layout.digit_bits, stash)) {
      return false;
    }
  }
  return true;
}

template <bool CheckOverflow = false>
inline bool RadixPassStash(TableView t, unsigned block_bits, unsigned r,
                           ResidualStash& stash) {
  return RadixPassStashRange<CheckOverflow>(
      t, block_bits, r, stash, 0, size_t{1} << block_bits);
}

inline TableView SubView(TableView t, size_t bucket_begin,
                         size_t num_buckets) {
  return TableView{t.layout, num_buckets,
                   t.data + bucket_begin * t.layout.BucketBytes(),
                   t.masks + bucket_begin};
}

}  // namespace byteslice
}  // namespace microram
