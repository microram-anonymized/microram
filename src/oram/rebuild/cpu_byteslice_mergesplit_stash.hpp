#pragma once

// MergeSplit at load 0.5: the pair kernel that sheds into a stash, and the
// fused two-level "quad" that halves its memory traffic.
//
// MergeSplitPairStash is MergeSplitPair with one addition: a direction that
// would exceed 64 entries sheds its surplus into the level's residual stash
// instead of failing.  Only the SECOND bucket's entries ever move, so the
// residual is always a suffix of second's survivors and the stash merge
// collapses the same way the MergeSplit itself does -- every shed byte lands
// at a position fixed by the direction masks, so it is one more VPERMT2B per
// byte line per stash bucket, on an index built once.
//
// THE QUAD.  One MergeSplit costs, per byte line and per bucket routed, one
// 512-bit load, one permute and one store.  The permutes are irreducible --
// every routed byte really is permuted once per level -- but the loads and
// stores are not.  Butterfly levels b and b+1 touch the SAME four buckets
// {first + m*2^bit : m in [0,4)}, so holding all four byte lines in registers
// and running both levels before writing back keeps the permute count and
// halves the traffic.  It stops at two levels: three levels over eight buckets
// needs 24 index registers plus 8 data plus scratch, spills seven zmm per
// iteration, and is no faster -- at two levels the kernel is already close to
// permute-throughput bound.
//
// Only the LAST level's permutes are masked, which is what keeps the kmask
// budget at 4 + 2*S instead of 8 + 2*S: every byte the intermediate level puts
// in a real slot is either overwritten or re-permuted by the second level, so
// zeroing the free slots in between buys nothing.
//
// OBLIVIOUSNESS.  Every MergeSplit executes the identical instruction sequence
// whether or not it overflowed.  Residual counts live only in scalar
// registers, kmasks and permutation-index vectors; the stash bucket lines are
// loaded and stored unconditionally; the only branches are on public
// quantities (the stash bucket count, the radix).  This matters more at load
// 0.5 than at 0.25, because here the overflow pattern is not negligible and
// the number of REAL entries routed is secret -- miss-inserted slots are
// dummies -- so branching on the residual count would leak the real count.
// In checked mode the one data-dependent branch is the stash-capacity abort
// itself, which fires with probability <= 2^-64 per rebuild.

#include <immintrin.h>

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <type_traits>
#include <utility>

#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/rebuild/cpu_byteslice_mergesplit.hpp"
#include "src/oram/rebuild/cpu_byteslice_residual_stash.hpp"

namespace microram {
namespace byteslice {

// "Take the stash bucket count from the plan at run time"; a non-negative
// StashBuckets is the exact compile-time count, and 0 means the caller passed
// a zero-capacity stash, i.e. there is no residual path at all.
inline constexpr int kDynamicStashBuckets = -1;

// Turns the run-time (public) stash bucket count into a compile-time one:
// calls `fn(std::integral_constant<int, S>{})` for the S that matches, and
// `fallback()` when the count is deeper than MaxDepth.
//
// WHY EVERY DEPTH AND NOT JUST THE SHALLOW ONES.  PlanStashBuckets takes the
// MAX over butterfly levels and hands that one number to every stash in the
// engine, so a configuration whose deepest level needs S buckets runs EVERY
// MergeSplit at depth S.  A dispatch that stops early therefore does not slow
// down the one level that overflowed -- it drops the whole butterfly, at every
// level, onto the unspecialized path.  That makes the dispatch table a CLIFF,
// and the schedule walks right off it: S reaches 3 at ~2^30 entries (load 0.5,
// 2^32-access lifetime), 4 at 2^32, and 8 at 2^34, and it reaches 3 as early
// as 2^29 on a 2^48-access lifetime.  The marginal cost of one more stash
// stream is small next to the cost of leaving the specialized kernels, so a
// table that stopped at a shallow depth would make the first unspecialized
// depth far slower than the stash itself explains.
//
// ResidualStash::masks is kMaxResidualStashBuckets long, so at that MaxDepth
// the fallback is unreachable; kernels that have no valid fallback (the fused
// quad's kernel is instantiated per depth and has no dynamic form) rely on
// exactly that.
//
// Not every kernel wants the full range -- see kMaxRadixStashBuckets, where the
// dynamic form is the same kernel with a runtime trip count rather than a cliff
// and the specialized range stops at 6.
template <int MaxDepth, typename Fn, typename Fallback>
inline bool DispatchStashDepth(size_t stash_buckets, Fn&& fn,
                               Fallback&& fallback) {
  static_assert(MaxDepth >= 0, "MaxDepth must be a real depth");
  if (stash_buckets == static_cast<size_t>(MaxDepth)) {
    return fn(std::integral_constant<int, MaxDepth>{});
  }
  if constexpr (MaxDepth == 0) {
    return fallback();
  } else {
    return DispatchStashDepth<MaxDepth - 1>(stash_buckets, fn, fallback);
  }
}

// The byte-line loop, specialized on the (public) stash bucket count so the
// permute indices and kmasks stay in registers across all routed lines.
// At StashBuckets = 0 the stash load/permute/store vanish and the loop is the
// bare two-stream MergeSplit -- see MergeSplitPairStash for when that applies.
template <int StashBuckets>
inline void MergeSplitPairStashLines(uint8_t* first, uint8_t* second,
                                     size_t lines, __m512i idx_zero,
                                     __mmask64 keep_zero, __m512i idx_one,
                                     __mmask64 keep_one, ResidualStash& stash,
                                     const StashPermutePlan& plan) {
  constexpr int kSlots = StashBuckets > 0 ? StashBuckets : 1;
  uint8_t* stash_ptr[kSlots];
  __m512i stash_idx[kSlots];
  __mmask64 stash_keep[kSlots];
  for (int b = 0; b < StashBuckets; ++b) {
    stash_ptr[b] = stash.Bucket(static_cast<size_t>(b));
    stash_idx[b] = plan.idx[b];
    stash_keep[b] = plan.keep[b];
  }
  size_t offset = 0;
  for (size_t line = 0; line < lines; ++line) {
    const __m512i first_line =
        _mm512_load_si512(reinterpret_cast<const void*>(first));
    const __m512i second_line =
        _mm512_load_si512(reinterpret_cast<const void*>(second));
    if constexpr (StashBuckets == kDynamicStashBuckets) {
      ApplyStashPermuteLineAtOffset(stash, plan, offset, second_line);
    } else {
      for (int b = 0; b < StashBuckets; ++b) {
        const __m512i line_b =
            _mm512_load_si512(reinterpret_cast<const void*>(stash_ptr[b]));
        _mm512_store_si512(
            reinterpret_cast<void*>(stash_ptr[b]),
            _mm512_maskz_permutex2var_epi8(stash_keep[b], line_b, stash_idx[b],
                                           second_line));
        stash_ptr[b] += kBucketCapacity;
      }
    }
    _mm512_store_si512(reinterpret_cast<void*>(first),
                       _mm512_maskz_permutex2var_epi8(keep_zero, first_line,
                                                      idx_zero, second_line));
    _mm512_store_si512(reinterpret_cast<void*>(second),
                       _mm512_maskz_permutex2var_epi8(keep_one, first_line,
                                                      idx_one, second_line));
    first += kBucketCapacity;
    second += kBucketCapacity;
    offset += kBucketCapacity;
  }
}

// MergeSplit at load 0.5: identical to MergeSplitPair, but a direction that
// exceeds 64 entries sheds its surplus into `stash` instead of failing.
// Only SECOND's entries move (FIRST's stay in their slots), so the residual
// of direction X is exactly the set of SECOND's direction-X slots that did
// not fit.  The stash merge executes unconditionally with the same
// instruction sequence whether the residual is empty or not.  With
// CheckOverflow=true, returns false if the stash itself would exceed capacity
// (probability <= 2^-64 per rebuild by sizing).  The default unchecked mode
// relies on that sizing.
//
// A zero-capacity stash (num_buckets == 0) with CheckOverflow=true is the
// load-0.25 contract: any surplus at all makes the MergeSplit fail, and the
// byte-line loop drops the stash stream entirely (one load, one permute and
// one store per line less).  That is the form for a table routed at load
// 0.25, where a shed is a rebuild failure rather than a residual.
template <bool CheckOverflow = false>
inline bool MergeSplitPairStash(uint8_t* first, uint8_t* second,
                                uint64_t* first_mask, uint64_t* second_mask,
                                size_t lines, size_t tag_line, unsigned bit,
                                ResidualStash& stash) {
  const uint64_t first_real = *first_mask;
  const uint64_t second_real = *second_mask;
  const PairMergePlan pair = PlanMergePairByTagBit(
      first, second, first_real, second_real, tag_line, bit);

  // A zero-capacity stash only makes sense in checked mode; unchecked
  // it would silently drop the surplus instead of shedding it.
  assert(CheckOverflow || stash.num_buckets > 0);
  if constexpr (CheckOverflow) {
    if (stash.Count() + Popcount64(pair.residual) > stash.Capacity()) {
      return false;
    }
  }
  StashPermutePlan plan;
  PlanStashMergePermute(stash, pair.residual, &plan);

  const __mmask64 keep_zero = _cvtu64_mask64(pair.new_a);
  const __mmask64 keep_one = _cvtu64_mask64(pair.new_b);

  // The stash bucket count is public, so dispatching on it leaks nothing.
  // Specialized to the full schedule range: the pair kernel needs 2 + S
  // permute indices, so even S = 8 costs one spill against the dynamic form's
  // per-line reload of the whole plan.
  const auto run = [&](auto depth) {
    MergeSplitPairStashLines<decltype(depth)::value>(
        first, second, lines, pair.idx_a, keep_zero, pair.idx_b, keep_one,
        stash, plan);
    return true;
  };
  DispatchStashDepth<static_cast<int>(kMaxResidualStashBuckets)>(
      plan.num_buckets, run, [&] {
        return run(std::integral_constant<int, kDynamicStashBuckets>{});
      });

  *first_mask = pair.new_a;
  *second_mask = pair.new_b;
  return true;
}

// ---------------------------------------------------------------------------
// Fused two-level MergeSplit ("quad")
// ---------------------------------------------------------------------------
//
// One MergeSplit costs, per byte line and per bucket routed, one 512-bit load,
// one VPERMT2B and one 512-bit store (plus the same three per stash bucket).
// The permutes are irreducible -- every routed byte really is permuted once
// per level -- but the loads and stores are not: butterfly levels b and b+1
// touch the same FOUR buckets {p, p+2^b, p+2^(b+1), p+3*2^b}, so holding all
// four byte lines in registers and running both levels before writing back
// halves the memory traffic.  Per byte line the quad does 4 + 2*S loads,
// 8 + 4*S permutes and 4 + 2*S stores for 4 buckets x 2 levels, against
// 2*(2 + S) / 2*(2 + S) / 2*(2 + S) for the same work as two separate
// MergeSplits: same permute count, half the loads and stores.
//
// Only the LAST level's permutes are masked.  Every byte that lands in a real
// output slot comes from a slot that was real on entry (a merge index only
// ever sources real slots, and the kept slots are the destination's own real
// ones), so the intermediate maskz is redundant: the final maskz zeroes every
// dummy slot anyway and the stored bytes are IDENTICAL to two unfused levels.
// That is what keeps the kmask count at 4 + 2*S instead of 8 + 2*S -- the
// difference between fitting k1..k7 and spilling.
//
// Register budget: 8 data indices + 4*S stash indices + ~8 transient
// data/scratch registers, i.e. ~16 / ~21 / ~26 zmm at S = 0 / 1 / 2 out of 32.
// S = 3 is the first depth that does not fit -- the generated inner loop spills
// two zmm -- and each depth past it spills several more (8 at S = 4, 33 at
// S = 8).  Three LEVELS over eight buckets is a different question, also
// answered no: 24 index registers plus 8 data plus scratch = 33+, spills seven
// zmm per iteration, and is no faster, because at two levels the kernel is
// already close to permute-throughput bound.
//
// kMaxQuadStashBuckets is where the fusion stops paying for those spills, and
// it is NOT the last depth that fits in registers.  The alternative is the
// unfused pair pass, which doubles the loads and stores and pays its own
// deep-stash cost on top, so the fused kernel keeps winning well past its own
// spill threshold; its advantage narrows as S grows and is roughly even at the
// deepest stash.  So the cap is simply the deepest stash that can exist, and
// one invariant ("every reachable depth is fused") holds.  The constant stays
// a named constant because that trade-off is empirical -- it moves with the
// entry width and the microarchitecture -- and because the unfused path has
// to stay reachable anyway: mismatched stash depths take it.
inline constexpr size_t kMaxQuadStashBuckets = kMaxResidualStashBuckets;

// Two-source variant of PlanStashMergePermute: the two MergeSplits of one
// butterfly level shed into the SAME level stash, so their residuals are
// merged with one permute each per stash bucket, chained.  The keep mask goes
// on the first permute of the chain and carries the final occupancy, exactly
// as in MergeSplitRadixStashFixed.
inline void PlanStashMergePermute2(ResidualStash& stash, size_t stash_buckets,
                                   uint64_t residual_a, uint64_t residual_b,
                                   __m512i (*idx)[2], __mmask64* keep) {
  uint64_t pending[2] = {residual_a, residual_b};
  for (size_t b = 0; b < stash_buckets; ++b) {
    const uint64_t old_mask = stash.masks[b];
    uint64_t available = ~old_mask;
    unsigned free_count =
        static_cast<unsigned>(kBucketCapacity) - Popcount64(old_mask);
    uint64_t filled = old_mask;
    for (int i = 0; i < 2; ++i) {
      const unsigned take = std::min(Popcount64(pending[i]), free_count);
      const uint64_t src = _pdep_u64(LowMask64(take), pending[i]);
      const uint64_t dest = _pdep_u64(LowMask64(take), available);
      idx[b][i] = BuildMergeIndex(dest, src);
      available &= ~dest;
      free_count -= take;
      filled |= dest;
      pending[i] &= ~src;
    }
    keep[b] = _cvtu64_mask64(filled);
    stash.masks[b] = filled;
  }
}

// WHERE a quad's four buckets are, and how much of each entry it moves.
//
// The main butterfly's table is indexed BY the tag bit it routes on, so both
// follow from `bit` -- that is ButterflyQuadShape, and it is what every
// butterfly call site passes.
struct QuadShape {
  size_t step = 1;   // buckets between consecutive quad members
  size_t lines = 0;  // byte lines to move
};

inline QuadShape ButterflyQuadShape(const Layout& layout, unsigned bit) {
  return QuadShape{size_t{1} << bit, layout.RoutedLines(bit + 1)};
}

// Routes butterfly bits `bit` and `bit + 1` over the four buckets
// {first + m * shape.step : m in [0, 4)} in one pass: bit pairs (0,1) and
// (2,3), bit+1 pairs (0,2) and (1,3).  `data`/`masks` point at bucket m = 0.
// Level `bit` sheds into stash_lo, level `bit + 1` into stash_hi (the
// per-level stashes).  They must be DISTINCT objects unless both have zero
// capacity: the two stash merge plans below are computed from the same
// starting masks, so an aliased pair with room would plan both levels' sheds
// into the same free slots and the second permute would overwrite the first
// -- silently, since each level's capacity check passes on its own (asserted
// below).  Two views of one buffer are illegal for the same reason.  The only
// aliasing caller is the residual range table's zero-capacity `none, none`,
// where nothing can be shed at all.
// Output bytes and masks are identical to running the four MergeSplits
// separately; only the order residuals enter a level stash differs, and a
// stash is a set.
template <int StashBuckets, bool CheckOverflow>
inline bool MergeSplitQuadStashFixed(uint8_t* data, uint64_t* masks,
                                     size_t bucket_bytes, const Layout& layout,
                                     unsigned bit, const QuadShape& shape,
                                     ResidualStash& stash_lo,
                                     ResidualStash& stash_hi) {
  constexpr int kSlots = StashBuckets > 0 ? StashBuckets : 1;
  const size_t step = shape.step;
  uint8_t* p[4];
  uint64_t real[4];
  for (int m = 0; m < 4; ++m) {
    p[m] = data + static_cast<size_t>(m) * step * bucket_bytes;
    real[m] = masks[static_cast<size_t>(m) * step];
  }
  const size_t off_lo = layout.TagLine(bit) * kBucketCapacity;
  const size_t off_hi = layout.TagLine(bit + 1) * kBucketCapacity;
  const size_t lines = shape.lines;
  const __m512i probe_lo =
      _mm512_set1_epi8(static_cast<char>(uint8_t{1} << (bit & 7)));
  const __m512i probe_hi =
      _mm512_set1_epi8(static_cast<char>(uint8_t{1} << ((bit + 1) & 7)));

  // ---- level `bit`: split on the tag line, plan both pairs ----
  __m512i tag_lo[4];
  uint64_t one[4];
  for (int m = 0; m < 4; ++m) {
    tag_lo[m] = _mm512_load_si512(reinterpret_cast<const void*>(p[m] + off_lo));
    one[m] = core::obliTestMask8(tag_lo[m], probe_lo) & real[m];
  }
  const PairMergePlan a01 = PlanMergePair(real[0], real[1], one[0], one[1]);
  const PairMergePlan a23 = PlanMergePair(real[2], real[3], one[2], one[3]);
  const __m512i idx0[4] = {a01.idx_a, a01.idx_b, a23.idx_a, a23.idx_b};
  const uint64_t mid[4] = {a01.new_a, a01.new_b, a23.new_a, a23.new_b};

  // ---- level `bit + 1`: the tag line AFTER level `bit` has permuted it ----
  // Cheaper to replay the permute in registers than to route the tag line
  // early and reload it; the intermediate garbage in dummy slots is filtered
  // by the AND with `mid`.
  __m512i tag_hi[4];
  if (off_hi == off_lo) {
    tag_hi[0] = _mm512_permutex2var_epi8(tag_lo[0], idx0[0], tag_lo[1]);
    tag_hi[1] = _mm512_permutex2var_epi8(tag_lo[0], idx0[1], tag_lo[1]);
    tag_hi[2] = _mm512_permutex2var_epi8(tag_lo[2], idx0[2], tag_lo[3]);
    tag_hi[3] = _mm512_permutex2var_epi8(tag_lo[2], idx0[3], tag_lo[3]);
  } else {
    __m512i raw[4];
    for (int m = 0; m < 4; ++m) {
      raw[m] = _mm512_load_si512(reinterpret_cast<const void*>(p[m] + off_hi));
    }
    tag_hi[0] = _mm512_permutex2var_epi8(raw[0], idx0[0], raw[1]);
    tag_hi[1] = _mm512_permutex2var_epi8(raw[0], idx0[1], raw[1]);
    tag_hi[2] = _mm512_permutex2var_epi8(raw[2], idx0[2], raw[3]);
    tag_hi[3] = _mm512_permutex2var_epi8(raw[2], idx0[3], raw[3]);
  }
  uint64_t one_hi[4];
  for (int m = 0; m < 4; ++m) {
    one_hi[m] = core::obliTestMask8(tag_hi[m], probe_hi) & mid[m];
  }
  const PairMergePlan b02 = PlanMergePair(mid[0], mid[2], one_hi[0], one_hi[2]);
  const PairMergePlan b13 = PlanMergePair(mid[1], mid[3], one_hi[1], one_hi[3]);
  const __m512i idx1[4] = {b02.idx_a, b13.idx_a, b02.idx_b, b13.idx_b};
  const uint64_t out[4] = {b02.new_a, b13.new_a, b02.new_b, b13.new_b};
  __mmask64 keep[4];
  for (int m = 0; m < 4; ++m) keep[m] = _cvtu64_mask64(out[m]);

  // ---- residual plans ----
  // A zero-capacity stash only makes sense in checked mode; unchecked it
  // would silently drop the surplus instead of shedding it.
  assert(CheckOverflow ||
         (stash_lo.num_buckets > 0 && stash_hi.num_buckets > 0));
  // Distinct stashes, or nothing to shed into (see the header comment).
  assert(&stash_lo != &stash_hi || stash_lo.Capacity() == 0);
  __m512i sidx_lo[kSlots][2];
  __m512i sidx_hi[kSlots][2];
  __mmask64 skeep_lo[kSlots];
  __mmask64 skeep_hi[kSlots];
  uint8_t* sp_lo[kSlots];
  uint8_t* sp_hi[kSlots];
  if constexpr (CheckOverflow) {
    const unsigned shed_lo =
        Popcount64(a01.residual) + Popcount64(a23.residual);
    const unsigned shed_hi =
        Popcount64(b02.residual) + Popcount64(b13.residual);
    if (stash_lo.Count() + shed_lo > stash_lo.Capacity() ||
        stash_hi.Count() + shed_hi > stash_hi.Capacity()) {
      return false;
    }
  }
  if constexpr (StashBuckets > 0) {
    PlanStashMergePermute2(stash_lo, StashBuckets, a01.residual, a23.residual,
                           sidx_lo, skeep_lo);
    PlanStashMergePermute2(stash_hi, StashBuckets, b02.residual, b13.residual,
                           sidx_hi, skeep_hi);
    for (int b = 0; b < StashBuckets; ++b) {
      sp_lo[b] = stash_lo.Bucket(static_cast<size_t>(b));
      sp_hi[b] = stash_hi.Bucket(static_cast<size_t>(b));
    }
  }

  // ---- byte-line loop ----
  uint8_t* q0 = p[0];
  uint8_t* q1 = p[1];
  uint8_t* q2 = p[2];
  uint8_t* q3 = p[3];
  for (size_t line = 0; line < lines; ++line) {
    const __m512i in0 = _mm512_load_si512(reinterpret_cast<const void*>(q0));
    const __m512i in1 = _mm512_load_si512(reinterpret_cast<const void*>(q1));
    const __m512i in2 = _mm512_load_si512(reinterpret_cast<const void*>(q2));
    const __m512i in3 = _mm512_load_si512(reinterpret_cast<const void*>(q3));
    // Level `bit` sheds out of buckets 1 and 3 (the "second" of each pair).
    if constexpr (StashBuckets > 0) {
      for (int b = 0; b < StashBuckets; ++b) {
        __m512i acc = _mm512_maskz_permutex2var_epi8(
            skeep_lo[b],
            _mm512_load_si512(reinterpret_cast<const void*>(sp_lo[b])),
            sidx_lo[b][0], in1);
        acc = _mm512_permutex2var_epi8(acc, sidx_lo[b][1], in3);
        _mm512_store_si512(reinterpret_cast<void*>(sp_lo[b]), acc);
        sp_lo[b] += kBucketCapacity;
      }
    }
    const __m512i t0 = _mm512_permutex2var_epi8(in0, idx0[0], in1);
    const __m512i t1 = _mm512_permutex2var_epi8(in0, idx0[1], in1);
    const __m512i t2 = _mm512_permutex2var_epi8(in2, idx0[2], in3);
    const __m512i t3 = _mm512_permutex2var_epi8(in2, idx0[3], in3);
    // Level `bit + 1` sheds out of buckets 2 and 3 of the level-`bit` output.
    if constexpr (StashBuckets > 0) {
      for (int b = 0; b < StashBuckets; ++b) {
        __m512i acc = _mm512_maskz_permutex2var_epi8(
            skeep_hi[b],
            _mm512_load_si512(reinterpret_cast<const void*>(sp_hi[b])),
            sidx_hi[b][0], t2);
        acc = _mm512_permutex2var_epi8(acc, sidx_hi[b][1], t3);
        _mm512_store_si512(reinterpret_cast<void*>(sp_hi[b]), acc);
        sp_hi[b] += kBucketCapacity;
      }
    }
    _mm512_store_si512(
        reinterpret_cast<void*>(q0),
        _mm512_maskz_permutex2var_epi8(keep[0], t0, idx1[0], t2));
    _mm512_store_si512(
        reinterpret_cast<void*>(q1),
        _mm512_maskz_permutex2var_epi8(keep[1], t1, idx1[1], t3));
    _mm512_store_si512(
        reinterpret_cast<void*>(q2),
        _mm512_maskz_permutex2var_epi8(keep[2], t0, idx1[2], t2));
    _mm512_store_si512(
        reinterpret_cast<void*>(q3),
        _mm512_maskz_permutex2var_epi8(keep[3], t1, idx1[3], t3));
    q0 += kBucketCapacity;
    q1 += kBucketCapacity;
    q2 += kBucketCapacity;
    q3 += kBucketCapacity;
  }

  for (int m = 0; m < 4; ++m) {
    masks[static_cast<size_t>(m) * step] = out[m];
  }
  return true;
}

// Two ordinary MergeSplitPairStash passes over the quad's four buckets: what
// the fused kernel falls back to above kMaxQuadStashBuckets.  Byte-for-byte
// the same output; only the order residuals enter a level stash differs, and a
// stash is a set.
template <bool CheckOverflow = false>
inline bool MergeSplitQuadStashUnfused(uint8_t* data, uint64_t* masks,
                                       size_t bucket_bytes,
                                       const Layout& layout, unsigned bit,
                                       ResidualStash& stash_lo,
                                       ResidualStash& stash_hi) {
  const size_t step = size_t{1} << bit;
  ResidualStash* stash[2] = {&stash_lo, &stash_hi};
  for (unsigned lev = 0; lev < 2; ++lev) {
    const unsigned b = bit + lev;
    const size_t half = size_t{1} << lev;
    const size_t lines = layout.RoutedLines(b);
    const size_t tag_line = layout.TagLine(b);
    for (size_t m = 0; m < 4; ++m) {
      if (m & half) continue;
      const size_t i = m * step;
      const size_t j = (m | half) * step;
      if (!MergeSplitPairStash<CheckOverflow>(
              data + i * bucket_bytes, data + j * bucket_bytes, &masks[i],
              &masks[j], lines, tag_line, b, *stash[lev])) {
        return false;
      }
    }
  }
  return true;
}

// Dispatches the quad on the (public) stash bucket count so the permutation
// indices stay in registers; falls back to two ordinary MergeSplit passes when
// the stash is deeper than kMaxQuadStashBuckets, or when the two levels'
// stashes have different depths (the hierarchy always sizes them alike).
//
// That fallback is a cliff, not a taper -- it gives up the fusion, i.e. twice
// the loads and stores, ON TOP of whatever the deeper stash itself costs -- so
// the cap belongs where the fused form stops winning, which is an empirical
// question and not the register count.  See kMaxQuadStashBuckets.
template <bool CheckOverflow = false>
inline bool MergeSplitQuadStash(uint8_t* data, uint64_t* masks,
                                size_t bucket_bytes, const Layout& layout,
                                unsigned bit, ResidualStash& stash_lo,
                                ResidualStash& stash_hi) {
  const auto unfused = [&] {
    return MergeSplitQuadStashUnfused<CheckOverflow>(
        data, masks, bucket_bytes, layout, bit, stash_lo, stash_hi);
  };
  if (stash_lo.num_buckets != stash_hi.num_buckets) return unfused();
  return DispatchStashDepth<static_cast<int>(kMaxQuadStashBuckets)>(
      stash_lo.num_buckets,
      [&](auto depth) {
        return MergeSplitQuadStashFixed<decltype(depth)::value, CheckOverflow>(
            data, masks, bucket_bytes, layout, bit,
            ButterflyQuadShape(layout, bit), stash_lo, stash_hi);
      },
      unfused);
}

// PlanStashMergePermute for several sheds of ONE source line -- the
// directions of one fixed-merge source bucket -- so that one permute per
// stash bucket and line appends them all.  Stash bucket by bucket, shed k
// takes its lowest pending slots into the lowest slots sheds 0..k-1 left
// free, which is where appending the sheds one after another puts them:
// either way shed k's share of bucket b is bounded by what it still holds and
// by what the earlier sheds left of b.  The rounds claim disjoint slots, so
// their indexes layer (BuildMergeIndexOnto); at count 1 this is
// PlanStashMergePermute.  `pending` is consumed.
inline void PlanStashMergePermuteRounds(ResidualStash& stash,
                                        uint64_t* pending, size_t count,
                                        StashPermutePlan* plan) {
  plan->num_buckets = stash.num_buckets;
  for (size_t b = 0; b < stash.num_buckets; ++b) {
    uint64_t filled = stash.masks[b];
    __m512i idx = IotaBytes();
    for (size_t k = 0; k < count; ++k) {
      const unsigned free_slots =
          static_cast<unsigned>(kBucketCapacity) - Popcount64(filled);
      const unsigned take = std::min(Popcount64(pending[k]), free_slots);
      const uint64_t take_src = _pdep_u64(LowMask64(take), pending[k]);
      const uint64_t dest = _pdep_u64(LowMask64(take), ~filled);
      idx = BuildMergeIndexOnto(idx, dest, take_src);
      filled |= dest;
      pending[k] &= ~take_src;
    }
    plan->idx[b] = idx;
    plan->keep[b] = _cvtu64_mask64(filled);
    stash.masks[b] = filled;
  }
}

// Merges SRC's entries into DST's free slots, shedding any surplus into the
// stash.  Used for the 0.25 -> 0.5 contraction of small levels (two source
// buckets merged into one arena bucket) and for the final fold of the
// fixed-level rebuild (lower-half bucket folded into its upper-half buddy).
// SRC's bytes are left in place -- hence `const`, which is what lets a caller
// whose source is another owner's IMMUTABLE published table hold it as one --
// but its occupancy mask is cleared, and that mask is the CALLER's copy (see
// MergeFixedLevelSourcesRange, which passes one per direction).
template <bool CheckOverflow = false>
inline bool MergeBucketIntoWithStash(uint8_t* dst, const uint8_t* src,
                                     uint64_t* dst_mask, uint64_t* src_mask,
                                     size_t lines, ResidualStash& stash) {
  const uint64_t dst_real = *dst_mask;
  const uint64_t src_real = *src_mask;
  const unsigned free_slots =
      static_cast<unsigned>(kBucketCapacity) - Popcount64(dst_real);
  const unsigned allocated = std::min(Popcount64(src_real), free_slots);
  const uint64_t used = _pdep_u64(LowMask64(allocated), ~dst_real);
  const uint64_t taken = _pdep_u64(LowMask64(allocated), src_real);
  const uint64_t residual_src = src_real & ~taken;
  // A zero-capacity stash only makes sense in checked mode; unchecked
  // it would silently drop the surplus instead of shedding it.
  assert(CheckOverflow || stash.num_buckets > 0);
  if constexpr (CheckOverflow) {
    if (stash.Count() + Popcount64(residual_src) > stash.Capacity()) {
      return false;
    }
  }
  StashPermutePlan plan;
  PlanStashMergePermute(stash, residual_src, &plan);
  const __m512i idx = BuildMergeIndex(used, taken);
  const __mmask64 keep = _cvtu64_mask64(dst_real | used);
  for (size_t line = 0; line < lines; ++line) {
    const size_t offset = line * kBucketCapacity;
    uint8_t* dst_ptr = dst + offset;
    const __m512i dst_line =
        _mm512_load_si512(reinterpret_cast<const void*>(dst_ptr));
    const __m512i src_line =
        _mm512_load_si512(reinterpret_cast<const void*>(src + offset));
    ApplyStashPermuteLineAtOffset(stash, plan, offset, src_line);
    _mm512_store_si512(
        reinterpret_cast<void*>(dst_ptr),
        _mm512_maskz_permutex2var_epi8(keep, dst_line, idx, src_line));
  }
  *dst_mask = dst_real | used;
  *src_mask = 0;
  return true;
}

// Merges the real entries of one byte-sliced bucket (e.g. a worker thread's
// residual-stash bucket) into the stash.  Used to combine per-thread stashes
// after a parallel rebuild phase; the source bucket's bytes are untouched.
//
// CheckOverflow has NO DEFAULT: this fold IS the aggregate capacity check.
// Each worker routed against a private stash of the full per-level capacity,
// so nothing below has bounded their SUM, and an unchecked fold returns true
// having dropped whatever did not fit -- the records then exist in neither the
// main table nor the republished tier.  A caller that has proved the sum fits
// may still spell `<false>`; it may not leave it unsaid.
template <bool CheckOverflow>
inline bool MergeBucketIntoResidualStash(ResidualStash& stash,
                                         const uint8_t* bucket,
                                         uint64_t bucket_mask, size_t lines) {
  if constexpr (CheckOverflow) {
    if (stash.Count() + Popcount64(bucket_mask) > stash.Capacity()) {
      return false;
    }
  }
  StashPermutePlan plan;
  PlanStashMergePermute(stash, bucket_mask, &plan);
  for (size_t line = 0; line < lines; ++line) {
    const size_t offset = line * kBucketCapacity;
    ApplyStashPermuteLineAtOffset(
        stash, plan, offset,
        _mm512_load_si512(reinterpret_cast<const void*>(bucket + offset)));
  }
  return true;
}

}  // namespace byteslice
}  // namespace microram
