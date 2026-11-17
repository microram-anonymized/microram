#pragma once

// THE MERGE PLANNERS: one level-arena merge, cut into three phases.  A merge
// at a level combines A, the OLDER operand (the level's current partial table,
// or at the top its whole current table), with B, the incoming CARRY (the
// fresher table the level below produced; DESIGN.md "Carries and
// preparation"), into an output C under a fresh index map.  The planners emit
// the shared rebuild kernels' subtask stream (subtask_plan.hpp); what this
// file decides is WHERE the cut between "work that needs the incoming carry"
// and "work that does not" falls, because in this design the two can run at
// different times, on different threads, arbitrarily far apart.
//
//   1. PREPARE   copy, re-tag and route every older source block.  Touches no
//                carry data at all, so it may run while the carry is still
//                being produced -- all it needs is the destination slot.
//   2. INSTALL   put the fresh carry into the output's first U buckets.  Three
//                flavours: a fused copy-and-re-tag (a sparse carry; a plain
//                copy at a binary level's digit 1), the dense prefix builder
//                (level 1), and -- at the TOP -- nothing at all, because its
//                sweep reads the carry where it lies.  A directly built
//                level one (PlanBuildDenseDirect) builds B into its own U
//                buckets instead, or into the output at digit 1, and its
//                finish is the separated one.
//   3. FINISH    block 0's deduplicating cross levels, the ordered radix pass,
//                and the residual second chances; at the top, the fixed
//                merge's sweep, its pass, and the tombstone drop.
//
// SEPARATED ORDINARY PASSES complete A's route in preparation with the
// carry region blank, skip install copying, then use the same fixed carry
// insertion planner as the top. Their tombstones remain occupied records.
//
// THE TOP IS THE SAME THREE PHASES over the fixed rebuild's planners,
// which is what lets one job, one state machine and one residual builder serve
// every level.  Its own section is below, after phase 3.
//
// THE UNSPLIT PATH IS THE SAME CODE.  RunLevelMerge below is the three phases
// in sequence, so there is one algorithm and one residual wiring to test
// rather than a prepared variant and an ordinary variant that drift.
//
// A PHASE RUNS AGAINST ITS OWN CONTEXT. The three share the output, nonce
// and map. Preparation and finish retain A's route sheds in one array;
// the direct prefix build keeps B's leftovers in its own tier.
//
// This file emits the merge's work through the shared planning helpers
// (PlanMergeOlderBlocks and PlanMergeFinish, in
// scheduler/cpu_byteslice_subtask_plan.hpp).  What is written out here is
// what is specific to an arena merge: the install, and the checks a merge
// over borrowed, published views needs.
//
// WHY THE INSTALL RE-TAGS.  Copying the carry verbatim would be correct only
// if its stored tags had just been written under this merge's map.  A carry
// here is not in that position.  It was PUBLISHED and probed, and a
// payload-only residual sweep may have left its stored tag bytes pruned or
// stale; and this merge's index map is not the one the carry was written
// under, because at digit j the output is r blocks and its entries need a
// radix digit the carry never carried.  So the install is a fused
// copy-and-re-tag: one pass over U buckets, no extra buffer.  (The one install
// at digit 1 -- a binary level installing P_1 into its odd bank instead of
// adopting it -- is a plain copy: no route follows it and digit 2 re-tags P_1
// as its older operand, so the tags it would write are never read.)
//
// AND WHY THAT DOES NOT MOVE ANYTHING.  Re-tagging normally means re-routing.
// It does not here, and the reason is the one invariant this whole file
// depends on:
//
//     A MERGE AND THE CARRY IT CONSUMES SHARE A NONCE.
//
// That is what the canonical family (cpu_byteslice_level_arena_family.hpp) is
// for.  A carry accepted at level l with ordinal v, and the table this merge
// publishes, have the SAME canonical coordinate -- at digit j < B because the
// loop stops immediately for both, and at digit B because the producer's
// (l, v) and the consumer's (l+1, v/B) are the same pair by construction.  So
// the carry's bucket index is the low K bits of a raw hash, and the re-tag
// recomputes the low K bits of THE SAME raw hash.  Higher bits and the radix
// digit change -- which is exactly what the finish phase needs -- and which of
// the U buckets an entry sits in does not.
//
// "This merge's nonce" therefore always names that shared nonce.  A merge
// that drew a FRESH nonce for itself would re-tag correctly and place every
// carry entry wrong -- in the bucket some other hash chose for it -- and the
// install, which performs no routing, would leave it there.  That fails
// LOUDLY rather than quietly, which is worth knowing: the carry copy and the
// older copy of a shared key then land in different cross pairs, the merge
// stops deduplicating, and both copies survive into the output.  It is a trap
// for whoever changes nonce assignment.
//
// The OLDER source is the opposite case and is handled the opposite way: its
// family is independent, so it is copied, re-tagged AND fully re-routed.
//
// WHAT IS NOT HERE.  No stage ladder, no carry token, no preparation registry.
// A prepared job is a destination slot plus the sheds it has not resolved yet;
// the phases below are pure planning over public geometry.

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <string>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp"
#include "src/oram/scheduler/cpu_byteslice_subtask_plan.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

// ---------------------------------------------------------------------------
// The shape of one merge
// ---------------------------------------------------------------------------
//
// At digit j, write j = r * 2^e with r odd.  The output is r blocks of
// 2^e * U buckets: block 0 holds the fresh carry plus (2^e - 1)U older
// buckets and is finished by e deduplicating cross levels; blocks 1..r-1 hold
// only older entries and are finished by the ordered radix-r pass.
//
// Every field is a public function of the digit and the carry size.  The
// struct exists so that PREPARATION -- which runs before the carry exists and
// must not consult it -- has the same shape the finish will use.
struct MergeShape {
  size_t carry_buckets = 0;   // U
  unsigned carry_bits = 0;    // K = log2(U)
  unsigned digit = 0;         // j
  unsigned odd_part = 1;      // r
  unsigned power = 0;         // e
  unsigned block_bits = 0;    // K + e
  size_t block_buckets = 0;   // 2^(K+e)
  size_t out_buckets = 0;     // j U
  // The OLDER source's extent, and the one field whose meaning differs at the
  // top: (j-1)U below it, where a level absorbs its own partial into a bigger
  // table, and the whole of A -- T buckets, the output's own size -- at the
  // top, which compacts a full level in place of growing one.
  size_t older_buckets = 0;

  bool has_cross_levels() const { return power != 0; }
  bool has_radix_pass() const { return odd_part > 1; }
};

// `radix` is the ODD part the output's index map routes on, which is where the
// runner reads it from too (CarryRadix).  Below the top it is the odd part of
// the digit; the top forces r = D and e = 0, so the same constructor covers
// both and the two never derive it differently.
inline MergeShape MakeMergeShape(size_t carry_buckets, unsigned digit,
                                 unsigned radix) {
  if (carry_buckets == 0 || digit == 0 || radix == 0) {
    throw std::invalid_argument("level arena: empty merge shape");
  }
  if (digit % radix != 0) {
    throw std::invalid_argument("level arena: digit is not a multiple of its "
                                "index map's radix");
  }
  MergeShape s;
  s.carry_buckets = carry_buckets;
  s.carry_bits = Log2Checked(carry_buckets, "carry size");
  s.digit = digit;
  s.odd_part = radix;
  s.power = Log2Checked(digit / radix, "digit / radix");
  s.block_bits = s.carry_bits + s.power;
  // BEFORE the shift, not after.  The output product below refuses an
  // oversized merge, but `1 << 64` is undefined behaviour rather than a wrap
  // that a later check could still catch -- and this helper is public and
  // callable without a geometry to have vetted its arguments first.
  if (s.block_bits >= 64) {
    throw std::overflow_error("level arena: a merge block does not fit a "
                              "64-bit bucket count");
  }
  s.block_buckets = size_t{1} << s.block_bits;
  s.out_buckets =
      static_cast<size_t>(CheckedMul(digit, carry_buckets, "merge output"));
  s.older_buckets =
      static_cast<size_t>(CheckedMul(digit - 1, carry_buckets, "older source"));
  return s;
}

// The shape of a merge whose context is fully populated -- the unsplit path,
// and the finish of a prepared one.
inline MergeShape MergeShapeOf(const RebuildStepContext& ctx) {
  const size_t carry = ctx.fresher.num_buckets;
  if (carry == 0 || ctx.out.num_buckets % carry != 0) {
    throw std::invalid_argument("level arena: output is not a whole number of "
                                "carries");
  }
  const size_t digit = ctx.out.num_buckets / carry;
  // The digit is a small number -- at most B below the top and D at it -- but
  // it is derived here from two view extents, and narrowing it silently would
  // turn an impossible output into a plausible one.
  if (digit > ~0u) {
    throw std::overflow_error("level arena: the output is more carries than a "
                              "digit can count");
  }
  return MakeMergeShape(carry, static_cast<unsigned>(digit),
                        CarryRadix(ctx.map));
}

// THE TOP'S SHAPE (DESIGN.md "Top compaction and residuals").
// Its digit is fixed at D, a power of two (LevelArenaGeometry::IsTopDigit),
// routed as one (K + log2 D)-level butterfly over all of T with no radix pass
// (r = 1, e = log2 D).  The same constructor serves the top and the levels
// below it, so the two can never derive a shape's fields differently.
//
// What does differ is the older source: the top does not absorb a partial of
// its own, it compacts A, and A is a FULL level of T buckets -- which is also
// the output's own size, so the block IS the output.
inline MergeShape MakeTopMergeShape(size_t carry_buckets, unsigned top_digit) {
  if (!LevelArenaGeometry::IsTopDigit(top_digit)) {
    throw std::invalid_argument("level arena: the top's digit is 1, 2, 4 or 8");
  }
  MergeShape s = MakeMergeShape(carry_buckets, top_digit, 1);
  s.older_buckets = s.out_buckets;
  return s;
}

// THE SHAPE OF A MERGE AT (level, digit), in the one spelling that both the
// job it binds and every publication that describes its output use: the top's
// rule at the top, whatever `digit` says, and the digit's odd part below it.
inline MergeShape LevelMergeShapeOf(const LevelArenaGeometry& geometry,
                                    unsigned level, unsigned digit) {
  const size_t carry = geometry.CarryBuckets(level);
  if (level == geometry.Levels()) {
    return MakeTopMergeShape(carry, geometry.TopDigit());
  }
  if (digit == 0) {
    throw std::invalid_argument("level arena: digits are one-based");
  }
  unsigned odd = digit;
  while (odd % 2 == 0) odd /= 2;
  return MakeMergeShape(carry, digit, odd);
}

// ---------------------------------------------------------------------------
// Preconditions
// ---------------------------------------------------------------------------
//
// These are CHECKED, not asserted, and the distinction is not pedantry: each
// one guards a subtask kind that turns a wrong view extent into an
// out-of-bounds READ of somebody else's arena -- kCopyAndRetagRange indexes
// `older` at `begin - upper_offset`, kCopyAndRetagFresher indexes `fresher`
// over the whole carry.
// assert() is compiled out of the Release build, which
// is the build that runs.  Planning happens once per phase, so the cost is
// nothing.

inline void ExpectMergeView(bool ok, const char* what) {
  if (!ok) {
    throw std::invalid_argument(std::string("level arena: ") + what);
  }
}

// Every re-tag in this merge -- the install, the older blocks, the dense
// builder's -- lays down the tag bytes `ctx.route_levels` asks for, and the
// cross and radix phases then route on them.  There is no chain here for the
// number to belong to: a merge is self-contained, so it is exactly the
// output's block depth.  Too few bytes and a later phase routes on bytes
// nobody wrote, which misplaces entries without reading out of bounds -- the
// quietest of the failures here, and the reason it is checked at every phase
// rather than only where the composites call them.
inline void ExpectMergeRouteLevels(const RebuildStepContext& ctx,
                                   const MergeShape& shape) {
  ExpectMergeView(ctx.route_levels == shape.block_bits,
                  "route_levels must be the merge's block depth");
}

inline void ExpectMergeOutput(const RebuildStepContext& ctx,
                              const MergeShape& shape) {
  ExpectMergeView(ctx.out.num_buckets == shape.out_buckets,
                  "the output view is not j*U buckets");
}

// ---------------------------------------------------------------------------
// Phase 1: prepare the older sources
// ---------------------------------------------------------------------------
//
// The pure blocks first, then block 0's older spans largest-first, which is
// RouteBinarySourcesDedup's order.  They are disjoint destination spans, so
// only "before the cross levels" is load bearing about it.
//
// The older source lands at ctx.upper_offset = U and is copied, re-tagged and
// routed under THIS merge's nonce and map; its own former family is
// independent and nothing here depends on it.
//
// No residual pass is planned here, and that is deliberate: every shed goes to
// the job's level stashes and is resolved by the finish, after the cross and
// radix work has put each entry in its final bucket.  Offering a shed back
// before then would pair it with a bucket it is not going to live in.  (This
// is also why PlanPrepareOlderHalf is not reused: it ends with pass 0, and it
// assumes a power-of-two span, which (j-1)U is not.)

template <typename PlanOut>
inline void PlanPrepareOlderSources(const RebuildStepContext& ctx,
                                    const MergeShape& shape,
                                    const SubtaskBudget& budget, PlanOut* out) {
  ExpectMergeRouteLevels(ctx, shape);
  ExpectMergeOutput(ctx, shape);
  // The older source lands at U and is read at `begin - upper_offset`.
  ExpectMergeView(ctx.upper_offset == shape.carry_buckets,
                  "the older source does not start at U");
  ExpectMergeView(ctx.older.num_buckets == shape.older_buckets,
                  "the older view is not (j-1)*U buckets");
  PlanMergeOlderBlocks(shape.carry_bits, shape.odd_part, shape.power,
                       ctx.out.layout.BucketBytes(), budget, out);
}

// ---------------------------------------------------------------------------
// Phase 2: install the fresh carry
// ---------------------------------------------------------------------------

// A sparse carry: one fused copy-and-re-tag into out[0, U).  See the header
// comment for why this needs no routing.
//
// At digit 1 (a binary level installing P_1 into its odd bank) it is a plain
// copy of the carry instead (PlanCopyFresherPrefix).  No route
// follows it, probes hash the key, and digit 2 re-tags P_1 as its older
// operand, so nothing reads the tags a re-tag would write.
template <typename PlanOut>
inline void PlanInstallSparseCarry(const RebuildStepContext& ctx,
                                   const MergeShape& shape,
                                   const SubtaskBudget& budget, PlanOut* out) {
  ExpectMergeRouteLevels(ctx, shape);
  ExpectMergeOutput(ctx, shape);
  ExpectMergeView(ctx.fresher.num_buckets == shape.carry_buckets,
                  "the carry view is not U buckets");
  if (shape.digit == 1) {
    PlanCopyFresherPrefix(shape.carry_buckets, budget, out);
    return;
  }
  PlanRange(Subtask::kCopyAndRetagFresher, 0, shape.carry_buckets,
            budget.copy_retag_buckets, out);
}

// s^2 r0 (r0-1) / 2: the FIXED number of bucket comparisons the prefix dedup
// costs, independent of how many real keys the prefix holds.
inline size_t DensePrefixDedupPairs(const LevelArenaGeometry& geometry) {
  const uint64_t s = geometry.StashBuckets();
  const uint64_t r0 = geometry.PrefixFlushes();
  return static_cast<size_t>(
      CheckedMul(CheckedMul(s, s, "dedup pairs"), r0 * (r0 - 1) / 2,
                 "dedup pairs"));
}

// LEVEL ONE'S DIRECT B BUILD (the kernels and their
// argument are cpu_byteslice_dense_select.hpp's).  The prefix dedup as above,
// then every prefix bucket hashed once into the home cache, then every B home
// scanning every prefix bucket, then the rejected winners into B's tier.  All
// four are ordered: the dedup's order is load bearing, and the selection
// clears the shared remaining masks.
//
// `ctx.fresher` is B's main, U buckets -- the output itself at digit one, a
// private table the fixed insertion reads above it -- and `ctx.dense_tier`
// its leftovers' stash: the output tier at digit one, B's one-bucket tier
// above it.  Overflowing that stash is the build's own declared failure.
template <typename PlanOut>
inline void PlanBuildDenseDirect(const RebuildStepContext& ctx,
                                 const LevelArenaGeometry& geometry,
                                 const SubtaskBudget& budget, PlanOut* out) {
  const size_t log_buckets = geometry.DensePrefixBuckets();   // M = r0 s
  const size_t homes = geometry.RoutedPrefixBuckets();        // U_1
  ExpectMergeView(ctx.small_log.num_buckets == log_buckets &&
                      ctx.small_old.num_buckets == log_buckets,
                  "the prefix is not Z/2 buckets");
  ExpectMergeView(ctx.small_log.data == ctx.small_old.data &&
                      ctx.small_log.masks != ctx.small_old.masks,
                  "the direct build borrows the prefix with private masks");
  ExpectMergeView(ctx.fresher.num_buckets == homes &&
                      ctx.fresher.data != nullptr &&
                      ctx.fresher.masks != nullptr,
                  "B's main is not U buckets");
  ExpectMergeView(ctx.dense_homes != nullptr && ctx.dense_tier != nullptr,
                  "the direct build has no home cache or no tier");
  MarkStage(out, OrderedStage());
  Subtask dedup;
  dedup.kind = Subtask::kPrefixLogDedup;
  dedup.levels = static_cast<unsigned>(geometry.StashBuckets());
  dedup.bit = geometry.PrefixFlushes();
  PlanTaggedRange(dedup, 0, DensePrefixDedupPairs(geometry),
                  budget.intersect_units, out);
  PlanRange(Subtask::kDenseHomes, 0, log_buckets, budget.retag_buckets, out);
  Subtask select;
  select.kind = Subtask::kDenseSelect;
  select.levels = static_cast<unsigned>(log_buckets);
  PlanTaggedRange(select, 0, homes, DenseSelectHomeSlice(budget, select.levels),
                  out);
  PlanRange(Subtask::kDenseDrain, 0, log_buckets, budget.copy_buckets, out);
}

// ---------------------------------------------------------------------------
// Phase 3: finish
// ---------------------------------------------------------------------------
//
// Block 0's cross-source levels, then the ordered radix pass, then the
// residual second chances.  Both logical inputs are internally duplicate-free,
// so deduplication needs only cross-source pairs: a duplicate is always (carry copy, older copy), both copies share a tag and
// therefore an offset within their blocks, and either a cross level pairs them
// or the radix prologue clears the block-q copy of a block-0 key.
//
// The residual passes run LAST, after the radix pass, because a second chance
// pairs an entry with its FINAL bucket and until the radix pass has run an
// entry of block q is not yet where the index map puts it.  Which pass is
// fused into which routing pass is read off the context: kCrossLevel when the digit is a power of two, kRadixPass when it is
// not, standalone otherwise.
// A residual pass may only be fused where this merge has a pass to fuse it
// into.  A pass fused anywhere else is planned NOWHERE -- PlanStandalonePasses
// skips it because its site is not kNone, and neither routing phase below
// looks for it -- so its entries would be built into a range table and never
// swept, drained or reset.  That is a silent loss of live records, which is
// why it is checked rather than commented.
inline bool LevelMergeFuseSitesSupported(const RebuildStepContext& ctx) {
  for (unsigned pass = 0; pass < kResidualPasses; ++pass) {
    const ResidualPass& rp = ctx.residual[pass];
    if (!rp.active) continue;
    if (rp.fuse != ResidualFuseSite::kNone &&
        rp.fuse != ResidualFuseSite::kCrossLevel &&
        rp.fuse != ResidualFuseSite::kRadixPass) {
      return false;
    }
  }
  return true;
}

template <typename PlanOut>
inline void PlanFinishMerge(const RebuildStepContext& ctx,
                            const MergeShape& shape,
                            const SubtaskBudget& budget, PlanOut* out) {
  if (!LevelMergeFuseSitesSupported(ctx)) {
    throw std::invalid_argument("level arena: a residual pass is fused at a "
                                "site this merge does not run");
  }
  ExpectMergeRouteLevels(ctx, shape);
  ExpectMergeOutput(ctx, shape);
  // A pass can only ride a phase this digit actually runs.
  ExpectMergeView(!HasFusedPass(ctx, ResidualFuseSite::kCrossLevel) ||
                      (shape.odd_part == 1 && shape.power >= 1),
                  "a pass is fused at a cross level this digit does not run");
  ExpectMergeView(!HasFusedPass(ctx, ResidualFuseSite::kRadixPass) ||
                      shape.odd_part > 1,
                  "a pass is fused at a radix pass this digit does not run");
  PlanMergeFinish(ctx, shape.carry_bits, shape.odd_part, shape.power, budget,
                  out);
}

// ---------------------------------------------------------------------------
// The top's phases (DESIGN.md "Top compaction and residuals")
// ---------------------------------------------------------------------------
//
// The top is the one level that never grows: it is always T = D*U_L buckets,
// it absorbs no partial of its own, and it consumes its carry from an inbox it
// never copies.  So its two phases are the FIXED REBUILD's, planned by
// PlanPrepareOlderHalf and PlanFixedMerge, and what this file adds is only
// the cut between them and the checks an arena merge needs:
//
//   PREPARE  C <- A: one fused copy-and-re-tag of the whole of A under the
//            next compaction's nonce, then the route -- one
//            (K + log2 D)-level butterfly over all of T.  It depends on nothing but A and a
//            coordinate, so it runs long before the carry exists -- which is
//            the same property the non-top preparation has, reached by the
//            same route.
//   FINISH   B into C: per source bucket, the D-way dedup-and-merge against
//            that bucket's D destinations, the residual second chance, and
//            then the tombstone drop over C and its tier.
//
// AND THE CARRY IS NEVER INSTALLED.  A non-top merge lays its carry into the
// output's first U buckets; the top's merge reads the carry where it lies and
// merges it bucket by bucket, so the install phase has no kernel at all.  It
// is still a phase -- it is where the job binds the carry and validates it,
// and keeping one state machine is worth more than saving a call.
//
// WHY THE CARRY'S TAGS NEED NO SCRATCH COPY.  The carry's stored tags were
// written under its producer's map, so they must be refreshed; the obvious
// way is per source bucket, in a private one-bucket scratch view.  The
// merge reads exactly ONE tag line of its source -- the digit -- and moves
// only payload lines out of it, so the copy has nothing to contribute and the
// re-tag is a register: FixedMergeRetag, set through
// RebuildStepContext::retag_fresher_digits.  Same digits, same kernel, no
// scratch bucket and no second pass over the carry.

// The top's preparation: PlanPrepareOlderHalf over the whole of A, which
// lands at offset zero.
//
// Unlike the non-top preparation, this one ENDS IN A RESIDUAL PASS of its own
// and retains what that pass cannot place.  It can, and the non-top one
// cannot, for one reason: the route's last butterfly level completes C's
// route, so after this phase every entry of A is in its FINAL bucket and a
// second chance can pair it with that bucket.  Below the top a block-q entry
// is not where the index map puts it until the finish's radix pass has run.
template <typename PlanOut>
inline void PlanTopPrepare(const RebuildStepContext& ctx,
                           const MergeShape& shape,
                           const SubtaskBudget& budget, PlanOut* out) {
  ExpectMergeRouteLevels(ctx, shape);
  ExpectMergeOutput(ctx, shape);
  // A is copied whole, at offset 0, and is the output's own size.  The
  // non-top check is the other one: (j-1)U landing at U.
  ExpectMergeView(ctx.upper_offset == 0,
                  "the top copies A whole, at offset zero");
  ExpectMergeView(ctx.older.num_buckets == shape.older_buckets,
                  "the top's older source is not the whole of A");
  // The preparation's offer rides A's last butterfly level; a pass fused
  // where this phase has nothing to fuse into is planned NOWHERE (see
  // LevelMergeFuseSitesSupported).
  ExpectMergeView(!shape.has_radix_pass() &&
                      !HasFusedPass(ctx, ResidualFuseSite::kRadixPass),
                  "the top is binary: its route has no radix pass to ride");
  PlanPrepareOlderHalf(ctx, budget, out);
}

// Top and separated ordinary passes insert the carry directly from its
// published view, with no install copy. Check its extent and way retagging
// before either planning or running the fixed insertion sweep.
inline void ExpectFixedCarry(const RebuildStepContext& ctx,
                             const MergeShape& shape) {
  ExpectMergeView(ctx.fresher.num_buckets == shape.carry_buckets,
                  "the fixed insertion carry is not U buckets");
  ExpectMergeView(ctx.retag_fresher_digits == (shape.digit > 1),
                  "the carry was published under its producer's map, so "
                  "its ways must be recomputed at D > 1 -- and there is "
                  "nothing to recompute at D = 1");
}

// Shared fixed carry insertion for top and separated ordinary finishes.
// Every active residual pass must ride this sweep: its shed is drain-only,
// and its fused offers and coordinated epilogue resolve the residual pool.
//
// Only top contexts enable drop_unshadowed. They resolve all versions before
// capacity decisions (ResolveTopDestination), omit tombstones and finish
// with the top-only drop. Ordinary insertion preserves tombstones. Sharing
// this planner must not grant ordinary contexts the top's deletion contract.
template <typename PlanOut>
inline void PlanFixedCarryInsertion(const RebuildStepContext& ctx,
                                    const MergeShape& shape,
                                    const SubtaskBudget& budget, PlanOut* out) {
  ExpectMergeRouteLevels(ctx, shape);
  ExpectMergeOutput(ctx, shape);
  ExpectFixedCarry(ctx, shape);
  for (unsigned pass = 0; pass < kResidualPasses; ++pass) {
    const ResidualPass& rp = ctx.residual[pass];
    ExpectMergeView(!rp.active || rp.fuse == ResidualFuseSite::kFixedMerge,
                    "the fixed insertion residual pass must ride its sweep; fused "
                    "anywhere else it is planned nowhere and its entries are "
                    "never swept, drained or reset");
  }
  // FixedMergeRadix reads D off the two extents; the shape says what it must
  // be, and a disagreement would split the source on a fan-in the way
  // computation did not write.  It is the DIGIT, not the map's odd part: a
  // binary top's map is kRaw and its sweep is still D-way.
  ExpectMergeView(FixedMergeRadix(ctx) == shape.digit,
                  "the fixed insertion would split its carry on another fan-in "
                  "than its digit");
  PlanFixedMerge(ctx, budget, out);
}

// ---------------------------------------------------------------------------
// The three phases as one merge
// ---------------------------------------------------------------------------
//
// Preparation and finish, by contrast, MUST share one array: they shed the
// same class (a cross level sheds its older operand), the finish's pool is
// sized over both, and a preparation shed that is not in the finish's pool is
// never offered back at all.
//
// The sparse install is the one phase that may share any context it likes: a
// fused copy-and-re-tag performs no routing and sheds nothing.
enum class LevelMergePhase : uint8_t { kPrepareOlder, kInstallCarry, kFinish };

inline const char* LevelMergePhaseName(LevelMergePhase phase) {
  switch (phase) {
    case LevelMergePhase::kPrepareOlder: return "prepare-older";
    case LevelMergePhase::kInstallCarry: return "install-carry";
    case LevelMergePhase::kFinish: return "finish";
  }
  return "?";
}

// What the three phases are planning: the shape, which of the three carry
// installs this merge runs, and -- for level 1 only -- the geometry the dense
// builder reads its prefix counters from.
//
// The three are exclusive and exhaustive: `top` is the fixed compaction, a
// non-null `dense_direct` is level 1's direct prefix build, and neither is
// the sparse install.
struct LevelMergeSpec {
  MergeShape shape;
  // Level 1's direct B build (PlanBuildDenseDirect).
  const LevelArenaGeometry* dense_direct = nullptr;
  bool top = false;
  // An ordinary digit > 1 whose carry is inserted by the fixed sweep: a
  // sparse one, or a directly built level one's.
  bool separated_sources = false;

  bool dense_direct_install() const { return dense_direct != nullptr; }
};

// The contexts of one merge.  They agree on the output, the nonce, the map and
// the route depth -- it is one table being built -- and differ in the sources
// each phase reads and in where it sheds.
struct LevelMergeContexts {
  const RebuildStepContext* prepare = nullptr;
  const RebuildStepContext* install = nullptr;
  const RebuildStepContext* finish = nullptr;

  // The one-context form, legal only for a sparse install (checked).
  static LevelMergeContexts Shared(const RebuildStepContext& ctx) {
    LevelMergeContexts c;
    c.prepare = c.install = c.finish = &ctx;
    return c;
  }

  const RebuildStepContext& At(LevelMergePhase phase) const {
    const RebuildStepContext* ctx = phase == LevelMergePhase::kPrepareOlder
                                        ? prepare
                                        : (phase == LevelMergePhase::kFinish
                                               ? finish
                                               : install);
    if (ctx == nullptr) {
      throw std::invalid_argument("level arena: this merge has no context for "
                                  "that phase");
    }
    return *ctx;
  }
};

// STASH SLOTS.  A route `n` bits deep owns slots [0, n): bit b sheds into
// level_stashes[b], and the fused quad's level_stashes[bit + 1] is the next
// ROUTED bit's slot, never one past the network (the slot layout is
// LevelMergeStashSlots in cpu_byteslice_level_arena_stash.hpp).
//
// Everything the three contexts have to agree on.  Planning-time only, like every other check in this file.
inline void ExpectLevelMergeContexts(const LevelMergeContexts& ctxs,
                                     const LevelMergeSpec& spec) {
  const RebuildStepContext& prepare = ctxs.At(LevelMergePhase::kPrepareOlder);
  const RebuildStepContext& install = ctxs.At(LevelMergePhase::kInstallCarry);
  const RebuildStepContext& finish = ctxs.At(LevelMergePhase::kFinish);
  const RebuildStepContext* phases[3] = {&prepare, &install, &finish};
  for (const RebuildStepContext* ctx : phases) {
    ExpectMergeView(ctx->out.data == prepare.out.data &&
                        ctx->out.masks == prepare.out.masks &&
                        ctx->out.num_buckets == prepare.out.num_buckets &&
                        ctx->out.layout == prepare.out.layout,
                    "the phases of one merge disagree about the output");
    ExpectMergeView(ctx->nonce_lo == prepare.nonce_lo &&
                        ctx->nonce_hi == prepare.nonce_hi,
                    "the phases of one merge disagree about the nonce");
    ExpectMergeView(ctx->route_levels == prepare.route_levels,
                    "the phases of one merge disagree about the tag depth");
    ExpectMergeView(ctx->map.kind == prepare.map.kind &&
                        ctx->map.low_bits == prepare.map.low_bits &&
                        ctx->map.modulus == prepare.map.modulus &&
                        ctx->map.digit_shift == prepare.map.digit_shift,
                    "the phases of one merge disagree about the index map");
    ExpectMergeView(ctx->upper_offset == prepare.upper_offset,
                    "the phases of one merge disagree about where the older "
                    "source lands");
    // The tag PRF's key, which is the instance's secret and not a parameter
    // of the tag word: two phases on two keys hash one key to two places, and
    // every check above would still pass.
    ExpectMergeView(ctx->aes_keys == prepare.aes_keys,
                    "the phases of one merge disagree about the tag key");
    // WHO MAY FORGET A TOMBSTONE, checked rather than left to whoever wires
    // the job.  It is the top and nothing else: only there does FIFO
    // consumption retire every older family, and only there does kDropErased
    // follow.  Pinned against `spec.top` rather than merely compared across
    // the phases, because the failure in both directions is silent -- set it
    // below the top and a staler value resurrects at the next carry, clear it
    // at the top and the `1/D` miss-capacity term comes back, which is what a
    // narrow top runs out of room on.
    ExpectMergeView(ctx->drop_unshadowed == spec.top,
                    "only a merge into the last level may drop unshadowed "
                    "tombstones");
  }
  ExpectMergeView(prepare.aes_keys != nullptr,
                  "a merge routes under the instance's tag key, and "
                  "this one has none");
  // The map has to describe the shape it is routing, or the re-tags split the
  // tag word at one bit and the passes read it at another.
  ExpectMergeView(CarryRadix(prepare.map) == spec.shape.odd_part,
                  "the index map's radix is not the merge's odd part");
  ExpectMergeView(prepare.map.kind != TagMapKind::kRadixDigit ||
                      prepare.map.low_bits == spec.shape.block_bits,
                  "the index map splits the tag at the wrong bit");
  // THE TAG HAS TO HOLD THE INDEX BITS **AND**, UNDER A RADIX MAP, THE WHOLE
  // DIGIT ABOVE THEM.  Three claims, none of which implies another:
  //
  //   1. the digit is where this layout keeps it.  A map is a separate object
  //      from the layout it is applied to -- here the job derives one from
  //      `layout_` and the other arrives inside a `TableView` -- so a re-tag
  //      can write the digit at one offset and a pass read it at another.
  //   2. the layout has room for the whole digit (RoutingDigitFits, which is
  //      where that rule is written down).  Easy to miss, because a digit
  //      with too few bits is not an error downstream: it is a perfectly good
  //      digit, and every entry that needed the missing bits routes to a
  //      block that is not its own: at tag_bytes = 1 and digit_bits = 7,
  //      dozens of entries go missing or survive in the wrong bucket.
  //   3. the index bits fit BELOW the digit, which is what stops the route
  //      from writing over it.
  const Layout& layout = prepare.out.layout;
  size_t index_capacity = 8 * layout.tag_bytes;
  if (prepare.map.kind == TagMapKind::kRadixDigit) {
    index_capacity = prepare.map.digit_shift;
    ExpectMergeView(prepare.map.digit_shift == RoutingDigitShift(layout),
                    "the index map's digit is not where this layout keeps it");
    ExpectMergeView(RoutingDigitFits(layout),
                    "the tag has no room above its index bits for a whole "
                    "radix digit");
  }
  ExpectMergeView(spec.shape.block_bits <= index_capacity,
                  "the merge routes on more tag bits than the layout stores");

  ExpectMergeView(prepare.level_stashes == finish.level_stashes,
                  "preparation and finish must shed into one array: the "
                  "finish's pool is what resolves the preparation's sheds");
  // The top and level-one install planners are exclusive.
  ExpectMergeView(!spec.dense_direct_install() ||
                      !spec.top,
                  "a direct B build is level one's");
  // Top and separated ordinary insertions read a carry published under its
  // producer's map and recompute its final way. Other merges route their
  // source in this rebuild and do not need that extra hash batch.
  for (const RebuildStepContext* ctx : phases) {
    ExpectMergeView(spec.top || spec.separated_sources || !ctx->retag_fresher_digits,
                    "only a fixed insertion sweep recomputes its source's block "
                    "digits");
  }
}

// One phase, planned from its own context.
template <typename PlanOut>
inline void PlanLevelMergePhase(LevelMergePhase phase,
                                const LevelMergeContexts& ctxs,
                                const LevelMergeSpec& spec,
                                const SubtaskBudget& budget, PlanOut* out) {
  ExpectLevelMergeContexts(ctxs, spec);
  if (spec.top) {
    switch (phase) {
      case LevelMergePhase::kPrepareOlder:
        PlanTopPrepare(*ctxs.prepare, spec.shape, budget, out);
        return;
      case LevelMergePhase::kInstallCarry:
        // No kernel: the sweep reads the carry where it lies.
        ExpectFixedCarry(*ctxs.install, spec.shape);
        return;
      case LevelMergePhase::kFinish:
        PlanFixedCarryInsertion(*ctxs.finish, spec.shape, budget, out);
        return;
    }
    throw std::invalid_argument("level arena: no such merge phase");
  }
  if (spec.dense_direct_install()) {
    ExpectMergeView(
        spec.shape.carry_buckets == spec.dense_direct->RoutedPrefixBuckets(),
        "level 1's carry is the routed prefix");
    ExpectMergeView(spec.separated_sources == (spec.shape.digit > 1),
                    "a directly built B above digit one is inserted by the "
                    "separated finish");
    if (spec.shape.digit == 1) {
      // No older half, and B is built straight into the output and its
      // tier, which is the whole merge: no finish pass.
      if (phase == LevelMergePhase::kInstallCarry) {
        PlanBuildDenseDirect(*ctxs.install, *spec.dense_direct, budget, out);
      }
      return;
    }
  }
  if (spec.separated_sources) {
    ExpectMergeView(spec.shape.digit > 1 &&
                        spec.shape.digit <= kMaxFixedMergeWays,
                    "separated routing requires an ordinary sparse merge");
    switch (phase) {
      case LevelMergePhase::kPrepareOlder: {
        // The topology is unchanged. B's region [0, U) is publicly empty;
        // every route shed belongs to A and survives until the finish's
        // offers.  Its masks are never cleared: the one pass that reads the
        // region -- the first continuation at an even digit, the radix pass
        // at an odd one (power == 0, where block 0 IS [0, U)) -- is told it
        // is blank and writes every mask of it.
        PlanPrepareOlderSources(*ctxs.prepare, spec.shape, budget, out);
        for (unsigned bit = spec.shape.carry_bits;
             bit < spec.shape.block_bits; ++bit) {
          StageMark stage = RangeStage();
          Subtask task;
          task.kind = Subtask::kRouteLevelRange;
          task.bit = bit;
          // The first continuation has an empty first operand and no
          // stash access; later levels can append A losses.
          task.blank_first = bit == spec.shape.carry_bits;
          if (!task.blank_first) {
            stage.shed_lo = bit;
            stage.shed_hi = bit + 1;
          }
          MarkStage(out, stage);
          PlanTaggedRange(task, 0, size_t{1} << bit, budget.cross_pairs, out);
        }
        if (spec.shape.has_radix_pass()) {
          StageMark stage = RangeStage();
          stage.radix_shed = true;
          MarkStage(out, stage);
          Subtask task;
          task.kind = Subtask::kRadixRouteRange;
          task.bit = spec.shape.odd_part;
          task.levels = spec.shape.block_bits;
          task.blank_first = spec.shape.power == 0;
          PlanTaggedRange(task, 0, spec.shape.block_buckets,
                          RadixRouteTupleSlice(budget, task.bit), out);
        }
        return;
      }
      case LevelMergePhase::kInstallCarry:
        ExpectFixedCarry(*ctxs.install, spec.shape);
        if (spec.dense_direct_install()) {
          PlanBuildDenseDirect(*ctxs.install, *spec.dense_direct, budget, out);
        }
        return;
      case LevelMergePhase::kFinish:
        PlanFixedCarryInsertion(*ctxs.finish, spec.shape, budget, out);
        return;
    }
  }
  switch (phase) {
    case LevelMergePhase::kPrepareOlder:
      PlanPrepareOlderSources(*ctxs.prepare, spec.shape, budget, out);
      return;
    case LevelMergePhase::kInstallCarry:
      PlanInstallSparseCarry(*ctxs.install, spec.shape, budget, out);
      return;
    case LevelMergePhase::kFinish:
      PlanFinishMerge(*ctxs.finish, spec.shape, budget, out);
      return;
  }
  throw std::invalid_argument("level arena: no such merge phase");
}

// Runs one phase against its own context.  THE ONLY executor: a prepared job
// runs phase 1 here long before phases 2 and 3, an unprepared one runs all
// three back to back through RunLevelMerge below, and neither can end up with
// a subtask issued against the wrong context -- which is what a flat plan
// executed against one context would silently do.
// `overflowed` NAMES THE KIND that ran out of room, and it is worth the
// out-parameter: "a residual stash overflowed" is true of a butterfly level,
// a radix pass, the fixed merge and the residual route, whose remedies have
// nothing in common -- a deeper stash, a wider tier, a range table sized for
// a different pool.
template <bool CheckOverflow = false>
inline bool RunLevelMergePhase(LevelMergePhase phase,
                               const LevelMergeContexts& ctxs,
                               const LevelMergeSpec& spec,
                               const SubtaskBudget& budget,
                               std::vector<Subtask>* scratch,
                               Subtask::Kind* overflowed = nullptr) {
  scratch->clear();
  PlanLevelMergePhase(phase, ctxs, spec, budget, scratch);
  const RebuildStepContext& ctx = ctxs.At(phase);
  bool ok = true;
  for (const Subtask& task : *scratch) {
    if (RunSubtask<CheckOverflow>(ctx, task)) continue;
    if (ok && overflowed != nullptr) *overflowed = task.kind;
    ok = false;
  }
  return ok;
}

// The unsplit path: the three phases in order, each against its own context.
// A level that has not had a chance to prepare ahead runs this; one that has
// runs kPrepareOlder earlier and the other two when the carry arrives.  Same
// planners either way, so there is one algorithm and one residual wiring.
template <bool CheckOverflow = false>
inline bool RunLevelMerge(const LevelMergeContexts& ctxs,
                          const LevelMergeSpec& spec,
                          const SubtaskBudget& budget,
                          std::vector<Subtask>* scratch) {
  bool ok = RunLevelMergePhase<CheckOverflow>(LevelMergePhase::kPrepareOlder,
                                              ctxs, spec, budget, scratch);
  ok &= RunLevelMergePhase<CheckOverflow>(LevelMergePhase::kInstallCarry, ctxs,
                                          spec, budget, scratch);
  ok &= RunLevelMergePhase<CheckOverflow>(LevelMergePhase::kFinish, ctxs, spec,
                                          budget, scratch);
  return ok;
}

// The sparse merge as ONE plan against ONE context.  It is sound because the
// install sheds nothing, so there is only one shed class in the whole merge and only
// one stash array for it.  The dense merge has no such form -- its two
// butterflies shed two classes -- and is planned phase by phase above.
template <typename PlanOut>
inline void PlanSparseLevelMerge(const RebuildStepContext& ctx,
                                 const MergeShape& shape,
                                 const SubtaskBudget& budget, PlanOut* out) {
  LevelMergeSpec spec;
  spec.shape = shape;
  const LevelMergeContexts ctxs = LevelMergeContexts::Shared(ctx);
  PlanLevelMergePhase(LevelMergePhase::kPrepareOlder, ctxs, spec, budget, out);
  PlanLevelMergePhase(LevelMergePhase::kInstallCarry, ctxs, spec, budget, out);
  PlanLevelMergePhase(LevelMergePhase::kFinish, ctxs, spec, budget, out);
}

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
