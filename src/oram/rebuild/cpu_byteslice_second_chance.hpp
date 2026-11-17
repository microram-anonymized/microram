#pragma once

// The second chance: putting shed residuals back into the table they belong
// to, obliviously.
//
// This is steps 2 and 3 of the construction cpu_byteslice_residual_range.hpp
// numbers; steps 0-1 are there.  After step 1 the range table's bucket i
// holds exactly the residuals destined for the i-th range of the main table,
// so the sweep can walk both tables in lockstep, offering each range's
// residuals to each of its buckets in turn.  Nothing about which bucket a
// residual actually wanted is observable, because the scan is a fixed
// sequential pass over both tables and does not depend on any residual's
// destination -- which is precisely what the naive "look up each residual's
// bucket" cannot claim.
//
// Two properties fall out of the construction, and both are load bearing:
//
//   - A residual that DUPLICATES a main-table entry never survives AS a
//     duplicate, whatever the dedup rule decides: under kTableWins the
//     candidate is consumed outright, and under kResidualWins the stale main
//     copy is cleared -- the candidate then either takes a slot or drains as
//     its key's only copy (see PlanResidualOfferMerge: crowding can leave a
//     resolver over, but never both copies).  So leftovers are never
//     duplicates, and the compacted remainder can be republished as a fresher
//     level.
//   - The leftover count stops depending on the network depth.  A residual only
//     fails when its target bucket is genuinely full (~2^-21 at load 0.5),
//     instead of every shed entry surviving to a final dump.
//
// WHICH COPY WINS.  Neither rule needs to know either side's source level, but
// each is only VALID for a particular class of residual:
//
//   - kResidualWins for an entry shed at a CROSS-SOURCE MergeSplit.  It
//     survived that level's dedup, so no fresher copy existed in the prefix and
//     every copy still standing is from a staler source block.
//   - kTableWins for an entry shed inside a source block's OWN butterfly,
//     provided it is re-offered while the table holds only blocks at least as
//     fresh as its own.  Any duplicate it meets is then fresher, and its own
//     block cannot hold a second copy -- so a survivor is known to have no
//     duplicate among those blocks at all.  That stays true to the end of the
//     network, since a cross level only ever sheds from its older operand.
//   - kNoDedup for a table that cannot contain a duplicate of the residual at
//     all: re-offering a block's residuals to that same block.
//
// This is why the passes are per BLOCK rather than one shared slot -- a
// carry's freshness class is its block's, so the sweeps have to be told apart.

#include <immintrin.h>

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <vector>

#include "src/core/mov_intrinsics.hpp"
#include "src/oram/rebuild/cpu_byteslice_dedup_masks.hpp"
#include "src/oram/rebuild/cpu_byteslice_dedup_network.hpp"
#include "src/oram/rebuild/cpu_byteslice_residual_range.hpp"
#include "src/oram/rebuild/cpu_byteslice_stash_rebuild.hpp"

namespace microram {
namespace byteslice {

// Which copy wins when a residual entry and a main-table entry hold the same
// key.  Neither rule needs to know either side's source level, but each is
// only VALID for a particular class of residual (see the file header).
// The rules:
//
//  - kResidualWins is correct for entries shed at a CROSS-SOURCE MergeSplit.
//    Such an entry survived that level's dedup, so no fresher copy existed in
//    the prefix; every copy still standing is from a staler source block.
//  - kTableWins is correct for entries shed inside a source block's own
//    butterfly, provided they are re-offered while the table holds only blocks
//    at least as fresh as theirs.
//  - kNoDedup is for a table that cannot contain a duplicate of the residual at
//    all (re-offering a block's residuals to that same block).
//  - kClassMark is the MERGED per-step offer: one range table holds both of
//    a chain step's swept classes, told apart by a per-entry class bit in the
//    META line (kMetaResidualClass, cpu_byteslice_meta.hpp) -- kTableWins
//    applied to the carry class, kResidualWins to the tier class, one tag
//    match and one permute-merge for the two.
enum class ResidualDedupRule { kNoDedup, kResidualWins, kTableWins, kClassMark };

// WHERE a pass's offers run, when they do not run as a standalone sweep.
//
//  - kCrossLevel: the offers ride the step's cross-source level
//    (kCrossLevelOffers) -- the chain step's carry and tier passes.
//  - kOwnLastLevel: the offers ride the LAST level of the pass's own
//    butterfly (kButterflyLevelOffers) -- pass 0, whose standalone sweep
//    would be the largest single share of the residual sweeps' cost.  The
//    range table is built from
//    the sheds of levels [0, l-1) plus the tier, and the last level's own
//    sheds are DRAIN-ONLY by the lemma at ButterflyLevelOffersRange.
//  - kRadixPass: the offers ride the mixed-radix pass that ENDS the route
//    (kRadixPassOffers with the absorb's dedup prologue, kRadixRouteOffers
//    without it for the fixed preparation) -- every output bucket is final
//    the moment its tuple has merged, so the offer sees exactly what the
//    standalone post-route sweep saw.  The radix shed is drain-only.
//  - kFixedMerge: the offers ride the fixed level's B-into-C merge
//    (kFixedMergeOffers): C's bucket is final once B's direction-q entries
//    have merged into it.  The merge shed is drain-only.
//
// The last two are the finalizers of items whose sweeps would otherwise run
// standalone over the whole level: the absorb (radix pass, or its last cross
// level when the digit is a power of two, which reuses kCrossLevel), the
// fixed preparation (radix pass, or its
// last butterfly level at r = 1, which reuses kOwnLastLevel) and the fixed
// merge.  Their one extra obligation is the leftover dedup, below: unlike a
// chain step, their drain-only shed can come from the FRESHER operand while a
// swept class is staler, and a same-key pair split between the shed stash and
// the range table's leftovers is out of the pool dedup's reach.
enum class ResidualFuseSite : uint8_t {
  kNone,
  kCrossLevel,
  kOwnLastLevel,
  kRadixPass,
  kFixedMerge,
};

// A STACKED range table (plan.groups > 1) needs no rule of its own, and this is
// worth stating because it looks as if it might: two copies of a key share a
// tag and so share an INDEX, but which sub-table they land in follows from
// which POOL BUCKET they came from, so a per-range-bucket scan could not see
// them together.  That does not matter -- step 0 has already made the pool
// duplicate-free, so there is no second copy for stacking to separate.  See
// ResidualPoolDedupRange.
//
// A DIRECT range table (range_bits == 0, the pool itself: see
// kResidualDirectMaxLevels) is the same situation one step further: a range
// bucket mixes DESTINATIONS rather than mixing sub-tables, the sweep's
// index_bits match does the selection a route would, and the dedup rules
// stay exact per (bucket, group) visit because a same-key pair always shares
// its destination bucket -- a duplicate of a main[b] entry is a candidate
// exactly when the sweep visits b.  Across groups, step 0 again guarantees no
// main bucket is ever offered two copies of one key; the groups of one b run
// in issue order (below), which is all the rules ever needed.

// Step 2.  Sweeps `main` and `range` together in index order; main bucket b
// takes the entries of residual bucket (b >> index_bits) whose low index_bits
// of tag select b, as many as its free slots allow.  Absorbed entries are
// cleared from the residual mask; the rest stay for the next caller.
//
// The unit is (main bucket, group), b-major, so the sweep is
// main.num_buckets * plan.groups units long and a unit reads and writes only
// main[b] and range[r].  On the usual unstacked plan groups is 1 and the unit
// IS the main bucket.  b-major keeps the main bucket hot
// across its groups while the (small) stacked range table streams past it, and
// it is what makes the groups of one b run in issue order -- which is what the
// dedup rules need, since group g may resolve against what group g-1 inserted.
//
// `lines` is how many byte lines an absorbed entry needs to carry: the payload
// alone after the last routing step, or the full entry when the caller intends
// to keep routing (re-offering a block's residuals mid-network).
//
// The main table need not be a power of two.  A base-B table is m * 2^K buckets
// and the caller sizes the range table from ceil(log2 M) rather than log2 M,
// so the ranges COVER the table with a few empty ones at the top: the pairing is arithmetic on the flat destination
// index, which the kResidualRetag map stores, and cares only that every main
// bucket has a range to pair with.
// One unit of the sweep: offer range bucket `g * sub + (b >> index_bits)`'s
// candidates that name main bucket `b`, under Rule, moving `lines` byte
// lines.  Factored out of the sweep loop so the cross-level pass can run it
// IN PLACE, right after it merges a bucket pair -- the fused form, where the
// sweep's whole main-table read-modify-write rides the routing pass that
// already performs it and the offer adds only the tag match, the intersect
// and the register-resident permute.
// Candidates of one range bucket for main bucket b: the real lanes whose low
// index_bits of stored tag name exactly b.  Tag byte tb lives at line
// tag_base - tb (the reversed order), so the low bytes are the last lines.
// Factored out of the offers so the single-rule and class-marked forms cannot
// drift on the match.
inline uint64_t ResidualOfferCandidates(const TableView& range,
                                        const uint8_t* rbucket, uint64_t rmask,
                                        const ResidualRangePlan& plan,
                                        size_t want) {
  const size_t tag_base = range.layout.TagOffset() + range.layout.tag_bytes - 1;
  const size_t full_tag_bytes = plan.index_bits >> 3;
  const unsigned rem_bits = plan.index_bits & 7;
  // `cand` is secret: with plain intrinsics GCC folded each `cand &=` into
  // the compare's write mask and read the tag line from memory under it, so
  // the compares are the register-only core form.
  uint64_t cand = rmask;
  for (size_t tb = 0; tb < full_tag_bytes; ++tb) {
    const __m512i line = _mm512_load_si512(reinterpret_cast<const void*>(
        rbucket + (tag_base - tb) * kBucketCapacity));
    cand &= core::obliCmpEqMask8(
        line, _mm512_set1_epi8(static_cast<char>(want >> (8 * tb))));
  }
  if (rem_bits != 0) {
    const uint8_t keep_bits = static_cast<uint8_t>((1u << rem_bits) - 1);
    const __m512i line = _mm512_load_si512(reinterpret_cast<const void*>(
        rbucket + (tag_base - full_tag_bytes) * kBucketCapacity));
    const __m512i masked = _mm512_and_si512(
        line, _mm512_set1_epi8(static_cast<char>(keep_bits)));
    cand &= core::obliCmpEqMask8(
        masked, _mm512_set1_epi8(static_cast<char>(
                    (want >> (8 * full_tag_bytes)) & keep_bits)));
  }
  return cand;
}

// ONE OFFER, planned: which candidates this main bucket takes, which lanes
// they land in, and what the two occupancy words become.  Every offer in this
// file goes through it -- the standalone sweeps, the fused routing passes and
// the fused fixed merge -- so there is one allocation rule to prove and one
// place for it to be wrong.
//
// THE ALLOCATION IS PER CLASS, FRESHER CLASS LAST, and that is a correctness
// rule rather than a preference.  A candidate that resolves a duplicate under
// kResidualWins CLEARS a main lane; the lane it frees may then be taken by a
// different candidate, since a round takes the LOWEST-INDEXED candidates that
// fit and a resolver can be crowded out by a non-resolver.  Where both classes
// allocate together, that freed lane can go to a STALER, kTableWins candidate
// -- and then the invariant every fused final pass rests on is gone:
//
//     A BUCKET THAT WAS FULL WHEN THE RIDDEN PASS SHED INTO IT ABSORBS NO
//     STALER-CLASS CANDIDATE.
//
// That is what makes the drain-only shed resolvable afterwards: a fused pass
// builds its range table before the pass it rides, so the shed is not in the
// table and its only backstop is ResidualLeftoverDedupRange, which reaches a
// range LEFTOVER and nothing else.  The staler copy of a shed key targets the
// same bucket as the shed one -- same key, same tag -- so it is a leftover
// exactly when that bucket would not take it.  Let it take a lane a fresher
// candidate freed and it is past the backstop, and the key is published twice:
// the staler copy in the main table, the fresher in the tier.
//
// So the staler class allocates out of the occupancy the bucket had BEFORE
// any clear, and the fresher class allocates out of what is left plus the
// lanes it freed.  Under a single rule the split costs nothing and changes
// nothing: kTableWins and kNoDedup clear no lane, so round 2 is empty, and
// under kResidualWins every candidate is the fresher class, so round 1 is.
//
// What is given up is packing, on the one shape where the two differ: in a
// bucket that is full before the offer, a lane a fresher candidate frees is
// not available to a staler one, which drains to the tier instead.  A
// bucket is that full with probability ~2^-21 at load 0.5.
//
// OCCUPANCY STILL NEVER DROPS, which the drain-only lemma
// (DrainResidualPoolRange) needs: each clear frees one lane and is matched by
// the fresher candidate that caused it, which is still a candidate in round 2,
// so round 2 allocates at least the cleared count.
struct ResidualOfferMergePlan {
  const uint8_t* bucket = nullptr;
  __m512i index;
  uint64_t mask = 0;
  size_t lines = 0;

  __m512i Apply(__m512i dst, size_t line) const {
    if (line >= lines) return dst;  // public payload/tag boundary
    return _mm512_maskz_permutex2var_epi8(
        _cvtu64_mask64(mask), core::obliPin512(dst), index,
        core::obliLoad512(bucket + line * kBucketCapacity));
  }

  // The plan applied in place, for an offer that is not riding a pass with a
  // payload loop of its own.
  void ApplyTo(uint8_t* mbucket) const {
    for (size_t line = 0; line < lines; ++line) {
      const size_t off = line * kBucketCapacity;
      _mm512_store_si512(reinterpret_cast<void*>(mbucket + off),
                         Apply(core::obliLoad512(mbucket + off), line));
    }
  }
};

// The rule is a template parameter so that each rule's plan holds only its
// own work: kNoDedup has no intersect, and a rule with one class skips the
// other class's round, which is publicly empty (a round that allocates
// nothing leaves the index as it was).
template <ResidualDedupRule Rule>
inline ResidualOfferMergePlan PlanResidualOfferMerge(
    const uint8_t* main_keys, uint64_t main_mask, size_t key_bytes,
    TableView range, const ResidualRangePlan& plan, size_t lines, size_t b,
    size_t g) {
  // One sub-table is 2^range_bits buckets, so the pairing needs no divide.
  assert(plan.range_buckets == plan.groups << plan.range_bits);
  const size_t r = (g << plan.range_bits) + (b >> plan.index_bits);
  const uint8_t* bucket = range.data + r * range.layout.BucketBytes();
  const size_t want = b & ((size_t{1} << plan.index_bits) - 1);
  uint64_t cand = ResidualOfferCandidates(range, bucket, range.masks[r],
                                          plan, want);
  // `clear` are main lanes a fresher candidate resolves away, `drop`
  // candidates the table's fresher copy consumes, and `fresh` the candidates
  // that take the kResidualWins rule -- all of them under that rule, the
  // class-marked ones under kClassMark, none under the other two.
  uint64_t clear = 0, drop = 0, fresh = 0;
  if constexpr (Rule == ResidualDedupRule::kResidualWins) {
    fresh = cand;
    clear = CrossBucketDuplicateMask(bucket, cand, main_keys, main_mask,
                                     key_bytes);
  } else if constexpr (Rule == ResidualDedupRule::kTableWins) {
    drop = CrossBucketDuplicateMask(main_keys, main_mask, bucket, cand,
                                    key_bytes);
  } else if constexpr (Rule == ResidualDedupRule::kClassMark) {
    const __m512i cls = core::obliLoad512(
        bucket + range.layout.MetaLine() * kBucketCapacity);
    fresh = cand & core::obliTestMask8(
                       cls, _mm512_set1_epi8(
                                static_cast<char>(kMetaResidualClass)));
    CrossBucketClassDuplicateMasks(main_keys, main_mask, bucket, cand & ~fresh,
                                   fresh, key_bytes, &clear, &drop);
  } else {
    (void)main_keys;
    (void)key_bytes;
  }
  __m512i index = IotaBytes();
  uint64_t occupied = main_mask & ~clear;
  uint64_t take_stale = 0, take_fresh = 0;
  // Round 1: the staler class, into the lanes that were free BEFORE any clear.
  if constexpr (Rule != ResidualDedupRule::kResidualWins) {
    const uint64_t stale = cand & ~fresh & ~drop;
    const unsigned free_stale =
        static_cast<unsigned>(kBucketCapacity) - Popcount64(main_mask);
    const unsigned alloc_stale = std::min(Popcount64(stale), free_stale);
    const uint64_t used_stale = _pdep_u64(LowMask64(alloc_stale), ~main_mask);
    take_stale = _pdep_u64(LowMask64(alloc_stale), stale);
    index = BuildMergeIndex(used_stale, take_stale);
    occupied |= used_stale;
  }
  // Round 2: the fresher class, into what round 1 left plus what it cleared.
  if constexpr (Rule == ResidualDedupRule::kResidualWins ||
                Rule == ResidualDedupRule::kClassMark) {
    const unsigned free_fresh =
        static_cast<unsigned>(kBucketCapacity) - Popcount64(occupied);
    const unsigned alloc_fresh = std::min(Popcount64(fresh), free_fresh);
    const uint64_t used_fresh = _pdep_u64(LowMask64(alloc_fresh), ~occupied);
    take_fresh = _pdep_u64(LowMask64(alloc_fresh), fresh);
    index = BuildMergeIndexOnto(index, used_fresh, take_fresh);
    occupied |= used_fresh;
  }
  // The consumed candidates leave the range table along with the absorbed
  // ones, so neither is carried over as a leftover.
  range.masks[r] &= ~(drop | take_stale | take_fresh);
  return {bucket, index, occupied, lines};
}

// The same, with the rule chosen at run time: one public branch per offer.
inline ResidualOfferMergePlan PlanResidualOfferMerge(
    const uint8_t* main_keys, uint64_t main_mask, size_t key_bytes,
    TableView range, const ResidualRangePlan& plan, ResidualDedupRule rule,
    size_t lines, size_t b, size_t g) {
  switch (rule) {
    case ResidualDedupRule::kNoDedup:
      return PlanResidualOfferMerge<ResidualDedupRule::kNoDedup>(
          main_keys, main_mask, key_bytes, range, plan, lines, b, g);
    case ResidualDedupRule::kResidualWins:
      return PlanResidualOfferMerge<ResidualDedupRule::kResidualWins>(
          main_keys, main_mask, key_bytes, range, plan, lines, b, g);
    case ResidualDedupRule::kTableWins:
      return PlanResidualOfferMerge<ResidualDedupRule::kTableWins>(
          main_keys, main_mask, key_bytes, range, plan, lines, b, g);
    case ResidualDedupRule::kClassMark:
      break;
  }
  return PlanResidualOfferMerge<ResidualDedupRule::kClassMark>(
      main_keys, main_mask, key_bytes, range, plan, lines, b, g);
}

// One unit of the standalone sweep: offer range bucket
// `(g << range_bits) + (b >> index_bits)`'s candidates that name main bucket
// `b`, under `Rule`, moving `lines` byte lines.  The fused forms differ only
// in applying the same plan inside the routing pass's own payload loop.
template <ResidualDedupRule Rule>
inline void OfferResidualsToBucket(TableView main, TableView range,
                                   const ResidualRangePlan& plan, size_t lines,
                                   size_t b, size_t g) {
  uint8_t* mbucket = main.data + b * main.layout.BucketBytes();
  const ResidualOfferMergePlan merge = PlanResidualOfferMerge<Rule>(
      mbucket, main.masks[b], main.layout.key_bytes, range, plan, lines, b, g);
  merge.ApplyTo(mbucket);
  main.masks[b] = merge.mask;
}

inline void OfferResidualsToBucket(TableView main, TableView range,
                                   const ResidualRangePlan& plan,
                                   ResidualDedupRule rule, size_t lines,
                                   size_t b, size_t g) {
  switch (rule) {
    case ResidualDedupRule::kNoDedup:
      OfferResidualsToBucket<ResidualDedupRule::kNoDedup>(main, range, plan,
                                                          lines, b, g);
      return;
    case ResidualDedupRule::kResidualWins:
      OfferResidualsToBucket<ResidualDedupRule::kResidualWins>(
          main, range, plan, lines, b, g);
      return;
    case ResidualDedupRule::kTableWins:
      OfferResidualsToBucket<ResidualDedupRule::kTableWins>(main, range, plan,
                                                            lines, b, g);
      return;
    case ResidualDedupRule::kClassMark:
      OfferResidualsToBucket<ResidualDedupRule::kClassMark>(main, range, plan,
                                                            lines, b, g);
      return;
  }
}

// The standalone sweep, over the (bucket, group) unit space.  `Rule` is a
// template parameter so that a caller which knows its rule gets the
// specialization -- kNoDedup in particular has no intersect at all; the body
// is the one offer above either way.
template <ResidualDedupRule Rule>
inline void ResidualSecondChanceSweepRange(TableView main, TableView range,
                                           const ResidualRangePlan& plan,
                                           size_t lines, size_t begin,
                                           size_t end) {
  assert(plan.range_buckets == plan.groups << plan.range_bits);
  assert(main.num_buckets <= (size_t{1} << (plan.range_bits + plan.index_bits)));
  assert(end <= main.num_buckets * plan.groups);

  // Carry the (bucket, group) pair rather than dividing per unit: groups is 1
  // on every table large enough to matter, where this is a plain b loop.
  size_t b = begin / plan.groups;
  size_t g = begin % plan.groups;
  for (size_t u = begin; u < end; ++u) {
    OfferResidualsToBucket<Rule>(main, range, plan, lines, b, g);
    if (++g == plan.groups) {
      g = 0;
      ++b;
    }
  }
}

template <ResidualDedupRule Rule>
inline void ResidualSecondChanceSweep(TableView main, TableView range,
                                      const ResidualRangePlan& plan,
                                      size_t lines) {
  ResidualSecondChanceSweepRange<Rule>(main, range, plan, lines, 0,
                                       main.num_buckets * plan.groups);
}

// The same, with the rule chosen at run time.  The subtask dispatcher
// (RunSubtask) runs a plan of subtasks and picks the rule per PASS (a block
// is re-offered its own residuals under kNoDedup, the end of the network runs
// kResidualWins), so it cannot template on it the way the monolithic network
// does.  Each arm is still the compile-time specialization.
inline void ResidualSecondChanceSweepRangeDynamic(
    ResidualDedupRule rule, TableView main, TableView range,
    const ResidualRangePlan& plan, size_t lines, size_t begin, size_t end) {
  switch (rule) {
    case ResidualDedupRule::kNoDedup:
      ResidualSecondChanceSweepRange<ResidualDedupRule::kNoDedup>(
          main, range, plan, lines, begin, end);
      return;
    case ResidualDedupRule::kResidualWins:
      ResidualSecondChanceSweepRange<ResidualDedupRule::kResidualWins>(
          main, range, plan, lines, begin, end);
      return;
    case ResidualDedupRule::kTableWins:
      ResidualSecondChanceSweepRange<ResidualDedupRule::kTableWins>(
          main, range, plan, lines, begin, end);
      return;
    case ResidualDedupRule::kClassMark:
      ResidualSecondChanceSweepRange<ResidualDedupRule::kClassMark>(
          main, range, plan, lines, begin, end);
      return;
  }
}

// One second chance riding another pass: the range table and rule of a pass
// whose offers are FUSED into the routing pass that already read-modify-writes
// every output bucket, instead of running as a standalone sweep.
struct ResidualOfferSet {
  TableView range;
  ResidualRangePlan plan;
  ResidualDedupRule rule = ResidualDedupRule::kNoDedup;
  size_t lines = 0;
};

// THE GROUPS OF ONE OFFER SET, CHAINED.  A set whose plan has several groups
// -- a stacked range table, or a DFS leaf of several pages -- offers main
// bucket b every group in order, and group g must see the keys and the
// occupancy group g-1 left.  Planned one after another against a copy of the
// bucket's key lines, then applied together in one pass over its lines, that
// is byte for byte the sequence of single offers; the bucket's payload is
// read and written once instead of once per group.  Several sets chain the
// same way, set after set (MergeBucketWithResidualOffers).
// A tuple of the fused radix pass holds r chains, so its fast path takes the
// short ones; a single bucket's offer chains up to 16 (a direct plan's pool).
inline constexpr size_t kMaxChainedOfferGroups = 4;
inline constexpr size_t kMaxBucketChainedOfferGroups = 16;

template <size_t MaxPlans = kMaxChainedOfferGroups>
struct ChainedResidualOffer {
  ResidualOfferMergePlan plans[MaxPlans];
  size_t count = 0;
  uint64_t mask = 0;

  // `keys` holds the bucket's key lines (unread under kNoDedup) and is
  // brought up to date through every group but the last.
  void Plan(const ResidualOfferSet& offer, uint8_t* keys, uint64_t main_mask,
            size_t key_bytes, size_t b) {
    Start(main_mask);
    Append(offer, offer.rule, keys, key_bytes, b, /*keys_read_later=*/false);
  }

  void Start(uint64_t main_mask) {
    count = 0;
    mask = main_mask;
  }

  // Every group of `offer`, under `rule`, planned after the plans already
  // held.  `keys` is brought up to date through each plan that a later one
  // reads it after: every group when `keys_read_later` (a later set reads
  // it), else every group but the last unless the rule is kNoDedup.
  void Append(const ResidualOfferSet& offer, ResidualDedupRule rule,
              uint8_t* keys, size_t key_bytes, size_t b,
              bool keys_read_later) {
    switch (rule) {
      case ResidualDedupRule::kNoDedup:
        AppendRule<ResidualDedupRule::kNoDedup>(offer, keys, key_bytes, b,
                                                keys_read_later);
        return;
      case ResidualDedupRule::kResidualWins:
        AppendRule<ResidualDedupRule::kResidualWins>(offer, keys, key_bytes,
                                                     b, keys_read_later);
        return;
      case ResidualDedupRule::kTableWins:
        AppendRule<ResidualDedupRule::kTableWins>(offer, keys, key_bytes, b,
                                                  keys_read_later);
        return;
      case ResidualDedupRule::kClassMark:
        AppendRule<ResidualDedupRule::kClassMark>(offer, keys, key_bytes, b,
                                                  keys_read_later);
        return;
    }
  }

  template <ResidualDedupRule Rule>
  void AppendRule(const ResidualOfferSet& offer, uint8_t* keys,
                  size_t key_bytes, size_t b, bool keys_read_later) {
    const size_t groups = offer.plan.groups;
    assert(count + groups <= MaxPlans);
    for (size_t g = 0; g < groups; ++g) {
      ResidualOfferMergePlan& plan = plans[count++];
      plan = PlanResidualOfferMerge<Rule>(keys, mask, key_bytes, offer.range,
                                          offer.plan, offer.lines, b, g);
      mask = plan.mask;
      if (!keys_read_later &&
          (g + 1 == groups || Rule == ResidualDedupRule::kNoDedup)) {
        continue;
      }
      for (size_t line = 0; line < key_bytes; ++line) {
        uint8_t* p = keys + line * kBucketCapacity;
        _mm512_store_si512(reinterpret_cast<void*>(p),
                           plan.Apply(core::obliLoad512(p), line));
      }
    }
  }

  __m512i Apply(__m512i value, size_t line) const {
    for (size_t i = 0; i < count; ++i) value = plans[i].Apply(value, line);
    return value;
  }
};

// Every group of `offer` for main bucket b: chained when it has several and
// they fit, else one full offer per group, which is the same result.
inline void OfferResidualGroupsToBucket(const ResidualOfferSet& offer,
                                        TableView main, size_t b) {
  const size_t groups = offer.plan.groups;
  if (groups == 1 || groups > kMaxBucketChainedOfferGroups) {
    for (size_t g = 0; g < groups; ++g) {
      OfferResidualsToBucket(main, offer.range, offer.plan, offer.rule,
                             offer.lines, b, g);
    }
    return;
  }
  uint8_t* mbucket = main.data + b * main.layout.BucketBytes();
  const size_t key_bytes = main.layout.key_bytes;
  alignas(64) uint8_t keys[kMaxKeyBytes * kBucketCapacity];
  if (offer.rule != ResidualDedupRule::kNoDedup) {
    std::memcpy(keys, mbucket, key_bytes * kBucketCapacity);
  }
  ChainedResidualOffer<kMaxBucketChainedOfferGroups> chain;
  chain.Plan(offer, keys, main.masks[b], key_bytes, b);
  for (size_t line = 0; line < offer.lines; ++line) {
    uint8_t* p = mbucket + line * kBucketCapacity;
    _mm512_store_si512(reinterpret_cast<void*>(p),
                       chain.Apply(core::obliLoad512(p), line));
  }
  main.masks[b] = chain.mask;
}

// The cross-source level with the second chances fused in: after each pair's
// dedup-and-MergeSplit, every offer set is run against both output buckets,
// in set order, while the buckets are still cache-resident.
//
// Equivalence to the standalone sweeps it replaces: a bucket reaches its
// final content the moment its own pair is merged, and an offer touches only
// its bucket and that bucket's range bucket, so per BUCKET the fused offer
// sees exactly what a post-pass sweep would have seen.  The one divergence is
// WHICH candidate wins when two main buckets sharing a range bucket compete
// for the same free slot -- pair order instead of bucket order -- which only
// redistributes absorptions; leftovers stay duplicate-free either way.
//
// The rule-validity arguments carry over unchanged: kTableWins (the carry) is
// exact against a merged pair -- T_j's side is strictly fresher and L_j's is
// the carry's own block -- and kResidualWins (the tier) is exact because a
// tier never duplicates its own table and every other entry here is staler.
// With SPLIT offer sets, offer order per bucket is the pass order (carry,
// then tier), so a carry copy absorbed first still loses to the fresher tier
// copy that meets it; the MERGED set (kClassMark) has no such order and
// leans on the pass's pool dedup having removed the carry copy before the
// scatter instead.
template <bool CheckOverflow = false>
inline bool CrossSourceLevelDedupOffers(TableView t, unsigned bit,
                                        ResidualStash& stash,
                                        const ResidualOfferSet* offers,
                                        size_t num_offers, size_t begin,
                                        size_t end) {
  const size_t half = size_t{1} << bit;
  assert(end <= half && t.num_buckets >= 2 * half);
  const size_t bucket_bytes = t.layout.BucketBytes();
  const size_t lines = t.layout.RoutedLines(bit);
  const size_t tag_line = t.layout.TagLine(bit);
  const size_t key_bytes = t.layout.key_bytes;
  for (size_t i = begin; i < end; ++i) {
    if (!MergeSplitPairDedupStash<CheckOverflow>(
            t.data + i * bucket_bytes, t.data + (i + half) * bucket_bytes,
            &t.masks[i], &t.masks[i + half], key_bytes, lines, tag_line, bit,
            stash)) {
      return false;
    }
    for (size_t o = 0; o < num_offers; ++o) {
      OfferResidualGroupsToBucket(offers[o], t, i);
    }
    for (size_t o = 0; o < num_offers; ++o) {
      OfferResidualGroupsToBucket(offers[o], t, i + half);
    }
  }
  return true;
}

// The LAST level of a block's own butterfly with pass 0's offer fused in:
// the pairs (i, i + 2^bit) of tag bit
// `bit` over `t` -- the plain load-0.5 MergeSplit, no dedup prologue, exactly
// what the butterfly recursion would have run for this level -- followed by
// the offer against both output buckets while they are cache-resident.  The
// range table was built BEFORE this level, from the sheds of levels [0, bit)
// plus the source's tier, so per bucket the offer sees exactly what the
// standalone post-butterfly sweep it replaces would have seen; the one
// divergence is which candidate wins when two buckets sharing a range bucket
// compete for a scarce free slot (pair order instead of index order), which
// is public and only redistributes absorptions.
//
// What about entries shed AT this level?  They are provably unabsorbable and
// go straight to the drain (the pass marks its own last-level stash
// drain-only): a last-level shed's target bucket was FULL at the moment of
// the shed, offers never take a full bucket below full (every clear is
// matched by an insert -- see PlanResidualOfferMerge), and under kNoDedup an
// absorption needs a free slot outright -- so re-offering one is fixed work
// that provably absorbs nothing, which is also what the standalone sweep
// would do with them: they become carry leftovers either way.
// And a drained one is never a duplicate of the published block: a shed MOVES
// an entry out of a source that holds each key at most once (the block plus
// its tier, disjoint by "leftovers are never duplicates").
//
// kNoDedup stays exact throughout the level: the candidates (earlier levels'
// sheds and the tier) and the block's remaining content partition one
// duplicate-free union, so no candidate can meet a duplicate in any bucket at
// any point of the pass, whatever the absorption order.
template <bool CheckOverflow = false>
inline bool ButterflyLevelOffersRange(TableView t, unsigned bit,
                                      ResidualStash& stash,
                                      const ResidualOfferSet& offer,
                                      size_t begin, size_t end) {
  const size_t half = size_t{1} << bit;
  assert(end <= half && t.num_buckets == 2 * half);
  const size_t bucket_bytes = t.layout.BucketBytes();
  const size_t lines = t.layout.RoutedLines(bit);
  const size_t tag_line = t.layout.TagLine(bit);
  for (size_t i = begin; i < end; ++i) {
    if (!MergeSplitPairStash<CheckOverflow>(
            t.data + i * bucket_bytes, t.data + (i + half) * bucket_bytes,
            &t.masks[i], &t.masks[i + half], lines, tag_line, bit, stash)) {
      return false;
    }
    OfferResidualGroupsToBucket(offer, t, i);
    OfferResidualGroupsToBucket(offer, t, i + half);
  }
  return true;
}

// The mixed-radix pass with the finalizing offers fused in: per stride tuple
// the r-1 ordered dedup clears (Dedup = the absorb's RadixPassDedupStashRange;
// false is the fixed preparation's plain RadixPassStashRange), the r-way
// MergeSplit, then every offer set against each of the tuple's r output
// buckets, in set order, while they are cache-resident.
//
// Equivalence to the standalone sweep it replaces is the cross level's
// argument: the radix pass is the LAST routing step, so a bucket is final the
// moment its tuple has merged, an offer reads nothing but that bucket and its
// range bucket, and the only divergence is which candidate wins a scarce free
// slot among buckets sharing a range bucket (tuple order rather than index
// order), which is public and only redistributes absorptions.
//
// What the pass itself sheds is drain-only, by the lemma at
// DrainResidualPoolRange: its target bucket was full and duplicate-free at
// the shed, and no offer ever takes a full bucket below full.  Unlike a chain
// step's cross shed, though, the radix shed is not one freshness class -- at
// an absorb it holds T_t-class and L_t^old-class entries alike -- so a shed
// entry and a range-table leftover of the same key can BOTH survive to the
// drain.  ResidualLeftoverDedupRange is the pass that resolves those, and a
// fused final pass must plan it whenever its ranks say a drain-only slot is
// fresher than a swept one (ResidualLeftoverDedupNeeded).
//
// Ranged over TUPLE index like the unfused passes, so disjoint ranges touch
// disjoint buckets of every block.
struct RadixResidualOutput {
  // Not an aggregate: the chains are filled by Prepare, and value-initializing
  // them would clear every plan once per tuple.
  RadixResidualOutput(const ResidualOfferSet& o, size_t b, size_t t, size_t k)
      : offer(o), block(b), tuple(t), key_bytes(k) {}

  const ResidualOfferSet& offer;
  size_t block, tuple, key_bytes;
  ChainedResidualOffer<> tails[kMaxRadix];

  template <unsigned R, typename Fill>
  void Prepare(uint64_t* masks, Fill&& fill) {
    alignas(64) uint8_t keys[R][kMaxKeyBytes * kBucketCapacity];
    if (offer.rule != ResidualDedupRule::kNoDedup) {
      for (size_t line = 0; line < key_bytes; ++line) {
        __m512i output[R];
        fill(line, output);
        for (unsigned q = 0; q < R; ++q) {
          _mm512_store_si512(
              reinterpret_cast<void*>(keys[q] + line * kBucketCapacity),
              output[q]);
        }
      }
    }
    // Candidate consumption follows the original q-major offer order, even
    // when several tuple outputs share a range bucket; a set's groups follow
    // in order within each output (ChainedResidualOffer).
    for (unsigned q = 0; q < R; ++q) {
      tails[q].Plan(offer, keys[q], masks[q], key_bytes, q * block + tuple);
      masks[q] = tails[q].mask;
    }
  }

  __m512i Apply(unsigned q, __m512i value, size_t line) const {
    return tails[q].Apply(value, line);
  }
};

template <bool Dedup, bool CheckOverflow = false>
inline bool RadixPassOffersRange(TableView t, unsigned block_bits, unsigned r,
                                 ResidualStash& stash,
                                 const ResidualOfferSet* offers,
                                 size_t num_offers, size_t begin, size_t end) {
  assert(r >= 2 && r <= kMaxRadix);
  const size_t block = size_t{1} << block_bits;
  assert(t.num_buckets == block * r);
  const size_t bucket_bytes = t.layout.BucketBytes();
  const size_t digit_line = t.layout.DigitLine();
  const size_t lines = t.layout.PayloadLines();
  const size_t key_bytes = t.layout.key_bytes;
  uint8_t* bptr[kMaxRadix];
  uint64_t* mptr[kMaxRadix];
  for (size_t p = begin; p < end; ++p) {
    for (unsigned q = 0; q < r; ++q) {
      bptr[q] = t.data + (q * block + p) * bucket_bytes;
      mptr[q] = &t.masks[q * block + p];
    }
    if constexpr (Dedup) {
      // Bucket 0 is the fresher operand (see RadixPassDedupStashRange).
      DedupBucketDestinations(bptr[0], *mptr[0], bptr + 1, mptr + 1,
                               r - 1, key_bytes);
    }
    if (num_offers == 1 && offers[0].plan.groups <= kMaxChainedOfferGroups) {
      RadixResidualOutput finish(offers[0], block, p, key_bytes);
      if (!MergeSplitRadixStash<CheckOverflow>(
              bptr, mptr, r, lines, digit_line, t.layout.digit_bits, stash,
              finish)) return false;
      continue;
    }
    if (!MergeSplitRadixStash<CheckOverflow>(bptr, mptr, r, lines, digit_line,
                                             t.layout.digit_bits, stash)) {
      return false;
    }
    for (unsigned q = 0; q < r; ++q) {
      for (size_t o = 0; o < num_offers; ++o) {
        OfferResidualGroupsToBucket(offers[o], t, q * block + p);
      }
    }
  }
  return true;
}

// The fixed level's merge with the finalizing offers fused in
// (MergeRadixLevelSourcesRange, which at r = 1 is MergeFixedLevelSourcesRange
// exactly): B's bucket i dedup-and-merged into each of its r destinations in C,
// each destination then offered every set in set order.  C's bucket is final
// the moment B's direction-q entries have merged into it, so per bucket the
// offer sees what a standalone post-merge sweep would see.  The merge shed is
// drain-only (it sheds from B against a full, already-deduplicated C bucket)
// and is B-class throughout, so its only same-key conflicts are with the
// staler carry class in the range table -- ResidualLeftoverDedupRange again.
//
// B stays live in the old probe plan until publication, so each merge takes a
// COPY of B's mask restricted to its direction, exactly as the unfused kernel
// does.
//
// At the top (kAll) the leftover-dedup argument above is moot:
// ResolveTopDestination, below, removes every older copy of B's keys and
// every tombstone before the merge, so no shed shares a key with a leftover.
//
// THE TOP'S RESOLUTION (FixedMergeTombstones::kAll): every freshness and
// tombstone decision for destination `ci`, made on keys and private masks
// BEFORE its first capacity decision -- the merge of B's direction into C[ci]
// and the offers after it.  REPORT.tex, Lemma "resolved-compression", is the
// contract: resolve every version, remove a winning tombstone together with
// what it shadows, then compress.  Afterwards C[ci], B's live direction and
// every candidate naming ci are distinct live winners, so nothing that runs
// later frees a main slot: a shed or a leftover targets a full home, and the
// home emits exactly (X_ci - 64)+ (DrainResidualTableRange's identity).
//
// What it resolves, against the complete sources of the top's one merge:
//   (a) older-class candidates (the preparation's retained carry: the
//       unmarked class of a kClassMark set, or a whole kTableWins/kNoDedup
//       set) against B's keys in this direction, live replacements and
//       tombstones alike -- `direction` includes the unshadowed tombstones
//       the merge skips unconditionally;
//   (b) C[ci]'s copies of fresher-class candidates (B's tier), which the
//       offer would otherwise clear only after the merge had already shed;
//   (c) every tombstone candidate, once (a) and (b) have run: a B-tier
//       tombstone has cleared C's copy and the pool dedup cleared the retained
//       carry's before the range build; an older one has nothing staler left;
//   (d) C[ci]'s own tombstones.  A is tombstone-free (the previous top merge
//       dropped them all), so this removes nothing on an engine history; it
//       makes the rule independent of that premise.
// C's copies of B's main keys were cleared by MergeRadixSourceBucket's dedup
// before this runs, and B's main tombstones leave the merge right after it.
// FIFO consumption is what makes dropping legal: nothing older than A and
// this carry is live.  B's main and tier are disjoint, as every published
// table's are; the retained carry and B's tier were resolved by the pool
// dedup before the scatter.
//
// All groups (range pages) of every offer set are resolved before any is
// allocated.  B is published and only read; C and the range masks are
// private, and the lane fold ANDs range masks, which only lose bits here.
// Each visit touches the same public buckets whatever the masks hold.
inline void ResolveTopDestination(const ResidualOfferSet* offers,
                                  size_t num_offers, size_t ci,
                                  const uint8_t* src, uint64_t direction,
                                  const uint8_t* dst, uint64_t* dst_mask,
                                  const Layout& layout) {
  const size_t key_bytes = layout.key_bytes;
  const size_t meta = layout.MetaLine();
  *dst_mask &= ~ErasedSlotMask(dst, meta);
  for (size_t o = 0; o < num_offers; ++o) {
    const ResidualOfferSet& offer = offers[o];
    assert(offer.plan.range_buckets == offer.plan.groups
                                           << offer.plan.range_bits);
    const size_t want = ci & ((size_t{1} << offer.plan.index_bits) - 1);
    for (size_t g = 0; g < offer.plan.groups; ++g) {
      const size_t r =
          (g << offer.plan.range_bits) + (ci >> offer.plan.index_bits);
      const uint8_t* bucket =
          offer.range.data + r * offer.range.layout.BucketBytes();
      const uint64_t cand = ResidualOfferCandidates(
          offer.range, bucket, offer.range.masks[r], offer.plan, want);
      uint64_t fresh = 0;
      if (offer.rule == ResidualDedupRule::kResidualWins) {
        fresh = cand;
      } else if (offer.rule == ResidualDedupRule::kClassMark) {
        fresh = cand & core::obliTestMask8(
                           core::obliLoad512(bucket + meta * kBucketCapacity),
                           _mm512_set1_epi8(
                               static_cast<char>(kMetaResidualClass)));
      }
      const uint64_t stale = CrossBucketDuplicateMask(
          src, direction, bucket, cand & ~fresh, key_bytes);
      *dst_mask &=
          ~CrossBucketDuplicateMask(bucket, fresh, dst, *dst_mask, key_bytes);
      offer.range.masks[r] &= ~(stale | (cand & ErasedSlotMask(bucket, meta)));
    }
  }
}

// The sheds of one source bucket's directions.  They all come from the same
// source line, so the stash takes them together, one permute per stash
// bucket and line, in the pass of the LAST direction, planned where appending
// them one direction at a time would have put them
// (PlanStashMergePermuteRounds).  B is published and only read, so its lines
// are the same then as at each direction's own merge.
struct FixedMergeSheds {
  uint64_t masks[kMaxFixedMergeWays];
  unsigned ways = 1;
  unsigned merged = 0;
};

// One destination of the fixed merge with every offer after it, in ONE pass
// over the destination's lines: B's direction merged into it, then every
// group of every set in set order (as kNoDedup once the top has resolved),
// each planned against a scratch copy of the key lines the plan before it
// left (ChainedResidualOffer).  Plans read only those key lines, the range
// buckets and masks, so this is byte for byte MergeBucketIntoWithStash
// followed by one offer per (set, group); the payload is read and written
// once instead of once per plan.  Each plan keeps its own set's rule and
// allocation rounds.  The chain must hold every plan
// (MergeFixedLevelSourcesOffersRange checks).
template <bool CheckOverflow>
inline bool MergeBucketWithResidualOffers(uint8_t* dst, const uint8_t* src,
                                          uint64_t* dst_mask,
                                          uint64_t src_real,
                                          const Layout& layout,
                                          ResidualStash& stash,
                                          FixedMergeSheds& sheds,
                                          const ResidualOfferSet* offers,
                                          size_t num_offers, bool resolved,
                                          size_t b) {
  const uint64_t dst_real = *dst_mask;
  const unsigned alloc = std::min(Popcount64(src_real),
                                  64u - Popcount64(dst_real));
  const uint64_t used = _pdep_u64(LowMask64(alloc), ~dst_real);
  const uint64_t taken = _pdep_u64(LowMask64(alloc), src_real);
  assert(sheds.merged < sheds.ways);
  sheds.masks[sheds.merged++] = src_real & ~taken;
  assert(CheckOverflow || stash.num_buckets > 0);
  StashPermutePlan shed_plan;  // empty except at the last direction
  if (sheds.merged == sheds.ways) {
    if constexpr (CheckOverflow) {
      size_t shed_count = 0;
      for (unsigned q = 0; q < sheds.ways; ++q) {
        shed_count += Popcount64(sheds.masks[q]);
      }
      if (stash.Count() + shed_count > stash.Capacity()) return false;
    }
    PlanStashMergePermuteRounds(stash, sheds.masks, sheds.ways, &shed_plan);
  }
  const __m512i index = BuildMergeIndex(used, taken);
  const uint64_t merged_mask = dst_real | used;
  const __mmask64 keep = _cvtu64_mask64(merged_mask);
  // The sets up to the last one whose plans read key lines: the scratch is
  // built, and kept up to date, only while a later plan will read it.
  size_t readers = 0;
  for (size_t o = 0; o < num_offers; ++o) {
    // The one line loop is the merge's; an offer moves no line past it.
    assert(offers[o].lines <= layout.PayloadLines());
    if (!resolved && offers[o].rule != ResidualDedupRule::kNoDedup) {
      readers = o + 1;
    }
  }
  alignas(64) uint8_t keys[kMaxKeyBytes * kBucketCapacity];
  if (readers != 0) {
    for (size_t line = 0; line < layout.key_bytes; ++line) {
      const size_t off = line * kBucketCapacity;
      _mm512_store_si512(reinterpret_cast<void*>(keys + off),
          _mm512_maskz_permutex2var_epi8(keep, core::obliLoad512(dst + off),
                                         index, core::obliLoad512(src + off)));
    }
  }
  ChainedResidualOffer<kMaxBucketChainedOfferGroups> tail;
  tail.Start(merged_mask);
  for (size_t o = 0; o < num_offers; ++o) {
    tail.Append(offers[o],
                resolved ? ResidualDedupRule::kNoDedup : offers[o].rule, keys,
                layout.key_bytes, b, o + 1 < readers);
  }
  for (size_t line = 0; line < layout.PayloadLines(); ++line) {
    const size_t off = line * kBucketCapacity;
    const __m512i original_src = core::obliLoad512(src + off);
    const __m512i original_dst = core::obliLoad512(dst + off);
    ApplyStashPermuteLineAtOffset(stash, shed_plan, off, original_src);
    const __m512i merged = _mm512_maskz_permutex2var_epi8(
        keep, original_dst, index, original_src);
    _mm512_store_si512(reinterpret_cast<void*>(dst + off),
                       tail.Apply(merged, line));
  }
  *dst_mask = tail.mask;
  return true;
}

// The direction split, the ordered clears and the private per-direction masks
// are MergeRadixSourceBucket's, shared with the unfused twin: the ONLY thing
// this adds is what happens to a destination bucket once B's entries for it
// have been selected.  `retag` is that twin's too (the level arena's top),
// and reaches here for the same reason -- the shape of the sweep does
// not depend on whether a pass is riding it.
//
// A destination's merge and offers run as one pass over its lines
// (MergeBucketWithResidualOffers), and a source bucket's sheds enter the
// stash once, at its last direction; a shape too wide for one chain runs the
// merge, then each set's offers, as separate passes -- the same bytes.
//
// Under kAll -- the level arena's top, where every staler pass rides this
// sweep (RunSubtask checks) -- ResolveTopDestination makes every freshness
// and tombstone decision for a destination before its merge and offers, and
// every B tombstone is then left out.  No branch or memory address depends
// on any mask.
template <bool CheckOverflow = false>
inline bool MergeFixedLevelSourcesOffersRange(
    TableView older, TableView fresher, unsigned r, ResidualStash& stash,
    const ResidualOfferSet* offers, size_t num_offers, size_t begin,
    size_t end, FixedMergeTombstones skip = FixedMergeTombstones::kMerge,
    const FixedMergeRetag* retag = nullptr) {
  assert(r >= 1 && r <= kMaxFixedMergeWays);
  const size_t block = fresher.num_buckets;
  assert(older.num_buckets == block * r);
  assert(end <= block);
  const size_t bucket_bytes = older.layout.BucketBytes();
  const size_t lines = older.layout.PayloadLines();
  const bool resolved = skip == FixedMergeTombstones::kAll;
  // Whether one pass per destination holds its merge and every offer: the
  // chain must hold every (set, group) plan and no offer may move a line
  // past the payload.  Public, and the same for every destination.
  size_t plans = 0;
  bool chained = true;
  for (size_t o = 0; o < num_offers; ++o) {
    plans += offers[o].plan.groups;
    chained = chained && offers[o].lines <= lines;
  }
  chained = chained && plans <= kMaxBucketChainedOfferGroups;
  for (size_t i = begin; i < end; ++i) {
    const uint8_t* b = fresher.data + i * bucket_bytes;
    FixedMergeSheds sheds;
    sheds.ways = r;
    const bool ok = MergeRadixSourceBucket(
        older, b, fresher.masks[i],
        FixedMergeSourceDigits(b, older.layout, r, retag), r, block, i, skip,
        [&](uint8_t* c, const uint8_t* src, uint64_t* dst_mask,
            uint64_t src_mask, uint64_t shadowing, uint64_t direction,
            size_t ci) {
          if (resolved) {
            ResolveTopDestination(offers, num_offers, ci, src, direction, c,
                                  dst_mask, older.layout);
            src_mask &= ~shadowing;
          }
          // RESOLVED, THE OFFERS NEED NO DEDUP.  No candidate naming ci now
          // shares a key with C[ci] (A is distinct, and (b) cleared C's
          // copies of B's tier), with an entry of B merged into it or shed
          // from it ((a) removed the retained copies of every key of B's
          // direction; B's main and tier are disjoint), or with another
          // candidate (the pool dedup).  So the class-marked dedup would
          // find nothing and clear no lane, and allocating every candidate
          // in one round is the same capacity decision.  The staler-first
          // rule it keeps elsewhere guards exactly the case (a) removed: a
          // staler copy of a shed key absorbed past the leftover dedup.
          if (chained) {
            return MergeBucketWithResidualOffers<CheckOverflow>(
                c, src, dst_mask, src_mask, older.layout, stash, sheds, offers,
                num_offers, resolved, ci);
          }
          if (!MergeBucketIntoWithStash<CheckOverflow>(c, src, dst_mask,
                                                       &src_mask, lines,
                                                       stash)) {
            return false;
          }
          for (size_t o = 0; o < num_offers; ++o) {
            ResidualOfferSet set = offers[o];
            if (resolved) set.rule = ResidualDedupRule::kNoDedup;
            OfferResidualGroupsToBucket(set, older, ci);
          }
          return true;
        });
    if (!ok) return false;
  }
  return true;
}

// The LEFTOVER dedup of a fused final pass: the range table's leftovers
// against the pass's drain-only stash buckets, both of which are about to
// drain into one published tier and so must be duplicate-free against each
// other.
//
// Why the pool dedup cannot do this.  Its post-pass emission (kDrainOnly)
// clears DRAIN-ONLY lanes that duplicate a fresher swept slot, reading the
// swept slot's STASH -- which still holds everything it offered, since the
// scatter copies rather than consumes.  That covers a shed copy that is
// staler than a swept one.  The other direction -- a shed copy FRESHER than a
// swept slot's -- has to clear the swept copy, and that copy no longer lives
// in its stash for any purpose: it is in the range table (or absorbed), and
// drains from there -- so it is caught in the DRAIN, once the range table
// has emptied into it.  At a chain step this direction never arises (the cross
// shed shares its class with the carry and is staler than the tier), which
// is why the merged step needs no such pass.  At an absorb the radix shed
// holds T_t-class entries, fresher than the L_t^old-class carry; at the fixed
// merge the merge shed is B-class, fresher than the preparation's A-class
// carry.  In both, a shed entry and a carry-class leftover of one key survive
// to the drain together: the shed's bucket was full, so the carry copy --
// same tag, same bucket -- could not be absorbed either.
//
// The rule is per CLASS of the leftover, which is what the class mark (or a
// single-rule pass's rule) says: a carry-class leftover loses to a shed copy
// of its key (dropped); a tier-class leftover beats one (the shed lane is
// cleared).  Exact under the same two facts every fused final pass has: the
// carry class is staler than everything the pass itself shed that it can
// collide with, and the tier class is fresher than -- or disjoint from -- it.
// BuildResidualPass checks the rank order that encodes those.
//
// It runs against the pass's DRAIN after the range table's leftovers have
// drained into it and before the drain-only slots do, rather than against
// the range table itself.  The range table is sized from the pool (eight
// buckets per pool bucket), not from the level, so at the many small absorbs
// it has hundreds of buckets while their whole output has a few dozen; run
// there the pass would cost more than fusing the sweeps saves.  The drain is
// one tier bucket, so this is a couple of intersects per item.  The class mark rides the meta line, a payload line
// the drain copies, so a drained leftover still says which rule it takes; the
// drain must hold nothing but this pass's range leftovers at that point,
// which every fused final pass's freshly acquired tier does.
//
// The unit is one (drain bucket, drain-only stash bucket) pair, drain-bucket
// major, drain-only buckets flattened across slots in pool order as
// DrainResidualPoolRange flattens them.  The unit count is public (both are
// capacities), and any slicing is legal: the pool dedup left each key in at
// most one leftover, a stash is a set, so each unit's clears are idempotent
// and independent of the others.
inline size_t ResidualLeftoverDedupUnits(const ResidualStash& drain,
                                         ResidualStash* const* pool,
                                         size_t drain_only_slots) {
  return drain.num_buckets * ResidualPoolBuckets(pool, drain_only_slots);
}

inline void ResidualLeftoverDedupRange(ResidualDedupRule rule,
                                       const Layout& layout,
                                       ResidualStash& drain,
                                       ResidualStash* const* pool,
                                       size_t drain_only_slots, size_t begin,
                                       size_t end) {
  assert(rule != ResidualDedupRule::kNoDedup);
  const size_t shed_buckets = ResidualPoolBuckets(pool, drain_only_slots);
  if (shed_buckets == 0) return;
  const size_t key_bytes = layout.key_bytes;
  const size_t meta_off = layout.MetaLine() * kBucketCapacity;
  const __m512i cls_bit =
      _mm512_set1_epi8(static_cast<char>(kMetaResidualClass));
  for (size_t u = begin; u < end; ++u) {
    const size_t tb = u / shed_buckets;
    size_t d = u % shed_buckets;
    size_t slot = 0;
    while (slot < drain_only_slots && d >= pool[slot]->num_buckets) {
      d -= pool[slot]->num_buckets;
      ++slot;
    }
    assert(slot < drain_only_slots && tb < drain.num_buckets);
    ResidualStash& shed = *pool[slot];
    const uint8_t* lbucket = drain.Bucket(tb);
    const uint64_t lmask = drain.masks[tb];
    uint64_t tier_c = 0, carry_c = 0;
    switch (rule) {
      case ResidualDedupRule::kClassMark: {
        const __m512i cls = _mm512_load_si512(
            reinterpret_cast<const void*>(lbucket + meta_off));
        tier_c = lmask & core::obliTestMask8(cls, cls_bit);
        carry_c = lmask & ~tier_c;
        break;
      }
      case ResidualDedupRule::kTableWins:
        carry_c = lmask;
        break;
      case ResidualDedupRule::kResidualWins:
        tier_c = lmask;
        break;
      case ResidualDedupRule::kNoDedup:
        return;
    }
    uint64_t shed_dup = 0, carry_dup = 0;
    CrossBucketClassDuplicateMasks(shed.Bucket(d), shed.masks[d], lbucket,
                                   carry_c, tier_c, key_bytes, &shed_dup,
                                   &carry_dup);
    shed.masks[d] &= ~shed_dup;
    drain.masks[tb] &= ~carry_dup;
  }
}

// Merges the real entries of residual buckets [begin, end) into `dst`, emptying
// them.  Payload only is the right `lines` for every caller here: whatever
// consumes `dst` next retags it, which recomputes the whole tag from the key
// under the consuming rebuild's nonce.
// "Drain" here means tier packing inside an ordinary rebuild, not shutdown.
// For a distinct-key kNoDedup build, after second chance every leftover
// targets a full bucket. The total leftovers are exactly sum_b (X_b-64)+,
// where X_b counts all input keys destined for b. Packing cannot exceed that
// count, irrespective of correlations among the stages that produced it.
// For a deduplicating pass the count is at most sum_b (X_b-64)+ over a fixed
// input key set U, provided main and the residuals already packed are
// disjoint subsets of U and every packed residual's destination stays full
// (the class-ordered offer and the leftover dedup maintain this); U must be
// chosen before tombstones are removed, not as the final live set.  The
// certification's scope and premises are in
// analysis/bound_certification/README.md.
inline bool DrainResidualTableRange(TableView range, ResidualStash& dst,
                                    size_t lines, size_t begin, size_t end) {
  const size_t bucket_bytes = range.layout.BucketBytes();
  for (size_t b = begin; b < end; ++b) {
    if (!MergeBucketIntoResidualStash</*CheckOverflow=*/true>(
            dst, range.data + b * bucket_bytes, range.masks[b], lines)) {
      return false;
    }
    range.masks[b] = 0;
  }
  return true;
}

// Merges the real entries of pool-stash buckets [begin, end) -- flat across
// `num_slots` stashes, slot 0's buckets first -- into `dst`, emptying them.
// The unit is one stash bucket, the same 64-slot oblivious merge the range
// drain performs, so the two phases share a slice width.
//
// This is the drain path of a DRAIN-ONLY pool slot: a shed class that is
// provably unabsorbable at its own step.  An entry is shed only because its
// target bucket is FULL at the end of the pass that shed it, and it can have
// no duplicate there (a duplicate would have CLEARED it at that pass's dedup
// prologue, not shed it), so no kResidualWins resolution can free it a slot
// -- offering it back to the table it just failed to enter is fixed work that
// provably absorbs nothing.  It therefore skips the range table and goes
// straight to the pass's drain, after the pool dedup has resolved it against
// the classes that ARE offered.  "Leftovers are never duplicates" is
// preserved by the same argument that makes it unabsorbable.
inline bool DrainResidualPoolRange(ResidualStash* const* pool,
                                   size_t num_slots, ResidualStash& dst,
                                   size_t lines, size_t begin, size_t end) {
  size_t slot = 0;
  size_t bucket = begin;
  while (slot < num_slots && bucket >= pool[slot]->num_buckets) {
    bucket -= pool[slot]->num_buckets;
    ++slot;
  }
  for (size_t at = begin; at < end; ++at) {
    assert(slot < num_slots);
    ResidualStash& src = *pool[slot];
    if (!MergeBucketIntoResidualStash</*CheckOverflow=*/true>(
            dst, src.Bucket(bucket), src.masks[bucket], lines)) {
      return false;
    }
    src.masks[bucket] = 0;
    if (++bucket == src.num_buckets) {
      bucket = 0;
      ++slot;
      while (slot < num_slots && pool[slot]->num_buckets == 0) ++slot;
    }
  }
  return true;
}

}  // namespace byteslice
}  // namespace microram
