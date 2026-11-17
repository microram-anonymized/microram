#pragma once

// The residual RANGE TABLE: turning a rebuild's scattered per-level stashes
// into one table that can be swept against the output.
//
// At load 0.5 every butterfly level sheds a few entries into its own stash.
// Their destination buckets are SECRET, so "look up each residual's bucket and
// insert it" cannot be done; the reunion is a fixed sequential scan instead.
// Its steps, numbered here and in cpu_byteslice_second_chance.hpp:
//
//   step 0  drop the pool's internal duplicates, by public freshness rank
//   step 1  build the range table: the DFS distributor's leaf pages
//           (cpu_byteslice_dfs_residual.hpp), or for a direct plan the pool
//           itself, scattered and tagged
//   step 2  sweep main and range together in index order (second_chance.hpp)
//   step 3  compact whatever did not fit (second_chance.hpp)
//
// STACKING.  Above ~2^23 entries one range table is not enough and the plan
// stacks several groups; a stacked table needs no dedup rule of its own,
// because a group only ever meets the main-table range it was built for.

#include <immintrin.h>

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "src/oram/rebuild/cpu_byteslice_dedup_masks.hpp"
#include "src/oram/rebuild/cpu_byteslice_stash_rebuild.hpp"

namespace microram {
namespace byteslice {

// ---------------------------------------------------------------------------
// The residual second chance
// ---------------------------------------------------------------------------
//
// Shedding is what breaks the freshness-by-level invariant: a shed entry skips
// its cross-source meeting and the residual dump republishes it as a FRESHER
// level than the table the same rebuild just built.  The fix is to give every
// residual a second chance at the bucket it was actually destined for,
// obliviously:
//
//   0. Drop the pool's internal duplicates by the slots' public freshness
//      rank.
//   1. Build a range table in which range bucket r holds only residuals
//      destined for main buckets [r*G, (r+1)*G), G = 2^index_bits: the DFS
//      distributor's pages, or (direct plan) the pool itself with G the whole
//      main table.
//   2. Sweep the main table LINEARLY, main bucket b pairing with residual
//      bucket b >> index_bits, absorbing the entries whose low index_bits of
//      tag equal b's -- as many as fit.
//   3. Compact what is left.
//
// Step 2 is the point: the residuals' destinations are secret, but the sweep is
// a fixed sequential scan of both tables, so nothing about which bucket a
// residual wanted is observable.  That is what makes this oblivious where the
// naive "look up each residual's bucket" is not.
//
// Two properties fall out.  A residual that duplicates a main-table entry
// never survives AS a duplicate, whatever the dedup rule decides -- resolving
// the duplicate removes one of the two copies, and the freed slot keeps the
// bucket's occupancy from ever dropping below full -- so **leftovers are never
// duplicates** and the compacted remainder can be republished as a fresher
// level without inverting anything.  And the leftover count stops depending on
// the network depth: a residual only fails when its target bucket is genuinely
// full (~2^-21 at load 0.5), instead of every shed surviving to the dump.

// Coarse ranges per pool bucket in PlanResidualRange.  The DFS distributor
// takes its coarse partition from that plan, so this fixes the certified
// geometry.
inline constexpr size_t kResidualsPerRange = 8;

// The DIRECT regime's threshold: at main_levels <= this, PlanResidualRange
// does not route at all -- the range table IS the pool (one range bucket per
// pool bucket, wholesale scatter, range_bits = 0) and the sweep pairs every
// main bucket with every range bucket, selecting candidates by the full
// destination index (index_bits = main_levels). No route means zero route
// overflow, regardless of the residual contents or their correlations.
// Drain/compact capacity checks remain. At larger depths the direct sweep's
// cost grows as 2^main_levels * pool_buckets, so this cutoff is a cost choice;
// above it the DFS distributor builds the table.
inline constexpr unsigned kResidualDirectMaxLevels = 3;

struct ResidualRangePlan {
  unsigned range_bits = 0;   // log2 of ONE sub-table's bucket count
  unsigned index_bits = 0;   // log2 of a range's main-bucket count
  // Stacked copies of the range table, one behind the other: main bucket b
  // pairs with residual bucket g * 2^range_bits + b for every g, and the sweep
  // visits all of them.  1 for every plan that fits in a single sub-table,
  // which is every plan on a table whose pool is smaller than it.
  //
  // INVARIANT: groups > 1 implies scatter_per_bucket == kBucketCapacity, and
  // one of two shapes.  STACKED (range_bits == main_levels, index_bits == 0):
  // reached through the main_levels cap with the scatter already saturated --
  // see FinishResidualRangePlan -- so a stacked range covers exactly one main
  // bucket and the sweep's tag match is a no-op.  DIRECT (range_bits == 0,
  // index_bits == main_levels, groups == range_buckets == pool_buckets): the
  // main_levels <= kResidualDirectMaxLevels regime, where the table is the
  // pool itself, nothing routes, and the sweep's tag match does ALL of the
  // selection.  Both share the g * 2^range_bits + (b >> index_bits) pairing
  // and the (bucket, group) unit space.
  size_t groups = 1;
  size_t range_buckets = 0;  // groups << range_bits: the WHOLE scratch
  // Slots of one pool bucket per residual bucket: the scatter fans each
  // 64-slot stash bucket over 64 / scatter_per_bucket residual buckets, so it
  // is also the deterministic bound on a residual bucket's starting load.
  size_t scatter_per_bucket = kResidualsPerRange;
};

// `pool_buckets` is the (public) number of stash buckets the rebuild sheds
// into; `main_levels` is CEIL of log2 of the main table's bucket count -- equal
// to log2 for every binary table, and one or two more for the two mixed-radix
// tables, whose top ranges then stay empty.
//
// A range must cover at least one main bucket, so range_bits is capped at
// main_levels.  Two regimes follow from that cap, and both are planned rather
// than refused:
//
//  - The cap binds but the pool still fits in one sub-table.  The scatter packs
//    more than 8 slots per residual bucket.
//  - The cap binds AND the pool has more buckets than the sub-table has.  The
//    scatter has saturated at a whole 64-slot bucket per residual bucket and
//    cannot pack further, so the table STACKS: `groups` copies of it, main
//    bucket b paired with residual bucket g * 2^range_bits + b for each.  This
//    is the fat-stash regime -- a 16-bucket chunk given stashes sized from the
//    largest ORAM level.
//
// The tail both planners share: cap `bits` at main_levels, then derive the
// scatter packing and the stacked-copy count from the pool.
inline ResidualRangePlan FinishResidualRangePlan(size_t pool_buckets,
                                                 unsigned bits,
                                                 unsigned main_levels) {
  if (pool_buckets == 0) {
    // One ordinary padding group clears reused scratch even without a source.
    // Fanout must be one: an eight-way scatter into one bucket has zero groups
    // and would leave the previous build's occupancy untouched.
    ResidualRangePlan plan;
    plan.index_bits = main_levels;
    plan.range_buckets = 1;
    plan.scatter_per_bucket = kBucketCapacity;
    return plan;
  }
  if (bits > main_levels) bits = main_levels;
  ResidualRangePlan plan;
  plan.range_bits = bits;
  plan.index_bits = main_levels - bits;
  const size_t sub = size_t{1} << bits;
  // Smallest power-of-two slot count per residual bucket that still lets the
  // whole pool land inside one sub-table: 64 * pool_buckets / 2^range_bits.
  size_t per = kResidualsPerRange;
  while (per < kBucketCapacity &&
         pool_buckets * (kBucketCapacity / per) > sub) {
    per *= 2;
  }
  plan.scatter_per_bucket = per;
  // What the packing could not absorb becomes stacked copies.  The loop above
  // only exits early when the pool fits, so this is 1 whenever the pool fits
  // in one sub-table.
  const size_t fanout = kBucketCapacity / per;
  plan.groups = (pool_buckets * fanout + sub - 1) / sub;
  plan.range_buckets = plan.groups * sub;
  // groups > 1 needs the cap to have bound: without it 2^bits >= pool >=
  // fanout * pool / 8, since the scatter never fans wider than 8.
  assert(plan.groups == 1 ||
         (plan.index_bits == 0 && plan.scatter_per_bucket == kBucketCapacity));
  return plan;
}

inline ResidualRangePlan PlanResidualRange(size_t pool_buckets,
                                           unsigned main_levels) {
  // The DIRECT regime (see kResidualDirectMaxLevels): the range table is the
  // pool, wholesale, and nothing routes -- the sweep visits every (main
  // bucket, pool bucket) pair and its index_bits match does the selection.
  // The route-overflow event of the packed regimes does not exist here.  A
  // decision by (pool, main_levels) alone, both public.  pool == 0 uses the
  // one-padding-group plan in FinishResidualRangePlan at every main depth.
  if (main_levels <= kResidualDirectMaxLevels && pool_buckets != 0) {
    ResidualRangePlan plan;
    plan.range_bits = 0;
    plan.index_bits = main_levels;
    plan.groups = pool_buckets;
    plan.range_buckets = pool_buckets;
    plan.scatter_per_bucket = kBucketCapacity;
    return plan;
  }
  unsigned bits = 0;
  // 8 destination buckets per pool bucket, rounded up to a power of two.
  while ((size_t{1} << bits) < pool_buckets * kResidualsPerRange) ++bits;
  return FinishResidualRangePlan(pool_buckets, bits, main_levels);
}

// Buckets a pool of stashes contributes, which is what PlanResidualRange sizes
// the range table from.  Public: a stash's capacity is a design constant, only
// its occupancy is secret.
inline size_t ResidualPoolBuckets(const ResidualStash* const* stashes,
                                  size_t num_stashes) {
  size_t total = 0;
  for (size_t s = 0; s < num_stashes; ++s) total += stashes[s]->num_buckets;
  return total;
}
// Same, for the mutable pools the kernels take.  `ResidualStash* const*` does
// not convert to `const ResidualStash* const*` -- the qualification conversion
// C++ does not do -- and every caller here holds a mutable pool.
inline size_t ResidualPoolBuckets(ResidualStash* const* stashes,
                                  size_t num_stashes) {
  size_t total = 0;
  for (size_t s = 0; s < num_stashes; ++s) total += stashes[s]->num_buckets;
  return total;
}

// Step 1, sliced.  The scatter fans ONE pool bucket over `fanout` consecutive
// range buckets, so the natural slice unit is that group: group g takes pool
// bucket g, or -- past the pool -- clears the padding it would have filled.
// Clearing matters: a range table is a reused scratch, and a previous sweep's
// occupancy words would resurrect its residuals as this one's.
// The pool is an array of POINTERS rather than a contiguous array of stashes,
// because a pass's pool is heterogeneous: a job's own
// butterfly-level stashes, its carry, and the second TIER of a table it is
// consuming, which lives in the registry and outlives the pass.  It is also
// read live rather than snapshotted, so the reset of the job's own stashes can
// be its own subtask after the scatter has finished with them.
//
// `drop_unshadowed` is THE UNSHADOWED SKIP (kMetaUnshadowed,
// cpu_byteslice_meta.hpp: a tombstone whose key has no older live copy): at an
// item that is allowed to forget a tombstone, a shed or borrowed-tier entry
// that shadows nothing is not offered back to the output and is not drained
// into the new second tier.
// The pool's own occupancy words are not edited -- the mask is taken by value
// into the scatter -- so the pool dedup that ran BEFORE this still saw the
// tombstone and still cleared any staler copy of its key, and the pass's reset
// is unaffected.
inline void ScatterResidualPoolRange(const ResidualStash* const* stashes,
                                     size_t num_stashes, TableView range,
                                     const ResidualRangePlan& plan,
                                     size_t begin, size_t end,
                                     bool drop_unshadowed = false) {
  const size_t entry_bytes = range.layout.EntryBytes();
  const size_t bucket_bytes = range.layout.BucketBytes();
  const size_t payload = range.layout.PayloadLines();
  const size_t meta_offset = range.layout.MetaLine();
  const size_t fanout = kBucketCapacity / plan.scatter_per_bucket;
  for (size_t g = begin; g < end; ++g) {
    const size_t dest = g * fanout;
    assert(dest + fanout <= range.num_buckets);
    size_t at = g;
    const ResidualStash* src = nullptr;
    for (size_t s = 0; s < num_stashes; ++s) {
      if (at < stashes[s]->num_buckets) {
        src = stashes[s];
        break;
      }
      at -= stashes[s]->num_buckets;
    }
    if (src == nullptr) {
      for (size_t b = dest; b < dest + fanout; ++b) range.masks[b] = 0;
      continue;
    }
    // Tag lines are recomputed by the retag, so only the payload moves.
    uint64_t src_mask = src->masks[at];
    if (drop_unshadowed) {
      DropUnshadowedFromMask(src->Bucket(at), &src_mask, meta_offset);
    }
    ScatterDenseBucket(src->Bucket(at), src_mask,
                       range.data + dest * bucket_bytes, range.masks + dest,
                       plan.scatter_per_bucket, entry_bytes, payload);
  }
}

// The class-mark stamp of the MERGED per-step pass (kClassMark in
// cpu_byteslice_second_chance.hpp).  It runs after the retag: at that instant
// every range bucket holds lanes from exactly ONE pool bucket (the scatter
// fans pool bucket g over destinations [g*fanout, (g+1)*fanout)), so a
// bucket's class is a public function of its index, and buckets fed from
// swept pool bucket `tier_from_group` onward are the kResidualWins class (bit
// set).  Padding groups sit past the pool and so past the class boundary,
// which stamps them as TIER class -- immaterial under their zero
// occupancy masks; all 64 lanes are stamped, dummies being excluded by the
// masks -- and only kMetaResidualClass moves, because the meta line's other
// bits carry the erasure tombstone.
//
// The mark is kMetaResidualClass in the META line: a payload line, so it
// is present at every geometry and moved like any other, which is what makes
// the merged shape available unconditionally.  The stamp is unconditional over
// [begin, end) -- it OVERWRITES whatever the pool's entries carried in, which
// is how a bit absorbed into a published table at an earlier step cannot be
// mistaken for this pass's class.  Ordering against the retag does not
// matter (the retag touches tag lines only); the stamp is issued from the
// retag arm, where the range table is already the resident working set.
inline void WriteResidualClassBitsRange(TableView range,
                                        const ResidualRangePlan& plan,
                                        size_t tier_from_group, size_t begin,
                                        size_t end) {
  const size_t bucket_bytes = range.layout.BucketBytes();
  const size_t line = range.layout.MetaLine();
  const size_t fanout = kBucketCapacity / plan.scatter_per_bucket;
  const __m512i bit = _mm512_set1_epi8(static_cast<char>(kMetaResidualClass));
  for (size_t rb = begin; rb < end; ++rb) {
    uint8_t* at = range.data + rb * bucket_bytes + line * kBucketCapacity;
    const __m512i cur = _mm512_load_si512(reinterpret_cast<const void*>(at));
    // The class is public geometry, so branching on it leaks nothing.
    const __m512i out = rb / fanout >= tier_from_group
                            ? _mm512_or_si512(cur, bit)
                            : _mm512_andnot_si512(bit, cur);
    _mm512_store_si512(reinterpret_cast<void*>(at), out);
  }
}

// Scatter with one 64-lane hash per SOURCE bucket, instead of hashing every
// destination (including its dummy lanes). Tags retain their full mapped word:
// the offer uses low index bits and a later carry may still need a radix digit.
// Only public capacity/geometry controls the work. In particular an empty
// source bucket is still hashed; only public padding skips the source work.
// Dummy bytes may differ from ScatterResidualPoolRange + retag, but masks and
// every occupied entry byte agree. Sources and their occupancy remain immutable.
inline void ScatterAndRetagResidualPoolRange(
    const ResidualStash* const* stashes, size_t num_stashes, TableView range,
    const ResidualRangePlan& plan, size_t begin, size_t end,
    uint64_t nonce_lo, uint64_t nonce_hi, const RoutingIndexMap& map,
    const AesTagKeys& aes_keys, bool class_mark = false,
    size_t tier_from_group = SIZE_MAX, bool drop_unshadowed = false) {
  const Layout& layout = range.layout;
  const size_t fanout = kBucketCapacity / plan.scatter_per_bucket;
  const uint64_t high_word = crypto::PackAesCtrHighWord(nonce_lo, nonce_hi);
  for (size_t g = begin; g < end; ++g) {
    const size_t dest = g * fanout;
    assert(dest + fanout <= range.num_buckets);
    size_t at = g;
    const ResidualStash* src = nullptr;
    for (size_t s = 0; s < num_stashes; ++s) {
      if (at < stashes[s]->num_buckets) {
        src = stashes[s];
        break;
      }
      at -= stashes[s]->num_buckets;
    }
    if (src == nullptr) {
      for (size_t b = dest; b < dest + fanout; ++b) range.masks[b] = 0;
      continue;
    }
    const uint8_t* source = src->Bucket(at);
    uint64_t mask = src->masks[at];
    if (drop_unshadowed) {
      DropUnshadowedFromMask(source, &mask, layout.MetaLine());
    }
    // The whole mapped word: the offer uses the low index bits and a later
    // carry may still need a radix digit.
    ScatterAndRetagDenseBucket(source, mask, range.Bucket(dest),
                               range.masks + dest, plan.scatter_per_bucket,
                               layout, high_word, map, layout.tag_bytes,
                               /*write_digit=*/false, aes_keys);
  }
  if (class_mark) {
    WriteResidualClassBitsRange(range, plan, tier_from_group,
                                begin * fanout, end * fanout);
  }
}

// How many range buckets one scatter group writes.  Named because the
// scheduler prices and slices a scatter by it: a group is one pool bucket
// fanned over this many destinations, so it is `fanout` bucket touches and not
// one.  1 whenever the scatter is saturated, which includes every stacked plan.
inline size_t ResidualScatterFanout(const ResidualRangePlan& plan) {
  return kBucketCapacity / plan.scatter_per_bucket;
}

// How many scatter groups a range table has.  PlanResidualRange guarantees
// fanout <= range_buckets and that the division is exact: below the stacking
// regime both are powers of two, and at plan.groups > 1 the fanout is 1 and
// every range bucket is its own group (pool bucket g, or cleared padding).
inline size_t ResidualScatterGroups(const TableView& range,
                                    const ResidualRangePlan& plan) {
  return range.num_buckets / ResidualScatterFanout(plan);
}

// No per-range-bucket self-dedup follows step 1.  It would find nothing:
// step 0 leaves the pool with each key at most once, and in a STACKED table it
// could not even catch a violation (two copies share an index but can sit in
// different sub-tables).  A violation of the equal-rank disjointness
// invariant therefore surfaces as a duplicate in the published table -- which
// the probe audit catches -- rather than as a silent arbitrary winner; the
// invariant itself is asserted by ResidualPoolEqualRanksDisjoint below in
// debug builds.

// Step 0, sliced -- and the reason no rank BYTE is needed in the entry.  A
// residual's source block is PUBLIC: a MergeSplit only ever sheds from its
// second operand, so where the MergeSplit sat in the network says which block
// the entry came from, and in both networks that fact is already carried by
// WHICH POOL SLOT
// the entry is in.  `rank` is that, one small public integer per slot, lower =
// fresher; equal ranks mean "these slots are provably duplicate-free against
// each other" (they draw from one source table) and are skipped.
//
// Without it two shed copies of one key would reach the range table with no
// freshness order, and that is not a tie: copy A, shed at its own
// cross-source level, LEAVES the prefix, so copy B never meets it and is shed
// in turn, and the two land in the same residual bucket.  Both shed is ~2^-39
// per duplicated key per rebuild -- the same order as the per-block carry
// itself, and the failure is a stale value winning (or a duplicate
// surviving) rather than an extra unrelated entry.
//
// THIS IS WHAT MAKES THE POOL DUPLICATE-FREE, and every later stage relies on
// it rather than re-establishing it.  The residual pool is a handful of small
// tables, each drawn from ONE source table and therefore holding each key at
// most once, carrying a public freshness order; deduplicating them pairwise is
// the whole of the argument, exactly as it is for the source tables of the
// rebuild itself.  Every pair of slots at DIFFERENT ranks is compared here, so
// afterwards a key can survive twice only inside one slot, or between two slots
// of EQUAL rank -- and equal rank means "one source table" by construction (see
// the per-pass source lists the engine hands BuildResidualPassFields, each of
// which says which single source its equal-rank slots are drawn from).
//
// NOTE what leans on that.  BuildResidualPassFields only rejects the same stash
// appearing twice in one pass; it does not check that two DIFFERENT equal-rank
// slots hold disjoint keys.  So the invariant is an argument, not a runtime
// check (asserted in debug by ResidualPoolEqualRanksDisjoint).  A pass that
// put two genuinely different sources at one rank would be a correctness bug
// that release builds catch only downstream, as a duplicate in the published
// table.
//
// Sliced over ordered BUCKET pairs, not slot pairs.  The unit has to be a
// bucket pair because that is what the kernel actually costs: comparing slot
// `a` against slot `b` is `a.num_buckets * b.num_buckets` calls to
// CrossBucketDuplicateMask, so pricing a slot pair as one cross-source pair
// underestimates the phase by the square of the stash depth -- which is 1 only
// when every stash is one bucket, and up to 64 at kStashCapMaxBuckets.  An
// underpriced unit is not just a reporting error: it is the slice width, so it
// would put a multiple of a piece's budget back into one uninterruptible block.
//
// The unit space is the ELIGIBLE ordered bucket pairs: (fresher slot f, staler
// slot s) with rank[f] < rank[s], each contributing `f.num_buckets *
// s.num_buckets` units, enumerated f-major in slot order.  Equal-rank pairs
// and staler-first pairs are not units the kernel skips; they are not units
// at all, so the count the planner slices and charges is the number of
// intersects that run.  A merged chain step with one-bucket stashes and a
// one-bucket tier plans its two emissions as 2 units rather than the 7 its
// enclosing slot rectangles would hold.
// Ranks, bucket counts and the window are all public, so the enumeration --
// and with it the trace -- is data-independent.
//
// Slicing is safe anywhere: each pair only clears bits of the staler bucket's
// occupancy word, and clearing is idempotent and order-independent (an entry
// survives iff no strictly fresher-ranked slot holds its key, whichever order
// the pairs are visited in).
//
// WHICH slots one emission covers.  The pool is the drain-only PREFIX
// followed by the swept SUFFIX, so every window is a slot rectangle, and which
// one an emission takes is a public function of WHEN it runs -- never of what
// the pool holds.  A BRACKETED pass -- the merged chain step, whose two
// emissions straddle the cross level -- would otherwise re-run every live
// pair of the first emission in the second.
enum class ResidualDedupWindow : uint8_t {
  // Every ordered pair.  What a pass with ONE emission BEFORE its scatter
  // needs: at that instant every slot's stash is live and still readable.
  kFull,
  // Swept x swept.  The pre-scatter emission of a pass whose drain-only prefix
  // is publicly EMPTY at that moment -- a chain step's cross shed, which was
  // reset at the previous step and only fills during the cross level the two
  // emissions bracket.  (Debug-asserted, see ResidualPoolPrefixEmpty.)
  kSweptOnly,
  // (anything) x drain-only.  What an emission AFTER the scatter needs, and
  // all one can still do: a swept slot's content now lives in the range table
  // and drains from THERE, so clearing its stash mask no longer reaches the
  // output -- only the drain-only prefix, which drains from its stash, does.
  // Its rows stay unrestricted, because a fresher copy may sit in either part.
  kDrainOnly,
};

// The SLOT rectangle of a window: fresher slots [fresher_begin, num_slots) x
// staler slots [staler_begin, staler_end).  Exact, because every window is a
// slot prefix or suffix of the pool.
struct ResidualDedupSlotWindow {
  size_t fresher_begin = 0;
  size_t staler_begin = 0;
  size_t staler_end = 0;
};

inline ResidualDedupSlotWindow ResidualPoolDedupSlotWindow(
    size_t num_slots, size_t drain_only_slots, ResidualDedupWindow window) {
  switch (window) {
    case ResidualDedupWindow::kFull:
      return ResidualDedupSlotWindow{0, 0, num_slots};
    case ResidualDedupWindow::kSweptOnly:
      return ResidualDedupSlotWindow{drain_only_slots, drain_only_slots,
                                     num_slots};
    case ResidualDedupWindow::kDrainOnly:
      return ResidualDedupSlotWindow{0, 0, drain_only_slots};
  }
  return ResidualDedupSlotWindow{};
}

// Walks the eligible slot pairs of a window in the one public order every
// caller shares -- fresher slot ascending, then staler slot ascending --
// calling `visit(f, s, units)` with the block's unit count.  `slot_buckets(s)`
// is the slot's bucket count; a callable rather than the pool itself so the
// cost model can run the identical enumeration from public geometry alone.
template <typename SlotBuckets, typename Visit>
inline void ForEachEligiblePoolPair(const uint8_t* rank, size_t num_slots,
                                    size_t drain_only_slots,
                                    ResidualDedupWindow window,
                                    SlotBuckets&& slot_buckets, Visit&& visit) {
  const ResidualDedupSlotWindow w =
      ResidualPoolDedupSlotWindow(num_slots, drain_only_slots, window);
  for (size_t f = w.fresher_begin; f < num_slots; ++f) {
    for (size_t s = w.staler_begin; s < w.staler_end; ++s) {
      if (rank[f] < rank[s]) visit(f, s, slot_buckets(f) * slot_buckets(s));
    }
  }
}

// kSweptOnly's precondition as a predicate: the drain-only prefix holds
// nothing, so the pairs the window drops could not have cleared anything.
// Debug only (it reads secret occupancy), like ResidualPoolEqualRanksDisjoint
// and for the same reason -- which window an emission may take is a statement
// about the CALLER's schedule, and this is the one place it can be checked.
inline bool ResidualPoolPrefixEmpty(ResidualStash* const* pool,
                                    size_t drain_only_slots) {
  for (size_t s = 0; s < drain_only_slots; ++s) {
    if (pool[s]->Count() != 0) return false;
  }
  return true;
}

inline void ResidualPoolDedupRange(ResidualStash* const* pool,
                                   const uint8_t* rank, size_t num_slots,
                                   size_t drain_only_slots,
                                   ResidualDedupWindow window, size_t key_bytes,
                                   size_t begin, size_t end) {
  assert(window != ResidualDedupWindow::kSweptOnly || begin != 0 ||
         ResidualPoolPrefixEmpty(pool, drain_only_slots));
  // Walk the eligible blocks in the order the unit count sums them, and run
  // the units of [begin, end) that fall inside each; a block's units are its
  // ordered bucket pairs, fresher-bucket-major.
  size_t at = 0;
  ForEachEligiblePoolPair(
      rank, num_slots, drain_only_slots, window,
      [&](size_t s) { return pool[s]->num_buckets; },
      [&](size_t f, size_t s, size_t units) {
        const size_t block_begin = at;
        const size_t block_end = at + units;
        at = block_end;
        if (block_end <= begin || block_begin >= end) return;
        const ResidualStash& fresher = *pool[f];
        ResidualStash& staler = *pool[s];
        const size_t columns = staler.num_buckets;
        const size_t lo = std::max(begin, block_begin) - block_begin;
        const size_t hi = std::min(end, block_end) - block_begin;
        for (size_t p = lo; p < hi; ++p) {
          const size_t fb = p / columns;
          const size_t sb = p % columns;
          staler.masks[sb] &= ~CrossBucketDuplicateMask(
              fresher.Bucket(fb), fresher.masks[fb], staler.Bucket(sb),
              staler.masks[sb], key_bytes);
        }
      });
}

// The pair space ResidualPoolDedupRange is sliced over: the eligible ordered
// pairs of pool BUCKETS inside the window, so one unit is exactly one
// CrossBucketDuplicateMask and costs what a cross-source pair's intersect
// costs.
inline size_t ResidualPoolDedupPairs(ResidualStash* const* pool,
                                     const uint8_t* rank, size_t num_slots,
                                     size_t drain_only_slots,
                                     ResidualDedupWindow window) {
  size_t total = 0;
  ForEachEligiblePoolPair(
      rank, num_slots, drain_only_slots, window,
      [&](size_t s) { return pool[s]->num_buckets; },
      [&](size_t, size_t, size_t units) { total += units; });
  return total;
}

// The contract ResidualPoolDedupRange RESTS on rather than establishes, as a
// predicate: every stash holds each key at most once, and two stashes of EQUAL
// rank hold disjoint key sets.  The dedup resolves pairs of DIFFERENT rank and
// skips equal ones on exactly this ground -- "they draw from one source table"
// -- and this predicate is the whole of the pool's duplicate-freeness: no
// later stage re-checks it.  Both halves are checked: a bucket against every
// OTHER bucket of equal rank with the cross-bucket intersect, and against
// ITSELF with the self form -- the one pair the cross form cannot judge, and
// without which two copies of a key inside one bucket would pass.
//
// Callers use it inside assert(), so it is compiled out of release builds
// entirely: it is O(pool_buckets^2) intersects on top of a phase that is
// already that shape, and it is a statement about the CALLER's source
// bookkeeping, not about this kernel.  A false negative is possible and
// harmless -- a cross-rank clear earlier in the same sweep may already have
// removed the offending copy -- but it never reports a violation that is not
// there.
inline bool ResidualPoolEqualRanksDisjoint(ResidualStash* const* pool,
                                           const uint8_t* rank,
                                           size_t num_slots, size_t key_bytes) {
  for (size_t a = 0; a < num_slots; ++a) {
    for (size_t b = a; b < num_slots; ++b) {
      if (rank[a] != rank[b]) continue;
      const ResidualStash& sa = *pool[a];
      const ResidualStash& sb = *pool[b];
      for (size_t ba = 0; ba < sa.num_buckets; ++ba) {
        for (size_t bb = 0; bb < sb.num_buckets; ++bb) {
          // A bucket always duplicates itself, so the cross-bucket intersect
          // says nothing about that one pair; the self form answers the
          // question actually asked -- does any key occur twice IN this
          // bucket.  Keyed on the stash POINTER, not the slot index, so a
          // pool that lists one stash twice is handled.
          if (pool[a] == pool[b] && ba == bb) {
            if (BucketSelfDuplicateMask(sa.Bucket(ba), sa.masks[ba],
                                        key_bytes) != 0) {
              return false;
            }
            continue;
          }
          if (CrossBucketDuplicateMask(sa.Bucket(ba), sa.masks[ba],
                                       sb.Bucket(bb), sb.masks[bb],
                                       key_bytes) != 0) {
            return false;
          }
        }
      }
    }
  }
  return true;
}

// Whether any pair INSIDE THE WINDOW survives the rank filter at all.  Only a
// pass that mixes freshness classes has any: a pass whose slots all rank equal
// is provably duplicate-free across slots (they draw from one source table), so
// every pair is skipped and planning the phase only dispatches empty subtasks.
// Window-aware because a window can be uniform-rank where the whole pool is not
// -- kSweptOnly over a swept suffix that is all one class, say.  Slot-granular,
// which is exact: every window is a slot prefix or a slot suffix.
inline bool ResidualPoolDedupNeeded(const uint8_t* rank, size_t num_slots,
                                    size_t drain_only_slots,
                                    ResidualDedupWindow window) {
  // The same slot rectangle ResidualPoolDedupSlotWindow names; any eligible
  // pair inside it is at least one unit, since every stash has a bucket.
  const bool swept_only = window == ResidualDedupWindow::kSweptOnly;
  const size_t fresher_begin = swept_only ? drain_only_slots : 0;
  const size_t staler_begin = fresher_begin;
  const size_t staler_end = window == ResidualDedupWindow::kDrainOnly
                                ? drain_only_slots
                                : num_slots;
  for (size_t f = fresher_begin; f < num_slots; ++f) {
    for (size_t st = staler_begin; st < staler_end; ++st) {
      if (rank[f] < rank[st]) return true;
    }
  }
  return false;
}

// Whether a FUSED final pass needs the leftover dedup
// (ResidualLeftoverDedupRange, cpu_byteslice_second_chance.hpp): some
// drain-only slot is FRESHER than some swept slot.  A shed copy staler than a
// swept one is the pool dedup's post-pass (kDrainOnly) business, since the
// swept stash is still readable; a shed copy fresher than a swept one has to
// clear a lane that now lives in the range table, which only the leftover
// pass can reach.  Ranks are public, so this is a public shape decision, and
// it is false for every chain step (the cross shed ranks with the carry and
// below the tier) and for every single-class pass.
inline bool ResidualLeftoverDedupNeeded(const uint8_t* rank, size_t num_slots,
                                        size_t drain_only_slots) {
  for (size_t d = 0; d < drain_only_slots; ++d) {
    for (size_t s = drain_only_slots; s < num_slots; ++s) {
      if (rank[d] < rank[s]) return true;
    }
  }
  return false;
}

}  // namespace byteslice
}  // namespace microram
