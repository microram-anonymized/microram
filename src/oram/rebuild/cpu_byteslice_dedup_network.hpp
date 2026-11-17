#pragma once

// The deduplicating rebuild network: the cross-source MergeSplit, the
// incremental chain built from it, and the two mixed-radix joins.
//
// WHY DUPLICATES EXIST.  An engine that removed an entry when an access found
// it would hold one copy of each key.  A background rebuild makes that
// impossible: it reads published source tables over many subsequent
// accesses, and for that whole window the sources have to stay PROBEABLE while new accesses keep inserting fresher copies of the same keys
// into the re-created small levels.  Removing on probe is also not available --
// clearing an occupancy bit is a write an observer could see.  So duplicates
// are real objects, and they are resolved here instead: when two sources meet,
// the copy from the FRESHER source wins.
//
// The binary layout below is the reference form.  In the level arena the same
// layout appears at a merge of digit j = r*2^e: block 0 is the incoming carry
// (U buckets) and the following spans U, 2U, ..., 2^(e-1)U are the older
// partial's blocks (rebuild DESIGN.md, "Deduplicate at source joins"); read
// L_k below as those spans and "stash" as the carry.
//
// WHERE THEY MEET.  A rebuild's input, freshest source first, is
//
//   bucket 0      2^s        2^(s+1)         2^(s+2)            2^t     2^(t+1)
//         [ stash ][   L_0   ][    L_1      ][    L_2     ]...[  L_(t-1)  ]
//
// Every prefix is a power of two, so the butterfly splits cleanly into
//
//   - INTRA-source MergeSplits, both operands from one source table.  A source
//     holds each key at most once, so the plain kernel applies unchanged.
//   - one CROSS-source group per butterfly level b >= s: the pairs
//     (i, i + 2^b), joining the already-merged prefix [0, 2^b) with the source
//     block L_(b-1) = [2^b, 2^(b+1)).
//
// And the cross-source pairing catches every duplicate exactly once, for a
// reason worth stating: two copies of a key carry the SAME routing tag T, so
// once bits [0, b) are routed they sit in prefix bucket T mod 2^b and block
// bucket 2^b + (T mod 2^b) -- precisely the pair that level compares.
//
// ISSUE ORDER.  RouteBinarySourcesDedup runs all the intra-source routing
// first, largest source first, then the cross-source levels in increasing
// order.  The MergeSplit set and each one's input state are identical to the
// flat level-by-level order; only the public issue order differs.  But this
// order is the one deamortization needs, because intra-source routing depends
// on a single immutable source table plus the rebuild's nonce and nothing else
// -- so it is exactly the part that can run ahead in the background -- and the
// largest source is the oldest, hence the first to become available.
//
// Dropping a duplicate is just clearing its occupancy bit before the split: the
// bytes stay in place, are never routed again, and the MergeSplit that follows
// is bit-for-bit the ordinary one.  Since dedup only ever removes entries
// before a split, a level's shed count can only go DOWN relative to the
// no-dedup bound the stash schedule was sized against.
//
// THE INCREMENTAL CHAIN.  A carry need not build its output in one pass.  It
// can walk T_0 = the frozen stash, T_(j+1) = merge(T_j, L_j), publishing each
// T_j as a real probeable table.  The level-arena engine does not publish the
// intermediate T_j; the chain kernels below are the reference the tests check
// the phase planners against.
//
// MIXED RADIX.  When the target's digit is not a power of two, the r odd blocks
// it leaves over are joined by the two kernels at the end of this file rather
// than by another butterfly level.

#include <immintrin.h>

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "src/core/mov_intrinsics.hpp"
#include "src/oram/rebuild/cpu_byteslice_dedup_masks.hpp"
#include "src/oram/rebuild/cpu_byteslice_stash_rebuild.hpp"

namespace microram {
namespace byteslice {

// The canonical binary-carry decomposition of 2^m buckets whose smallest block
// is 2^first_block_log2 buckets: block 0 is [0, 2^s) and block j >= 1 is
// [2^(s+j-1), 2^(s+j)), so blocks 0 and 1 have the same size and every later
// one matches the whole prefix below it -- the layout that makes each
// cross-source level a single (prefix, block) join (RouteBinarySourcesDedup).
inline unsigned BinarySourceBlockCount(unsigned m, unsigned first_block_log2) {
  return m - first_block_log2 + 1;
}

inline void BinarySourceBlock(unsigned first_block_log2, unsigned index,
                              size_t* offset, size_t* size) {
  if (index == 0) {
    *offset = 0;
    *size = size_t{1} << first_block_log2;
  } else {
    *offset = size_t{1} << (first_block_log2 + index - 1);
    *size = *offset;
  }
}

// MergeSplit of a fresher bucket against an older one, dropping every entry of
// `second` whose key also lives in `first`.  Dropping is just clearing the
// occupancy bit before the split: the bytes stay in place, are never routed
// again, and the MergeSplit that follows is bit-for-bit the ordinary one.
//
// The dedup adds one line load per key byte per bucket; the MergeSplit then
// re-reads those same lines from L1, which is why fusing the two loops is not
// worth the register pressure (the intersects dominate either way).
template <bool CheckOverflow = false>
inline bool MergeSplitPairDedupStash(uint8_t* first, uint8_t* second,
                                     uint64_t* first_mask,
                                     uint64_t* second_mask, size_t key_bytes,
                                     size_t lines, size_t tag_line,
                                     unsigned bit, ResidualStash& stash) {
  *second_mask &= ~CrossBucketDuplicateMask(first, *first_mask, second,
                                            *second_mask, key_bytes);
  return MergeSplitPairStash<CheckOverflow>(first, second, first_mask,
                                            second_mask, lines, tag_line, bit,
                                            stash);
}

// ---------------------------------------------------------------------------
// The rebuild network
// ---------------------------------------------------------------------------

// One cross-source butterfly level: pairs (i, i + 2^bit) for i in [0, 2^bit),
// joining the merged prefix (fresher) with the source block above it (older).
// Range-parameterized so the phase planners can issue it in slices.
template <bool CheckOverflow = false>
inline bool CrossSourceLevelDedup(TableView t, unsigned bit,
                                  ResidualStash& stash, size_t begin,
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
  }
  return true;
}
// Routes the whole rebuild input (2^m buckets, tags already computed with the
// rebuild's nonce) into the target table, deduplicating across sources.
//
// Phase 1 -- every source block's own butterfly, LARGEST SOURCE FIRST.  These
// are ordinary MergeSplits: a source table holds each key at most once.
// Phase 2 -- the cross-source levels b = first_block_log2 .. m-1, in
// increasing order, each deduplicating.
//
// Legality of the split order: a MergeSplit on bit b needs both operands routed
// on bits [0, b).  Cross level b's older operand is the 2^b-bucket block
// L_(b-1), routed on 0..b-1 by its own butterfly in phase 1; its fresher
// operand is the prefix [0, 2^b), routed on 0..b-1 by the cross levels below it
// (and, at b = s, by the two smallest blocks' butterflies).  The resulting
// MergeSplit set, input states, outputs and shed residuals are identical to the
// flat level-by-level butterfly.
//
// `level_stashes` is indexed by absolute butterfly bit, exactly as in
// ButterflyRouteStash: intra- and cross-source MergeSplits on bit b share
// level_stashes[b], and dedup only ever removes entries before a split, so a
// level's shed count can only go down relative to the no-dedup bound.
template <bool CheckOverflow = false>
inline bool RouteBinarySourcesDedup(TableView t, unsigned first_block_log2,
                                    ResidualStash* level_stashes) {
  const size_t num_buckets = t.num_buckets;
  if (num_buckets <= 1) return true;
  const unsigned m = Log2Exact(num_buckets);
  assert(num_buckets == (size_t{1} << m));
  assert(first_block_log2 >= 1 && first_block_log2 <= m);
  assert(t.layout.tag_bytes * 8 >= m);

  const unsigned blocks = BinarySourceBlockCount(m, first_block_log2);
  for (int j = static_cast<int>(blocks) - 1; j >= 0; --j) {
    size_t offset, size;
    BinarySourceBlock(first_block_log2, static_cast<unsigned>(j), &offset,
                      &size);
    if (!ButterflyRouteStashCacheOblivious<CheckOverflow>(
            SubView(t, offset, size), Log2Exact(size), level_stashes)) {
      return false;
    }
  }
  for (unsigned bit = first_block_log2; bit < m; ++bit) {
    if (!CrossSourceLevelDedup<CheckOverflow>(t, bit, level_stashes[bit], 0,
                                              size_t{1} << bit)) {
      return false;
    }
  }
  return true;
}
// ---------------------------------------------------------------------------
//
// RouteBinarySourcesDedup routes one contiguous input in place.  A rebuild
// whose sources are simultaneously serving probes cannot do that: a step READS
// its two inputs and WRITES a fresh output.  The reference chain
//
//     T_0 = the frozen online stash
//     T_{j+1} = merge(T_j, L_j)          laid out as [ T_j | L_j ]
//     level t = T_t
//
// is the SAME network -- T_j is exactly the prefix [0, 2^b) after cross level
// b, and each step is exactly one CrossSourceLevelDedup -- issued so that every
// intermediate is a complete, probeable hash table on the bits routed so far.
// Publishing them would bound the probe list at two tables per size class
// (step j releases L_j instead of holding every source to the end); the
// level-arena engine does not publish them, and these kernels serve as the
// reference its phase planners are tested against.
//
// Two consequences the callers rely on:
//
//  - The whole chain shares ONE nonce.  Its members are never live together
//    (publishing T_{j+1} retires T_j and L_j in the same swap) and their
//    windows all end at the snapshot instant, so the "at most one real probe
//    per (nonce family, key)" invariant still holds and the incremental
//    schedule costs the same as the monolithic one rather than 2x.  L_j is
//    therefore re-tagged under the rebuild's nonce before it is routed, while
//    T_j's tags are already correct and its low bits already routed.
//  - `route_levels` is the depth of the WHOLE chain (log2 of the final table's
//    bucket count), not of this step: it is what decides how many tag bytes
//    ComputeRoutingTags lays down, and the bytes a later step needs must be
//    written now.

// Scatters the dense online-stash bucket into `out` (64 -> num_buckets x
// 64/num_buckets, load 0.25 or 0.5 alike), tags it under the rebuild's nonce
// and routes its own butterfly: the head of the chain, T_0.
template <bool CheckOverflow = false>
inline bool BuildIncrementalChainHead(
    TableView out, const uint8_t* dense_bucket, uint64_t dense_mask,
    uint64_t nonce_lo, uint64_t nonce_hi, unsigned route_levels,
    ResidualStash* level_stashes,
    const AesTagKeys& aes_keys = DefaultAesTagKeys()) {
  ScatterDenseBucket(dense_bucket, dense_mask, out.data, out.masks,
                     kBucketCapacity / out.num_buckets, out.layout.EntryBytes(),
                     out.layout.PayloadLines());
  ComputeRoutingTags(out, nonce_lo, nonce_hi, {}, route_levels, aes_keys);
  return ButterflyRouteStashCacheOblivious<CheckOverflow>(
      out, Log2Exact(out.num_buckets), level_stashes);
}

// Fills the UPPER half of a step's output with `older` (= L_j): copy, re-tag
// under the rebuild's nonce, and run its own butterfly.  Split out because this
// is the entire half of a step that does not depend on T_j.  Only the tests
// call it: it is the unfused oracle for the planners' fused copy-and-re-tag
// (PlanPrepareOlderHalf).
//
// The copy moves whole buckets rather than payload lines: the tag lines are
// overwritten by the re-tag immediately after, and one contiguous memcpy per
// bucket beats a strided per-line one.
template <bool CheckOverflow = false>
inline bool PrepareIncrementalUpperHalf(
    TableView out, TableView older, uint64_t nonce_lo, uint64_t nonce_hi,
    unsigned route_levels, ResidualStash* level_stashes,
    const AesTagKeys& aes_keys = DefaultAesTagKeys()) {
  const size_t half = out.num_buckets / 2;
  assert(older.num_buckets == half);
  const size_t bucket_bytes = out.layout.BucketBytes();
  std::memcpy(out.data + half * bucket_bytes, older.data, half * bucket_bytes);
  std::memcpy(out.masks + half, older.masks, half * sizeof(uint64_t));
  TableView upper = SubView(out, half, half);
  ComputeRoutingTags(upper, nonce_lo, nonce_hi, {}, route_levels, aes_keys);
  return ButterflyRouteStashCacheOblivious<CheckOverflow>(upper, Log2Exact(half),
                                                          level_stashes);
}

// One step of the chain: out = merge(fresher, older), physically [fresher |
// older] so every in-place kernel applies unchanged.  `fresher` is T_j, already
// routed on bits [0, bit) under this nonce; `older` is L_j.  With
// `upper_prepared` the caller has already run PrepareIncrementalUpperHalf into
// `out`, and only the lower-half copy and the cross-source level remain.
template <bool CheckOverflow = false>
inline bool IncrementalMergeStep(
    TableView out, TableView fresher, TableView older, uint64_t nonce_lo,
    uint64_t nonce_hi, unsigned route_levels, ResidualStash* level_stashes,
    bool upper_prepared = false,
    const AesTagKeys& aes_keys = DefaultAesTagKeys()) {
  const size_t half = out.num_buckets / 2;
  assert(fresher.num_buckets == half);
  const unsigned bit = Log2Exact(half);
  const size_t bucket_bytes = out.layout.BucketBytes();
  std::memcpy(out.data, fresher.data, half * bucket_bytes);
  std::memcpy(out.masks, fresher.masks, half * sizeof(uint64_t));
  if (!upper_prepared &&
      !PrepareIncrementalUpperHalf<CheckOverflow>(
          out, older, nonce_lo, nonce_hi, route_levels, level_stashes,
          aes_keys)) {
    return false;
  }
  return CrossSourceLevelDedup<CheckOverflow>(out, bit, level_stashes[bit], 0,
                                              half);
}

// The fixed last level's final merge.  Unlike every other level,
// the largest one absorbs itself, so its rebuild ends with two sources of its
// own size and no free slot to land in:
//
//     fresher = B, the chain's output T_L, routed under the rebuild's nonce
//     older   = C, a PRIVATE copy of the old resident level L, re-tagged and
//               routed under the same nonce -- and the destination
//
// Both are routed on all log2(M) index bits under one nonce, so every copy of a
// key in either source sits in bucket tag(k) mod M and all cross-source
// duplicates are confined to the single pair (B[i], C[i]).  So the merge needs
// no double-sized staging table, no extra routing bit and no pairwise fold:
// merging B[i] into C[i] is the whole of bucket i's union.
//
// B owns the newer window and wins every conflict, which is the ordinary
// operand order.  Two things are easy to get wrong and fatal:
//
//  - MergeBucketIntoWithStash ZEROES *src_mask, and B is still live in the old
//    probe plan until the publication that follows, so it is passed a COPY.
//    (Its bytes it already leaves alone.)
//  - C is a private workspace, never a source slab.  Copying a live source
//    somewhere else does not retire it: until the replacement is published and
//    the old readers have drained, the old plan still names the old level L.
//
// A residual here comes from B, the FRESHER operand -- unlike a cross-source
// MergeSplit, which sheds from the older one -- and C has already had every
// duplicate of a B key cleared, so a shed entry is the only surviving copy of
// its key and has nothing to conflict with.  At load 0.25 `stash` is
// zero-capacity and a shed is a hard rebuild failure.
//
// Bucket pairs are independent -- the sweep never moves an entry between
// indices -- so it is range-parameterized like the cross-source level, which is
// what lets the scheduler issue it in slices.
//
// WHICH OF B'S TOMBSTONES TAKE A SLOT IN C.  This sweep is followed, in the same
// item, by kDropErased over C, so no tombstone it writes outlives the item; the
// only question is whether one occupies a slot WHILE the item routes.  One that
// does is capacity the live set cannot use: a map filled to capacity() that
// erases half its keys and writes as many new ones has 1.5x capacity() entries
// in C until the tail drop, which is load 0.75 against a stash sized for 0.5.
// Whatever the policy, the skip is applied to `src_mask` -- the merge's
// private copy -- and NOT to the dedup above it: the dedup still sees every
// tombstone and still clears C's copy of its key, so a tombstone that is left
// out has finished its shadowing job in C by the time it is left out.
//
//  - kMerge: every tombstone is merged.  An item that may not forget one.
//  - kUnshadowed: THE UNSHADOWED SKIP -- a tombstone marked as having no
//    older live copy (kMetaUnshadowed, cpu_byteslice_meta.hpp: its access
//    found no copy of the key, or found an unshadowed tombstone) has nothing
//    to shadow, so it is left out, whatever else is still to come.
//  - kAll: every tombstone is left out.  Exact only when no STALER copy of any
//    of B's keys can still reach C after the sweep -- every older copy is in C
//    already, where the dedup clears it -- and the caller has to know that:
//    here it means no staler residual pass follows (RunSubtask checks the
//    context), and the offer-fused twin in cpu_byteslice_second_chance.hpp
//    clears matching older residuals before omitting the tombstones.
//
// Leaving a tombstone out never resurrects anything under those conditions,
// and it keeps the tombstone doing its position job exactly as long as
// before: B is not written, stays probeable until this item publishes, and the
// output forgets the tombstone at this item either way.
enum class FixedMergeTombstones : uint8_t { kMerge, kUnshadowed, kAll };

// B's tombstones that the sweep leaves out of C unconditionally under `skip`,
// and the ones kAll omits after resolving older residual copies (`shadowing`,
// zero under the other two policies). One meta-line read.
struct FixedMergeSkip {
  uint64_t always = 0;
  uint64_t shadowing = 0;
};

inline FixedMergeSkip FixedMergeSkippedSlots(const uint8_t* b,
                                             size_t meta_offset,
                                             FixedMergeTombstones skip) {
  FixedMergeSkip out;
  if (skip == FixedMergeTombstones::kMerge) return out;
  out.always = UnshadowedSlotMask(b, meta_offset);
  if (skip == FixedMergeTombstones::kAll) {
    out.shadowing = ErasedSlotMask(b, meta_offset) & ~out.always;
  }
  return out;
}

template <bool CheckOverflow = false>
inline bool MergeFixedLevelSourcesRange(
    TableView older, TableView fresher, ResidualStash& stash, size_t begin,
    size_t end, FixedMergeTombstones skip = FixedMergeTombstones::kMerge) {
  assert(older.num_buckets == fresher.num_buckets);
  assert(end <= older.num_buckets);
  const size_t bucket_bytes = older.layout.BucketBytes();
  const size_t lines = older.layout.PayloadLines();
  const size_t key_bytes = older.layout.key_bytes;
  const size_t meta_offset = older.layout.MetaLine();
  for (size_t i = begin; i < end; ++i) {
    uint8_t* b = fresher.data + i * bucket_bytes;
    uint8_t* c = older.data + i * bucket_bytes;
    older.masks[i] &= ~CrossBucketDuplicateMask(b, fresher.masks[i], c,
                                                older.masks[i], key_bytes);
    // See above: B stays live, and nothing staler follows this form.
    const FixedMergeSkip skipped = FixedMergeSkippedSlots(b, meta_offset, skip);
    uint64_t src_mask =
        fresher.masks[i] & ~(skipped.always | skipped.shadowing);
    if (!MergeBucketIntoWithStash<CheckOverflow>(c, b, &older.masks[i],
                                                 &src_mask, lines, stash)) {
      return false;
    }
  }
  return true;
}

template <bool CheckOverflow = false>
inline bool MergeFixedLevelSources(TableView older, TableView fresher,
                                   ResidualStash& stash) {
  return MergeFixedLevelSourcesRange<CheckOverflow>(older, fresher, stash, 0,
                                                    older.num_buckets);
}
// ---------------------------------------------------------------------------
//
// Base B leaves exactly two places where a table's bucket count is m * 2^K with
// m not a power of two -- the absorb of a level into itself at a non-power-of-
// two digit, and the fixed last level's final merge.  Everything else stays on
// the binary network.  Both need r-1 ORDERED dedup pairs per group, NOT
// the r(r-1)/2 an all-pairs reading would suggest, and the reason is the same
// in both cases: only ONE of the r buckets in a group can hold an entry from
// the fresher source.

// The radix pass with a dedup prologue: RadixPassStashRange plus, in each
// stride tuple, r-1 ordered (bucket 0, bucket q) duplicate clears.
//
// Why bucket 0 alone is the fresher side.  The absorb's output blocks
// 1 .. r-1 are pure L_t^old, and L_t^old holds each key at most once, so no two
// of them can hold the same key; block 0 is the only one carrying anything from
// the chain temporary T_t.  A duplicate is therefore always (block 0, block q)
// and the stale copy always the block-q one -- which is exactly r-1 clears,
// each of them the ordinary CrossBucketDuplicateMask a binary cross level runs.
//
// Cost is (m - 2^e)*2^K dedups against a binary cross level's M/2, the same
// order, and it happens once per carry.
template <bool CheckOverflow = false>
inline bool RadixPassDedupStashRange(TableView t, unsigned block_bits,
                                     unsigned r, ResidualStash& stash,
                                     size_t begin, size_t end) {
  if (r <= 1) return true;
  const size_t block = size_t{1} << block_bits;
  assert(t.num_buckets == block * r);
  assert(r <= kMaxRadix);
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
    // The prologue.  Bucket 0 is the fresher operand and keeps every copy; a
    // block-q copy of one of its keys dies before the MergeSplit sees it, so
    // the pass routes a duplicate-free tuple exactly as the binary network
    // routes a deduplicated cross level.
    DedupBucketDestinations(bptr[0], *mptr[0], bptr + 1, mptr + 1,
                             r - 1, key_bytes);
    if (!MergeSplitRadixStash<CheckOverflow>(bptr, mptr, r, lines, digit_line,
                                             t.layout.digit_bits, stash)) {
      return false;
    }
  }
  return true;
}

// WHERE ONE SOURCE BUCKET'S DIGITS COME FROM.
//
// Normally: the digit byte the kRadixDigit re-tag laid down in the source
// itself, because the same rebuild routed it.  The level arena's TOP is the
// one case where that is not so: its carry is an immutable inbox table (the
// table a lower level publishes for the top to consume; see
// src/oram/levelarena/DESIGN.md) built under its PRODUCER's map, whose
// stored digit line says nothing about which of the top's D blocks an entry
// belongs to.  Setting `map` recomputes the digit from the bucket's keys
// instead, under this merge's nonce, map and instance key.
//
// It is the whole of that re-tag.  The merge reads no other tag line of its
// source and moves only PAYLOAD lines out of it, so there is nothing a
// re-tagged COPY of the bucket would offer that the bucket itself does not --
// see ComputeBucketDigitLine, which is also why the digit is recomputed here
// rather than in a scratch buffer.
//
// Built by MakeFixedMergeRetag, which validates the fan-in and derives
// everything about the way but the keys once per merge (PlanBucketWay) rather
// than once per source bucket.
struct FixedMergeRetag {
  const RoutingIndexMap* map = nullptr;  // null: read the stored digit line
  const AesTagKeys* aes_keys = nullptr;
  BucketWayPlan way;
};

// `carry_bits` is log2 of the carry, i.e. the index bits the carry's own
// placement fixed.  A binary top's way is the raw tag's bits just above them
// (ComputeBucketWayLine); a whole-digit map's way does not read it.  `ways`
// is the r of the merge the retag serves.
inline FixedMergeRetag MakeFixedMergeRetag(const RoutingIndexMap& map,
                                           uint64_t nonce_lo,
                                           uint64_t nonce_hi,
                                           const AesTagKeys& aes_keys,
                                           unsigned carry_bits,
                                           unsigned ways) {
  FixedMergeRetag retag;
  retag.map = &map;
  retag.aes_keys = &aes_keys;
  retag.way = PlanBucketWay(map, nonce_lo, nonce_hi, carry_bits, ways);
  return retag;
}

// At r = 1 there is nothing to split: the whole bucket goes to the one
// destination, which is MergeFixedLevelSourcesRange exactly.  So no way is
// read and none is recomputed -- which is also why the top at D = 1 needs no
// re-tag at all.
//
// With a re-tag, the way is recomputed from the keys under the merge's own
// map, which is the ONLY spelling that serves both a whole-digit map and the
// level arena's binary top (ComputeBucketWayLine).  Without one, the way is
// the digit line the same rebuild stored -- which presumes a whole-digit map,
// as every stored-digit caller has.
inline __m512i FixedMergeSourceDigits(const uint8_t* bucket,
                                      const Layout& layout, unsigned r,
                                      const FixedMergeRetag* retag) {
  if (r == 1) return _mm512_setzero_si512();
  if (retag != nullptr && retag->map != nullptr) {
    assert(retag->way.ways == r);
    return ComputeBucketWayLine(bucket, layout, *retag->map, retag->way,
                                *retag->aes_keys);
  }
  return NormalizeDigitLine(
      _mm512_load_si512(reinterpret_cast<const void*>(
          bucket + layout.DigitLine() * kBucketCapacity)),
      layout.digit_bits);
}

// ONE SOURCE BUCKET, dedup-and-merged into each of its r destinations.
//
// The body of the fixed level's sweep, factored out because its offer-fused
// twin (MergeFixedLevelSourcesOffersRange, second_chance.hpp) runs exactly
// this and differs only in what it does to a destination bucket once B's
// entries for it have been selected.  That difference is `merge_into`; the
// direction split, the ordered clears and the private per-direction masks --
// which is the part that is easy to get wrong -- are here once.
//
// `merge_into(c, b, dst_mask, src_mask, shadowing, direction, ci)` returns
// false on stash overflow.  `src_mask` has the unconditional skip applied
// already; `shadowing` is the part of it kAll omits after the caller resolves
// any older residual copies at that destination (see FixedMergeTombstones);
// `direction` is B's whole direction, skipped tombstones included, for a
// caller that resolves other copies against every one of B's keys.
template <typename MergeInto>
inline bool MergeRadixSourceBucket(TableView older, const uint8_t* b,
                                   uint64_t b_real, __m512i digits, unsigned r,
                                   size_t block, size_t i,
                                   FixedMergeTombstones skip,
                                   MergeInto&& merge_into) {
  const size_t bucket_bytes = older.layout.BucketBytes();
  const size_t key_bytes = older.layout.key_bytes;
  const size_t meta_offset = older.layout.MetaLine();
  assert(r >= 1 && r <= kMaxFixedMergeWays);
  uint8_t* destinations[kMaxFixedMergeWays];
  uint64_t* destination_masks[kMaxFixedMergeWays];
  for (unsigned q = 0; q < r; ++q) {
    const size_t ci = i + static_cast<size_t>(q) * block;
    destinations[q] = older.data + ci * bucket_bytes;
    destination_masks[q] = &older.masks[ci];
  }
  DedupBucketDestinations(b, b_real, destinations, destination_masks, r,
                          key_bytes);
  // The skip, exactly as in the binary twin: B's copy only, never the dedup
  // above and never B itself.
  const FixedMergeSkip skipped = FixedMergeSkippedSlots(b, meta_offset, skip);
  for (unsigned q = 0; q < r; ++q) {
    // A COPY, and only this direction's entries: B stays live, and the merge
    // would otherwise hand every destination the whole bucket.
    // The register-only compare, as in the radix split: `b_real` is secret
    // and would become the compare's write mask.
    const uint64_t direction =
        r == 1 ? b_real
               : (core::obliCmpEqMask8(
                      digits, _mm512_set1_epi8(static_cast<char>(q))) &
                  b_real);
    const uint64_t src_mask = direction & ~skipped.always;
    const size_t ci = i + static_cast<size_t>(q) * block;
    if (!merge_into(destinations[q], b, destination_masks[q], src_mask,
                    src_mask & skipped.shadowing, direction, ci)) {
      return false;
    }
  }
  return true;
}

// The mixed-radix twin of MergeFixedLevelSourcesRange.
//
//   older   = C, r * 2^K buckets, the old resident level L re-tagged and routed
//             under the new nonce on the map (K, r)
//   fresher = B, 2^K buckets, the chain's output, routed under the same nonce
//             on bits [0, K)
//
// Unlike the binary sweep, B and C differ in size, which is the whole
// difference.  But K is
// exactly the map's low_bits, so **B's bucket i holds precisely the entries
// destined for the tuple {C[i + q*2^K]}** -- every cross-source duplicate is
// confined to that tuple, which is what keeps the dedup local and the sweep a
// fixed linear scan of both tables.
//
// r dedups per B bucket = M dedups over the whole sweep: the same rate as the
// binary MergeFixedLevelSourcesRange, not r times it.
//
// The two traps of the binary sweep carry over and are now r-fold:
//
//  - MergeBucketIntoWithStash ZEROES *src_mask, and B is still live in the old
//    probe plan until publication, so each of the r merges is handed its own
//    COPY of B's mask restricted to that direction.
//  - C is a private workspace, never A's slab.  Copying a live source somewhere
//    else does not retire it.
//
// A shed here comes from B, the FRESHER operand, and C has already had every
// duplicate of a B key cleared, so a shed entry is the only surviving copy of
// its key -- the binary sweep's argument, and with it the pass-2
// kResidualWins rule, is unchanged.
//
// Ranged over B's buckets, which is also the tuple index, so disjoint ranges
// touch disjoint buckets of both tables and the scheduler may slice it.
//
// No residual is offered inside this form, so kAll leaves every tombstone out;
// the caller vouches that nothing staler follows (FixedMergeTombstones).

template <bool CheckOverflow = false>
inline bool MergeRadixLevelSourcesRange(
    TableView older, TableView fresher, unsigned r, ResidualStash& stash,
    size_t begin, size_t end,
    FixedMergeTombstones skip = FixedMergeTombstones::kMerge,
    const FixedMergeRetag* retag = nullptr) {
  assert(r >= 1 && r <= kMaxFixedMergeWays);
  const size_t block = fresher.num_buckets;
  assert(older.num_buckets == block * r);
  assert(end <= block);
  const size_t bucket_bytes = older.layout.BucketBytes();
  const size_t lines = older.layout.PayloadLines();
  for (size_t i = begin; i < end; ++i) {
    const uint8_t* b = fresher.data + i * bucket_bytes;
    const bool ok = MergeRadixSourceBucket(
        older, b, fresher.masks[i],
        FixedMergeSourceDigits(b, older.layout, r, retag), r, block, i, skip,
        [&](uint8_t* c, const uint8_t* src, uint64_t* dst_mask,
            uint64_t src_mask, uint64_t shadowing, uint64_t, size_t) {
          src_mask &= ~shadowing;
          return MergeBucketIntoWithStash<CheckOverflow>(
              c, src, dst_mask, &src_mask, lines, stash);
        });
    if (!ok) return false;
  }
  return true;
}

template <bool CheckOverflow = false>
inline bool MergeRadixLevelSources(TableView older, TableView fresher,
                                   unsigned r, ResidualStash& stash) {
  return MergeRadixLevelSourcesRange<CheckOverflow>(older, fresher, r, stash, 0,
                                                    fresher.num_buckets);
}

}  // namespace byteslice
}  // namespace microram
