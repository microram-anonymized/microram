#pragma once

// What a subtask is issued against, and the dispatcher that runs one.
//
// RebuildStepContext is everything a slice needs beyond its own [begin, end):
// the source and destination views, the nonce, the stashes, the residual
// passes.  Keeping it out of the Subtask is what lets a plan be a flat list a
// cursor can hold across stops and resume.
//
// RunSubtask is a switch, and deliberately nothing more.  Each arm calls the
// range-parameterized kernel the corresponding monolithic phase would have
// called, over the subtask's range, with no state carried between arms -- so
// running a plan in order is indistinguishable from running the phases whole,
// and running it in slices is indistinguishable from running it in one go.

#include <immintrin.h>

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "src/oram/scheduler/cpu_byteslice_subtask.hpp"
#include "src/oram/scheduler/cpu_byteslice_subtask_cost.hpp"
#include "src/oram/rebuild/cpu_byteslice_dense_select.hpp"
#include "src/oram/rebuild/cpu_byteslice_dfs_residual.hpp"

namespace microram {
namespace byteslice {

// ---------------------------------------------------------------------------
// What a subtask is issued against
// ---------------------------------------------------------------------------

// The immutable operands of one rebuild step.  A step reads `fresher` and
// `older` and writes `out` -- it must not mutate its inputs, which are
// simultaneously serving probes -- so every subtask of one step shares this and
// carries only its range.
//
// The shapes it takes:
//
//   direct B build  fresher = B's main (written), small_old = the published
//                   prefix, small_log = it with private remaining masks,
//                   dense_homes = the home cache, dense_tier = B's leftovers
//   merge step      out = [T_j | L_j], fresher = T_j, older = L_j,
//                   upper_offset = |T_j|
//   fixed workspace out = C, older = A, upper_offset = 0
//   fixed merge     out = C, fresher = B

// One residual second chance, as the subtasks of one step see it.  A step runs
// three, and they are separate rather than pooled because each is a freshness
// CLASS with a dedup rule that is exact for it and wrong for the others.
//
//   pass 0  kNoDedup       the block's own butterfly shed, back into the block,
//                          which cannot hold a duplicate of it.  Leftovers wait
//                          in the carry.
//   pass 1  kTableWins     the carry, into the finished output, where every
//                          entry is either from a fresher source or from the
//                          carry's own block (which holds each key once).
//   pass 2  kResidualWins  what a cross-source level or the fixed merge shed,
//                          pass 1's survivors, and the fresher operand's second
//                          tier -- all of them provably the surviving copy.
struct ResidualPass {
  bool active = false;
  TableView range;   // all offer storage, including an optional direct tail
  TableView main;    // what the residuals are offered back to
  ResidualRangePlan plan;
  // `range` owns A leaves followed by one private retagged copy of B.
  // With no direct slots, the whole pool is distributed as before.
  // Dedup and drain see the combined inventory; only A enters the distributor.
  size_t direct_slots = 0;
  size_t direct_buckets = 0;
  // The DFS distributor, configured for this pass, when `plan` is a
  // DfsResidualRangePlan: it gathers the swept pool and partitions it into
  // `range`, the stacked leaf table, instead of the scatter/retag/route.
  // Null everywhere else.
  DfsResidualWorkspace* dfs = nullptr;
  // What the partition costs (DfsResidualWorkspace::PriceOf), which is what
  // the planner charges it; zero units on every pass that is not DFS.  Set
  // with `dfs` by AttachResidualDfs, or alone on a pass that is only planned
  // and priced, never run (LevelArenaResidualPrefixTouches).
  DfsResidualWorkspace::Price dfs_price;
  // What feeds the range table: the job's butterfly-level stashes and carry,
  // plus -- as the trailing entries -- the second tier of a table this rebuild
  // is consuming.  Pointers rather than a contiguous array because the two
  // classes live in different places, and read live rather than snapshotted
  // because the reset is then its own subtask (kResidualReset) at the end.
  ResidualStash* const* pool = nullptr;
  // Public freshness order over `pool`, lower = fresher.  Two slots share
  // a rank exactly when they draw from one source table and so cannot hold two
  // copies of a key between them; otherwise the fresher slot wins, which is
  // what keeps a stale shed copy from surviving the pool dedup.
  const uint8_t* rank = nullptr;
  size_t pool_slots = 0;
  size_t reset_slots = 0;          // leading pool entries the job owns
  // Leading pool slots that skip the range table and the sweep: shed classes
  // that are provably unabsorbable at this step -- an entry sheds only
  // because its target bucket is FULL, and it can have no duplicate there (a
  // duplicate would have cleared it at the dedup prologue, not shed it), so
  // no resolution can free it a slot.  They go straight to the drain, after
  // the pool dedup, which still covers every slot; the plan and range are
  // sized from the remaining (swept) suffix alone.  Which slots are
  // drain-only is a public function of the pass, so the schedule stays
  // data-independent.
  size_t drain_only = 0;
  // False when the swept suffix has zero capacity and the pass is not forced:
  // capacity is public, so a provably empty range table plans no
  // scatter/retag/route/sweep at all.  The pool dedup, the drain
  // of the drain-only slots and the reset still run.
  bool sweep_active = true;
  // Where the pass's offers run instead of a standalone kResidualSweep:
  // kCrossLevel rides the step's cross-source level (kCrossLevelOffers, the
  // chain step's carry and tier passes), kOwnLastLevel rides the last level
  // of the pass's own butterfly (kButterflyLevelOffers, pass 0).  Either way
  // the range table is built BEFORE that pass and drained after it, and no
  // sweep subtasks are planned.  Which passes fuse, and where, is public.
  ResidualFuseSite fuse = ResidualFuseSite::kNone;
  ResidualStash* drain = nullptr;  // the carry, or the published second tier
  ResidualDedupRule rule = ResidualDedupRule::kNoDedup;
  size_t lines = 0;  // what an absorbed entry has to carry
  // kClassMark only (the class-marked offer, src/oram/rebuild/DESIGN.md): the flat
  // SWEPT-pool bucket index where the tier class begins -- the retag stamps
  // kMetaResidualClass on every range bucket fed from a pool bucket at or past
  // it, and clears it below.  SIZE_MAX on every single-rule pass.
  size_t tier_class_from = SIZE_MAX;
  // The FLAT DESTINATION INDEX map.  The sweep pairs main bucket b with
  // residual bucket b >> index_bits and matches on the low index_bits of the
  // stored tag, so a residual has to be tagged with where it is GOING, not with
  // the raw hash.  On a power-of-two main those are the same word and this
  // stays kRaw; on a mixed-radix one it is the rebuild's own map with
  // digit_shift = low_bits, which packs idx(T) contiguously.
  RoutingIndexMap map;
};

inline size_t DistributedPoolSlots(const ResidualPass& rp) {
  return rp.pool_slots - rp.drain_only - rp.direct_slots;
}
inline TableView DistributedResidualRange(const ResidualPass& rp) {
  TableView view = rp.range;
  view.num_buckets -= rp.direct_buckets;
  return view;
}
inline TableView DirectResidualRange(const ResidualPass& rp) {
  TableView view = rp.range;
  const size_t offset = view.num_buckets - rp.direct_buckets;
  // Descriptor-only cost planning also calls this with null storage.
  if (view.data != nullptr) view.data += offset * view.layout.BucketBytes();
  if (view.masks != nullptr) view.masks += offset;
  view.num_buckets = rp.direct_buckets;
  return view;
}
inline ResidualRangePlan DirectResidualPlan(const ResidualPass& rp) {
  return DirectResidualRangePlan(rp.direct_buckets,
                                 Log2Exact(rp.main.num_buckets));
}

struct RebuildStepContext {
  // THE UNSHADOWED SKIP.  A tombstone (an erase marker) is UNSHADOWED,
  // metadata bit kMetaUnshadowed (src/oram/table/cpu_byteslice_meta.hpp),
  // when no live copy of its key older than it exists anywhere in the
  // hierarchy, so it shadows nothing and dropping it cannot resurrect a
  // stale value.  Set
  // for exactly the items that are allowed to forget a tombstone -- a carry
  // into the last level, at the item kDropErased runs at (the level arena sets
  // it on its top's jobs).  Every subtask that READS
  // a source table into this item's output then ANDs the source's unshadowed
  // tombstones out of ITS OWN COPY of the occupancy word: kCopyFresher, the
  // fused copy-and-re-tags and the residual scatter.  The fixed merge, in
  // both its shapes, goes further and leaves out every tombstone that nothing
  // staler can still need (FixedMergeTombstonesOf).  The source table is
  // never written -- it is still probeable, and the tombstone is still doing
  // its job, until this item publishes.
  bool drop_unshadowed = false;
  // Top and separated ordinary fixed insertions read a published carry.
  // Its producer's stored digit does not identify this output's way, so
  // recompute it from the key, nonce and final map. The sweep reads no other
  // source tag line and moves only payload (FixedMergeRetag).
  // Other routes prepare their source tags themselves. At radix one no
  // way is needed and this flag is inert.
  bool retag_fresher_digits = false;
  // THE OLDER SOURCE IS ALREADY IN THE WORKSPACE, so there is nothing to copy
  // and only the tags have to be written (Subtask::kRetagRange, which exists
  // for exactly this).  It is how a DIRECT INITIALIZATION reaches the ordinary
  // preparation (src/oram/rebuild/DESIGN.md, "Initialize directly into the
  // final table"; src/oram/levelarena/DESIGN.md, "Direct initialization"): the
  // records are scattered straight into the destination region at its final
  // load, so `older` and `out` are the same bytes and the fused
  // copy-and-re-tag would be a self-copy -- one whole extra read and write of
  // the table for nothing.
  //
  // A CONTEXT FLAG AND NOT A PLANNER, for the same reason
  // `retag_fresher_digits` is one: everything after the arrival -- the block
  // butterflies, the radix pass, the fused residual second chance and its
  // drain -- is what an ordinary preparation does, and a second planner
  // spelling it out again would be a second chance to spell it differently.
  bool source_in_place = false;
  // A free proof, checked builds only, no behaviour attached: `older` is known
  // to hold no tombstone at all, because the rebuild that produced it was
  // itself a carry into the last level and cleared them at its tail.  True for
  // the fixed preparation (older = A, the old last level) and for a growth
  // carry's absorb (older = the same level at the previous digit); false
  // everywhere else, where `older` is an ordinary level and tombstones are
  // expected.
  bool older_tombstone_free = false;
  // All views are fixed public extents, in the normal byte-sliced layout.
  // small_log is private output; source views remain immutable through epoch
  // retirement.
  TableView small_log;
  TableView small_old;
  TableView out;
  TableView fresher;
  TableView older;
  size_t upper_offset = 0;  // where `older` lands inside `out`
  uint64_t nonce_lo = 0;
  uint64_t nonce_hi = 0;
  // Depth of the WHOLE chain, not of this step: it decides how many tag bytes
  // the re-tag lays down, and the bytes a later step will route have to be
  // written now.
  unsigned route_levels = 0;
  // Indexed by absolute butterfly bit, exactly as in ButterflyRouteStash.
  ResidualStash* level_stashes = nullptr;
  // Where the fixed level's final merge sheds.  It is not a butterfly level,
  // so it does not share the array above.
  ResidualStash* merge_stash = nullptr;
  // Where a mixed-radix pass sheds, for the same reason: it is one more stage
  // past the last butterfly bit, not one of them.
  ResidualStash* radix_stash = nullptr;
  // ONE map per rebuild, public and fixed at its trigger: every re-tag of the
  // rebuild -- head, chunk, absorb, C <- A -- stores map(tag) rather than the
  // raw tag, so all
  // members of the nonce family agree on the index function.  kRaw (the
  // default) is every power-of-two table, i.e. all of B = 2.
  RoutingIndexMap map;
  const AesTagKeys* aes_keys = &DefaultAesTagKeys();
  // Empty (`active == false`) at load 0.25, where a shed is a hard rebuild
  // failure and there is nothing to give a second chance to.
  ResidualPass residual[kResidualPasses];
  // Level one's direct B build (cpu_byteslice_dense_select.hpp): the cached
  // home lines of every prefix lane, and where B's leftovers drain -- B's
  // one-bucket tier above digit one, the output tier at digit one.  B's main
  // is `fresher`, U buckets, which the build writes and the fixed insertion
  // then reads.
  uint8_t* dense_homes = nullptr;
  ResidualStash* dense_tier = nullptr;
  // The second tier THIS item publishes beside `out` -- the final pass's
  // drain, freshly acquired for the item -- or null when it publishes none
  // (a head, load 0.25, a hand-built test context).  Public identity, secret
  // content, like every stash.  It exists so the tombstone drop can reach the
  // tier without knowing which pass drained into it (kDropErasedTier); the
  // borrowed tiers in the passes' pools are never named here.
  ResidualStash* tier_out = nullptr;
};

// Which of the fresher operand's tombstones the fixed merge leaves out of the
// output (FixedMergeTombstones), read off the context.  Only an item that may
// forget a tombstone at all (`drop_unshadowed`, the level arena's top) leaves
// any out, and it leaves out EVERY one -- the capacity a live set of
// capacity() needs while the item routes -- unless some pass that could still
// offer a staler copy of a key runs outside the sweep.  A pass fused into the
// sweep has its older copies cleared inside it; a kResidualWins pass holds
// nothing staler than the fresher operand, or its rule would be wrong.  The
// level arena's top has no such pass, so this is its whole policy; the
// fallback keeps a hand-built context with a standalone carry pass exact.
inline FixedMergeTombstones FixedMergeTombstonesOf(
    const RebuildStepContext& ctx) {
  if (!ctx.drop_unshadowed) return FixedMergeTombstones::kMerge;
  for (unsigned pass = 0; pass < kResidualPasses; ++pass) {
    const ResidualPass& rp = ctx.residual[pass];
    if (!rp.active || !rp.sweep_active) continue;
    if (rp.fuse == ResidualFuseSite::kFixedMerge) continue;
    if (rp.rule == ResidualDedupRule::kResidualWins) continue;
    return FixedMergeTombstones::kUnshadowed;
  }
  return FixedMergeTombstones::kAll;
}

// The top's key-only resolution before each destination's merge
// (ResolveTopDestination): per public group, the candidate match and two
// intersects -- older candidates against B's direction, C against fresher
// candidates -- whatever the rule, since both run with possibly empty masks:
// two units, as a class-marked offer's two compare nests.  The offer after it
// then allocates without dedup (MergeFixedLevelSourcesOffersRange), one unit
// where the pass's rule charged two, so the pair is the pass's own weight
// plus one per group.  It is charged even when every secret mask is zero.  The resolution walks every
// offer set, so the top's direct tier (its merge pass is separated, as every
// finish is) counts one unit per bucket too.
inline unsigned TopResolveOfferWeight(const RebuildStepContext& ctx,
                                      ResidualFuseSite site,
                                      const ResidualPass& rp) {
  return site == ResidualFuseSite::kFixedMerge &&
                 FixedMergeTombstonesOf(ctx) == FixedMergeTombstones::kAll
             ? static_cast<unsigned>(rp.plan.groups + rp.direct_buckets)
             : 0;
}

// Whether the fixed merge's sweep resolves every destination before its
// capacity decisions (ResolveTopDestination): the top's kAll with a pass
// riding the sweep.  Its trailing tombstone drops then find nothing, which
// the checked build asserts.
inline bool TopResolutionRuns(const RebuildStepContext& ctx) {
  if (FixedMergeTombstonesOf(ctx) != FixedMergeTombstones::kAll) return false;
  for (unsigned pass = 0; pass < kResidualPasses; ++pass) {
    const ResidualPass& rp = ctx.residual[pass];
    if (rp.active && rp.sweep_active &&
        rp.fuse == ResidualFuseSite::kFixedMerge) {
      return true;
    }
  }
  return false;
}

// The offer sets of every active pass fused at `site`, in pass order, and
// their summed WEIGHT -- touches per output bucket: a class-marked set counts
// two, any other one, each times its plan's GROUPS (only a DIRECT plan at the
// smallest tables has more than one).  The planner sliced the fused pass by
// this same number (FusedOfferWeight), including TopResolveOfferWeight for
// top merges, and every fused arm asserts the two
// agree.  Pass order is the offer order per bucket, which is what the SPLIT
// cross-level shape leans on (carry before tier).
inline size_t GatherFusedOffers(const RebuildStepContext& ctx,
                                ResidualFuseSite site,
                                ResidualOfferSet* offers, unsigned* weight) {
  size_t num_offers = 0;
  *weight = 0;
  for (unsigned pass = 0; pass < kResidualPasses; ++pass) {
    const ResidualPass& rp = ctx.residual[pass];
    if (!rp.active || rp.fuse != site || !rp.sweep_active) continue;
    offers[num_offers].range = DistributedResidualRange(rp);
    offers[num_offers].plan = rp.plan;
    offers[num_offers].rule =
        rp.direct_slots ? ResidualDedupRule::kTableWins : rp.rule;
    offers[num_offers].lines = rp.lines;
    *weight += (rp.direct_slots ? 1u :
                (rp.rule == ResidualDedupRule::kClassMark ? 2u : 1u)) *
               static_cast<unsigned>(rp.plan.groups) +
               TopResolveOfferWeight(ctx, site, rp);
    ++num_offers;
    if (rp.direct_slots) {
      offers[num_offers].range = DirectResidualRange(rp);
      offers[num_offers].plan = DirectResidualPlan(rp);
      offers[num_offers].rule = ResidualDedupRule::kResidualWins;
      offers[num_offers].lines = rp.lines;
      *weight += static_cast<unsigned>(rp.direct_buckets);
      ++num_offers;
    }
  }
  return num_offers;
}

// Where the fixed merge's source digits come from, read off the context.  A
// merge that recomputes them does so under the SAME nonce, map and key every
// other phase of the item uses -- a second coordinate would place the carry's
// entries by a hash they were never placed under.
inline FixedMergeRetag FixedMergeRetagOf(const RebuildStepContext& ctx) {
  if (!ctx.retag_fresher_digits) return FixedMergeRetag{};
  // The merge's r, off the two extents (C is r blocks of B's size); at r = 1
  // no way is read.
  const size_t ways = ctx.out.num_buckets / ctx.fresher.num_buckets;
  if (ways <= 1) return FixedMergeRetag{};
  // The carry's own index bits, off its extent: a binary top's way sits just
  // above them in the raw tag (ComputeBucketWayLine).
  return MakeFixedMergeRetag(ctx.map, ctx.nonce_lo, ctx.nonce_hi,
                             *ctx.aes_keys,
                             Log2Exact(ctx.fresher.num_buckets),
                             static_cast<unsigned>(ways));
}

template <bool CheckOverflow = false>
inline bool RunSubtask(const RebuildStepContext& ctx, const Subtask& task) {
  const Layout& layout = ctx.out.layout;
  const size_t bucket_bytes = layout.BucketBytes();
  switch (task.kind) {
    case Subtask::kPrefixLogDedup: {
      // Unit pair index pu <-> (old, fresh) with fresh >= 1 and old < fresh,
      // numbered fresh*(fresh-1)/2 + old so that the index order IS increasing
      // fresh order.  The loop runs at most r0 <= 8 times.
      const size_t unit = task.levels, units = task.bit;
      assert(unit != 0 && units >= 2 &&
             ctx.small_log.num_buckets == unit * units);
      for (size_t p = task.begin; p < task.end; ++p) {
        size_t pu = p / (unit * unit);
        const size_t within = p % (unit * unit);
        size_t fresh = 1;
        while (pu >= fresh) pu -= fresh++;
        const size_t o = pu * unit + within / unit;
        const size_t f = fresh * unit + within % unit;
        assert(f < ctx.small_log.num_buckets && o < f);
        ctx.small_log.masks[o] &= ~CrossBucketDuplicateMask(
            ctx.small_log.data + f * bucket_bytes, ctx.small_log.masks[f],
            ctx.small_log.data + o * bucket_bytes, ctx.small_log.masks[o],
            layout.key_bytes);
      }
      return true;
    }
    case Subtask::kDenseHomes:
      assert(ctx.dense_homes != nullptr &&
             task.end <= ctx.small_log.num_buckets);
      ComputeDenseHomesRange(ctx.small_log, ctx.dense_homes,
                             Log2Exact(ctx.fresher.num_buckets), ctx.nonce_lo,
                             ctx.nonce_hi, *ctx.aes_keys, task.begin,
                             task.end);
      return true;
    case Subtask::kDenseSelect:
      assert(task.levels == ctx.small_log.num_buckets &&
             task.end <= ctx.fresher.num_buckets);
      SelectDenseHomesRange(ctx.small_log, ctx.dense_homes,
                            Log2Exact(ctx.fresher.num_buckets), ctx.fresher,
                            task.begin, task.end);
      return true;
    case Subtask::kDenseDrain:
      assert(ctx.dense_tier != nullptr &&
             task.end <= ctx.small_log.num_buckets);
      return DrainDenseRemainderRange<CheckOverflow>(
          ctx.small_log, *ctx.dense_tier, task.begin, task.end);
    case Subtask::kRouteLevelRange: {
      const size_t half = size_t{1} << task.bit;
      // The first separated continuation pairs the public blank carry
      // region with one A bucket. At most 64 records enter either output,
      // so it cannot shed. Earlier preparation writers may have populated
      // this stage's stash: leave it entirely untouched. The planner says
      // which task this is; nothing clears the blank region, so its masks
      // are stale and the blank-first kernel does not read them.
      assert(!task.blank_first || half == ctx.upper_offset);
      for (size_t i = task.begin; i < task.end; ++i) {
        uint8_t* first = ctx.out.data + i * bucket_bytes;
        uint8_t* second = ctx.out.data + (i + half) * bucket_bytes;
        const bool ok = task.blank_first
            ? MergeSplitPair<CheckOverflow, /*BlankFirst=*/true>(
                  first, second, &ctx.out.masks[i], &ctx.out.masks[i + half],
                  layout.RoutedLines(task.bit), layout.TagLine(task.bit), task.bit)
            : MergeSplitPairStash<CheckOverflow>(
                  first, second, &ctx.out.masks[i], &ctx.out.masks[i + half],
                  layout.RoutedLines(task.bit), layout.TagLine(task.bit),
                  task.bit, ctx.level_stashes[task.bit]);
        if (!ok) return false;
      }
      return true;
    }
    case Subtask::kCopyFresher: {
      const size_t n = task.end - task.begin;
      uint8_t* dst = ctx.out.data + task.begin * bucket_bytes;
      const uint8_t* src = ctx.fresher.data + task.begin * bucket_bytes;
      assert(task.levels <= 8 * layout.tag_bytes);
      const size_t copy_lines = layout.EntryBytes() - task.levels / 8;
      // A later radix pass must still have its packed or reserved digit.
      assert(task.levels == 0 || ctx.map.kind != TagMapKind::kRadixDigit ||
             copy_lines > layout.DigitLine());
      const bool stream = StreamStoresForTable(ctx.out);
      if (ctx.drop_unshadowed || (stream && copy_lines < layout.EntryBytes())) {
        // Prune only paths that already need per-bucket work, or use streaming
        // stores. Small, ordinary cached copies retain the contiguous memcpy:
        // splitting that into bucket-sized copies costs more than pruning saves.
        // The tombstone filter reads the source's still-hot metadata and edits
        // only the destination mask, as before.
        const size_t meta_offset = layout.MetaLine();
        for (size_t b = task.begin; b < task.end; ++b) {
          uint8_t* const to = ctx.out.data + b * bucket_bytes;
          const uint8_t* const from = ctx.fresher.data + b * bucket_bytes;
          if (stream) {
            for (size_t i = 0; i < copy_lines; ++i) {
              _mm512_stream_si512(
                  reinterpret_cast<__m512i*>(to + 64 * i),
                  _mm512_load_si512(
                      reinterpret_cast<const void*>(from + 64 * i)));
            }
          } else {
            std::memcpy(to, from, copy_lines * kBucketCapacity);
          }
          if (ctx.drop_unshadowed) {
            ctx.out.masks[b] = ctx.fresher.masks[b];
            DropUnshadowedFromMask(from, &ctx.out.masks[b], meta_offset);
          }
        }
        if (stream) _mm_sfence();
        if (!ctx.drop_unshadowed) {
          std::memcpy(ctx.out.masks + task.begin, ctx.fresher.masks + task.begin,
                      n * sizeof(uint64_t));
        }
        return true;
      }
      if (stream) {
        // Write-once into a table nothing reads back until its butterfly,
        // which is a whole copy pass later: streaming stores skip the
        // read-for-ownership a cached store pays for every destination line
        // and keep the lines out of the L3 the request thread's cascade is
        // probing, which would otherwise slow the concurrent requests.
        const size_t lines = n * bucket_bytes / 64;
        for (size_t i = 0; i < lines; ++i) {
          _mm512_stream_si512(
              reinterpret_cast<__m512i*>(dst + 64 * i),
              _mm512_load_si512(reinterpret_cast<const void*>(src + 64 * i)));
        }
        _mm_sfence();
      } else {
        std::memcpy(dst, src, n * bucket_bytes);
      }
      std::memcpy(ctx.out.masks + task.begin, ctx.fresher.masks + task.begin,
                  n * sizeof(uint64_t));
      return true;
    }
    case Subtask::kRetagRange:
      ComputeRoutingTagsRange(ctx.out, ctx.nonce_lo, ctx.nonce_hi, task.begin,
                              task.end, ctx.map, ctx.route_levels,
                              *ctx.aes_keys);
      return true;
    case Subtask::kCopyAndRetagFresher:
      // The carry lands at destination offset zero, so `upper_offset` -- which
      // is where `older` lands -- has nothing to do with this range.
      CopyAndRetagRange(ctx.out, ctx.fresher, task.begin, task.end,
                        /*dst_offset=*/0, ctx.nonce_lo, ctx.nonce_hi, ctx.map,
                        ctx.route_levels, *ctx.aes_keys,
                        /*cached_stores=*/false, ctx.drop_unshadowed);
      return true;
    case Subtask::kCopyAndRetagRange:
    case Subtask::kCopyAndRetagTile:
      assert(!ctx.older_tombstone_free ||
             RangeHasNoErasedEntries(ctx.older, task.begin - ctx.upper_offset,
                                     task.end - ctx.upper_offset,
                                     layout.MetaLine()));
      CopyAndRetagRange(ctx.out, ctx.older, task.begin, task.end,
                        ctx.upper_offset, ctx.nonce_lo, ctx.nonce_hi, ctx.map,
                        ctx.route_levels, *ctx.aes_keys,
                        /*cached_stores=*/task.kind == Subtask::kCopyAndRetagTile,
                        ctx.drop_unshadowed);
      return true;
    case Subtask::kButterflySubnetwork: {
      ButterflyStashContext bctx;
      bctx.data = ctx.out.data;
      bctx.masks = ctx.out.masks;
      bctx.layout = layout;
      bctx.bucket_bytes = bucket_bytes;
      bctx.level_stashes = ctx.level_stashes;
      return RouteSubnetworkRecursive<CheckOverflow>(bctx, task.begin,
                                                     task.log2_stride,
                                                     task.levels);
    }
    case Subtask::kCrossLevelRange:
      return CrossSourceLevelDedup<CheckOverflow>(
          ctx.out, task.bit, ctx.level_stashes[task.bit], task.begin, task.end);
    case Subtask::kCrossLevelOffers: {
      // The offer sets, in pass order.  Split shape: the carry's kTableWins
      // offer first, then the tier's kResidualWins one, so a carry copy
      // absorbed first still loses to the fresher tier copy that meets it.
      // Merged shape: one kClassMark set carries both classes, ordered by
      // nothing (the pool dedup resolved carry x tier before the scatter).
      // `task.levels` is the offer WEIGHT -- touches per output bucket, a
      // class-marked set counting two, a set counting once per GROUP (only a
      // DIRECT plan at the smallest steps has more than one) -- which is what
      // the planner sliced by (CrossOfferWeight).
      ResidualOfferSet offers[2 * kResidualPasses];
      unsigned weight = 0;
      const size_t num_offers = GatherFusedOffers(
          ctx, ResidualFuseSite::kCrossLevel, offers, &weight);
      assert(weight == task.levels);
      (void)weight;
      return CrossSourceLevelDedupOffers<CheckOverflow>(
          ctx.out, task.bit, ctx.level_stashes[task.bit], offers, num_offers,
          task.begin, task.end);
    }
    case Subtask::kFixedMergeOffers: {
      // The fixed merge with its passes' offers fused in; `bit` is r as for
      // kFixedMergeRange, and at r = 1 the kernel is the binary merge.
      ResidualOfferSet offers[2 * kResidualPasses];
      unsigned weight = 0;
      const size_t num_offers = GatherFusedOffers(
          ctx, ResidualFuseSite::kFixedMerge, offers, &weight);
      assert(weight == task.levels);
      (void)weight;
      const FixedMergeRetag retag = FixedMergeRetagOf(ctx);
      return MergeFixedLevelSourcesOffersRange<CheckOverflow>(
          ctx.out, ctx.fresher, task.bit < 1 ? 1u : task.bit, *ctx.merge_stash,
          offers, num_offers, task.begin, task.end, FixedMergeTombstonesOf(ctx),
          &retag);
    }
    case Subtask::kRadixPassOffers:
    case Subtask::kRadixRouteOffers: {
      // The radix pass with the offers fused in.  The block is the output's
      // size over r: the output IS r blocks, so this is exact.
      ResidualOfferSet offers[2 * kResidualPasses];
      unsigned weight = 0;
      const size_t num_offers = GatherFusedOffers(
          ctx, ResidualFuseSite::kRadixPass, offers, &weight);
      assert(weight == task.levels);
      (void)weight;
      const unsigned r = task.bit;
      assert(r >= 2 && ctx.out.num_buckets % r == 0);
      const unsigned block_bits = Log2Exact(ctx.out.num_buckets / r);
      if (task.kind == Subtask::kRadixPassOffers) {
        return RadixPassOffersRange</*Dedup=*/true, CheckOverflow>(
            ctx.out, block_bits, r, *ctx.radix_stash, offers, num_offers,
            task.begin, task.end);
      }
      return RadixPassOffersRange</*Dedup=*/false, CheckOverflow>(
          ctx.out, block_bits, r, *ctx.radix_stash, offers, num_offers,
          task.begin, task.end);
    }
    case Subtask::kResidualLeftoverDedup: {
      // Between the two halves of the drain: the range leftovers are in the
      // drain, the drain-only slots still in their stashes.
      const ResidualPass& rp = ctx.residual[task.pass];
      assert(rp.active && rp.sweep_active && rp.drain != nullptr);
      ResidualLeftoverDedupRange(rp.rule, rp.main.layout, *rp.drain, rp.pool,
                                 rp.drain_only, task.begin, task.end);
      return true;
    }
    case Subtask::kButterflyLevelOffers: {
      // The last level of the pass's own butterfly, with its offer fused in.
      // The pairs are within the pass's MAIN view (the chunk half), and the
      // level sheds into the same per-bit stash the butterfly recursion would
      // have used -- which is the pass's drain-only slot, drained after this.
      const ResidualPass& rp = ctx.residual[task.pass];
      assert(rp.active && rp.fuse == ResidualFuseSite::kOwnLastLevel &&
             rp.sweep_active);
      ResidualOfferSet offer;
      offer.range = rp.range;
      offer.plan = rp.plan;
      offer.rule = rp.rule;
      offer.lines = rp.lines;
      assert(rp.plan.groups *
                 (rp.rule == ResidualDedupRule::kClassMark ? 2u : 1u) ==
             task.levels);
      return ButterflyLevelOffersRange<CheckOverflow>(
          rp.main, task.bit, ctx.level_stashes[task.bit], offer, task.begin,
          task.end);
    }
    case Subtask::kFixedMergeRange:
      // The fixed level's sweep is the mixed-radix twin, and at r = 1 the
      // two kernels are the same computation -- but the binary one is what
      // B = 2 has always run, so it keeps running it rather than relying on
      // that.  (r = 1 also reads no digit, so `retag_fresher_digits` has
      // nothing to do there and the binary kernel never sees it.)
      if (task.bit > 1) {
        const FixedMergeRetag retag = FixedMergeRetagOf(ctx);
        return MergeRadixLevelSourcesRange<CheckOverflow>(
            ctx.out, ctx.fresher, task.bit, *ctx.merge_stash, task.begin,
            task.end, FixedMergeTombstonesOf(ctx), &retag);
      }
      return MergeFixedLevelSourcesRange<CheckOverflow>(
          ctx.out, ctx.fresher, *ctx.merge_stash, task.begin, task.end,
          FixedMergeTombstonesOf(ctx));
    case Subtask::kRadixPassRange:
      return RadixPassDedupStashRange<CheckOverflow>(
          ctx.out, task.levels, task.bit, *ctx.radix_stash, task.begin,
          task.end);
    case Subtask::kRadixRouteRange:
      return task.blank_first
                 ? RadixPassStashRange<CheckOverflow, /*BlankFirst=*/true>(
                       ctx.out, task.levels, task.bit, *ctx.radix_stash,
                       task.begin, task.end)
                 : RadixPassStashRange<CheckOverflow>(
                       ctx.out, task.levels, task.bit, *ctx.radix_stash,
                       task.begin, task.end);
    case Subtask::kResidualPoolDedup: {
      const ResidualPass& rp = ctx.residual[task.pass];
      // `bit` carries the emission's window; the planner sized
      // [begin, end) over that rectangle, not over the full pool square.
      ResidualPoolDedupRange(rp.pool, rp.rank, rp.pool_slots, rp.drain_only,
                             static_cast<ResidualDedupWindow>(task.bit),
                             layout.key_bytes, task.begin, task.end);
      return true;
    }
    case Subtask::kResidualScatter:
    case Subtask::kResidualScatterRetag: {
      const ResidualPass& rp = ctx.residual[task.pass];
      // Checked once per pass, on the first slice, and only in a build with
      // assertions live.  It goes here rather than with the pool dedup because
      // that phase is planned ONLY when the pass mixes freshness classes --
      // and a pass whose slots all rank equal is precisely the one whose
      // equal-rank disjointness has never been checked by anything.
      assert(task.begin != 0 ||
             ResidualPoolEqualRanksDisjoint(rp.pool, rp.rank, rp.pool_slots,
                                            layout.key_bytes));
      // kResidualScatterRetag is only a separated pass's direct B tail.
      if (task.kind == Subtask::kResidualScatterRetag) {
        ScatterAndRetagResidualPoolRange(
            rp.pool + rp.pool_slots - rp.direct_slots, rp.direct_slots,
            DirectResidualRange(rp), DirectResidualPlan(rp), task.begin,
            task.end, ctx.nonce_lo, ctx.nonce_hi, rp.map, *ctx.aes_keys,
            /*class_mark=*/true, /*tier_from_group=*/0, ctx.drop_unshadowed);
        return true;
      }
      ScatterResidualPoolRange(rp.pool + rp.drain_only,
                               DistributedPoolSlots(rp),
                               DistributedResidualRange(rp),
                               rp.plan, task.begin, task.end,
                               ctx.drop_unshadowed);
      return true;
    }
    case Subtask::kResidualRetag: {
      const ResidualPass& rp = ctx.residual[task.pass];
      // route_levels = 0: the sweep reads the low index_bits of the tag back
      // out, so the range table keeps the whole thing.  `rp.map` is the flat
      // destination index (9), kRaw whenever the main table is a power of two.
      ComputeRoutingTagsRange(DistributedResidualRange(rp), ctx.nonce_lo,
                              ctx.nonce_hi, task.begin,
                              task.end, rp.map, 0, *ctx.aes_keys);
      // The merged pass's class mark goes down here, alongside the retag that
      // already has the range table resident.
      if (rp.rule == ResidualDedupRule::kClassMark) {
        WriteResidualClassBitsRange(DistributedResidualRange(rp), rp.plan,
                                    rp.tier_class_from,
                                    task.begin, task.end);
      }
      return true;
    }
    case Subtask::kResidualDfsGather: {
      const ResidualPass& rp = ctx.residual[task.pass];
      if (rp.dfs == nullptr) {
        throw std::logic_error("DFS residual task has no workspace");
      }
      // As at the scatter: once per pass, with assertions live.
      assert(task.begin != 0 ||
             ResidualPoolEqualRanksDisjoint(rp.pool, rp.rank, rp.pool_slots,
                                            layout.key_bytes));
      const TableView gather = rp.dfs->Gather();
      ResidualRangePlan one;  // one source bucket per gathered bucket
      one.scatter_per_bucket = kBucketCapacity;
      one.groups = gather.num_buckets;
      one.range_buckets = gather.num_buckets;
      one.index_bits = rp.plan.range_bits + rp.plan.index_bits;
      ScatterAndRetagResidualPoolRange(
          rp.pool + rp.drain_only, DistributedPoolSlots(rp), gather, one,
          task.begin, task.end, ctx.nonce_lo, ctx.nonce_hi, rp.map,
          *ctx.aes_keys, rp.rule == ResidualDedupRule::kClassMark,
          rp.tier_class_from, ctx.drop_unshadowed);
      return true;
    }
    case Subtask::kResidualDfsPartition: {
      const ResidualPass& rp = ctx.residual[task.pass];
      if (rp.dfs == nullptr) {
        throw std::logic_error("DFS residual task has no workspace");
      }
      // Always checked.
      return rp.dfs->Run(DistributedResidualRange(rp), task.begin, task.end);
    }
    case Subtask::kResidualSweep: {
      const ResidualPass& rp = ctx.residual[task.pass];
      ResidualSecondChanceSweepRangeDynamic(rp.rule, rp.main, rp.range,
                                            rp.plan, rp.lines, task.begin,
                                            task.end);
      return true;
    }
    case Subtask::kResidualDrain: {
      const ResidualPass& rp = ctx.residual[task.pass];
      // Payload only: the carry and the second tier are both re-tagged from
      // the key by whatever consumes them next.  Units [0, range.num_buckets)
      // are the range table's leftovers; the ones past it are the drain-only
      // slots' stash buckets, in slot order.
      const size_t lines = rp.main.layout.PayloadLines();
      const size_t range_units = rp.sweep_active ? rp.range.num_buckets : 0;
      size_t begin = task.begin;
      if (begin < range_units) {
        const size_t stop = task.end < range_units ? task.end : range_units;
        if (!DrainResidualTableRange(rp.range, *rp.drain, lines, begin,
                                     stop)) {
          return false;
        }
        begin = stop;
      }
      if (begin < task.end) {
        if (!DrainResidualPoolRange(rp.pool, rp.drain_only, *rp.drain, lines,
                                    begin - range_units,
                                    task.end - range_units)) {
          return false;
        }
      }
      return true;
    }
    case Subtask::kResidualReset: {
      const ResidualPass& rp = ctx.residual[task.pass];
      for (size_t s = task.begin; s < task.end; ++s) rp.pool[s]->Reset();
      return true;
    }
    case Subtask::kDropErasedTier: {
      // The tier holds entries in the main layout, so its meta line is where
      // the output table's is.  One byte line read and one occupancy word
      // written per bucket, exactly as over the main table: nothing about the
      // work depends on how many tombstones there were.
      // At the top after ResolveTopDestination it finds nothing: the drop
      // is kept as public work, and no slot it could free is counted.
      ResidualStash& tier = *ctx.tier_out;
      const size_t meta_offset = layout.MetaLine();
      for (size_t b = task.begin; b < task.end; ++b) {
        assert(!TopResolutionRuns(ctx) ||
               (tier.masks[b] & ErasedSlotMask(tier.Bucket(b), meta_offset)) ==
                   0);
        DropErasedEntries(tier.Bucket(b), &tier.masks[b], meta_offset);
      }
      return true;
    }
    case Subtask::kDropErased:
      assert(!TopResolutionRuns(ctx) ||
             RangeHasNoErasedEntries(ctx.out, task.begin, task.end,
                                     layout.MetaLine()));
      DropErasedEntriesRange(ctx.out, task.begin, task.end);
      return true;
  }
  return false;
}

}  // namespace byteslice
}  // namespace microram
