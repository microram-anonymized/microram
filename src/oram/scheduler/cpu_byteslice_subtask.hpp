#pragma once

// The unit of rebuild work: one slice of one phase of a rebuild step.
//
// Every live caller plans a phase whole (WholeLevelMergeBudget), one subtask
// per range, and a PhaseCursor then runs the plan in pieces at the executing
// group's budget: a thread can only stop between
// pieces, so the longest piece bounds how long an urgent level waits behind a
// big one.
//
// A SLICE IS NOT A DIFFERENT ALGORITHM.  Every cut is at a point the kernels
// already stop at.  Copies and re-tags are over independent bucket ranges; the
// cross-source level and the fixed merge are over independent bucket PAIRS, and
// already take a [begin, end).  The butterfly is the one phase that is not a
// flat loop, and it is cut by walking the SAME cache-oblivious recursion the
// kernel walks and stopping early -- so the emitted sub-networks, executed in
// order, issue exactly the MergeSplit sequence the monolithic call would.  The
// tests assert byte- and mask-identical output at every granularity down to a
// one-bucket budget.
//
// Everything a subtask needs beyond its own range lives in the
// RebuildStepContext it is issued against, so a plan is a plain vector of these
// and a scheduler can hold, sort and re-issue them without dragging table
// pointers around.
//
// A PLAN IS MATERIALIZED ONCE PER PHASE on the live path, into a task list
// the level's job reserves at construction (LevelPhasePlanCapacity), and run
// by a cursor (cpu_byteslice_subtask_cursor.hpp) that can stop after any
// piece and resume later, on the same thread or, lane by lane, on another.
// The planners are templates over the sink so that a counter
// (SubtaskTouchCounter) and the tests' vectors can take the same stream.
//
// Deliberately NOT here: deadlines, urgency, and the thread.  A plan built here
// is ordered by nothing but data dependencies.  Deadlines belong to a work
// ITEM rather than to a subtask, so a Subtask carries none.  Publication is
// not a subtask either -- it moves the registry and the probe plan, which
// belong to the engine and not to the kernels -- so a step's plan ends where
// its publication begins.

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "src/oram/rebuild/cpu_byteslice_dedup_rebuild.hpp"

namespace microram {
namespace byteslice {

// ---------------------------------------------------------------------------
// The unit of worker work
// ---------------------------------------------------------------------------

// One slice of a rebuild step.  Everything a subtask needs beyond its own
// range lives in the RebuildStepContext it is issued against, so a plan is a
// plain vector of these and a scheduler can hold, sort and re-issue them
// without dragging table pointers around.
struct Subtask {
  enum Kind : uint8_t {
    // out[begin, end) <- fresher[begin, end). `levels` is the public number
    // of already-routed low bits; zero requests the full-copy fallback.
    // Whole retired tag lines may be omitted by the per-bucket copy paths.
    kCopyFresher,
    // ComputeRoutingTagsRange over out[begin, end), under the rebuild's nonce.
    // Only where the records are already in place (a direct initialization,
    // RebuildStepContext::source_in_place): everywhere else a re-tag follows a
    // copy of the range it re-tags, and the two are one pass (below).
    kRetagRange,
    // out[begin, end) <- older[begin - upper_offset, ...), re-tagged under the
    // rebuild's nonce in the SAME pass over the data (CopyAndRetagRange).
    // The upper half of [T_j | L_j], the old level of an in-place absorb, or
    // the whole of the fixed last level's workspace copy.
    //
    // Charged TWO touches per bucket -- it is both phases -- so a touch count
    // is the one the two unfused phases had, and all that fusing moved is what
    // a touch COSTS.
    kCopyAndRetagRange,
    // The same range, with cached stores: a first-phase butterfly tile
    // consumes this copy before the next tile group's copy is issued.
    kCopyAndRetagTile,
    // out[begin, end) <- fresher[begin, end), re-tagged under this rebuild's
    // nonce in the SAME pass -- CopyAndRetagRange with the FRESHER table as
    // its source and destination offset zero.
    //
    // Why a fresher copy ever needs a re-tag: the chain's kCopyFresher moves a
    // prefix the same rebuild just wrote, so its tags are already this
    // rebuild's.  A carry that was PUBLISHED and later consumed by a different
    // merge is not in that position -- a payload-only residual sweep may have
    // left its stored tag bytes pruned or stale, and the consumer's map and
    // nonce are its own -- so the bytes have to be recomputed.  It stays one
    // pass over the data and installs no routing -- but only because the
    // consumer re-tags under the CARRY'S OWN nonce, which the level arena's
    // canonical family makes the consumer's nonce too.  Same nonce, same raw
    // hash, so a power-of-two carry's bucket index -- the low log2(U) bits of
    // it -- is unchanged and re-tagging cannot move an entry out of the bucket
    // it is already in.  Only the MAP changes, adding the radix digit and the
    // higher bits the merge will route on.  Under a different nonce the hash
    // is a different number and every entry would be left in the bucket the
    // old one chose; the kernel cannot tell, so this is the caller's
    // invariant.
    kCopyAndRetagFresher,
    // RouteSubnetworkRecursive(base = begin, log2_stride, levels): one node of
    // the cache-oblivious butterfly recursion.  It touches the strided set
    // {begin + j << log2_stride : j in [0, 2^levels)}; `end` is one past its
    // last bucket, so [begin, end) is the span two nodes must not share if a
    // scheduler ever wants to check overlap cheaply.
    kButterflySubnetwork,
    // CrossSourceLevelDedup(out, bit, [begin, end)): the pairs (i, i + 2^bit)
    // for i in [begin, end).  The one phase that deduplicates.
    kCrossLevelRange,
    // Separated A-only continuation of the same pairs, without dedup.
    // With `blank_first`, the first operand is publicly empty: the route
    // reads neither its masks nor its lines and does not touch its stage
    // stash.
    kRouteLevelRange,
    // The same pairs with the step's FUSED residual offers run against both
    // output buckets right after each merge (CrossSourceLevelDedupOffers):
    // the carry's kTableWins offer and the tier's kResidualWins offer ride
    // the pass that already read-modify-writes every bucket, so the two
    // standalone sweeps they replace cost only their tag match, intersect and
    // register-resident permute.  `levels` carries the number of active offer
    // sets, which is what prices a pair.
    kCrossLevelOffers,
    // ButterflyLevelOffersRange(residual[pass].main, bit, [begin, end)): the
    // LAST level of pass 0's own butterfly with that pass's offer fused in --
    // the plain MergeSplit pairs (i, i + 2^bit), then the offer against both
    // output buckets while they are cache-resident, replacing the pass's
    // standalone sweep the way kCrossLevelOffers replaces the chain step's.
    // `bit` is the level; `levels` carries the offer WEIGHT (touches per
    // output bucket -- the plan's group count, since a kNoDedup offer set is
    // one touch per group); `pass` names the residual pass whose main table,
    // range table and level stash it runs against.
    kButterflyLevelOffers,
    // MergeFixedLevelSourcesRange(out = C, fresher = B, [begin, end)): the
    // fixed last level's direct dedup-and-merge sweep.
    kFixedMergeRange,
    // The same merge with the fixed level's FUSED residual offers run against
    // each C bucket right after B's entries have merged into it
    // (MergeFixedLevelSourcesOffersRange): the preparation's carry and B's
    // tier ride the pass that already read-modify-writes every bucket of C,
    // replacing the two standalone sweeps over the whole level.  `bit` is the
    // radix r as for kFixedMergeRange; `levels` carries the offer WEIGHT
    // (touches per output bucket), which prices a unit at 2r + r * weight.
    kFixedMergeOffers,
    // RadixPassDedupStashRange(out, block_bits = `levels`, r = `bit`,
    // [begin, end)): the last routing step of a mixed-radix absorb.
    // One radix-r MergeSplit per
    // stride-2^levels tuple, preceded by the r-1 ordered dedup clears against
    // block 0.  Ranged over TUPLE index, so disjoint ranges touch disjoint
    // buckets of all r blocks.
    kRadixPassRange,
    // RadixPassStashRange: the same pass with no dedup prologue, which is what
    // the fixed level's C <- A workspace copy needs -- A is ONE source and
    // holds each key at most once, so the r-1 clears per tuple would provably
    // find nothing.  With `blank_first`, block 0 is publicly empty (a
    // separated preparation at an odd digit) and its masks are not read.
    kRadixRouteRange,
    // The two radix passes with the item's FUSED residual offers run against
    // each of a tuple's r output buckets right after it has merged
    // (RadixPassOffersRange<Dedup>): the absorb's (kRadixPassOffers, with the
    // prologue) and the fixed preparation's (kRadixRouteOffers, without),
    // replacing the standalone sweeps over the whole level that followed
    // them.  `bit` is r and the block is read off the output's size; `levels`
    // carries the offer WEIGHT (touches per output bucket), so a tuple is
    // RadixTupleTouches(r) + r * weight touches.
    kRadixPassOffers,
    kRadixRouteOffers,

    // ---- the residual second chance (load 0.5 only) ----------------------
    //
    // Six phases over one residual pass, all against ctx.residual[pass].
    // They are ordered and must run in this order; only the ranges inside a
    // phase are independent.

    // ResidualPoolDedupRange over the ELIGIBLE ordered pool-BUCKET pairs
    // [begin, end): resolve pool-internal duplicates by the slots' PUBLIC
    // freshness rank, before the routing scrambles which slot an entry came
    // from.  One unit is exactly one CrossBucketDuplicateMask over a (fresher,
    // staler) bucket pair -- the public rank order decides which pairs are
    // units at all, and the kernel never MergeSplits -- so it is charged one
    // touch at the intersect's rate.  An eligible slot pair is `a.num_buckets
    // * b.num_buckets` units; pricing all of that as ONE unit would let this
    // phase escape its slice width.  `bit` is the emission's
    // ResidualDedupWindow: the pair space is the eligible pairs inside that
    // window's slot rectangle, so a pass with two emissions plans each over
    // what it can act on rather than over the full pool twice.
    kResidualPoolDedup,
    // Scatter the pool's stash buckets into the range table, 64 -> fanout x
    // scatter_per_bucket, clearing the padding.  Ranged over scatter GROUPS
    // (one pool bucket each), which is the unit ScatterDenseBucket writes.
    kResidualScatter,
    // A separated pass's direct B tail (levels=1, fanout one): payload/tag
    // copy, retag and class stamping; charged scatter + retag touches.
    kResidualScatterRetag,
    // ComputeRoutingTagsRange over the range table, under the rebuild's nonce
    // and over the WHOLE tag: the sweep reads the low index_bits back.
    kResidualRetag,
    // THE DFS DISTRIBUTOR (ResidualPass::dfs, cpu_byteslice_dfs_residual.hpp),
    // which builds the range table in place of the scatter and retag.
    // Its gather: the swept pool into the workspace, one source bucket per
    // gathered bucket, re-tagged under the flat destination map and
    // class-marked -- kResidualScatterRetag's kernel at fanout one.  Ranged
    // over pool buckets.
    kResidualDfsGather,
    // Its partition: units [begin, end) of the pass's public unit list, each
    // one child compaction, strictly in order, into the stacked leaf table
    // (the pass's range view).  `levels` carries the pass's whole touch
    // estimate and `bit` its unit count; a piece is charged its units' share
    // (DfsPartitionPieceTouches).  A child over its capacity is a declared
    // failure.
    kResidualDfsPartition,
    // The oblivious lockstep sweep: main bucket b takes the residuals of range
    // bucket b >> index_bits that name it, as many as fit.
    kResidualSweep,
    // A FUSED final pass's leftover dedup (ResidualLeftoverDedupRange): the
    // range leftovers, already drained into the pass's drain, against the
    // drain-only stash buckets still waiting to drain -- one (drain bucket,
    // stash bucket) pair per unit, drain-bucket major, between the two halves
    // of kResidualDrain.  Planned only where ResidualLeftoverDedupNeeded says
    // a drain-only slot outranks a swept one -- the absorb's radix shed
    // against its carry class, the fixed merge's shed against the
    // preparation's carry -- and priced at the intersect's rate times the
    // weight in `levels` (a class-marked pass runs two masked intersects per
    // pair).
    kResidualLeftoverDedup,
    // Whatever did not fit, into the pass's drain stash -- the carry after a
    // per-block pass, the published second tier after the final one.
    kResidualDrain,
    // Empties the pass's own stashes, now that the scatter has copied them out
    // and the sweep has put them back.  Only the leading `reset_slots` sources
    // are the job's: the trailing ones are the SECOND TIER of a table this
    // rebuild is consuming, which stays live in the probe plan until the
    // publication that retires it.
    kResidualReset,

    // ---- the dense prefix (level 1's carry builder) -----------------------

    // The DENSE PREFIX's chronological duplicate sweep (a dense prefix is the
    // log of r0 recent online-stash units from which level one builds its
    // carry, src/oram/levelarena/DESIGN.md).
    // The log holds `bit`
    // units of `levels` buckets each in chronological order; this walks every
    // ORDERED pair of units (old < fresh) and, within it, all levels^2 bucket
    // pairs, clearing matched keys from the OLDER unit's log mask only.
    //
    // It is not a rectangle: a prefix is r0 units, and each unit is only
    // internally unique.  The unit pairs are
    // enumerated in increasing FRESH order, and that order is load bearing --
    // a pair (old, fresh) reads `fresh`'s mask, which must not yet have been
    // cleared by a pair in which `fresh` was itself the older member.  So its
    // slices must run in index order, on one thread.
    kPrefixLogDedup,
    // ---- level one's direct B build (cpu_byteslice_dense_select.hpp) -----
    // The B home of every lane of prefix buckets [begin, end), cached.
    kDenseHomes,
    // B homes [begin, end), each scanning all `levels` prefix buckets.
    kDenseSelect,
    // The rejected winners of prefix buckets [begin, end), into B's tier.
    kDenseDrain,

    // ---- erasure --------------------------------------------------------

    // The tombstone drop over the item's OUTPUT TIER
    // (RebuildStepContext::tier_out), ranged over its buckets.  Planned
    // wherever kDropErased is, right after it, and for the same reason: the
    // tier is published in the same window as its main table, and a tombstone
    // the final pass drained into it would otherwise survive the one rebuild
    // allowed to forget it and rejoin every later rebuild as occupancy.
    // Never a
    // borrowed tier: those stay immutable until the publication that retires
    // them.  Listed before kDropErased so that stays the last kind, which the
    // per-kind diagnostics are sized by.
    kDropErasedTier,
    // DropErasedEntriesRange over out[begin, end): every tombstone becomes a
    // dummy.  The FIXED merge's last phase -- and the one growth carry into
    // the last level while it is still empty -- and nothing else: those
    // rebuilds consume every table and retire every live nonce family, which
    // is the only state in which forgetting a tombstone does not turn its key
    // into a repeat-probed absent key.  It runs AFTER the residual passes,
    // because before them a shed older copy of an erased key would be offered
    // back to a table with no tombstone left to lose to.
    kDropErased,
  };

  Kind kind = kCopyFresher;
  size_t begin = 0;
  size_t end = 0;
  // kButterflySubnetwork's stride.
  unsigned log2_stride = 0;
  unsigned levels = 0;  // kButterflySubnetwork, kRadixPassRange
  unsigned bit = 0;     // kCrossLevelRange; the radix r of kRadixPassRange
  // Which residual pass of the step this belongs to.  A step runs one per
  // freshness class: the block's own residuals back into the block under
  // kNoDedup, then the cross-source ones into the whole output under
  // kResidualWins.
  uint8_t pass = 0;
  // kRouteLevelRange, kRadixRouteRange: the first operand is publicly blank,
  // which only the planner knows (from public geometry).  The kernels then
  // treat its masks as zero without reading them, so nothing has to clear
  // them first.
  bool blank_first = false;
};

// For diagnostics that would otherwise report a kind as a bare number, and an
// integer is not an answer to "which phase was it".  Not a switch over a
// `Kind` variable with no default, deliberately: this must never be the thing
// that stops a new kind from compiling.
inline const char* SubtaskKindName(Subtask::Kind kind) {
  switch (kind) {
    case Subtask::kCopyFresher: return "copy-fresher";
    case Subtask::kRetagRange: return "retag";
    case Subtask::kCopyAndRetagRange: return "copy-retag";
    case Subtask::kCopyAndRetagTile: return "copy-retag-tile";
    case Subtask::kCopyAndRetagFresher: return "copy-retag-fresher";
    case Subtask::kButterflySubnetwork: return "butterfly";
    case Subtask::kRouteLevelRange: return "route-level";
    case Subtask::kCrossLevelRange: return "cross-level";
    case Subtask::kCrossLevelOffers: return "cross-level-offers";
    case Subtask::kButterflyLevelOffers: return "butterfly-offers";
    case Subtask::kFixedMergeRange: return "fixed-merge";
    case Subtask::kFixedMergeOffers: return "fixed-merge-offers";
    case Subtask::kRadixPassRange: return "radix-dedup";
    case Subtask::kRadixRouteRange: return "radix-route";
    case Subtask::kRadixPassOffers: return "radix-dedup-offers";
    case Subtask::kRadixRouteOffers: return "radix-route-offers";
    case Subtask::kResidualLeftoverDedup: return "residual-leftover-dedup";
    case Subtask::kResidualReset: return "residual-reset";
    case Subtask::kResidualScatter: return "residual-scatter";
    case Subtask::kResidualScatterRetag: return "residual-build";
    case Subtask::kResidualRetag: return "residual-retag";
    case Subtask::kResidualDfsGather: return "residual-dfs-gather";
    case Subtask::kResidualDfsPartition: return "residual-dfs-partition";
    case Subtask::kResidualPoolDedup: return "residual-pool-dedup";
    case Subtask::kResidualSweep: return "residual-sweep";
    case Subtask::kResidualDrain: return "residual-drain";
    case Subtask::kDropErasedTier: return "drop-erased-tier";
    case Subtask::kDropErased: return "drop-erased";
    case Subtask::kPrefixLogDedup: return "prefix-log-dedup";
    case Subtask::kDenseHomes: return "dense-homes";
    case Subtask::kDenseSelect: return "dense-select";
    case Subtask::kDenseDrain: return "dense-drain";
  }
  return "?";
}

// The one spelling of a butterfly leaf's Subtask (PlanSubnetwork's).  The
// `end` arithmetic is the span rule two nodes must not share, so it must not
// be written twice.
inline Subtask MakeButterflyLeafSubtask(size_t base, unsigned log2_stride,
                                        unsigned levels) {
  Subtask task;
  task.kind = Subtask::kButterflySubnetwork;
  task.begin = base;
  task.end = base + (((size_t{1} << levels) - 1) << log2_stride) + 1;
  task.log2_stride = log2_stride;
  task.levels = levels;
  return task;
}

}  // namespace byteslice
}  // namespace microram
