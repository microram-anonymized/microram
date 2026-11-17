#pragma once

// The load-0.5 butterfly: the LSB-first routing network, driven two levels at
// a time through the quad kernel, in two orders.
//
// GROUPED order tiles for one cache level with a fixed group size: for a group
// starting at level l0, the 2^group_levels buckets that interact are swept
// through every level of the group while they are hot, so DRAM sees
// ceil(L / group) passes over the array instead of L.  One knob, one cache
// level.
//
// CACHE-OBLIVIOUS order instead cuts the network recursively: route the low
// half of the levels over each half-sized sub-network, then the high half.
// The recursion is correct because a MergeSplit on bit b only needs both
// operands routed on bits below b, which the sub-network guarantees -- the
// MergeSplit SET and each MergeSplit's input state are identical to the
// grouped order, only the (public, size-derived) execution order differs.  It
// needs no tuning and it is also the finest cut the phase planners can slice a
// butterfly at, which is why the leaf size is a named constant rather than a
// local.
//
// Tag pruning applies throughout: level b retires tag byte b/8, so a MergeSplit
// on bit b routes only Layout::RoutedLines(b) byte lines.  Everything that runs
// after the last routing bit -- the fold, the 0.25 -> 0.5 contraction, the
// radix pass, the stash merges, the dense scatters -- routes
// Layout::PayloadLines() and moves no tag at all.

#include <immintrin.h>

#include <cassert>
#include <cstddef>
#include <cstdint>

#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/rebuild/cpu_byteslice_mergesplit_stash.hpp"
#include "src/oram/rebuild/cpu_byteslice_residual_stash.hpp"

namespace microram {
namespace byteslice {

// Butterfly at load 0.5, grouped: runs MergeSplitPairStash and takes the
// number of levels to route explicitly: the fixed-level rebuild routes only log2(num_buckets) - 1
// levels over both arena halves (two independent butterflies) and resolves
// the top bit with the fold instead.  In checked mode, returns false on stash
// overflow.
// `level_stashes` is an array of route_levels stashes; the MergeSplit routing
// tag bit b sheds its residual into level_stashes[b] (a separate stash per
// butterfly level -- see the per-level sizing section).
//
// Levels are taken two at a time by MergeSplitQuadStash (four buckets held in
// registers across both), which halves the load/store traffic; an odd
// trailing level in a group runs as ordinary MergeSplits.
template <bool CheckOverflow = false>
inline bool ButterflyRouteStash(TableView t, unsigned route_levels,
                                ResidualStash* level_stashes,
                                unsigned group_levels = 6) {
  const size_t num_buckets = t.num_buckets;
  if (num_buckets <= 1 || route_levels == 0) return true;
  assert(group_levels >= 1);
  assert(route_levels <= Log2Exact(num_buckets));
  assert(t.layout.tag_bytes * 8 >= route_levels);
  const Layout& layout = t.layout;
  const size_t bucket_bytes = layout.BucketBytes();
  uint8_t* data = t.data;
  uint64_t* masks = t.masks;

  for (unsigned l0 = 0; l0 < route_levels; l0 += group_levels) {
    const unsigned group = std::min(group_levels, route_levels - l0);
    const size_t low_count = size_t{1} << l0;
    const size_t mid_count = size_t{1} << group;
    const size_t high_count = num_buckets >> (l0 + group);
    for (size_t high = 0; high < high_count; ++high) {
      for (size_t low = 0; low < low_count; ++low) {
        const size_t base = (high << (l0 + group)) | low;
        unsigned lev = 0;
        for (; lev + 1 < group; lev += 2) {
          const size_t half = size_t{1} << lev;
          const unsigned bit = l0 + lev;
          for (size_t mid = 0; mid < mid_count; ++mid) {
            if (mid & (half | (half << 1))) continue;
            const size_t i = base + (mid << l0);
            if (!MergeSplitQuadStash<CheckOverflow>(
                    data + i * bucket_bytes, &masks[i], bucket_bytes, layout,
                    bit, level_stashes[bit], level_stashes[bit + 1])) {
              return false;
            }
          }
        }
        for (; lev < group; ++lev) {
          const size_t half = size_t{1} << lev;
          const unsigned bit = l0 + lev;
          const size_t lines = layout.RoutedLines(bit);
          const size_t tag_line = layout.TagLine(bit);
          for (size_t mid = 0; mid < mid_count; ++mid) {
            if (mid & half) continue;
            const size_t i = base + (mid << l0);
            const size_t j = base + ((mid | half) << l0);
            if (!MergeSplitPairStash<CheckOverflow>(
                    data + i * bucket_bytes, data + j * bucket_bytes,
                    &masks[i], &masks[j], lines, tag_line, bit,
                    level_stashes[bit])) {
              return false;
            }
          }
        }
      }
    }
  }
  return true;
}

// ---------------------------------------------------------------------------
// Cache-oblivious recursive butterfly
// ---------------------------------------------------------------------------
//
// ButterflyRouteStash above tiles for one cache level with a fixed group
// size.  The recursive formulation is cache-agnostic: a sub-network
// {base + j * 2^s : j in [0, 2^k)} routing tag bits [s, s+k) is split into
// 2^(k-k/2) contiguous low-half sub-networks of 2^(k/2) buckets (bits
// [s, s+k/2)) followed by 2^(k/2) stride-multiplied high-half sub-networks
// (bits [s+k/2, s+k)).  Every size of sub-network occurs at some recursion
// depth, so whichever sizes fit L1/L2/L3 are each traversed while resident;
// the whole array is streamed from DRAM only O(log_M 2^k) times instead of
// k/group times, with no cache-size parameter.
//
// The MergeSplit set and each MergeSplit's input state (its dependency cone
// of earlier levels) are identical to the flat level-by-level order, so the
// routed output, the occupancy masks and the set of shed residuals are all
// unchanged; only the (public, size-derived) execution order differs, and
// stash occupancy only grows, so the capacity check is order-invariant.

struct ButterflyStashContext {
  uint8_t* data = nullptr;
  uint64_t* masks = nullptr;
  Layout layout;
  size_t bucket_bytes = 0;
  // One stash per absolute butterfly bit-level; pair(bit) sheds into
  // level_stashes[bit].
  ResidualStash* level_stashes = nullptr;
};

// L1-sized leaf of the recursion below: a sub-network of this many levels (16
// buckets, ~29 KiB at the default layout) is routed by the flat level-by-level
// loop instead of recursing further, which caps the recursion overhead at one
// call per 32 MergeSplits.
//
// It is named rather than local because it is also the FINEST CUT a subtask
// decomposition can make: the phase planners slice a butterfly by walking this
// same recursion and stopping early (PlanSubnetwork), so its stopping rule has
// to agree with this one or the sliced issue order stops being the kernel's
// own.  It also decides whether a preparation's copy can be tiled against its
// route (PlanCopyThenRoute): a kernel leaf has no root split to tile by.
inline constexpr unsigned kButterflyLeafLevels = 4;

// The recursion's shape, in one place because two walks have to agree on it
// exactly: RouteSubnetworkRecursive below and the planners' PlanSubnetwork and
// PlanCopyThenRoute.  They are not merely similar -- a sliced butterfly is
// byte-identical to a monolithic one only because the cut frontier is a
// frontier of this same tree.  The split below never reads the budget, so a
// planner may cut at any frontier and still issue the kernel's own leaf order.
//
// Bucket touches of a sub-network of `levels` levels: one MergeSplit reads and
// writes two buckets, and a level is 2^(levels-1) of them.
inline constexpr size_t SubnetworkTouches(unsigned levels) {
  return static_cast<size_t>(levels) << levels;
}

// Whether this node is issued whole rather than split further.  The kernel has
// no budget and passes 0, which makes this exactly `levels <=
// kButterflyLeafLevels`: a leaf cannot be cut anyway, since its flat loop
// interleaves two levels as fused quads.
inline constexpr bool SubnetworkIsLeaf(unsigned levels, size_t budget_touches) {
  return levels <= kButterflyLeafLevels ||
         SubnetworkTouches(levels) <= budget_touches;
}

// The split: 2^high contiguous low-half sub-networks on bits [0, low), then
// 2^low stride-multiplied high-half ones on bits [low, levels).
//
// `low` is kept EVEN.  A leaf routes its levels two at a time as fused quads
// and only an odd final level as a pair pass, which moves twice the lines per
// level; with an even low half, every low branch of the tree has an even level
// count and only the high chain can end in an odd leaf, so a route has at most
// one unfused level.  A plain `levels >> 1` would leave 2-8 unfused levels in
// a route of 10-24 levels.
struct SubnetworkSplit {
  unsigned low = 0;
  unsigned high = 0;
};

inline constexpr SubnetworkSplit SplitSubnetwork(unsigned levels) {
  const unsigned low = (levels >> 1) & ~1u;
  return SubnetworkSplit{low, levels - low};
}

// Routes tag bits [log2_stride, log2_stride + levels) of the sub-network
// {base + j << log2_stride : j in [0, 2^levels)}.
template <bool CheckOverflow = false>
inline bool RouteSubnetworkRecursive(const ButterflyStashContext& ctx,
                                     size_t base, unsigned log2_stride,
                                     unsigned levels) {
  uint8_t* data = ctx.data;
  uint64_t* masks = ctx.masks;
  const Layout& layout = ctx.layout;
  const size_t bb = ctx.bucket_bytes;
  // The leaf's levels are taken two at a time as fused quads (four buckets
  // resident across both levels).
  if (SubnetworkIsLeaf(levels, /*budget_touches=*/0)) {
    const size_t count = size_t{1} << levels;
    unsigned lev = 0;
    for (; lev + 1 < levels; lev += 2) {
      const size_t half = size_t{1} << lev;
      const unsigned bit = log2_stride + lev;
      for (size_t mid = 0; mid < count; ++mid) {
        if (mid & (half | (half << 1))) continue;
        const size_t i = base + (mid << log2_stride);
        if (!MergeSplitQuadStash<CheckOverflow>(
                data + i * bb, &masks[i], bb, layout, bit,
                ctx.level_stashes[bit], ctx.level_stashes[bit + 1])) {
          return false;
        }
      }
    }
    for (; lev < levels; ++lev) {
      const size_t half = size_t{1} << lev;
      const unsigned bit = log2_stride + lev;
      const size_t lines = layout.RoutedLines(bit);
      const size_t tag_line = layout.TagLine(bit);
      for (size_t mid = 0; mid < count; ++mid) {
        if (mid & half) continue;
        const size_t i = base + (mid << log2_stride);
        const size_t j = base + ((mid | half) << log2_stride);
        if (!MergeSplitPairStash<CheckOverflow>(
                data + i * bb, data + j * bb, &masks[i], &masks[j], lines,
                tag_line, bit, ctx.level_stashes[bit])) {
          return false;
        }
      }
    }
    return true;
  }
  const SubnetworkSplit split = SplitSubnetwork(levels);
  for (size_t h = 0; h < (size_t{1} << split.high); ++h) {
    if (!RouteSubnetworkRecursive<CheckOverflow>(
            ctx, base + (h << (log2_stride + split.low)), log2_stride,
            split.low)) {
      return false;
    }
  }
  for (size_t l = 0; l < (size_t{1} << split.low); ++l) {
    if (!RouteSubnetworkRecursive<CheckOverflow>(
            ctx, base + (l << log2_stride), log2_stride + split.low,
            split.high)) {
      return false;
    }
  }
  return true;
}

// Drop-in replacement for ButterflyRouteStash (route_levels <
// log2(num_buckets) splits the array into independent contiguous blocks,
// exactly as the flat version pairs them).
template <bool CheckOverflow = false>
inline bool ButterflyRouteStashCacheOblivious(
    TableView t, unsigned route_levels, ResidualStash* level_stashes) {
  const size_t num_buckets = t.num_buckets;
  if (num_buckets <= 1 || route_levels == 0) return true;
  assert(route_levels <= Log2Exact(num_buckets));
  assert(t.layout.tag_bytes * 8 >= route_levels);
  ButterflyStashContext ctx;
  ctx.data = t.data;
  ctx.masks = t.masks;
  ctx.layout = t.layout;
  ctx.bucket_bytes = t.layout.BucketBytes();
  ctx.level_stashes = level_stashes;
  const size_t block = size_t{1} << route_levels;
  for (size_t base = 0; base < num_buckets; base += block) {
    if (!RouteSubnetworkRecursive<CheckOverflow>(ctx, base, 0,
                                                          route_levels)) {
      return false;
    }
  }
  return true;
}

}  // namespace byteslice
}  // namespace microram
