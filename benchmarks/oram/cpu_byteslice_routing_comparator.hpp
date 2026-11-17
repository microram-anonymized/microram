#pragma once

// Benchmark-only fusion ablation for the routing network.  The production
// butterfly (src/oram/rebuild/cpu_byteslice_butterfly_stash.hpp) fuses two
// butterfly levels into one four-bucket "quad" merge-split per pass over the
// data; these traversals (`--network grouped6_unfused` and
// `cache_oblivious_unfused` of cpu_byteslice_stash_rebuild_benchmark) mirror
// the production grouped and cache-oblivious traversals, sharing their
// leaf/split rules, tag pruning and stage stashes, and differ only in calling
// MergeSplitQuadStashUnfused (the same quad as two separate pair passes).
// No production engine, capacity, tag pruning or routing obligation changes.
#include "src/oram/rebuild/cpu_byteslice_butterfly_stash.hpp"

namespace microram::byteslice::benchmark_comparator {

template <bool CheckOverflow = false>
inline bool GroupedUnfused(TableView t, unsigned route_levels,
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
            if (!MergeSplitQuadStashUnfused<CheckOverflow>(
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

template <bool CheckOverflow = false>
inline bool SubnetworkUnfused(const ButterflyStashContext& ctx,
                              size_t base, unsigned log2_stride,
                              unsigned levels) {
  uint8_t* data = ctx.data;
  uint64_t* masks = ctx.masks;
  const Layout& layout = ctx.layout;
  const size_t bb = ctx.bucket_bytes;
  // Keep the production leaf order; use its two-pass quad comparator.
  if (SubnetworkIsLeaf(levels, /*budget_touches=*/0)) {
    const size_t count = size_t{1} << levels;
    unsigned lev = 0;
    for (; lev + 1 < levels; lev += 2) {
      const size_t half = size_t{1} << lev;
      const unsigned bit = log2_stride + lev;
      for (size_t mid = 0; mid < count; ++mid) {
        if (mid & (half | (half << 1))) continue;
        const size_t i = base + (mid << log2_stride);
        if (!MergeSplitQuadStashUnfused<CheckOverflow>(
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
    if (!SubnetworkUnfused<CheckOverflow>(
            ctx, base + (h << (log2_stride + split.low)), log2_stride,
            split.low)) {
      return false;
    }
  }
  for (size_t l = 0; l < (size_t{1} << split.low); ++l) {
    if (!SubnetworkUnfused<CheckOverflow>(
            ctx, base + (l << log2_stride), log2_stride + split.low,
            split.high)) {
      return false;
    }
  }
  return true;
}

template <bool CheckOverflow = false>
inline bool CacheObliviousUnfused(
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
    if (!SubnetworkUnfused<CheckOverflow>(ctx, base, 0, route_levels)) {
      return false;
    }
  }
  return true;
}

}  // namespace microram::byteslice::benchmark_comparator
