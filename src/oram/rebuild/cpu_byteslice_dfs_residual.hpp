#pragma once

// THE PUBLIC-CAPACITY DFS RESIDUAL DISTRIBUTOR
// (analysis/bound_certification/REPORT.tex, "A simpler distributor:
// containment of range events").
//
// It builds a residual pass's RANGE TABLE: the table of candidate pages a
// second-chance sweep offers to the main buckets (defined in
// cpu_byteslice_residual_range.hpp).  The gathered, tagged pool is
// partitioned by destination into one LEAF per coarse range -- 2^index_bits
// main homes, the production plan's range (DfsResidualRangePlan) -- of
// `pages` 64-slot pages, holding exactly that range's candidates in pool
// order.  Page g of leaf l is range
// bucket g * 2^coarse_bits + l, the stacked geometry the offers read
// (DfsResidualRangePlan): main bucket b is offered page g of leaf
// b >> index_bits, for every g in order.  So the downstream consumers --
// fused offers, lanes, drains, the leftover dedup -- read a DFS-built range
// table exactly as they read any other.
//
// CAPACITIES ARE PUBLIC AND NESTED.  A node covering 2^h leaves (its HEIGHT
// h) holds the pool records routed below it and has capacity
// C(h) = min(P, S * 2^h), S = 64 * pages, P = the pool's slots.  If every leaf
// holds at most S candidates then every node fits: an ancestor holds only its
// descendants' records.  So ONE event -- some coarse range has more than S
// candidates -- covers the whole distributor, with no factor for nodes or
// depth; a failure is a checked, declared overflow like every other capacity.
//
// THE TREE, cheapest first:
//   - Heights where C(h) = P cannot fail, so they are not split level by
//     level.  The gathered pool is compacted DIRECTLY into each node at the
//     first height hd with C(hd) < P, one child at a time, selecting that
//     child's top destination bits.  That is 2^(D - hd) compactions of P
//     against 2 * (2^(D - hd) - 1) for binary splits.
//   - Below hd every split halves the capacity.  Both children are one unit.
//     The left child is compacted from the parent into the left buffer of its
//     height; the RIGHT child is compacted in place in the parent's own
//     buffer, which is dead after the split.  Right children therefore need
//     no buffer of their own, and the pending sibling on the DFS path is the
//     parent's storage.
//   - Children at height 0 are compacted straight into their leaf's pages.
//   - Subtrees whose homes start at or past `main_buckets` are PADDING (the
//     empty top ranges of a mixed-radix output).  They are public and hold
//     no record, so they are skipped; their leaf pages are cleared instead.
//
// A UNIT is one direct child's compaction or one split: both children's
// compactions, selected by one pass over the parent and fed by one read of it
// where the parent is small (DfsCompactNetwork), or the left one alone when
// the right is padding.  The whole traversal is a public list of units built
// by Configure.  Units run strictly in order (Run), each touching only public
// addresses, so a scheduler may stop between any two and resume on another
// thread: the position is the unit index, and everything a unit reads is in
// this workspace.  A unit is indivisible: one compaction of P slots, or two of
// a parent below P.  Nothing is allocated after construction.
//
// Freshness is untouched: a leaf holds its range's candidates in pool order,
// with every byte -- key, payload, tag, class mark, tombstone -- preserved.
// The gathered pool is private scratch; the pass's sources stay where they
// are for its epilogue.
#include <immintrin.h>

#include <algorithm>
#include <cassert>
#include <stdexcept>
#include <utility>
#include <vector>

#include "src/core/mov_intrinsics.hpp"
#include "src/oram/rebuild/cpu_byteslice_residual_range.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"

namespace microram {
namespace byteslice {

// The range plan a DFS pass offers from: the production plan's partition of
// the destination into 2^range_bits coarse ranges of 2^index_bits homes, with
// `pages` stacked pages per range.  A pool whose
// production plan is DIRECT (it routes nothing, so it has no range event) or
// empty keeps that plan and gets no DFS.
// Whether a pool's production plan routes at all, which is when a DFS
// distributor has a range event to replace.
inline bool DfsResidualRangeApplies(size_t pool_buckets,
                                    unsigned main_levels) {
  if (pool_buckets == 0) return false;
  const ResidualRangePlan plan = PlanResidualRange(pool_buckets, main_levels);
  return !(plan.range_bits == 0 && plan.groups == pool_buckets &&
           plan.index_bits == main_levels);
}

// The widest coarse range, in homes: 2^kDfsMaxRangeIndexBits.  A range's
// capacity event bounds the complete-home excess of its homes, whose tail
// grows with the range (at half load one 64-slot page over 2^18 homes is
// about 2^-82.8, and each doubling costs about 2^4.8), so the range must not
// grow with the table.  The production width (8 ranges per pool bucket)
// only reaches the cap where a small pool meets a large main: the top
// finish's retained carry, two buckets over 2^23 or more homes.
inline constexpr unsigned kDfsMaxRangeIndexBits = 18;

// The coarse ranges keep the production plan's width, narrowed where it
// would span more than 2^kDfsMaxRangeIndexBits homes: the certified coarse
// events (analysis/bound_certification) are evaluated at exactly this plan.
inline ResidualRangePlan DfsResidualRangePlan(size_t pool_buckets,
                                              unsigned main_levels,
                                              size_t pages) {
  ResidualRangePlan plan = PlanResidualRange(pool_buckets, main_levels);
  if (!DfsResidualRangeApplies(pool_buckets, main_levels)) return plan;
  if (plan.index_bits > kDfsMaxRangeIndexBits) {
    plan.range_bits += plan.index_bits - kDfsMaxRangeIndexBits;
    plan.index_bits = kDfsMaxRangeIndexBits;
  }
  plan.groups = pages;
  plan.range_buckets = pages << plan.range_bits;
  plan.scatter_per_bucket = kBucketCapacity;
  return plan;
}

// Whether `plan` is the DFS leaf table DfsResidualRangePlan gives this pool.
// (At one page it has the shape of a saturated production plan; what makes a
// pass DFS is its workspace, which only a DFS-shaped pass may be given.)
inline bool IsDfsResidualRangePlan(const ResidualRangePlan& plan,
                                   size_t pool_buckets, unsigned main_levels,
                                   size_t pages) {
  if (!DfsResidualRangeApplies(pool_buckets, main_levels)) return false;
  const ResidualRangePlan dfs =
      DfsResidualRangePlan(pool_buckets, main_levels, pages);
  return plan.range_bits == dfs.range_bits &&
         plan.index_bits == dfs.index_bits && plan.groups == dfs.groups &&
         plan.range_buckets == dfs.range_buckets &&
         plan.scatter_per_bucket == dfs.scatter_per_bucket;
}

// The DIRECT plan at any depth: the range table is the pool itself and every
// main bucket is offered every pool bucket, so there is no route and no range
// event at all.  Its cost is main_buckets * pool_buckets offers, which is why
// PlanResidualRange uses it only for the smallest mains by default.
inline ResidualRangePlan DirectResidualRangePlan(size_t pool_buckets,
                                                 unsigned main_levels) {
  if (pool_buckets == 0) return PlanResidualRange(0, main_levels);
  ResidualRangePlan plan;
  plan.range_bits = 0;
  plan.index_bits = main_levels;
  plan.groups = pool_buckets;
  plan.range_buckets = pool_buckets;
  plan.scatter_per_bucket = kBucketCapacity;
  return plan;
}

namespace dfs_detail {

// [a >= b] as an integer: a compare that compiles to setcc, never a branch.
INLINE uint64_t Ge(uint64_t a, uint64_t b) { return static_cast<uint64_t>(a >= b); }

INLINE size_t LargestPow2AtMost(size_t n) {
  return size_t{1} << (63 - __builtin_clzll(static_cast<unsigned long long>(n)));
}
INLINE unsigned Log2Pow2(size_t pow2) {
  return static_cast<unsigned>(__builtin_ctzll(static_cast<unsigned long long>(pow2)));
}

INLINE __m512i Load(const uint8_t* p) {
  return _mm512_loadu_si512(reinterpret_cast<const void*>(p));
}
INLINE void Store(uint8_t* p, __m512i v) {
  _mm512_storeu_si512(reinterpret_cast<void*>(p), v);
}

INLINE __m512i Iota() {
  return _mm512_set_epi8(63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48,
                         47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32,
                         31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16,
                         15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0);
}

// The 64-bit mask of lanes i with i >= k, for any integer k (clamped to
// [0, 64]).  Branch-free: max/min by sign-bit arithmetic, then BZHI, which
// returns its first operand unchanged for an index of 64.
INLINE uint64_t LanesFrom(int64_t k) {
  const int64_t lo = k & ~(k >> 63);            // max(k, 0)
  const int64_t d = 64 - lo;
  const int64_t hi = 64 - (d & ~(d >> 63));     // min(lo, 64)
  return ~_bzhi_u64(~uint64_t{0}, static_cast<unsigned>(hi));
}

// The blends of a group of n (a power of two) blocks and of a network of n,
// in DfsCompactNetwork's order: a tile's plan has one mask per blend.
constexpr size_t GroupOps(size_t n) {
  return n <= 1 ? 0 : 2 * GroupOps(n / 2) + n / 2;
}
constexpr size_t Pow2AtMost(size_t n) {
  return n <= 1 ? 1 : 2 * Pow2AtMost(n / 2);
}
constexpr size_t ForwardOps(size_t n) {
  return n <= 1 ? 0
                : ForwardOps(n - Pow2AtMost(n)) + GroupOps(Pow2AtMost(n)) +
                      (n - Pow2AtMost(n));
}
constexpr size_t MaxForwardOps(size_t n) {
  return n == 0 ? 0 : std::max(ForwardOps(n), MaxForwardOps(n - 1));
}

}  // namespace dfs_detail

// THE COMPACTION NETWORK, FED BY BLOCK MASKS.  ORCompact (Sasy, Johnson,
// Goldberg, "Fast Fully Oblivious Compaction and Shuffling", CCS 2022,
// Figures 1-2) over byte-sliced blocks, level for level: marked records go to
// the front in order.  A power-of-two group of blocks compacts its halves to
// offsets z mod n/2 and (z + m) mod n/2, m the left half's marks, then swaps
// across the halves under the flag s ^ [i >= (z + m) mod n/2],
// s = [(z mod n/2) + m >= n/2] ^ [z >= n/2]; a general count peels off its
// largest power-of-two suffix (Forward).  The per-record form reads a prefix
// count per RECORD, which costs 64 counts per block to build and 63 scalar
// iterations per block to read in the fused intra-block levels -- a fixed
// cost that would dominate the DFS's small nodes.  Here the cross-block levels
// read per-BLOCK counts (`block_prefix[b]`, the marks before block b) and the
// intra-block levels are one compress and one rotation of the block's own
// 64-bit mark word.  The placement of every marked record is the network's;
// unmarked records may sit in other dummy positions, which nothing reads.
// The marks and the offsets are secret and meet the records only in
// registers.
//
// WHERE THE BLOCKS LIVE.  Block b is read from `src` (the parent) by its own
// intra-block step, which is always the first thing the network does to it,
// and from then on lives at Out(b): `out` + b * `out_stride` for the `keep`
// blocks the caller reads -- the child -- and `work` otherwise.  So the parent
// is compacted without first being copied, and a leaf child is compacted
// straight into its stacked pages.  The last level stores only the kept
// blocks.  All of it is public: the shape and `keep` fix every address.
//
// LINE-MAJOR TILES.  Every intra-block index and every blend mask depends on
// the marks and the block counts only, never on the records.  So a TILE -- a
// sub-network of at most kTileBlocks blocks, the whole network of a small
// parent or the lowest levels of a larger one -- is planned first, then run a
// line at a time: each block's line is loaded from `src`, permuted and blended
// in registers in network order, and stored once.  All loads of a line precede
// its stores, so a compaction in place is safe.  A larger network runs its
// tiles first and then its remaining levels as block passes, in their order;
// the tiles are disjoint and each precedes every level above it, so this is
// the network's own order restricted to each block.  The network may carry
// two compactions of one parent (a split's two children, the second possibly
// in place).  Where the parent is one tile, one read of each line feeds both.
class DfsCompactNetwork {
 public:
  // One compaction of the parent: its selection, the marks before each block,
  // and where its blocks live.
  struct Side {
    const uint32_t* block_prefix;
    const uint64_t* marks;
    uint8_t* work;  // block b at work + b * block bytes, when not kept
    uint8_t* out;   // kept block b at out + b * out_stride
    size_t out_stride;
  };

  // Eight blocks' lines and indices fill half the vector registers.
  static constexpr size_t kTileBlocks = 8;

  // `count` (one or two) compactions of the `blocks` blocks at `src`, each
  // keeping its first `keep`.  Only the last side may write `src`: the first
  // one's stores of a line come before the second one's loads of it.
  DfsCompactNetwork(const uint8_t* src, size_t lines, size_t blocks,
                    size_t keep, const Side* sides, size_t count)
      : src_(src), lines_(lines), blocks_(blocks), keep_(keep),
        sides_(sides), count_(count) {}

  // Marked records of all blocks to the front, in order.
  void Compact() {
    if (blocks_ <= kTileBlocks) {
      Tile(0, blocks_, 0, false, keep_, 0, count_);
      return;
    }
    for (side_ = 0; side_ < count_; ++side_) {
      phase_ = kTiles;
      Forward(0, blocks_, keep_);
      phase_ = kPasses;
      Forward(0, blocks_, keep_);
    }
  }

 private:
  static constexpr size_t kStoreAll = ~size_t{0};

  // The recursion below runs a network in one of three ways: its tiles, its
  // levels above the tiles, or -- inside one tile -- recording the tile's plan.
  enum Phase : uint8_t { kTiles, kPasses, kPlan };

  // One side's tile, in network order: each block's intra-block index, then
  // every blend's mask.
  struct TilePlan {
    __m512i idx[kTileBlocks];
    uint64_t mask[dfs_detail::MaxForwardOps(kTileBlocks)];
    size_t lo, ops;
  };

  // Blocks [lo, lo + n); a level's blend stores only blocks below `store`.
  void Forward(size_t lo, size_t n, size_t store) {
    if (n == 0) return;
    if (phase_ != kPlan && n <= kTileBlocks) {
      if (phase_ == kTiles) Tile(lo, n, 0, false, store, side_, 1);
      return;
    }
    if (n == 1) {
      Intra(lo, 0);
      return;
    }
    const size_t n1 = dfs_detail::LargestPow2AtMost(n);
    const size_t n2 = n - n1;
    const uint32_t m = Prefix(lo + n2) - Prefix(lo);
    Forward(lo, n2, kStoreAll);
    // With n2 = 0 the group's own top level is the last one.
    ForwardGroup(lo + n2, dfs_detail::Log2Pow2(n1) + 6,
                 (64 * n1 - 64 * n2 + m) & (64 * n1 - 1),
                 n2 == 0 ? store : kStoreAll);
    if (phase_ == kTiles) return;
    for (size_t t = 0; t < n2; ++t) {
      Blend(lo + t, lo + t + n1,
            dfs_detail::LanesFrom(static_cast<int64_t>(m) - 64 * t), store);
    }
  }

  void CrossLevel(size_t start, unsigned levels, size_t z, size_t store) {
    const size_t half = size_t{1} << (levels - 1);
    const size_t half_blocks = half >> 6;
    const uint32_t m = Prefix(start + half_blocks) - Prefix(start);
    const size_t z_left = z & (half - 1);
    const size_t z_right = (z + m) & (half - 1);
    const uint64_t s = dfs_detail::Ge(z_left + m, half) ^ dfs_detail::Ge(z, half);
    const uint64_t s_mask = uint64_t{0} - s;
    for (size_t t = 0; t < half_blocks; ++t) {
      const uint64_t mask =
          dfs_detail::LanesFrom(static_cast<int64_t>(z_right) -
                            static_cast<int64_t>(64 * t)) ^
          s_mask;
      Blend(start + t, start + t + half_blocks, mask, store);
    }
  }

  void ForwardGroup(size_t start, unsigned levels, size_t z, size_t store) {
    const size_t blocks = size_t{1} << (levels - 6);
    if (phase_ != kPlan && blocks <= kTileBlocks) {
      if (phase_ == kTiles) Tile(start, blocks, z, true, store, side_, 1);
      return;
    }
    if (levels == 6) {
      Intra(start, z & 63u);
      return;
    }
    const size_t half = size_t{1} << (levels - 1);
    const size_t half_blocks = half >> 6;
    const uint32_t m = Prefix(start + half_blocks) - Prefix(start);
    ForwardGroup(start, levels - 1, z & (half - 1), kStoreAll);
    ForwardGroup(start + half_blocks, levels - 1, (z + m) & (half - 1),
                 kStoreAll);
    if (phase_ != kTiles) CrossLevel(start, levels, z, store);
  }

  uint32_t Prefix(size_t block) const {
    return sides_[side_].block_prefix[block];
  }

  uint8_t* Out(size_t side, size_t block) const {
    const Side& s = sides_[side];
    return block < keep_ ? s.out + block * s.out_stride
                         : s.work + block * lines_ * 64;
  }

  // BlendBlocks between Out(a) and Out(b), a < b, storing each side only
  // below `store`: a pair whose outputs are both past it is not computed.
  // Inside a tile, the mask is recorded instead.
  void Blend(size_t a, size_t b, uint64_t mask, size_t store) {
    if (phase_ == kPlan) {
      plan_->mask[plan_->ops++] = mask;
      return;
    }
    if (a >= store) return;
    uint8_t* pa = Out(side_, a);
    uint8_t* pb = Out(side_, b);
    if (b >= store) {
      for (size_t p = 0; p < lines_; ++p) {
        const __m512i x = dfs_detail::Load(pa + p * 64);
        const __m512i y = dfs_detail::Load(pb + p * 64);
        dfs_detail::Store(pa + p * 64, core::obliMaskMov8(x, mask, y));
      }
      return;
    }
    for (size_t p = 0; p < lines_; ++p) {
      const __m512i x = dfs_detail::Load(pa + p * 64);
      const __m512i y = dfs_detail::Load(pb + p * 64);
      dfs_detail::Store(pa + p * 64, core::obliMaskMov8(x, mask, y));
      dfs_detail::Store(pb + p * 64, core::obliMaskMov8(y, mask, x));
    }
  }

  // The six intra-block levels of one block, fused into one permutation, with
  // `z` the block's segment offset.  They put the marked record of rank r at
  // lane (z + r) mod 64, so the index is the marked lanes compressed to the
  // front and rotated up by z; the other lanes read lane 0, a dummy position.
  // The compress stays in a register (its memory form stores popcount bytes)
  // and z only feeds register arithmetic.  Only a tile's plan records it.
  void Intra(size_t block, size_t z) {
    const __m512i iota = dfs_detail::Iota();
    const __m512i packed = _mm512_maskz_compress_epi8(
        _cvtu64_mask64(sides_[side_].marks[block]), iota);
    // VPERMB reads the low six index bits: lane p takes packed[(p - z) mod 64].
    plan_->idx[block - plan_->lo] = _mm512_permutexvar_epi8(
        _mm512_sub_epi8(iota, _mm512_set1_epi8(static_cast<char>(z))), packed);
  }

  // Plans the tile at blocks [lo, lo + n) -- a network (`group` false, where
  // z is 0) or a group at offset z -- for sides [first, first + count), then
  // runs it.
  void Tile(size_t lo, size_t n, size_t z, bool group, size_t store,
            size_t first, size_t count) {
    const Phase phase = phase_;
    const size_t side = side_;
    phase_ = kPlan;
    for (size_t s = 0; s < count; ++s) {
      side_ = first + s;
      plan_ = &plans_[s];
      plan_->lo = lo;
      plan_->ops = 0;
      if (group) {
        ForwardGroup(lo, dfs_detail::Log2Pow2(n) + 6, z, store);
      } else {
        Forward(lo, n, store);
      }
      assert(plan_->ops == dfs_detail::ForwardOps(n));
    }
    phase_ = phase;
    side_ = side;
    switch (n) {
      case 1: return RunTile<1>(lo, store, first, count);
      case 2: return RunTile<2>(lo, store, first, count);
      case 3: return RunTile<3>(lo, store, first, count);
      case 4: return RunTile<4>(lo, store, first, count);
      case 5: return RunTile<5>(lo, store, first, count);
      case 6: return RunTile<6>(lo, store, first, count);
      case 7: return RunTile<7>(lo, store, first, count);
      default: return RunTile<8>(lo, store, first, count);
    }
  }

  template <size_t N>
  void RunTile(size_t lo, size_t store, size_t first, size_t count) {
    static_assert(N <= kTileBlocks, "a tile is at most kTileBlocks blocks");
    if (count == 2) {
      RunTileLines<N, 2>(lo, store, first);
    } else {
      RunTileLines<N, 1>(lo, store, first);
    }
  }

  // The tile a line at a time.  Its indices and masks are copied into locals
  // first: the line stores may alias the plans, which would otherwise be
  // re-read every line.  The masks meet the lines only through the
  // register-only blend.
  template <size_t N, size_t S>
  void RunTileLines(size_t lo, size_t store, size_t first) {
    constexpr size_t kOps = dfs_detail::ForwardOps(N);
    const size_t block_bytes = lines_ * 64;
    const size_t kept = store <= lo ? 0 : std::min(N, store - lo);
    __m512i idx[S][N];
    uint64_t mask[S][kOps > 0 ? kOps : 1];
    uint8_t* to[S][N];
    for (size_t s = 0; s < S; ++s) {
      for (size_t b = 0; b < N; ++b) {
        idx[s][b] = plans_[s].idx[b];
        to[s][b] = Out(first + s, lo + b);
      }
      for (size_t k = 0; k < kOps; ++k) mask[s][k] = plans_[s].mask[k];
    }
    const uint8_t* from = src_ + lo * block_bytes;
    for (size_t p = 0; p < lines_; ++p) {
      for (size_t s = 0; s < S; ++s) {
        __m512i v[N];
        for (size_t b = 0; b < N; ++b) {
          v[b] = _mm512_permutexvar_epi8(
              idx[s][b], dfs_detail::Load(from + b * block_bytes + p * 64));
        }
        RegForward<0, N, 0>(v, mask[s]);
        for (size_t b = 0; b < N; ++b) {
          if (b < kept) dfs_detail::Store(to[s][b] + p * 64, v[b]);
        }
      }
    }
  }

  // Forward and ForwardGroup over one line of blocks [Lo, Lo + N) held in v,
  // with compile-time block indices, taking their masks from m[K] on in the
  // order the recursion above records them.
  template <size_t Lo, size_t N, size_t K>
  static INLINE void RegForward(__m512i* v, const uint64_t* m) {
    using dfs_detail::ForwardOps, dfs_detail::GroupOps, dfs_detail::Pow2AtMost;
    if constexpr (N > 1) {
      constexpr size_t n1 = Pow2AtMost(N);
      constexpr size_t n2 = N - n1;
      RegForward<Lo, n2, K>(v, m);
      RegGroup<Lo + n2, n1, K + ForwardOps(n2)>(v, m);
      RegBlends<Lo, Lo + n1, K + ForwardOps(n2) + GroupOps(n1)>(
          v, m, std::make_index_sequence<n2>{});
    }
  }
  template <size_t Lo, size_t N, size_t K>
  static INLINE void RegGroup(__m512i* v, const uint64_t* m) {
    using dfs_detail::GroupOps;
    if constexpr (N > 1) {
      RegGroup<Lo, N / 2, K>(v, m);
      RegGroup<Lo + N / 2, N / 2, K + GroupOps(N / 2)>(v, m);
      RegBlends<Lo, Lo + N / 2, K + 2 * GroupOps(N / 2)>(
          v, m, std::make_index_sequence<N / 2>{});
    }
  }
  template <size_t A, size_t B, size_t K, size_t... T>
  static INLINE void RegBlends(__m512i* v, const uint64_t* m,
                               std::index_sequence<T...>) {
    (RegBlend(v[A + T], v[B + T], m[K + T]), ...);
  }
  static INLINE void RegBlend(__m512i& x, __m512i& y, uint64_t mask) {
    const __m512i a = x;
    x = core::obliMaskMov8(a, mask, y);
    y = core::obliMaskMov8(y, mask, a);
  }

  const uint8_t* src_;
  size_t lines_, blocks_, keep_;
  const Side* sides_;
  size_t count_;
  size_t side_ = 0;
  Phase phase_ = kTiles;
  TilePlan* plan_ = nullptr;
  TilePlan plans_[2];
};

class DfsResidualWorkspace {
 public:
  // One pass's public shape.
  struct Shape {
    size_t pool_buckets = 0;   // the swept pool, gathered
    unsigned coarse_bits = 0;  // log2 of the leaves
    unsigned index_bits = 0;   // log2 of the homes per leaf
    size_t main_buckets = 0;   // homes; leaves from here on are padding
  };

  // What one workspace allocates: every pass of the level fits it.
  struct Bytes {
    size_t data_bytes = 0;   // one aligned block of record buffers
    size_t plain_bytes = 0;  // buffer descriptors, masks, prefix sums, unit list
  };

  static constexpr unsigned kMaxCoarseBits = 16;

  DfsResidualWorkspace(const Layout& layout, size_t max_pool_buckets,
                       unsigned max_coarse_bits, size_t pages)
      : layout_(layout), max_pool_(max_pool_buckets),
        max_coarse_(max_coarse_bits), pages_(pages) {
    ValidateLayoutWidths(layout);
    if (layout.key_bytes < 1 || layout.key_bytes > kMaxKeyBytes ||
        layout.tag_bytes < 1 || layout.tag_bytes > 8 ||
        max_pool_buckets == 0 || max_pool_buckets > (size_t{1} << 20) ||
        pages == 0 || pages > 64 || max_coarse_bits > kMaxCoarseBits) {
      throw std::invalid_argument("DFS residual: invalid public geometry");
    }
    const Plan plan = PlanBuffers(max_pool_buckets, max_coarse_bits, pages);
    top_ = plan.top_height;
    buckets_ = plan.buffer_buckets;
    size_t total = 0;
    offsets_.resize(buckets_.size());
    for (size_t i = 0; i < buckets_.size(); ++i) {
      offsets_[i] = total;
      total += buckets_[i];
    }
    data_ = AllocateAligned64(CheckedTableBytes(total, layout));
    masks_.assign(total, 0);
    select_.resize(max_pool_buckets);
    prefix_.resize(max_pool_buckets + 1);
    select_right_.resize(SplitParentBuckets(plan));
    prefix_right_.resize(SplitParentBuckets(plan) + 1);
    units_.reserve(MaxUnits(max_coarse_bits));
  }

  DfsResidualWorkspace(const DfsResidualWorkspace&) = delete;
  DfsResidualWorkspace& operator=(const DfsResidualWorkspace&) = delete;

  // The allocation the constructor makes, for a caller's byte bill.
  static Bytes Planned(const Layout& layout, size_t max_pool_buckets,
                       unsigned max_coarse_bits, size_t pages) {
    const Plan plan = PlanBuffers(max_pool_buckets, max_coarse_bits, pages);
    size_t total = 0;
    for (size_t b : plan.buffer_buckets) total += b;
    const size_t split = SplitParentBuckets(plan);
    Bytes bytes;
    bytes.data_bytes = CheckedTableBytes(total, layout);
    bytes.plain_bytes = 2 * plan.buffer_buckets.size() * sizeof(size_t) +
                        (total + max_pool_buckets + split) * sizeof(uint64_t) +
                        (max_pool_buckets + split + 2) * sizeof(uint32_t) +
                        MaxUnits(max_coarse_bits) * sizeof(Unit);
    return bytes;
  }
  Bytes Allocated() const {
    Bytes bytes;
    bytes.data_bytes =
        CheckedTableBytes(offsets_.back() + buckets_.back(), layout_);
    bytes.plain_bytes = (buckets_.capacity() + offsets_.capacity()) *
                            sizeof(size_t) +
                        (masks_.capacity() + select_.capacity() +
                         select_right_.capacity()) *
                            sizeof(uint64_t) +
                        (prefix_.capacity() + prefix_right_.capacity()) *
                            sizeof(uint32_t) +
                        units_.capacity() * sizeof(Unit);
    return bytes;
  }

  // Binds one pass: its capacities and its public unit list.  No allocation.
  void Configure(const Shape& shape) {
    if (shape.pool_buckets == 0 || shape.pool_buckets > max_pool_ ||
        shape.coarse_bits > max_coarse_ ||
        shape.index_bits >= 8 * sizeof(size_t) ||
        shape.index_bits + shape.coarse_bits > layout_.tag_bytes * 8 ||
        shape.index_bits + shape.coarse_bits >= 8 * sizeof(size_t) ||
        shape.main_buckets == 0 ||
        shape.main_buckets >
            (size_t{1} << (shape.index_bits + shape.coarse_bits))) {
      throw std::invalid_argument("DFS residual: invalid pass shape");
    }
    shape_ = shape;
    direct_height_ = DirectHeight(shape.pool_buckets, shape.coarse_bits,
                                  pages_);
    if (direct_height_ > top_) {
      throw std::logic_error("DFS residual: a pass is wider than its storage");
    }
    units_.clear();
    touches_ = 0;
    ForEachUnit(shape, pages_, [&](const Unit& unit) {
      Push(unit);
      touches_ += UnitTouchesOf(shape, pages_, unit);
    });
    next_ = 0;
    failed_ = false;
    configured_ = true;
  }

  const Shape& shape() const { return shape_; }
  size_t pages() const { return pages_; }
  size_t Units() const { return units_.size(); }
  // The whole partition's work estimate in bucket touches: every unit's
  // UnitTouches, summed.
  size_t Touches() const { return touches_; }
  unsigned DirectHeight() const { return direct_height_; }
  // A node's capacity in slots at `height`, for the bound's audit.
  size_t Capacity(unsigned height) const {
    return NodeCapacity(shape_.pool_buckets, pages_, height);
  }

  // WHAT A PASS'S PARTITION COSTS, from its public shape alone: its unit
  // count and Touches(), without a workspace -- the numbers Configure gives a
  // workspace bound to `shape`, from the same traversal.  For a caller's
  // estimate of the work ahead (the inline executor's share).
  struct Price {
    size_t units = 0;
    size_t touches = 0;
  };
  static Price PriceOf(const Shape& shape, size_t pages) {
    Price price;
    if (shape.pool_buckets == 0 || pages == 0) return price;
    ForEachUnit(shape, pages, [&](const Unit& unit) {
      ++price.units;
      price.touches += UnitTouchesOf(shape, pages, unit);
    });
    return price;
  }

  // The pool's gathered copy, which the caller fills -- one source bucket per
  // bucket, re-tagged and class-marked -- before the first unit runs.
  TableView Gather() {
    RequireConfigured();
    return Buffer(kGather, shape_.pool_buckets);
  }

  // Runs units [begin, end) into `leaves`, a table of pages << coarse_bits
  // buckets in the pass's layout.  Units run strictly in order; a call that
  // does not continue exactly where the last one stopped is refused.  False
  // on the first capacity overflow, which is a declared failure: the pass may
  // not be resumed after it.
  bool Run(TableView leaves, size_t begin, size_t end) {
    RequireConfigured();
    if (leaves.layout != layout_ ||
        leaves.num_buckets != (pages_ << shape_.coarse_bits) ||
        leaves.data == nullptr || leaves.masks == nullptr) {
      throw std::invalid_argument("DFS residual: wrong leaf table");
    }
    if (failed_ || begin != next_ || end < begin || end > units_.size()) {
      throw std::logic_error("DFS residual: units out of order");
    }
    if (begin == 0) ClearPaddingLeaves(leaves);
    for (size_t u = begin; u < end; ++u) {
      next_ = u + 1;
      if (!RunUnit(units_[u], leaves)) {
        failed_ = true;
        return false;
      }
    }
    return true;
  }
  bool Done() const { return configured_ && next_ == units_.size(); }

 private:
  // A direct child; a split's left child alone, its right being padding; or
  // both children of a split.
  enum UnitKind : uint8_t { kDirect, kLeft, kPair };
  // Buffer ids: the gathered pool, the direct child's buffer, then the left
  // buffer of each height below the direct one.
  static constexpr uint8_t kGather = 0;
  static constexpr uint8_t kTopBuffer = 1;
  static uint8_t LeftBuffer(unsigned height) {
    return static_cast<uint8_t>(2 + height);
  }

  // One unit.  `height` and `node` are the (left) CHILD's; `src` holds its
  // parent and `work` receives its compaction.  A pair's right child, node
  // + 1, is compacted in place in `src`.
  struct Unit {
    UnitKind kind;
    uint8_t height;
    uint8_t src;
    uint8_t work;
    uint32_t node;
  };

  struct Plan {
    unsigned top_height = 0;
    std::vector<size_t> buffer_buckets;
  };

  static size_t NodeCapacity(size_t pool_buckets, size_t pages,
                             unsigned height) {
    const size_t pool = pool_buckets * kBucketCapacity;
    const size_t s = pages * kBucketCapacity;  // at most 2^12
    return height > kMaxCoarseBits || (s << height) >= pool ? pool
                                                           : s << height;
  }

  // The first height at which a node's capacity is below the pool's, capped
  // at the root; 0 when no capacity ever binds (a pool of at most S slots).
  static unsigned DirectHeight(size_t pool_buckets, unsigned coarse_bits,
                               size_t pages) {
    const size_t pool = pool_buckets * kBucketCapacity;
    const size_t s = pages * kBucketCapacity;
    if (s >= pool) return 0;
    unsigned h = 0;
    while (h < coarse_bits && (s << (h + 1)) < pool) ++h;
    return h;
  }

  // Every pass with at most `max_pool` buckets and `max_coarse` bits fits:
  // its direct height is at most the top one, whose buffer holds the whole
  // pool; the left buffer of height h holds a copy of a height-(h+1) parent.
  static Plan PlanBuffers(size_t max_pool, unsigned max_coarse, size_t pages) {
    Plan plan;
    plan.top_height = DirectHeight(max_pool, max_coarse, pages);
    plan.buffer_buckets.push_back(max_pool);  // gather
    plan.buffer_buckets.push_back(max_pool);  // direct child
    for (unsigned h = 0; h < plan.top_height; ++h) {
      plan.buffer_buckets.push_back(
          NodeCapacity(max_pool, pages, h + 1) / kBucketCapacity);
    }
    return plan;
  }

  // A direct child and every split below it: one unit per internal node of
  // a forest with at most 2^D leaves, so at most 2^D units.
  static size_t MaxUnits(unsigned max_coarse) {
    return size_t{1} << max_coarse;
  }

  // The widest parent a split reads: a node at the top height, if any.
  static size_t SplitParentBuckets(const Plan& plan) {
    return plan.top_height == 0 ? 0 : plan.buffer_buckets.back();
  }

  // One compaction's work: the network over its parent -- ceil(log2 blocks)
  // cross levels plus the fused intra-block level, in the network's
  // block-pair touches -- plus two passes for a parent copy and a copy out.
  // The kernel makes neither copy and runs a tile's levels in registers, but
  // the cost model charges all of them as passes: its calibration constants
  // were fitted to this count, so piece prices, and the schedules cut from
  // them, stay consistent with it.
  static size_t UnitTouches(size_t parent_buckets) {
    unsigned levels = 1;
    while ((size_t{1} << (levels - 1)) < parent_buckets) ++levels;
    return parent_buckets * (levels + 2);
  }
  // A pair is charged its two compactions, so a pass's Touches() does not
  // depend on how its splits are grouped into units.
  static size_t UnitTouchesOf(const Shape& shape, size_t pages,
                              const Unit& unit) {
    return UnitTouches(ParentBuckets(shape, pages, unit)) *
           (unit.kind == kPair ? 2 : 1);
  }

  // A unit's parent: the gathered pool for a direct child, else a node one
  // height up, at its capacity.
  static size_t ParentBuckets(const Shape& shape, size_t pages,
                              const Unit& unit) {
    return unit.kind == kDirect
               ? shape.pool_buckets
               : NodeCapacity(shape.pool_buckets, pages, unit.height + 1u) /
                     kBucketCapacity;
  }

  // Configure bounds index_bits + coarse_bits below the word width, and a
  // node at `height` is below 2^(coarse_bits - height), so this cannot wrap.
  static bool Padding(const Shape& shape, unsigned height, size_t node) {
    return (node << (height + shape.index_bits)) >= shape.main_buckets;
  }

  void Push(const Unit& unit) {
    if (units_.size() == units_.capacity()) {
      throw std::logic_error("DFS residual: unit list outgrew its storage");
    }
    units_.push_back(unit);
  }

  // THE UNIT LIST, in order, through visit(unit): each live direct child,
  // then its splits in preorder.  Configure records it and PriceOf counts it,
  // so the two cannot disagree.
  template <class Visit>
  static void ForEachUnit(const Shape& shape, size_t pages, Visit&& visit) {
    const unsigned hd =
        DirectHeight(shape.pool_buckets, shape.coarse_bits, pages);
    const size_t direct = size_t{1} << (shape.coarse_bits - hd);
    for (size_t c = 0; c < direct; ++c) {
      if (Padding(shape, hd, c)) continue;
      visit(Unit{kDirect, static_cast<uint8_t>(hd), kGather, kTopBuffer,
                 static_cast<uint32_t>(c)});
      if (hd > 0) Descend(shape, hd, c, kTopBuffer, visit);
    }
  }

  // Preorder below a node of height h >= 1 held in buffer `at`: split it,
  // then the left subtree, then the right one, which waits in `at`.
  template <class Visit>
  static void Descend(const Shape& shape, unsigned h, size_t node, uint8_t at,
                      Visit&& visit) {
    const unsigned child = h - 1;
    const size_t left = 2 * node, right = 2 * node + 1;
    const bool right_live = !Padding(shape, child, right);
    visit(Unit{right_live ? kPair : kLeft, static_cast<uint8_t>(child), at,
               LeftBuffer(child), static_cast<uint32_t>(left)});
    if (child == 0) return;
    Descend(shape, child, left, LeftBuffer(child), visit);
    if (right_live) Descend(shape, child, right, at, visit);
  }

  TableView Buffer(uint8_t id, size_t buckets) {
    TableView v;
    v.layout = layout_;
    v.num_buckets = buckets;
    v.data = data_.get() + offsets_[id] * layout_.BucketBytes();
    v.masks = masks_.data() + offsets_[id];
    return v;
  }

  void RequireConfigured() const {
    if (!configured_) throw std::logic_error("DFS residual: not configured");
  }

  void ClearPaddingLeaves(TableView leaves) const {
    const size_t q = size_t{1} << shape_.coarse_bits;
    const size_t homes = size_t{1} << shape_.index_bits;
    const size_t live = (shape_.main_buckets + homes - 1) / homes;
    for (size_t g = 0; g < pages_; ++g) {
      for (size_t l = live; l < q; ++l) leaves.masks[g * q + l] = 0;
    }
  }

  // The lanes a unit selects from each parent block -- valid, and matching
  // the child's destination bits -- and the counts before each block.  The
  // bits are tested a tag byte at a time: one line per byte, its selected
  // bits compared with the child's.  A pair's right child takes the valid
  // lanes that fail its one-bit test, in the right arrays, and its count goes
  // to `right`.  The masks are secret, so the tag lines meet them only
  // through register-only compares.
  uint32_t Select(const Unit& u, TableView parent, uint32_t* right) {
    const unsigned first = shape_.index_bits + u.height;
    const unsigned end =
        first + (u.kind == kDirect ? shape_.coarse_bits - u.height : 1);
    const size_t value = u.kind == kDirect ? u.node : (u.node & 1);
    // At most kMaxCoarseBits bits, so at most three tag bytes.
    struct TagByte {
      size_t line;
      __m512i field, want;
    };
    TagByte bytes[3];
    unsigned n = 0;
    for (unsigned bit = first; bit < end; ++n) {
      const unsigned low = bit & 7;
      const unsigned take = std::min(8 - low, end - bit);
      const unsigned field = ((1u << take) - 1) << low;
      bytes[n].line = layout_.TagLine(bit) * kBucketCapacity;
      bytes[n].field = _mm512_set1_epi8(static_cast<char>(field));
      bytes[n].want = _mm512_set1_epi8(
          static_cast<char>(((value >> (bit - first)) << low) & field));
      bit += take;
    }
    const bool pair = u.kind == kPair;
    uint32_t base = 0, base_right = 0;
    for (size_t b = 0; b < parent.num_buckets; ++b) {
      const uint8_t* bucket = parent.Bucket(b);
      const uint64_t valid = parent.masks[b];
      uint64_t match = ~uint64_t{0};
      for (unsigned i = 0; i < n; ++i) {
        const __m512i line = core::obliLoad512(bucket + bytes[i].line);
        match &= core::obliCmpEqMask8(_mm512_and_si512(line, bytes[i].field),
                                      bytes[i].want);
      }
      select_[b] = valid & match;
      prefix_[b] = base;
      base += static_cast<uint32_t>(_mm_popcnt_u64(select_[b]));
      if (pair) {
        select_right_[b] = valid & ~match;
        prefix_right_[b] = base_right;
        base_right += static_cast<uint32_t>(_mm_popcnt_u64(select_right_[b]));
      }
    }
    prefix_[parent.num_buckets] = base;
    if (pair) prefix_right_[parent.num_buckets] = base_right;
    *right = base_right;
    return base;
  }

  bool RunUnit(const Unit& u, TableView leaves) {
    const size_t parent_buckets = ParentBuckets(shape_, pages_, u);
    const TableView parent = Buffer(u.src, parent_buckets);
    const TableView work = Buffer(u.work, parent_buckets);
    const size_t bucket_bytes = layout_.BucketBytes();
    // Counted from the parent before any byte of it moves: a pair's right
    // child is compacted over its own parent.
    uint32_t count[2];
    count[0] = Select(u, parent, &count[1]);
    const size_t capacity = Capacity(u.height);
    const size_t child_buckets = capacity / kBucketCapacity;
    // A leaf is compacted straight into its pages, stacked one sub-table
    // apart; any other child into the front of its buffer: `work` for the
    // left one, its own parent for the right one.
    const size_t q = size_t{1} << shape_.coarse_bits;
    const bool leaf = u.height == 0;
    const size_t children = u.kind == kPair ? 2 : 1;
    const TableView home[2] = {work, parent};
    DfsCompactNetwork::Side sides[2];
    for (size_t c = 0; c < children; ++c) {
      sides[c] = {c == 0 ? prefix_.data() : prefix_right_.data(),
                  c == 0 ? select_.data() : select_right_.data(),
                  home[c].data,
                  leaf ? leaves.Bucket(u.node + c) : home[c].data,
                  leaf ? q * bucket_bytes : bucket_bytes};
    }
    DfsCompactNetwork(parent.data, layout_.EntryBytes(), parent_buckets,
                      child_buckets, sides, children)
        .Compact();
    for (size_t c = 0; c < children; ++c) {
      if (leaf) {
        // A pool smaller than a leaf's pages leaves the rest of it empty.
        for (size_t g = 0; g < pages_; ++g) {
          leaves.masks[g * q + u.node + c] =
              g < child_buckets
                  ? ~dfs_detail::LanesFrom(
                        int64_t(count[c]) - int64_t(g * kBucketCapacity))
                  : 0;
        }
      } else {
        for (size_t b = 0; b < child_buckets; ++b) {
          home[c].masks[b] = ~dfs_detail::LanesFrom(
              int64_t(count[c]) - int64_t(b * kBucketCapacity));
        }
      }
    }
    // A pair that overflows either child fails the pass.
    return count[0] <= capacity && (children == 1 || count[1] <= capacity);
  }

  Layout layout_;
  size_t max_pool_;
  unsigned max_coarse_;
  size_t pages_;
  unsigned top_ = 0;
  std::vector<size_t> buckets_, offsets_;
  Aligned64Ptr data_;
  std::vector<uint64_t> masks_;
  // One unit's selection: each parent block's selected lanes, and the counts
  // before each block (pool_buckets + 1); a pair's right child's in the right
  // arrays, sized for the widest split.
  std::vector<uint64_t> select_, select_right_;
  std::vector<uint32_t> prefix_, prefix_right_;
  std::vector<Unit> units_;
  Shape shape_;
  unsigned direct_height_ = 0;
  size_t touches_ = 0;
  size_t next_ = 0;
  bool configured_ = false, failed_ = false;
};

}  // namespace byteslice
}  // namespace microram
