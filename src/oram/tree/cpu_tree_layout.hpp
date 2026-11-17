#pragma once

// Geometry and storage of the tree ORAM (src/oram/tree/DESIGN.md, "Geometry
// and the default rule" and "Storage formats"): a binary Path ORAM tree of
// four-slot buckets, one bucket per leaf, whose top `fold` levels are not
// stored but held in a byte-sliced stash region of `64 A` lanes.  One access
// works on the stash region and the path, which is one 64-lane register of
// at most 16 buckets or two of at most 32.
//
// Nothing here is oblivious or not; it is arithmetic on public quantities.
// Every address a path touches is a function of the leaf position alone.

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <algorithm>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

#include "src/core/mov_intrinsics.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"

namespace microram {
namespace tree {

using byteslice::Aligned64Ptr;
using byteslice::AllocateAligned64;

// Z, the bucket's slots.
inline constexpr unsigned kBucketSlots = 4;
// The path is at most two registers of 16 buckets.  The arrays indexed by
// path position are sized by it.
inline constexpr unsigned kMaxPathLevels = 32;
// THE ROOT'S FAN-OUT.  The stash region is the tree's root, and `fold` is
// how many levels above the first stored level it stands for, so the root
// has `2^fold` children.  Five is the deepest fold the stash measurement
// covers (DESIGN.md, "Stash size").
inline constexpr unsigned kMaxFold = 5;
// Levels of the tree itself, the folded ones included, as an array bound:
// `leaf_bits` reaches `fold + P - 1`.
inline constexpr unsigned kMaxTreeLevels = kMaxFold + kMaxPathLevels;
// The stash registers `A` an engine is built with (DESIGN.md, "Stash
// size").
inline constexpr unsigned kMinStashRegisters = 3;
inline constexpr unsigned kMaxStashRegisters = 4;

// Entry: uid (8) | position (8) | value.
inline constexpr size_t kUidBytes = 8;
inline constexpr size_t kPositionBytes = 8;
inline constexpr size_t kMetaBytes = kUidBytes + kPositionBytes;
inline constexpr size_t kUidOffset = 0;
inline constexpr size_t kPositionOffset = kUidBytes;

// THE REAL BIT: the top bit of the stored POSITION says whether the slot holds
// an entry.  It does not live in the uid, and the reason is that then the uid
// is free to be anything -- in particular the KEY, which is what lets the
// position map store the position alone, `ceil(leaf_bits / 8)` bytes, instead
// of a position and an eight-byte uid (cpu_tree_map.hpp's THE UID).  A
// uid-is-nonzero convention cannot allow that: 2^64 keys do not inject into
// the 2^64 - 1 nonzero uids, so one key would always have to be reserved.
//
// The position needs only `leaf_bits <= 36` bits, so bit 63 is free by a wide
// margin, and an all-zero slot is still a dummy -- an all-zero arena is still
// an empty tree.  Testing it is one VPMOVB2M on the top position line.
//
// Everything that XORs the stored position against a path must set this bit in
// the path too, or it will not cancel; `PlanReadPath` does.
inline constexpr uint64_t kRealPositionBit = uint64_t{1} << 63;
// The byte line the real bit lives on, and its mask within that line.
inline constexpr size_t kRealPositionLine = kPositionOffset + 7;

inline uint64_t EncodeStoredPosition(uint64_t leaf) {
  return leaf | kRealPositionBit;
}
inline bool StoredPositionIsReal(uint64_t stored) {
  return (stored & kRealPositionBit) != 0;
}
inline uint64_t StoredPositionLeaf(uint64_t stored) {
  return stored & ~kRealPositionBit;
}

// A stored bucket is a run of 64-byte CHUNKS; chunk t holds bytes
// 16 t .. 16 t + 15 of all four slots, interleaved: byte k of slot z at
// 4 k + z.  So a chunk is 16 entry bytes wide, and chunk 0 is exactly the
// metadata.
inline constexpr size_t kChunkBytes = 64;
inline constexpr size_t kChunkColumns = kChunkBytes / kBucketSlots;

// THE DEFAULT RULE (DESIGN.md, "Geometry and the default rule").  For a tree
// of `leaf_bits` leaf bits the fold is `leaf_bits - 15` while that is 2 to
// 5, which keeps the path at 16 buckets -- one register -- from 17 to 20
// leaf bits; shallower trees have a path of at most 16 buckets at fold 1,
// and deeper ones take fold 1 and a path of two registers, because fold 6
// would spend 252 of the stash's lanes on the folded levels.  The stash is
// three registers up to fold 4 and four at fold 5, the fewest that hold the
// measured requirement at a per-access overflow probability of 2^-96
// (DESIGN.md, "Stash size", which names the tools that measure it) -- and
// four at any fold from kWideStashLeafBits leaf bits, the depth that holds
// 2^27 entries at the default load: fold 1 fits the 191 lanes three
// registers leave at every power of two up to 2^26 and passes them at 2^27.
inline constexpr unsigned kWideStashLeafBits = 25;
inline constexpr unsigned DefaultFold(unsigned leaf_bits) {
  return leaf_bits >= 17 && leaf_bits <= 20 ? leaf_bits - 15 : 1u;
}
inline constexpr unsigned DefaultStashRegisters(unsigned fold,
                                                unsigned leaf_bits) {
  return fold <= 4 && leaf_bits < kWideStashLeafBits ? 3u : 4u;
}
// Fewer stash registers than the rule's for the tree are refused: they do
// not hold its measured requirement (fold 5's, and fold 1's at 2^27
// entries, exceed the 191 lanes three registers leave beside the accessed
// entry).
inline void RequireRuleStashRegisters(unsigned fold, unsigned leaf_bits,
                                      unsigned stash_registers) {
  const unsigned want = DefaultStashRegisters(fold, leaf_bits);
  if (stash_registers < want) {
    throw std::invalid_argument(
        "a tree of " + std::to_string(leaf_bits) + " leaf bits at fold " +
        std::to_string(fold) + " needs " + std::to_string(want) +
        " stash registers to hold its measured stash requirement "
        "(src/oram/tree/DESIGN.md, \"Stash size\"), not " +
        std::to_string(stash_registers));
  }
}
// The slots of the `fold` levels that are not stored, which an entry whose
// position reaches none of the stored levels holds in a stash lane.
inline constexpr unsigned FoldedSlots(unsigned fold) {
  return kBucketSlots * ((1u << fold) - 1u);
}

// THE SHAPE: the sizing inputs and the stash width.  The bucket and the
// branching are fixed (four slots, binary).
struct TreeShape {
  // The load `ForCapacity` sizes the tree for, i.e. `N / slots`, stash lanes
  // included.  0 is one half, the load the stash was measured at.
  double max_load = 0.0;

  // The most stash lanes the fold may spend (`TreeGeometry::folded_slots`),
  // out of the `64 A - 1` the stash leaves free for the accessed entry.  0
  // is whatever the fold built costs; a smaller value lowers the default
  // rule's fold to one it pays for and refuses an explicit fold that costs
  // more.  A sizing input like `max_load`: the stored layout does not depend
  // on it.
  unsigned max_folded_slots = 0;

  // A, the stash region's 64-lane registers: 3 or 4, and at least the
  // default rule's for the depth and fold built, or 0 for the rule's choice.
  // Stored layout.
  unsigned stash_registers = 0;
  unsigned stash_lanes() const { return 64u * stash_registers; }

  bool operator==(const TreeShape& o) const {
    return max_load == o.max_load && max_folded_slots == o.max_folded_slots &&
           stash_registers == o.stash_registers;
  }
  bool operator!=(const TreeShape& o) const { return !(*this == o); }
  // Whether two shapes describe the same STORED LAYOUT, which is all a
  // built engine depends on: the sizing inputs are spent by `ForCapacity`,
  // and a `stash_registers` of 0 on either side is the "choose it" request
  // that the geometry has already resolved.
  bool SameLayout(const TreeShape& o) const {
    return stash_registers == o.stash_registers || stash_registers == 0 ||
           o.stash_registers == 0;
  }
  double target_load() const { return max_load > 0.0 ? max_load : 0.5; }
  // The fold `ForCapacity` builds when asked for fold 0: the default rule's,
  // lowered to the deepest fold a caller's `max_folded_slots` pays for.
  unsigned default_fold(unsigned leaf_bits) const {
    unsigned fold = DefaultFold(leaf_bits);
    while (max_folded_slots != 0 && fold > 1 &&
           FoldedSlots(fold) > max_folded_slots) {
      --fold;
    }
    return fold;
  }
  // The fold's lane budget: the caller's, or what `fold` costs.  Never above
  // the stash lanes less the one the accessed entry lands in.
  unsigned folded_slot_budget(unsigned fold) const {
    const unsigned want =
        max_folded_slots != 0 ? max_folded_slots : FoldedSlots(fold);
    const unsigned spare = stash_lanes() - 1u;
    return want < spare ? want : spare;
  }
};

// Declared before the geometry and defined after it: `ForCapacity` validates
// the sizes of the geometry it is about to hand back, and those checks need
// the completed type.
struct TreeGeometry;
inline void ValidateGeometrySizes(const TreeGeometry& g);

struct TreeGeometry {
  unsigned leaf_bits = 0;      // 2^leaf_bits leaves
  unsigned fold = 1;           // top levels held in the stash region
  size_t value_bytes = 0;      // V
  size_t capacity_entries = 0;  // N, as requested
  // Halve the load, i.e. one more level of tree per unit.  The stash tail is
  // a function of the load, so this is the knob the stash measurement moves.
  unsigned leaf_scale = 0;
  TreeShape shape;
  // Levels 0 (the root) .. tree_levels, level j holding 2^j buckets: one
  // level per leaf bit, so `tree_levels == leaf_bits`.
  unsigned tree_levels = 0;
  // The planner's eligibility threshold per path position, FROM THE LEAF UP:
  // `path_match_bits[m]` is how many leading leaf bits a lane's position
  // must share with the path to be placeable in the bucket `m` levels above
  // the leaf, `leaf_bits - m`.
  uint8_t path_match_bits[kMaxPathLevels] = {};

  // The most leaf bits the level tables hold.  The path bound cuts in well
  // before this, but the tables must not be written past whatever a search
  // over `leaf_bits` tries.
  static constexpr unsigned max_leaf_bits() { return kMaxTreeLevels - 1; }

  // Fill `tree_levels` and `path_match_bits` from `leaf_bits` and `fold`.
  void DeriveShape() {
    if (leaf_bits > max_leaf_bits()) {
      throw std::length_error("leaf_bits exceeds the level tables");
    }
    tree_levels = leaf_bits;
    // `path_levels()` underflows while the tree is still too shallow for the
    // fold (ForCapacity deepens it until it is not), so the table is only
    // filled once there is a path.
    if (tree_levels >= fold) {
      for (unsigned m = 0; m < path_buckets() && m < kMaxPathLevels; ++m) {
        path_match_bits[m] = static_cast<uint8_t>(leaf_bits - m);
      }
    }
  }

  // THE FOLD'S COST IN STASH LANES: the slots of the levels that are NOT
  // stored.  An entry whose position reaches no stored level has no path
  // destination and lives in a stash lane, so this many of the lanes are
  // spoken for before the eviction's tail is considered.
  size_t folded_slots() const { return FoldedSlots(fold); }

  // Buckets at level `j`.
  static size_t buckets_at(unsigned j) { return size_t{1} << j; }

  // A SLICE OF THE ENTRY (DESIGN.md, "Parallel payload").  The plan of a
  // pass is a function of the 16 metadata byte lines and the public leaf
  // alone, so chunks 1..C-1 are independent of each other given that plan --
  // and a chunk range of EVERY bucket, together with the stash lines those
  // chunks carry, is a self-contained storage with exactly this layout and a
  // stride of 64 (chunk_count) instead of 64 C.  That is what lets the
  // payload move on other cores with nothing shared: the metadata plane is
  // the slice [0, 1), payload worker k owns a contiguous range further along,
  // and every byte of the arena has one owner.
  //
  // The default -- `chunk_count == 0` -- is the whole entry from
  // `chunk_begin`.
  unsigned chunk_begin = 0;
  unsigned chunk_count = 0;

  size_t entry_bytes() const { return kMetaBytes + value_bytes; }
  // C: chunks per WHOLE entry, whatever this geometry stores of it.
  size_t chunks() const {
    return (entry_bytes() + kChunkColumns - 1) / kChunkColumns;
  }
  // Chunks this geometry's arena actually holds per bucket.
  size_t stored_chunks() const {
    return chunk_count != 0 ? chunk_count : chunks() - chunk_begin;
  }
  // The byte lines this slice carries, as GLOBAL line indices: a line index
  // is an entry byte offset everywhere in the engine, slice or not, so that
  // `i < kMetaBytes` and `value_out[i - kMetaBytes]` mean the same thing on
  // every plane.
  size_t line_begin() const {
    return static_cast<size_t>(chunk_begin) * kChunkColumns;
  }
  size_t line_end() const {
    const size_t end =
        (static_cast<size_t>(chunk_begin) + stored_chunks()) * kChunkColumns;
    return end < entry_bytes() ? end : entry_bytes();
  }
  size_t stored_lines() const { return line_end() - line_begin(); }
  size_t bucket_stride() const { return stored_chunks() * kChunkBytes; }
  // This geometry with only chunks [begin, begin + count) of every bucket and
  // the stash lines they carry.  `count == 0` means to the end of the entry.
  TreeGeometry ForSlice(unsigned begin, unsigned count) const {
    TreeGeometry g = *this;
    g.chunk_begin = chunk_begin + begin;
    g.chunk_count = count;
    return g;
  }
  // Columns of the last chunk that are real entry bytes; the rest is padding.
  size_t last_chunk_columns() const {
    const size_t rem = entry_bytes() % kChunkColumns;
    return rem == 0 ? kChunkColumns : rem;
  }
  // P: the path's levels and buckets, `fold .. tree_levels`.
  unsigned path_levels() const { return tree_levels - fold + 1; }
  unsigned path_buckets() const { return path_levels(); }
  unsigned path_slots() const { return kBucketSlots * path_buckets(); }
  // Lanes an entry with no home on this path can occupy.
  unsigned stash_capacity() const { return shape.stash_lanes(); }
  size_t leaves() const { return size_t{1} << leaf_bits; }
  size_t capacity() const { return capacity_entries; }
  // Every slot of the tree, the folded levels included, and of the stash
  // region.
  size_t slots() const {
    return kBucketSlots * ((size_t{2} << tree_levels) - 1) + shape.stash_lanes();
  }
  double slots_per_entry() const {
    return static_cast<double>(slots()) / static_cast<double>(capacity_entries);
  }
  // Stored buckets, levels fold..tree_levels, level-major.  Level j's first
  // bucket is bucket `2^j - 2^fold`.
  size_t num_buckets() const {
    return (size_t{2} << tree_levels) - (size_t{1} << fold);
  }
  // THE PER-LEVEL SKEW.  Level `j`'s buckets start one cache line further on
  // than packing them would put them.  A schedule that visits the same stored
  // slot at every level (a fixed-leaf sweep) would otherwise put the P
  // addresses of one pass at exact multiples of a power-of-two stride, all in
  // one cache set; the skew separates them.  The read path's random paths do
  // not depend on it.  It costs 64 bytes per level, and every address still
  // depends only on the geometry and the leaf.
  static constexpr size_t kLevelSkewBytes = 64;
  // Byte offset of level `level`'s first bucket.
  size_t level_offset_bytes(unsigned level) const {
    return ((size_t{1} << level) - (size_t{1} << fold)) * bucket_stride() +
           static_cast<size_t>(level - fold) * kLevelSkewBytes;
  }
  size_t bucket_bytes_total() const {
    return num_buckets() * bucket_stride() +
           static_cast<size_t>(path_levels()) * kLevelSkewBytes;
  }
  size_t stash_bytes() const { return shape.stash_lanes() * stored_lines(); }
  size_t arena_bytes() const { return bucket_bytes_total() + stash_bytes(); }

  // THE STORED ORDER OF A LEVEL IS BIT-REVERSED: bucket `b` of level `j` is
  // stored at slot `rev_j(b)`.  A reverse-lexicographic eviction sweep then
  // visits each level linearly.  A uniformly random path is uniform under
  // either order, so the read path needs neither property, and its addresses
  // stay a function of the leaf alone.
  //
  // It costs one bit reversal per pass and no arithmetic per level, because
  // the reversals nest: with `rev = revbits_leaf_bits(position)`, level `j`'s
  // slot is the LOW `j` bits of `rev`.  Derivation: bit `k` of `rev` is bit
  // `leaf_bits - 1 - k` of `position`, and `rev_j(position >> (leaf_bits-j))`
  // has bit `k` equal to bit `leaf_bits - 1 - k` of `position` as well.
  static uint64_t ReverseBits64(uint64_t v) {
    v = ((v >> 1) & 0x5555555555555555ull) | ((v & 0x5555555555555555ull) << 1);
    v = ((v >> 2) & 0x3333333333333333ull) | ((v & 0x3333333333333333ull) << 2);
    v = ((v >> 4) & 0x0F0F0F0F0F0F0F0Full) | ((v & 0x0F0F0F0F0F0F0F0Full) << 4);
    return __builtin_bswap64(v);
  }
  // `position` with its `leaf_bits` significant bits reversed.  Every level's
  // slot is a mask of this, so a pass computes it once.
  uint64_t reverse_position(uint64_t position) const {
    return ReverseBits64(position) >> (64 - leaf_bits);
  }
  // Slot of the bucket at `level`, from the reversed leaf: the low `level`
  // bits.  The natural order's slot is the top `level` bits of the leaf.
  static uint64_t slot_rev(unsigned level, uint64_t rev) {
    return rev & ((uint64_t{1} << level) - 1);
  }
  // Where bucket `bucket` of level `level` is STORED.  Tests and reference
  // scans walk the tree by natural index and need this to find the bytes.
  uint64_t stored_slot(unsigned level, uint64_t bucket) const {
    if (level == 0) return 0;
    const uint64_t position = bucket << (leaf_bits - level);
    return slot_rev(level, reverse_position(position));
  }
  // Byte offset of the bucket at `level` on the path whose reversed leaf is
  // `rev` (bit-reversed order) or whose leaf is `position` (natural order).
  size_t bucket_offset_rev(unsigned level, uint64_t rev) const {
    return level_offset_bytes(level) +
           static_cast<size_t>(slot_rev(level, rev)) * bucket_stride();
  }
  size_t bucket_offset(unsigned level, uint64_t position) const {
    return bucket_offset_rev(level, reverse_position(position));
  }

  // The smallest geometry holding `requested` entries at the shape's load.
  //
  // THE LOAD IS THE CONTRACT, and `leaf_bits` is what is solved for: the
  // tree is deepened until `slots() >= capacity / load`, where the load is
  // the shape's (TreeShape::target_load) halved once per unit of
  // `leaf_scale` and `slots()` counts the stash lanes.  At the default load
  // that is about `log2 N - 2` leaf bits.
  //
  // `fold` 0 and `stash_registers` 0 ask for the default rule at each
  // candidate depth.  The stash lanes count toward the load and the rule's
  // stash width depends on the depth and the fold, so both are set for a
  // candidate before its slots are counted.
  static TreeGeometry ForCapacity(size_t requested, unsigned fold,
                                  size_t value_bytes,
                                  unsigned leaf_scale = 0,
                                  TreeShape shape = {}) {
    if (requested == 0) throw std::invalid_argument("capacity must be nonzero");
    if (value_bytes == 0) throw std::invalid_argument("value_bytes must be nonzero");
    // `kMetaBytes + value_bytes` wraps, and a wrapped entry width answers
    // every later question with a plausible small number instead of an
    // error (ValidateGeometrySizes).
    if (value_bytes > SIZE_MAX - kMetaBytes) {
      throw std::length_error(
          "value_bytes is too large: the entry's 16 metadata bytes do not fit "
          "beside it");
    }
    if (fold > kMaxFold) {
      throw std::invalid_argument("fold must be in [0, " +
                                  std::to_string(kMaxFold) + "]");
    }
    if (shape.stash_registers != 0 &&
        (shape.stash_registers < kMinStashRegisters ||
         shape.stash_registers > kMaxStashRegisters)) {
      throw std::invalid_argument("stash_registers must be 0, 3 or 4");
    }
    if (shape.max_folded_slots > 64 * kMaxStashRegisters - 1) {
      throw std::invalid_argument(
          "max_folded_slots must be at most the stash lanes less one");
    }
    if (leaf_scale > 4) throw std::invalid_argument("leaf_scale must be <= 4");
    if (shape.max_load != 0.0 &&
        !(shape.max_load > 0.0 && shape.max_load < 1.0)) {
      throw std::invalid_argument("max_load must be zero or in (0, 1)");
    }

    const double target =
        shape.target_load() / static_cast<double>(size_t{1} << leaf_scale);
    TreeGeometry t;
    t.value_bytes = value_bytes;
    t.leaf_scale = leaf_scale;
    t.capacity_entries = requested;
    t.shape = shape;
    for (unsigned bits = 1;; ++bits) {
      if (bits > max_leaf_bits()) {
        throw std::length_error("capacity is too large");
      }
      t.leaf_bits = bits;
      t.fold = fold != 0 ? fold : shape.default_fold(bits);
      t.shape.stash_registers = shape.stash_registers != 0
                                    ? shape.stash_registers
                                    : DefaultStashRegisters(t.fold, bits);
      t.DeriveShape();
      if (t.tree_levels < t.fold) continue;  // no stored level yet
      if (static_cast<double>(t.slots()) * target >=
          static_cast<double>(requested)) {
        break;
      }
    }
    RequireRuleStashRegisters(t.fold, t.leaf_bits, t.shape.stash_registers);
    if (t.shape.max_folded_slots > t.shape.stash_lanes() - 1u) {
      throw std::invalid_argument(
          "max_folded_slots must be at most the stash lanes less one");
    }
    if (t.folded_slots() > t.shape.folded_slot_budget(t.fold)) {
      throw std::invalid_argument(
          "this fold would spend " + std::to_string(t.folded_slots()) +
          " stash lanes, past the " +
          std::to_string(t.shape.folded_slot_budget(t.fold)) +
          " its budget leaves: lower `fold` or raise `max_folded_slots`");
    }
    if (t.path_buckets() > kMaxPathLevels) {
      throw std::length_error(
          "capacity needs a path of " + std::to_string(t.path_buckets()) +
          " buckets, more than the working set's " +
          std::to_string(kMaxPathLevels) +
          ": raise `fold` or lower the capacity");
    }
    ValidateGeometrySizes(t);
    return t;
  }
};

// CHECKED SIZE ARITHMETIC.  A geometry is arithmetic on public quantities,
// but the engines take one from a caller rather than a capacity, and every
// step of the arena's size wraps rather than saturating: `value_bytes =
// SIZE_MAX - 15` made `entry_bytes()` zero, `chunks()` zero, `bucket_stride()`
// zero and a 64-byte arena, all accepted.  So the chain is re-derived once
// with a check at each step, BEFORE anything is allocated, rather than
// trusted where it is used.
inline size_t CheckedAddSize(size_t a, size_t b, const char* what) {
  if (a > SIZE_MAX - b) {
    throw std::length_error(std::string("tree geometry overflows: ") + what);
  }
  return a + b;
}
inline size_t CheckedMulSize(size_t a, size_t b, const char* what) {
  if (a != 0 && b > SIZE_MAX / a) {
    throw std::length_error(std::string("tree geometry overflows: ") + what);
  }
  return a * b;
}

// Every size `TreeStorage::Create` derives, recomputed with a check at each
// step, plus the consistency of a slice's chunk range with the entry it
// slices.  `ValidateWorkingSet` must have passed first: `path_levels()`
// underflows on a geometry shallower than its fold.
inline void ValidateGeometrySizes(const TreeGeometry& g) {
  if (g.value_bytes == 0) {
    throw std::invalid_argument("value_bytes must be nonzero");
  }
  const size_t entry = CheckedAddSize(kMetaBytes, g.value_bytes,
                                      "the entry's metadata plus its value");
  const size_t chunks = (entry - 1) / kChunkColumns + 1;  // entry > 0
  // `chunk_begin` and `chunk_count` are `unsigned`, and so is every slice
  // count derived from them (SliceLayout).
  if (chunks > static_cast<size_t>(~0u)) {
    throw std::length_error("tree geometry overflows: chunks per entry");
  }
  if (static_cast<size_t>(g.chunk_begin) > chunks ||
      CheckedAddSize(g.chunk_begin, g.chunk_count, "the slice's chunks") >
          chunks) {
    throw std::invalid_argument("the slice names chunks the entry does not have");
  }
  const size_t stored =
      g.chunk_count != 0 ? g.chunk_count : chunks - g.chunk_begin;
  const size_t stride = CheckedMulSize(stored, kChunkBytes, "the bucket stride");
  size_t buckets = 0;
  for (unsigned j = g.fold; j <= g.tree_levels; ++j) {
    if (j >= 64) {
      throw std::length_error("tree geometry overflows: a level's buckets");
    }
    buckets = CheckedAddSize(buckets, size_t{1} << j, "the tree's buckets");
  }
  const size_t bucket_bytes = CheckedAddSize(
      CheckedMulSize(buckets, stride, "the stored buckets"),
      CheckedMulSize(g.path_levels(), TreeGeometry::kLevelSkewBytes,
                     "the per-level skew"),
      "the bucket region");
  const size_t line_end_raw = CheckedMulSize(
      CheckedAddSize(g.chunk_begin, stored, "the slice's last chunk"),
      kChunkColumns, "the slice's last line");
  const size_t line_end = line_end_raw < entry ? line_end_raw : entry;
  const size_t stash = CheckedMulSize(
      g.shape.stash_lanes(), line_end - g.line_begin(), "the stash region");
  (void)CheckedAddSize(bucket_bytes, stash, "the arena");
}

// THE WORKING SET'S BOUNDS, which the engines index fixed arrays by.
// `ForCapacity` never returns a geometry past them, but the engines take a
// geometry rather than a capacity, so the bounds are checked where they are
// relied on: the per-position bucket and mask arrays are sized by
// kMaxPathLevels and the planner's words by kMaxStashRegisters, and a
// hand-built geometry past either would write off the end of them.
inline void ValidateWorkingSet(const TreeGeometry& g) {
  if (g.fold == 0 || g.fold > kMaxFold || g.tree_levels >= kMaxTreeLevels) {
    throw std::invalid_argument("invalid tree depth or fold");
  }
  if (g.tree_levels < g.fold) {
    throw std::invalid_argument("the tree has no stored level: fold exceeds its depth");
  }
  if (g.shape.stash_registers < kMinStashRegisters ||
      g.shape.stash_registers > kMaxStashRegisters) {
    throw std::invalid_argument("a built geometry has 3 or 4 stash registers");
  }
  if (g.path_buckets() > kMaxPathLevels) {
    throw std::invalid_argument(
        "the path has " + std::to_string(g.path_buckets()) +
        " buckets, more than the engine's " + std::to_string(kMaxPathLevels) +
        ": raise `fold` or lower the capacity");
  }
  if (g.leaf_bits > TreeGeometry::max_leaf_bits()) {
    throw std::invalid_argument("leaf_bits exceeds the level tables");
  }
}

// The whole geometry boundary: the working set, then every size the arena
// derives.  The engine runs this before it allocates or derives a layout
// (cpu_tree_read_path_oram.hpp's ValidateReadPathConfiguration).
inline void ValidateGeometry(const TreeGeometry& g) {
  ValidateWorkingSet(g);
  // Addressing and eviction use different derived quantities.  Requiring the
  // planner's table to describe the declared depth prevents an in-bounds but
  // inconsistent table from routing an entry to a bucket off its path.
  TreeGeometry derived = g;
  derived.DeriveShape();
  if (g.tree_levels != derived.tree_levels) {
    throw std::invalid_argument("tree depth disagrees with the leaf width");
  }
  for (unsigned j = 0; j < g.path_buckets(); ++j) {
    if (g.path_match_bits[j] != derived.path_match_bits[j]) {
      throw std::invalid_argument("tree path tables disagree with the shape");
    }
  }
  ValidateGeometrySizes(g);
}

// The buckets and a byte-sliced stash region of E lines, both
// zero-initialized: a slot with the real bit clear is a dummy
// (kRealPositionBit above), so an all-zero tree is an empty tree.
struct TreeStorage {
  TreeGeometry geometry;
  Aligned64Ptr buckets;
  Aligned64Ptr stash;
  // The stash allocation and the GLOBAL line index its first line carries;
  // see Rebase().  Set by Create and must be re-derived after a move.
  uint8_t* stash_lines = nullptr;
  size_t stash_line0 = 0;
  // One stash line: byte i of every stash lane, `64 stash_registers` of
  // them, register `a`'s at `64 a`.
  size_t stash_line_bytes = 0;

  static TreeStorage Create(const TreeGeometry& g) {
    TreeStorage s;
    s.geometry = g;
    s.buckets = AllocateAligned64(g.bucket_bytes_total());
    std::memset(s.buckets.get(), 0, g.bucket_bytes_total());
    s.stash = AllocateAligned64(g.stash_bytes());
    std::memset(s.stash.get(), 0, g.stash_bytes());
    s.Rebase();
    return s;
  }

  // Byte-sliced regions are addressed by the GLOBAL line index even on a
  // slice, so that `i < kMetaBytes` and `value_out[i - kMetaBytes]` mean the
  // same on every plane (TreeGeometry's A SLICE OF THE ENTRY).
  //
  // THE BIAS IS ON THE INDEX, NOT THE POINTER.  `stash.get() - line_begin()
  // * 64` would be a pointer BEFORE the allocation: forming it is undefined
  // even where it is never dereferenced.  Subtracting the first line instead
  // is loop-invariant in every caller, so the kernel pays nothing for it.
  void Rebase() {
    stash_lines = stash.get();
    stash_line0 = geometry.line_begin();
    stash_line_bytes = geometry.shape.stash_lanes();
  }

  // What was actually allocated.
  size_t arena_bytes() const { return geometry.arena_bytes(); }

  // Buckets are addressed by BYTE OFFSET, not by a flat index: the level bases
  // carry a skew (TreeGeometry::kLevelSkewBytes) so they are not a uniform
  // stride apart.
  uint8_t* BucketAt(size_t byte_offset) { return buckets.get() + byte_offset; }
  const uint8_t* BucketAt(size_t byte_offset) const {
    return buckets.get() + byte_offset;
  }
  // Byte line i of the stash region: byte i of every stash lane.  `i` is a
  // GLOBAL line index -- an entry byte offset -- so on a slice it runs over
  // [line_begin(), line_end()) rather than from zero.
  uint8_t* StashLine(size_t i) {
    return stash_lines + (i - stash_line0) * stash_line_bytes;
  }
  const uint8_t* StashLine(size_t i) const {
    return stash_lines + (i - stash_line0) * stash_line_bytes;
  }
};

// ---------------------------------------------------------------------------
// Path addressing
// ---------------------------------------------------------------------------
//
// Precomputed per level so one path address is a mask and a multiply-add.
// The bases carry the slice's own stride and level skew, so a plane addresses
// its arena exactly as the whole-entry engine addresses its own.
struct PathAddressing {
  uint8_t* level_base[kMaxPathLevels] = {};
  uint64_t slot_mask[kMaxPathLevels] = {};
  size_t stride = 0;
  unsigned levels = 0;
  unsigned leaf_bits = 0;

  void Init(TreeStorage& storage) {
    const TreeGeometry& g = storage.geometry;
    levels = g.path_buckets();
    leaf_bits = g.leaf_bits;
    stride = g.bucket_stride();
    for (unsigned i = 0; i < levels; ++i) {
      const unsigned level = g.fold + i;
      level_base[i] = storage.BucketAt(g.level_offset_bytes(level));
      slot_mask[i] = (uint64_t{1} << level) - 1;
    }
  }

  // The P bucket pointers of one path, ROOT FIRST: one bit reversal and then
  // a mask per level.
  INLINE void Buckets(uint64_t position, uint8_t** out) const {
    const uint64_t rev = TreeGeometry::ReverseBits64(position) >> (64 - leaf_bits);
    for (unsigned i = 0; i < levels; ++i) {
      out[i] = level_base[i] + (rev & slot_mask[i]) * stride;
    }
  }
};

// ---------------------------------------------------------------------------
// Planes
// ---------------------------------------------------------------------------
//
// The metadata plane owns chunk 0.  The remaining chunks divide into exactly
// the selected number of contiguous payload planes by quotient and
// remainder, so rounding does not silently reduce the selected thread
// count.  Clamped only when there are fewer chunks than workers; no empty
// plane runs.
struct SliceLayout {
  struct Range {
    unsigned begin = 0;
    unsigned count = 0;
  };
  std::vector<Range> ranges;

  static SliceLayout For(size_t chunks, unsigned workers) {
    SliceLayout s;
    if (chunks <= 1 || workers == 0) {
      s.ranges.push_back({0, static_cast<unsigned>(chunks)});
      return s;
    }
    const unsigned payload = static_cast<unsigned>(chunks - 1);
    if (workers > payload) workers = payload;
    s.ranges.push_back({0, 1});
    const unsigned per = payload / workers;
    const unsigned extra = payload % workers;
    unsigned at = 1;
    for (unsigned k = 0; k < workers && at < chunks; ++k) {
      const unsigned count = per + (k < extra ? 1 : 0);
      s.ranges.push_back({at, count});
      at += count;
    }
    return s;
  }
  unsigned payload_planes() const {
    return static_cast<unsigned>(ranges.size()) - 1;
  }
};

// THE BYTE-IDENTITY ORACLE, for tests: interleave the planes' arenas back
// into one of the whole-entry stride and compare with a whole-entry
// storage, the stash region included.  A mismatch is a plan, an order or an
// ownership bug; there is no tolerance in it.
inline bool SlicedStorageEquals(const std::vector<const TreeStorage*>& planes,
                                const TreeStorage& whole,
                                std::string* what = nullptr) {
  const TreeGeometry& g = whole.geometry;
  const size_t C = g.chunks();
  auto fail = [&](const std::string& msg) {
    if (what != nullptr) *what = msg;
    return false;
  };
  size_t covered = 0;
  for (const TreeStorage* sp : planes) {
    const TreeStorage& s = *sp;
    const TreeGeometry& sg = s.geometry;
    if (sg.chunk_begin + sg.stored_chunks() > C) return fail("slice past C");
    covered += sg.stored_chunks();
    // Buckets: chunk `chunk_begin + t` of the whole bucket is chunk t of the
    // slice's, and the level bases differ only in the stride and the skew.
    for (unsigned level = g.fold; level <= g.tree_levels; ++level) {
      const size_t base_whole = g.level_offset_bytes(level);
      const size_t base_slice = sg.level_offset_bytes(level);
      for (size_t b = 0; b < g.buckets_at(level); ++b) {
        const uint8_t* w = whole.BucketAt(base_whole + b * g.bucket_stride());
        const uint8_t* p = s.BucketAt(base_slice + b * sg.bucket_stride());
        if (std::memcmp(w + sg.chunk_begin * kChunkBytes, p,
                        sg.stored_chunks() * kChunkBytes) != 0) {
          return fail("bucket mismatch at level " + std::to_string(level) +
                      " bucket " + std::to_string(b));
        }
      }
    }
    for (size_t i = sg.line_begin(); i < sg.line_end(); ++i) {
      if (std::memcmp(whole.StashLine(i), s.StashLine(i),
                      whole.stash_line_bytes) != 0) {
        return fail("stash line " + std::to_string(i));
      }
    }
  }
  if (covered != C) return fail("the planes do not tile the entry");
  return true;
}

// Scalar accessors for tests and reference implementations -- one byte at a
// time through the interleaved layout.  Not for the access path.
//
// Byte `k` of slot `z` sits at `4 k + z` of the bucket, which holds across
// chunk boundaries: byte k is in chunk `k / 16` at column `k mod 16`, i.e.
// at `64 (k / 16) + 4 (k mod 16) + z`, and that is `4 k + z`.
inline uint8_t ReadBucketByte(const uint8_t* bucket, size_t slot, size_t byte) {
  return bucket[kBucketSlots * byte + slot];
}
inline uint64_t ReadBucketU64(const uint8_t* bucket, size_t slot, size_t offset) {
  uint64_t v = 0;
  for (size_t b = 0; b < 8; ++b) {
    v |= uint64_t{ReadBucketByte(bucket, slot, offset + b)} << (8 * b);
  }
  return v;
}
inline uint64_t ReadStashU64(const TreeStorage& s, size_t lane, size_t offset) {
  uint64_t v = 0;
  for (size_t b = 0; b < 8; ++b) {
    v |= uint64_t{s.StashLine(offset + b)[lane]} << (8 * b);
  }
  return v;
}

}  // namespace tree
}  // namespace microram
