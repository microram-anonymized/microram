#pragma once

// A SCALAR TREE-ORAM SIMULATOR over metadata alone: the read-path engine's
// plan (cpu_tree_read_path_eviction.hpp), for the stash measurement
// (src/oram/tree/DESIGN.md, "Stash size").
//
// The engine's plan is a function of the 16 metadata byte lines and the
// public leaf and of nothing else, so the stash tail can be measured without
// the transposition, the AVX-512 kernel, the layout or the payload.  This
// file is that measurement's model of the engine's shape: a binary tree of
// four-slot buckets, the top `fold` levels folded into the stash region, and
// ONE pass per access that reads the accessed path, takes the target out and
// evicts along the same path.
//
// WHAT IS MODELLED EXACTLY, because the tail depends on it:
//
//   * The working set's PRIORITY order: the path's lanes from the leaf level
//     up, a bucket's slots in order, then the stash lanes in index order.  A
//     destination takes the lowest-ranked eligible lane, so a path entry only
//     moves down and never into the stash.
//   * A stash entry the plan cannot place keeps its lane; every other stash
//     lane is free, and the accessed entry lands in the lowest free one.
//   * The target is not a candidate for the pass that lifts it out.
//
// The stash lane array here is unbounded, where the engine's is `64 A` lanes
// and throws past `64 A - 1` kept entries: letting the stash grow is what
// lets a row whose tail does not fit still be measured instead of stopping at
// its first overflow.  `tests/oram/cpu_tree_read_path_oram_test.cpp` checks
// the whole of the above against `CpuReadPathOram` itself, slot for slot and
// stash lane for stash lane.
//
// Positions are 32-bit, so `leaf_bits <= 32`; the engine allows 36.  Block
// ids are `int32_t`, so a tree holds at most 2^31 entries (`kMaxEntries`).

#include <immintrin.h>
#include <sys/mman.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <new>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace microram {
namespace tree {
namespace stash_sim {

// A tree slot, or a stash lane: which block it holds and where that block's
// path is.  The position rides in the slot because the pass needs it for every
// lane it loads and a separate block -> position lookup would be a random
// access per lane.  `block < 0` is a dummy (the engine's clear REAL BIT).
struct Slot {
  int32_t block = -1;
  uint32_t pos = 0;
};

// The most entries a tree can hold: ids 0 .. 2^31 - 1 fit `Slot::block`, and
// a larger id would turn negative, which is a dummy.  `TreeSim` refuses more.
constexpr uint64_t kMaxEntries = uint64_t{1} << 31;

// A fixed-size array in transparent huge pages where the kernel grants them.
// Under THP's `madvise` mode only a region that asks is backed by 2 MiB pages,
// and the tree and the position map are tens of MiB read at random: on 4 KiB
// pages nearly every deep bucket is a TLB miss as well as a cache miss.
template <typename T>
class HugeArray {
 public:
  static constexpr size_t kHuge = size_t{2} << 20;
  HugeArray() = default;
  HugeArray(size_t n, const T& fill) : n_(n) {
    if (n_ == 0) return;
    const size_t bytes = (n_ * sizeof(T) + kHuge - 1) / kHuge * kHuge;
    p_ = static_cast<T*>(std::aligned_alloc(kHuge, bytes));
    if (p_ == nullptr) throw std::bad_alloc();
    madvise(p_, bytes, MADV_HUGEPAGE);  // a hint: failure leaves 4 KiB pages
    for (size_t i = 0; i < n_; ++i) p_[i] = fill;
  }
  HugeArray(const HugeArray&) = delete;
  HugeArray(HugeArray&& o) noexcept : p_(o.p_), n_(o.n_) { o.p_ = nullptr; o.n_ = 0; }
  HugeArray& operator=(HugeArray o) noexcept {
    std::swap(p_, o.p_);
    std::swap(n_, o.n_);
    return *this;
  }
  ~HugeArray() { std::free(p_); }
  T& operator[](size_t i) { return p_[i]; }
  const T& operator[](size_t i) const { return p_[i]; }

 private:
  T* p_ = nullptr;
  size_t n_ = 0;
};

// Slots per bucket, and the most path levels the engine's two path
// registers hold.
constexpr unsigned kZ = 4;
constexpr unsigned kMaxPathLevels = 32;
constexpr unsigned kMaxPathLanes = kZ * kMaxPathLevels;

// The shape of the tree: levels 0 (the root) .. leaf_bits, level j holding
// `2^j` buckets of four slots, levels `fold..leaf_bits` stored and levels
// `0..fold-1` folded into the stash region of `64 A` lanes.
struct Geometry {
  unsigned fold = 1;
  unsigned leaf_bits = 0;        // lambda, one level per leaf bit
  unsigned path_levels = 0;      // P = leaf_bits - fold + 1
  unsigned stash_registers = 3;  // A
  std::vector<size_t> level_base;  // slot index of level j slot 0, j = fold..
  size_t stored_slots = 0;  // slots in levels fold..leaf_bits
  size_t all_slots = 0;     // slots in levels 0..leaf_bits, the folded ones included

  unsigned path_lanes() const { return kZ * path_levels; }
  // The engine's path registers: one while the path fits 64 lanes.
  unsigned path_registers() const { return path_lanes() <= 64 ? 1u : 2u; }
  // The kept stash entries the engine has lanes for: all but the one the
  // accessed entry lands in.
  unsigned leftover_lanes() const { return 64u * stash_registers - 1u; }
  // Slots per entry: the whole tree plus the stash region, as
  // `TreeGeometry::slots_per_entry` counts it.
  double slots_per_entry(uint64_t entries) const {
    return static_cast<double>(all_slots + 64u * stash_registers) /
           static_cast<double>(entries);
  }
  double load(uint64_t entries) const { return 1.0 / slots_per_entry(entries); }
};

inline Geometry MakeGeometry(unsigned leaf_bits, unsigned fold,
                             unsigned stash_registers) {
  Geometry g;
  g.fold = fold;
  g.leaf_bits = leaf_bits;
  g.stash_registers = stash_registers;
  if (leaf_bits > 32) throw std::invalid_argument("leaf_bits must be <= 32");
  if (fold == 0 || fold > leaf_bits) {
    throw std::invalid_argument("fold must be in [1, leaf_bits]");
  }
  if (stash_registers == 0) {
    throw std::invalid_argument("stash_registers must be nonzero");
  }
  g.path_levels = leaf_bits - fold + 1;
  if (g.path_levels > kMaxPathLevels) {
    throw std::invalid_argument("the path exceeds the engine's two path registers");
  }
  g.level_base.assign(leaf_bits + 1, 0);
  size_t base = 0;
  for (unsigned j = fold; j <= leaf_bits; ++j) {
    g.level_base[j] = base;
    base += size_t{kZ} << j;
  }
  g.stored_slots = base;
  g.all_slots = kZ * ((size_t{2} << leaf_bits) - 1);
  return g;
}

struct OpResult {
  unsigned leftovers = 0;        // the per-access failure quantity
  unsigned occupancy_after = 0;  // stash-region occupancy
};

inline uint64_t SimSplitMix64(uint64_t& state) {
  uint64_t z = (state += 0x9E3779B97F4A7C15ull);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
  return z ^ (z >> 31);
}

// The output `k` draws from now (k >= 1), without advancing the state.
inline uint64_t SimSplitMix64Peek(uint64_t state, uint64_t k) {
  state += (k - 1) * 0x9E3779B97F4A7C15ull;
  return SimSplitMix64(state);
}

// Thrown when the stash grows past `kStashLimit`: the row has diverged and
// there is no tail to fit.
struct SimDivergedError : std::runtime_error {
  explicit SimDivergedError(const std::string& what) : std::runtime_error(what) {}
};

class TreeSim {
 public:
  // The stash is unbounded so a row that does not fit its lanes still yields
  // a distribution; this is where "does not fit" becomes "has diverged".
  static constexpr unsigned kStashLimit = 4096;

  TreeSim(Geometry geometry, uint64_t entries, uint64_t seed)
      : g_(std::move(geometry)),
        rng_(seed * 0x9E3779B97F4A7C15ull + 0x2545F4914F6CDD1Dull) {
    if (entries > kMaxEntries) {
      throw std::invalid_argument(std::to_string(entries) +
                                  " entries: block ids are int32_t, so a tree "
                                  "holds at most 2^31");
    }
    slots_ = HugeArray<Slot>(g_.stored_slots, Slot{});
    pos_ = HugeArray<uint32_t>(entries, 0);
    stash_.assign(kStashLimit + 64 + 8, Slot{});
    lanes_.resize(kStashLimit + kMaxPathLanes + 8);
    depth_words_.assign(static_cast<size_t>(g_.leaf_bits + 1) * kMaxWords, 0);
    // The path's per-level constants, indexed by path level `i = j - fold`,
    // so a pass does no per-level arithmetic beyond its leaf's shift.
    np_ = g_.path_lanes();
    prefetch_from_ = g_.path_levels;
    for (unsigned i = 0; i < g_.path_levels; ++i) {
      const unsigned j = g_.fold + i;
      p_base_[i] = g_.level_base[j];
      p_shift_[i] = static_cast<uint8_t>(g_.leaf_bits - j);
      // The levels too big to stay in L1: those are the ones worth a
      // prefetch ahead of the access that needs them.
      const size_t bytes = (size_t{kZ} << j) * sizeof(Slot);
      if (bytes > (size_t{32} << 10) && prefetch_from_ == g_.path_levels) {
        prefetch_from_ = i;
      }
    }
  }

  const Geometry& geometry() const { return g_; }
  // The SplitMix64 state itself, not a draw (`SimSplitMix64(rng())` draws).
  uint64_t& rng() { return rng_; }
  // Real entries in the stash region.
  unsigned StashOccupancy() const {
    unsigned n = 0;
    for (unsigned i = 0; i < stash_n_; ++i) n += stash_[i].block >= 0;
    return n;
  }

  uint64_t RandomLeaf() { return SimSplitMix64(rng_) & ((uint64_t{1} << g_.leaf_bits) - 1); }

  // The operations, mirroring `CpuTreeMap`: one tree access each.
  OpResult ReadBlock(uint64_t block) {
    const uint32_t fresh = static_cast<uint32_t>(RandomLeaf());
    OpResult r = Access(pos_[block], static_cast<int32_t>(block),
                        static_cast<int32_t>(block), fresh);
    pos_[block] = fresh;
    return r;
  }
  // An access that looks for a key the tree does not hold: a random path and
  // nothing found (`CpuTreeMap`'s `random_path`).
  OpResult MissBlock() { return Access(RandomLeaf(), -1, -1, 0); }
  OpResult Insert(uint64_t block) {
    const uint32_t fresh = static_cast<uint32_t>(RandomLeaf());
    OpResult r = Access(RandomLeaf(), -1, static_cast<int32_t>(block), fresh);
    pos_[block] = fresh;
    return r;
  }
  OpResult EraseBlock(uint64_t block) {
    return Access(pos_[block], static_cast<int32_t>(block), -1, 0);
  }

  // The working set as it stands, for the equivalence test: the stash region's
  // lanes up to the last live one, and the tree's slots.
  unsigned StashLanes() const { return stash_n_; }
  const Slot& StashLane(unsigned i) const { return stash_[i]; }
  const Slot& TreeSlot(unsigned level, uint64_t bucket, unsigned t) const {
    return slots_[g_.level_base[level] + bucket * kZ + t];
  }

  // A HINT for an operation some way ahead that will read `block`: request
  // its path, the levels of it that do not stay in L1.  The block's position
  // only changes when it is read, so it is known in advance, and fetching it
  // early is what overlaps the misses of successive operations instead of
  // paying them one operation at a time.  It changes no state, so it changes
  // no result.
  void PrefetchOp(uint64_t block) const { PrefetchPath(pos_[block]); }
  void PrefetchPath(uint64_t leaf) const {
    for (unsigned i = prefetch_from_; i < g_.path_levels; ++i) {
      _mm_prefetch(reinterpret_cast<const char*>(
                       &slots_[p_base_[i] + static_cast<size_t>(leaf >> p_shift_[i]) * kZ]),
                   _MM_HINT_T0);
    }
  }
  // The position's cache line alone, for a lookahead long enough that the
  // position itself would miss (a uniform workload's next blocks).
  void PrefetchPosition(uint64_t block) const {
    _mm_prefetch(reinterpret_cast<const char*>(&pos_[block]), _MM_HINT_T0);
  }

  // ONE OPERATION, one pass.  `target` is the block to take out (-1: an
  // access that finds nothing), `land` what lands in the stash afterwards
  // (-1: nothing, i.e. a miss or an erase).  The caller owns the position
  // bookkeeping; `ReadBlock` and friends are the wrappers that do it.
  //
  // The working set is gathered in PRIORITY order, so taking each bucket's
  // lowest eligible lanes is Glover's rule for this convex matching: the
  // entry whose current level is deepest goes first and a stash entry last.
  // That places as many entries as any plan can, keeps every path entry on
  // the path at its own level or deeper, and leaves the stash's leftovers in
  // their lanes.  The stash keeps its holes, because a lane's index is its
  // priority, and the accessed entry lands in the lowest one.  The count is
  // the unplaced stash entries, the landed one excluded.
  OpResult Access(uint64_t leaf, int32_t target, int32_t land,
                  uint32_t land_pos) {
    const unsigned S = stash_n_;
    const unsigned P = g_.path_levels;
    const unsigned nl = np_ + S;
    const unsigned nw = (nl + 63) >> 6;

    // 1. Gather: the path from the leaf level up, then the stash.
    size_t path_base[kMaxPathLevels];
    for (unsigned i = 0; i < P; ++i) {
      path_base[i] = p_base_[i] + static_cast<size_t>(leaf >> p_shift_[i]) * kZ;
      _mm_prefetch(reinterpret_cast<const char*>(&slots_[path_base[i]]), _MM_HINT_T0);
    }
    Slot* const lanes = lanes_.data();
    unsigned r = 0;
    for (unsigned i = P; i-- > 0;) {
      std::memcpy(lanes + r, &slots_[path_base[i]], kZ * sizeof(Slot));
      r += kZ;
    }
    std::memcpy(lanes + np_, stash_.data(), S * sizeof(Slot));

    // 2. Valid, less the target's lane, which is excluded from the pool.
    uint64_t avail[kMaxWords];
    std::memset(avail, 0, nw * sizeof(uint64_t));
    for (unsigned l = 0; l < nl; ++l) {
      const int32_t b = lanes[l].block;
      const uint64_t real = static_cast<uint64_t>(b >= 0);
      const uint64_t is_target = static_cast<uint64_t>(b == target) & real;
      avail[l >> 6] |= (real & ~is_target) << (l & 63);
    }

    // 3. The deepest level each lane may occupy -- the leaf bits its
    // position shares with the path -- binned by level.
    uint64_t* dm = depth_words_.data();
    std::memset(dm, 0, static_cast<size_t>(g_.leaf_bits + 1) * nw * sizeof(uint64_t));
    for (unsigned w = 0; w < nw; ++w) {
      uint64_t bits = avail[w];
      while (bits) {
        const unsigned b = static_cast<unsigned>(_tzcnt_u64(bits));
        bits = _blsr_u64(bits);
        const uint64_t x = lanes[64 * w + b].pos ^ leaf;
        const unsigned bitlen = 64u - static_cast<unsigned>(_lzcnt_u64(x | 1)) -
                                static_cast<unsigned>(x == 0);
        const unsigned d = g_.leaf_bits - bitlen;
        dm[static_cast<size_t>(d) * nw + w] |= uint64_t{1} << b;
      }
    }

    // 4. The greedy, leaf first: each bucket takes the `Z` lowest-ranked
    // unplaced lanes that may reach it.
    uint64_t rem[kMaxWords], ge[kMaxWords];
    std::memcpy(rem, avail, nw * sizeof(uint64_t));
    std::memset(ge, 0, nw * sizeof(uint64_t));
    for (unsigned i = P; i-- > 0;) {
      const uint64_t* d = dm + static_cast<size_t>(g_.fold + i) * nw;
      Slot* dst = &slots_[path_base[i]];
      unsigned got = 0;
      for (unsigned w = 0; w < nw; ++w) {
        ge[w] |= d[w];
        uint64_t pool = rem[w] & ge[w];
        while (pool && got < kZ) {
          const unsigned b = static_cast<unsigned>(_tzcnt_u64(pool));
          pool = _blsr_u64(pool);
          rem[w] &= ~(uint64_t{1} << b);
          dst[got++] = lanes[64 * w + b];
        }
      }
      for (unsigned t = got; t < kZ; ++t) dst[t] = Slot{};
    }

    // 5. Every path entry was placed; a stash entry the plan left keeps its
    // lane, every other stash lane is free, and the accessed entry lands in
    // the lowest free one (the buffer has room past `S`).
    for (unsigned l = 0; l < np_; ++l) {
      if ((rem[l >> 6] >> (l & 63)) & 1) {
        throw std::logic_error("the plan left a path entry unplaced");
      }
    }
    unsigned count = 0;
    for (unsigned i = 0; i < S; ++i) {
      const unsigned l = np_ + i;
      const bool kept = (rem[l >> 6] >> (l & 63)) & 1;
      count += kept;
      if (!kept) stash_[i] = Slot{};
    }
    if (land >= 0) {
      unsigned h = 0;
      while (h < S && stash_[h].block >= 0) ++h;
      stash_[h] = Slot{land, land_pos};
      if (h == S) stash_n_ = S + 1;
    }
    while (stash_n_ > 0 && stash_[stash_n_ - 1].block < 0) --stash_n_;

    if (count >= kStashLimit) {
      throw SimDivergedError("the stash passed " + std::to_string(kStashLimit) +
                             " lanes: the row has diverged");
    }
    OpResult out;
    out.leftovers = count;
    out.occupancy_after = StashOccupancy();
    return out;
  }

 private:
  static constexpr unsigned kMaxWords =
      (kStashLimit + kMaxPathLanes + 63) / 64 + 1;

  Geometry g_;
  uint64_t rng_ = 0;
  HugeArray<Slot> slots_;
  // The stash region's lanes up to the last live one, `stash_n_` of them, in
  // a buffer sized for the most a pass can leave.
  std::vector<Slot> stash_;
  unsigned stash_n_ = 0;
  std::vector<Slot> lanes_;
  HugeArray<uint32_t> pos_;
  std::vector<uint64_t> depth_words_;
  // Per path level `i = j - fold`: level j's first slot and the shift that
  // takes a leaf to its level-j bucket.
  unsigned np_ = 0;
  unsigned prefetch_from_ = 0;
  size_t p_base_[kMaxPathLevels] = {};
  uint8_t p_shift_[kMaxPathLevels] = {};
};

}  // namespace stash_sim
}  // namespace tree
}  // namespace microram
