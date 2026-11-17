#pragma once

// The tree ORAM's planner (src/oram/tree/DESIGN.md, "Read-path eviction"):
// from the metadata lines of a working set of one or two path registers and
// `A` stash registers to the routing the data pass applies to every byte
// line.  Four-slot buckets in a binary tree, so a path register holds 16
// buckets.
//
// THE RULE.  The path's lanes are stored LEAF FIRST -- path position `m` is
// the bucket `m` levels above the leaf (TreeGeometry::path_match_bits is in
// that order) -- and the priority is lane order over [path 0, path 1,
// stash 0, ..., stash A-1].  Step `m` takes the four lowest-numbered lanes
// that are eligible at position `m` and still unplaced.  Three properties
// follow, and the data pass and the overflow check rely on all of them:
//
//   * EVERY PATH ENTRY IS PLACED, AT ITS OWN POSITION OR DEEPER.  When step
//     `m` runs, every path entry from a position below `m` has been placed
//     (induction), so the unplaced entries that sat at position `m` -- at
//     most four, and eligible there -- are the four highest-priority
//     candidates.  So a path entry only moves down, never into the stash,
//     and destination register 1 (positions 16..31) never takes a source
//     from register 0.
//   * A STASH ENTRY THE PLAN CANNOT PLACE KEEPS ITS LANE.  There is no stash
//     permutation: the stash changes only where an entry left for the path,
//     where the target left, and in the one lane the accessed entry lands in.
//   * IT PLACES AS MANY ENTRIES AS ANY GREEDY.  Eligibility is nested -- an
//     entry eligible at a position is eligible at every shallower one -- so
//     any leaf-first greedy that fills each bucket with as many eligible
//     unplaced entries as it can is a maximum placement, whatever its
//     priority.  The simulator's in-place plan
//     (benchmarks/oram/cpu_tree_stash_sim.hpp) is this rule, which is what
//     ties the engine to the stash measurement.
//
// THE ACCESSED ENTRY is not a candidate (it is the target, and is excluded
// from the pool).  Its bytes are gathered from wherever it was, and the
// version the access leaves -- the found entry, or a created one, unless the
// access erases -- lands in the LOWEST free stash lane, where the next access
// treats it as any other stash entry.  The plan fails (overflow) when no
// stash lane is free for it: more than `64 A - 1` entries kept.
//
// Everything here is oblivious: the instruction and memory trace depend on
// the public geometry and the public pass kind (target or no target) alone.
// Lane sets are 64-bit words; every scalar step on one is PDEP / POPCNT /
// TZCNT / BLSI or a hardened select (core::obliSelectU64, which is inline
// asm and so cannot be turned back into a branch), every compare goes
// through the register-only forms of src/core/mov_intrinsics.hpp, and every
// store goes to a public address.  A ternary on a secret compiles to a
// branch under GCC at -O3; do not introduce one.

#include <immintrin.h>

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <type_traits>

#include "src/core/mov_intrinsics.hpp"
#include "src/oram/tree/cpu_tree_layout.hpp"

namespace microram {
namespace tree {

// The working set: up to two path registers -- 32 buckets of four -- and A
// stash registers.
inline constexpr unsigned kReadPathPathRegisters = 2;
inline constexpr unsigned kReadPathBucketsPerRegister = 16;
inline constexpr unsigned kReadPathMaxBuckets =
    kReadPathPathRegisters * kReadPathBucketsPerRegister;
static_assert(kReadPathMaxBuckets <= kMaxPathLevels,
              "the per-position tables are sized by kMaxPathLevels");

struct ReadPathEvictionInput {
  // Stash line 0: line `i` of stash register `a` is the 64 bytes at
  // `stash_meta + 64 A i + 64 a` (TreeStorage::StashLine).
  const uint8_t* stash_meta = nullptr;
  // Line `i` of path register `b` (leaf-first positions 16 b .. 16 b + 15)
  // is `path_meta[16 b + i]`: chunk 0 of the path, transposed tile by tile.
  const __m512i* path_meta = nullptr;
  uint64_t target_uid = 0;  // meaningful only when `has_target`
  bool has_target = false;
  // Whether the accessed entry stays: found or created, and not erased.
  // Both are public.
  bool create = false;
  bool erase = false;
  uint64_t path_position = 0;
  unsigned leaf_bits = 0;
  unsigned path_buckets = 0;  // P <= 32, positions 0..P-1 leaf first
  // Leaf bits an entry must share with the path to sit at position `m`
  // (TreeGeometry::path_match_bits).
  const uint8_t* level_match_bits = nullptr;
};

// THE PLAN.  The working set's W = B + A source words are, in priority order,
// [path 0, path 1, stash 0, ..., stash A - 1].  Destination path register
// `b` can only take from words b..W-1 -- register 1 takes nothing from
// register 0 (THE RULE's first property) -- and the gather can take from
// any word, as destination 0.  Each destination's words are grouped into
// consecutive PAIRS from its first word -- (b, b + 1), (b + 2, b + 3), ...
// -- so a lane's source is a pair and a seven-bit index into it, which is
// what VPERMT2B takes.  An odd count leaves the last word, W - 1, alone: it
// is a pair whose first table is the ACCUMULATOR, so its lanes' indices are
// 64 + lane (the second table), and the data pass folds it in with one
// merge-masked VPERMT2B.  A destination lane in no pair's mask has no source
// and comes out as a dummy, zero.  One type for every A, sized for the most
// (only ReadPathPairs(A, B, b) pairs and A stash words mean anything), so the
// payload workers' job slot has one plan type.
//
// THE PATH REGISTERS, B.  A path of at most 16 buckets is one register (B = 1,
// public: the geometry's P), and then the words are [path 0, stash 0, ...] and
// pair 0 is (path 0, stash 0) -- one pair fewer than a zero path register 1
// would cost.  The default rule's folded trees live here.
inline constexpr unsigned ReadPathFirstWord(unsigned b) { return b; }
inline constexpr unsigned ReadPathPairs(unsigned A, unsigned B, unsigned b) {
  return (B + A - ReadPathFirstWord(b) + 1) / 2;
}
inline constexpr unsigned kReadPathMaxPairs =
    ReadPathPairs(kMaxStashRegisters, kReadPathPathRegisters, 0);
// The path registers a path of `path_buckets` buckets spans.
inline constexpr unsigned ReadPathRegisters(unsigned path_buckets) {
  return path_buckets > kReadPathBucketsPerRegister ? 2u : 1u;
}
struct ReadPathPlan {
  // Per destination path register `b`: every lane's index within its pair,
  // and pair `q`'s lanes (pair q of b's words, ReadPathFirstWord(b) + 2 q on).
  __m512i index[kReadPathPathRegisters];
  uint64_t from[kReadPathPathRegisters][kReadPathMaxPairs];
  // The target's index within its pair in every lane, and the pair (grouped
  // as destination 0's): all ones for the pair holding it, zero for the
  // others (all zero when not found).
  __m512i target_index;
  uint64_t target_from[kReadPathMaxPairs];
  uint64_t keep[kMaxStashRegisters];  // stash lanes whose entry stays put
  uint64_t land[kMaxStashRegisters];  // the landing lane, one bit or none
  bool found = false;
  unsigned stash_count = 0;  // stash entries kept, the landed one excluded
  unsigned occupancy = 0;    // stash entries after the pass
  bool overflow = false;     // no free lane: stash_count > 64 A - 1
};

namespace detail {

// Per-lane bit length (0..8) of one byte line, by two nibble LUTs.
INLINE __m512i BitLength8(__m512i x) {
  const __m128i lut_lo = _mm_setr_epi8(0, 1, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4);
  const __m128i lut_hi = _mm_setr_epi8(0, 5, 6, 6, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8);
  const __m512i nib = _mm512_set1_epi8(0x0F);
  const __m512i lo = _mm512_and_si512(x, nib);
  const __m512i hi = _mm512_and_si512(_mm512_srli_epi16(x, 4), nib);
  const __m512i bl_lo = _mm512_shuffle_epi8(_mm512_broadcast_i32x4(lut_lo), lo);
  const __m512i bl_hi = _mm512_shuffle_epi8(_mm512_broadcast_i32x4(lut_hi), hi);
  return _mm512_mask_blend_epi8(core::obliTestMask8(hi, hi), bl_lo, bl_hi);
}

// The eight byte lines of a 64-bit field, line `k` at `base + Stride k`, XOR
// the word's bytes broadcast once by the caller (`word_bytes[k]` is byte `k`
// of the word in every lane), OR-ed together: a zero byte is a lane whose
// field equals the word.  The lines are read in place -- a stash register's
// are a stash line apart -- because copying them into a local array first
// cost a stack store per line.
template <size_t Stride>
INLINE __m512i FieldXorOr8At(const uint8_t* base, const __m512i* word_bytes) {
  __m512i x[8];
  for (int i = 0; i < 8; ++i) {
    x[i] = _mm512_xor_si512(
        _mm512_load_si512(reinterpret_cast<const void*>(base + Stride * i)),
        word_bytes[i]);
  }
  const __m512i t0 = _mm512_ternarylogic_epi64(x[0], x[1], x[2], 0xFE);
  const __m512i t1 = _mm512_ternarylogic_epi64(x[3], x[4], x[5], 0xFE);
  const __m512i t2 = _mm512_ternarylogic_epi64(x[6], x[7], t0, 0xFE);
  return _mm512_or_si512(t1, t2);
}

// Per-lane bit length of the same field XOR the word, resolved exactly below
// `cap` bits.  At or above `cap` the only promise is that the answer is also
// at or above `cap` -- it is `cap` itself, or the exact length when the byte
// line that carries it was resolved anyway.
//
// That weaker promise is free, because the caller only ever wants
// `leaf_bits - bitlen` saturated at zero and `cap` is `leaf_bits + 1`: every
// bit length past `leaf_bits` is the same answer, an entry that belongs
// nowhere on this path.  So the byte lines above `leaf_bits` do not need a
// nibble-LUT round each; folding them into ONE "is any of these bytes
// nonzero" test drops four to six of the eight rounds at the depths the
// tree is built at.
template <size_t Stride>
INLINE __m512i BitLengthCappedAt(const uint8_t* base, const __m512i* word_bytes,
                                 unsigned cap) {
  const unsigned top = (cap + 7) / 8 < 8 ? (cap + 7) / 8 : 8;
  const auto line = [&](unsigned k) {
    return _mm512_xor_si512(
        _mm512_load_si512(reinterpret_cast<const void*>(base + Stride * k)),
        word_bytes[k]);
  };
  __m512i high = _mm512_setzero_si512();
  for (unsigned k = top; k < 8; ++k) high = _mm512_or_si512(high, line(k));
  __mmask64 seen = core::obliTestMask8(high, high);
  // Both broadcasts are PINNED (core::obliPin512).  Written plainly, GCC at
  // -O3 fuses a broadcast and the masked move into one
  // `VPBROADCASTB zmm{k}{z}, m8` whose byte load is under a secret mask, so
  // whether that (public, L1-resident) byte is fetched would depend on the
  // working set.  The pin costs nothing.
  __m512i len = _mm512_maskz_mov_epi8(
      seen, core::obliPin512(_mm512_set1_epi8(static_cast<char>(cap))));
  for (int k = static_cast<int>(top) - 1; k >= 0; --k) {
    const __m512i x = line(static_cast<unsigned>(k));
    const __mmask64 nz = core::obliTestMask8(x, x);
    const __m512i bl = _mm512_add_epi8(
        BitLength8(x),
        core::obliPin512(_mm512_set1_epi8(static_cast<char>(8 * k))));
    len = _mm512_mask_mov_epi8(len, _kandn_mask64(seen, nz), bl);
    seen = _kor_mask64(seen, nz);
  }
  return len;
}

// The lowest set lane over `n` words as a one-hot (the input is cleared to
// it), branch-free.  `n` is public.
INLINE void LowestOverWords(uint64_t* words, unsigned n) {
  uint64_t none_yet = ~uint64_t{0};
  for (unsigned w = 0; w < n; ++w) {
    const uint64_t low = words[w] & (uint64_t{0} - words[w]) & none_yet;
    words[w] = low;
    none_yet = core::obliSelectU64(none_yet, 0, low != 0);
  }
}

}  // namespace detail

// The byte iota 0..63 as a 64-byte constant, for the permute-index vectors.
struct IotaBytes {
  alignas(64) uint8_t b[64];
};
inline constexpr IotaBytes MakeIotaBytes() {
  IotaBytes r{};
  for (unsigned i = 0; i < 64; ++i) r.b[i] = static_cast<uint8_t>(i);
  return r;
}
inline constexpr IotaBytes kIotaBytes = MakeIotaBytes();

// `HasTarget` is the PUBLIC pass kind: an engine access names a uid to
// gather; a pass with none (the planner test's and the comparator's) is
// specialized to skip the uid comparisons rather than mask them to nothing.
template <unsigned A, unsigned B, bool HasTarget>
inline void PlanReadPathImpl(const ReadPathEvictionInput& in,
                             ReadPathPlan* plan) {
  static_assert(A >= kMinStashRegisters && A <= kMaxStashRegisters, "A is 3 or 4");
  static_assert(B == 1 || B == 2, "one or two path registers");
  constexpr unsigned W = B + A;
  constexpr uint64_t kSlotMask = (uint64_t{1} << kBucketSlots) - 1;
  const unsigned P = in.path_buckets;

  // 1. Valid, match and the deepest level, word by word, every line read in
  // place: a path register's lines are consecutive tile lines, a stash
  // register's are one stash line (64 A bytes) apart.  The uid's and the
  // path's bytes are broadcast once for every word.
  const __m512i leaf = _mm512_set1_epi8(static_cast<char>(in.leaf_bits));
  const unsigned cap = in.leaf_bits + 1;
  const uint64_t path_word = in.path_position | kRealPositionBit;
  constexpr size_t kStashStride = 64 * A;
  __m512i uid_bytes[8];
  __m512i path_bytes[8];
  for (unsigned k = 0; k < 8; ++k) {
    if constexpr (HasTarget) {
      uid_bytes[k] = _mm512_set1_epi8(static_cast<char>(in.target_uid >> (8 * k)));
    }
    path_bytes[k] = _mm512_set1_epi8(static_cast<char>(path_word >> (8 * k)));
  }
  uint64_t valid[W];
  uint64_t match[W] = {};
  __m512i deepest[W];
  const auto front = [&](unsigned w, const uint8_t* base, auto stride) {
    constexpr size_t S = decltype(stride)::value;
    valid[w] = _cvtmask64_u64(_mm512_movepi8_mask(_mm512_load_si512(
        reinterpret_cast<const void*>(base + S * kRealPositionLine))));
    if constexpr (HasTarget) {
      const __m512i mx =
          detail::FieldXorOr8At<S>(base + S * kUidOffset, uid_bytes);
      match[w] = core::obliTestNMask8(mx, mx) & valid[w];
    }
    deepest[w] = _mm512_subs_epu8(
        leaf, detail::BitLengthCappedAt<S>(base + S * kPositionOffset,
                                           path_bytes, cap));
  };
  for (unsigned w = 0; w < W; ++w) {
    if (w < B) {
      front(w, reinterpret_cast<const uint8_t*>(in.path_meta + kMetaBytes * w),
            std::integral_constant<size_t, 64>{});
    } else {
      front(w, in.stash_meta + 64 * (w - B),
            std::integral_constant<size_t, kStashStride>{});
    }
  }
  // At most one lane holds a given uid; keep the first if storage were ever
  // inconsistent, so the plan stays a function.
  if constexpr (HasTarget) detail::LowestOverWords(match, W);
  uint64_t any = 0;
  for (unsigned w = 0; w < W; ++w) any |= match[w];
  const bool found = any != 0;

  // 2. The eligibility masks, hoisted out of the placement: they do not
  // depend on it, and the runtime trip count stops the compiler hoisting
  // them itself.  Path register 0 holds positions 0..15, and every one of
  // its entries is placed by step 15, so its masks past that are zero.
  uint64_t ge[kReadPathMaxBuckets][W];
  for (unsigned m = 0; m < P; ++m) {
    const __m512i level =
        _mm512_set1_epi8(static_cast<char>(in.level_match_bits[m]));
    for (unsigned w = 0; w < W; ++w) {
      ge[m][w] = (B == 2 && w == 0 && m >= kReadPathBucketsPerRegister)
                     ? 0
                     : core::obliCmpGeU8Mask(deepest[w], level);
    }
  }

  // 3. Placement, leaf first.  Each word takes the slots its predecessors
  // left: `kSlotMask >> filled`, where `filled` is how many slots the words
  // ahead of it took.  That is the clamped count of eligible lanes ahead,
  // min(eligible ahead, 4), since popcnt(pdep(kSlotMask >> c, pool)) =
  // min(4 - c, popcnt(pool)) -- the same take masks with no clamp, and the
  // running counts also place every pair's sources in the bucket.
  const __m512i iota =
      _mm512_load_si512(reinterpret_cast<const void*>(kIotaBytes.b));
  const __m512i iota_hi = _mm512_or_si512(iota, _mm512_set1_epi8(64));
  alignas(64) uint8_t index_bytes[kReadPathPathRegisters][64];
  std::memset(index_bytes, 0, sizeof(index_bytes));
  uint64_t from[kReadPathPathRegisters][kReadPathMaxPairs] = {};
  uint64_t rem[W];
  for (unsigned w = 0; w < W; ++w) rem[w] = valid[w] & ~match[w];
  // Step `m`, whose bucket is in destination register `b` (public, a
  // constant: the steps of each register run as their own loop).
  const auto place = [&](unsigned m, auto dest) {
    constexpr unsigned b = decltype(dest)::value;
    constexpr unsigned F = ReadPathFirstWord(b);
    constexpr unsigned Q = ReadPathPairs(A, B, b);
    uint64_t take[W];
    unsigned filled[W + 1];
    filled[0] = 0;
    for (unsigned w = 0; w < W; ++w) {
      take[w] = _pdep_u64(kSlotMask >> filled[w], rem[w] & ge[m][w]);
      filled[w + 1] = filled[w] + static_cast<unsigned>(_mm_popcnt_u64(take[w]));
    }
    for (unsigned w = 0; w < W; ++w) rem[w] ^= take[w];
    // The pairs' source lists, in priority order, joined into the bucket's
    // four index bytes: pair q of register b's words is (lo, lo + 1) with
    // lo = F + 2q; its list starts at slot filled[lo], its high word's at
    // filled[lo + 1], and it ends at filled[lo + 2].  The odd last word (lo =
    // W - 1) is the accumulator's pair: its list is word lo's alone, as the
    // high word.  Register 1's steps take nothing from word 0 (its masks
    // past position 15 are zero), so filled[1] = 0 there.  All counts are at
    // most 4, so no shift reaches 64.
    const unsigned d0 = kBucketSlots * (m % kReadPathBucketsPerRegister);
    uint64_t word = 0;
    for (unsigned q = 0; q < Q; ++q) {
      const unsigned lo = F + 2 * q;
      const unsigned start = filled[lo];
      const unsigned end = filled[lo + 2 <= W ? lo + 2 : W];
      uint64_t list;
      if (lo + 1 < W) {
        list = static_cast<uint32_t>(_mm_cvtsi128_si32(
            _mm512_castsi512_si128(_mm512_maskz_compress_epi8(take[lo], iota))));
        const unsigned n_lo = filled[lo + 1] - start;
        const uint64_t hi_list = static_cast<uint32_t>(_mm_cvtsi128_si32(
            _mm512_castsi512_si128(
                _mm512_maskz_compress_epi8(take[lo + 1], iota_hi))));
        list |= hi_list << (8 * n_lo);
      } else {
        list = static_cast<uint32_t>(_mm_cvtsi128_si32(_mm512_castsi512_si128(
            _mm512_maskz_compress_epi8(take[lo], iota_hi))));
      }
      word |= list << (8 * start);
      from[b][q] |= ((uint64_t{1} << end) - (uint64_t{1} << start)) << d0;
    }
    const uint32_t word32 = static_cast<uint32_t>(word);
    std::memcpy(&index_bytes[b][d0], &word32, sizeof(word32));
  };
  // Register 0's steps, then register 1's.  One path register (B = 1) is
  // register 0 at every step.
  const unsigned P0 =
      B == 1 || P < kReadPathBucketsPerRegister ? P : kReadPathBucketsPerRegister;
  for (unsigned m = 0; m < P0; ++m) {
    place(m, std::integral_constant<unsigned, 0>{});
  }
  if constexpr (B == 2) {
    for (unsigned m = kReadPathBucketsPerRegister; m < P; ++m) {
      place(m, std::integral_constant<unsigned, 1>{});
    }
  }

  // 4. The stash: what stays, the count, and the landing lane -- the lowest
  // one not kept, taken only if the accessed entry stays.
  unsigned count = 0;
  uint64_t free_lanes[A];
  for (unsigned a = 0; a < A; ++a) {
    const uint64_t kept = rem[B + a];
    plan->keep[a] = kept;
    count += static_cast<unsigned>(_mm_popcnt_u64(kept));
    free_lanes[a] = ~kept;
  }
  detail::LowestOverWords(free_lanes, A);
  const unsigned lands =
      (static_cast<unsigned>(found) | static_cast<unsigned>(in.create)) &
      static_cast<unsigned>(!in.erase);
  const uint64_t land_mask = uint64_t{0} - lands;
  for (unsigned a = 0; a < A; ++a) plan->land[a] = free_lanes[a] & land_mask;

  // 5. The target's source: its pair, and its index within the pair, the
  // words grouped as destination 0's.  The odd last word's pair is (the
  // accumulator, word W - 1), so its match is the high word's.
  constexpr unsigned Q0 = ReadPathPairs(A, B, 0);
  uint64_t target_index = 0;
  for (unsigned q = 0; q < Q0; ++q) {
    const bool pair = 2 * q + 1 < W;  // public
    const uint64_t lo = pair ? match[2 * q] : 0;
    const uint64_t hi = pair ? match[2 * q + 1] : match[2 * q];
    const uint64_t in_pair = uint64_t{0} - static_cast<uint64_t>((lo | hi) != 0);
    const uint64_t index = core::obliSelectU64(
        _tzcnt_u64(lo), 64 + _tzcnt_u64(hi), lo == 0);
    target_index |= index & in_pair;
    plan->target_from[q] = in_pair;
  }

  for (unsigned b = 0; b < kReadPathPathRegisters; ++b) {
    plan->index[b] =
        _mm512_load_si512(reinterpret_cast<const void*>(index_bytes[b]));
    for (unsigned q = 0; q < kReadPathMaxPairs; ++q) plan->from[b][q] = from[b][q];
  }
  plan->target_index = _mm512_set1_epi8(static_cast<char>(target_index));
  plan->found = found;
  plan->stash_count = count;
  plan->occupancy = count + lands;
  // The failure event, the one secret-dependent branch the construction
  // permits (the caller throws on it before any store).
  plan->overflow = count > 64 * A - 1;
}

template <unsigned A, unsigned B>
inline void PlanReadPath(const ReadPathEvictionInput& in, ReadPathPlan* plan) {
  if (in.has_target) {
    PlanReadPathImpl<A, B, true>(in, plan);
  } else {
    PlanReadPathImpl<A, B, false>(in, plan);
  }
}

// THE SCALAR REFERENCE of the same rule, for tests.  The working set is in
// priority order: path lanes 0..64 B - 1 (position `l / 4`, slot `l % 4`;
// B = ReadPathRegisters(P)), then stash lanes 64 B + 64 a + l.  `uid` and `pos` are as stored, so `pos`
// carries the real bit.
struct ReferenceReadPath {
  static constexpr uint16_t kNone = 0xFFFF;
  uint16_t source[kReadPathPathRegisters * 64];  // per path destination lane
  bool keep[kMaxStashRegisters * 64] = {};
  int landing = -1;  // stash lane, or -1
  int target = -1;   // working-set lane, or -1
  bool found = false;
  bool path_entry_dropped = false;  // the rule's first property, violated
  unsigned stash_count = 0;
  bool overflow = false;
};

inline ReferenceReadPath ReferenceReadPathEvict(
    const uint64_t* uid, const uint64_t* pos, unsigned stash_registers,
    uint64_t target_uid, bool has_target, bool create, bool erase,
    uint64_t path_position, unsigned leaf_bits, unsigned path_buckets,
    const uint8_t* level_match_bits) {
  ReferenceReadPath r;
  const unsigned path_lanes = 64 * ReadPathRegisters(path_buckets);
  const unsigned lanes = path_lanes + 64 * stash_registers;
  for (auto& s : r.source) s = ReferenceReadPath::kNone;
  bool placed[(kReadPathPathRegisters + kMaxStashRegisters) * 64] = {};
  const auto real = [&](unsigned l) { return StoredPositionIsReal(pos[l]); };
  for (unsigned l = 0; l < lanes; ++l) {
    if (real(l) && has_target && uid[l] == target_uid && r.target < 0) {
      r.target = static_cast<int>(l);
    }
  }
  r.found = r.target >= 0;
  if (r.found) placed[r.target] = true;
  const auto deepest = [&](unsigned l) {
    const uint64_t x = StoredPositionLeaf(pos[l]) ^ path_position;
    unsigned bitlen = 0;
    while (bitlen < 64 && (x >> bitlen) != 0) ++bitlen;
    return bitlen > leaf_bits ? 0u : leaf_bits - bitlen;
  };
  for (unsigned m = 0; m < path_buckets; ++m) {
    unsigned taken = 0;
    for (unsigned l = 0; l < lanes && taken < kBucketSlots; ++l) {
      if (!real(l) || placed[l] || deepest(l) < level_match_bits[m]) continue;
      r.source[kBucketSlots * m + taken] = static_cast<uint16_t>(l);
      placed[l] = true;
      ++taken;
    }
  }
  for (unsigned l = 0; l < path_lanes; ++l) {
    if (real(l) && !placed[l]) r.path_entry_dropped = true;
  }
  for (unsigned s = 0; s < 64 * stash_registers; ++s) {
    const unsigned l = path_lanes + s;
    r.keep[s] = real(l) && !placed[l];
    r.stash_count += r.keep[s];
  }
  if ((r.found || create) && !erase) {
    for (unsigned s = 0; s < 64 * stash_registers; ++s) {
      if (!r.keep[s]) {
        r.landing = static_cast<int>(s);
        break;
      }
    }
  }
  r.overflow = r.stash_count > 64 * stash_registers - 1;
  return r;
}

}  // namespace tree
}  // namespace microram
