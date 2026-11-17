#pragma once

// Routing-index maps, the re-tag pass, and nonce identity.
//
// ROUTING-INDEX MAPS.  A level of fanout 2 (and every butterfly block) routes
// into tables of 2^k buckets, where the tag's low k bits ARE the bucket index.
// A level of fanout B > 2 ("base-B" below: its digit counts the carries a
// partial table has absorbed, src/oram/levelarena/DESIGN.md) routes into
// tables of m * 2^k buckets for a digit m that need not be a power of two, so
// the index is (T mod 2^k) + 2^k * ((T >> k) mod m): a low field taken verbatim
// and a high field reduced by a small odd modulus.  The map is public -- m and
// k are public geometry -- while T is secret and needs fixed-time arithmetic.
// The map is applied once at tag time and written back into the tag lines,
// which keeps every downstream
// MergeSplit a plain test of one bit.
//
// The high field has to stay uniform for the bucket-load argument to hold, and
// it does: the residues of a uniform 64-bit word mod a small odd m are uniform
// to within 2^-58, and the m values in use differ in every bit.
//
// THE RE-TAG PASS.  A rebuild consumes tables hashed under other nonces, so it
// must recompute every tag under its own.  CopyAndRetagRange fuses the copy
// into the destination with the re-hash, because a separate copy pass and
// re-hash pass would read the same lines twice.  ScatterBucketTags is split
// out so the index map can be re-applied without re-running AES.
//
// NONCE IDENTITY.  The effective nonce is ALLOCATED from a monotone counter,
// not sampled.  Sampling looks safer and is not: a 64-bit birthday collision
// over the lifetime of a long-running instance is a real event, and a repeated
// nonce means two tables hash the same key into the same bucket -- exactly the
// correlation the re-hash exists to destroy.  A counter cannot repeat.
//
// One rebuild draws one EPOCH and derives two nonces from it, real and dummy.
// The FAMILY, not the table id, is the unit of identity, because one epoch can
// span a whole chain of published tables and the security invariant that
// matters -- at most one real probe per (family, key) -- is only meaningful at
// that granularity.

#include <immintrin.h>

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <stdexcept>

#include "src/oram/table/cpu_byteslice_host_cache.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/table/cpu_byteslice_meta.hpp"
#include "src/oram/table/cpu_byteslice_tags.hpp"

namespace microram {
namespace byteslice {

// ---------------------------------------------------------------------------
// How wide the routing tag has to be, and where the radix digit sits in it
// ---------------------------------------------------------------------------
//
// Both hierarchies answer this the same way, from one number: `index_bits`,
// the DEEPEST butterfly the configuration ever routes.  The tag has to hold
// that many index bits, and -- above B = 2 -- three more for the radix digit,
// which the radix pass compares as a single byte line.
//
// Giving the digit a byte of its own costs a 64-byte line per bucket, moved
// at every butterfly level, copied by every re-tag, and the one tag line
// per-level pruning can never retire -- bought for three bits.  It is only
// necessary when the index bits already fill their own top byte to within
// two: at `index_bits % 8 <= 5` the digit fits ALONGSIDE them in that byte,
// which is what Layout::digit_bits records and NormalizeDigitLine undoes.  At
// 6 or 7 it would straddle a byte boundary, so the reserved byte is kept --
// and those are exactly the residues where packing would save nothing anyway.
//
// Rounding the width up "just in case" is therefore not free, in either
// direction.  Every caller should size the tag from here.
struct RoutingTagPlan {
  size_t tag_bytes = 1;
  size_t digit_bits = 0;  // Layout::digit_bits; 0 means a reserved digit byte
};

// THE DIGIT'S WIDTH IN THE TAG, and the only place it is written down.
//
// Three bits, because the radices are 1..7 (kMaxRadix, which lives in
// rebuild/ and so cannot be named from here).  It is RESERVED rather than
// fitted: one layout serves every digit of a hierarchy, a rebuild's modulus
// varies from item to item, and a tag sized for the modulus in front of it
// would have to be resized for the next one.  So every rule below is stated
// in these three bits and none of them in a modulus.
inline constexpr unsigned kRoutingDigitBits = 3;

// Whether the digit fits in the top index byte alongside the index bits.  It
// needs its three bits there, so it fits iff the index bits leave that many
// spare in their own top byte -- `bits % 8 <= 5`.  At `% 8 == 0` the digit
// starts a fresh byte and the two layouts coincide exactly.
inline bool RoutingDigitPacks(unsigned index_bits) {
  return (index_bits % 8) + kRoutingDigitBits <= 8;
}

// `raw_route_bits` is the deepest butterfly the configuration routes under a
// kRaw map, when that is deeper than `index_bits`: the level arena's binary
// top routes `K + log2 D` raw bits over a table whose digit-bearing tables
// route `K` (levelarena DESIGN.md, "Top compaction and residuals": the top
// digit D is a power of two and preparation routes one binary butterfly over
// all T top buckets).  A raw route needs
// no digit and no particular byte, only room, so it widens the tag and moves
// nothing.  Wherever a digit is reserved the room is already there:
// ceil((K+3)/8) bytes in every residue, which is what makes the binary top
// free of tag bytes above B = 2.  0 means no such route.
inline RoutingTagPlan PlanRoutingTag(unsigned index_bits,
                                     bool has_radix_digit,
                                     unsigned raw_route_bits = 0) {
  RoutingTagPlan plan;
  const size_t index_bytes = (index_bits + 7) / 8;
  if (!has_radix_digit) {  // B = 2: no radix pass, no digit
    plan.tag_bytes = index_bytes;
  } else if (RoutingDigitPacks(index_bits)) {
    // Wide enough for the index bits PLUS the digit's three, which is one byte
    // narrower than a reserved byte whenever the index bits do not already
    // fill their top byte to within two.
    plan.tag_bytes = (index_bits + kRoutingDigitBits + 7) / 8;
    plan.digit_bits = index_bits % 8;
  } else {
    plan.tag_bytes = index_bytes + 1;
  }
  const size_t raw_bytes = (static_cast<size_t>(raw_route_bits) + 7) / 8;
  if (raw_bytes > plan.tag_bytes) plan.tag_bytes = raw_bytes;
  return plan;
}

// The digit's bit position within the whole tag word, i.e. what a kRadixDigit
// map's `digit_shift` must be for this layout.  The digit always lives in the
// most significant tag byte (Layout::DigitLine()), at offset `digit_bits`
// inside it.  This is the ONLY spelling of the rule; a rebuild that computes
// it by hand is a rebuild that can disagree with the layout.
inline unsigned RoutingDigitShift(const Layout& layout) {
  return static_cast<unsigned>(8 * (layout.tag_bytes - 1) + layout.digit_bits);
}

// Whether this layout can carry a radix digit AT ALL -- i.e. whether the three
// bits at RoutingDigitShift are inside the tag.
//
// A SEPARATE QUESTION FROM "are the index bits inside the tag", and the one
// that is easy to miss, because a rebuild that checks only the index sees a
// digit field that is present, addressable and simply too narrow.  The re-tag
// writes the digit's byte by truncating the mapped tag word to eight bits
// (ScatterBucketTags), so a digit with two bits of room is not an error
// anywhere downstream: it is a perfectly good digit, and every entry whose
// digit needed the third bit routes to a block that is not its own.
//
// Three equivalent statements, which is why this is a function rather than a
// line in each caller: the arithmetic below, `layout.digit_bits <= 5`, and
// "this is a layout PlanRoutingTag produces for a radix hierarchy" -- the
// packed form for index residues 0..5 and the reserved-byte form otherwise,
// and nothing else.  tests/oram/cpu_byteslice_routing_tag_test.cpp sweeps the
// three against each other.
inline bool RoutingDigitFits(const Layout& layout) {
  return RoutingDigitShift(layout) + kRoutingDigitBits <= 8 * layout.tag_bytes;
}

// A base-B level routes into tables of m * 2^k buckets, so the stored
// tag word is not always the raw AES output: a public per-rebuild map
// turns the 64-bit tag T into the stored routing word.  kRaw stores T itself
// (the plain power-of-two butterfly); kRadixDigit stores the low `low_bits`
// index bits plus a radix digit ((T >> low_bits) mod modulus) placed in the
// last tag byte, where the radix-r MergeSplit pass compares it as one byte
// line; kFoldDuplicate is the fixed-level map: class g = (T >> low_bits) mod
// modulus homes at block g+1, and the duplicated class g = modulus-1 splits
// over blocks {0, modulus+1-1=B-1} on one more tag bit, later folded.  0 and
// B-1 differ in every bit, so each stored bit stays exactly 50/50 and bucket
// loads keep mean <= 32 at every butterfly level.
enum class TagMapKind : uint8_t { kRaw, kRadixDigit, kFoldDuplicate };

struct RoutingIndexMap {
  TagMapKind kind = TagMapKind::kRaw;
  unsigned low_bits = 0;     // butterfly bits below the digit / class field
  unsigned modulus = 1;      // radix r, or B-1 classes for kFoldDuplicate
  unsigned digit_shift = 0;  // kRadixDigit: bit position of the digit byte
};

inline uint64_t RoutingMultiplyHigh(uint64_t a, uint64_t b) {
  unsigned long long high;
  (void)_mulx_u64(a, b, &high);
  return high;
}

// Constant-divisor mod for the small radices. Spell out the reciprocal
// arithmetic: GCC (15.2, -O3) can merge v % {3,5,6,7} switch arms back into a
// shared DIV in the batched address pass, despite emitting multiply sequences
// at other call sites. Its dividend is a secret AES tag; DIV has no portable
// data-independent timing guarantee. These exact unsigned quotients avoid it.
//
// The name says "odd" because AbsorbShape's r is odd by construction below
// the top level.  The even arms make the function total over every supported
// radix 1..8, for callers that use a whole digit as the modulus; 8 is the
// whole-digit map a binary top's way is checked against.  This runs on secret
// tags wherever a map is applied, which is why they get their own arms rather
// than the 64-bit divide the default would be; a re-tag applies it eight lanes
// at a time (ModSmallLanes).
inline uint64_t ModSmallOdd(uint64_t v, unsigned m) {
  switch (m) {
    case 1: return 0;
    case 2: return v & 1;
    case 3: {
      const uint64_t q = RoutingMultiplyHigh(v, 0xAAAAAAAAAAAAAAABull) >> 1;
      return v - 3 * q;
    }
    case 4: return v & 3;
    case 5: {
      const uint64_t q = RoutingMultiplyHigh(v, 0xCCCCCCCCCCCCCCCDull) >> 2;
      return v - 5 * q;
    }
    case 6: {
      const uint64_t q = RoutingMultiplyHigh(v, 0xAAAAAAAAAAAAAAABull) >> 2;
      return v - 6 * q;
    }
    case 7: {
      const uint64_t high = RoutingMultiplyHigh(v, 0x2492492492492493ull);
      const uint64_t q = (high + ((v - high) >> 1)) >> 2;
      return v - 7 * q;
    }
    case 8: return v & 7;
    // Outside the hierarchy's supported radices (1..8); no constant-time
    // guarantee for this general-purpose fallback.
    default: return v % m;
  }
}

// Index in `modulus` contiguous blocks of 2^low_bits buckets. Rebuild tags put
// the block digit in a reserved high byte (`digit_shift > low_bits`); probes
// want the compact physical table index (`digit_shift == low_bits`). Keeping
// both forms in one primitive makes the rebuild and lookup algebra identical.
inline uint64_t ApplyRadixIndexMap(uint64_t t, unsigned low_bits,
                                   unsigned modulus, unsigned digit_shift) {
  return (t & LowMask64(low_bits)) |
         (ModSmallOdd(t >> low_bits, modulus) << digit_shift);
}

// The stored routing word for raw tag `t`.
inline uint64_t ApplyRoutingIndexMap(const RoutingIndexMap& map, uint64_t t) {
  switch (map.kind) {
    case TagMapKind::kRaw:
      return t;
    case TagMapKind::kRadixDigit:
      return ApplyRadixIndexMap(t, map.low_bits, map.modulus,
                                map.digit_shift);
    case TagMapKind::kFoldDuplicate: {
      const uint64_t g = ModSmallOdd(t >> map.low_bits, map.modulus);
      // Homes: class g -> block g+1 (blocks 1..B-1, the arena top).  The
      // duplicated class g = modulus-1 also owns block 0, chosen by one
      // more tag bit; the fold later merges block 0 into block modulus.
      //
      // Branchless, and not only for speed: `t` is the AES tag of a stored key
      // under the rebuild's secret nonce, so both of the tests this replaces
      // were data-dependent branches on a secret, evaluated 64 times per
      // bucket inside ScatterBucketTags' scalar loop.  The destination digit
      // is meant to be revealed by the butterfly's fixed permutation trace,
      // not by branch timing -- and the inner `t >> 63` test is 50/50, so the
      // mispredicts were real as well.
      const uint64_t top = 0ull - (t >> 63);              // all ones iff set
      const uint64_t dup = 0ull - static_cast<uint64_t>(g == map.modulus - 1);
      const uint64_t d = (dup & (top & uint64_t{map.modulus})) | (~dup & (g + 1));
      return (t & LowMask64(map.low_bits)) | (d << map.low_bits);
    }
  }
  return t;
}

// Number of tag bytes a rebuild that routes `route_levels` butterfly levels
// actually consumes.  route_levels == 0 means "the whole tag" (the standalone
// / test entry points).  With the reversed byte order those are tag bytes
// [0, n), i.e. the LAST n tag byte lines; the radix digit byte (the most
// significant one, at DigitLine()) is written on top of them when the map
// calls for it.  Anything above stays stale, which is fine: the tag is
// scratch and every rebuild recomputes what it needs.
inline size_t RoutedTagBytes(const Layout& layout, unsigned route_levels) {
  if (route_levels == 0) return layout.tag_bytes;
  const size_t needed = (static_cast<size_t>(route_levels) + 7) / 8;
  return needed < layout.tag_bytes ? needed : layout.tag_bytes;
}

// The index map applied to the 64 raw tag words of one bucket, IN PLACE.
//
// Its own function because two different things need it: the re-tag below,
// which then writes the mapped word out byte line by byte line, and the level
// arena's top compaction, which needs only the mapped word's DIGIT and writes
// nothing (ComputeBucketDigitLine).  A second spelling of the scalar loop
// would be a second place for the map to be applied differently.
// ModSmallOdd of eight qword lanes, exactly, for the moduli it has arms for.
// No DIV, branch or table touches the value, and it stays in registers: the
// scalar loop it replaces spilled the tags, ran 64 64x64 multiplies and
// reloaded each register across eight scalar stores.
//
// An odd modulus first shrinks the word to a small sum with the same residue:
// 256 = 1 (mod 3) and (mod 5), so VPSADBW's byte sum (at most 2040) serves;
// mod 7 the byte weights cycle 1, 4, 2 (256^i mod 7), which VPMADDUBSW and
// VPMADDWD apply (sum at most 4845).  The sum's residue is then
// ((c * s mod 2^32) * m) >> 32 with c = ceil(2^32 / m), exact for every
// s < 2^16 (the routing tag test reaches every sum).  6 is the residue mod 3
// moved to the member of {r3, r3 + 3} with the word's parity.
template <unsigned M>
INLINE __m512i ModSmallLanes(__m512i v) {
  static_assert(M >= 1 && M <= 8, "no fixed-time arm for this modulus");
  if constexpr (M == 1) {
    return _mm512_setzero_si512();
  } else if constexpr ((M & (M - 1)) == 0) {
    return _mm512_and_si512(v, _mm512_set1_epi64(M - 1));
  } else if constexpr (M == 6) {
    const __m512i r3 = ModSmallLanes<3>(v);
    const __m512i odd = _mm512_and_si512(_mm512_xor_si512(v, r3),
                                         _mm512_set1_epi64(1));
    return _mm512_add_epi64(r3,
                            _mm512_add_epi64(odd, _mm512_slli_epi64(odd, 1)));
  } else {
    __m512i sum;
    if constexpr (M == 7) {
      const __m512i pairs = _mm512_maddubs_epi16(
          v, _mm512_set1_epi64(0x0401020401020401ll));
      const __m512i halves = _mm512_madd_epi16(pairs, _mm512_set1_epi16(1));
      // The low dword is the sum; the high one is left over and unread.
      sum = _mm512_add_epi64(halves, _mm512_srli_epi64(halves, 32));
    } else {
      sum = _mm512_sad_epu8(v, _mm512_setzero_si512());
    }
    constexpr uint32_t kCeil =
        static_cast<uint32_t>((uint64_t{1} << 32) / M + 1);
    const __m512i fraction =
        _mm512_mul_epu32(sum, _mm512_set1_epi64(kCeil));
    return _mm512_srli_epi64(
        _mm512_mul_epu32(fraction, _mm512_set1_epi64(M)), 32);
  }
}

// ApplyRoutingIndexMapKind over 64 tags, for modulus M.
template <unsigned M>
INLINE void ApplyModularMapToTags(const RoutingIndexMap& map, __m512i* tags) {
  const __m512i low =
      _mm512_set1_epi64(static_cast<long long>(LowMask64(map.low_bits)));
  const __m128i low_bits = _mm_cvtsi32_si128(static_cast<int>(map.low_bits));
  if (map.kind == TagMapKind::kRadixDigit) {
    const __m128i digit_shift =
        _mm_cvtsi32_si128(static_cast<int>(map.digit_shift));
    for (int i = 0; i < 8; ++i) {
      const __m512i digit =
          ModSmallLanes<M>(_mm512_srl_epi64(tags[i], low_bits));
      // (t & low) | (digit << digit_shift)
      tags[i] = _mm512_ternarylogic_epi64(
          tags[i], low, _mm512_sll_epi64(digit, digit_shift), 0xEA);
    }
    return;
  }
  assert(map.kind == TagMapKind::kFoldDuplicate);
  const __m512i one = _mm512_set1_epi64(1);
  const __m512i modulus = _mm512_set1_epi64(M);
  for (int i = 0; i < 8; ++i) {
    const __m512i t = tags[i];
    // h = g + 1, the class's home block, is M exactly for the duplicated
    // class, whose block is then M or 0 by the top tag bit: d = h & top.
    const __m512i home = _mm512_add_epi64(
        ModSmallLanes<M>(_mm512_srl_epi64(t, low_bits)), one);
    const __m512i dup = _mm512_srai_epi64(
        _mm512_sub_epi64(_mm512_xor_si512(home, modulus), one), 63);
    const __m512i top = _mm512_srai_epi64(t, 63);
    // home & ~(dup & ~top)
    const __m512i block = _mm512_ternarylogic_epi64(home, dup, top, 0xB0);
    tags[i] = _mm512_ternarylogic_epi64(
        t, low, _mm512_sll_epi64(block, low_bits), 0xEA);
  }
}

inline void ApplyRoutingIndexMapToTags(const RoutingIndexMap& map,
                                       __m512i* tags) {
  if (map.kind == TagMapKind::kRaw) return;
  // Byte for byte ApplyRoutingIndexMap on each tag, for ModSmallOdd's
  // fixed-time arms; its general fallback is not fixed-time and is refused.
  switch (map.modulus) {
    case 1: return ApplyModularMapToTags<1>(map, tags);
    case 2: return ApplyModularMapToTags<2>(map, tags);
    case 3: return ApplyModularMapToTags<3>(map, tags);
    case 4: return ApplyModularMapToTags<4>(map, tags);
    case 5: return ApplyModularMapToTags<5>(map, tags);
    case 6: return ApplyModularMapToTags<6>(map, tags);
    case 7: return ApplyModularMapToTags<7>(map, tags);
    case 8: return ApplyModularMapToTags<8>(map, tags);
  }
  throw std::invalid_argument(
      "routing map: no fixed-time re-tag for a modulus outside 1..8");
}

// The vpermt2b selectors of TagByteLineGroup: for a register pair's 16 words
// (8 in each), byte 4g + k of word j goes to byte 16k + j.
struct TagLineSelectors {
  alignas(64) uint8_t idx[2][kBucketCapacity];
  constexpr TagLineSelectors() : idx{} {
    for (unsigned g = 0; g < 2; ++g) {
      for (unsigned k = 0; k < 4; ++k) {
        for (unsigned j = 0; j < 16; ++j) {
          idx[g][16 * k + j] = static_cast<uint8_t>(8 * j + 4 * g + k);
        }
      }
    }
  }
};
inline constexpr TagLineSelectors kTagLineSelectors{};

// Byte lines 4g .. 4g+3 of 64 tag words, in registers: out[k] holds byte
// 4g + k of word e at byte e.  One two-source byte permute per register pair
// packs four bytes of its 16 words into one 128-bit lane each, and a 4x4 lane
// transpose (as at the end of TransposeKeyLinesToQwords) joins the pairs --
// 12 shuffles for four whole lines, against the 8 shifts and 8 narrow stores
// per line of vpmovqb.  The selectors are constants.
INLINE void TagByteLineGroup(const __m512i* tags, unsigned group,
                             __m512i* out) {
  const __m512i idx = _mm512_load_si512(
      reinterpret_cast<const void*>(kTagLineSelectors.idx[group]));
  const __m512i p0 = _mm512_permutex2var_epi8(tags[0], idx, tags[1]);
  const __m512i p1 = _mm512_permutex2var_epi8(tags[2], idx, tags[3]);
  const __m512i p2 = _mm512_permutex2var_epi8(tags[4], idx, tags[5]);
  const __m512i p3 = _mm512_permutex2var_epi8(tags[6], idx, tags[7]);
  const __m512i e0 = _mm512_shuffle_i64x2(p0, p1, 0x88);
  const __m512i e1 = _mm512_shuffle_i64x2(p0, p1, 0xDD);
  const __m512i e2 = _mm512_shuffle_i64x2(p2, p3, 0x88);
  const __m512i e3 = _mm512_shuffle_i64x2(p2, p3, 0xDD);
  out[0] = _mm512_shuffle_i64x2(e0, e2, 0x88);
  out[1] = _mm512_shuffle_i64x2(e1, e3, 0x88);
  out[2] = _mm512_shuffle_i64x2(e0, e2, 0xDD);
  out[3] = _mm512_shuffle_i64x2(e1, e3, 0xDD);
}

// The low byte of each of 64 words as one line (a way or digit line).
INLINE __m512i LowByteLine(const __m512i* words) {
  __m512i lines[4];
  TagByteLineGroup(words, 0, lines);
  return lines[0];
}

// Calls store(b, line) once for each tag byte b < routed and for b ==
// digit_byte (SIZE_MAX: none), with the line of byte b of all 64 tag words.
// Both bounds are public; a group of four lines no store wants is not built.
template <typename Store>
INLINE void ForEachTagByteLine(const __m512i* tags, size_t routed,
                               size_t digit_byte, Store&& store) {
  for (unsigned g = 0; g < 2; ++g) {
    const size_t first = 4 * g;
    if (routed <= first && (digit_byte < first || digit_byte >= first + 4)) {
      continue;
    }
    __m512i lines[4];
    TagByteLineGroup(tags, g, lines);
    for (unsigned k = 0; k < 4; ++k) {
      const size_t b = first + k;
      if (b < routed || b == digit_byte) store(b, lines[k]);
    }
  }
}

// The shift that puts the DIGIT's tag byte -- the most significant one,
// Layout::DigitLine() -- in the low eight bits of a mapped tag word.
inline unsigned DigitTagByteShift(const Layout& layout) {
  return static_cast<unsigned>(8 * (layout.tag_bytes - 1));
}

// The tag-WRITING half of a re-tag: apply the public index map to the 64 tags
// a bucket's keys hashed to, then lay down the byte lines the rebuild will
// actually route.  `routed` and `write_digit` are loop invariants of the
// caller (they are functions of the layout and the map, both public), so they
// are computed once and passed in.
//
// Split out of ComputeRoutingTagsRange so that CopyAndRetagRange, which does
// the same thing from keys it never re-read, cannot drift into writing
// different bytes than the standalone pass does.  The two are checked against
// each other byte for byte, but sharing the code is what makes that check a
// regression test rather than a coincidence.
//
// `stream` writes the lines with streaming stores (CopyAndRetagRange's
// StreamStoresForTable); each is a whole 64-byte line either way.
inline void ScatterBucketTags(uint8_t* bucket, const Layout& layout,
                              const RoutingIndexMap& map, size_t routed,
                              bool write_digit, __m512i* tags,
                              bool stream = false) {
  const size_t tag_bytes = layout.tag_bytes;
  uint8_t* const tag_base = bucket + layout.TagOffset() * kBucketCapacity;
  ApplyRoutingIndexMapToTags(map, tags);

  // Reversed order: byte tb goes to line tag_bytes-1-tb, so the bytes the
  // butterfly retires first end up last and pruning is a prefix (see the
  // Layout comment).  The digit is the most significant byte.
  //
  // Keeping all eight tag registers live across the bucket costs a handful
  // of L1-hot spill slots, because GCC hoists the eleven round keys into
  // registers.  Interleaving AES and scatter half a bucket at a time would
  // remove those spills, but the spills are cheaper than the shorter store
  // runs and extra loop overhead that interleaving costs.
  ForEachTagByteLine(
      tags, routed, write_digit ? tag_bytes - 1 : SIZE_MAX,
      [&](size_t tb, __m512i line) {
        uint8_t* const at = tag_base + (tag_bytes - 1 - tb) * kBucketCapacity;
        if (stream) {
          _mm512_stream_si512(reinterpret_cast<__m512i*>(at), line);
        } else {
          _mm512_storeu_si512(reinterpret_cast<void*>(at), line);
        }
      });
}

// The radix pass compares the most significant tag byte as a whole line after
// the butterfly, so it has to be written even when the butterfly itself does
// not reach that far up the tag.
inline bool RetagWritesDigitLine(const Layout& layout,
                                 const RoutingIndexMap& map, size_t routed) {
  return map.kind == TagMapKind::kRadixDigit && routed < layout.tag_bytes;
}

// The 64 raw AES tags of one bucket's keys, in registers: gather -> AES, with
// the keys never touching memory.  `wide_key` is `key_bytes > 8` hoisted by
// the caller, since it is a property of the layout and so a loop invariant.
inline void HashBucketKeys(const uint8_t* bucket, size_t key_bytes,
                           bool wide_key, uint64_t high_word,
                           const AesTagKeys& aes_keys, __m512i* tags) {
  __m512i keys[8];
  GatherBucketKeys(bucket, key_bytes, keys);
  if (wide_key) {
    __m512i keys_hi[8];
    GatherBucketKeyLines(bucket, 8, key_bytes, keys_hi);
    AesBatch64Regs(keys, keys_hi, high_word, tags, aes_keys);
  } else {
    AesBatch64Regs(keys, nullptr, high_word, tags, aes_keys);
  }
}

// Computes the routing tag of every slot of buckets [bucket_begin,
// bucket_end) (dummies included: the work is data-independent) and writes the
// bytes of map(tag) that `route_levels` will actually route into the bucket's
// tag byte lines.  tag_i = AesCtrTagU128WordsHost(nonce_lo, nonce_hi, key_i),
// which for a stored key of at most 8 bytes is AesCtrTagU64WordsHost.
// Buckets are independent, so disjoint ranges may be hashed concurrently.
//
// Gather -> AES -> scatter runs entirely in registers; the keys and tags
// never touch memory.  See GatherBucketKeys and AesBatch64Regs for why each
// phase looks the way it does.
inline void ComputeRoutingTagsRange(
    TableView t, uint64_t nonce_lo, uint64_t nonce_hi, size_t bucket_begin,
    size_t bucket_end, const RoutingIndexMap& map = {},
    unsigned route_levels = 0,
    const AesTagKeys& aes_keys = DefaultAesTagKeys()) {
  const uint64_t high_word = crypto::PackAesCtrHighWord(nonce_lo, nonce_hi);
  const size_t key_bytes = t.layout.key_bytes;
  const size_t bucket_bytes = t.layout.BucketBytes();
  const size_t routed = RoutedTagBytes(t.layout, route_levels);
  const bool write_digit = RetagWritesDigitLine(t.layout, map, routed);
  // Public (it is the layout), so hoisting the whole wide-key arm out of the
  // loop costs nothing and keeps the 8-byte path's register allocation.
  const bool wide_key = key_bytes > 8;

  for (size_t b = bucket_begin; b < bucket_end; ++b) {
    uint8_t* bucket = t.data + b * bucket_bytes;
    __m512i tags[8];
    HashBucketKeys(bucket, key_bytes, wide_key, high_word, aes_keys, tags);
    ScatterBucketTags(bucket, t.layout, map, routed, write_digit, tags);
  }
}

// ScatterDenseBucket AND the re-tag of its destinations, with one 64-lane
// hash of the SOURCE bucket instead of one per destination bucket.  A
// fanout-f scatter followed by ComputeRoutingTagsRange hashes f times as many
// lanes, most of them dummies past `per_bucket`.  Writes the same tag lines
// ComputeRoutingTagsRange would (the low `routed` bytes and the digit line
// when `write_digit`), so every occupied entry and every mask agree with that
// pair; only dummy lanes past `per_bucket` keep their stale tag bytes, which
// no kernel reads through a mask.  The work is a function of the layout
// alone: an empty source bucket is hashed all the same.
//
// The tag lines go from registers straight into their destination slots
// (ScatterDenseLine), and at fanout 1 the whole bucket is ScatterBucketTags'
// destination.
template <size_t Per>
inline void ScatterAndRetagDenseBucketFor(
    const uint8_t* source, uint64_t source_mask, uint8_t* dest_region,
    uint64_t* dest_masks, const Layout& layout, uint64_t high_word,
    const RoutingIndexMap& map, size_t routed, bool write_digit,
    const AesTagKeys& aes_keys) {
  __m512i tags[8];
  HashBucketKeys(source, layout.key_bytes, layout.key_bytes > 8, high_word,
                 aes_keys, tags);
  const size_t entry_bytes = layout.EntryBytes();
  ScatterDenseBucketFor<Per>(source, source_mask, dest_region, dest_masks,
                             entry_bytes, layout.PayloadLines());
  if constexpr (Per == kBucketCapacity) {
    ScatterBucketTags(dest_region, layout, map, routed, write_digit, tags);
  } else {
    ApplyRoutingIndexMapToTags(map, tags);
    const size_t tag_bytes = layout.tag_bytes;
    const size_t bucket_bytes = entry_bytes * kBucketCapacity;
    uint8_t* const dest_tags =
        dest_region + layout.TagOffset() * kBucketCapacity;
    ForEachTagByteLine(
        tags, routed, write_digit ? tag_bytes - 1 : SIZE_MAX,
        [&](size_t tb, __m512i line) {
          ScatterDenseLine<Per>(
              dest_tags + (tag_bytes - 1 - tb) * kBucketCapacity,
              bucket_bytes, line);
        });
  }
}

inline void ScatterAndRetagDenseBucket(
    const uint8_t* source, uint64_t source_mask, uint8_t* dest_region,
    uint64_t* dest_masks, size_t per_bucket, const Layout& layout,
    uint64_t high_word, const RoutingIndexMap& map, size_t routed,
    bool write_digit, const AesTagKeys& aes_keys) {
  WithDensePerBucket(per_bucket, [&](auto per) {
    ScatterAndRetagDenseBucketFor<decltype(per)::value>(
        source, source_mask, dest_region, dest_masks, layout, high_word, map,
        routed, write_digit, aes_keys);
  });
}

// THE DIGIT BYTE LINE ONE BUCKET WOULD HAVE after a re-tag under (nonce, map),
// computed without writing anything.
//
// The level arena's top compaction (levelarena DESIGN.md, "Top compaction
// and residuals") needs exactly this and nothing else from its incoming carry.  The carry is
// an immutable inbox table published under its producer's map, so the digit
// saying which of the top's D blocks each entry belongs to is not in its
// stored digit line -- but the merge kernel reads only that ONE line of the
// source's tag (MergeRadixLevelSourcesRange), and moves only PAYLOAD lines
// out of it (Layout::PayloadLines()).  So the whole re-tag reduces to this
// register, and no private one-bucket scratch copy is needed: there is nothing for the merge to read out of a copy that it
// does not read out of the carry itself.
//
// Byte for byte what ScatterBucketTags would have laid in the digit line,
// because it is the same map application and the same shift -- which is why
// both are their own functions above.  The caller normalizes it exactly as it
// normalizes a stored one (NormalizeDigitLine).
//
// Sound only under a SHARED NONCE FAMILY (the carry and its consuming merge
// share one; levelarena DESIGN.md, "Carries and preparation"): the
// recomputed hash is the
// hash the carry was already placed by, so the low log2(U) bits still name
// the bucket the entry is in and only the digit above them is new.
inline __m512i ComputeBucketDigitLine(
    const uint8_t* bucket, const Layout& layout, uint64_t nonce_lo,
    uint64_t nonce_hi, const RoutingIndexMap& map,
    const AesTagKeys& aes_keys = DefaultAesTagKeys()) {
  __m512i tags[8];
  HashBucketKeys(bucket, layout.key_bytes, layout.key_bytes > 8,
                 crypto::PackAesCtrHighWord(nonce_lo, nonce_hi), aes_keys,
                 tags);
  ApplyRoutingIndexMapToTags(map, tags);
  const unsigned shift = DigitTagByteShift(layout);
  for (int i = 0; i < 8; ++i) tags[i] = _mm512_srli_epi64(tags[i], shift);
  return LowByteLine(tags);
}

// THE WAY OF EACH OF A BUCKET'S 64 KEYS in a `ways`-way fixed merge: which of
// the `ways` destination blocks, all sharing the entry's low `carry_bits`
// index bits, the entry belongs to -- already normalized to [0, ways), one
// byte per lane.
//
// The fixed merge splits carry bucket i across C[i + q * 2^carry_bits] for
// q in [0, ways), and `ways` is what the two extents say (FixedMergeRadix),
// not what the map says.  The two agree in only one of two spellings:
//
//   - a whole-digit map, kRadixDigit(low_bits = carry_bits, modulus = ways),
//     where the way IS the stored digit;
//   - a kRaw map at a power-of-two `ways`, where the way is the raw tag's
//     bits [carry_bits, carry_bits + log2 ways) -- the level arena's BINARY
//     top, whose route reads those same bits as its last butterfly levels.
//
// One formula covers both, on the mapped word w with e = log2(ways / modulus):
//
//     way = ((w >> carry_bits) & (2^e - 1)) | (((w >> digit_shift) & 7) << e)
//
// which at e = 0 is the digit byte's three bits, i.e. byte for byte what
// ComputeBucketDigitLine + NormalizeDigitLine give, and at modulus 1 is the
// index bits alone.  Under a shared nonce family the recomputed hash is
// the hash the carry was placed by, so the low `carry_bits` still name the
// bucket the entry is in and only the way above them is new.
//
// Everything but the keys is fixed for a whole merge, so PlanBucketWay
// validates and derives it once (FixedMergeRetag holds the plan).
struct BucketWayPlan {
  uint64_t high_word = 0;  // PackAesCtrHighWord of the merge's nonce
  unsigned carry_bits = 0;
  unsigned ways = 1;
  unsigned way_bits = 0;     // e
  bool reads_digit = false;  // modulus > 1
};

inline BucketWayPlan PlanBucketWay(const RoutingIndexMap& map,
                                   uint64_t nonce_lo, uint64_t nonce_hi,
                                   unsigned carry_bits, unsigned ways) {
  const unsigned modulus =
      map.kind == TagMapKind::kRadixDigit ? map.modulus : 1u;
  if (ways == 0 || modulus == 0 || ways % modulus != 0 ||
      (ways / modulus) & ((ways / modulus) - 1)) {
    throw std::invalid_argument(
        "fixed merge: the fan-in is not the map's modulus times a power of "
        "two");
  }
  BucketWayPlan plan;
  plan.high_word = crypto::PackAesCtrHighWord(nonce_lo, nonce_hi);
  plan.carry_bits = carry_bits;
  plan.ways = ways;
  while ((modulus << (plan.way_bits + 1)) <= ways) ++plan.way_bits;
  plan.reads_digit = modulus > 1;
  return plan;
}

inline __m512i ComputeBucketWayLine(
    const uint8_t* bucket, const Layout& layout, const RoutingIndexMap& map,
    const BucketWayPlan& plan,
    const AesTagKeys& aes_keys = DefaultAesTagKeys()) {
  __m512i tags[8];
  HashBucketKeys(bucket, layout.key_bytes, layout.key_bytes > 8,
                 plan.high_word, aes_keys, tags);
  ApplyRoutingIndexMapToTags(map, tags);
  const __m128i carry_bits =
      _mm_cvtsi32_si128(static_cast<int>(plan.carry_bits));
  const __m128i digit_shift =
      _mm_cvtsi32_si128(static_cast<int>(map.digit_shift));
  const __m128i way_bits = _mm_cvtsi32_si128(static_cast<int>(plan.way_bits));
  const __m512i index_mask =
      _mm512_set1_epi64(static_cast<long long>(LowMask64(plan.way_bits)));
  const __m512i digit_mask = _mm512_set1_epi64(plan.reads_digit ? 7 : 0);
  for (int i = 0; i < 8; ++i) {
    const __m512i index_part =
        _mm512_and_si512(_mm512_srl_epi64(tags[i], carry_bits), index_mask);
    const __m512i digit_part = _mm512_sll_epi64(
        _mm512_and_si512(_mm512_srl_epi64(tags[i], digit_shift), digit_mask),
        way_bits);
    tags[i] = _mm512_or_si512(index_part, digit_part);
  }
  return LowByteLine(tags);
}

// Whether a write-once copy into `out` should use streaming (non-temporal)
// stores.  A cached store to a line not in cache first reads the line
// (read-for-ownership), so every byte a copy pass writes costs a DRAM read
// as well, and the written line then occupies L3 until it is evicted --
// displacing lines the request thread's cascade is about to probe, on a host
// where every core shares one L3.  A streaming store does neither.  It is
// wrong for a table small enough that the whole rebuild stays cache-resident:
// there the butterfly that follows the copy wants the lines it just wrote hot,
// and a streaming store hands them to DRAM instead.  The threshold is the
// per-core L2, read from the host once (1 MiB on Zen 5, 2 MiB on Granite
// Rapids); above it the copy pass alone cycles the L2 before the butterfly
// starts, so nothing is lost.  Defining CPU_BYTESLICE_STREAM_STORE_MIN_BYTES
// pins it at build time.
// PlanCopyThenRoute opts out through CopyAndRetagRange's cached_stores for
// each tile group: its butterfly consumes the written lines immediately,
// even when the full output table is much larger than this threshold.
inline size_t StreamStoreMinBytes() {
#ifdef CPU_BYTESLICE_STREAM_STORE_MIN_BYTES
  return static_cast<size_t>(CPU_BYTESLICE_STREAM_STORE_MIN_BYTES);
#else
  static const size_t bytes = HostLevel2CacheBytes();
  return bytes;
#endif
}

// Maximum output footprint of one copy-and-route tile group.  This limits
// producer/consumer distance, not the butterfly kernel's recursion or leaf
// size.  4 MiB leaves room in the shared L3 for the source and online probes
// while keeping copy waves several slices wide.  Zero disables fusion.
#ifndef CPU_BYTESLICE_FUSED_TILE_MAX_BYTES
#define CPU_BYTESLICE_FUSED_TILE_MAX_BYTES (size_t{4} << 20)
#endif
inline bool StreamStoresForTable(const TableView& out) {
  return out.num_buckets * out.layout.BucketBytes() >= StreamStoreMinBytes();
}

// Copy [dst_begin, dst_end) of `out` from `src` -- whose bucket i is out's
// bucket i + dst_offset -- AND tag it, in one pass over the data
// Byte for byte what a whole-
// bucket copy followed by ComputeRoutingTagsRange over the same range leaves
// behind, at less memory traffic:
//
//  - the tag byte lines the re-tag is about to write IN FULL are not copied.
//    Under the reversed tag byte order those are the LAST `routed` lines of
//    the entry, so "everything else" stays one contiguous prefix and the copy
//    stays one straight-line run of whole 64-byte lines.  (The digit line is
//    inside that prefix and is copied and then overwritten -- one line, and
//    splitting the run in two to save it costs more than it saves.)
//  - the key lines are read ONCE.  A separate re-tag pass has to stream them
//    back in to hash them, which at the deepest levels means reading the key
//    third of the table from DRAM a second time; here the copy's own loads
//    are what the transpose consumes.
//
// Ranges are independent, exactly as they would be for the two separate passes.
//
// `drop_unshadowed` is THE UNSHADOWED SKIP (kMetaUnshadowed in
// cpu_byteslice_meta.hpp): every byte of the source is
// copied whatever its meta byte says -- the work is fixed -- and only the
// DESTINATION's occupancy word loses the tombstones that shadow nothing.  `src`
// is a live, probeable table and is never written.
//
// IN PLACE: `src` may BE the destination range (the synchronous engine's
// tables grow inside one region, so an older operand already sits where the
// merge copies it; LevelMergeBinding::in_place).  Then the copy is the
// identity and only the tags and the unshadowed skip are written.  Whether it
// is in place is a comparison of public pointers.
inline void CopyAndRetagRange(
    TableView out, TableView src, size_t dst_begin, size_t dst_end,
    size_t dst_offset, uint64_t nonce_lo, uint64_t nonce_hi,
    const RoutingIndexMap& map = {}, unsigned route_levels = 0,
    const AesTagKeys& aes_keys = DefaultAesTagKeys(),
    bool cached_stores = false, bool drop_unshadowed = false) {
  if (dst_begin >= dst_end) return;
  const Layout& layout = out.layout;
  const uint64_t high_word = crypto::PackAesCtrHighWord(nonce_lo, nonce_hi);
  const size_t key_bytes = layout.key_bytes;
  const size_t bucket_bytes = layout.BucketBytes();
  const bool in_place = src.data + (dst_begin - dst_offset) * bucket_bytes ==
                        out.data + dst_begin * bucket_bytes;
  assert(in_place == (src.masks + (dst_begin - dst_offset) ==
                      out.masks + dst_begin));
  const size_t routed = RoutedTagBytes(layout, route_levels);
  const bool write_digit = RetagWritesDigitLine(layout, map, routed);
  const bool wide_key = key_bytes > 8;
  // Every line the tag scatter will not write in full.  It is always at least
  // the payload, since `routed` never exceeds tag_bytes -- which is what lets
  // the key lines below be both copied and hashed from one load.
  const size_t copy_lines = layout.EntryBytes() - routed;
  assert(copy_lines >= key_bytes);
  // Streaming stores for every line when the table is large
  // (StreamStoresForTable), the tag lines included: each is built whole in
  // registers.  The digit line is then skipped by the copy rather than
  // copied and overwritten: two stores to one line through the combining
  // buffer would otherwise rest on their ordering.
  const bool stream = !cached_stores && StreamStoresForTable(out);
  const size_t digit_line = write_digit ? layout.TagOffset() : SIZE_MAX;
  for (size_t b = dst_begin; b < dst_end; ++b) {
    const uint8_t* in = src.data + (b - dst_offset) * bucket_bytes;
    uint8_t* bucket = out.data + b * bucket_bytes;
    __m512i keys[8];
    __m512i keys_hi[8];
    __m512i tags[8];
    {
      // The key lines, loaded once and used twice: stored to the destination
      // and transposed into the AES input.  GatherBucketKeyLines' own zero
      // fill above key_bytes is reproduced here rather than reused, because
      // its loads are the ones this fusion exists to remove.
      __m512i lines[8];
      for (size_t i = 0; i < 8; ++i) {
        if (i >= key_bytes) {
          lines[i] = _mm512_setzero_si512();
          continue;
        }
        lines[i] = _mm512_load_si512(
            reinterpret_cast<const void*>(in + i * kBucketCapacity));
        if (in_place) continue;
        if (stream) {
          _mm512_stream_si512(
              reinterpret_cast<__m512i*>(bucket + i * kBucketCapacity),
              lines[i]);
        } else {
          _mm512_store_si512(
              reinterpret_cast<void*>(bucket + i * kBucketCapacity), lines[i]);
        }
      }
      TransposeKeyLinesToQwords(lines, keys);
      if (wide_key) {
        for (size_t i = 0; i < 8; ++i) {
          const size_t line = 8 + i;
          if (line >= key_bytes) {
            lines[i] = _mm512_setzero_si512();
            continue;
          }
          lines[i] = _mm512_load_si512(
              reinterpret_cast<const void*>(in + line * kBucketCapacity));
          if (in_place) continue;
          if (stream) {
            _mm512_stream_si512(
                reinterpret_cast<__m512i*>(bucket + line * kBucketCapacity),
                lines[i]);
          } else {
            _mm512_store_si512(
                reinterpret_cast<void*>(bucket + line * kBucketCapacity),
                lines[i]);
          }
        }
        TransposeKeyLinesToQwords(lines, keys_hi);
      }
    }
    AesBatch64Regs(keys, wide_key ? keys_hi : nullptr, high_word, tags,
                   aes_keys);
    // The rest of the prefix: value, meta, and any tag byte too high for this
    // rebuild to route (carried over stale, as a separate copy would).
    // Placed after the AES so the copy's loads and the encryption chains
    // overlap rather than queueing behind one another.
    if (in_place) {
      // Already there.
    } else if (stream) {
      for (size_t line = key_bytes; line < copy_lines; ++line) {
        if (line == digit_line) continue;  // the scatter writes it in full
        _mm512_stream_si512(
            reinterpret_cast<__m512i*>(bucket + line * kBucketCapacity),
            _mm512_load_si512(
                reinterpret_cast<const void*>(in + line * kBucketCapacity)));
      }
    } else {
      for (size_t line = key_bytes; line < copy_lines; ++line) {
        _mm512_store_si512(
            reinterpret_cast<void*>(bucket + line * kBucketCapacity),
            _mm512_load_si512(
                reinterpret_cast<const void*>(in + line * kBucketCapacity)));
      }
    }
    ScatterBucketTags(bucket, layout, map, routed, write_digit, tags, stream);
    // THE UNSHADOWED SKIP, inside the bucket's own pass: the meta line is one
    // of the `copy_lines` this iteration just moved, so it is still in L1.  A
    // trailing loop over [dst_begin, dst_end) would re-read a source that
    // at production sizes does not fit in any cache -- a second walk of the
    // table for one byte line in twenty-nine.  The occupancy word is written
    // here rather than by the block memcpy below, which is then skipped.
    if (drop_unshadowed) {
      out.masks[b] = src.masks[b - dst_offset];
      DropUnshadowedFromMask(in, &out.masks[b], layout.MetaLine());
    }
  }
  // Streaming stores are weakly ordered; fence them before the caller
  // publishes the range (under a mutex, but the argument should not rest on
  // that) or hands the stream to another worker.
  if (stream) _mm_sfence();
  // The masks, unless the loop above already wrote them one at a time because
  // it was also dropping unshadowed tombstones, or they are already there.
  if (!drop_unshadowed && !in_place) {
    std::memcpy(out.masks + dst_begin, src.masks + (dst_begin - dst_offset),
                (dst_end - dst_begin) * sizeof(uint64_t));
  }
}

inline void ComputeRoutingTags(
    TableView t, uint64_t nonce_lo, uint64_t nonce_hi,
    const RoutingIndexMap& map = {}, unsigned route_levels = 0,
    const AesTagKeys& aes_keys = DefaultAesTagKeys()) {
  ComputeRoutingTagsRange(t, nonce_lo, nonce_hi, 0, t.num_buckets, map,
                          route_levels, aes_keys);
}

inline void ComputeRoutingTags(Table& t, uint64_t nonce_lo,
                               uint64_t nonce_hi) {
  ComputeRoutingTags(View(t), nonce_lo, nonce_hi);
}

// ---------------------------------------------------------------------------
// Nonce identity
// ---------------------------------------------------------------------------
//
// The effective nonce is the 64-bit word crypto::PackAesCtrHighWord builds:
//
//     domain bit (1) | rebuild epoch (48, monotone) | target level (15)
//
// It is ALLOCATED, not sampled.  Sampling it (e.g. from a SplitMix64
// generator) would give two rebuilds a ~2^-11 chance of sharing a hash function outright over a
// 2^32-access lifetime -- and with a fixed generator seed that is not a
// probability but a fixed property of the build -- which is exactly the
// across-rebuild nonce reuse this whole scheme forbids.  A monotone epoch
// makes the
// collision impossible instead of unlikely, at the cost of a completely public
// nonce; that cost is paid by making the PRF key per-ORAM and secret
// (crypto::SecretKeySeed, threaded in as AesTagKeys above).  The two halves are
// a package: a public nonce under a public key is a plaintext trace.
//
// A rebuild draws ONE epoch and gets two nonces from it, real and dummy, that
// differ only in the domain bit -- and one `family_id`, which is the security
// boundary the probe audit keys on: every temporary T_j of one
// incremental rebuild, and the resident level its last member becomes, share
// the nonce and therefore the family.
struct RebuildNonce {
  uint64_t family_id = 0;
  uint64_t epoch = 0;
  unsigned target_level = 0;
  uint64_t real_lo = 0, real_hi = 0;
  uint64_t dummy_lo = 0, dummy_hi = 0;
  uint64_t real_high = 0;   // PackAesCtrHighWord(real_lo, real_hi)
  uint64_t dummy_high = 0;  // ... of the dummy nonce
};

class NonceAllocator {
 public:
  // Refuse to run rather than wrap.  Both bounds are astronomically far
  // away (2^48 rebuilds), which is the point -- the check is what turns "the
  // nonce is unique" from a probability into a property.
  static constexpr uint64_t kMaxEpoch = crypto::kAesCtrCounterMask;

  RebuildNonce Allocate(unsigned target_level) {
    if (epoch_ >= kMaxEpoch) {
      throw std::runtime_error("rebuild epoch exhausted: refusing to reuse a "
                               "nonce family");
    }
    if (target_level > crypto::kAesCtrLevelMask) {
      throw std::invalid_argument("target level does not fit the nonce's "
                                  "level field");
    }
    RebuildNonce n;
    n.family_id = ++next_family_;
    n.epoch = ++epoch_;
    n.target_level = target_level;
    // PackAesCtrHighWord takes the domain bit and the level from `lo` and the
    // epoch from `hi`, so the split below IS the layout above.
    n.real_lo = target_level;
    n.real_hi = n.epoch;
    n.dummy_lo = target_level | crypto::kAesCtrDomainBit;
    n.dummy_hi = n.epoch;
    n.real_high = crypto::PackAesCtrHighWord(n.real_lo, n.real_hi);
    n.dummy_high = crypto::PackAesCtrHighWord(n.dummy_lo, n.dummy_hi);
    return n;
  }

  uint64_t Epoch() const { return epoch_; }
  uint64_t FamiliesAllocated() const { return next_family_; }

 private:
  uint64_t epoch_ = 0;
  uint64_t next_family_ = 0;
};

}  // namespace byteslice
}  // namespace microram
