#pragma once

// All-pairs key equality between two byte-sliced buckets, and within one.
//
// The rebuild has to find duplicate keys, and both operands are
// 64-slot buckets, so the question is always "which of these 64 keys equal
// which of those 64" -- 4096 comparisons -- reduced to a 64-bit mask.
//
// The primitive is AVX512_VP2INTERSECT, which takes two vectors of 8 qwords (or
// 16 dwords) and returns, for each element of the second, whether it appears in
// the first.  Sixty-four keys is eight such vectors per side, so an all-pairs
// mask is 8x8 = 64 intersect instructions on register-resident operands.  The
// keys themselves come from a transpose: byte line l holds key byte l of all 64
// entries, so four or eight lines transpose into 64 packed keys without
// touching memory.
//
// VP2INTERSECT is native on Zen 5 and microcoded on Tiger Lake; Zen 4 and the
// Intel server parts lack it.  Where it is absent the all-pairs kernels take
// an xor + unsigned-min fallback over the same registers
// (AllPairsMatchMaskQFallback), correct on any AVX-512F host and several
// times the native instruction's cost where both are available.
//
// WIDE KEYS. Both qwords are compared against the SAME partner before any
// membership reduction. Synchronized rotations cover every partner; the OR
// of the two XORs is zero exactly for a complete stored-key match. This path
// does not use VP2INTERSECT, which discards the partner identity.  Where
// kWideKeySegmentMatch is on, a 16-byte key instead ANDs four 32-bit segment
// matches (VP2INTERSECTD), which is approximate; see WideSegmentMatchMask.
//
// ZERO KEYS.  Dummy slots hold don't-care bytes that read as zero after
// masking, and zero equals zero, so every dummy would match every other dummy.
// LoadKeyLinesZeroingDummies and RepairZeroKeyMatches exist to keep those out
// of the mask without branching on which slots are real.

#include <immintrin.h>

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <cstdint>

#include "src/core/mov_intrinsics.hpp"

#include "src/oram/rebuild/cpu_byteslice_compare_count.hpp"

#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/table/cpu_byteslice_key_intersect.hpp"

namespace microram {
namespace byteslice {

// ---------------------------------------------------------------------------
// All-pairs key equality
// ---------------------------------------------------------------------------
//
// 64 keys against 64 keys is 4096 equalities.  VP2INTERSECTQ does 8x8 = 64 of
// them per instruction and returns both reduced masks; only the second
// operand's (k2) is wanted here, since duplicates are dropped from the older
// bucket.  Eight registers a side => 64 instructions for 8-byte keys; at 4
// bytes the same registers hold 16 keys each, so it is 4x4 = 16 VP2INTERSECTD.
//
// The keys never round-trip through memory the way a scalar gather would: the
// transposed registers of both sides are what the nest reads, with GCC
// spilling and reloading some of them through L1 around the 64 intersects.
// The nest is `b`-major with a mask-register accumulator; see
// AllPairsMatchMaskQ for why the `a`-major form with a 64-bit accumulator
// compiled worse.

// dup bit e = 1 iff key b[e] equals some key in a (all 64 lanes of each side).
//
// The nest is b-register major, accumulating the eight a-side answers for one
// b register in ONE mask register before it leaves for the scalar word.  The
// obvious a-major form with a 64-bit accumulator compiles (GCC 15, -O3) to a
// kmovb of every intersect result onto the stack, a reload, a shift and an
// or -- some 200 scalar instructions around 64 VP2INTERSECTQ -- because the
// per-pair widening has nowhere to live in the eight mask registers while
// the second intersect output is also being written.  This form keeps one
// accumulator and the two intersect outputs live, ORs in the mask domain, and
// widens once per b register, which removes most of those scalar round trips.
//
// Without VP2INTERSECT the answer comes from AllPairsMatchMaskQFallback below.

// Where one b register's answer lands in the slot-order result.  A b side from
// TransposeKeyLinesToQwords holds slots 8j..8j+7 in register j; one straight
// from UnpackKeyLinesToQwords (`Unpacked`) holds slot 16q+2j+t in qword 2q+t,
// which PDEP with a constant mask spreads back out, saving the b side's 16
// lane-fix shuffles.  The a side is only ever read as a set, so its register
// order never matters.
template <bool Unpacked>
INLINE uint64_t PlaceMatchesQ(uint32_t acc, int j) {
  return Unpacked ? _pdep_u64(acc, 0x0003000300030003ull) << (2 * j)
                  : static_cast<uint64_t>(acc) << (8 * j);
}

// The same for sixteen dwords: UnpackKeyLinesToDwords holds slot 16q+4j+t in
// dword 4q+t of register j.
template <bool Unpacked>
INLINE uint64_t PlaceMatchesD(uint32_t acc, int j) {
  return Unpacked ? _pdep_u64(acc, 0x000F000F000F000Full) << (4 * j)
                  : static_cast<uint64_t>(acc) << (16 * j);
}

// The fallback for hosts without VP2INTERSECT.  It uses AVX-512F only and is
// compiled on every host, so the tests check it on a VP2INTERSECT machine too.
//
// Two keys are equal iff their XOR is zero.  Comparing b against the eight lane
// rotations of each a register covers all 64 pairs of a register pair, and the
// UNSIGNED minimum of those XORs is zero in lane e exactly when b[e] equals
// some key of a.  So each b register gets one vector accumulator, and it is
// reduced to a mask once, at the end: eight accumulators, the eight b
// registers and the rotating a register, 17 of the 32.  The alternative --
// a rotate-and-compare that makes one comparison mask per register pair --
// moves every mask through a scalar register (kmov, shift, or): 512 round
// trips for 8-byte keys, against none here.
// cpu_byteslice_dedup_kernel_benchmark times this form against the native
// one on the host at hand.
//
// The minimum has to be unsigned.  A signed minimum lets the XOR of two keys
// that differ only in the top bit, which is negative, beat a genuine zero.
template <bool Unpacked = false>
INLINE uint64_t AllPairsMatchMaskQFallback(const __m512i* a, const __m512i* b) {
  __m512i acc[8];
  for (int j = 0; j < 8; ++j) acc[j] = _mm512_set1_epi64(-1);
  for (int i = 0; i < 8; ++i) {
    __m512i ai = a[i];
    for (int r = 0; r < 8; ++r) {
      for (int j = 0; j < 8; ++j) {
        acc[j] = _mm512_min_epu64(acc[j], _mm512_xor_si512(ai, b[j]));
      }
      ai = _mm512_alignr_epi64(ai, ai, 1);  // lane k <- lane k + 1 (mod 8)
    }
  }
  uint64_t dup = 0;
  for (int j = 0; j < 8; ++j) {
    dup |= PlaceMatchesQ<Unpacked>(core::obliTestNMask64(acc[j], acc[j]), j);
  }
  return dup;
}

// 32-bit twin: four registers of sixteen keys a side and sixteen rotations.
template <bool Unpacked = false>
INLINE uint64_t AllPairsMatchMaskDFallback(const __m512i* a, const __m512i* b) {
  __m512i acc[4];
  for (int j = 0; j < 4; ++j) acc[j] = _mm512_set1_epi32(-1);
  for (int i = 0; i < 4; ++i) {
    __m512i ai = a[i];
    for (int r = 0; r < 16; ++r) {
      for (int j = 0; j < 4; ++j) {
        acc[j] = _mm512_min_epu32(acc[j], _mm512_xor_si512(ai, b[j]));
      }
      ai = _mm512_alignr_epi32(ai, ai, 1);  // lane k <- lane k + 1 (mod 16)
    }
  }
  uint64_t dup = 0;
  for (int j = 0; j < 4; ++j) {
    dup |= PlaceMatchesD<Unpacked>(core::obliTestNMask32(acc[j], acc[j]), j);
  }
  return dup;
}

template <bool Unpacked = false>
INLINE uint64_t AllPairsMatchMaskQ(const __m512i* a, const __m512i* b) {
  CountCompare(CompareKind::kPairQ);
#if MICRORAM_BYTESLICE_USE_VP2INTERSECT
  uint64_t dup = 0;
  for (int j = 0; j < 8; ++j) {
    __mmask8 acc = 0;
    for (int i = 0; i < 8; ++i) {
      acc = _kor_mask8(acc, IntersectSecondMaskQ(a[i], b[j]));
    }
    dup |= PlaceMatchesQ<Unpacked>(_cvtmask8_u32(acc), j);
  }
  return dup;
#else
  return AllPairsMatchMaskQFallback<Unpacked>(a, b);
#endif
}

template <bool Unpacked = false>
INLINE uint64_t AllPairsMatchMaskD(const __m512i* a, const __m512i* b) {
  CountCompare(CompareKind::kPairD);
#if MICRORAM_BYTESLICE_USE_VP2INTERSECT
  // b-major with a mask-register accumulator, as the qword form above.
  uint64_t dup = 0;
  for (int j = 0; j < 4; ++j) {
    __mmask16 acc = 0;
    for (int i = 0; i < 4; ++i) {
      acc = _kor_mask16(acc, IntersectSecondMaskD(a[i], b[j]));
    }
    dup |= PlaceMatchesD<Unpacked>(_cvtmask16_u32(acc), j);
  }
  return dup;
#else
  return AllPairsMatchMaskDFallback<Unpacked>(a, b);
#endif
}

// ---------------------------------------------------------------------------
// Cross-bucket deduplication
// ---------------------------------------------------------------------------

// Repairs a raw all-pairs result into the answer for one key FIELD (a whole
// key, or one 32-bit segment of a wide one).
//
// LoadKeyLinesZeroingDummies collapses `first`'s dummy lanes onto 0, so the
// value set the intersection sees is {first's real values} u {0}.  The raw
// result is therefore exact for every nonzero value, and every real
// zero-valued slot of `second` matches unconditionally; those lanes are
// overridden with "does `first` really hold a zero there".  An entirely dummy
// `first` falls out of the same rule (zero_first == 0 => no match anywhere).
// Nothing here branches on a secret: the masks feed blends and scalar bit ops
// only.
inline uint64_t RepairZeroKeyMatches(uint64_t raw, uint64_t zero_first,
                                     uint64_t zero_second,
                                     uint64_t second_real) {
  const uint64_t zero_hit = uint64_t{0} - static_cast<uint64_t>(zero_first != 0);
  return ((raw & ~zero_second) | (zero_second & zero_hit)) & second_real;
}

// One 32-bit key field: byte lines [0, field_bytes) of the two buckets, which
// the caller offsets to the segment it wants.  16 VP2INTERSECTD.
//
// Only `first` is read as a set, so only its dummies are zeroed: `second`'s
// lanes are all ANDed with second_real by RepairZeroKeyMatches, whatever bytes
// its dummies hold.  Neither side needs the lane fix (PlaceMatchesD).
// Force-inlined with the public width constant (CrossBucketDuplicateMaskAt),
// so the loads and the transposes fold into straight-line code.
INLINE uint64_t CrossBucketFieldMatchMaskD(const uint8_t* first,
                                           uint64_t first_real,
                                           const uint8_t* second,
                                           uint64_t second_real,
                                           size_t field_bytes) {
  __m512i fl[4], sl[4];
  const uint64_t zero_first =
      LoadKeyLinesZeroingDummies(first, field_bytes, first_real, 4, fl);
  const uint64_t zero_second =
      LoadKeyLinesKeepingDummies(second, field_bytes, second_real, 4, sl);
  __m512i a[4], b[4];
  UnpackKeyLinesToDwords(fl, a);
  UnpackKeyLinesToDwords(sl, b);
  return RepairZeroKeyMatches(AllPairsMatchMaskD<true>(a, b), zero_first,
                              zero_second, second_real);
}

// One 64-bit key field.  64 VP2INTERSECTQ.
INLINE uint64_t CrossBucketFieldMatchMaskQ(const uint8_t* first,
                                           uint64_t first_real,
                                           const uint8_t* second,
                                           uint64_t second_real,
                                           size_t field_bytes) {
  __m512i fl[8], sl[8];
  const uint64_t zero_first =
      LoadKeyLinesZeroingDummies(first, field_bytes, first_real, 8, fl);
  const uint64_t zero_second =
      LoadKeyLinesKeepingDummies(second, field_bytes, second_real, 8, sl);
  __m512i a[8], b[8];
  UnpackKeyLinesToQwords(fl, a);
  UnpackKeyLinesToQwords(sl, b);
  return RepairZeroKeyMatches(AllPairsMatchMaskQ<true>(a, b), zero_first,
                              zero_second, second_real);
}

// The public key widths the dedup entry points specialize on: 4 and 8 are the
// single-field narrow keys, 16 a rehashed wide key (StoredKeyBytes).  K = 0 is
// every other width, read at run time.  The width is public, so branching on
// it once at the entry is free, and each body is straight-line code with no
// width tests inside the nest.
template <size_t K>
INLINE size_t DedupKeyWidth(size_t key_bytes) {
  static_assert(K == 0 || K == 4 || K == 8 || K == 16, "specialized widths");
  return K != 0 ? K : key_bytes;
}

// Slot-ordered qwords, with absent high bytes padded by zero. The zero mask
// covers the COMPLETE key: a real key with just one zero half is not a dummy.
struct WideDedupKeys {
  __m512i lo[8], hi[8];
  uint64_t zero;
};

template <bool ZeroDummies>
INLINE WideDedupKeys LoadWideDedupKeys(const uint8_t* bucket, uint64_t real,
                                      size_t width) {
  assert(width > 8 && width <= kMaxKeyBytes);
  WideDedupKeys keys;
  __m512i lines[8];
  const uint64_t lo_zero = LoadKeyLinesMaskingZeros<ZeroDummies>(
      bucket, 8, real, 8, lines);
  TransposeKeyLinesToQwords(lines, keys.lo);
  const uint64_t hi_zero = LoadKeyLinesMaskingZeros<ZeroDummies>(
      bucket + 8 * kBucketCapacity, width - 8, real, 8, lines);
  TransposeKeyLinesToQwords(lines, keys.hi);
  keys.zero = lo_zero & hi_zero;
  return keys;
}

// Bit 8*j+t is set iff some complete key in a equals b[j][t]. At rotation r,
// both a halves in lane t belong to slot 8*i + (t+r)%8. Reducing each half
// separately would lose that identity. Unsigned minimum preserves a zero
// score even when another score has its high bit set.
INLINE uint64_t AllPairsMatchMaskWide(const WideDedupKeys& a,
                                     const WideDedupKeys& b) {
  CountCompare(CompareKind::kPairWide);
  __m512i acc[8];
  for (int j = 0; j < 8; ++j) acc[j] = _mm512_set1_epi64(-1);
  for (int i = 0; i < 8; ++i) {
    __m512i lo = a.lo[i], hi = a.hi[i];
    for (int r = 0; r < 8; ++r) {
      for (int j = 0; j < 8; ++j) {
        const __m512i diff = _mm512_or_si512(
            _mm512_xor_si512(lo, b.lo[j]), _mm512_xor_si512(hi, b.hi[j]));
        acc[j] = _mm512_min_epu64(acc[j], diff);
      }
      lo = _mm512_alignr_epi64(lo, lo, 1);
      hi = _mm512_alignr_epi64(hi, hi, 1);
    }
  }
  uint64_t dup = 0;
  for (int j = 0; j < 8; ++j) {
    dup |= core::obliTestNMask64(acc[j], acc[j]) << (8 * j);
  }
  return dup;
}

INLINE uint64_t CrossBucketWideMatchMask(const uint8_t* first,
                                        uint64_t first_real,
                                        const uint8_t* second,
                                        uint64_t second_real, size_t width) {
  const auto a = LoadWideDedupKeys<true>(first, first_real, width);
  const auto b = LoadWideDedupKeys<false>(second, second_real, width);
  return RepairZeroKeyMatches(AllPairsMatchMaskWide(a, b), a.zero, b.zero,
                              second_real);
}

// The kWideKeySegmentMatch form of a 16-byte comparison: each 32-bit segment
// is matched on its own (16 VP2INTERSECTD) and the four answers are ANDed.
// That says "every segment of this key occurs somewhere in the other bucket",
// which a slot can satisfy through four DIFFERENT partners, so it is not the
// exact predicate.  Stored keys this wide are always AES outputs under a
// secret schedule, so with at most 64 partners a segment collides with
// probability <= 2^-26 and all four with <= 2^-104 per slot and comparison;
// the caller budgets that over its comparisons.  The four answers are each
// zero-repaired before the AND, as one-field keys are.
INLINE uint64_t WideSegmentMatchMask(const uint8_t* first, uint64_t first_real,
                                     const uint8_t* second,
                                     uint64_t second_real) {
  uint64_t dup = second_real;
  for (size_t off = 0; off < kMaxKeyBytes; off += 4) {
    dup &= CrossBucketFieldMatchMaskD(first + off * kBucketCapacity, first_real,
                                      second + off * kBucketCapacity,
                                      second_real, 4);
  }
  return dup;
}

template <size_t K>
INLINE uint64_t CrossBucketDuplicateMaskAt(const uint8_t* first,
                                           uint64_t first_real,
                                           const uint8_t* second,
                                           uint64_t second_real,
                                           size_t key_bytes) {
  const size_t width = DedupKeyWidth<K>(key_bytes);
  if (width <= 4) {
    return CrossBucketFieldMatchMaskD(first, first_real, second, second_real,
                                      width);
  }
  if (width <= 8) {
    return CrossBucketFieldMatchMaskQ(first, first_real, second, second_real,
                                      width);
  }
  if (kWideKeySegmentMatch && width == kMaxKeyBytes) {
    return WideSegmentMatchMask(first, first_real, second, second_real);
  }
  return CrossBucketWideMatchMask(first, first_real, second, second_real,
                                  width);
}

// Returns the slot mask of `second`'s REAL entries whose key also occurs among
// `first`'s REAL entries.  `first` is the fresher source, so these are the
// copies the rebuild must drop.  Reads only the two buckets' key byte lines and
// writes to neither bucket.
//
// All stored widths 1..16 use exact equality, independently of the key's
// origin or distribution, except width 16 under kWideKeySegmentMatch
// (WideSegmentMatchMask). Normalization collisions are a separate concern.
inline uint64_t CrossBucketDuplicateMask(const uint8_t* first,
                                         uint64_t first_real,
                                         const uint8_t* second,
                                         uint64_t second_real,
                                         size_t key_bytes) {
  assert(key_bytes >= 1 && key_bytes <= kMaxKeyBytes);
  switch (key_bytes) {
    case 4:
      return CrossBucketDuplicateMaskAt<4>(first, first_real, second,
                                           second_real, key_bytes);
    case 8:
      return CrossBucketDuplicateMaskAt<8>(first, first_real, second,
                                           second_real, key_bytes);
    case 16:
      return CrossBucketDuplicateMaskAt<16>(first, first_real, second,
                                            second_real, key_bytes);
    default:
      return CrossBucketDuplicateMaskAt<0>(first, first_real, second,
                                           second_real, key_bytes);
  }
}

// A public tuple/merge compares the same immutable fresher bucket against
// several destinations. Retain its decoded keys across that run. The current
// destination mask is loaded on every comparison; no candidate mask is cached.
// The unpacked registers and the kept dummies are those of
// CrossBucketFieldMatchMaskQ / D.
template <bool Qwords>
INLINE void DedupBucketDestinationsNarrow(
    const uint8_t* first, uint64_t first_real, uint8_t* const* destinations,
    uint64_t* const* masks, size_t count, size_t key_bytes) {
  constexpr size_t n = Qwords ? 8 : 4;
  __m512i lines[n], keys[n];
  const uint64_t zero = LoadKeyLinesZeroingDummies(first, key_bytes,
                                                  first_real, n, lines);
  if constexpr (Qwords) UnpackKeyLinesToQwords(lines, keys);
  else UnpackKeyLinesToDwords(lines, keys);
  for (size_t q = 0; q < count; ++q) {
    __m512i other_lines[n], other_keys[n];
    const uint64_t real = *masks[q];
    const uint64_t other_zero = LoadKeyLinesKeepingDummies(
        destinations[q], key_bytes, real, n, other_lines);
    if constexpr (Qwords) UnpackKeyLinesToQwords(other_lines, other_keys);
    else UnpackKeyLinesToDwords(other_lines, other_keys);
    const uint64_t raw = Qwords ? AllPairsMatchMaskQ<true>(keys, other_keys)
                                : AllPairsMatchMaskD<true>(keys, other_keys);
    *masks[q] &= ~RepairZeroKeyMatches(raw, zero, other_zero, real);
  }
}

// Retain both source qwords across destinations. Destination occupancy is
// read afresh in destination order (including if mask pointers alias).
INLINE void DedupBucketDestinationsWide(
    const uint8_t* first, uint64_t first_real, uint8_t* const* destinations,
    uint64_t* const* masks, size_t count) {
  if constexpr (kWideKeySegmentMatch) {
    // WideSegmentMatchMask with the source's four segments retained.
    __m512i keys[4][4];
    uint64_t zero[4];
    for (size_t f = 0; f < 4; ++f) {
      __m512i lines[4];
      zero[f] = LoadKeyLinesZeroingDummies(first + f * 4 * kBucketCapacity,
                                           4, first_real, 4, lines);
      UnpackKeyLinesToDwords(lines, keys[f]);
    }
    for (size_t q = 0; q < count; ++q) {
      const uint64_t real = *masks[q];
      uint64_t dup = real;
      for (size_t f = 0; f < 4; ++f) {
        __m512i lines[4], other[4];
        const uint64_t other_zero = LoadKeyLinesKeepingDummies(
            destinations[q] + f * 4 * kBucketCapacity, 4, real, 4, lines);
        UnpackKeyLinesToDwords(lines, other);
        dup &= RepairZeroKeyMatches(AllPairsMatchMaskD<true>(keys[f], other),
                                    zero[f], other_zero, real);
      }
      *masks[q] &= ~dup;
    }
    return;
  }
  const auto a = LoadWideDedupKeys<true>(first, first_real, 16);
  for (size_t q = 0; q < count; ++q) {
    const uint64_t real = *masks[q];
    const auto b = LoadWideDedupKeys<false>(destinations[q], real, 16);
    const uint64_t dup = RepairZeroKeyMatches(
        AllPairsMatchMaskWide(a, b), a.zero, b.zero, real);
    *masks[q] &= ~dup;
  }
}

// One destination is the retained form's first iteration, so it takes that
// form too: one nest per width instead of two.
template <size_t K>
INLINE void DedupBucketDestinationsAt(
    const uint8_t* first, uint64_t first_real, uint8_t* const* destinations,
    uint64_t* const* masks, size_t count, size_t key_bytes) {
  const size_t width = DedupKeyWidth<K>(key_bytes);
#if !(defined(__MINGW32__) && __GNUC__ <= 13)
  if (width <= 4) {
    DedupBucketDestinationsNarrow<false>(first, first_real, destinations,
                                         masks, count, width);
    return;
  }
  if (width <= 8) {
    DedupBucketDestinationsNarrow<true>(first, first_real, destinations,
                                        masks, count, width);
    return;
  }
  if (width == 16) {
    DedupBucketDestinationsWide(first, first_real, destinations, masks, count);
    return;
  }
#endif
  for (size_t q = 0; q < count; ++q) {
    *masks[q] &= ~CrossBucketDuplicateMaskAt<K>(
        first, first_real, destinations[q], *masks[q], width);
  }
}

inline void DedupBucketDestinations(
    const uint8_t* first, uint64_t first_real, uint8_t* const* destinations,
    uint64_t* const* masks, size_t count, size_t key_bytes) {
  assert(key_bytes >= 1 && key_bytes <= kMaxKeyBytes);
  switch (key_bytes) {
    case 4:
      DedupBucketDestinationsAt<4>(first, first_real, destinations, masks,
                                   count, key_bytes);
      return;
    case 8:
      DedupBucketDestinationsAt<8>(first, first_real, destinations, masks,
                                   count, key_bytes);
      return;
    case 16:
      DedupBucketDestinationsAt<16>(first, first_real, destinations, masks,
                                    count, key_bytes);
      return;
    default:
      DedupBucketDestinationsAt<0>(first, first_real, destinations, masks,
                                   count, key_bytes);
      return;
  }
}

// ---------------------------------------------------------------------------
// Class-marked cross-bucket deduplication (the merged residual offer)
// ---------------------------------------------------------------------------
//
// The merged second chance (kClassMark in cpu_byteslice_second_chance.hpp)
// routes BOTH of a step's residual classes through one range table, so its
// offer needs two answers per (main bucket, range bucket) pair:
//
//   *first_dup   `first`'s real lanes whose key occurs among `second`'s
//                TIER-class lanes -- the stale table copies the tier's
//                kResidualWins absorption clears;
//   *carry_dup   `second`'s CARRY-class lanes whose key occurs in `first` --
//                the candidates the table's fresher copy consumes under
//                kTableWins.
//
// Load and transpose each side once, then select each candidate class in
// packed-key registers. The zero-key masks must be split by class too:
// zeroing an excluded lane must not invent a real zero key in that class.
// Keep the two-call fallback for MinGW GCC <= 13, whose register allocator
// has hit an internal error on shared-transpose intersect nests.
//
// `second` is the set side of the first answer only through `selected`, which
// keeps its tier lanes, and the element side of the second, which is ANDed
// with carry_real; so, as in CrossBucketFieldMatchMaskQ, its dummies are not
// zeroed and both sides stay in unpacked register order.  `selected` then
// needs tier_real in that order too: register j of the unpacked qwords holds
// slots 16q+2j+t in qword 2q+t, which PEXT gathers out of tier_real (and
// 16q+4j+t in dword 4q+t for dwords), the inverse of PlaceMatchesQ / D.
template <bool Qwords>
INLINE void CrossBucketClassFieldMasks(const uint8_t* first,
                                       uint64_t first_real,
                                       const uint8_t* second,
                                       uint64_t carry_real, uint64_t tier_real,
                                       size_t field_bytes,
                                       uint64_t* first_dup,
                                       uint64_t* carry_dup) {
  constexpr size_t n = Qwords ? 8 : 4;
  __m512i fl[n], sl[n], a[n], b[n], selected[n];
  const uint64_t zero_first =
      LoadKeyLinesZeroingDummies(first, field_bytes, first_real, n, fl);
  const uint64_t zero_second = LoadKeyLinesKeepingDummies(
      second, field_bytes, carry_real | tier_real, n, sl);
  if constexpr (Qwords) {
    UnpackKeyLinesToQwords(fl, a);
    UnpackKeyLinesToQwords(sl, b);
  } else {
    UnpackKeyLinesToDwords(fl, a);
    UnpackKeyLinesToDwords(sl, b);
  }
  // `tier_real` is secret: the register-only moves (into zero), because a
  // Granite Rapids build read the spilled b[i] from memory under it.
  for (size_t j = 0; j < n; ++j) {
    if constexpr (Qwords) {
      selected[j] = core::obliMaskMov64(
          _mm512_setzero_si512(),
          _pext_u64(tier_real >> (2 * j), 0x0003000300030003ull), b[j]);
    } else {
      selected[j] = core::obliMaskMov32(
          _mm512_setzero_si512(),
          _pext_u64(tier_real >> (4 * j), 0x000F000F000F000Full), b[j]);
    }
  }
  const uint64_t hit_first = Qwords ? AllPairsMatchMaskQ<true>(selected, a)
                                   : AllPairsMatchMaskD<true>(selected, a);
  *first_dup = RepairZeroKeyMatches(hit_first, zero_second & tier_real,
                                    zero_first, first_real);
  // The second output is restricted to carry_real after the comparison;
  // the tier lanes in b cannot affect whether a carry lane matches a.
  const uint64_t hit_carry = Qwords ? AllPairsMatchMaskQ<true>(a, b)
                                   : AllPairsMatchMaskD<true>(a, b);
  *carry_dup = RepairZeroKeyMatches(hit_carry, zero_first,
                                    zero_second & carry_real, carry_real);
}

template <size_t K>
INLINE void CrossBucketClassDuplicateMasksAt(const uint8_t* first,
                                             uint64_t first_real,
                                             const uint8_t* second,
                                             uint64_t carry_real,
                                             uint64_t tier_real,
                                             size_t key_bytes,
                                             uint64_t* first_dup,
                                             uint64_t* carry_dup) {
  const size_t width = DedupKeyWidth<K>(key_bytes);
#if !(defined(__MINGW32__) && __GNUC__ <= 13)
  if (width <= 8) {
    if (width <= 4) {
      CrossBucketClassFieldMasks<false>(first, first_real, second, carry_real,
                                        tier_real, width, first_dup,
                                        carry_dup);
    } else {
      CrossBucketClassFieldMasks<true>(first, first_real, second, carry_real,
                                       tier_real, width, first_dup,
                                       carry_dup);
    }
    return;
  }
  if (kWideKeySegmentMatch && width == kMaxKeyBytes) {
    // Share both transposes per segment. Keep the two class answers apart
    // until all four are ANDed: a segment may match a different partner, but
    // never one of the other class.
    uint64_t first_match = first_real, carry_match = carry_real;
    for (size_t off = 0; off < kMaxKeyBytes; off += 4) {
      uint64_t first_field, carry_field;
      CrossBucketClassFieldMasks<false>(
          first + off * kBucketCapacity, first_real,
          second + off * kBucketCapacity, carry_real, tier_real, 4,
          &first_field, &carry_field);
      first_match &= first_field;
      carry_match &= carry_field;
    }
    *first_dup = first_match;
    *carry_dup = carry_match;
    return;
  }
  const auto a = LoadWideDedupKeys<true>(first, first_real, width);
  const auto b = LoadWideDedupKeys<false>(
      second, carry_real | tier_real, width);
  WideDedupKeys tier;
  for (int j = 0; j < 8; ++j) {
    const uint64_t lanes = (tier_real >> (8 * j)) & 0xff;
    tier.lo[j] = core::obliMaskMov64(_mm512_setzero_si512(), lanes, b.lo[j]);
    tier.hi[j] = core::obliMaskMov64(_mm512_setzero_si512(), lanes, b.hi[j]);
  }
  tier.zero = b.zero & tier_real;
  *first_dup = RepairZeroKeyMatches(AllPairsMatchMaskWide(tier, a),
                                    tier.zero, a.zero, first_real);
  *carry_dup = RepairZeroKeyMatches(AllPairsMatchMaskWide(a, b), a.zero,
                                    b.zero & carry_real, carry_real);
  return;
#endif
  *first_dup =
      CrossBucketDuplicateMaskAt<K>(second, tier_real, first, first_real,
                                    width);
  *carry_dup =
      CrossBucketDuplicateMaskAt<K>(first, first_real, second, carry_real,
                                    width);
}

// carry_real and tier_real are disjoint halves of the candidate mask.
inline void CrossBucketClassDuplicateMasks(const uint8_t* first,
                                           uint64_t first_real,
                                           const uint8_t* second,
                                           uint64_t carry_real,
                                           uint64_t tier_real,
                                           size_t key_bytes,
                                           uint64_t* first_dup,
                                           uint64_t* carry_dup) {
  assert((carry_real & tier_real) == 0);
  switch (key_bytes) {
    case 4:
      CrossBucketClassDuplicateMasksAt<4>(first, first_real, second,
                                          carry_real, tier_real, key_bytes,
                                          first_dup, carry_dup);
      return;
    case 8:
      CrossBucketClassDuplicateMasksAt<8>(first, first_real, second,
                                          carry_real, tier_real, key_bytes,
                                          first_dup, carry_dup);
      return;
    case 16:
      CrossBucketClassDuplicateMasksAt<16>(first, first_real, second,
                                           carry_real, tier_real, key_bytes,
                                           first_dup, carry_dup);
      return;
    default:
      CrossBucketClassDuplicateMasksAt<0>(first, first_real, second,
                                          carry_real, tier_real, key_bytes,
                                          first_dup, carry_dup);
      return;
  }
}

// One 32-bit key field of a bucket against itself; `bucket` is offset to the
// segment by the caller.
//
// VPCONFLICT covers the pairs inside one register (it reports, per lane, the
// earlier lanes it equals); the cross-register pairs are the ordinary
// intersect, taken only for i < j.  Without VP2INTERSECT that intersect is
// IntersectSecondMask*'s single-pair rotate-and-compare emulation
// (cpu_byteslice_key_intersect.hpp), not the xor + unsigned-min fallback
// above, and VPCONFLICT is used unconditionally; the cost of both on Intel
// server parts has not been characterized.
inline uint64_t BucketSelfFieldMatchMaskD(const uint8_t* bucket, uint64_t real,
                                          size_t field_bytes) {
  CountCompare(CompareKind::kSelfD);
  __m512i l[4], a[4];
  const uint64_t zero =
      LoadKeyLinesZeroingDummies(bucket, field_bytes, real, 4, l);
  TransposeKeyLinesToDwords(l, a);
  uint64_t dup = 0;
  for (int j = 0; j < 4; ++j) {
    const __m512i conf = _mm512_conflict_epi32(a[j]);
    uint64_t acc = core::obliTestMask32(conf, conf);
    for (int i = 0; i < j; ++i) {
      acc |= _cvtmask16_u32(IntersectSecondMaskD(a[i], a[j]));
    }
    dup |= acc << (16 * j);
  }
  // The zero repair in scalar form: after dummy lanes are zeroed every real
  // zero-valued slot looks like a repeat, so all of them but the lowest are.
  return ((dup & ~zero) | (zero & (zero - 1))) & real;
}

inline uint64_t BucketSelfFieldMatchMaskQ(const uint8_t* bucket, uint64_t real,
                                          size_t field_bytes) {
  CountCompare(CompareKind::kSelfQ);
  __m512i l[8], a[8];
  const uint64_t zero =
      LoadKeyLinesZeroingDummies(bucket, field_bytes, real, 8, l);
  TransposeKeyLinesToQwords(l, a);
  uint64_t dup = 0;
  for (int j = 0; j < 8; ++j) {
    const __m512i conf = _mm512_conflict_epi64(a[j]);
    uint64_t acc = core::obliTestMask64(conf, conf);
    for (int i = 0; i < j; ++i) {
      acc |= _cvtmask8_u32(IntersectSecondMaskQ(a[i], a[j]));
    }
    dup |= acc << (8 * j);
  }
  return ((dup & ~zero) | (zero & (zero - 1))) & real;
}

// Returns the slot mask of `bucket`'s real entries whose key also occurs in a
// LOWER-numbered real slot of the same bucket -- i.e. every copy but the first.
// Used to make a residual bucket internally duplicate-free before its entries
// are merged back into the main table; two copies of a key share a tag, so
// range routing always lands them in the same residual bucket.
inline uint64_t BucketSelfDuplicateMask(const uint8_t* bucket, uint64_t real,
                                        size_t key_bytes) {
  assert(key_bytes >= 1 && key_bytes <= kMaxKeyBytes);
  if (key_bytes <= 4) {
    return BucketSelfFieldMatchMaskD(bucket, real, key_bytes);
  }
  if (key_bytes <= 8) {
    return BucketSelfFieldMatchMaskQ(bucket, real, key_bytes);
  }
  if (kWideKeySegmentMatch && key_bytes == kMaxKeyBytes) {
    // Slot j is reported iff EVERY segment repeats some lower real slot's,
    // as in WideSegmentMatchMask.  A true duplicate repeats the same lower
    // slot in all four, so it is always caught; the lowest copy of a key
    // survives unless its four segments all collide by chance.
    uint64_t dup = real;
    for (size_t off = 0; off < kMaxKeyBytes; off += 4) {
      dup &= BucketSelfFieldMatchMaskD(bucket + off * kBucketCapacity, real, 4);
    }
    return dup;
  }
  CountCompare(CompareKind::kSelfWide);
  const auto a = LoadWideDedupKeys<true>(bucket, real, key_bytes);
  uint64_t dup = 0;
  for (int j = 0; j < 8; ++j) {
    __m512i acc = _mm512_set1_epi64(-1);
    for (int i = 0; i <= j; ++i) {
      __m512i lo = a.lo[i], hi = a.hi[i];
      for (int r = 0; r < 8; ++r) {
        __m512i diff = _mm512_or_si512(
            _mm512_xor_si512(lo, a.lo[j]),
            _mm512_xor_si512(hi, a.hi[j]));
        // Earlier registers are entirely earlier slots. In this register
        // the wrapped lanes t >= 8-r alone have (t+r)%8 < t. These masks
        // depend only on the public loop counters, never on key contents.
        if (i == j) {
          const uint64_t earlier = (0xffu << (8 - r)) & 0xffu;
          diff = core::obliMaskMov64(_mm512_set1_epi64(-1), earlier, diff);
        }
        acc = _mm512_min_epu64(acc, diff);
        lo = _mm512_alignr_epi64(lo, lo, 1);
        hi = _mm512_alignr_epi64(hi, hi, 1);
      }
    }
    dup |= core::obliTestNMask64(acc, acc) << (8 * j);
  }
  // Zeroed dummies can match only the complete zero key. Keep exactly its
  // lowest real slot, just as in the narrow self kernels.
  return ((dup & ~a.zero) | (a.zero & (a.zero - 1))) & real;
}

}  // namespace byteslice
}  // namespace microram
