#pragma once

// The meta byte line, and the dense scatter that starts a rebuild.
//
// Every entry carries one meta byte, holding three pairwise disjoint bits:
//
//   - bit 7 (kMetaErased) is the erasure TOMBSTONE.  A hashed table has no
//     removal: a probe reads, it never clears an occupancy bit, because
//     clearing one would make the access observable.  So erasing a key is an
//     INSERTION of a real entry carrying that key, a zero value and this bit;
//     the dedup at the next rebuild that sees both copies resolves them, and
//     the tombstone is finally forgotten by a carry into the last level, which
//     is the only rebuild that retires every live nonce family at once.
//
//   - bit 5 (kMetaUnshadowed) qualifies bit 7: this tombstone had nothing to
//     shadow when it was inserted, so a carry into the last level may skip it
//     at its READ instead of routing it.
//
//   - bit 6 (kMetaResidualClass) marks a residual candidate's class inside one
//     class-marked offer pass, and is meaningless anywhere else.
//
// DENSE SCATTER.  A rebuild's input arrives as dense 64-slot buckets -- an
// online-stash flush, a worker's output -- and the routing network wants them
// spread evenly over the destination.  ScatterDenseBucket distributes one dense
// bucket over 64/per_bucket destination buckets.  It runs before any tag is
// computed, so it moves Layout::PayloadLines() and leaves tag lines stale.

#include <immintrin.h>

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <stdexcept>
#include <type_traits>

#include "src/core/mov_intrinsics.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"

namespace microram {
namespace byteslice {

// ---------------------------------------------------------------------------
// Meta byte-line helpers
// ---------------------------------------------------------------------------
//
// One byte per entry, at Layout::MetaLine() (= StashLayout::MetaOffset()):
//
//   bit 7      kMetaErased -- the erasure TOMBSTONE.  Set by Erase() on the
//              entry it inserts; means "this key is absent".  Cleared by
//              nothing: a tombstone is dropped whole (its occupancy bit goes),
//              and only by a rebuild of the last level, which is the only one
//              that retires every live nonce family at once.  Dropping it
//              earlier would let a staler copy of the key reappear.
//   bit 6      kMetaResidualClass -- see below.
//   bit 5      kMetaUnshadowed -- see below; qualifies bit 7.
//   bits 0-4   unused.
inline constexpr uint8_t kMetaErased = 0x80;

// Bit 5: no LIVE copy of this tombstone's key older than it exists anywhere in
// the hierarchy, because the access that inserted it probed and found nothing,
// or found a tombstone that carried this bit itself -- the found entry is the
// key's freshest copy, so everything older is that tombstone or older still.
// The second case is why the bit is inherited: a tombstone written over an
// unshadowed tombstone is itself unshadowed.  It therefore does the
// repeated-position job only -- keeping the NEXT access to that key from
// re-probing the same bucket under a family that already saw a real probe for
// it -- and never the SHADOWING job, because there is no older value to shadow
// and no rebuild can invent one.  That is what lets a carry into the last level
// skip it at its READ instead of routing it through the merge and clearing it
// at the tail (kDropErased).  The top's fixed merge leaves out most other
// tombstones too, once its dedup has cleared their older copies
// (FixedMergeTombstones); this bit is what the other read sites -- the
// residual scatter and the copies -- go by.
//
// It is meaningful only together with kMetaErased, and every reader below tests
// BOTH bits.
//
// CONSERVATIVE-SAFE: clearing this bit is always correct and merely costs
// capacity; setting it wrongly is a silent correctness bug -- a stale value
// resurrects, nothing throws.  A path that cannot establish the invariant
// cheaply must leave the bit clear.  The batch path gets it from its
// forwarding chain, which gives every lane the bit the serial access would
// (ForwardBatchLane): a lane that repeats a key sees the entry the earlier
// lane left, so an earlier lane's write clears it.
inline constexpr uint8_t kMetaUnshadowed = 0x20;

// Bits 0-4 are UNUSED.

// The MERGED residual offer's class mark.  (A "residual" is an entry that
// overflowed its routed main bucket during a rebuild; it waits in a bounded
// residual stash, the table's "tier", and an "offer" gives it a second chance
// at free main slots.  A "carry" is the full table a level hands to the level
// above.  See src/oram/DESIGN.md, "Rebuilds preserve both destination and
// freshness", and levelarena DESIGN.md, "Carries and preparation".)
// The bit records which of a class-marked pass's two swept classes a residual
// candidate belongs to -- set = the kResidualWins (tier) class, clear = the
// kTableWins (carry) one.  Stamped per range bucket before the residual route
// (WriteResidualClassBitsRange), read per candidate by the merged offer
// (PlanResidualOfferMerge), and meaningless anywhere else: a bit that
// rides an absorbed entry into the published table is never read again, because
// the only reader is a range table and every range table is re-stamped over its
// whole extent between its retag and its route.
//
// It lives HERE, in the meta byte, rather than in a spare high routing-tag bit:
// the meta byte is a payload line, so it
// exists in every configuration, is always routed and can never be pruned --
// whereas a tag bit had to be found above the DEEPEST carry's index bits and
// clear of the packed digit field, a search that simply fails at some public
// geometries (B = 2 with s + L a multiple of 8 at the minimal tag; B > 2 with
// the index bits at 5 mod 8) and would force those constructions onto a
// slower split two-pass shape.
inline constexpr uint8_t kMetaResidualClass = 0x40;

// The whole bit budget, pinned.
static_assert((kMetaErased & kMetaResidualClass) == 0 &&
                  (kMetaErased & kMetaUnshadowed) == 0 &&
                  (kMetaResidualClass & kMetaUnshadowed) == 0,
              "the tombstone bit, the residual class mark and the unshadowed "
              "mark must be pairwise disjoint");

// Slot mask of the bucket's tombstones (real or not -- the caller ANDs with
// its own occupancy word, and dummy slots hold don't-care bytes).
//
// That AND is why the test here and the compare in UnshadowedSlotMask are the
// register-only core forms: GCC folded a caller's `secret & mask` into the
// instruction's write mask and read the constant from memory under it.
inline uint64_t ErasedSlotMask(const uint8_t* bucket, size_t meta_offset) {
  const __m512i line = _mm512_load_si512(reinterpret_cast<const void*>(
      bucket + meta_offset * kBucketCapacity));
  return core::obliTestMask8(
      line, _mm512_set1_epi8(static_cast<char>(kMetaErased)));
}

// Slot mask of the bucket's UNSHADOWED tombstones: bit 7 and bit 5 together,
// because bit 5 alone is meaningless (see kMetaUnshadowed).  One byte line read
// and nothing written -- the caller ANDs the result out of its own copy of the
// occupancy word, never out of the source table's, which stays probeable until
// the carry publishes.  Real or not: dummy slots hold don't-care bytes and the
// caller's word excludes them.
inline uint64_t UnshadowedSlotMask(const uint8_t* bucket, size_t meta_offset) {
  const __m512i line = _mm512_load_si512(reinterpret_cast<const void*>(
      bucket + meta_offset * kBucketCapacity));
  const __m512i both = _mm512_set1_epi8(
      static_cast<char>(kMetaErased | kMetaUnshadowed));
  return core::obliCmpEqMask8(_mm512_and_si512(line, both), both);
}

// The skip, as a carry applies it: `mask` is the caller's COPY of a source
// bucket's occupancy word and the source is not written.  Nothing about the
// work depends on how many unshadowed tombstones there were.
inline void DropUnshadowedFromMask(const uint8_t* bucket, uint64_t* mask,
                                   size_t meta_offset) {
  *mask &= ~UnshadowedSlotMask(bucket, meta_offset);
}

// Turns every tombstone of the bucket into a dummy.  Its bytes stay where they
// are and are never moved again -- clearing the occupancy bit is the whole
// deletion, exactly as the cross-source dedup drops a duplicate.  Reads one
// byte line and writes one occupancy word; nothing about the work depends on
// how many tombstones there were.
inline void DropErasedEntries(const uint8_t* bucket, uint64_t* mask,
                              size_t meta_offset) {
  *mask &= ~ErasedSlotMask(bucket, meta_offset);
}

// No REAL tombstone anywhere in [begin, end) of `t`.  A predicate, for the
// checked build's assertions: a table produced by a carry into the last level
// has had every tombstone cleared at that carry's tail, and the rebuilds that
// consume such a table say so here rather than in a comment.  One byte line and one
// occupancy word per bucket, so it is affordable under assert() and nowhere
// else.
inline bool RangeHasNoErasedEntries(TableView t, size_t begin, size_t end,
                                    size_t meta_offset) {
  const size_t bucket_bytes = t.layout.BucketBytes();
  for (size_t b = begin; b < end; ++b) {
    if ((t.masks[b] & ErasedSlotMask(t.data + b * bucket_bytes, meta_offset)) !=
        0) {
      return false;
    }
  }
  return true;
}

// The same over a range of a table, which is the form a rebuild issues it in.
inline void DropErasedEntriesRange(TableView t, size_t begin, size_t end) {
  const size_t bucket_bytes = t.layout.BucketBytes();
  const size_t meta_offset = t.layout.MetaLine();
  for (size_t b = begin; b < end; ++b) {
    DropErasedEntries(t.data + b * bucket_bytes, &t.masks[b], meta_offset);
  }
}

// ---------------------------------------------------------------------------
// The online-stash insert
// ---------------------------------------------------------------------------

// One entry into slot `slot` of a DENSE bucket.  The online stash is the only
// place either hierarchy writes an entry directly -- everything else in the
// arena arrives through a rebuild -- so this is the whole of it.
//
// Every access inserts exactly one entry, whatever it found: a read
// re-inserts what it took, an erase inserts a tombstone, a write inserts the
// value.  That uniformity is the point, and it is why `real` and `erased` are
// SECRET here and are applied as arithmetic rather than as a branch or a
// ternary -- mov_intrinsics.hpp's premise is that a ternary is under no
// obligation to compile to a CMOV, and at -O2 GCC turns one back into a branch
// whenever it thinks the condition is predictable.  "Was this key present" is
// exactly the condition an attacker wants branched on.
//
// So every byte of the entry is written, to a fixed address, whatever the two
// flags say; the only thing they decide is one register CMOV over the
// occupancy word, which is stored either way.  `value` is the caller's value,
// `layout.value_bytes - 1` bytes of it -- the last value line is the meta byte
// this writes itself.
//
// Tag lines are NOT written: every rebuild recomputes them wholesale.
template <bool Values = true>
INLINE void WriteDenseStashEntry(uint8_t* bucket, uint64_t* mask, size_t slot,
                                 const Layout& layout, KeyWords key,
                                 const uint8_t* value, bool real, bool erased,
                                 bool unshadowed = false) {
  const size_t key_bytes = layout.key_bytes;
  const size_t meta_line = layout.MetaLine();
  WriteSlotKey(bucket, slot, key_bytes, key);
  if constexpr (Values) {
    for (size_t line = key_bytes; line < meta_line; ++line)
      bucket[line * kBucketCapacity + slot] = value[line - key_bytes];
  }
  // `unshadowed` is as secret as `erased` and is applied the same way: a mask
  // built by negating the bool, never a branch or a ternary on a probe result.
  bucket[meta_line * kBucketCapacity + slot] = static_cast<uint8_t>(
      ((0u - static_cast<unsigned>(erased)) & kMetaErased) |
      ((0u - static_cast<unsigned>(unshadowed)) & kMetaUnshadowed));
  const uint64_t with_entry = *mask | (uint64_t{1} << slot);
  core::CMOV8(real, *mask, with_entry);
}

// ---------------------------------------------------------------------------
// Dense-bucket scatter (rebuild input preparation)
// ---------------------------------------------------------------------------

// Slots [b * Per, (b + 1) * Per) of one line register to the same line of
// destination bucket b, `bucket_bytes` apart: stores of exactly Per bytes at
// public addresses, so slots past Per keep their bytes.  With Per a constant
// these are register stores; a runtime width would compile to a memcpy@PLT
// call per (line, destination bucket).
template <size_t Per>
INLINE void ScatterDenseLine(uint8_t* dest, size_t bucket_bytes,
                             __m512i line) {
  static_assert(Per >= 1 && kBucketCapacity % Per == 0, "Per divides 64");
  if constexpr (Per == 64) {
    _mm512_storeu_si512(reinterpret_cast<void*>(dest), line);
  } else if constexpr (Per == 32) {
    _mm256_storeu_si256(reinterpret_cast<__m256i*>(dest),
                        _mm512_castsi512_si256(line));
    _mm256_storeu_si256(reinterpret_cast<__m256i*>(dest + bucket_bytes),
                        _mm512_extracti64x4_epi64(line, 1));
  } else if constexpr (Per == 16 || Per == 8) {
    const __m128i part[4] = {
        _mm512_castsi512_si128(line), _mm512_extracti32x4_epi32(line, 1),
        _mm512_extracti32x4_epi32(line, 2), _mm512_extracti32x4_epi32(line, 3)};
    for (size_t q = 0; q < 4; ++q) {
      if constexpr (Per == 16) {
        _mm_storeu_si128(reinterpret_cast<__m128i*>(dest + q * bucket_bytes),
                         part[q]);
      } else {
        uint8_t* const at = dest + 2 * q * bucket_bytes;
        _mm_storel_epi64(reinterpret_cast<__m128i*>(at), part[q]);
        _mm_storeh_pd(reinterpret_cast<double*>(at + bucket_bytes),
                      _mm_castsi128_pd(part[q]));
      }
    }
  } else {
    alignas(64) uint8_t bytes[kBucketCapacity];
    _mm512_store_si512(reinterpret_cast<void*>(bytes), line);
    for (size_t b = 0; b < kBucketCapacity / Per; ++b) {
      std::memcpy(dest + b * bucket_bytes, bytes + b * Per, Per);
    }
  }
}

// Calls f(std::integral_constant<size_t, per_bucket>{}), so that the scatter's
// store widths are constants.  per_bucket divides 64.
template <typename F>
INLINE void WithDensePerBucket(size_t per_bucket, F&& f) {
  switch (per_bucket) {
    case 64: return f(std::integral_constant<size_t, 64>{});
    case 32: return f(std::integral_constant<size_t, 32>{});
    case 16: return f(std::integral_constant<size_t, 16>{});
    case 8: return f(std::integral_constant<size_t, 8>{});
    case 4: return f(std::integral_constant<size_t, 4>{});
    case 2: return f(std::integral_constant<size_t, 2>{});
    case 1: return f(std::integral_constant<size_t, 1>{});
  }
  throw std::invalid_argument(
      "dense scatter: per_bucket must be a power of two up to 64");
}

// Distributes one dense 64-slot bucket evenly over 64/Per destination
// buckets (Per entries each: 16 at load 0.25, 32 at load 0.5).  Safe in place
// (destination bucket 0 may alias the source): each byte line is loaded
// whole before any part of it is stored.  Destination slots past Per keep
// whatever bytes they had; the masks exclude them.
//
// `entry_bytes` is the layout's full width (it fixes the destination bucket
// stride); `lines` is how many of them to move.  Every scatter in the
// hierarchy is followed by a fresh ComputeRoutingTags, so they all pass
// Layout::PayloadLines() and leave the tag lines stale.
template <size_t Per>
inline void ScatterDenseBucketFor(const uint8_t* source, uint64_t source_mask,
                                  uint8_t* dest_region, uint64_t* dest_masks,
                                  size_t entry_bytes, size_t lines) {
  const size_t bucket_bytes = entry_bytes * kBucketCapacity;
  assert(lines <= entry_bytes);
  for (size_t byte = 0; byte < lines; ++byte) {
    ScatterDenseLine<Per>(dest_region + byte * kBucketCapacity, bucket_bytes,
                          _mm512_loadu_si512(reinterpret_cast<const void*>(
                              source + byte * kBucketCapacity)));
  }
  for (size_t b = 0; b < kBucketCapacity / Per; ++b) {
    dest_masks[b] = (source_mask >> (b * Per)) &
                    LowMask64(static_cast<unsigned>(Per));
  }
}

inline void ScatterDenseBucket(const uint8_t* source, uint64_t source_mask,
                               uint8_t* dest_region, uint64_t* dest_masks,
                               size_t per_bucket, size_t entry_bytes,
                               size_t lines) {
  WithDensePerBucket(per_bucket, [&](auto per) {
    ScatterDenseBucketFor<decltype(per)::value>(
        source, source_mask, dest_region, dest_masks, entry_bytes, lines);
  });
}

}  // namespace byteslice
}  // namespace microram
