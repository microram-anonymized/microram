#pragma once

// The residual stash: what a load-0.5 MergeSplit does with the entries that do
// not fit.
//
// At load 0.25 a butterfly output bucket holds 16 real entries on average and
// the Chernoff bound on exceeding 64 is ~2^-65, so an overflow is treated as a
// rebuild failure and no machinery exists for it.  At load 0.5 a bucket is
// Poisson(32) and the same tail is ~2^-21 per bucket -- a routine event over a
// rebuild of millions of buckets.  So instead of failing, every MergeSplit
// emits a (usually empty) local residual and obliviously merges it into a
// stash held in the same byte-sliced form as everything else.
//
// PER-LEVEL STASHES. Each butterfly level gets a separate stash, indexed by
// level_stashes[bit]. Sheds at different levels can be correlated; their
// failure probabilities must be union-bounded rather than pooled under an
// independence assumption.
//
// SIZING MODEL. For independent X_b ~ Poisson(32), O_b = max(X_b - 64, 0),
// P[sum_b O_b >= S+1] <= min_(z>1) z^-(S+1) E[z^O_b]^N.
// analysis/gen_stash_capacity_table.cpp evaluates this model offline. The
// generated table is shared by the engines. Applying it to actual routing,
// offers and drains needs the corresponding joint MGF domination argument;
// fixed totals or pairwise negative correlation alone are insufficient.
// analysis/bound_certification/README.md describes how the engine's capacity
// events are certified and under which premises.
// S is a multiple of 64 because one stash bucket holds 64 slots.
//
// LAYOUT.  key | value | meta(1) | tag, byte-sliced exactly like the base
// layout, with the meta line folded into the value so that every base kernel
// (tags, MergeSplit, butterfly, probe) applies unchanged.  The meta byte
// records the residual's source level as source_level + 1, with 0 meaning "not
// a residual"; that is what lets an access keep issuing REAL probes through the
// table a residual originally belonged to, instead of having to guess.

#include <immintrin.h>

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstring>

#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/rebuild/cpu_byteslice_mergesplit.hpp"
#include "src/oram/rebuild/cpu_byteslice_stash_capacity_table.hpp"

namespace microram {
namespace byteslice {

// key | value | meta(1) | tag.  Reuses all base-layout machinery by folding
// the meta line into the value: Base() has value_bytes + 1 value lines, so
// ComputeRoutingTags, the MergeSplit kernels, the butterflies and the probe
// helpers from cpu_byteslice_rebuild.hpp all apply unchanged, and a probe
// that extracts "the value" with Base() extracts value+meta in one pass.
struct StashLayout {
  size_t key_bytes = 8;    // 1..kMaxKeyBytes, the STORED width (see Layout)
  size_t value_bytes = 16;
  size_t tag_bytes = 4;    // 1..8
  // Layout::digit_bits, forwarded by Base().  The ENGINE owns it -- it is a
  // function of the same geometry that sizes the tag (PlanRoutingTag), and
  // getting it wrong routes entries to the wrong block -- so a hierarchy
  // overwrites whatever a caller passed.  0 is the reserved-digit-byte layout
  // every hand-built Layout gets.
  size_t digit_bits = 0;

  size_t MetaOffset() const { return key_bytes + value_bytes; }
  size_t TagOffset() const { return MetaOffset() + 1; }
  size_t EntryBytes() const { return key_bytes + value_bytes + 1 + tag_bytes; }
  size_t BucketBytes() const { return EntryBytes() * kBucketCapacity; }
  Layout Base() const {
    return Layout{key_bytes, value_bytes + 1, tag_bytes, digit_bits};
  }
};

inline constexpr size_t kStashTargetRealPerBucket = 32;  // load factor 0.5
// Largest per-butterfly-level stash, in whole 64-slot buckets (one zmm byte
// line each).  A single butterfly level's own stash never needs more than a
// few hundred slots even for 2^32-request lifetimes (see BuildStashSchedule);
// 8 covers every tabled config with margin.
inline constexpr size_t kMaxResidualStashBuckets = 8;

// ---------------------------------------------------------------------------
// Per-butterfly-level stash sizing (union bound across levels)
// ---------------------------------------------------------------------------
//
// The table bounds a sum of independent Poisson excesses as described above.
// It is a stage-sizing model, not a certificate for every residual event.
//
// LevelStashSlots(n_events, target_log2) -> smallest S (multiple of 64) whose
// single-level overflow bound is <= 2^target_log2, is provided by the
// generated cpu_byteslice_stash_capacity_table.hpp as an integer table lookup;
// the Chernoff bound behind it is computed offline by
// analysis/gen_stash_capacity_table.cpp.  kStashCapMaxBuckets there must stay
// <= kMaxResidualStashBuckets.
static_assert(kStashCapMaxBuckets <= kMaxResidualStashBuckets,
              "stash capacity table exceeds kMaxResidualStashBuckets");

// A shared residual stash of num_buckets byte-sliced buckets.  Occupancy is
// secret; the data pointer and num_buckets are public.
struct ResidualStash {
  uint8_t* data = nullptr;  // num_buckets * entry_bytes * 64 bytes, 64-aligned
  size_t num_buckets = 0;
  size_t entry_bytes = 0;
  uint64_t masks[kMaxResidualStashBuckets] = {};

  size_t Capacity() const { return num_buckets * kBucketCapacity; }
  size_t Count() const {
    size_t count = 0;
    for (size_t b = 0; b < num_buckets; ++b) count += Popcount64(masks[b]);
    return count;
  }
  uint8_t* Bucket(size_t b) { return data + b * entry_bytes * kBucketCapacity; }
  const uint8_t* Bucket(size_t b) const {
    return data + b * entry_bytes * kBucketCapacity;
  }
  void Reset() {
    for (size_t b = 0; b < kMaxResidualStashBuckets; ++b) masks[b] = 0;
  }
};

// ---------------------------------------------------------------------------
// Residual stash merge
// ---------------------------------------------------------------------------
//
// The stash merge collapses the same way the MergeSplit itself does (see the
// header of cpu_byteslice_mergesplit.hpp, which also defines BuildMergeIndex
// and the iota constants): all bytes shed by one MergeSplit
// come from a SINGLE source line -- the second bucket's, since only its
// entries move -- so one two-source byte permute per stash bucket per byte
// line replaces the whole compress/compress/expand staging plus the stash
// expand.  Which stash slot a shed entry lands in is a pure function of the
// occupancy masks, and their order inside a stash bucket is immaterial (a
// stash is a set), which is what lets the two directions' residuals be taken
// in slot order under one index.

// Per-stash-bucket permutation index plus the mask that zeroes the free
// slots receiving nothing.  Built once per MergeSplit, applied to every line.
struct StashPermutePlan {
  __m512i idx[kMaxResidualStashBuckets];
  __mmask64 keep[kMaxResidualStashBuckets];
  size_t num_buckets = 0;
};

// Updates the stash occupancy masks and fills `plan`.  `residual_src` is the
// set of source-line slots holding shed entries; their order in the stash is
// irrelevant, so they are taken in slot order (which is what lets the whole
// residual path collapse to one permute).
inline void PlanStashMergePermute(ResidualStash& stash, uint64_t residual_src,
                                  StashPermutePlan* plan) {
  plan->num_buckets = stash.num_buckets;
  uint64_t pending = residual_src;
  for (size_t b = 0; b < stash.num_buckets; ++b) {
    const uint64_t old_mask = stash.masks[b];
    const unsigned free_slots =
        static_cast<unsigned>(kBucketCapacity) - Popcount64(old_mask);
    const unsigned take = std::min(Popcount64(pending), free_slots);
    const uint64_t take_src = _pdep_u64(LowMask64(take), pending);
    const uint64_t dest = _pdep_u64(LowMask64(take), ~old_mask);
    plan->idx[b] = BuildMergeIndex(dest, take_src);
    plan->keep[b] = _cvtu64_mask64(old_mask | dest);
    stash.masks[b] = old_mask | dest;
    pending &= ~take_src;
  }
}

inline void ApplyStashPermuteLineAtOffset(ResidualStash& stash,
                                          const StashPermutePlan& plan,
                                          size_t offset, __m512i source) {
  for (size_t b = 0; b < plan.num_buckets; ++b) {
    uint8_t* ptr = stash.Bucket(b) + offset;
    const __m512i line =
        _mm512_load_si512(reinterpret_cast<const void*>(ptr));
    _mm512_store_si512(reinterpret_cast<void*>(ptr),
                       _mm512_maskz_permutex2var_epi8(plan.keep[b], line,
                                                      plan.idx[b], source));
  }
}

}  // namespace byteslice
}  // namespace microram
