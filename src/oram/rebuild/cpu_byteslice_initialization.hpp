#pragma once

// DIRECT INITIALIZATION: the pieces the level-arena hierarchy needs to build
// its largest level straight out of an input stream instead of one online
// write at a time (the engine side is in
// src/oram/levelarena/cpu_byteslice_level_arena_engine.hpp).
//
// An ordinary fill pays the whole ladder for every record: accesses fill the
// online dense prefix, a full prefix carries into the smallest hashed level,
// and over a capacity cycle every record is re-routed once per level it
// passes through.  A table built from a
// known input does not need any of that.  The records are scattered
// CONSECUTIVELY over the final largest-level region at its ordinary initial
// load, tagged under one fresh nonce, and routed in place by the same
// butterfly (plus the terminal radix pass above B = 2) that an ordinary
// rebuild of that level would run -- one network, no staging table, no
// per-record dictionary, and no intermediate levels at all.
//
// WHAT IS PUBLIC.  `count` is public and so is every address this schedule
// touches: which destination bucket a record lands in is its ORDINAL, not its
// key, so the scatter is a straight-line write and the routing that follows is
// the same data-oblivious network the engine already runs.  A partial input
// pads the same public geometry -- the level is published at its full digit
// whatever `count` is -- so the arena shape after initialization reveals only
// the record count the caller already knew.
//
// WHAT IS NOT HERE.  The policy enum names duplicate-resolving modes, but the
// level arena rejects them: resolving copies shed at different routing stages
// would need an input ordinal carried through routing, an ordered residual
// pass, and residual capacity sized for arbitrary duplicates.  kDistinct is a
// caller GUARANTEE that the stored keys are distinct, and it omits all of
// that work.

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstring>

#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/table/cpu_byteslice_routing_map.hpp"

namespace microram {
namespace byteslice {

// How an initialization resolves two input records with the same STORED key.
//
// kDistinct is not a resolution rule but a promise: the caller states that no
// stored key repeats, and the initializer skips every comparison.  A wide-key
// instance rehashes, so "distinct" is a statement about the rehashed keys --
// which for an injective input is the same statement up to a 2^-128 collision.
//
// The other two would compare INPUT POSITIONS: the earliest, respectively
// latest, record of a repeated key wins, independently of which routing stage
// the losing copies were shed at.  They are reserved values; the level arena
// rejects them (see the file header).
enum class InitializationPolicy : uint8_t { kDistinct, kFirstWins, kLastWins };

// One record of an initialization input.  `key` is `UserKeyBytes()` wide (the
// caller's width, before any rehash) and `value` is `value_bytes` wide.  Both
// pointers need only stay valid until the iterator is advanced, so a generated
// input needs storage for exactly one record.
struct InitializationEntry {
  const uint8_t* key = nullptr;
  const uint8_t* value = nullptr;
};

// ---------------------------------------------------------------------------
// The initial load
// ---------------------------------------------------------------------------
//
// `count` records over `num_buckets` destination buckets at `per_bucket`
// records each (32 at the load-0.5 main arena), consecutively: record j lands
// in bucket j / per_bucket at slot j % per_bucket.  Every field below is a
// function of the two public sizes and `count`.
struct InitialLoadPlan {
  size_t num_buckets = 0;
  size_t per_bucket = 0;
  size_t full_buckets = 0;     // buckets receiving `per_bucket` records
  size_t partial_records = 0;  // records the bucket after those receives

  // Records destined for bucket b.  Public: it reads `count`, never a key.
  size_t RecordsFor(size_t bucket) const {
    if (bucket < full_buckets) return per_bucket;
    if (bucket == full_buckets) return partial_records;
    return 0;
  }
};

inline InitialLoadPlan PlanInitialLoad(size_t num_buckets, size_t per_bucket,
                                       size_t count) {
  assert(per_bucket >= 1 && per_bucket <= kBucketCapacity);
  assert(count <= num_buckets * per_bucket);
  InitialLoadPlan plan;
  plan.num_buckets = num_buckets;
  plan.per_bucket = per_bucket;
  plan.full_buckets = count / per_bucket;
  plan.partial_records = count % per_bucket;
  return plan;
}

// Writes the input into `t` -- a view of the FINAL destination region, in the
// base layout (the meta line folded into the value) -- and sets its occupancy
// masks.  `stored_key(const uint8_t*) -> KeyWords` is the engine's own
// user-key conversion, so a wide key is rehashed exactly as an online write
// would rehash it.
//
// The iterator is single pass: each record is dereferenced once, consumed, and
// only then is the iterator advanced.  Nothing is retained across the
// increment.
//
// EVERY byte of the region is written, the padding and the tag lines
// included: real slots get the record, everything else gets zero.  Two
// reasons, and neither is the routing -- which does recompute the tag lines it
// reads.  An initialized table's bytes should be a function of its INPUT and
// not of whatever the allocator or a previous owner left in the region, and
// the MergeSplits move whole entries (Layout::RoutedLines includes the tag
// bytes no level has retired yet), so leaving those lines indeterminate would
// have the network permuting indeterminate bytes around.  The meta line,
// zeroed with the rest, is exactly the "not a residual, not a tombstone" an
// online insert writes.
template <class InputIterator, class KeyFn>
inline void ScatterInitialRecords(TableView t, const InitialLoadPlan& plan,
                                  InputIterator& first, KeyFn&& stored_key) {
  assert(plan.num_buckets == t.num_buckets);
  const Layout& layout = t.layout;
  const size_t key_bytes = layout.key_bytes;
  const size_t meta_line = layout.MetaLine();
  const size_t bucket_bytes = layout.BucketBytes();
  // One whole bucket, staged so the arena sees one sequential run of byte
  // lines per bucket instead of a stride-64 byte store per record field.
  // Bounded scratch: a couple of KiB, independent of the input length.
  Aligned64Ptr staging = AllocateAligned64(bucket_bytes);
  uint8_t* stage = staging.get();
  for (size_t b = 0; b < plan.num_buckets; ++b) {
    const size_t take = plan.RecordsFor(b);
    std::memset(stage, 0, bucket_bytes);
    for (size_t slot = 0; slot < take; ++slot) {
      const InitializationEntry record = *first;
      WriteSlotKey(stage, slot, key_bytes, stored_key(record.key));
      for (size_t line = key_bytes; line < meta_line; ++line) {
        stage[line * kBucketCapacity + slot] = record.value[line - key_bytes];
      }
      ++first;
    }
    std::memcpy(t.data + b * bucket_bytes, stage, bucket_bytes);
    t.masks[b] = LowMask64(static_cast<unsigned>(take));
  }
}

}  // namespace byteslice
}  // namespace microram
