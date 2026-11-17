#pragma once

// Fixture helpers for the level-arena job, top and engine tests.
//
// (cpu_byteslice_level_arena_merge_test.cpp has narrower ones of its own,
// sufficient for a fixture that never leaves 8-byte keys; these handle every
// key width, and are here rather than inline so that each fixture that needs
// them shares one set.)
//
// What is awkward enough to be worth factoring out:
//
//   - PLANT an entry at a known (bucket, slot) and READ it back, which nothing
//     in the engine ever does -- the kernels write byte lines, and the only
//     scalar accessors are for tests and input generation;
//   - read a STORED TAG back out of a bucket, which nothing in the engine does
//     either: a tag is written once and consumed by a routing kernel;
//   - enumerate a table's or a stash array's live entries as (key, value)
//     pairs, which is what a key/value model can be compared against;
//   - find keys whose tag lands on a CHOSEN index, which is the only way to
//     force a routing level to overload a bucket and shed on purpose.  At
//     load 0.5 a fixture that plants keys at random never sheds, and a test
//     of the residual wiring that never sheds tests nothing;
//   - fill and PUBLISH one arena slot, which is how a job's operands have to
//     be built: they are views into published storage, and a merge over
//     tables assembled any other way is a merge no engine could hand it.

#include <immintrin.h>

#include <cstdint>
#include <cstring>
#include <map>
#include <stdexcept>
#include <utility>
#include <vector>

#include "src/crypto/hash_primitives.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_slots.hpp"
#include "src/oram/rebuild/cpu_byteslice_residual_stash.hpp"
#include "src/oram/scheduler/cpu_byteslice_subtask_cursor.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/table/cpu_byteslice_meta.hpp"
#include "src/oram/table/cpu_byteslice_routing_map.hpp"
#include "src/oram/table/cpu_byteslice_stored_key.hpp"
#include "src/oram/table/cpu_byteslice_tags.hpp"

namespace microram {
namespace byteslice {
namespace test_support {

inline Table ZeroedTable(size_t buckets, const Layout& layout) {
  Table t = Table::Create(buckets, layout);
  std::memset(t.data.get(), 0, buckets * layout.BucketBytes());
  for (size_t b = 0; b < buckets; ++b) t.masks[b] = 0;
  return t;
}

// ---------------------------------------------------------------------------
// Keys and payloads, at the full stored width
// ---------------------------------------------------------------------------
//
// A fixture that plants uint64 keys and checks one value byte cannot say
// anything about a WIDE layout: above 8 stored key bytes the hash reads a
// second word and every dedup compares one, and a payload wider than a byte is
// only tested by comparing all of it.  So keys here are KeyWords at the
// layout's width, and the payload is a function of the key that the checker
// recomputes rather than a constant it trusts.

inline uint64_t FixtureMask(unsigned bits) {
  return bits >= 64 ? ~uint64_t{0} : ((uint64_t{1} << bits) - 1);
}

// The n-th distinct key of a fixture, at this layout's stored width.
//
// Above eight stored bytes, use the engine's EncodeStoredKey on a 16-byte
// user key to exercise normalization as well as both stored words through
// copying, equality and routing. Exact stored-key matching also accepts
// hand-built keys with shared fields; the dedicated dedup and batch-match
// tests exercise those adversarial cases independently of hashing.
inline KeyWords FixtureKey(uint64_t n, size_t key_bytes) {
  const unsigned low_bits =
      static_cast<unsigned>(8 * (key_bytes < 8 ? key_bytes : 8));
  if (key_bytes <= 8) return KeyWords{(n + 1) & FixtureMask(low_bits)};
  const uint64_t user[2] = {n + 1, 0x9E3779B97F4A7C15ull * (n + 1)};
  KeyWords key = EncodeStoredKey(reinterpret_cast<const uint8_t*>(user),
                                 sizeof(user), crypto::FixedAesRoundKeys());
  if (key_bytes < 16) {
    key.w1 &= FixtureMask(static_cast<unsigned>(8 * (key_bytes - 8)));
  }
  return key;
}

// Byte i of the payload of `key` from source `source` (1 older, 2 fresher).
// Byte 0 IS the source, so a checker can recover it and then verify every
// other byte; the rest depend on BOTH key words, so a copy that dropped the
// high word or crossed two entries shows up.
inline uint8_t PayloadByte(KeyWords key, uint8_t source, size_t i) {
  if (i == 0) return source;
  uint64_t h = (key.w0 + 0x9E3779B97F4A7C15ull) * 0xBF58476D1CE4E5B9ull;
  h ^= (key.w1 + 0x94D049BB133111EBull) * 0x2545F4914F6CDD1Dull;
  h ^= (uint64_t{source} << 56) ^ (i * 0x27D4EB2F165667C5ull);
  h *= 0xD6E8FEB86659FD93ull;
  return static_cast<uint8_t>(h >> 29);
}

// Payload bytes an entry carries: the value region less its last byte, which
// is the meta line.
inline size_t FixturePayloadBytes(const Layout& layout) {
  return layout.value_bytes - 1;
}

inline KeyWords SlotKeyWordsOf(const Layout& layout, const uint8_t* bucket,
                               size_t slot) {
  return ReadSlotKey(bucket, slot, layout.key_bytes);
}

// The meta byte, WITHOUT the residual class mark.
//
// kMetaResidualClass is engine scratch, not data: a class-marked second chance
// stamps it per range bucket, the merged offer copies the meta line into the
// table along with the rest of the payload, and nothing clears it afterwards.
// So an entry a second chance put back carries bit 6 into the published table
// -- which is inert, because the next pass to care re-stamps every range
// bucket unconditionally (WriteResidualClassBitsRange says so in as many
// words) and because the bit lies outside the tombstone and the unshadowed
// qualifier.  A fixture that compared it would be asserting which entries
// happened to be shed.
inline uint8_t SlotMetaOf(const Layout& layout, const uint8_t* bucket,
                          size_t slot) {
  return static_cast<uint8_t>(
      bucket[layout.MetaLine() * kBucketCapacity + slot] &
      ~kMetaResidualClass);
}

// The low `bits` bits of a slot's STORED tag.  Tag bit b lives in bit b % 8 of
// byte line TagLine(b).
inline uint64_t SlotTagBitsOf(const Layout& layout, const uint8_t* bucket,
                              size_t slot, unsigned bits) {
  uint64_t tag = 0;
  for (unsigned b = 0; b < bits; ++b) {
    const uint8_t byte = bucket[layout.TagLine(b) * kBucketCapacity + slot];
    tag |= uint64_t{static_cast<uint8_t>((byte >> (b & 7)) & 1)} << b;
  }
  return tag;
}

inline void PlantEntry(const Layout& layout, uint8_t* bucket, size_t slot,
                       KeyWords key, uint8_t source, uint8_t meta = 0) {
  WriteSlotKey(bucket, slot, layout.key_bytes, key);
  for (size_t i = 0; i < FixturePayloadBytes(layout); ++i) {
    bucket[(layout.key_bytes + i) * kBucketCapacity + slot] =
        PayloadByte(key, source, i);
  }
  bucket[layout.MetaLine() * kBucketCapacity + slot] = meta;
}

// One live entry as a fixture sees it: which source it came from, and its
// meta byte.  The rest of the payload is not stored -- it is RECOMPUTED from
// the key and the source and compared byte for byte at collection, which is
// what makes a wide value tested rather than merely present.
struct LiveEntry {
  uint8_t source = 0;
  uint8_t meta = 0;

  friend bool operator==(const LiveEntry& a, const LiveEntry& b) {
    return a.source == b.source && a.meta == b.meta;
  }
  friend bool operator!=(const LiveEntry& a, const LiveEntry& b) {
    return !(a == b);
  }
};

inline bool PayloadIntact(const Layout& layout, const uint8_t* bucket,
                          size_t slot, KeyWords key, uint8_t source) {
  for (size_t i = 1; i < FixturePayloadBytes(layout); ++i) {
    if (bucket[(layout.key_bytes + i) * kBucketCapacity + slot] !=
        PayloadByte(key, source, i)) {
      return false;
    }
  }
  return true;
}

// Every live entry of a table, keyed by its FULL key.  `*unique` is cleared if
// a key occurs twice -- the uniqueness half of every claim these fixtures make
// -- and `*damaged` counts entries whose payload is not the one their key and
// source say it should be, which is how a copy that moved the wrong lines, or
// mixed two entries, is caught rather than reduced to one byte.
inline void CollectLive(const TableView& t, std::map<KeyWords, LiveEntry>* live,
                        bool* unique, size_t* damaged) {
  for (size_t b = 0; b < t.num_buckets; ++b) {
    uint64_t mask = t.masks[b];
    while (mask != 0) {
      const unsigned slot = static_cast<unsigned>(_tzcnt_u64(mask));
      mask &= mask - 1;
      const KeyWords key = SlotKeyWordsOf(t.layout, t.Bucket(b), slot);
      const LiveEntry entry{
          t.Bucket(b)[t.layout.key_bytes * kBucketCapacity + slot],
          SlotMetaOf(t.layout, t.Bucket(b), slot)};
      if (!PayloadIntact(t.layout, t.Bucket(b), slot, key, entry.source)) {
        ++*damaged;
      }
      if (!live->emplace(key, entry).second) *unique = false;
    }
  }
}

// The same over a run of residual stashes.  A stash is byte-identical to a
// table bucket, so the accessors above serve both.
inline void CollectLiveStashes(const Layout& layout, const ResidualStash* slots,
                               size_t count,
                               std::map<KeyWords, LiveEntry>* live,
                               bool* unique, size_t* damaged) {
  for (size_t s = 0; s < count; ++s) {
    const ResidualStash& stash = slots[s];
    for (size_t b = 0; b < stash.num_buckets; ++b) {
      uint64_t mask = stash.masks[b];
      while (mask != 0) {
        const unsigned slot = static_cast<unsigned>(_tzcnt_u64(mask));
        mask &= mask - 1;
        const KeyWords key = SlotKeyWordsOf(layout, stash.Bucket(b), slot);
        const LiveEntry entry{
            stash.Bucket(b)[layout.key_bytes * kBucketCapacity + slot],
            SlotMetaOf(layout, stash.Bucket(b), slot)};
        if (!PayloadIntact(layout, stash.Bucket(b), slot, key, entry.source)) {
          ++*damaged;
        }
        if (!live->emplace(key, entry).second) *unique = false;
      }
    }
  }
}

// `count` keys whose tag's low `bits` bits are exactly `target` under this
// nonce, map AND KEY.  Planting them all in one place is what makes a routing
// level overload a destination bucket and shed.
//
// The key matters as much as the nonce here: these keys are chosen for where
// the PRF sends them, so a fixture that searched under one key and routed
// under another would plant an ordinary spread of keys and quietly stop
// forcing anything.
inline std::vector<KeyWords> KeysAtTagIndex(
    const Layout& layout, uint64_t nonce_lo, uint64_t nonce_hi,
    const RoutingIndexMap& map, unsigned route_levels, unsigned bits,
    uint64_t target, size_t count, uint64_t* next_key,
    const AesTagKeys& aes_keys = DefaultAesTagKeys()) {
  std::vector<KeyWords> keys;
  Table probe = ZeroedTable(1, layout);
  probe.masks[0] = ~uint64_t{0};
  while (keys.size() < count) {
    KeyWords planted[kBucketCapacity];
    for (size_t slot = 0; slot < kBucketCapacity; ++slot) {
      planted[slot] = FixtureKey((*next_key)++, layout.key_bytes);
      PlantEntry(layout, probe.Bucket(0), slot, planted[slot], 0);
    }
    TableView v = View(probe);
    ComputeRoutingTags(v, nonce_lo, nonce_hi, map, route_levels, aes_keys);
    for (size_t slot = 0; slot < kBucketCapacity && keys.size() < count;
         ++slot) {
      if (SlotTagBitsOf(layout, probe.Bucket(0), slot, bits) != target) continue;
      keys.push_back(planted[slot]);
    }
  }
  return keys;
}

// A cheap (FNV-1a) digest of a table's bytes and masks.  Used to
// state that a merge did not write a source it only reads -- which is not a
// convention here but a requirement: a source is published storage that the
// request thread may be probing (5).
inline uint64_t DigestBytes(const uint8_t* data, size_t bytes) {
  uint64_t h = 0xcbf29ce484222325ull;
  for (size_t i = 0; i < bytes; ++i) {
    h = (h ^ data[i]) * 0x100000001b3ull;
  }
  return h;
}

inline uint64_t DigestTable(const TableView& t) {
  uint64_t h = DigestBytes(t.data, t.num_buckets * t.layout.BucketBytes());
  for (size_t b = 0; b < t.num_buckets; ++b) {
    h = (h ^ t.masks[b]) * 0x100000001b3ull;
  }
  return h;
}

inline uint64_t DigestStash(const Layout& layout, const ResidualStash& stash) {
  uint64_t h =
      DigestBytes(stash.data, stash.num_buckets * layout.BucketBytes());
  for (size_t b = 0; b < stash.num_buckets; ++b) {
    h = (h ^ stash.masks[b]) * 0x100000001b3ull;
  }
  return h;
}

// ---------------------------------------------------------------------------
// Operands built the way an engine builds them
// ---------------------------------------------------------------------------

// A filled, published arena slot, with the digest of everything a merge is not
// allowed to write.  A source is published storage that the request thread may
// be probing (merge jobs may borrow published payload only while writing
// private masks; src/oram/levelarena/DESIGN.md, "Publication, readers and
// progress"), so "the merge did not touch it" is a
// requirement and not a convention.
struct PublishedSource {
  levelarena::LevelArena* arena = nullptr;
  unsigned slot = 0;
  size_t buckets = 0;
  size_t offset = 0;  // into the slot's main: a bank-first run's top tables
  uint64_t main_digest = 0;
  uint64_t tier_digest = 0;

  TableView Main() const {
    return arena->PublishedMain(slot, offset, buckets);
  }
  const ResidualStash* Tier() const { return arena->PublishedTier(slot); }

  void Digest(const Layout& layout) {
    main_digest = DigestTable(Main());
    tier_digest = DigestStash(layout, *Tier());
  }
  bool Unchanged(const Layout& layout) const {
    return DigestTable(Main()) == main_digest &&
           DigestStash(layout, *Tier()) == tier_digest;
  }
};

// Fills one slot's main and tier through the arena's own lifecycle, then
// publishes and accepts it.  `fill` gets the writable views.
template <class Fill>
inline PublishedSource PublishSlot(levelarena::LevelArena* arena,
                                   unsigned slot, size_t buckets,
                                   const Layout& layout, Fill&& fill,
                                   size_t offset = 0) {
  levelarena::SlotLease lease;
  if (!arena->TryLeaseOwn(slot, &lease)) {
    throw std::logic_error("the fixture could not lease a source slot");
  }
  TableView main = arena->WritableMain(lease, offset, buckets);
  ResidualStash* tier = arena->WritableTier(lease);
  // An arena is not cleared when it is allocated, and it should not be: a
  // dummy slot's bytes are don't-care and zeroing a level's whole arena would
  // be a real cost for nothing.  A FIXTURE that compares bytes has to clear
  // them itself, though -- a copy carries a dummy lane's uninitialized value
  // and tag lines into the output, and two runs then differ in bytes no
  // contract defines.
  std::memset(main.data, 0, buckets * layout.BucketBytes());
  std::memset(tier->data, 0, tier->num_buckets * layout.BucketBytes());
  fill(main, tier);
  if (!arena->Publish(lease) || !arena->TryAccept(slot, lease.generation)) {
    throw std::logic_error("the fixture could not publish a source slot");
  }
  PublishedSource source;
  source.arena = arena;
  source.slot = slot;
  source.buckets = buckets;
  source.offset = offset;
  source.Digest(layout);
  return source;
}

// Plants `keys` into a tier stash, at most one bucket's worth per bucket,
// which is what a drained tier actually holds.  `meta_of(key)` gives each
// entry's meta byte, so a fixture can tombstone some of a tier and not all of
// it -- which is the only way to test a rule that treats the two differently.
template <class MetaOf>
inline void PlantTierPerKey(const Layout& layout, ResidualStash* tier,
                            const std::vector<KeyWords>& keys, uint8_t value,
                            MetaOf&& meta_of,
                            std::map<KeyWords, LiveEntry>* model) {
  size_t planted = 0;
  for (size_t b = 0; b < tier->num_buckets && planted < keys.size(); ++b) {
    uint64_t mask = 0;
    for (size_t slot = 0; slot < kBucketCapacity && planted < keys.size();
         ++slot, ++planted) {
      const uint8_t meta = meta_of(keys[planted]);
      PlantEntry(layout, tier->Bucket(b), slot, keys[planted], value, meta);
      (*model)[keys[planted]] = {value, meta};
      mask |= uint64_t{1} << slot;
    }
    tier->masks[b] = mask;
  }
}

inline void PlantTier(const Layout& layout, ResidualStash* tier,
                      const std::vector<KeyWords>& keys, uint8_t value,
                      uint8_t meta, std::map<KeyWords, LiveEntry>* model) {
  PlantTierPerKey(layout, tier, keys, value,
                  [meta](KeyWords) { return meta; }, model);
}

// What one piece adds to a job's RESIDUAL work as LevelMergeResidualTouches
// counts it: a residual phase's whole charge, and the offer weight a fused
// routing kind carries on top of its own routing (PieceTouches's weight term).
inline uint64_t ResidualCharge(const Subtask& piece) {
  const uint64_t units = piece.end - piece.begin;
  switch (piece.kind) {
    case Subtask::kResidualPoolDedup:
    case Subtask::kResidualScatter:
    case Subtask::kResidualScatterRetag:
    case Subtask::kResidualRetag:
    case Subtask::kResidualDfsGather:
    case Subtask::kResidualDfsPartition:
    case Subtask::kResidualSweep:
    case Subtask::kResidualLeftoverDedup:
    case Subtask::kResidualDrain:
    case Subtask::kResidualReset:
      return PieceTouches(piece);
    case Subtask::kCrossLevelOffers:
    case Subtask::kButterflyLevelOffers:
      return 2 * uint64_t{piece.levels} * units;
    case Subtask::kRadixPassOffers:
    case Subtask::kRadixRouteOffers:
    case Subtask::kFixedMergeOffers:
      return SubtaskRadixOf(piece.bit) * uint64_t{piece.levels} * units;
    default:
      return 0;
  }
}

}  // namespace test_support
}  // namespace byteslice
}  // namespace microram
