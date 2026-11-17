// The two mixed-radix kernels a base-B hierarchy needs where a table has
// m * 2^K buckets with m not a power of two (B = 4 and B = 8 levels take digit
// radices r = 3, 5, 7): RadixPassDedupStashRange, which finishes the ABSORB of
// a level into itself (the level's old contents L_t^old merged with the chain
// temporary T_t that the carry produced) at a non-power-of-two digit, and
// MergeRadixLevelSourcesRange, the fixed last level's final sweep.  Both are
// defined and explained in src/oram/rebuild/cpu_byteslice_dedup_network.hpp.
// A third fixture checks the residual second chance (re-offering entries a
// bucket overflowed into the residual stash) on a mixed-radix main table.
//
// The claim both of them rest on -- and the one thing here worth a test of its
// own -- is that each needs r-1 ORDERED dedup pairs per group, not the
// r(r-1)/2 an all-pairs reading would suggest.  So the tests do not merely
// check that duplicates die; they check that the pairs the design says cannot
// occur are NOT paid for, which is what pins the count at r-1.

#include "src/oram/rebuild/cpu_byteslice_dedup_rebuild.hpp"
#include "src/oram/rebuild/cpu_byteslice_dfs_residual.hpp"

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <random>
#include <set>
#include <vector>

namespace {

namespace bs = microram::byteslice;

int failures = 0;

void Expect(bool value, const char* message) {
  if (!value) {
    std::fprintf(stderr, "test failed: %s\n", message);
    ++failures;
  }
}

uint64_t ReadKey(const uint8_t* bucket, size_t slot, size_t key_bytes) {
  return bs::ReadSlotKey(bucket, slot, key_bytes).w0;
}

void WriteKey(uint8_t* bucket, size_t slot, size_t key_bytes, uint64_t key) {
  bs::WriteSlotKey(bucket, slot, key_bytes, key);
}

bs::Layout TestLayout() {
  bs::Layout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 4;
  // Two tag bytes: the digit byte is the most significant one, at DigitLine(),
  // which is where the kRadixDigit retag puts it and where both kernels read
  // it.  The rest is scratch neither kernel touches.
  layout.tag_bytes = 2;
  return layout;
}

// The tag lines are private scratch here: the kernels only ever read the digit
// byte, so the tests write it directly rather than routing a real AES tag.
void SetDigit(const bs::Layout& layout, uint8_t* bucket, size_t slot,
              unsigned digit) {
  bucket[layout.DigitLine() * bs::kBucketCapacity + slot] =
      static_cast<uint8_t>(digit);
}

// Value byte 0 carries which SOURCE BLOCK an entry came from, so a survivor can
// be attributed rather than merely counted.  It is PAYLOAD, which matters: the
// radix pass moves payload lines only -- the digit line is loaded to plan the
// split and never stored -- so the digit byte of a destination bucket is stale
// scratch afterwards and cannot be used to check where an entry ended up.
// Value byte 1 therefore carries a travelling copy of the intended digit.
void SetTag(const bs::Layout& layout, uint8_t* bucket, size_t slot,
            uint8_t block) {
  bucket[layout.key_bytes * bs::kBucketCapacity + slot] = block;
}
uint8_t GetTag(const bs::Layout& layout, const uint8_t* bucket, size_t slot) {
  return bucket[layout.key_bytes * bs::kBucketCapacity + slot];
}
void SetWantedBlock(const bs::Layout& layout, uint8_t* bucket, size_t slot,
                    unsigned digit) {
  bucket[(layout.key_bytes + 1) * bs::kBucketCapacity + slot] =
      static_cast<uint8_t>(digit);
}
unsigned WantedBlock(const bs::Layout& layout, const uint8_t* bucket,
                     size_t slot) {
  return bucket[(layout.key_bytes + 1) * bs::kBucketCapacity + slot];
}

struct Entry {
  uint64_t key;
  uint8_t block;
};

std::vector<Entry> BucketEntries(const bs::Layout& layout,
                                 const uint8_t* bucket, uint64_t mask) {
  std::vector<Entry> out;
  for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
    if ((mask >> e) & 1) {
      out.push_back({ReadKey(bucket, e, layout.key_bytes),
                     GetTag(layout, bucket, e)});
    }
  }
  return out;
}

// ---------------------------------------------------------------------------
// RadixPassDedupStashRange
// ---------------------------------------------------------------------------
//
// The absorb's output is [ block 0 = T_t | blocks 1..r-1 = pure L_t^old ], and
// the radix pass is the last routing step: every entry ends in the block its
// digit names.  Block 0 is the only one that can hold a copy of a key that also
// lives elsewhere in the tuple, so the prologue clears exactly the r-1 ordered
// (block 0, block q) pairs.
//
// `dup_high` seeds a duplicate between two blocks q, q' BOTH nonzero -- a shape
// the absorb cannot produce, because L_t^old holds each key once.  The kernel
// must leave both copies alone: that is the behavioural form of "r-1 pairs, not
// r(r-1)/2", and without it the count could be anything.
void TestRadixPassDedup(unsigned r, unsigned block_bits, size_t per_bucket,
                        bool dup_high, uint64_t seed) {
  const bs::Layout layout = TestLayout();
  const size_t block = size_t{1} << block_bits;
  const size_t num_buckets = block * r;
  auto table = bs::Table::Create(num_buckets, layout);
  std::memset(table.data.get(), 0, num_buckets * layout.BucketBytes());
  std::mt19937_64 rng(seed);

  // Per tuple: the multiset of (key, digit) that must survive, and the keys
  // whose stale copy must have died.
  std::vector<std::multiset<uint64_t>> want(block);
  std::vector<std::vector<uint64_t>> must_be_gone(block);
  std::vector<std::vector<uint64_t>> must_still_be_doubled(block);

  uint64_t next_key = 1;
  for (size_t p = 0; p < block; ++p) {
    // One key per tuple planted in block 0 and re-planted in a random block q,
    // which is the only duplicate shape the absorb can produce.
    const unsigned dup_q = 1 + static_cast<unsigned>(rng() % (r - 1));
    const uint64_t dup_key = next_key++;
    // And, optionally, one planted in two NONZERO blocks.
    const uint64_t high_key = next_key++;
    unsigned high_a = 1, high_b = 2;
    if (r >= 3) {
      high_a = 1 + static_cast<unsigned>(rng() % (r - 1));
      do {
        high_b = 1 + static_cast<unsigned>(rng() % (r - 1));
      } while (high_b == high_a);
    }

    for (unsigned q = 0; q < r; ++q) {
      uint8_t* bucket = table.Bucket(q * block + p);
      size_t slot = 0;
      const auto place = [&](uint64_t key, unsigned digit) {
        WriteKey(bucket, slot, layout.key_bytes, key);
        SetTag(layout, bucket, slot, static_cast<uint8_t>(q));
        SetDigit(layout, bucket, slot, digit);
        SetWantedBlock(layout, bucket, slot, digit);
        ++slot;
      };
      // The seeded duplicate: both copies carry the SAME digit, since a digit
      // is a function of the key.  Block 0's copy is the fresher one.
      if (q == 0) place(dup_key, dup_q);
      if (q == dup_q) place(dup_key, dup_q);
      if (dup_high && r >= 3 && (q == high_a || q == high_b)) {
        place(high_key, high_a);
      }
      while (slot < per_bucket) {
        place(next_key++, static_cast<unsigned>(rng() % r));
      }
      // Stale dummy slots holding live keys -- what the dedup must not be
      // fooled by, and what the pass must not move.
      for (size_t e = slot; e < bs::kBucketCapacity; ++e) {
        WriteKey(bucket, e, layout.key_bytes, 1 + (rng() % next_key));
        SetDigit(layout, bucket, e, static_cast<unsigned>(rng() % r));
      }
      table.masks[q * block + p] =
          bs::LowMask64(static_cast<unsigned>(slot));
    }
    // Expectations for this tuple.
    for (unsigned q = 0; q < r; ++q) {
      const uint8_t* bucket = table.Bucket(q * block + p);
      for (const Entry& e :
           BucketEntries(layout, bucket, table.masks[q * block + p])) {
        if (e.key == dup_key && q != 0) continue;  // the stale copy dies
        want[p].insert(e.key);
      }
    }
    must_be_gone[p].push_back(dup_key);
    if (dup_high && r >= 3) must_still_be_doubled[p].push_back(high_key);
  }

  // Capacity: this test is about the dedup and the routing, not about shedding,
  // so the stash is generous and a shed would be a bug in the test's sizing.
  auto stash_data = bs::AllocateAligned64(8 * layout.BucketBytes());
  std::memset(stash_data.get(), 0, 8 * layout.BucketBytes());
  bs::ResidualStash stash;
  stash.data = stash_data.get();
  stash.num_buckets = 8;
  stash.entry_bytes = layout.EntryBytes();

  Expect(bs::RadixPassDedupStashRange</*CheckOverflow=*/true>(
             bs::View(table), block_bits, r, stash, 0, block),
         "the radix dedup pass overflowed");
  Expect(stash.Count() == 0, "the radix dedup pass shed with room to spare");

  for (size_t p = 0; p < block; ++p) {
    std::multiset<uint64_t> got;
    for (unsigned q = 0; q < r; ++q) {
      const size_t bi = q * block + p;
      const uint8_t* bucket = table.Bucket(bi);
      for (size_t e = 0; e < bs::kBucketCapacity; ++e) {
        if (!((table.masks[bi] >> e) & 1)) continue;
        // Every survivor sits in the block its digit named: that is the whole
        // job of the pass.  Read from the PAYLOAD copy -- the digit line does
        // not travel with the entry.
        Expect(WantedBlock(layout, bucket, e) == q,
               "the radix pass left an entry in the wrong block");
        got.insert(ReadKey(bucket, e, layout.key_bytes));
      }
    }
    Expect(got == want[p], "the radix dedup pass did not conserve the tuple");
    for (uint64_t key : must_be_gone[p]) {
      Expect(got.count(key) == 1,
             "the (block 0, block q) duplicate did not lose exactly one copy");
    }
    for (uint64_t key : must_still_be_doubled[p]) {
      Expect(got.count(key) == 2,
             "the kernel paid for a (block q, block q') pair: it is doing "
             "r(r-1)/2 comparisons, not the r-1 the design needs");
    }
    if (got != want[p]) return;
  }
}

// ---------------------------------------------------------------------------
// MergeRadixLevelSourcesRange
// ---------------------------------------------------------------------------
//
// C is r * 2^K buckets, B is 2^K, and K is the map's low_bits -- so B's bucket
// i holds exactly the entries destined for the tuple {C[i + q*2^K]} and every
// cross-source duplicate is confined to that tuple.  What has to hold:
//
//  - B is untouched, byte for byte and mask for mask (it is still in the old
//    probe plan, and MergeBucketIntoWithStash zeroes the mask word it is given
//    -- hence the per-direction COPY the kernel passes it).
//  - Every B entry lands in the C bucket its digit names.
//  - The union is deduplicated and total: B wins every conflict.
void TestMergeRadixLevelSources(unsigned r, unsigned block_bits,
                                size_t c_per_bucket, size_t b_per_bucket,
                                size_t shared, uint64_t seed) {
  const bs::Layout layout = TestLayout();
  const size_t bucket_bytes = layout.BucketBytes();
  const size_t block = size_t{1} << block_bits;
  auto c_table = bs::Table::Create(block * r, layout);
  auto b_table = bs::Table::Create(block, layout);
  std::memset(c_table.data.get(), 0, block * r * bucket_bytes);
  std::memset(b_table.data.get(), 0, block * bucket_bytes);
  std::mt19937_64 rng(seed);

  // Per C bucket: key -> which side it must come from (0 = B, 1 = C).
  std::vector<std::map<uint64_t, unsigned>> want(block * r);
  uint64_t next_key = 1;

  for (size_t i = 0; i < block; ++i) {
    uint8_t* b = b_table.Bucket(i);
    std::vector<uint64_t> b_keys;
    std::vector<unsigned> b_digits;
    for (size_t e = 0; e < b_per_bucket; ++e) {
      // Key 0 in the first bucket: the value the dedup kernel's dummy-zeroing
      // collapses onto and then has to repair.
      const uint64_t key = (i == 0 && e == 0) ? 0 : next_key++;
      const unsigned digit = static_cast<unsigned>(rng() % r);
      WriteKey(b, e, layout.key_bytes, key);
      SetTag(layout, b, e, 0);
      SetDigit(layout, b, e, digit);
      b_keys.push_back(key);
      b_digits.push_back(digit);
      want[i + digit * block][key] = 0;
    }
    b_table.masks[i] = bs::LowMask64(static_cast<unsigned>(b_per_bucket));
    for (size_t e = b_per_bucket; e < bs::kBucketCapacity; ++e) {
      WriteKey(b, e, layout.key_bytes, 1 + (rng() % (next_key + 1)));
      SetDigit(layout, b, e, static_cast<unsigned>(rng() % r));
    }

    for (unsigned q = 0; q < r; ++q) {
      const size_t ci = i + static_cast<size_t>(q) * block;
      uint8_t* c = c_table.Bucket(ci);
      // The C-side duplicates of B keys have to be keys whose digit really is
      // q: a B key destined elsewhere could not be in this bucket to begin
      // with, and seeding one would be testing an unreachable state.
      std::vector<uint64_t> shared_here;
      for (size_t k = 0; k < b_keys.size(); ++k) {
        if (b_digits[k] == q) shared_here.push_back(b_keys[k]);
      }
      for (size_t e = 0; e < c_per_bucket; ++e) {
        const bool dup = e < shared && e < shared_here.size();
        const uint64_t key = dup ? shared_here[e] : next_key++;
        WriteKey(c, e, layout.key_bytes, key);
        SetTag(layout, c, e, 1);
        SetDigit(layout, c, e, q);
        // B wins outright: a duplicate leaves no trace of the C copy.
        if (!dup) want[ci][key] = 1;
      }
      c_table.masks[ci] = bs::LowMask64(static_cast<unsigned>(c_per_bucket));
      for (size_t e = c_per_bucket; e < bs::kBucketCapacity; ++e) {
        WriteKey(c, e, layout.key_bytes, 1 + (rng() % (next_key + 1)));
      }
    }
  }

  auto b_before = bs::Table::Create(block, layout);
  std::memcpy(b_before.data.get(), b_table.data.get(), block * bucket_bytes);
  std::memcpy(b_before.masks.get(), b_table.masks.get(),
              block * sizeof(uint64_t));

  bs::ResidualStash no_stash;
  no_stash.entry_bytes = layout.EntryBytes();
  Expect(bs::MergeRadixLevelSources</*CheckOverflow=*/true>(
             bs::View(c_table), bs::View(b_table), r, no_stash),
         "the mixed-radix fixed merge overflowed with room to spare");

  Expect(std::memcmp(b_before.data.get(), b_table.data.get(),
                     block * bucket_bytes) == 0,
         "the merge modified the fresher operand's bytes");
  Expect(std::memcmp(b_before.masks.get(), b_table.masks.get(),
                     block * sizeof(uint64_t)) == 0,
         "the merge clobbered the fresher operand's mask -- the src_mask copy "
         "is missing, r-fold");

  for (size_t ci = 0; ci < block * r; ++ci) {
    std::map<uint64_t, unsigned> got;
    for (const Entry& e :
         BucketEntries(layout, c_table.Bucket(ci), c_table.masks[ci])) {
      Expect(got.find(e.key) == got.end(),
             "the merged bucket holds one key twice");
      got[e.key] = e.block;
    }
    Expect(got == want[ci],
           "the mixed-radix merge is not the deduplicated union, or put an "
           "entry in the wrong block");
    if (got != want[ci]) return;
  }
}

// r = 1 is a power-of-two table, and the kernel has to be the binary
// MergeFixedLevelSourcesRange there byte for byte -- that is what makes it safe
// to route every branching factor through one call site.
void TestMergeRadixMatchesBinaryAtRadixOne(unsigned block_bits,
                                           size_t c_per_bucket,
                                           size_t b_per_bucket,
                                           uint64_t seed) {
  const bs::Layout layout = TestLayout();
  const size_t bucket_bytes = layout.BucketBytes();
  const size_t block = size_t{1} << block_bits;
  auto c_radix = bs::Table::Create(block, layout);
  auto c_binary = bs::Table::Create(block, layout);
  auto b_table = bs::Table::Create(block, layout);
  std::memset(c_radix.data.get(), 0, block * bucket_bytes);
  std::memset(b_table.data.get(), 0, block * bucket_bytes);
  std::mt19937_64 rng(seed);

  uint64_t next_key = 1;
  for (size_t i = 0; i < block; ++i) {
    uint8_t* b = b_table.Bucket(i);
    uint8_t* c = c_radix.Bucket(i);
    for (size_t e = 0; e < b_per_bucket; ++e) {
      WriteKey(b, e, layout.key_bytes, next_key++);
      // Junk in the digit byte: at r = 1 it is an ordinary tag byte and the
      // kernel must not read it as a direction.
      SetDigit(layout, b, e, static_cast<unsigned>(rng()));
    }
    b_table.masks[i] = bs::LowMask64(static_cast<unsigned>(b_per_bucket));
    for (size_t e = 0; e < c_per_bucket; ++e) {
      // Half the C entries duplicate a B key of the same bucket.
      const bool dup = (e % 2) == 0 && e / 2 < b_per_bucket;
      WriteKey(c, e, layout.key_bytes,
               dup ? ReadKey(b, e / 2, layout.key_bytes) : next_key++);
      SetDigit(layout, c, e, static_cast<unsigned>(rng()));
    }
    c_radix.masks[i] = bs::LowMask64(static_cast<unsigned>(c_per_bucket));
  }
  std::memcpy(c_binary.data.get(), c_radix.data.get(), block * bucket_bytes);
  std::memcpy(c_binary.masks.get(), c_radix.masks.get(),
              block * sizeof(uint64_t));

  bs::ResidualStash no_stash;
  no_stash.entry_bytes = layout.EntryBytes();
  bs::ResidualStash no_stash2;
  no_stash2.entry_bytes = layout.EntryBytes();
  Expect(bs::MergeRadixLevelSources</*CheckOverflow=*/true>(
             bs::View(c_radix), bs::View(b_table), 1, no_stash),
         "the radix merge refused a union the binary one accepts");
  Expect(bs::MergeFixedLevelSources</*CheckOverflow=*/true>(
             bs::View(c_binary), bs::View(b_table), no_stash2),
         "the binary fixed merge overflowed");
  Expect(std::memcmp(c_radix.data.get(), c_binary.data.get(),
                     block * bucket_bytes) == 0,
         "at r = 1 the radix merge is not byte-identical to the binary one");
  Expect(std::memcmp(c_radix.masks.get(), c_binary.masks.get(),
                     block * sizeof(uint64_t)) == 0,
         "at r = 1 the radix merge produced different occupancy masks");
}

// ---------------------------------------------------------------------------
// The residual second chance on a mixed-radix main
// ---------------------------------------------------------------------------
//
// The correctness-relevant part is the retag: on a table of m * 2^K buckets
// an entry's destination is idx(T), not T, so a residual has to be tagged with
// WHERE IT IS GOING.  Everything else -- the range routing, the
// b >> index_bits pairing, the sweep's low-bit match -- is arithmetic on that
// index and needs nothing radix-specific.  The range table is a DIRECT plan at the main's
// depth (DirectResidualRangePlan, the separated B tail's shape): the pool
// itself, tagged under the residual map, so the sweep's full-index match does
// all of the selection.
//
// The reference is the PRODUCTION ROUTER, not a second copy of the formula: the
// same keys are put through the butterfly and radix-pass kernels under the
// main rebuild's own map, and the residual has to land in the bucket that
// router chose.  The two maps differ only in where the digit is written -- the reserved
// top tag byte for the main rebuild, so the radix pass can compare a whole byte
// line; just above the index field for the residual, so the stored word IS the
// flat index -- and a hand-recomputed destination could agree with a wrong pair
// of shifts while the router disagreed with both.
//
// `stash_buckets` is the pool's CAPACITY, which is what the range table is
// sized from -- pass 0 to pack the residuals densely, or a larger count for a
// pool of several slots.
void TestResidualSecondChanceOnMixedRadix(unsigned r, unsigned block_bits,
                                          size_t n_residuals,
                                          size_t stash_buckets,
                                          uint64_t seed) {
  bs::Layout layout = TestLayout();
  // The flat index needs block_bits + ceil(log2 r) bits and the range table
  // routes on the top of them, so give the tag room and let the map place the
  // digit rather than the layout.
  layout.tag_bytes = 4;
  const size_t block = size_t{1} << block_bits;
  const size_t num_buckets = block * r;
  const uint64_t nonce_lo = 0x51D3u + seed;
  const uint64_t nonce_hi = 0xB10Cu + seed;

  // The main rebuild's map (digit in the top tag byte) and the residual pass's
  // (digit just above the index field).  Same kind, same modulus.
  bs::RoutingIndexMap main_map;
  main_map.kind = bs::TagMapKind::kRadixDigit;
  main_map.low_bits = block_bits;
  main_map.modulus = r;
  main_map.digit_shift = static_cast<unsigned>(8 * (layout.tag_bytes - 1));
  bs::RoutingIndexMap residual_map = main_map;
  residual_map.digit_shift = main_map.low_bits;

  auto main = bs::Table::Create(num_buckets, layout);
  std::memset(main.data.get(), 0, num_buckets * layout.BucketBytes());
  for (size_t b = 0; b < num_buckets; ++b) main.masks[b] = 0;

  // The pool, exactly as the butterfly-level stashes hand it over: one slot
  // per stash, each at most kMaxResidualStashBuckets buckets, flattened into
  // one bucket index space by ScatterResidualPoolRange.
  const size_t packed = (n_residuals + bs::kBucketCapacity - 1) /
                        bs::kBucketCapacity;
  const size_t pool_buckets = std::max(packed, stash_buckets);
  const size_t per_slot = bs::kMaxResidualStashBuckets;
  const size_t num_slots = (pool_buckets + per_slot - 1) / per_slot;
  bs::Table stash_backing = bs::Table::Create(pool_buckets, layout);
  std::memset(stash_backing.data.get(), 0,
              pool_buckets * layout.BucketBytes());
  std::vector<bs::ResidualStash> stashes(num_slots);
  std::vector<bs::ResidualStash*> pool(num_slots);
  size_t at = 0;
  for (size_t s = 0; s < num_slots; ++s) {
    const size_t n = std::min(per_slot, pool_buckets - at);
    stashes[s].data = stash_backing.Bucket(at);
    stashes[s].num_buckets = n;
    stashes[s].entry_bytes = layout.EntryBytes();
    pool[s] = &stashes[s];
    at += n;
  }
  auto pool_bucket = [&](size_t flat) -> bs::ResidualStash& {
    return stashes[flat / per_slot];
  };
  std::mt19937_64 rng(seed);
  std::vector<uint64_t> keys;
  for (size_t i = 0; i < n_residuals; ++i) {
    const uint64_t key = 1 + rng() % 0xFFFFFFFFull;
    // Round robin over the pool's buckets rather than filling them in turn.
    const size_t flat = i % pool_buckets;
    const size_t e = i / pool_buckets;
    Expect(e < bs::kBucketCapacity, "the residual pool is overfull");
    bs::ResidualStash& slot = pool_bucket(flat);
    const size_t b = flat % per_slot;
    WriteKey(slot.Bucket(b), e, layout.key_bytes, key);
    slot.masks[b] |= uint64_t{1} << e;
    keys.push_back(key);
  }

  // ceil(log2 M), which is what makes the ranges COVER a table that is not a
  // power of two; the top ranges then stay empty.
  const unsigned main_levels = bs::Log2Exact(num_buckets);
  Expect((size_t{1} << main_levels) >= num_buckets,
         "the range sizing does not cover the mixed-radix main");
  const bs::ResidualRangePlan plan =
      bs::DirectResidualRangePlan(pool_buckets, main_levels);
  auto range = bs::Table::Create(plan.range_buckets, layout);
  std::memset(range.data.get(), 0, plan.range_buckets * layout.BucketBytes());
  bs::ScatterResidualPoolRange(pool.data(), num_slots, bs::View(range), plan,
                               0, bs::ResidualScatterGroups(bs::View(range),
                                                            plan));
  bs::ComputeRoutingTags(bs::View(range), nonce_lo, nonce_hi, residual_map, 0,
                         bs::DefaultAesTagKeys());
  // kNoDedup is what a block re-offered its own shed runs: the
  // pool holds each key at most once, so no main bucket is
  // ever offered two copies however many sub-tables it is swept against.
  bs::ResidualSecondChanceSweep<bs::ResidualDedupRule::kNoDedup>(
      bs::View(main), bs::View(range), plan, layout.EntryBytes());

  std::map<uint64_t, size_t> placed;
  for (size_t b = 0; b < num_buckets; ++b) {
    for (const Entry& e : BucketEntries(layout, main.Bucket(b), main.masks[b])) {
      Expect(placed.emplace(e.key, b).second,
             "a residual was placed in two buckets at once");
    }
  }
  size_t left = 0;
  for (size_t b = 0; b < plan.range_buckets; ++b) {
    left += bs::Popcount64(range.masks[b]);
  }
  Expect(left == 0,
         "the mixed-radix sweep left residuals behind in an empty table");
  Expect(placed.size() == keys.size(),
         "the mixed-radix sweep lost or duplicated a residual");

  // The reference: the same keys, routed by the real thing.  One entry per
  // bucket of a sparse table, so no MergeSplit can shed and every key ends
  // exactly where the map sends it.
  auto reference = bs::Table::Create(num_buckets, layout);
  std::memset(reference.data.get(), 0, num_buckets * layout.BucketBytes());
  for (size_t b = 0; b < num_buckets; ++b) reference.masks[b] = 0;
  for (size_t i = 0; i < keys.size(); ++i) {
    const size_t b = i % num_buckets;
    const size_t e = i / num_buckets;
    Expect(e < bs::kBucketCapacity, "the reference table is overfull");
    WriteKey(reference.Bucket(b), e, layout.key_bytes, keys[i]);
    reference.masks[b] |= uint64_t{1} << e;
  }
  bs::ComputeRoutingTags(bs::View(reference), nonce_lo, nonce_hi, main_map, 0,
                         bs::DefaultAesTagKeys());
  std::vector<bs::ResidualStash> level_stashes(block_bits);
  for (bs::ResidualStash& s : level_stashes) s.entry_bytes = layout.EntryBytes();
  bs::ResidualStash radix_stash;
  radix_stash.entry_bytes = layout.EntryBytes();
  // Each block's butterfly, then the cross-block radix pass.
  bool routed = true;
  for (unsigned q = 0; q < r; ++q) {
    routed = routed &&
             bs::ButterflyRouteStashCacheOblivious</*CheckOverflow=*/true>(
                 bs::SubView(bs::View(reference), q * block, block), block_bits,
                 level_stashes.data());
  }
  routed = routed && bs::RadixPassStash</*CheckOverflow=*/true>(
                         bs::View(reference), block_bits, r, radix_stash);
  Expect(routed,
         "the reference route shed, so it is not a placement reference");
  for (size_t b = 0; b < num_buckets; ++b) {
    for (const Entry& e :
         BucketEntries(layout, reference.Bucket(b), reference.masks[b])) {
      const auto it = placed.find(e.key);
      Expect(it != placed.end() && it->second == b,
             "a residual landed somewhere other than where the router put it");
    }
  }
  std::printf(
      "  mixed-radix second chance r=%u * 2^%u buckets, %zu residuals in %zu "
      "pool buckets: %zu x 2^%u ranges (%zu slots/input), all placed where the "
      "router put them\n",
      r, block_bits, n_residuals, pool_buckets, plan.groups, plan.range_bits,
      plan.scatter_per_bucket);
}

}  // namespace

int main() {
  // r = 3 is B = 4's only radix; 5 and 7 are B = 8's.
  for (uint64_t seed = 0; seed < 4; ++seed) {
    for (unsigned r : {3u, 5u, 7u}) {
      TestRadixPassDedup(r, /*block_bits=*/4, /*per_bucket=*/12,
                         /*dup_high=*/false, 0x7100 + seed * 16 + r);
      TestRadixPassDedup(r, /*block_bits=*/4, /*per_bucket=*/12,
                         /*dup_high=*/true, 0x7200 + seed * 16 + r);
      // Load 0.5's mean occupancy, where the tuple is nearly full.
      TestRadixPassDedup(r, /*block_bits=*/3, /*per_bucket=*/32,
                         /*dup_high=*/false, 0x7300 + seed * 16 + r);
    }
  }

  for (uint64_t seed = 0; seed < 4; ++seed) {
    for (unsigned r : {3u, 5u, 7u}) {
      // C starts around 21 per bucket (A's contents spread over r blocks) and
      // B's ~32 split r ways: the occupancy a real final sweep sees.
      TestMergeRadixLevelSources(r, /*block_bits=*/4, /*c_per_bucket=*/21,
                                 /*b_per_bucket=*/32, /*shared=*/4,
                                 0x8100 + seed * 16 + r);
      TestMergeRadixLevelSources(r, /*block_bits=*/3, /*c_per_bucket=*/8,
                                 /*b_per_bucket=*/16, /*shared=*/0,
                                 0x8200 + seed * 16 + r);
      TestMergeRadixLevelSources(r, /*block_bits=*/3, /*c_per_bucket=*/32,
                                 /*b_per_bucket=*/8, /*shared=*/8,
                                 0x8300 + seed * 16 + r);
    }
    TestMergeRadixMatchesBinaryAtRadixOne(/*block_bits=*/4,
                                          /*c_per_bucket=*/24,
                                          /*b_per_bucket=*/24, 0x8400 + seed);
  }

  // The residual second chance: both radices of both branching factors.
  for (uint64_t seed = 0; seed < 4; ++seed) {
    for (unsigned r : {3u, 5u, 7u}) {
      TestResidualSecondChanceOnMixedRadix(r, /*block_bits=*/6,
                                           /*n_residuals=*/64,
                                           /*stash_buckets=*/0,
                                           0x9100 + seed * 16 + r);
      TestResidualSecondChanceOnMixedRadix(r, /*block_bits=*/3,
                                           /*n_residuals=*/8,
                                           /*stash_buckets=*/0,
                                           0x9200 + seed * 16 + r);
      TestResidualSecondChanceOnMixedRadix(r, /*block_bits=*/5,
                                           /*n_residuals=*/130,
                                           /*stash_buckets=*/0,
                                           0x9300 + seed * 16 + r);
      // A pool of several slots, larger than the main.
      TestResidualSecondChanceOnMixedRadix(r, /*block_bits=*/2,
                                           /*n_residuals=*/200,
                                           /*stash_buckets=*/40,
                                           0x9400 + seed * 16 + r);
    }
  }

  if (failures != 0) {
    std::fprintf(stderr, "%d mixed-radix kernel checks failed\n", failures);
    return 1;
  }
  std::printf("base-B absorb and fixed-merge kernels ok\n");
  return 0;
}
