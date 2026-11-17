// Key matching inside one 64-slot byte-sliced bucket (key byte b of slot s at
// bucket[b * 64 + s]).  The generic, scalar and register matchers must agree
// with a scalar oracle on every stored key width: a match requires the full
// stored key AND a set occupancy (live) bit, so stale keys left in dummy slots
// never match, duplicates are all reported, and the all-zero key is an
// ordinary key rather than a sentinel.
//
// The dense-slot recovery (MatchUniqueDenseSlots, used by the batch probe on
// the dense buckets the engine publishes with unique live keys) is checked for
// the exact row/column-derived slot of every lane.  For two-word (16-byte)
// stored keys it must compare COMPLETE keys: adversarial buckets whose low and
// high halves come from different keys must not produce a match.  Under the
// approximate segment matcher (kWideKeySegmentMatch, on hosts with
// VP2INTERSECT), halves may match different partners; there the test checks
// that full-key verification rejects such a candidate -- a false negative
// counted in the access error budget, never a wrong value -- and skips the
// adversarial all-lane cases that only the exact path promises.
#include "src/oram/table/cpu_byteslice_probe.hpp"
#include "src/oram/table/cpu_byteslice_batch_probe.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"
#include "src/oram/table/cpu_byteslice_dense_match.hpp"
#include <algorithm>
#include <random>

namespace bs = microram::byteslice;
using microram::byteslice::test_support::Expect;

uint64_t Oracle(const uint8_t* bucket, size_t bytes, uint64_t live, bs::KeyWords key) {
  uint64_t result = 0;
  for (unsigned slot = 0; slot < 64; ++slot) {
    bool equal = true;
    for (size_t b = 0; b < bytes; ++b) {
      const uint64_t word = b < 8 ? key.w0 : key.w1;
      equal &= bucket[b * 64 + slot] == static_cast<uint8_t>(word >> (8 * (b % 8)));
    }
    if (equal && ((live >> slot) & 1)) result |= uint64_t{1} << slot;
  }
  return result;
}

template<size_t Width, size_t Field>
void TestDenseSlots() {
  std::mt19937_64 rng(14219 + Width);
  alignas(64) uint8_t bucket[(Width + 17) * 64];
  alignas(64) uint8_t slots[64], values[17 * 64];
  bs::KeyWords queries[64], keys[64];
  bs::DenseMatchQueries prepared;
  for (unsigned trial = 0; trial < 40; ++trial) {
    for (unsigned s = 0; s < 64; ++s) {
      keys[s] = {(rng() & ~uint64_t{255}) | s, rng()};
      if constexpr (Width == 16) {
        // Real zero fields, including keys with only the upper field nonzero.
        if (trial % 3 == 0) keys[s].w1 = 0;
        if (trial % 3 == 1) keys[s] = {0, (rng() & ~uint64_t{255}) | s};
      }
      if (s == 0) keys[s] = {};
      if (s == 63) keys[s] = {~uint64_t{0}, ~uint64_t{0}};
      bs::WriteSlotKey(bucket, s, Width, keys[s]);
    }
    for (size_t b = Width * 64; b < sizeof(bucket); ++b) bucket[b] = uint8_t(rng());
    for (unsigned j = 0; j < 64; ++j)
      queries[j] = (j + trial) % 3 ? keys[(j * 13 + trial) % 64] : bs::KeyWords{rng(), rng()};
    queries[0] = {}; // zero is a real key, not a dummy sentinel
    queries[1] = queries[2]; // duplicate queries do not require unique lanes
    const uint64_t live = trial % 4 == 0 ? 0 : trial % 4 == 1 ? ~uint64_t{0} : rng();
    for (size_t lanes = 0; lanes <= 64; ++lanes) {
      bs::PrepareDenseMatchQueries<Field, Width / Field>(queries, lanes, prepared);
      uint64_t hits = bs::MatchUniqueDenseSlots<Field, Width / Field>(bucket, live, prepared, lanes, slots);
      std::memset(values, 0xA5, sizeof(values));
      bs::ExtractDenseWave(bucket, Width, 17, slots, hits, values);
      for (size_t j = 0; j < 64; ++j) {
        uint64_t expected = j < lanes ? Oracle(bucket, Width, live, queries[j]) : 0;
        Expect(((hits >> j) & 1) == unsigned(expected != 0), "direct-slot hit equals scalar oracle");
        if (expected) Expect(expected == (uint64_t{1} << slots[j]), "direct slot preserves slot identity");
        for (size_t v = 0; v < 17; ++v) {
          uint8_t want = expected ? bucket[(Width + v) * 64 + _tzcnt_u64(expected)] : 0xA5;
          Expect(values[v * 64 + j] == want, "direct slot extracts exact value and preserves misses/tails");
        }
      }
    }
  }
}

void TestWideRecoveryVerification() {
  alignas(64) uint8_t bucket[16 * 64]{};
  alignas(64) uint8_t slots[64]{};
  bs::KeyWords keys[64]{};
  keys[0] = {1, 2};
  bs::DenseMatchQueries query;
  bs::PrepareDenseMatchQueries<8, 2>(keys, 1, query);
  // Different donors satisfy both fields in row 7 and column 1. Approximate
  // recovery (kWideKeySegmentMatch) selects (4,2), hiding the actual complete
  // key in slot zero; it MUST NOT return a value or clear an entry.
  bs::WriteSlotKey(bucket, 0, 16, {1, 2});
  bs::WriteSlotKey(bucket, 1, 16, {1, 9});
  bs::WriteSlotKey(bucket, 56, 16, {1, 3});
  bs::WriteSlotKey(bucket, 57, 16, {4, 2});
  const uint64_t live = 3 | (uint64_t{3} << 56);
  const uint64_t hits =
      bs::MatchUniqueDenseSlots<8, 2>(bucket, live, query, 1, slots);
  if (bs::kWideKeySegmentMatch) {
    Expect(hits == 0, "full verification rejects mixed-donor recovery "
                      "(a budgeted false negative)");
  } else {
    Expect(hits == 1 && slots[0] == 0,
           "mixed donors must not displace a true complete-key hit");
  }
  // Full-key equality at an inactive stale slot is insufficient as well.
  std::memset(slots, 0, sizeof(slots));
  Expect(bs::VerifyDenseMatchSlots(bucket, query, slots, live & ~uint64_t{1}, 1) == 0,
         "verification rejects stale inactive copy even when all key bytes match");
}

// Check both membership and the exact row/column-derived slot for every public
// batch width. The scalar oracle reads complete stored keys independently.
void CheckWideDenseCase(const uint8_t* bucket, uint64_t live,
                        const bs::KeyWords* queries) {
  alignas(64) uint8_t slots[64], values[3 * 64];
  uint64_t expected[64];
  for (size_t j = 0; j < 64; ++j) {
    expected[j] = Oracle(bucket, 16, live, queries[j]);
    Expect((expected[j] & (expected[j] - 1)) == 0,
           "dense fixtures must have unique complete live keys");
  }
  bs::DenseMatchQueries prepared;
  for (size_t lanes = 0; lanes <= 64; ++lanes) {
    bs::PrepareDenseMatchQueries<8, 2>(queries, lanes, prepared);
    const uint64_t hits =
        bs::MatchUniqueDenseSlots<8, 2>(bucket, live, prepared, lanes, slots);
    std::memset(values, 0xA5, sizeof(values));
    bs::ExtractDenseWave(bucket, 16, 3, slots, hits, values);
    for (size_t j = 0; j < 64; ++j) {
      const uint64_t want = j < lanes ? expected[j] : 0;
      Expect(((hits >> j) & 1) == unsigned(want != 0),
             "wide row/column membership must equal complete-key equality");
      if (want)
        Expect((uint64_t{1} << slots[j]) == want,
               "wide row and column must recover the same true partner");
      for (size_t v = 0; v < 3; ++v) {
        const uint8_t value = want
            ? bucket[(16 + v) * 64 + _tzcnt_u64(want)] : 0xA5;
        Expect(values[v * 64 + j] == value,
               "adversarial dense recovery preserves exact values and misses");
      }
    }
  }
}

void TestWideDenseDisplacementAllLanes() {
  alignas(64) uint8_t bucket[19 * 64];
  bs::KeyWords queries[64];
  const bs::KeyWords victims[] = {{1, 2}, {1, 0}, {0, 2}, {0, 0}};
  for (bs::KeyWords victim : victims) {
    for (size_t true_slot = 0; true_slot < 64; ++true_slot) {
      const bs::KeyWords keys[] = {
          victim, {victim.w0, victim.w1 + 9},
          {victim.w0, victim.w1 + 13}, {victim.w0 + 4, victim.w1}};
      const size_t positions[] = {0, 1, 56, 57};
      // Stale exact copies in every dummy lane must not affect slot recovery.
      for (size_t slot = 0; slot < 64; ++slot) {
        bs::WriteSlotKey(bucket, slot, 16, victim);
        for (size_t v = 0; v < 3; ++v)
          bucket[(16 + v) * 64 + slot] = uint8_t(slot + 67 * v);
      }
      uint64_t live = 0;
      for (size_t k = 0; k < 4; ++k) {
        const size_t row = (positions[k] / 8 + true_slot / 8) % 8;
        const size_t col = (positions[k] % 8 + true_slot % 8) % 8;
        const size_t slot = row * 8 + col;
        bs::WriteSlotKey(bucket, slot, 16, keys[k]);
        live |= uint64_t{1} << slot;
      }
      for (size_t j = 0; j < 64; ++j)
        queries[j] = j % 5 < 4 ? keys[j % 5]
                               : bs::KeyWords{victim.w0 + 17, victim.w1 + 23};
      CheckWideDenseCase(bucket, live, queries);
    }
  }
}

void TestWideDenseSharedHalves() {
  std::mt19937_64 rng(0xD3E5E128);
  alignas(64) uint8_t bucket[19 * 64];
  bs::KeyWords keys[64], queries[64];
  for (unsigned trial = 0; trial < 48; ++trial) {
    // All 64 combinations of eight low and high halves are distinct full
    // keys. Shuffle their physical slots to create false subset memberships.
    uint64_t low[8], high[8];
    size_t permutation[64];
    for (size_t i = 0; i < 8; ++i) {
      low[i] = i == 0 ? 0 : (rng() & ~uint64_t{7}) | i;
      high[i] = i == 0 ? 0 : (rng() & ~uint64_t{7}) | i;
    }
    for (size_t i = 0; i < 64; ++i) permutation[i] = i;
    std::shuffle(std::begin(permutation), std::end(permutation), rng);
    const uint64_t live = trial % 4 == 0 ? 0
        : trial % 4 == 1 ? ~uint64_t{0} : rng();
    for (size_t slot = 0; slot < 64; ++slot)
      keys[slot] = {low[permutation[slot] % 8], high[permutation[slot] / 8]};
    for (size_t slot = 0; slot < 64; ++slot) {
      const bs::KeyWords stored = ((live >> slot) & 1) ? keys[slot]
          : slot % 2 ? keys[rng() % 64] : bs::KeyWords{rng(), rng()};
      bs::WriteSlotKey(bucket, slot, 16, stored);
      for (size_t v = 0; v < 3; ++v)
        bucket[(16 + v) * 64 + slot] = uint8_t(rng());
      queries[slot] = keys[(slot + trial) % 64];
      if (trial % 2 && slot % 5 == 0) queries[slot] = {rng(), rng()};
    }
    if (trial % 2) queries[1] = queries[2];
    CheckWideDenseCase(bucket, live, queries);
  }
}

int main() {
  TestDenseSlots<4, 4>();
  TestDenseSlots<8, 8>();
  TestDenseSlots<16, 8>();
  TestWideRecoveryVerification();
  // Adversarial halves: exact recovery only (the _exact_wide twin on a
  // kWideKeySegmentMatch host).
  if (!bs::kWideKeySegmentMatch) {
    TestWideDenseDisplacementAllLanes();
    TestWideDenseSharedHalves();
  }
  std::mt19937_64 rng(9217);
  for (size_t bytes = 1; bytes <= 16; ++bytes) {
    bs::Layout layout;
    layout.key_bytes = bytes;
    auto table = bs::Table::Create(1, layout);
    uint8_t* bucket = table.Bucket(0);
    for (unsigned trial = 0; trial < 100; ++trial) {
      bs::KeyWords keys[64];
      for (unsigned slot = 0; slot < 64; ++slot) {
        keys[slot] = {rng(), rng()};
        if (slot == 0) keys[slot] = {};
        if (slot == 63) keys[slot] = {~uint64_t{0}, ~uint64_t{0}};
        if (slot % 7 == 1) keys[slot] = keys[0];
        bs::WriteSlotKey(bucket, slot, bytes, keys[slot]);
      }
      const uint64_t live = trial % 4 == 0 ? 0 : trial % 4 == 1 ? ~uint64_t{0} : rng();
      __m512i lines[16];
      for (size_t b = 0; b < bytes; ++b) lines[b] = microram::core::obliLoad512(bucket + b * 64);
      for (size_t j = 0; j < 80; ++j) {
        const bs::KeyWords key = j < 64 ? keys[j] : bs::KeyWords{rng(), rng()};
        const uint64_t expected = Oracle(bucket, bytes, live, key);
        Expect(bs::MatchMaskByteSliced(bucket, live, layout, key) == expected,
               "generic matching must preserve all real duplicates and ignore dummies");
        Expect(bs::MatchMaskByteSlicedTree(bucket, live, layout, key) == expected,
               "scalar matching must preserve all real duplicates and ignore dummies");
        Expect(bs::MatchMaskFromKeyLines(lines, bytes, live, key) == expected,
               "register matching must preserve all real duplicates and ignore dummies");
      }
    }
  }
  std::puts("cpu_byteslice_batch_match_test passed");
}
