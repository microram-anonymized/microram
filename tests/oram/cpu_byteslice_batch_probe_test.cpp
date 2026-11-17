// Correctness tests for the batch primitives of
// src/oram/table/cpu_byteslice_batch_probe.hpp, each against a scalar
// reference that spells the intended semantics out one lane at a time:
//
//  - DedupBatchLanes: the conflict set of every lane is exactly the earlier
//    lanes holding the same stored key, at 1–4, 8 and 16 stored bytes (where a
//    key equal in one word but not the other must NOT conflict), for every
//    chunk width that crosses an eight- or sixteen-lane group boundary.
//  - ResolveHashedProbeAddressesBatch: lane for lane, the candidate pointers
//    the per-access pass ResolveHashedProbeAddresses writes for the same key
//    and the same dummy counter, also checked against scalar routing and an
//    independent index calculation over power-of-two and mixed-radix tables.
//  - ForwardBatchLane: a chunk of mixed read / write / erase / exchange lanes
//    over a small key pool returns and leaves behind exactly what running the
//    same lanes one at a time against a reference map would.
//
// Together these are what lets a batch of up to 64 accesses share one probe
// of the hierarchy: only the first lane holding a key probes real candidate
// buckets, a repeated lane probes fresh dummy buckets instead (so the trace
// does not reveal the repetition), and the repeated lane's answer is forwarded
// from the earlier lanes of the chunk.

#include "src/oram/table/cpu_byteslice_batch_probe.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"

#include <array>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <map>
#include <random>
#include <vector>

namespace {

namespace bs = microram::byteslice;
using microram::byteslice::test_support::Expect;

// ---------------------------------------------------------------------------
// Dedup
// ---------------------------------------------------------------------------

void TestDedup(const std::vector<bs::KeyWords>& keys, size_t key_bytes) {
  bs::BatchDedup d;
  bs::DedupBatchLanes(keys.data(), keys.size(), key_bytes, &d);
  uint64_t want_dup = 0, want_sup = 0;
  for (size_t j = 0; j < keys.size(); ++j) {
    uint64_t conf = 0;
    unsigned prev = static_cast<unsigned>(j);
    for (size_t i = 0; i < j; ++i) {
      const bool eq = key_bytes > 8 ? keys[i] == keys[j]
                                    : keys[i].w0 == keys[j].w0;
      if (eq) {
        conf |= uint64_t{1} << i;
        prev = static_cast<unsigned>(i);
      }
    }
    Expect(d.conflicts[j] == conf, "dedup: conflict set differs");
    Expect(d.prev[j] == prev, "dedup: prev differs");
    if (conf != 0) want_dup |= uint64_t{1} << j;
    want_sup |= conf;
  }
  Expect(d.duplicates == want_dup, "dedup: duplicates mask differs");
  Expect(d.superseded == want_sup, "dedup: superseded mask differs");
}

void TestDedupWidths(uint64_t seed) {
  std::mt19937_64 rng(seed);
  const size_t widths[] = {0, 1, 2, 3, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64};
  for (size_t key_bytes : {size_t{1}, size_t{2}, size_t{3}, size_t{4}, size_t{8}, size_t{16}}) {
    for (size_t m : widths) {
      for (int round = 0; round < 8; ++round) {
        // A pool small enough that repeats are common; at 16 bytes, half the
        // pool shares its low word with another member so the high word has
        // to be compared too.
        const size_t pool = 1 + rng() % 12;
        std::vector<bs::KeyWords> keys(m);
        for (size_t j = 0; j < m; ++j) {
          const uint64_t p = rng() % pool;
          const uint64_t lo = 0x1000 + (p / 2) * 0x9E3779B97F4A7C15ull;
          const uint64_t hi = key_bytes > 8 ? (p % 2) * 0xABCDEFull + 7 : 0;
          keys[j] = bs::MaskKey(key_bytes > 8 ? bs::KeyWords{lo, hi}
                                                : bs::KeyWords{lo + p}, key_bytes);
        }
        TestDedup(keys, key_bytes);
      }
    }
  }
  // Degenerate shapes: all equal, all distinct.
  for (size_t m : {size_t{1}, size_t{8}, size_t{64}}) {
    std::vector<bs::KeyWords> same(m, bs::KeyWords{42});
    TestDedup(same, 8);
    std::vector<bs::KeyWords> distinct(m);
    for (size_t j = 0; j < m; ++j) distinct[j] = bs::KeyWords{1000 + j};
    TestDedup(distinct, 8);
  }
  // Zeros, all-ones and duplicate chains spanning every dword group boundary.
  for (size_t key_bytes : {1u, 2u, 3u, 4u}) {
    for (size_t m = 0; m <= 64; ++m) {
      std::vector<bs::KeyWords> keys(m);
      for (size_t j = 0; j < m; ++j) {
        keys[j] = bs::MaskKey(bs::KeyWords{j % 3 == 0 ? ~uint64_t{0} : j % 5}, key_bytes);
      }
      TestDedup(keys, key_bytes);
      std::fill(keys.begin(), keys.end(), bs::KeyWords{});
      TestDedup(keys, key_bytes);
    }
  }
  // Neither half alone defines an eight-byte conflict. The two halves must
  // match the SAME earlier lane, both within and across 16-lane groups.
  for (size_t bytes : {5u, 6u, 7u, 8u}) {
    for (size_t m = 0; m <= 64; ++m) {
      std::vector<bs::KeyWords> keys(m);
      for (size_t j = 0; j < m; ++j)
        keys[j] = bs::KeyWords{((j % 7) << 32) | (j % 5)};
      TestDedup(keys, bytes);
      if (m > 32) {
        keys[0] = bs::KeyWords{1};
        keys[15] = bs::KeyWords{uint64_t{1} << 32};
        keys[16] = bs::KeyWords{(uint64_t{1} << 32) | 1};
        keys[31] = keys[0];
        keys[32] = keys[16];
        TestDedup(keys, bytes);
      }
    }
  }
  std::puts("  dedup: ok");
}

// ---------------------------------------------------------------------------
// The batched address pass
// ---------------------------------------------------------------------------

struct FakeTable {
  bs::Aligned64Ptr data;
  std::vector<uint64_t> masks;
  size_t buckets = 0;
  uint64_t real_lo = 0, real_hi = 0;
  uint64_t dummy_lo = 0, dummy_hi = 0;
};

void TestAddressPassBatch(uint64_t seed, size_t cascade_tables) {
  bs::Layout layout;  // 8 / 16 / 4
  const size_t bucket_bytes = layout.BucketBytes();
  std::mt19937_64 rng(seed);
  // Up to six hashed tables: power-of-two and mixed radix, with dense
  // placeholders at 0 and 3 so cascade indices and hashed slots differ.
  // Odd hashed-table counts exercise the padded final SIMD group.
  struct Shape { unsigned index_bits; unsigned radix; };
  const Shape shapes[] = {{6, 1}, {5, 3}, {8, 1}, {4, 7}, {7, 5}, {9, 1}};
  std::vector<FakeTable> tables;
  bs::ProbeAddressing a;
  a.Begin(cascade_tables - 1 - (cascade_tables > 3 ? 1 : 0));
  size_t hashed = 0;
  for (size_t i = 0; i < cascade_tables; ++i) {
    if (i == 0 || i == 3) continue;
    const Shape s = shapes[hashed];
    FakeTable t;
    t.buckets = static_cast<size_t>(s.radix) << s.index_bits;
    t.data = bs::AllocateAligned64(t.buckets * bucket_bytes);
    t.masks.assign(t.buckets, 0);
    t.real_lo = rng() & microram::crypto::kAesCtrLevelMask;
    t.real_hi = rng() & microram::crypto::kAesCtrCounterMask;
    t.dummy_lo = t.real_lo | microram::crypto::kAesCtrDomainBit;
    t.dummy_hi = t.real_hi;
    a.AddHashed(static_cast<uint32_t>(i), t.data.get(), t.masks.data(),
                s.index_bits, s.radix,
                microram::crypto::PackAesCtrHighWord(t.real_lo, t.real_hi),
                microram::crypto::PackAesCtrHighWord(t.dummy_lo, t.dummy_hi), i);
    tables.push_back(std::move(t));
    ++hashed;
  }
  const auto scalar_aes = microram::crypto::DeriveRoutingAesRoundKeys(
      microram::crypto::SecretKeySeed::Fixed(seed));
  const auto vector_aes = bs::MakeAesTagKeys(scalar_aes);
  const bs::AesTagKeys& aes = *vector_aes;
  bs::BatchProbeScratch batch;
  batch.Resize(bs::kMaxBatchLanes, cascade_tables, hashed);
  bs::ProbeScratch single;
  single.Resize(cascade_tables, hashed);
  const size_t padded_messages = ((2 * hashed + 3) / 4) * 4;
  Expect(a.aes_template.size() == 4 * padded_messages &&
             a.aes_index.size() == a.aes_template.size() &&
             single.blocks.size() == a.aes_template.size() &&
             single.tags.size() == padded_messages,
         "address pass: two-block message scratch has the wrong extent");
  const auto extents = bs::ProbeScratch::BufferSizes(cascade_tables, hashed);
  Expect(extents == std::array<size_t, 4>{
             single.blocks.size() * sizeof(uint64_t),
             single.tags.size() * sizeof(uint64_t),
             single.bucket.size() * sizeof(uint8_t*),
             single.mask.size() * sizeof(uint64_t*)},
         "address pass: scalar storage report differs from allocated buffers");
  Expect(bs::BatchProbeScratch::Bytes(bs::kMaxBatchLanes, cascade_tables, hashed) ==
             (batch.blocks.size() + batch.tags.size()) * sizeof(uint64_t) +
             batch.bucket.size() * sizeof(uint8_t*) +
             batch.mask.size() * sizeof(uint64_t*),
         "address pass: batch storage report differs from allocated buffers");
  for (size_t m = 0; m <= 64; ++m) {
    for (size_t key_bytes : {size_t{1}, size_t{8}, size_t{9}, size_t{15}, size_t{16}}) {
      std::vector<bs::KeyWords> keys(m);
      for (size_t j = 0; j < m; ++j) {
        keys[j] = bs::MaskKey(bs::KeyWords{rng(), rng()}, key_bytes);
      }
      if (m > 1) keys[m - 1] = keys[0];
      const uint64_t dummy_base = rng() >> 1;
      const uint64_t stride = cascade_tables;
      bs::ResolveHashedProbeAddressesBatch(a, keys.data(), m, dummy_base,
                                           stride, bucket_bytes, aes, batch);
      for (size_t j = 0; j < m; ++j) {
        bs::ResolveHashedProbeAddresses(a, keys[j], dummy_base + j * stride,
                                        bucket_bytes, aes, single);
        for (size_t i = 0; i < cascade_tables; ++i) {
          if (i == 0 || i == 3) continue;
          for (unsigned half = 0; half < 2; ++half) {
            Expect(batch.LaneBuckets(j)[2 * i + half] ==
                       single.bucket[2 * i + half],
                   "address pass: bucket candidate differs from the "
                   "per-access pass");
            Expect(batch.LaneMasks(j)[2 * i + half] ==
                       single.mask[2 * i + half],
                   "address pass: mask candidate differs from the per-access "
                   "pass");
            // And a candidate lies inside its table.
            const size_t table_slot = i < 3 ? i - 1 : i - 2;
            const FakeTable& t = tables[table_slot];
            const ptrdiff_t off = batch.LaneBuckets(j)[2 * i + half] -
                                  t.data.get();
            Expect(off >= 0 && static_cast<size_t>(off) <
                                   t.buckets * bucket_bytes &&
                       off % static_cast<ptrdiff_t>(bucket_bytes) == 0,
                   "address pass: candidate outside its table");
            const uint64_t tag = half == 0
                ? microram::crypto::AesCtrTagU128WordsHost(
                      t.real_lo, t.real_hi, keys[j].w0, keys[j].w1, scalar_aes)
                : microram::crypto::AesCtrTagU64WordsHost(
                      t.dummy_lo, t.dummy_hi,
                      dummy_base + j * stride + i, scalar_aes);
            const Shape s = shapes[table_slot];
            const size_t expected_bucket =
                (tag & ((uint64_t{1} << s.index_bits) - 1)) |
                (((tag >> s.index_bits) % s.radix) << s.index_bits);
            Expect(batch.LaneBuckets(j)[2 * i + half] ==
                       t.data.get() + expected_bucket * bucket_bytes &&
                       batch.LaneMasks(j)[2 * i + half] ==
                       t.masks.data() + expected_bucket,
                   "address pass: candidate differs from scalar routing oracle");
          }
        }
        // Two lanes with the same key get the same REAL candidates and
        // different DUMMY ones.
        for (size_t k = 0; k < j; ++k) {
          if (!(keys[k] == keys[j])) continue;
          for (size_t i = 0; i < cascade_tables; ++i) {
            if (i == 0 || i == 3) continue;
            Expect(batch.LaneBuckets(j)[2 * i] == batch.LaneBuckets(k)[2 * i],
                   "equal keys resolve to different real candidates");
          }
        }
      }
    }
  }
  std::puts("  address pass: ok");
}

// ---------------------------------------------------------------------------
// Forwarding
// ---------------------------------------------------------------------------

struct RefEntry {
  bool exists = false;   // some entry (live or tombstone) is known
  bool erased = false;
  std::vector<uint8_t> value;
};

struct Lane {
  bs::BatchOp op;
  bool insert;
  uint64_t key;
  std::vector<uint8_t> value_in;
};

void TestForwardChain(uint64_t seed, size_t value_bytes) {
  std::mt19937_64 rng(seed);
  bs::BatchForwardState state;
  state.Resize(value_bytes);
  for (int round = 0; round < 64; ++round) {
    const size_t m = 1 + rng() % bs::kMaxBatchLanes;
    const size_t pool = 1 + rng() % 6;
    // The reference map BEFORE the chunk: some keys live, some tombstones,
    // some unknown.
    std::map<uint64_t, RefEntry> ref;
    for (uint64_t k = 0; k < pool; ++k) {
      RefEntry e;
      const unsigned kind = rng() % 3;
      e.exists = kind != 0;
      e.erased = kind == 2;
      e.value.resize(value_bytes);
      if (kind == 1) for (auto& b : e.value) b = static_cast<uint8_t>(rng());
      ref[k] = e;
    }
    std::vector<Lane> lanes(m);
    std::vector<bs::KeyWords> keys(m);
    for (size_t j = 0; j < m; ++j) {
      lanes[j].op = static_cast<bs::BatchOp>(rng() % 4);
      lanes[j].insert = (rng() & 1) != 0;
      lanes[j].key = rng() % pool;
      lanes[j].value_in.resize(value_bytes);
      for (auto& b : lanes[j].value_in) b = static_cast<uint8_t>(rng());
      keys[j] = bs::KeyWords{lanes[j].key};
    }
    bs::BatchDedup dedup;
    bs::DedupBatchLanes(keys.data(), m, 8, &dedup);

    // The probe result of every lane: the reference state before the chunk
    // for a first occurrence, garbage for a repeat (the batch never reads it).
    std::vector<std::vector<uint8_t>> probe_rows(m);
    std::vector<uint64_t> probe_found(m);
    for (size_t j = 0; j < m; ++j) {
      probe_rows[j].resize(value_bytes + 1);
      const bool dup = ((dedup.duplicates >> j) & 1) != 0;
      if (dup) {
        for (auto& b : probe_rows[j]) b = static_cast<uint8_t>(rng());
        probe_found[j] = rng() & 1;
        continue;
      }
      const RefEntry& e = ref[lanes[j].key];
      probe_found[j] = e.exists;
      if (e.exists) {
        std::memcpy(probe_rows[j].data(), e.value.data(), value_bytes);
        probe_rows[j][value_bytes] = e.erased ? bs::kMetaErased : 0;
      }
    }

    // Run the chain and the scalar model side by side.
    std::map<uint64_t, RefEntry> model = ref;
    std::vector<uint8_t> insert_value(value_bytes);
    std::vector<uint8_t> value_out(value_bytes);
    for (size_t j = 0; j < m; ++j) {
      const Lane& l = lanes[j];
      const bool dup = ((dedup.duplicates >> j) & 1) != 0;
      bs::BatchLaneInsert ins;
      ins.value = insert_value.data();
      std::fill(value_out.begin(), value_out.end(), 0xEE);
      const bool present = bs::ForwardBatchLane(
          l.op, l.insert, probe_rows[j].data(), probe_found[j], dup,
          dedup.prev[j], l.value_in.data(), value_out.data(), j, state, &ins);

      // The model: what the serial access would have returned and inserted.
      RefEntry& e = model[l.key];
      const bool want_present = e.exists && !e.erased;
      std::vector<uint8_t> want_out(value_bytes, 0);
      if (e.exists && !e.erased) want_out = e.value;
      RefEntry after;
      after.exists = true;
      after.value.resize(value_bytes);
      switch (l.op) {
        case bs::BatchOp::kRead:
          after.erased = !e.exists || e.erased;
          if (!after.erased) after.value = e.value;
          break;
        case bs::BatchOp::kWrite:
          after.erased = false;
          after.value = l.value_in;
          break;
        case bs::BatchOp::kErase:
          after.erased = true;
          break;
        case bs::BatchOp::kExchange: {
          const bool store = want_present || l.insert;
          after.erased = !store;
          if (store) after.value = l.value_in;
          break;
        }
      }
      Expect(present == want_present, "forward: present flag differs");
      Expect(value_out == want_out, "forward: returned value differs");
      Expect(ins.erased == after.erased, "forward: inserted tombstone bit differs");
      Expect(insert_value == after.value, "forward: inserted value differs");
      e = after;
    }
  }
  std::printf("  forwarding chain (%zu-byte values): ok\n", value_bytes);
}

}  // namespace

int main() {
  TestDedupWidths(0xD3D0);
  TestAddressPassBatch(0xADD2, 2);
  TestAddressPassBatch(0xADD3, 7);
  TestAddressPassBatch(0xADD4, 8);
  TestForwardChain(0xF0F0, 16);
  TestForwardChain(0xF0F1, 8);
  TestForwardChain(0xF0F2, 33);
  std::puts("cpu_byteslice_batch_probe_test passed");
  return 0;
}
