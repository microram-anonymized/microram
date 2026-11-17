// LARGE INSERTION UNITS: `Options::deamortized_online_stash_entries` well
// above its 64-entry default, which is the knob that says how many entries the
// online stash takes before it flushes one unit into the hierarchy.
//
// This file asks the public question only: that a unit far larger than the
// default still resolves to a valid geometry, still flushes exactly once per
// unit of accesses (the flush schedule is public, a function of the access
// count alone), and still answers every operation the way a std::map does --
// scalar and batched, at wide keys and wide values, after a bulk load and
// after a drain.  The engine's internals at those shapes (its dense side is a
// ring of prefixes of flushed stash buckets) are covered by the
// cpu_byteslice_level_arena_* fixtures.
#include <cpu_byteslice_oram/oram.hpp>
#include "tests/oram/cpu_byteslice_test_support.hpp"

#include <algorithm>
#include <array>
#include <cstdio>
#include <cstring>
#include <map>
#include <vector>

namespace {
namespace bs = microram::byteslice;
namespace api = cpu_byteslice_oram;
using bs::test_support::Expect;
using bs::test_support::ExpectThrows;
using Value = std::array<uint8_t, 16>;

std::array<uint8_t, 8> KeyOf(uint64_t key) {
  std::array<uint8_t, 8> bytes{};
  std::memcpy(bytes.data(), &key, sizeof(key));
  return bytes;
}

api::Options Options(size_t entries, unsigned owner_threads,
                     unsigned participants, api::BatchExecutionShape mode) {
  api::Options options;
  options.deamortized_online_stash_entries = entries;
  options.deamortized_owner_threads = owner_threads;
  options.deamortized_batch_participants = participants;
  options.deamortized_batch_execution = mode;
  options.deamortized_batch_lanes = 64;
  options.deamortized_branching_factor = 4;
  options.secret_seed = microram::crypto::SecretKeySeed::Fixed(174);
  return options;
}

// One unit width, driven through a full capacity cycle of mixed batches.
void Check(size_t entries, unsigned owner_threads, unsigned participants,
           api::BatchExecutionShape mode) {
  api::ByteMap<true> map(4 * entries, 8, sizeof(Value),
                         Options(entries, owner_threads, participants, mode));
  Expect(map.geometry_choice().geometry.stash_buckets == entries / 64,
         "the insertion unit did not reach the geometry");
  Expect(map.capacity() >= 4 * entries,
         "a large-unit map did not cover its request");

  // Scalar writes up to just short of the first flush boundary: the same slot
  // index in different stash buckets must stay independent.
  std::map<uint64_t, Value> model;
  for (size_t i = 0; i + 1 < entries; ++i) {
    Value v{};
    v[0] = static_cast<uint8_t>(i);
    v[1] = static_cast<uint8_t>(i >> 8);
    map.insert_without_probe(KeyOf(i).data(), v.data());
    model[i] = v;
    Expect(map.flush_count() == 0,
           "the stash flushed before its configured boundary");
  }
  Value out{};
  Expect(map.find(KeyOf(0).data(), out.data()) && out == model[0],
         "a key in the current unit did not read back");
  Expect(map.flush_count() == 1,
         "the stash did not flush at its configured boundary");
  map.drain_rebuilds();
  for (const auto& entry : model) {
    Expect(map.find(KeyOf(entry.first).data(), out.data()) &&
               out == entry.second,
           "a key was lost across the first large flush");
  }

  // Full cycles, cross-bucket and cross-tile repeats, all four operations and
  // misses, in batches whose length straddles the unit boundary.
  const size_t total = 3 * map.capacity();
  size_t serial = 0;
  for (size_t done = 0; done < total;) {
    const size_t n = std::min<size_t>(done % 2 ? entries + 1 : entries - 1,
                                      total - done);
    std::vector<std::array<uint8_t, 8>> keys(n);
    std::vector<Value> input(n), expected(n), actual(n);
    std::vector<uint8_t> expected_found(n), found(n);
    std::vector<api::BatchRequest> requests(n);
    for (size_t i = 0; i < n; ++i, ++serial) {
      const uint64_t key = (serial * 11 + serial / 31) % (entries + 37);
      keys[i] = KeyOf(key);
      input[i][0] = static_cast<uint8_t>(serial);
      input[i][1] = static_cast<uint8_t>(serial >> 8);
      const auto op = static_cast<api::BatchOp>((serial / 7) % 4);
      const bool insert = serial % 2;
      const auto it = model.find(key);
      expected_found[i] = it != model.end();
      if (it != model.end()) expected[i] = it->second;
      if (op == api::BatchOp::kErase) model.erase(key);
      if (op == api::BatchOp::kWrite ||
          (op == api::BatchOp::kExchange &&
           (insert || expected_found[i] != 0))) {
        model[key] = input[i];
      }
      requests[i] = {op, insert, keys[i].data(), input[i].data(),
                     actual[i].data()};
    }
    map.access_batch(n, requests.data(), found.data());
    Expect(found == expected_found && actual == expected,
           "a large-unit batch differs from the oracle");
    Expect(map.flush_count() == map.access_count() / entries,
           "the flush frequency differs from accesses / unit");
    done += n;
  }
  map.drain_rebuilds();
  for (const auto& entry : model) {
    Expect(map.find(KeyOf(entry.first).data(), out.data()) &&
               out == entry.second,
           "a post-rebuild value was lost at a large unit");
  }
}

// A large unit with WIDE keys and a value wider than a line, bulk-loaded
// rather than written one access at a time, then read back several times so
// the reads span many flushes.
void WideKeysAndInitialization() {
  api::Options options = Options(1024, /*owner_threads=*/2,
                                 /*participants=*/3,
                                 api::BatchExecutionShape::kParallelTiles);
  api::ByteMap<true> map(8192, 16, 65, options);
  const size_t n = 2051;
  std::vector<std::array<uint8_t, 16>> keys(n);
  std::vector<std::array<uint8_t, 65>> values(n), out(n);
  std::vector<api::InitializationEntry> entries(n);
  for (size_t i = 0; i < n; ++i) {
    keys[i][0] = 19;
    std::memcpy(keys[i].data() + 8, &i, sizeof(i));
    values[i].fill(static_cast<uint8_t>(i));
    values[i][64] = static_cast<uint8_t>(i >> 8);
    entries[i] = {keys[i].data(), values[i].data()};
  }
  map.initialize(entries.begin(), n);
  std::vector<api::BatchRequest> requests(n);
  std::vector<uint8_t> found(n);
  for (unsigned cycle = 0; cycle < 5; ++cycle) {
    for (size_t i = 0; i < n; ++i) {
      requests[i] = {api::BatchOp::kRead, false, keys[i].data(), nullptr,
                     out[i].data()};
    }
    map.access_batch(n, requests.data(), found.data());
    Expect(out == values &&
               std::all_of(found.begin(), found.end(),
                           [](uint8_t x) { return x == 1; }),
           "initialized wide keys/values lost across large flushes");
  }
  map.drain_rebuilds();
}

// The public surface at a large unit, and the units that are refused rather
// than rounded: the online stash is a whole number of 64-entry buckets and the
// geometry says so by naming the public knob.
void PublicAndValidation() {
  api::Options options = Options(1024, /*owner_threads=*/0, /*participants=*/1,
                                 api::BatchExecutionShape::kChunkedCascade);
  api::ByteMap<true> map(8192, 8, sizeof(Value), options);
  std::array<uint8_t, 8> key{};
  Value v{};
  v[0] = 73;
  Value out{};
  map.insert_or_assign(key.data(), v.data());
  Expect(map.find(key.data(), out.data()) && out == v,
         "a large-unit map built through the public surface is unusable");
  for (size_t bad : {size_t{0}, size_t{63}, size_t{65}, size_t{4095}}) {
    options.deamortized_online_stash_entries = bad;
    ExpectThrows([&] { api::ByteMap<true> reject(8192, 8, sizeof(Value),
                                                 options); },
                 "an insertion unit that is not a multiple of 64 was accepted");
  }
}

}  // namespace

int main() {
  PublicAndValidation();
  WideKeysAndInitialization();
  // The unit ladder, on the deterministic inline executor.
  for (size_t entries : {size_t{64}, size_t{128}, size_t{256}, size_t{512},
                         size_t{1024}, size_t{2048}}) {
    Check(entries, /*owner_threads=*/0, /*participants=*/1,
          api::BatchExecutionShape::kChunkedCascade);
  }
  // ...and with owner threads driving the hierarchy beside the batch, in both
  // batch shapes.
  Check(512, /*owner_threads=*/2, /*participants=*/3,
        api::BatchExecutionShape::kParallelTiles);
  Check(1024, /*owner_threads=*/2, /*participants=*/1,
        api::BatchExecutionShape::kChunkedCascade);
  std::puts("cpu_byteslice_large_flush_test passed");
}
