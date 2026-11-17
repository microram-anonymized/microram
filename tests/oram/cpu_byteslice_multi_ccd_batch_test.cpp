// Runtime batch concurrency through the PUBLIC surface, plus the topology
// resolver, without machine-dependent pins.
//
// THE QUESTION THIS FILE ASKS: that a caller can BUILD a batch participant
// pool (threads that scan a batch's lanes alongside the request thread),
// MOVE the participant count and the lane width at run time, and get the same
// answers at every combination, and that the option surface says no to the
// combinations no engine implements.  That is all reachable through
// `ByteMap`/`Map`/`HybridByteMap`, so that is what it is driven through;
// `cpu_byteslice_level_arena_batch_test` owns the engine-level schedule.
#include <cpu_byteslice_oram/oram.hpp>
#include "benchmarks/oram/cpu_byteslice_benchmark_topology.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"
#include <array>
#include <atomic>
#include <cstdio>
#include <cstring>
#include <map>
#include <string>
#include <vector>

namespace {
namespace bs = microram::byteslice;
namespace api = cpu_byteslice_oram;
using bs::test_support::Expect;
using bs::test_support::ExpectThrows;

constexpr size_t kKeyBytes = 16;

std::array<uint8_t, kKeyBytes> KeyOf(unsigned key) {
  std::array<uint8_t, kKeyBytes> bytes{};
  bytes[0] = static_cast<uint8_t>(key + 1);
  bytes[8] = 71;
  return bytes;
}

// ---------------------------------------------------------------------------
// Runtime concurrency: the participant count and the lane width both move
// while the map is live, and every combination answers the same as a plain
// std::map.
// ---------------------------------------------------------------------------
//
// `capacity` is the pool the map is BUILT with, which is a construction-time
// decision because each participant is a preallocated tile and a persistent
// thread; a caller may then run narrower but never wider.  The batch sizes
// swept per configuration are the ones that bracket a combined job: empty, one
// short, exact, one long, and a run several jobs long.
void TestRuntime(unsigned capacity, api::BatchExecutionShape mode,
                 size_t value_bytes, unsigned owner_threads) {
  api::Options options;
  options.deamortized_batch_participants = capacity;
  options.deamortized_batch_execution = mode;
  options.deamortized_owner_threads = owner_threads;
  options.deamortized_branching_factor = 4;
  options.secret_seed = microram::crypto::SecretKeySeed::Fixed(717);
  api::ByteMap<true> map(2048, kKeyBytes, value_bytes, options);
  Expect(map.batch_participant_capacity() == capacity,
         "the participant pool the map was built with was lost");
  Expect(map.batch_participants() == capacity,
         "the initial participant count is not the pool");

  std::map<unsigned, std::vector<uint8_t>> model;
  uint64_t serial = 0;
  // Every count up to the pool, then a shrink/grow sequence: a pool that is
  // only ever walked upwards would never exercise reusing a tile that has been
  // idle.
  std::vector<unsigned> counts;
  for (unsigned t = 1; t <= capacity; ++t) counts.push_back(t);
  counts.insert(counts.end(), {capacity, std::min(2u, capacity), 1u,
                               std::min(4u, capacity), capacity});

  for (unsigned width : {1u, 7u, 32u, 64u}) {
    map.set_batch_lanes(width);
    Expect(map.batch_lanes() == width, "the lane width setter was lost");
    for (unsigned t : counts) {
      map.set_batch_participants(t);
      // In the chunked shape one thread cuts the batch into chunks, so the
      // combined width is the lane width whatever the participant count; in
      // the parallel shape each participant brings its own tile.
      const size_t combined =
          width * (mode == api::BatchExecutionShape::kParallelTiles ? t : 1);
      Expect(map.max_combined_batch_lanes() == combined,
             "the runtime combined width is not lanes x participants");
      ExpectThrows([&] { map.set_batch_participants(0); },
                   "zero participants accepted");
      ExpectThrows([&] { map.set_batch_participants(capacity + 1); },
                   "participants above the built pool accepted");
      Expect(map.batch_participants() == t && map.batch_lanes() == width,
             "a rejected setter mutated the live configuration");

      for (size_t n : {size_t{0}, combined - 1, combined, combined + 1,
                       size_t{1025}}) {
        // The long call is needed once per width/count, not on every repeat.
        if (n == 1025 && width != 64) continue;
        std::vector<std::array<uint8_t, kKeyBytes>> keys(n);
        std::vector<std::vector<uint8_t>> input(n,
                                                std::vector<uint8_t>(value_bytes));
        std::vector<std::vector<uint8_t>> expected(
            n, std::vector<uint8_t>(value_bytes));
        std::vector<std::vector<uint8_t>> output(
            n, std::vector<uint8_t>(value_bytes));
        std::vector<uint8_t> found(n), expected_found(n);
        std::vector<api::BatchRequest> requests(n);
        for (size_t i = 0; i < n; ++i, ++serial) {
          // Cross-tile repeats, all four operations, present and absent
          // exchanges.
          const unsigned key =
              static_cast<unsigned>((serial * 7 + serial / 13) % 37);
          keys[i] = KeyOf(key);
          std::fill(input[i].begin(), input[i].end(),
                    static_cast<uint8_t>(serial));
          const auto op = static_cast<api::BatchOp>((serial / 3) % 4);
          const bool insert = serial % 2;
          auto it = model.find(key);
          expected_found[i] = it != model.end();
          if (it != model.end()) expected[i] = it->second;
          if (op == api::BatchOp::kErase) model.erase(key);
          if (op == api::BatchOp::kWrite ||
              (op == api::BatchOp::kExchange &&
               (insert || expected_found[i] != 0))) {
            model[key] = input[i];
          }
          requests[i] = {op, insert, keys[i].data(), input[i].data(),
                         output[i].data()};
        }
        const uint64_t accesses = map.access_count();
        map.access_batch(n, requests.data(), found.data());
        Expect(found == expected_found && output == expected,
               "a mixed runtime batch differs from the oracle");
        Expect(map.access_count() == accesses + n,
               "the runtime access accounting lost or repeated a lane");
      }
    }
  }
  map.drain_rebuilds();
  for (unsigned key = 0; key < 37; ++key) {
    const auto bytes = KeyOf(key);
    std::vector<uint8_t> out(value_bytes);
    const bool found = map.find(bytes.data(), out.data());
    Expect(found == (model.count(key) != 0), "post-drain presence mismatch");
    if (found) Expect(out == model.at(key), "post-drain value mismatch");
  }
}

// ---------------------------------------------------------------------------
// The public option surface
// ---------------------------------------------------------------------------

template <class Map>
void CheckPublic(Map& map, unsigned capacity) {
  Expect(map.batch_participant_capacity() == capacity, "public capacity lost");
  for (unsigned t : {capacity, 1u, capacity}) {
    map.set_batch_participants(t);
    Expect(map.batch_participants() == t, "public setter lost");
    ExpectThrows([&] { map.set_batch_participants(0); },
                 "public zero accepted");
    ExpectThrows([&] { map.set_batch_participants(capacity + 1); },
                 "public excess accepted");
    Expect(map.batch_participants() == t,
           "a rejected public setter mutated state");
  }
}

void TestPublicConstruction() {
  api::Options options;
  options.deamortized_batch_participants = 5;
  options.deamortized_batch_execution = api::BatchExecutionShape::kParallelTiles;
  options.deamortized_owner_threads = 3;
  options.deamortized_near_max_level = 0;
  std::atomic<unsigned> online{0}, workers{0};
  // The two placement hooks, which are the only way a caller can put a
  // participant or an owner group on a chosen core.  Participant 0 is the
  // CALLING thread, so a pool of five runs the batch hook four times.
  options.deamortized_batch_thread_init = [&](unsigned) { ++online; };
  options.worker_thread_init = [&](unsigned) { ++workers; };
  {
    api::ByteMap<true> map(500, 8, 16, options);
    Expect(map.batch_participants() == 5, "public initial count lost");
    // OWNER THREADS START ON FIRST USE, not at construction, so that
    // `initialize` stays available at every thread count.
    Expect(workers == 0,
           "the owner threads started before the map was used");
    CheckPublic(map, 5);
    std::array<uint8_t, 8> key{};
    std::array<uint8_t, 16> value{};
    value[0] = 39;
    map.set_batch_participants(5);
    std::vector<api::BatchRequest> requests(
        513, {api::BatchOp::kWrite, false, key.data(), value.data(), nullptr});
    map.access_batch(requests.size(), requests.data(), nullptr);
    map.drain_rebuilds();
    std::array<uint8_t, 16> out{};
    const bool found = map.find(key.data(), out.data());
    Expect(found && out == value, "public split batch result");
  }
  Expect(online == 4 && workers == 3, "public pool options not forwarded");
  { api::Map<uint64_t, uint64_t> map(500, options); CheckPublic(map, 5); }
  { api::HybridByteMap<true> map(500, 8, 16, options); CheckPublic(map, 5); }

  // The counts no engine implements.
  options.deamortized_batch_participants = 9;  // above kMaxOnlineParticipants
  ExpectThrows([&] { api::ByteMap<true> bad(500, 8, 16, options); },
               "a participant pool above the maximum was accepted");
  options.deamortized_batch_participants = 0;
  ExpectThrows([&] { api::ByteMap<true> bad(500, 8, 16, options); },
               "a participant pool of zero was accepted");
  // The CHUNKED shape runs on the calling thread alone and says so rather than
  // quietly ignoring a pool it will not use.
  options.deamortized_batch_participants = 3;
  options.deamortized_batch_execution = api::BatchExecutionShape::kChunkedCascade;
  ExpectThrows([&] { api::ByteMap<true> bad(500, 8, 16, options); },
               "the chunked shape accepted more than one participant");
  options.deamortized_batch_execution = api::BatchExecutionShape::kParallelTiles;
  // The synchronous storage mode shares the batch path, pool included.
  { api::ByteMap<false> map(500, 8, 16, options); CheckPublic(map, 3); }
  options.deamortized_batch_participants = 1;
  { api::ByteMap<false> map(100, 8, 16, options); CheckPublic(map, 1); }
  // The hybrid's TREE selection runs batches serially and refuses a pool,
  // whichever half named it.
  api::HybridOptions hybrid(options);
  hybrid.tree_value_threshold = 1;
  hybrid.tree.payload_max_threads = 0;
  { api::HybridByteMap<true> map(100, 8, 16, hybrid); CheckPublic(map, 1); }
  hybrid.hierarchical.deamortized_batch_participants = 2;
  ExpectThrows([&] { api::HybridByteMap<true> bad(100, 8, 16, hybrid); },
               "the serial tree backend accepted a participant pool");
}

// ---------------------------------------------------------------------------
// The benchmark topology resolver, which places those threads on real CPUs.
// ---------------------------------------------------------------------------

void TestTopology() {
  namespace top = bs::benchmark_topology;
  std::vector<top::Cpu> cpus;
  for (unsigned i = 0; i < 12; ++i)
    cpus.push_back({i, 0, int(i), 0, 0, i < 6 ? "0-5" : "6-11",
                    std::to_string(i), 32u << 20});
  const auto p = top::Resolve(cpus, {0, 1, 2, 3, 4}, {5}, {6, 7});
  Expect(p.local_cores == 6 && p.cpus.size() == 8 && p.l3_bytes == 32u << 20,
         "six-core topology budget");
  ExpectThrows([&] { top::Resolve(cpus, {0, 1, 2, 3, 4}, {5}, {5, 6}); },
               "oversubscribed placement accepted");
  ExpectThrows([&] { top::Resolve(cpus, {0}, {6}, {7}); },
               "remote near worker accepted");
  ExpectThrows([&] { top::Resolve(cpus, {0}, {1}, {2}); },
               "local far worker accepted");
  ExpectThrows([&] { top::Resolve(cpus, {0}, {1}, {12}); },
               "CPU outside allowed mask accepted");
  cpus[7].core = 6;
  ExpectThrows([&] { top::Resolve(cpus, {0}, {1}, {6, 7}); },
               "worker SMT siblings accepted");
}

}  // namespace

int main() {
  TestTopology();
  TestPublicConstruction();
  // The chunked shape at its only legal pool size, the inline executor, and a
  // value narrower than a line.
  TestRuntime(1, api::BatchExecutionShape::kChunkedCascade, 16,
              /*owner_threads=*/0);
  // Parallel tiles, a pool the caller shrinks and grows under traffic, owner
  // threads driving the hierarchy beside them, and a value wider than one.
  TestRuntime(3, api::BatchExecutionShape::kParallelTiles, 16, /*owner_threads=*/2);
  TestRuntime(5, api::BatchExecutionShape::kParallelTiles, 65, /*owner_threads=*/2);
  std::puts("cpu_byteslice_multi_ccd_batch_test passed");
}
