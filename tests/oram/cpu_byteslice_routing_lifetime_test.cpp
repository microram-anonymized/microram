// Routing admission counts actual padded evaluations across every executor.
// Exhaustion is terminal: an interrupted rebuild or value job is not retried.
// This is the engine-level half of the routing budget
// (src/oram/levelarena/DESIGN.md, "Routing budget"): every requester, value
// worker, batch participant, rebuild owner and helper borrows the one
// counter, and a refusal must leave the engine failed rather than resumable.
#include <array>
#include <cstdint>
#include <cstdio>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

#include "cpu_byteslice_oram/byte_map.hpp"

namespace {
namespace bs = microram::byteslice;
namespace la = bs::levelarena;
namespace oram = cpu_byteslice_oram;
using Engine = la::LevelArenaEngine;
using Value = std::array<uint8_t, 8>;
const Value kValue{{3, 1, 4, 1, 5, 9, 2, 6}};

void Check(bool condition, const char* message) {
  if (!condition) throw std::runtime_error(message);
}

template <class Fn>
void Refuses(Fn&& fn, const char* message) {
  try {
    fn();
  } catch (const std::overflow_error& error) {
    Check(std::string(error.what()).find("routing evaluation budget") !=
              std::string::npos,
          "refusal must identify the routing allowance");
    return;
  }
  throw std::runtime_error(message);
}

Engine::Options Options(bool synchronous = false) {
  Engine::Options options;
  options.geometry.branching = 2;
  options.geometry.levels = 2;
  options.geometry.top_digit = 2;
  options.geometry.prefix_flushes = 2;
  options.geometry.stash_buckets = 1;
  options.geometry.dense_prefixes = 2;
  options.key_bytes = 8;
  options.value_bytes = 8;
  options.max_accesses = 4096;
  options.synchronous = synchronous;
  options.flush_policy = Engine::FlushPolicy::kSettle;
  options.secret_seed = microram::crypto::SecretKeySeed::Fixed(0x123456);
  options.batch_spin_nanos = 0;
  options.wait_limit_millis = 5000;
  return options;
}

// Derive the number from the public candidate schedule, independently of the
// limiter and its leaf wrappers. A real/dummy pair is evaluated for every
// hashed table, including candidates the cascade will not select.
uint64_t ProbeEvaluations(Engine& engine) {
  engine.ProbeListLength();
  const uint64_t candidates =
      2 * engine.publisher().CurrentPlan()->addressing.hashed;
  Check(candidates != 0, "fixture must contain a hashed probe");
  return ((candidates + 3) / 4) * 4;
}

void CheckStopped(Engine& engine) {
  Check(engine.Failed(), "routing refusal must permanently fail the engine");
  const uint64_t count = engine.RoutingEvaluationCount();
  const uint64_t accesses = engine.AccessCount();
  Value out;
  out.fill(0xa5);
  const Value sentinel = out;
  Refuses([&] { engine.Read(uint64_t{7}, out.data()); }, "read resumed stopped engine");
  Refuses([&] { engine.Write(uint64_t{7}, kValue.data()); }, "blind write resumed stopped engine");
  Refuses([&] { engine.Drain(); }, "drain resumed stopped engine");
  Refuses([&] { engine.StepOnce(); }, "step resumed stopped engine");
  Refuses([&] { engine.StartOwnerThreads(); }, "owner start ignored stopped engine");
  Refuses([&] { engine.AccessBatch(0, static_cast<const bs::BatchRequest64*>(nullptr), nullptr); },
          "empty batch resumed stopped engine");
  const uint64_t key = 7;
  Refuses([&] { engine.StoredKey(reinterpret_cast<const uint8_t*>(&key)); },
          "standalone key conversion resumed stopped engine");
  Check(out == sentinel && engine.AccessCount() == accesses &&
            engine.RoutingEvaluationCount() == count,
        "stopped public calls must preserve replies and counters");
}

void TestInitialization(bool synchronous) {
  const uint64_t keys[] = {7, 9};
  const bs::InitializationEntry entries[] = {
      {reinterpret_cast<const uint8_t*>(&keys[0]), kValue.data()},
      {reinterpret_cast<const uint8_t*>(&keys[1]), kValue.data()}};
  uint64_t routed = 0;
  {
    Engine engine(Options(synchronous));
    Check(engine.RoutingEvaluationCount() == 0 &&
              engine.MaxRoutingEvaluations() == std::numeric_limits<uint64_t>::max(),
          "construction must expose the default unused allowance");
    engine.Initialize(entries, 0);
    Check(engine.RoutingEvaluationCount() == 0, "empty initialization spent routing work");
    engine.Initialize(entries, 1);
    routed = engine.RoutingEvaluationCount();
    Check(routed >= 64 * engine.geometry().TopBuckets() && routed % 32 == 0,
          "initialization must account for whole physical routing buckets");
    Check(engine.AccessCount() == 0, "initialization consumed online accesses");
    Value out{};
    Check(engine.Read(keys[0], out.data()) && out == kValue,
          "accounted initialization changed the logical result");
  }
  {
    Engine engine(Options(synchronous));
    engine.Initialize(entries, 2);
    Check(engine.RoutingEvaluationCount() == routed,
          "initial route volume must include dummy slots independently of live count");
  }
  {
    auto options = Options(synchronous);
    options.max_routing_evaluations = routed - 1;
    Engine engine(options);
    const auto* before = engine.publisher().CurrentPlan();
    const uint64_t epoch = before->epoch;
    Refuses([&] { engine.Initialize(entries, 1); }, "initial route exceeded its allowance");
    Check(engine.RoutingEvaluationCount() == routed - 32 &&
              engine.AccessCount() == 0 && engine.dense().positions() == 0 &&
              engine.publisher().CurrentPlan()->epoch == epoch,
          "failed initialization must retain spent routing and publish nothing");
    Refuses([&] { engine.Initialize(entries, 1); }, "failed initial route was retried");
    Refuses([&] { engine.Initialize(entries, 0); }, "empty initialization ignored terminal failure");
    CheckStopped(engine);
  }
}

void TestScalarAndBatch(bool synchronous) {
  auto options = Options(synchronous);
  Engine engine(options);
  engine.Write(uint64_t{7}, kValue.data());
  Check(engine.RoutingEvaluationCount() == 0, "blind dense insertion performed routing");
  const uint64_t per_lane = ProbeEvaluations(engine);
  const uint64_t candidates = 2 * engine.publisher().CurrentPlan()->addressing.hashed;
  Check(per_lane > candidates, "fixture must exercise a padded scalar tail");
  Value out{};
  Check(engine.Read(uint64_t{7}, out.data()) && out == kValue,
        "scalar accounting changed a present result");
  Check(engine.RoutingEvaluationCount() == per_lane,
        "scalar route count must include real, dummy and SIMD padding");
  std::array<Value, 3> outputs{};
  std::array<uint8_t, 3> found{};
  const bs::BatchRequest64 requests[] = {
      {bs::BatchOp::kRead, false, 7, nullptr, outputs[0].data()},
      {bs::BatchOp::kRead, false, 9, nullptr, outputs[1].data()},
      {bs::BatchOp::kRead, false, 7, nullptr, outputs[2].data()}};
  engine.AccessBatch(3, requests, found.data());
  Check(engine.RoutingEvaluationCount() == 4 * per_lane &&
            found == std::array<uint8_t, 3>{{1, 0, 1}} &&
            outputs[0] == kValue && outputs[1] == Value{} && outputs[2] == kValue,
        "batch accounting must include padded duplicate lanes without changing forwarding");

  options.max_routing_evaluations = per_lane;
  Engine stopped(options);
  stopped.Write(uint64_t{7}, kValue.data());
  Check(stopped.Read(uint64_t{7}, out.data()), "last admitted probe failed");
  out.fill(0xa5);
  const Value sentinel = out;
  Refuses([&] { stopped.Read(uint64_t{7}, out.data()); }, "scalar exceeded exact allowance");
  Check(out == sentinel && stopped.AccessCount() == 2 &&
            stopped.RoutingEvaluationCount() == per_lane,
        "scalar routing refusal must precede replies and online insertion");
  CheckStopped(stopped);
}

void TestParallelBatch(bool synchronous) {
  auto options = Options(synchronous);
  options.batch_execution = la::BatchExecutionShape::kParallelTiles;
  options.batch_lanes = 2;
  options.batch_participants = 3;
  uint64_t per_lane;
  {
    Engine reference(options);
    per_lane = ProbeEvaluations(reference);
  }
  options.max_routing_evaluations = 6 * per_lane - 1;
  Engine engine(options);
  engine.Write(uint64_t{7}, kValue.data());
  std::array<Value, 6> outputs;
  for (auto& out : outputs) out.fill(0xa5);
  const auto sentinel = outputs;
  std::array<uint8_t, 6> found;
  found.fill(0xa5);
  const auto found_sentinel = found;
  std::array<bs::BatchRequest64, 6> requests;
  for (size_t i = 0; i < requests.size(); ++i)
    requests[i] = {bs::BatchOp::kRead, false, 7 + i, nullptr, outputs[i].data()};
  Refuses([&] { engine.AccessBatch(requests.size(), requests.data(), found.data()); },
          "parallel participants exceeded the shared allowance");
  Check(outputs == sentinel && found == found_sentinel && engine.AccessCount() == 1 &&
            engine.RoutingEvaluationCount() == 4 * per_lane,
        "joined batch refusal must preserve replies and count successful tile reservations");
  CheckStopped(engine);
}

void TestValueWorkers(bool synchronous, bool serial) {
  auto options = Options(synchronous);
  options.value_bytes = 64;
  options.value_workers = 3;
  options.value_tail = 0;
  options.value_serial = serial;
  options.value_spin_nanos = 0;
  std::array<uint8_t, 64> value;
  value.fill(0x5a);
  uint64_t per_lane;
  {
    Engine engine(options);
    Check(engine.ValueWorkers() == 3, "value worker fixture was not enabled");
    per_lane = ProbeEvaluations(engine);
    engine.Write(uint64_t{7}, value.data());
    Check(engine.PendingValue(), "fixture must have a pending previous payload");
    std::array<uint8_t, 64> out{};
    Check(engine.Read(uint64_t{7}, out.data()) && out == value,
          "repeated worker routing changed the payload result");
    Check(engine.RoutingEvaluationCount() == 4 * per_lane,
          "requester and every value worker must spend their repeated evaluations");
    engine.AccessBatch(0, static_cast<const bs::BatchRequest64*>(nullptr), nullptr);
    Check(engine.RoutingEvaluationCount() == 4 * per_lane && !engine.PendingValue(),
          "empty batch payload drain must spend no routing evaluations");
  }
  options.max_routing_evaluations = 3 * per_lane;
  Engine engine(options);
  engine.Write(uint64_t{7}, value.data());
  std::array<uint8_t, 64> out{};
  Refuses([&] { engine.Read(uint64_t{7}, out.data()); },
          "value worker routing exceeded the shared allowance");
  Check(engine.Failed() && engine.RoutingEvaluationCount() == 3 * per_lane,
        "value worker refusal must join, retain reservations and fail the instance");
  Refuses([&] { engine.Drain(); }, "failed value work was retried by draining");
  // Destruction joins even when a worker failed before committing the preceding
  // pending value. Its logical contents are intentionally not inspected.
}

void TestRebuild(bool synchronous, bool threaded) {
  auto options = Options(synchronous);
  options.max_routing_evaluations = 32;
  options.preroute = false;
  if (threaded) {
    options.owner_threads = 2;
    options.defer_owner_start = true;
    options.owner_spin_nanos = 0;
    options.lanes.lanes = 2;
    options.lanes.min_buckets = 1;
    options.top_helpers = 1;
    options.flush_policy = Engine::FlushPolicy::kHandOver;
  }
  Engine engine(options);
  Refuses([&] {
    if (threaded) engine.StartOwnerThreads();
    // Blind writes isolate routing performed by scheduled/speculative rebuild
    // work; no online probe can spend the allowance.
    for (uint64_t i = 0; i < 4 * engine.geometry().PrefixPositions(); ++i)
      engine.Write(i % 7, kValue.data());
    engine.Drain();
  }, "rebuild work failed to enforce its routing allowance");
  Check(engine.RoutingEvaluationCount() == 32 && engine.Failed(),
        "partial bucket rebuild must retain its first reservation and stop");
  Refuses([&] { engine.Write(uint64_t{7}, kValue.data()); }, "failed rebuild admitted another write");
  Refuses([&] { engine.Drain(); }, "failed rebuild resumed during drain");
}

void TestSpeculativeRebuild(bool threaded) {
  auto options = Options();
  options.max_routing_evaluations = 32;
  if (threaded) {
    options.owner_threads = 2;
    options.defer_owner_start = true;
    options.owner_spin_nanos = 0;
    options.lanes.lanes = 2;
    options.lanes.min_buckets = 1;
    options.top_helpers = 1;
  }
  Engine engine(options);
  Refuses([&] {
    if (threaded) engine.StartOwnerThreads();
    engine.Drain();
  }, "speculative top preparation ignored its allowance");
  Check(engine.AccessCount() == 0 && engine.RoutingEvaluationCount() == 32 &&
            engine.Failed(),
        "speculative routing must be charged before any online request");
  Refuses([&] { engine.StartOwnerThreads(); }, "owner restart ignored routing failure");
}

template <bool Deamortize>
void TestPublicOption() {
  oram::Options options;
  options.max_accesses = 4096;
  options.deamortized_owner_threads = 0;
  options.deamortized_online_stash_entries = 64;
  options.max_routing_evaluations = 0;
  oram::ByteMap<Deamortize> map(128, 8, 8, options);
  Check(map.engine().MaxRoutingEvaluations() == 0,
        "public map did not forward the routing allowance");
  const uint64_t key = 7;
  Value out;
  out.fill(0xa5);
  const Value sentinel = out;
  Refuses([&] { map.find(reinterpret_cast<const uint8_t*>(&key), out.data()); },
          "public map ignored zero routing allowance");
  Check(map.failed() && out == sentinel && map.access_count() == 0,
        "public map must report terminal routing refusal before first reply");
}
}  // namespace

int main() {
  try {
    for (bool synchronous : {false, true}) {
      TestInitialization(synchronous);
      TestScalarAndBatch(synchronous);
      TestParallelBatch(synchronous);
      for (bool serial : {false, true}) TestValueWorkers(synchronous, serial);
      TestRebuild(synchronous, false);
    }
    TestRebuild(false, true);
    TestSpeculativeRebuild(false);
    TestSpeculativeRebuild(true);
    TestPublicOption<false>();
    TestPublicOption<true>();
    std::puts("routing lifetime tests passed");
    return 0;
  } catch (const std::exception& error) {
    std::fprintf(stderr, "routing lifetime test failed: %s\n", error.what());
    return 1;
  }
}
