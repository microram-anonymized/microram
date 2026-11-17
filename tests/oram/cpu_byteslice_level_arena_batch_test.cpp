// THE LEVEL-ARENA BATCH PATH: `LevelArenaEngine::AccessBatch`, which serves
// up to 64 lanes of independent requests with one shared probe of the
// hierarchy (src/oram/table/cpu_byteslice_batch_probe.hpp explains the dedup,
// the batched address pass and the forwarding chain it rests on).
//
// ONE CLAIM, MADE OVER AND OVER: a batch answers exactly what the SAME
// SEQUENCE of scalar calls answers.  Every fixture below builds two engines
// from one seed and one geometry, drives one of them scalar-wise and the
// other through `AccessBatch`, and compares every returned value and flag
// lane for lane -- then sweeps the whole key pool on both, drains both, and
// sweeps again. The frozen-cut fixture also checks that each immutable unit
// represents its own logical request prefix. The internal layout may differ
// from scalar execution, and callers whose buffers depend on each other are
// outside the API's batch-equivalence contract.
//
// THE SECURITY PROPERTY IS CHECKED TOO, and it is the reason the in-batch
// dedup exists: two equal keys hash to one bucket under one nonce, so a chunk
// holding a key twice must real-probe it once.  The probe audit is LIVE in
// every case here, and a second real probe of one key under one nonce family
// is counted and asserted absent.  Without that line the runs above would
// prove nothing about it -- the audit counts, it does not throw.
//
// WHAT EACH FIXTURE ADDS, so that a reader can tell coverage from repetition:
//
//   - TestEquivalence sweeps the axes that change the CASCADE: B, L, the top
//     digit, the insertion unit (which is the removable multi-bucket run),
//     the prefix flushes, the lane width, the caller's batch size, the result
//     layout, the key width and the execution shape.
//   - TestDuplicateChunk drives a chunk that is ALL ONE KEY under mixed
//     operations, which is the forwarding chain with nothing else in it.
//   - the "single lane" arm in main pins the degenerate case: at one lane a
//     batch is a loop of accesses and must be indistinguishable from one.
//   - the "parallel tiles" arms run the same comparison with several
//     participants, including against a hierarchy that has owner threads of
//     its own; the direct-slot and bucket-scan arms after them add
//     initialized engines and whole-bucket producers.
//   - TestBucketScanOracle checks the bucket-owned scan against an
//     independent newest-entry oracle; TestEveryParticipantRuns and
//     TestParticipantInitThrows check that the participants really run and
//     that a throwing init hook fails construction.
//   - TestFrozenUnitCuts checks that later lanes neither suppress tombstones
//     nor eagerly remove newest values from an earlier frozen unit.
//   - TestRefusals pins what the engine will not do rather than what it does.
//
// THE GEOMETRIES ARE SMALL ON PURPOSE.  What this file tests is the cascade
// and the forwarding, both of which are functions of the plan's SHAPE, and a
// small hierarchy reaches every shape -- adoption, a full carry, a top
// compaction -- in a few thousand accesses instead of a few million.

#define MICRORAM_BYTESLICE_PROBE_AUDIT 1

#include <algorithm>
#include <atomic>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <memory>
#include <random>
#include <stdexcept>
#include <string>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_engine.hpp"

namespace {

namespace bs = microram::byteslice;
namespace la = microram::byteslice::levelarena;

int failures = 0;

void Expect(bool value, const std::string& message) {
  if (!value) {
    std::fprintf(stderr, "test failed: %s\n", message.c_str());
    ++failures;
  }
}

template <class Fn>
bool Throws(Fn&& fn) {
  try {
    fn();
  } catch (const std::exception&) {
    return true;
  }
  return false;
}

constexpr uint64_t kMaxAccesses = uint64_t{1} << 32;

// Everything one arm of a comparison is built from.  A struct rather than
// fifteen positional arguments, because a fixture that swept `lanes` when it
// meant `batch` would still compile and still pass.
struct Arm {
  unsigned branching = 4;
  unsigned levels = 3;
  unsigned top_digit = 2;
  unsigned prefix_flushes = 2;
  size_t stash_buckets = 1;   // s; the insertion unit is 64 s entries
  unsigned dense_prefixes = 2;
  size_t key_bytes = 8;
  size_t value_bytes = 8;
  unsigned lanes = 16;
  unsigned participants = 1;
  unsigned owner_threads = 0;
  bool bucket_scan = false;
  bool alternate = false;
  la::BatchExecutionShape execution =
      la::BatchExecutionShape::kChunkedCascade;
  bs::BatchResultLayout layout = bs::BatchResultLayout::kSlicedPlaceAtLane;
  size_t batch = 40;      // requests per AccessBatch call
  size_t accesses = 3000;
  size_t pool = 40;       // distinct keys the workload draws from
  bool initialize = false; // distinct direct initialization before online work
  bool word_keys = false; // drive the BatchRequest64 form
  uint64_t seed = 0x11E7;

  std::string Describe() const {
    return "B=" + std::to_string(branching) + " L=" + std::to_string(levels) +
           " D=" + std::to_string(top_digit) +
           " r0=" + std::to_string(prefix_flushes) +
           " s=" + std::to_string(stash_buckets) +
           " key=" + std::to_string(key_bytes) +
           " value=" + std::to_string(value_bytes) +
           " lanes=" + std::to_string(lanes) +
           " batch=" + std::to_string(batch) +
           " participants=" + std::to_string(participants) +
           " owners=" + std::to_string(owner_threads) + " " +
           la::BatchExecutionShapeName(execution) +
           (bucket_scan ? " bucket-scan" : "") +
           (layout == bs::BatchResultLayout::kRows ? " rows" : " place") +
           (word_keys ? " word-keys" : "") +
           (initialize ? " initialized" : "");
  }
};

const char* LayoutName(bs::BatchResultLayout layout) {
  return layout == bs::BatchResultLayout::kRows ? "rows" : "place-at-lane";
}

// THE SERIAL ARM IS BUILT WITH THE SAME BATCH OPTIONS AS THE BATCHED ONE, and
// deliberately: the batch configuration must change nothing but how requests
// are issued, so an arm that differed in it would be comparing two engines
// rather than two ways of driving one.
la::LevelArenaEngine::Options OptionsOf(const Arm& arm) {
  la::LevelArenaEngine::Options options;
  options.geometry.branching = arm.branching;
  options.geometry.levels = arm.levels;
  options.geometry.top_digit = arm.top_digit;
  options.geometry.prefix_flushes = arm.prefix_flushes;
  options.geometry.stash_buckets = arm.stash_buckets;
  options.geometry.dense_prefixes = arm.dense_prefixes;
  options.key_bytes = arm.key_bytes;
  options.value_bytes = arm.value_bytes;
  options.max_accesses = kMaxAccesses;
  options.batch_bucket_scan = arm.bucket_scan;
  options.batch_profile = arm.bucket_scan;
  options.batch_lanes = arm.lanes;
  options.batch_execution = arm.execution;
  options.batch_participants = arm.participants;
  options.batch_result_layout = arm.layout;
  options.owner_threads = arm.owner_threads;
  // SHORT SPINS (50 us): the library's 1 ms default is a LATENCY
  // choice for an engine that has the machine to itself, and a correctness
  // fixture does not.  Thirty copies of this file in parallel -- the stress
  // run a threaded fixture should survive before it is believed -- put five
  // spinning threads per engine on a twelve-core host,
  // and at 1 ms each they saturate it so thoroughly that the quiescence
  // protocol's 1 ms idle slice stops being observable and `Drain` reports its
  // deadlock deadline.  Nothing here is timing-dependent on purpose; this is
  // what keeps it from becoming so under load.
  options.owner_spin_nanos = 50 * 1000;
  options.batch_spin_nanos = 50 * 1000;
  // Fixed, so that a failure is reproducible: every bucket an entry lands in
  // is a function of this.
  options.secret_seed = microram::crypto::SecretKeySeed::Fixed(arm.seed);
  return options;
}

// ---------------------------------------------------------------------------
// The workload
// ---------------------------------------------------------------------------

// Keys of 9..15 bytes are stored verbatim, so there the key's low bytes go
// in bytes 8.. and the rest in bytes 0..7: at 12 bytes every pool key shares
// one (zero) low stored word, and a comparison that dropped the high word
// would merge them all.
std::vector<uint8_t> KeyBytes(uint64_t key, size_t key_bytes) {
  std::vector<uint8_t> out(key_bytes, 0);
  if (key_bytes > 8 && key_bytes < 16) {
    const unsigned high_bits = static_cast<unsigned>(8 * (key_bytes - 8));
    for (size_t i = 0; i < key_bytes; ++i) {
      const uint64_t word = i < 8 ? key >> high_bits : key;
      out[i] = static_cast<uint8_t>(word >> (8 * (i % 8)));
    }
    return out;
  }
  for (size_t i = 0; i < 8 && i < key_bytes; ++i) {
    out[i] = static_cast<uint8_t>(key >> (8 * i));
  }
  uint64_t state = key * 0xD6E8FEB86659FD93ull + 7;
  for (size_t i = 8; i < key_bytes; ++i) {
    state = state * 6364136223846793005ull + 1442695040888963407ull;
    out[i] = static_cast<uint8_t>(state >> 33);
  }
  return out;
}

std::vector<uint8_t> ValueBytes(uint64_t key, size_t value_bytes,
                                unsigned version) {
  std::vector<uint8_t> out(value_bytes, 0);
  uint64_t state = key * 0x9E3779B97F4A7C15ull + version;
  for (size_t i = 0; i < value_bytes; ++i) {
    state = state * 6364136223846793005ull + 1442695040888963407ull;
    out[i] = static_cast<uint8_t>(state >> 33);
  }
  return out;
}

struct Request {
  bs::BatchOp op = bs::BatchOp::kRead;
  bool insert = false;
  uint64_t key = 0;
  std::vector<uint8_t> value_in;
};

// One request run through the SCALAR surface, reporting (found, previous)
// exactly as a lane does.  `kWrite` is `Exchange(..., insert=true)` and not
// `Write`, because a lane reports the presence and the previous value of a
// write too and `Write` returns neither -- the two insert the same entry.
bool RunScalar(la::LevelArenaEngine& engine, const Request& request,
               const uint8_t* key, std::vector<uint8_t>* value_out) {
  switch (request.op) {
    case bs::BatchOp::kRead:
      return engine.Read(key, value_out->data());
    case bs::BatchOp::kWrite:
      return engine.Exchange(key, request.value_in.data(), value_out->data(),
                             /*insert=*/true);
    case bs::BatchOp::kErase:
      return engine.Erase(key, value_out->data());
    case bs::BatchOp::kExchange:
      return engine.Exchange(key, request.value_in.data(), value_out->data(),
                             request.insert);
  }
  return false;
}

void ExpectSameContents(la::LevelArenaEngine& a, la::LevelArenaEngine& b,
                        const std::vector<uint64_t>& keys, const Arm& arm,
                        const std::string& where) {
  std::vector<uint8_t> va(arm.value_bytes), vb(arm.value_bytes);
  for (uint64_t key : keys) {
    const std::vector<uint8_t> bytes = KeyBytes(key, arm.key_bytes);
    const bool fa = a.Read(bytes.data(), va.data());
    const bool fb = b.Read(bytes.data(), vb.data());
    Expect(fa == fb, where + ": the two engines disagree about presence");
    Expect(va == vb, where + ": the two engines disagree about a value");
    if (failures != 0) return;
  }
}

// The comparison itself.  `make_request` decides the stream, so a fixture can
// hand it a random mix or a chunk of one key without a second copy of this.
template <class MakeRequest>
void CompareWithScalar(const Arm& arm, const std::vector<uint64_t>& pool,
                       size_t accesses, MakeRequest&& make_request,
                       const std::string& what) {
  // THE WORD-KEY FORM IS THE SAME KEY only up to eight bytes: past that the
  // byte form is rehashed to an AES block and a `uint64_t` cannot say what it
  // rehashed.  The two arms would then be comparing different keys and
  // agreeing about nothing, so the combination is refused here rather than
  // passing vacuously.
  if (arm.word_keys && arm.key_bytes > 8) {
    Expect(false, what + ": the word-key request form needs a key of at most "
                         "eight bytes");
    return;
  }
  la::LevelArenaEngine scalar(OptionsOf(arm));
  la::LevelArenaEngine batched(OptionsOf(arm));
  if (arm.initialize) {
    std::vector<std::vector<uint8_t>> keys, values;
    for (uint64_t key : pool) {
      keys.push_back(KeyBytes(key, arm.key_bytes));
      values.push_back(ValueBytes(key, arm.value_bytes, 0));
    }
    std::vector<bs::InitializationEntry> entries;
    for (size_t i = 0; i < pool.size(); ++i)
      entries.push_back({keys[i].data(), values[i].data()});
    scalar.Initialize(entries.begin(), entries.size());
    batched.Initialize(entries.begin(), entries.size());
    // The unprobed-write path must also keep the current unit unique.
    for (unsigned repeat = 0; repeat < 3; ++repeat) {
      scalar.WriteWithoutProbe(keys[0].data(), values[0].data());
      batched.WriteWithoutProbe(keys[0].data(), values[0].data());
    }
  }
  Expect(batched.batch_lanes() == arm.lanes, "the lane width is not reported");
  Expect(batched.batch_participants() == arm.participants,
         "the participant count is not reported");
  Expect(batched.MaxCombinedBatchLanes() ==
             (arm.execution == la::BatchExecutionShape::kParallelTiles
                  ? size_t{arm.lanes} * arm.participants
                  : size_t{arm.lanes}),
         "the combined width is not the lanes times the participants");

  size_t done = 0;
  unsigned version = 1;
  size_t round = 0;
  constexpr size_t sizes[] = {512, 1, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129};
  while (done < accesses) {
    if (arm.alternate)
      batched.SetBatchParticipants(1 + round % arm.participants);
    const size_t n = std::min(arm.alternate ? sizes[round % 14] : arm.batch,
                              accesses - done);
    std::vector<Request> requests(n);
    std::vector<std::vector<uint8_t>> keys(n), scalar_out(n), batch_out(n);
    std::vector<bs::BatchRequest> lanes(n);
    std::vector<bs::BatchRequest64> word_lanes(n);
    for (size_t j = 0; j < n; ++j) {
      requests[j] = make_request(done + j, version);
      keys[j] = KeyBytes(requests[j].key, arm.key_bytes);
      // Distinct fill bytes, so a value_out nobody wrote is not mistaken for
      // an agreement between two engines that both left it alone.
      scalar_out[j].assign(arm.value_bytes, 0xA5);
      batch_out[j].assign(arm.value_bytes, 0x5A);
      lanes[j].op = requests[j].op;
      lanes[j].insert = requests[j].insert;
      lanes[j].key = keys[j].data();
      lanes[j].value_in = requests[j].value_in.data();
      lanes[j].value_out = batch_out[j].data();
      word_lanes[j].op = requests[j].op;
      word_lanes[j].insert = requests[j].insert;
      word_lanes[j].key = requests[j].key;
      word_lanes[j].value_in = requests[j].value_in.data();
      word_lanes[j].value_out = batch_out[j].data();
    }
    std::vector<uint8_t> scalar_found(n, 0), batch_found(n, 0);
    for (size_t j = 0; j < n; ++j) {
      scalar_found[j] = static_cast<uint8_t>(
          RunScalar(scalar, requests[j], keys[j].data(), &scalar_out[j]));
    }
    if (arm.word_keys) {
      batched.AccessBatch(n, word_lanes.data(), batch_found.data());
    } else {
      batched.AccessBatch(n, lanes.data(), batch_found.data());
    }
    for (size_t j = 0; j < n; ++j) {
      Expect(scalar_found[j] == batch_found[j],
             what + ": a lane's found flag differs from the scalar access");
      Expect(scalar_out[j] == batch_out[j],
             what + ": a lane's previous value differs from the scalar "
                    "access");
      if (failures != 0) return;
    }
    // A batch of n is n accesses, which is what makes the two engines'
    // flush schedules -- and therefore their geometries -- comparable at all.
    Expect(scalar.AccessCount() == batched.AccessCount(),
           what + ": a batch of n requests is not n accesses");
    done += n;
    if (arm.alternate) {
      // Cross the scalar/batch boundary with a nonempty unit, including writes
      // and tombstones; then resume with a different active participant count.
      Request request = make_request(done, version);
      auto key = KeyBytes(request.key, arm.key_bytes);
      std::vector<uint8_t> a(arm.value_bytes), b(arm.value_bytes);
      Expect(RunScalar(scalar, request, key.data(), &a) ==
                 RunScalar(batched, request, key.data(), &b) && a == b,
             "scalar/bucket transition lost state");
    }
    ++round;
  }
  if (arm.bucket_scan) {
    const auto& profile = batched.batch_profile(0).stages;
    Expect(profile[static_cast<size_t>(la::BatchStage::kMetadata)].calls != 0,
           "enabled metadata profile recorded no calls");
    Expect(profile[static_cast<size_t>(la::BatchStage::kJoinedPhase)].calls != 0,
           "enabled joined-phase profile recorded no calls");
  }
  ExpectSameContents(scalar, batched, pool, arm, what + " (live)");
  if (failures != 0) return;
  scalar.Drain();
  batched.Drain();
  ExpectSameContents(scalar, batched, pool, arm, what + " (drained)");
  // The security property, not the values.
  Expect(scalar.ProbeAuditViolations() == 0,
         what + ": the scalar engine repeated a real probe (the fixture is "
                "broken, not the batch path)");
  Expect(batched.ProbeAuditViolations() == 0,
         what + ": the batch path real-probed one key twice under one nonce "
                "family");
  Expect(batched.RealProbes() != 0,
         what + ": no real probe was recorded at all, so the audit above is "
                "vacuous");
}

std::vector<uint64_t> KeyPool(size_t n) {
  std::vector<uint64_t> pool(n);
  for (size_t i = 0; i < n; ++i) pool[i] = 1000 + i * 7919;
  return pool;
}

// ---------------------------------------------------------------------------
// The fixtures
// ---------------------------------------------------------------------------

void TestEquivalence(const Arm& arm) {
  std::printf("  equivalence: %s\n", arm.Describe().c_str());
  const std::vector<uint64_t> pool = KeyPool(arm.pool);
  std::mt19937_64 rng(arm.seed ^ 0x5EEDull);
  CompareWithScalar(
      arm, pool, arm.accesses,
      [&](size_t, unsigned& version) {
        Request request;
        const unsigned pick = static_cast<unsigned>(rng() % 10);
        request.op = pick < 4   ? bs::BatchOp::kRead
                     : pick < 7 ? bs::BatchOp::kWrite
                     : pick < 8 ? bs::BatchOp::kErase
                                : bs::BatchOp::kExchange;
        request.insert = (rng() & 1) != 0;
        // A tenth of the keys are absent forever, so misses -- and the
        // tombstones they insert -- are covered rather than assumed.
        request.key =
            (rng() % 10 == 0) ? 5 + (rng() % 8) : pool[rng() % arm.pool];
        request.value_in = ValueBytes(request.key, arm.value_bytes, version++);
        return request;
      },
      "equivalence");
}

// A CHUNK THAT IS ALL ONE KEY: the forwarding chain with nothing else in it.
// Every lane but the first is a duplicate, so every lane but the first probes
// dummies at every hashed table and takes its answer from the state the
// previous lane left -- and the entry all but the last of them insert is
// superseded and must not become live.
void TestDuplicateChunk(const Arm& base) {
  Arm arm = base;
  arm.pool = 4;
  arm.accesses = 1200;
  arm.batch = 48;
  std::printf("  one key per chunk: %s\n", arm.Describe().c_str());
  const std::vector<uint64_t> pool = KeyPool(arm.pool);
  std::mt19937_64 rng(arm.seed ^ 0xD00Dull);
  CompareWithScalar(
      arm, pool, arm.accesses,
      [&](size_t index, unsigned& version) {
        Request request;
        // One key for a whole chunk, and a different one for the next.
        request.key = pool[(index / arm.batch) % arm.pool];
        const unsigned pick = static_cast<unsigned>(rng() % 8);
        request.op = pick < 3   ? bs::BatchOp::kRead
                     : pick < 5 ? bs::BatchOp::kWrite
                     : pick < 6 ? bs::BatchOp::kErase
                                : bs::BatchOp::kExchange;
        request.insert = (rng() & 1) != 0;
        request.value_in = ValueBytes(request.key, arm.value_bytes, version++);
        return request;
      },
      "one key per chunk");
}

// A frozen unit must retain the state at its own lane prefix. Final API
// answers alone cannot detect batch-wide suppression/removal across a cut.
// The s=1 arm uses the certified geometry L2_r2_D8_2 (B = 8, two levels,
// level fanout 2, top digit 8, two prefix flushes, as configured below;
// capacity 2048); s=2
// also drives the bucket-scan path with more than one current-unit bucket.
void ExpectFrozenEntry(const la::LevelArenaEngine& engine, uint64_t key,
                       bool erased, const std::vector<uint8_t>& value,
                       const std::string& what) {
  bs::ProbePlan plan;
  plan.prefix_slots = engine.dense().plan_prefix_slots();
  plan.tables.resize(plan.prefix_slots);
  plan.heads_consumed = engine.dense().consumed();
  engine.dense().FillDensePrefix(&plan);
  size_t matches = 0;
  const bs::Layout& layout = engine.layout();
  for (size_t t = plan.first_live; t < plan.prefix_slots; ++t) {
    const auto& table = plan.tables[t];
    if (table.removable) continue;
    for (size_t b = 0; b < table.num_buckets; ++b) {
      const uint8_t* bucket = table.data + b * layout.BucketBytes();
      for (size_t slot = 0; slot < bs::kBucketCapacity; ++slot) {
        if (((table.masks[b] >> slot) & 1u) == 0 ||
            bs::ReadSlotKey(bucket, slot, layout.key_bytes).w0 != key) continue;
        ++matches;
        const uint8_t meta = bucket[(layout.key_bytes + engine.ValueBytes()) *
                                   bs::kBucketCapacity + slot];
        Expect(((meta & bs::kMetaErased) != 0) == erased,
               what + ": frozen entry has the wrong tombstone flag");
        if (!erased) {
          for (size_t v = 0; v < value.size(); ++v)
            Expect(bucket[(layout.key_bytes + v) * bs::kBucketCapacity + slot] == value[v],
                   what + ": frozen entry has the wrong value");
        }
      }
    }
  }
  Expect(matches == 1, what + ": expected exactly one frozen record");
}

void TestFrozenUnitCuts() {
  for (bool eager_removal : {false, true}) {
    for (unsigned mode = 0; mode < 4; ++mode) {
      for (auto result_layout : {bs::BatchResultLayout::kRows,
                                bs::BatchResultLayout::kSlicedPlaceAtLane}) {
        Arm arm;
        arm.branching = 8;
        arm.levels = 2;
        arm.top_digit = 8;
        arm.prefix_flushes = 2;
        arm.layout = result_layout;
        arm.lanes = mode == 1 ? 1 : 64;
        arm.participants = mode == 0 ? 1 : 3;
        arm.stash_buckets = mode == 3 ? 2 : 1;
        arm.bucket_scan = mode == 3;
        if (mode != 0) arm.execution = la::BatchExecutionShape::kParallelTiles;
        auto options = OptionsOf(arm);
        options.geometry.level_fanouts = {2};
        la::LevelArenaEngine engine(options);
        const auto key_a = KeyBytes(1, arm.key_bytes);
        const auto old_a = ValueBytes(1, arm.value_bytes, 1);
        const auto new_a = ValueBytes(1, arm.value_bytes, 2);
        const auto new_b = ValueBytes(2, arm.value_bytes, 1);
        const bs::InitializationEntry initial{key_a.data(), old_a.data()};
        engine.Initialize(&initial, 1);
        if (eager_removal) engine.Write(uint64_t{1}, new_a.data());
        std::vector<uint8_t> scratch(arm.value_bytes);
        while (engine.StashSize() < engine.dense().unit_entries() - 2)
          engine.Read(uint64_t{999}, scratch.data());
        const uint64_t before = engine.AccessCount();
        std::vector<std::vector<uint8_t>> out(3, std::vector<uint8_t>(arm.value_bytes, 0xA5));
        std::vector<bs::BatchRequest64> lanes(3);
        lanes[0].op = eager_removal ? bs::BatchOp::kRead : bs::BatchOp::kErase;
        lanes[0].key = eager_removal ? 2 : 1;
        lanes[1].op = eager_removal ? bs::BatchOp::kRead : bs::BatchOp::kWrite;
        lanes[1].key = eager_removal ? 3 : 2;
        lanes[1].value_in = new_b.data();
        lanes[2].op = bs::BatchOp::kRead;
        lanes[2].key = 1;
        for (size_t i = 0; i < lanes.size(); ++i) lanes[i].value_out = out[i].data();
        uint8_t found[3] = {0xA5, 0xA5, 0xA5};
        engine.AccessBatch(lanes.size(), lanes.data(), found);
        const std::vector<uint8_t> zero(arm.value_bytes, 0);
        Expect(engine.AccessCount() == before + 3 && engine.FlushCount() == 1 &&
                   engine.StashSize() == 1,
               "cut-safe batch changed the public position schedule");
        if (eager_removal) {
          Expect(found[0] == 0 && found[1] == 0 && found[2] == 1 &&
                     out[0] == zero && out[1] == zero && out[2] == new_a,
                 "eager-removal cut changed external replies");
          ExpectFrozenEntry(engine, 1, false, new_a, "later probe of A");
        } else {
          Expect(found[0] == 1 && found[1] == 0 && found[2] == 0 &&
                     out[0] == old_a && out[1] == zero && out[2] == zero,
                 "erase A/write B/miss A cut changed external replies");
          ExpectFrozenEntry(engine, 1, true, zero, "erase A before the cut");
          ExpectFrozenEntry(engine, 2, false, new_b, "write B before the cut");
          Expect(!engine.Read(uint64_t{1}, scratch.data()) && scratch == zero,
                 "A was resurrected after the cut");
          Expect(engine.Read(uint64_t{2}, scratch.data()) && scratch == new_b,
                 "B was lost after the cut");
        }
        Expect(engine.ProbeAuditViolations() == 0,
               "cut-safe chunks repeated a real probe under one family");
      }
    }
  }
  std::puts("  frozen cuts: tombstones and newest values survive later lanes");
}

// ---------------------------------------------------------------------------

// Independent newest-entry/last-bucket oracle, with worker boundaries inside
// runs and between runs. A synthetic all-dense plan also tests an empty suffix.
void TestBucketScanOracle() {
  for (size_t key_bytes : {3u, 4u, 8u, 16u}) {
    bs::Layout layout;
    layout.key_bytes = key_bytes;
    layout.value_bytes = 18;  // 17 user bytes + metadata
    bs::ProbePlan plan;
    plan.first_live = 0;
    plan.tables.resize(3);
    std::array<bs::Aligned64Ptr, 3> data;
    std::array<std::vector<uint64_t>, 3> masks;
    const size_t counts[] = {19, 23, 31};
    for (size_t t = 0; t < 3; ++t) {
      data[t] = bs::AllocateAligned64(counts[t] * layout.BucketBytes());
      std::memset(data[t].get(), 0, counts[t] * layout.BucketBytes());
      masks[t].assign(counts[t], 0);
      auto& table = plan.tables[t];
      table.kind = bs::TableKind::kDense;
      table.removable = t == 0;
      table.num_buckets = counts[t];
      table.data = data[t].get();
      table.masks = masks[t].data();
      for (size_t b = 0; b < counts[t]; ++b) {
        uint8_t* bucket = table.data + b * layout.BucketBytes();
        const unsigned slot = unsigned(b % 64);
        bs::WriteSlotKey(bucket, slot, key_bytes,
                         bs::KeyWords{t == 0 ? b : 10 + b % 17, 0});
        masks[t][b] = uint64_t{1} << slot;
        for (size_t v = 0; v < layout.value_bytes; ++v)
          bucket[(key_bytes + v) * 64 + slot] = uint8_t(1 + b + 37*t + v);
        bucket[(key_bytes + 17) * 64 + slot] = b % 3 == 0 ? bs::kMetaErased : 0;
      }
    }
    const auto original_masks = masks;
    la::LevelArenaBucketBatch scratch;
    scratch.Resize(3, 17);
    std::array<std::unique_ptr<la::LevelArenaBatchTile>, 3> owners;
    for (auto& owner : owners) {
      owner = std::make_unique<la::LevelArenaBatchTile>();
      owner->Resize(3, 1, layout, 17, 19);
      Expect(reinterpret_cast<uintptr_t>(owner->clear_masks.begin()) % 64 == 0,
             "private removals are not cache-line aligned");
    }
    for (size_t n : {129u, 64u, 1u, 65u, 32u}) {
      for (size_t j = 0; j < n; ++j) scratch.keys[j] = bs::KeyWords{j % 83, 0};
      size_t buckets = 0;
      const size_t end = la::InitialDenseEnd(plan, &buckets);
      for (unsigned w = 0; w < 3; ++w)
        la::ScanLevelArenaBucketRange(plan, end, buckets, layout, n, w, 3,
                                      scratch, *owners[w]);
      const bs::BatchPartition partition{n, std::min(size_t{3}, n)};
      for (unsigned t = 0; t < partition.owners; ++t) {
        auto& tile = *owners[t];
        tile.lanes = partition.Count(t);
        tile.dedup.duplicates = 0;
        for (size_t j = 0; j < tile.lanes; ++j) {
          const size_t ordinal = partition.Offset(t) + j;
          tile.key[j] = scratch.keys[ordinal];
          tile.dedup.duplicates |= uint64_t{ordinal >= 83} << j;
        }
        la::MergeLevelArenaBucketResults(scratch, 3, partition.Offset(t), layout, tile);
        la::ProbeLevelArenaBatchLanes(plan, layout, bs::BatchResultLayout::kRows,
                                      tile, nullptr, end);
        for (size_t j = 0; j < tile.lanes; ++j) {
          if (partition.Offset(t) + j >= 83) continue;
          std::vector<uint8_t> expected(18, 0);
          bool found = false;
          for (size_t i = 0; i < 3 && !found; ++i) {
            const auto& table = plan.tables[i];
            for (size_t b = 0; b < table.num_buckets; ++b) {
              const uint8_t* bucket = table.data + b * layout.BucketBytes();
              const uint64_t match = bs::MatchMaskByteSlicedTree(
                  bucket, table.masks[b], layout, tile.key[j]);
              if (match) {
                found = true;
                for (size_t v = 0; v < 18; ++v)
                  expected[v] = bucket[(key_bytes + v)*64 + _tzcnt_u64(match)];
              }
            }
          }
          Expect(tile.found[j] == uint64_t{found}, "bucket reduction found differs");
          Expect(std::memcmp(tile.Row(j), expected.data(), 18) == 0,
                 "bucket reduction broke entry/bucket freshness or tombstones");
        }
      }
      for (size_t b = 0; b < 19; ++b) {
        uint64_t clear = 0;
        for (auto& owner : owners) clear |= owner->clear_masks[b];
        Expect(clear == (b < n ? masks[0][b] : 0), "bucket removal reduction differs");
      }
      Expect(masks == original_masks, "bucket producers modified canonical masks");
    }
  }
  std::puts("  bucket scan: freshness, tombstones, empty suffix and private removals");
}

void TestRefusals() {
  Arm arm;
  Expect(Throws([&] {
           auto options = OptionsOf(arm);
           options.batch_bucket_scan = true;
           la::LevelArenaEngine engine(options);
         }), "bucket scan accepted without parallel tiles");
  Expect(Throws([&] {
           la::LevelArenaEngine::Options options = OptionsOf(arm);
           options.batch_lanes = 65;
           la::LevelArenaEngine engine(options);
         }),
         "a lane width above 64 was accepted");
  Expect(Throws([&] {
           la::LevelArenaEngine::Options options = OptionsOf(arm);
           options.batch_lanes = 0;
           la::LevelArenaEngine engine(options);
         }),
         "a zero lane width was accepted");
  // The chunked shape is the single-thread batch execution, so it refuses
  // participants rather than allocating idle ones.
  Expect(Throws([&] {
           la::LevelArenaEngine::Options options = OptionsOf(arm);
           options.batch_participants = 2;
           la::LevelArenaEngine engine(options);
         }),
         "the chunked shape accepted a second participant");
  Expect(Throws([&] {
           la::LevelArenaEngine::Options options = OptionsOf(arm);
           options.batch_participants = 9;
           options.batch_execution = la::BatchExecutionShape::kParallelTiles;
           la::LevelArenaEngine engine(options);
         }),
         "a ninth participant was accepted");

  // And the refusals with a control beside them, because a Throws with no
  // control tests only that something went wrong.
  la::LevelArenaEngine::Options options = OptionsOf(arm);
  options.batch_execution = la::BatchExecutionShape::kParallelTiles;
  options.batch_participants = 3;
  la::LevelArenaEngine engine(options);
  Expect(engine.batch_participant_capacity() == 3,
         "the participant capacity is not what the engine was built with");
  engine.SetBatchParticipants(2);
  Expect(engine.batch_participants() == 2,
         "the participant count did not move");
  Expect(Throws([&] { engine.SetBatchParticipants(4); }),
         "a participant count above the built capacity was accepted");
  Expect(Throws([&] { engine.SetBatchParticipants(0); }),
         "a zero participant count was accepted");
  engine.SetBatchLanes(8);
  Expect(engine.batch_lanes() == 8, "the lane width did not move");
  Expect(Throws([&] { engine.SetBatchLanes(0); }), "zero lanes was accepted");
  Expect(Throws([&] { engine.SetBatchLanes(65); }), "65 lanes was accepted");
  std::vector<bs::BatchRequest> none;
  Expect(Throws([&] { engine.AccessBatch(4, none.data(), nullptr); }),
         "a null request array was accepted");
  // Zero requests is a no-op and not a refusal: a caller that batches a
  // client's arrivals gets an empty one whenever nobody arrived.
  engine.AccessBatch(0, none.data(), nullptr);
  Expect(engine.AccessCount() == 0, "an empty batch consumed an access");
  std::printf("  refusals: lane width, participants, result layout, null "
              "requests\n");
}

// A THROWING PARTICIPANT INIT HOOK IS A CONSTRUCTION FAILURE, not a surprise
// for the first batch -- the same contract the owner threads' hook has.
void TestParticipantInitThrows() {
  Arm arm;
  arm.execution = la::BatchExecutionShape::kParallelTiles;
  arm.participants = 3;
  la::LevelArenaEngine::Options options = OptionsOf(arm);
  options.batch_thread_init = [](unsigned t) {
    if (t == 2) throw std::runtime_error("no");
  };
  bool threw = false;
  try {
    la::LevelArenaEngine engine(options);
  } catch (const std::runtime_error& error) {
    threw = std::string(error.what()) == "no";
  }
  Expect(threw,
         "a throwing batch-participant init hook was not the constructor's "
         "own exception");
  std::printf("  a throwing participant init hook fails construction\n");
}

// EVERY PARTICIPANT REALLY RUNS.  A comparison that passed with the helpers
// asleep would pass for the wrong reason, so the hook counts them.
void TestEveryParticipantRuns() {
  Arm arm;
  arm.execution = la::BatchExecutionShape::kParallelTiles;
  arm.participants = 4;
  arm.lanes = 8;
  // The hook runs on each PARTICIPANT's own thread, concurrently, so what it
  // writes has to be shared state -- a bitmask of the indices seen, one
  // atomic OR each.  A plain container here would be a data race (one
  // ThreadSanitizer reports).
  std::atomic<uint64_t> seen{0};
  la::LevelArenaEngine::Options options = OptionsOf(arm);
  options.batch_thread_init = [&seen](unsigned t) {
    seen.fetch_or(uint64_t{1} << t, std::memory_order_relaxed);
  };
  la::LevelArenaEngine engine(options);
  Expect(seen.load() == 0xEu,
         "the participants other than the caller did not all start");
  // A job wide enough to need every tile, and the waits prove the caller
  // really joined three of them.
  const size_t n = size_t{arm.lanes} * arm.participants;
  std::vector<std::vector<uint8_t>> keys(n), values(n);
  std::vector<bs::BatchRequest> lanes(n);
  for (size_t j = 0; j < n; ++j) {
    keys[j] = KeyBytes(j, arm.key_bytes);
    values[j] = ValueBytes(j, arm.value_bytes, 1);
    lanes[j] = bs::BatchRequest{bs::BatchOp::kReadThenWrite, false, keys[j].data(),
                                values[j].data(), nullptr};
  }
  engine.AccessBatch(n, lanes.data(), nullptr);
  uint64_t helper_waits = 0;
  for (unsigned t = 1; t < arm.participants; ++t) {
    helper_waits += engine.batch_waits(t).waits();
  }
  Expect(helper_waits != 0,
         "no participant ever waited for a phase, so they cannot have been "
         "the threads that ran it");
  std::vector<uint8_t> got(arm.value_bytes);
  for (size_t j = 0; j < n; ++j) {
    Expect(engine.Read(keys[j].data(), got.data()) && got == values[j],
           "a lane of a full-width parallel job was lost");
    if (failures != 0) return;
  }
  std::printf("  all %u participants start, wait and run a full-width job\n",
              arm.participants);
}

}  // namespace

int main() {
  std::printf("level arena: the batch path\n");

  // ---- the cascade's axes, chunked ----------------------------------------
  for (bs::BatchResultLayout layout :
       {bs::BatchResultLayout::kSlicedPlaceAtLane,
        bs::BatchResultLayout::kRows}) {
    std::printf(" result layout: %s\n", LayoutName(layout));
    Arm arm;
    arm.layout = layout;
    TestEquivalence(arm);
    TestDuplicateChunk(arm);
    if (failures != 0) return 1;

    // A WIDER INSERTION UNIT is the batch path's main tuning axis: the removable
    // online-stash table becomes a multi-bucket RUN, every bucket of which a
    // lane scans and in which the entry's answer is the LAST match.
    Arm wide_unit = arm;
    wide_unit.stash_buckets = 8;
    wide_unit.prefix_flushes = 4;
    wide_unit.accesses = 4000;
    TestEquivalence(wide_unit);

    // And a unit of 1024 entries, which is 16 buckets of removable run, the
    // largest unit the tuning range covers: the clear-mask vector is
    // sized from `s`, and a fixture that only ever saw one bucket would be
    // testing the run scan and not the removal that goes with it.
    Arm widest_unit = arm;
    widest_unit.stash_buckets = 16;
    widest_unit.prefix_flushes = 2;
    widest_unit.accesses = 4000;
    TestEquivalence(widest_unit);

    // B = 2, where every table is a power of two and the windows partition
    // the timeline; and B = 8 with a packed radix digit, where they do not.
    Arm binary = arm;
    binary.branching = 2;
    binary.levels = 4;
    binary.top_digit = 1;
    TestEquivalence(binary);

    Arm wide_fanout = arm;
    wide_fanout.branching = 8;
    wide_fanout.levels = 2;
    wide_fanout.top_digit = 8;
    TestEquivalence(wide_fanout);
    if (failures != 0) return 1;
  }

  {
    // ONE LANE IS A LOOP OF ACCESSES: the scalar control, and the arm in
    // which the dedup, the waves and the forwarding chain all degenerate.
    Arm single;
    single.lanes = 1;
    single.batch = 7;
    single.accesses = 1500;
    std::printf(" single lane\n");
    TestEquivalence(single);

    // The widest chunk, so the lane mask is a full word and the eight-lane
    // extract groups are all complete.
    Arm widest;
    widest.lanes = 64;
    widest.batch = 200;
    std::printf(" widest chunk\n");
    TestEquivalence(widest);

    // A caller batch that is not a multiple of the lane width, so the last
    // chunk is a tail; and the word-key request form.
    Arm tail;
    tail.lanes = 16;
    tail.batch = 37;
    tail.word_keys = true;
    std::printf(" ragged tail, word keys\n");
    TestEquivalence(tail);

    // Short stored keys exercise dword batch conflicts across group boundaries
    // and the four-byte match tree, with the real-probe uniqueness audit live.
    for (size_t bytes : {2u, 3u, 4u}) {
      Arm short_keys = widest;
      short_keys.key_bytes = bytes;
      std::printf(" short keys: %zu bytes\n", bytes);
      TestEquivalence(short_keys);
      TestDuplicateChunk(short_keys);
    }

    // Wide user keys normalize to 16 stored bytes, 9..15-byte ones are stored
    // verbatim; both words compared exactly.
    for (size_t bytes : {12u, 24u}) {
      Arm wide_keys;
      wide_keys.key_bytes = bytes;
      wide_keys.value_bytes = 20;
      std::printf(" wide keys and values: %zu bytes\n", bytes);
      TestEquivalence(wide_keys);
      TestDuplicateChunk(wide_keys);
    }
    if (failures != 0) return 1;
  }

  // ---- parallel tiles ------------------------------------------------------
  {
    std::printf(" parallel tiles\n");
    Arm parallel;
    parallel.execution = la::BatchExecutionShape::kParallelTiles;
    parallel.participants = 3;
    parallel.lanes = 8;
    parallel.batch = 24;
    TestEquivalence(parallel);
    TestDuplicateChunk(parallel);

    // One participant in the parallel shape: the same code path as three,
    // with the cross-tile dedup degenerated to one tile.  It is what says a
    // disagreement between the shapes is about the TILES and not about the
    // parallel forwarding kernels.
    Arm alone = parallel;
    alone.participants = 1;
    TestEquivalence(alone);

    // The rows layout through the parallel publish, which is a copy rather
    // than the accumulate-in-place the sliced layout gets.
    Arm rows = parallel;
    rows.layout = bs::BatchResultLayout::kRows;
    TestEquivalence(rows);

    // AND WITH OWNER THREADS: the participants probe while the owners
    // rebuild, which is the only configuration in which a published table
    // can change under a batch that is already in flight.
    Arm threaded = parallel;
    threaded.owner_threads = 2;
    threaded.accesses = 4000;
    TestEquivalence(threaded);
    if (failures != 0) return 1;
  }

  // Direct-slot recovery with cross-tile duplicate chains, ragged tails,
  // multi-bucket stashes and concurrent rebuild. The audit checks every live
  // dense bucket for exact within-bucket uniqueness throughout these runs.
  for (size_t bytes : {4u, 8u, 12u, 24u}) {
    Arm initialized;
    initialized.key_bytes = bytes;
    initialized.initialize = true;
    initialized.stash_buckets = 16;
    initialized.lanes = 64;
    initialized.batch = 129;
    initialized.accesses = 6000;
    TestEquivalence(initialized);
    for (auto layout : {bs::BatchResultLayout::kRows,
                        bs::BatchResultLayout::kSlicedPlaceAtLane}) {
      Arm direct;
      direct.key_bytes = bytes;
      direct.layout = layout;
      direct.lanes = 64;
      direct.batch = 129;
      direct.participants = 2;
      direct.owner_threads = 2;
      direct.execution = la::BatchExecutionShape::kParallelTiles;
      direct.stash_buckets = 16;
      direct.pool = 97;
      direct.accesses = 10000;
      TestEquivalence(direct);
      TestDuplicateChunk(direct);
      Arm half = direct;
      half.lanes = 32;
      half.batch = 65;
      TestEquivalence(half);
      if (failures != 0) return 1;
    }
  }

  // Whole-bucket producers, including owners straddling global query groups,
  // P != W, short/full reuse, both result layouts and scalar transitions.
  for (size_t key_bytes : {3u, 4u, 8u, 12u, 24u}) {
    for (auto layout : {bs::BatchResultLayout::kRows,
                        bs::BatchResultLayout::kSlicedPlaceAtLane}) {
      Arm buckets;
      buckets.execution = la::BatchExecutionShape::kParallelTiles;
      buckets.bucket_scan = true;
      buckets.participants = 3;
      buckets.lanes = 64;
      buckets.batch = 129;
      buckets.stash_buckets = key_bytes == 3 ? 2 : 16;
      buckets.key_bytes = key_bytes;
      buckets.value_bytes = key_bytes == 3 ? 65 : 16;
      buckets.layout = layout;
      buckets.pool = 257;
      buckets.accesses = 9000;
      buckets.owner_threads = 2;
      TestEquivalence(buckets);
      TestDuplicateChunk(buckets);
      buckets.alternate = true;
      buckets.accesses = 4000;
      TestEquivalence(buckets);
      if (failures != 0) return 1;
    }
  }
  {
    Arm buckets;
    buckets.execution = la::BatchExecutionShape::kParallelTiles;
    buckets.bucket_scan = true;
    buckets.participants = 8;
    buckets.lanes = 64;
    buckets.batch = 512;
    buckets.stash_buckets = 1;
    buckets.accesses = 1500;
    TestEquivalence(buckets);
  }

  TestFrozenUnitCuts();
  TestBucketScanOracle();
  TestEveryParticipantRuns();
  TestParticipantInitThrows();
  TestRefusals();

  if (failures != 0) {
    std::fprintf(stderr, "%d level-arena batch checks failed\n", failures);
    return 1;
  }
  std::printf("level arena 11.7 batch: OK\n");
  return 0;
}
