// The engine's LIFETIME limits.  Its capacity and obliviousness guarantees
// hold only up to a public request horizon (`max_accesses`), and each probe of
// a dummy bucket consumes a fresh dummy counter (an AES input that must never
// repeat, or two dummy probes would land on the same bucket and become
// distinguishable from fresh ones); likewise the key-normalization allowance.
// When any of these would be exceeded, the engine must refuse (throw
// std::overflow_error) BEFORE the new request removes a record or writes a
// reply, so a refused request has no effect.  Earlier batch chunks and pending
// payloads belong to accepted requests and remain committed.  Also checked:
// that the lifetime coordinates (family ordinals, counters) of every geometry
// fit their fields for the requested horizon, and that draining at the
// horizon still completes.

#define MICRORAM_BYTESLICE_PROBE_AUDIT 1
#define MICRORAM_BYTESLICE_LEVEL_ARENA_PAUSE 1

#include <algorithm>
#include <array>
#include <atomic>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <limits>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_engine.hpp"

namespace {
namespace bs = microram::byteslice;
namespace la = microram::byteslice::levelarena;

int failures = 0;

void Expect(bool condition, const std::string& message) {
  if (!condition) {
    std::fprintf(stderr, "test failed: %s\n", message.c_str());
    ++failures;
  }
}

template <class Fn>
bool Refuses(Fn&& fn) {
  try {
    fn();
  } catch (const std::overflow_error&) {
    return true;
  }
  return false;
}

la::LevelArenaEngine::Options Options(uint64_t horizon) {
  la::LevelArenaEngine::Options options;
  options.geometry.branching = 2;
  options.geometry.levels = 2;
  options.geometry.top_digit = 2;
  options.geometry.prefix_flushes = 2;
  options.geometry.stash_buckets = 1;
  options.geometry.dense_prefixes = 2;
  options.key_bytes = 8;
  options.value_bytes = 8;
  options.max_accesses = horizon;
  options.flush_policy = la::LevelArenaEngine::FlushPolicy::kSettle;
  options.secret_seed = microram::crypto::SecretKeySeed::Fixed(0x11F371);
  options.batch_spin_nanos = 0;
  return options;
}

bool FitsLifetime(const la::LevelArenaGeometry& geometry, uint64_t horizon) {
  try {
    la::RequireLifetimeFits(geometry, horizon);
    return true;
  } catch (const std::exception&) {
    return false;
  }
}

void TestLifetimeCoordinates() {
  auto params = Options(1).geometry;
  params.tier_buckets = 1;
  const la::LevelArenaGeometry geometry(params);
  const auto seed = la::DirectInitializationSeed(geometry);
  const uint64_t last =
      la::kMaxFamilyOrdinal * geometry.PrefixPositions() - 1 -
      seed.access_offset;
  Expect(FitsLifetime(geometry, 0) && FitsLifetime(geometry, 1) &&
             FitsLifetime(geometry, uint64_t{1} << 32),
         "ordinary horizons fit both empty and initialized executions");
  Expect(FitsLifetime(geometry, last),
         "the last horizon with a representable speculative family fits");
  Expect(Refuses([&] { la::RequireLifetimeFits(geometry, last + 1); }),
         "the next horizon refuses before its speculative family wraps");
  Expect(Refuses([&] {
    la::RequireLifetimeFits(geometry,
                           la::kMaxFamilyOrdinal * geometry.PrefixPositions() - 1);
  }), "the horizon must include the synthetic initialization offset");
  Expect(Refuses([&] {
    la::RequireLifetimeFits(geometry, std::numeric_limits<uint64_t>::max());
  }), "adding initialization to an excessive horizon refuses without wrapping");

  // Check the actual ID encoders at the last accepted physical counters.
  // The high bit distinguishes dense tables; the low byte distinguishes the
  // complete prefix, frozen partial and currently writable unit.
  const uint64_t positions = seed.access_offset + last;
  const uint64_t prefix = positions / geometry.PrefixPositions();
  const uint64_t flush = positions / geometry.OnlineStashEntries();
  const uint64_t prefix_id = la::DensePrefixRing::PrefixTableId(prefix);
  const uint64_t partial_id = la::DensePrefixRing::PartialTableId(prefix, 1);
  const uint64_t unit_id = la::DensePrefixRing::UnitTableId(flush);
  Expect(((prefix_id & ~la::kDenseTableIdBit) >> 8) == prefix &&
             ((partial_id & ~la::kDenseTableIdBit) >> 8) == prefix &&
             ((unit_id & ~la::kDenseTableIdBit) >> 8) == flush &&
             prefix_id != partial_id && prefix_id != unit_id &&
             partial_id != unit_id,
         "last accepted dense identities retain their coordinates and domains");

  // Geometry construction computes counts, without allocating its tables.
  // Here every family ordinal fits, but even the first speculative top job's
  // complete future window would end at 2^64.
  params.levels = 45;
  params.top_digit = 1;
  params.stash_buckets = size_t{1} << 12;
  const la::LevelArenaGeometry tall(params);
  const auto tall_seed = la::DirectInitializationSeed(tall);
  Expect(tall_seed.access_offset == (uint64_t{1} << 63) &&
             tall_seed.prefixes + 1 <= la::kMaxFamilyOrdinal,
         "the tall fixture isolates a window overflow from ordinal exhaustion");
  Expect(Refuses([&] { la::RequireLifetimeFits(tall, 1); }),
         "a fitting position and family ordinal do not justify a wrapped future window");
}

void TestLifetimeGeometrySweep() {
  for (unsigned branching : {2u, 4u, 8u}) {
    for (unsigned levels : {2u, 4u, 8u}) {
      for (unsigned digit : {1u, branching}) {
        for (size_t stash : {size_t{1}, size_t{2}, size_t{4}}) {
          auto params = Options(1).geometry;
          params.branching = branching;
          params.levels = levels;
          params.top_digit = digit;
          params.prefix_flushes = branching;
          params.stash_buckets = stash;
          params.tier_buckets = 1;
          for (bool heterogeneous : {false, true}) {
            if (heterogeneous) {
              params.level_fanouts.assign(levels - 1, branching);
              params.level_fanouts[0] = 2;
            }
            const la::LevelArenaGeometry geometry(params);
            Expect(FitsLifetime(geometry, uint64_t{1} << 32),
                   "default horizon fits uniform and heterogeneous native ladders");
          }
        }
      }
    }
  }
}

void TestLifetimeConstruction() {
  for (bool synchronous : {false, true}) {
    auto options = Options(1);
    options.synchronous = synchronous;
    auto params = options.geometry;
    params.tier_buckets = 1;
    const la::LevelArenaGeometry geometry(params);
    options.max_accesses = la::kMaxFamilyOrdinal * geometry.PrefixPositions() -
                           la::DirectInitializationSeed(geometry).access_offset;
    Expect(Refuses([&] { la::LevelArenaEngine engine(options); }),
           "engine construction refuses an unrepresentable lifetime in both execution modes");
    options.max_accesses = std::numeric_limits<uint64_t>::max();
    Expect(Refuses([&] { la::LevelArenaEngine engine(options); }),
           "engine construction refuses position overflow before starting work");
    options.max_accesses = 0;
    bool invalid = false;
    try {
      la::LevelArenaEngine engine(options);
    } catch (const std::invalid_argument&) {
      invalid = true;
    }
    Expect(invalid, "a zero lifetime remains an invalid engine configuration");
  }
}

bs::ProbePlan DensePlan(const la::LevelArenaEngine& engine) {
  bs::ProbePlan plan;
  plan.prefix_slots = engine.dense().plan_prefix_slots();
  plan.tables.resize(plan.prefix_slots);
  plan.heads_consumed = engine.dense().consumed();
  engine.dense().FillDensePrefix(&plan);
  return plan;
}

// Snapshot the live dense source, including dummy bytes and physical counters.
// No request is spent reading the state after its horizon is exhausted.
std::vector<uint8_t> DenseSnapshot(const la::LevelArenaEngine& engine) {
  std::vector<uint8_t> out;
  const auto append_word = [&](uint64_t word) {
    const auto* bytes = reinterpret_cast<const uint8_t*>(&word);
    out.insert(out.end(), bytes, bytes + sizeof(word));
  };
  append_word(engine.AccessCount());
  append_word(engine.dense().positions());
  append_word(engine.dense().flushes());
  append_word(engine.StashSize());
  const auto plan = DensePlan(engine);
  for (size_t i = plan.first_live; i < plan.prefix_slots; ++i) {
    const auto& table = plan.tables[i];
    append_word(table.table_id);
    append_word(table.window_begin);
    append_word(table.window_end);
    append_word(table.num_buckets);
    for (size_t b = 0; b < table.num_buckets; ++b)
      append_word(table.masks[b]);
    out.insert(out.end(), table.data,
               table.data + table.num_buckets * engine.layout().BucketBytes());
  }
  return out;
}

void ExpectCurrentValue(const la::LevelArenaEngine& engine, bs::KeyWords key,
                        const std::array<uint8_t, 8>& value,
                        const std::string& where) {
  const auto plan = DensePlan(engine);
  size_t matches = 0;
  for (size_t i = plan.first_live; i < plan.prefix_slots; ++i) {
    const auto& table = plan.tables[i];
    if (!table.removable) continue;
    for (size_t b = 0; b < table.num_buckets; ++b) {
      const uint8_t* bucket = table.data + b * engine.layout().BucketBytes();
      for (size_t slot = 0; slot < bs::kBucketCapacity; ++slot) {
        const auto stored =
            bs::ReadSlotKey(bucket, slot, engine.layout().key_bytes);
        if (((table.masks[b] >> slot) & 1u) == 0 ||
            stored.w0 != key.w0 || stored.w1 != key.w1)
          continue;
        ++matches;
        for (size_t byte = 0; byte < value.size(); ++byte)
          Expect(bucket[(engine.layout().key_bytes + byte) *
                        bs::kBucketCapacity + slot] == value[byte], where);
      }
    }
  }
  Expect(matches == 1, where + ": current key is missing or duplicated");
}

void TestDummyReservation() {
  constexpr uint64_t max = std::numeric_limits<uint64_t>::max();
  uint64_t used = max;
  Expect(la::ReserveDummyCounters(used, 0, max) == 0 && used == max,
         "zero lanes reserve nothing at exhaustion");
  Expect(la::ReserveDummyCounters(used, max, 0) == 0 && used == max,
         "zero tables reserve nothing at exhaustion");
  Expect(Refuses([&] { la::ReserveDummyCounters(used, 1, 1); }) && used == max,
         "an exhausted counter refuses without wrapping its base");
  used = max - 12;
  Expect(la::ReserveDummyCounters(used, 3, 4) == max - 11 && used == max,
         "the last complete range includes UINT64_MAX");
  used = max - 11;
  Expect(Refuses([&] { la::ReserveDummyCounters(used, 3, 4); }) &&
             used == max - 11,
         "a partially fitting range refuses without mutation");
  used = 0;
  Expect(Refuses([&] { la::ReserveDummyCounters(used, max, 2); }) && used == 0,
         "the reservation checks multiplication before it can overflow");
  Expect(la::ReserveDummyCounters(used, 1, max) == 1 && used == max,
         "a whole-domain positive reservation is representable");
  used = 0;
  Expect(la::ReserveDummyCounters(used, 2, 3) == 1 && used == 6 &&
             la::ReserveDummyCounters(used, 1, 3) == 7 && used == 9,
         "successive scalar and batch ranges are disjoint");
}

void TestScalarStop() {
  for (bool synchronous : {false, true}) {
    auto options = Options(2);
    options.synchronous = synchronous;
    la::LevelArenaEngine engine(options);
    const std::array<uint8_t, 8> value{{1, 2, 3, 4, 5, 6, 7, 8}};
    engine.Write(uint64_t{7}, value.data());
    std::array<uint8_t, 8> out{};
    Expect(engine.Read(uint64_t{7}, out.data()) && out == value,
           "the final allowed scalar request succeeds");
    const auto before = DenseSnapshot(engine);
    out.fill(0xa5);
    const auto sentinel = out;
    Expect(Refuses([&] { engine.Read(uint64_t{7}, out.data()); }), "read stops");
    Expect(Refuses([&] { engine.Erase(uint64_t{7}, out.data()); }), "erase stops");
    Expect(Refuses([&] { engine.Write(uint64_t{7}, out.data()); }), "blind write stops");
    Expect(Refuses([&] { engine.ReadThenWrite(uint64_t{7}, out.data()); }),
           "probed write stops");
    Expect(Refuses([&] { engine.Exchange(uint64_t{7}, value.data(), out.data(), true); }),
           "exchange stops");
    bool called = false;
    Expect(Refuses([&] {
      engine.AccessStored(bs::KeyWords{7}, out.data(),
                          [&](uint8_t*, bool) { called = true; });
    }), "callback access stops");
    Expect(!called && out == sentinel, "refused requests preserve replies and skip callbacks");
    Expect(DenseSnapshot(engine) == before && !engine.Failed(),
           "scalar exhaustion preserves records and does not latch corruption");
    engine.Drain();
  }
}

void TestInitializedOffset() {
  la::LevelArenaEngine engine(Options(1));
  const uint64_t key = 7;
  const std::array<uint8_t, 8> value{{8, 7, 6, 5, 4, 3, 2, 1}};
  const bs::InitializationEntry records[] = {
      {reinterpret_cast<const uint8_t*>(&key), value.data()}};
  engine.Initialize(records, 1);
  Expect(engine.AccessCount() == 0 && engine.dense().positions() > 1,
         "synthetic initialization positions do not consume online accesses");
  std::array<uint8_t, 8> out{};
  Expect(engine.Read(key, out.data()) && out == value && engine.AccessCount() == 1,
         "initialized execution retains its full online horizon");
  const auto before = DenseSnapshot(engine);
  Expect(Refuses([&] { engine.Write(key, out.data()); }) &&
             DenseSnapshot(engine) == before,
         "initialized execution also stops at its horizon");
}

void TestNormalizationBudget() {
  const std::array<uint8_t, 8> value{{8, 7, 6, 5, 4, 3, 2, 1}};
  std::array<uint8_t, 64> key{};
  key[0] = 7;
  key[8] = 9;
  key[16] = 17;
  key[63] = 64;
  for (size_t width : {size_t{8}, size_t{9}, size_t{15}, size_t{16}, size_t{17},
                       size_t{64}}) {
    // Widths below 16 are stored verbatim and never call AES.
    const bool verbatim = width < 16;
    auto options = Options(8);
    options.key_bytes = width;
    options.max_key_normalizations = verbatim ? 0 : 2;
    la::LevelArenaEngine engine(options);
    const auto& const_engine = engine;
    const auto stored = const_engine.StoredKey(key.data());
    const auto repeated = const_engine.StoredKey(key.data());
    Expect(stored.w0 == repeated.w0 && stored.w1 == repeated.w1,
           "normalization reservations preserve repeated-key encoding");
    Expect(engine.KeyNormalizationCount() == (verbatim ? 0 : 2),
           "public const conversion charges every AES evaluation, including repeats");
    if (verbatim) {
      engine.RequireKeyNormalizationBudget(std::numeric_limits<uint64_t>::max());
      engine.Write(key.data(), value.data());
      std::array<uint8_t, 8> out{};
      Expect(engine.Read(key.data(), out.data()) && out == value &&
                 engine.KeyNormalizationCount() == 0,
             "verbatim keys need no normalization allowance");
      continue;
    }
    const auto before = DenseSnapshot(engine);
    Expect(Refuses([&] { const_engine.StoredKey(key.data()); }),
           "the public const conversion cannot exceed its allowance");
    std::array<uint8_t, 8> out;
    out.fill(0xa5);
    const auto sentinel = out;
    Expect(Refuses([&] { engine.Read(key.data(), out.data()); }),
           "normalization exhaustion stops reads");
    Expect(Refuses([&] { engine.Write(key.data(), value.data()); }),
           "normalization exhaustion stops blind writes");
    Expect(Refuses([&] { engine.ReadThenWrite(key.data(), value.data()); }),
           "normalization exhaustion stops probed writes");
    Expect(Refuses([&] { engine.WriteWithoutProbe(key.data(), value.data()); }),
           "normalization exhaustion stops the compatibility write entry point");
    Expect(Refuses([&] { engine.Erase(key.data()); }),
           "normalization exhaustion stops erase");
    Expect(Refuses([&] { engine.Erase(key.data(), out.data()); }),
           "normalization exhaustion stops erase with a reply");
    Expect(Refuses([&] {
      engine.Exchange(key.data(), value.data(), out.data(), true);
    }), "normalization exhaustion stops exchange");
    Expect(engine.KeyNormalizationCount() == 2 && out == sentinel &&
               DenseSnapshot(engine) == before && !engine.Failed(),
           "rejected normalization preserves allowance, records and outputs");
    // Stored representations already exist; drain and stored-key operations
    // do not need new normalizations.
    engine.WriteStored(stored, value.data());
    Expect(engine.ReadStored(stored, out.data()) && out == value &&
               engine.KeyNormalizationCount() == 2,
           "stored-key operations remain usable without additional conversion");
    engine.Drain();
  }

  auto options = Options(1);
  options.key_bytes = 17;
  {
    la::LevelArenaEngine engine(options);
    Expect(engine.MaxKeyNormalizations() == engine.Capacity() + options.max_accesses,
           "the default allowance covers one full initialization and the online horizon");
    engine.Write(key.data(), value.data());
    Expect(Refuses([&] { engine.Write(key.data(), value.data()); }) &&
               engine.KeyNormalizationCount() == 1,
           "access-horizon rejection happens before scalar normalization");
  }
  options.max_key_normalizations = 0;
  {
    la::LevelArenaEngine engine(options);
    Expect(engine.MaxKeyNormalizations() == 0 &&
               Refuses([&] { engine.StoredKey(key.data()); }) &&
               engine.KeyNormalizationCount() == 0,
           "an explicit zero allowance refuses before the first conversion");
    engine.RequireKeyNormalizationBudget(0);
  }
  options.max_key_normalizations = std::numeric_limits<uint64_t>::max();
  {
    la::LevelArenaEngine engine(options);
    engine.RequireKeyNormalizationBudget(std::numeric_limits<uint64_t>::max());
    engine.StoredKey(key.data());
    engine.RequireKeyNormalizationBudget(std::numeric_limits<uint64_t>::max() - 1);
    Expect(Refuses([&] {
      engine.RequireKeyNormalizationBudget(std::numeric_limits<uint64_t>::max());
    }) && engine.KeyNormalizationCount() == 1,
           "normalization preflight subtracts before addition can overflow");
  }
  options.max_accesses = 8;
  options.max_key_normalizations = 1;
  options.value_workers = 1;
  options.value_serial = true;
  {
    la::LevelArenaEngine engine(options);
    engine.Write(key.data(), value.data());
    Expect(engine.PendingValue(), "the last normalization can leave an accepted payload pending");
    std::array<uint8_t, 8> out{};
    Expect(Refuses([&] { engine.Read(key.data(), out.data()); }),
           "normalization exhaustion refuses another request with pending payloads");
    engine.Drain();
    const auto stored = bs::EncodeStoredKey(
        key.data(), options.key_bytes, bs::DeriveStoredKeyHashKeys(*options.secret_seed));
    Expect(!engine.PendingValue() && engine.ReadStored(stored, out.data()) &&
               out == value && engine.KeyNormalizationCount() == 1 && !engine.Failed(),
           "drain completes the accepted wide-key payload without another normalization");
  }
}

struct NormalizationRecords {
  const bs::InitializationEntry* entries;
  size_t* reads;
  size_t* advances;
  size_t throw_at;
  size_t index = 0;

  bs::InitializationEntry operator*() const {
    ++*reads;
    return entries[index];
  }
  NormalizationRecords& operator++() {
    ++*advances;
    if (index == throw_at) throw std::runtime_error("normalization input failed");
    ++index;
    return *this;
  }
};

void TestNormalizationInitialization() {
  for (bool synchronous : {false, true}) {
    auto options = Options(4);
    options.synchronous = synchronous;
    options.key_bytes = 17;
    options.max_key_normalizations = 4;
    la::LevelArenaEngine engine(options);
    std::array<std::array<uint8_t, 17>, 3> keys{};
    for (size_t j = 0; j < keys.size(); ++j)
      keys[j][16] = static_cast<uint8_t>(7 + j);
    const auto& key = keys[0];
    const std::array<uint8_t, 8> value{{3, 1, 4, 1, 5, 9, 2, 6}};
    const bs::InitializationEntry entries[] = {
        {keys[0].data(), value.data()}, {keys[1].data(), value.data()},
        {keys[2].data(), value.data()}};
    size_t reads = 0, advances = 0;
    bool threw = false;
    try {
      engine.Initialize(NormalizationRecords{entries, &reads, &advances, 0}, 2);
    } catch (const std::runtime_error& error) {
      threw = std::string(error.what()) == "normalization input failed";
    }
    Expect(threw && reads == 1 && advances == 1 &&
               engine.KeyNormalizationCount() == 2 && engine.AccessCount() == 0 &&
               engine.publisher().live_count() == 1 && !engine.Failed(),
           "a throwing initializer rolls back records but retains its whole reservation");
    const auto before = DenseSnapshot(engine);
    Expect(Refuses([&] {
      engine.Initialize(NormalizationRecords{entries, &reads, &advances, 0}, 3);
    }) && reads == 1 && advances == 1 &&
               engine.KeyNormalizationCount() == 2 && DenseSnapshot(engine) == before,
           "an oversized initialization retry refuses before dereferencing its input");
    engine.Initialize(entries, 1);
    std::array<uint8_t, 8> out{};
    Expect(engine.KeyNormalizationCount() == 3 && engine.AccessCount() == 0 &&
               engine.Read(key.data(), out.data()) && out == value &&
               engine.KeyNormalizationCount() == 4,
           "a smaller initialization retry and read use the remaining allowance");
    Expect(Refuses([&] { engine.Read(key.data(), out.data()); }) && !engine.Failed(),
           "initialization work and online conversions share one lifetime allowance");
    engine.Drain();
  }
}

void TestNormalizationBatchStop() {
  const std::array<uint8_t, 8> value{{4, 5, 6, 7, 8, 9, 10, 11}};
  std::array<uint8_t, 17> key{};
  key[16] = 7;
  for (unsigned mode = 0; mode < 3; ++mode) {
    for (auto layout : {bs::BatchResultLayout::kRows,
                        bs::BatchResultLayout::kSlicedPlaceAtLane}) {
      const size_t chunk = mode == 0 ? 2 : 4;
      auto options = Options(32);
      options.key_bytes = key.size();
      options.max_key_normalizations = chunk + 1;
      options.batch_lanes = 2;
      options.batch_result_layout = layout;
      if (mode != 0) {
        options.batch_execution = la::BatchExecutionShape::kParallelTiles;
        options.batch_participants = 2;
      }
      if (mode == 2) {
        options.batch_bucket_scan = true;
        options.geometry.stash_buckets = 2;
      }
      la::LevelArenaEngine engine(options);
      std::vector<std::array<uint8_t, 8>> out(chunk + 2);
      std::vector<uint8_t> found(chunk + 2, 0xa5);
      std::vector<bs::BatchRequest> requests(chunk + 2);
      for (size_t j = 0; j < requests.size(); ++j) {
        out[j].fill(0xa5);
        requests[j] = {bs::BatchOp::kWrite, false, key.data(), value.data(), out[j].data()};
      }
      Expect(Refuses([&] {
        engine.AccessBatch(requests.size(), requests.data(), found.data());
      }), "the first batch chunk beyond the normalization allowance refuses");
      Expect(engine.AccessCount() == chunk && engine.KeyNormalizationCount() == chunk &&
                 found[0] == 0,
             "completed batch lanes retain their access and normalization charges");
      for (size_t j = 1; j < chunk; ++j)
        Expect(found[j] == 1 && out[j] == value,
               "duplicate lanes remain charged and forward their values");
      for (size_t j = chunk; j < requests.size(); ++j)
        Expect(found[j] == 0xa5 &&
                   std::all_of(out[j].begin(), out[j].end(), [](uint8_t b) { return b == 0xa5; }),
               "a normalization refusal leaves every unexecuted lane output untouched");
      engine.AccessBatch(1, requests.data() + chunk, found.data() + chunk);
      Expect(engine.AccessCount() == chunk + 1 &&
                 engine.KeyNormalizationCount() == chunk + 1 &&
                 found[chunk] == 1 && out[chunk] == value,
             "a smaller batch retry uses the remaining normalization allowance");
      const auto before = DenseSnapshot(engine);
      Expect(Refuses([&] {
        engine.AccessBatch(1, requests.data() + chunk + 1, found.data() + chunk + 1);
      }) && DenseSnapshot(engine) == before && !engine.Failed(),
             "normalization exhaustion preserves the completed retry");
      engine.AccessBatch(0, static_cast<const bs::BatchRequest*>(nullptr), nullptr);
      engine.Drain();
    }
  }

  auto options = Options(8);
  options.key_bytes = key.size();
  options.max_key_normalizations = 2;
  la::LevelArenaEngine engine(options);
  std::array<bs::BatchRequest, 3> blind;
  for (auto& request : blind)
    request = {bs::BatchOp::kWrite, false, key.data(), value.data(), nullptr};
  Expect(Refuses([&] { engine.AccessBatch(blind.size(), blind.data(), nullptr); }) &&
             engine.AccessCount() == 2 && engine.KeyNormalizationCount() == 2,
         "blind batch lanes charge normalization and preserve their accepted prefix");
  // Independent conversion for inspection avoids spending the exhausted
  // engine's public accessor allowance.
  const auto stored = bs::EncodeStoredKey(
      key.data(), key.size(), bs::DeriveStoredKeyHashKeys(*options.secret_seed));
  ExpectCurrentValue(engine, stored, value, "blind batch prefix keeps its last value");
}

void TestBatchStop() {
  for (unsigned mode = 0; mode < 3; ++mode) {
    for (auto layout : {bs::BatchResultLayout::kRows,
                        bs::BatchResultLayout::kSlicedPlaceAtLane}) {
      const size_t chunk = mode == 0 ? 2 : 4;
      auto options = Options(chunk + 1);
      options.batch_lanes = 2;
      options.batch_result_layout = layout;
      if (mode != 0) {
        options.batch_execution = la::BatchExecutionShape::kParallelTiles;
        options.batch_participants = 2;
      }
      if (mode == 2) {
        options.batch_bucket_scan = true;
        options.geometry.stash_buckets = 2;
      }
      la::LevelArenaEngine engine(options);
      const std::array<uint8_t, 8> value{{4, 5, 6, 7, 8, 9, 10, 11}};
      std::vector<std::array<uint8_t, 8>> out(chunk + 2);
      std::vector<uint8_t> found(chunk + 2, 0xa5);
      std::vector<bs::BatchRequest64> requests(chunk + 2);
      for (size_t j = 0; j < requests.size(); ++j) {
        out[j].fill(0xa5);
        requests[j] = {bs::BatchOp::kWrite, false, 7, value.data(), out[j].data()};
      }
      Expect(Refuses([&] {
        engine.AccessBatch(requests.size(), requests.data(), found.data());
      }), "a batch refuses its first over-budget chunk");
      Expect(engine.AccessCount() == chunk && found[0] == 0,
             "the completed batch prefix remains committed");
      for (size_t j = 1; j < chunk; ++j)
        Expect(found[j] == 1 && out[j] == value, "completed replies retain forwarding");
      for (size_t j = chunk; j < requests.size(); ++j)
        Expect(found[j] == 0xa5 &&
                   std::all_of(out[j].begin(), out[j].end(), [](uint8_t b) { return b == 0xa5; }),
               "an unexecuted chunk leaves every output untouched");
      ExpectCurrentValue(engine, 7, value, "refusal preserves the committed key");
      engine.AccessBatch(1, requests.data() + chunk, found.data() + chunk);
      Expect(engine.AccessCount() == chunk + 1 && found[chunk] == 1 && out[chunk] == value,
             "a smaller retry may use the remaining access");
      const auto before = DenseSnapshot(engine);
      Expect(Refuses([&] {
        engine.AccessBatch(1, requests.data() + chunk + 1, found.data() + chunk + 1);
      }) && DenseSnapshot(engine) == before && !engine.Failed(),
             "the next chunk stops without corrupting the completed retry");
      engine.AccessBatch(0, static_cast<const bs::BatchRequest64*>(nullptr), nullptr);
    }
  }
}

void TestUnitBoundaryStop() {
  auto options = Options(65);
  options.batch_lanes = 64;
  la::LevelArenaEngine engine(options);
  const std::array<uint8_t, 8> value{{1, 3, 5, 7, 9, 11, 13, 15}};
  for (unsigned i = 0; i < 63; ++i) engine.Write(uint64_t{7}, value.data());
  std::array<std::array<uint8_t, 8>, 3> out{};
  std::array<uint8_t, 3> found{{0xa5, 0xa5, 0xa5}};
  std::array<bs::BatchRequest64, 3> requests;
  for (size_t j = 0; j < requests.size(); ++j) {
    out[j].fill(0xa5);
    requests[j] = {bs::BatchOp::kRead, false, 7, nullptr, out[j].data()};
  }
  Expect(Refuses([&] { engine.AccessBatch(3, requests.data(), found.data()); }),
         "budget is rechecked after a frozen-unit cut");
  Expect(engine.AccessCount() == 64 && engine.FlushCount() == 1 && found[0] == 1 &&
             out[0] == value && found[1] == 0xa5 && found[2] == 0xa5,
         "the boundary chunk commits and the following chunk stays untouched");
  engine.AccessBatch(1, requests.data() + 1, found.data() + 1);
  Expect(engine.AccessCount() == 65 && found[1] == 1 && out[1] == value,
         "the last access reads correctly across the frozen boundary");
}

void TestCallbackAndPendingValue() {
  const std::array<uint8_t, 8> value{{3, 1, 4, 1, 5, 9, 2, 6}};
  {
    la::LevelArenaEngine engine(Options(2));
    engine.Write(uint64_t{7}, value.data());
    std::array<uint8_t, 8> out{};
    bool threw = false;
    try {
      engine.AccessStored(bs::KeyWords{7}, out.data(), [](uint8_t* bytes, bool) {
        bytes[0] = 0xff;
        throw std::runtime_error("callback failure");
      });
    } catch (const std::runtime_error& error) {
      threw = std::string(error.what()) == "callback failure";
    }
    Expect(threw && engine.AccessCount() == 2,
           "callback rollback completes and counts its accepted access");
    ExpectCurrentValue(engine, 7, value, "throwing callback restores the prior value");
    Expect(Refuses([&] { engine.Write(uint64_t{7}, out.data()); }),
           "callback failure does not refund an executed access");
  }
  {
    auto options = Options(1);
    options.value_workers = 1;
    options.value_serial = true;
    la::LevelArenaEngine engine(options);
    engine.Write(uint64_t{7}, value.data());
    Expect(engine.PendingValue(), "the final accepted write leaves a pending payload");
    std::array<uint8_t, 8> replacement{};
    Expect(Refuses([&] { engine.Write(uint64_t{7}, replacement.data()); }),
           "pending payload completion does not admit another write");
    Expect(!engine.PendingValue() && engine.AccessCount() == 1 && !engine.Failed(),
           "refusal can finish the previous accepted payload without spending an access");
    ExpectCurrentValue(engine, 7, value, "pending completion preserves the accepted value");
    engine.Drain();
  }
}

std::atomic<bool> hold_publication{false};
std::atomic<bool> publication_held{false};

void PausePublication(la::ArenaPause point, unsigned who) {
  if (point != la::ArenaPause::kBeforePlanInstall || who != 1) return;
  publication_held.store(true, std::memory_order_release);
  while (hold_publication.load(std::memory_order_acquire))
    std::this_thread::yield();
}

struct ScopedPublicationPause {
  ScopedPublicationPause() {
    hold_publication.store(true, std::memory_order_release);
    publication_held.store(false, std::memory_order_release);
    la::SetArenaPauseHook(&PausePublication);
  }
  ~ScopedPublicationPause() {
    hold_publication.store(false, std::memory_order_release);
    la::SetArenaPauseHook(nullptr);
  }
};

void TestDrainAtHorizon() {
  // With one outstanding-prefix slot, holding prefix 0's publication makes
  // the final request, whose insertion would complete prefix 1, wait for a
  // slot before it probes and refuse at the wait limit with nothing applied.
  // Released, the same request is the horizon's last, and a drain publishes
  // it.
  auto options = Options(256);
  options.geometry.branching = 4;
  options.geometry.levels = 3;
  options.geometry.top_digit = 4;
  options.geometry.dense_prefixes = 1;
  options.owner_threads = 3;
  options.defer_owner_start = true;
  options.flush_policy = la::LevelArenaEngine::FlushPolicy::kHandOver;
  options.wait_limit_millis = 250;
  la::LevelArenaEngine engine(options);
  // Destroy the pause before the engine even if a test operation throws.
  ScopedPublicationPause pause;
  engine.StartOwnerThreads();
  const std::array<uint8_t, 8> value{{2, 7, 1, 8, 2, 8, 1, 8}};
  std::string refusal;
  for (uint64_t key = 1; key <= 256; ++key) {
    try {
      engine.Write(key, value.data());
    } catch (const std::exception& error) {
      refusal = error.what();
      break;
    }
  }
  Expect(publication_held.load(std::memory_order_acquire) &&
             refusal.find("dense prefix slot") != std::string::npos &&
             engine.AccessCount() == 255 && !engine.dense().UnitFull() &&
             !engine.Failed(),
         "the final request was applied although it was refused");
  hold_publication.store(false, std::memory_order_release);
  engine.Drain();
  Expect(!Refuses([&] { engine.Write(uint64_t{256}, value.data()); }),
         "the refused request was not accepted once a slot was free");
  Expect(Refuses([&] { engine.Write(uint64_t{257}, value.data()); }),
         "exhaustion does not refuse another insertion");
  engine.Drain();
  Expect(engine.AccessCount() == 256 && engine.FlushCount() == 4 &&
             !engine.dense().UnitFull() && engine.StashSize() == 0 &&
             !engine.Failed(),
         "Drain does not complete the accepted work at the horizon");

  engine.ProbeListLength();
  la::ReaderEpoch::Guard guard(engine.publisher().epoch());
  const auto& plan = *engine.publisher().CurrentPlan();
  size_t matches = 0;
  for (size_t i = plan.first_live; i < plan.tables.size(); ++i) {
    const auto& table = plan.tables[i];
    for (size_t b = 0; b < table.num_buckets; ++b) {
      const uint8_t* bucket = table.data + b * engine.layout().BucketBytes();
      for (size_t slot = 0; slot < bs::kBucketCapacity; ++slot) {
        if (((table.masks[b] >> slot) & 1u) == 0 ||
            bs::ReadSlotKey(bucket, slot, engine.layout().key_bytes).w0 != 256)
          continue;
        ++matches;
        for (size_t byte = 0; byte < value.size(); ++byte)
          Expect(bucket[(engine.layout().key_bytes + byte) *
                        bs::kBucketCapacity + slot] == value[byte],
                 "Drain retains the final accepted record's value");
      }
    }
  }
  Expect(matches == 1, "Drain publishes the final accepted record exactly once");
}
}  // namespace

int main() {
  TestLifetimeCoordinates();
  TestLifetimeGeometrySweep();
  TestLifetimeConstruction();
  TestDummyReservation();
  TestScalarStop();
  TestInitializedOffset();
  TestNormalizationBudget();
  TestNormalizationInitialization();
  TestNormalizationBatchStop();
  TestBatchStop();
  TestUnitBoundaryStop();
  TestCallbackAndPendingValue();
  TestDrainAtHorizon();
  if (failures != 0) return 1;
  std::printf("lifetime: coordinate bounds, dummy ranges, scalar/batch horizons, normalization budgets, initialization, "
              "unit cuts, callback rollback, pending payloads and drain passed\n");
  return 0;
}
