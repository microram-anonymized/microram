// The public tree ORAM map (include/cpu_byteslice_oram/tree_oram.hpp) over the
// real hierarchical position map, byte and typed forms, amortized and
// deamortized: the same model-checked workload the engine test runs, plus
// argument validation, the capacity floor and the arena split.
//
// What this adds over cpu_tree_read_path_oram_test is the position map: there
// the map is a std::unordered_map, here every operation is a real ORAM exchange,
// so a mistake in the (position, uid) round trip through the stored bytes
// shows up here and nowhere else.  It also covers the two ways the uid is
// chosen (from the key, or from a counter), `exchange`, and the HYBRID that
// picks between this engine and the hierarchical one by value width.

// The level arena's pause hooks, to inject a rebuild failure into the
// hybrid's hierarchy (TestHybridReportsHierarchyFailure).  Nothing here is
// timed.
#define MICRORAM_BYTESLICE_LEVEL_ARENA_PAUSE 1
#include <cpu_byteslice_oram/oram.hpp>

#include "tests/oram/cpu_byteslice_test_support.hpp"

#include <array>
#include <atomic>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <random>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

namespace {

namespace oram = cpu_byteslice_oram;
namespace la = microram::byteslice::levelarena;
using microram::byteslice::test_support::Expect;
using microram::byteslice::test_support::ExpectThrows;
using microram::byteslice::test_support::ExpectThrowsAs;
using microram::byteslice::test_support::WideKey;

std::vector<uint8_t> ValueFor(uint64_t key, uint64_t version, size_t bytes) {
  std::vector<uint8_t> v(bytes);
  uint64_t state = key * 0x9E3779B97F4A7C15ull + version * 0xD1B54A32D192ED03ull + 1;
  for (auto& b : v) {
    state = state * 6364136223846793005ull + 1442695040888963407ull;
    b = static_cast<uint8_t>(state >> 40);
  }
  return v;
}

template <typename Map>
void ExerciseByteMap(Map& map, size_t key_bytes, size_t value_bytes,
                     unsigned steps, uint64_t seed) {
  Expect(map.capacity() >= map.requested_capacity(),
         "capacity is below the request");
  Expect(map.key_bytes() == key_bytes, "wrong key width");
  Expect(map.value_bytes() == value_bytes, "wrong value width");
  Expect(map.arena_bytes() ==
             map.tree_arena_bytes() + map.position_map_arena_bytes(),
         "the arena split does not add up");
  Expect(map.tree_arena_bytes() > 0 && map.position_map_arena_bytes() > 0,
         "an arena half is empty");

  std::mt19937_64 rng(seed);
  const size_t universe = map.capacity();
  std::unordered_map<uint64_t, uint64_t> live;
  std::vector<uint8_t> out(value_bytes);
  const std::vector<uint8_t> zeros(value_bytes, 0);
  for (unsigned step = 0; step < steps; ++step) {
    const uint64_t k = 1 + rng() % universe;
    const std::vector<uint8_t> key = WideKey(k, key_bytes);
    auto it = live.find(k);
    const bool present = it != live.end();
    const unsigned op = rng() % 10;
    if (op < 4) {
      const bool found = map.find(key.data(), out.data());
      Expect(found == present, "find disagrees with the model");
      Expect(out == (present ? ValueFor(k, it->second, value_bytes) : zeros),
             "find returned the wrong bytes");
    } else if (op < 6) {
      Expect(map.contains(key.data()) == present,
             "contains disagrees with the model");
    } else if (op < 9 || live.size() >= universe) {
      if (live.size() >= universe && !present) continue;
      const uint64_t version = present ? it->second + 1 : 1;
      map.insert_or_assign(key.data(), ValueFor(k, version, value_bytes).data());
      live[k] = version;
    } else {
      Expect(map.erase(key.data()) == present, "erase disagrees with the model");
      if (present) live.erase(it);
    }
  }
  for (const auto& kv : live) {
    const std::vector<uint8_t> key = WideKey(kv.first, key_bytes);
    Expect(map.find(key.data(), out.data()), "a live key vanished");
    Expect(out == ValueFor(kv.first, kv.second, value_bytes),
           "a live key holds a stale value");
  }
  Expect(!map.failed(), "the map reports a failure that did not happen");
  map.drain_rebuilds();
  std::printf("  %s N=%zu K=%zu V=%zu: %u steps, %zu live, max stash %u, "
              "%.2f MiB (tree %.2f + posmap %.2f)\n",
              Map::deamortized ? "deamortized" : "amortized  ", map.capacity(),
              key_bytes, value_bytes, steps, live.size(),
              map.max_stash_occupancy(), map.arena_bytes() / 1048576.0,
              map.tree_arena_bytes() / 1048576.0,
              map.position_map_arena_bytes() / 1048576.0);
}


// A model-checked workload over the interface ByteMap, TreeByteMap and
// HybridByteMap all share, so the same body checks all three.
template <typename Map>
void ExerciseCommon(Map& map, size_t key_bytes, size_t value_bytes,
                    unsigned steps, uint64_t seed) {
  std::mt19937_64 rng(seed);
  const size_t universe = map.capacity();
  std::unordered_map<uint64_t, uint64_t> live;
  std::vector<uint8_t> out(value_bytes), old(value_bytes);
  const std::vector<uint8_t> zeros(value_bytes, 0);
  for (unsigned step = 0; step < steps; ++step) {
    const uint64_t k = rng() % universe;  // includes key 0
    const std::vector<uint8_t> key = WideKey(k, key_bytes);
    auto it = live.find(k);
    const bool present = it != live.end();
    const unsigned op = rng() % 10;
    if (op < 3) {
      Expect(map.find(key.data(), out.data()) == present,
             "find disagrees with the model");
      Expect(out == (present ? ValueFor(k, it->second, value_bytes) : zeros),
             "find returned the wrong bytes");
    } else if (op < 5) {
      Expect(map.contains(key.data()) == present,
             "contains disagrees with the model");
    } else if (op < 7) {
      // exchange: one access that reads the old value and writes the new.
      const uint64_t version = present ? it->second + 1 : 1;
      const std::vector<uint8_t> next = ValueFor(k, version, value_bytes);
      const bool insert = (rng() & 1) != 0;
      Expect(map.exchange(key.data(), next.data(), old.data(), insert) == present,
             "exchange disagrees with the model");
      Expect(old == (present ? ValueFor(k, it->second, value_bytes) : zeros),
             "exchange returned the wrong old bytes");
      if (present || insert) live[k] = version;
    } else if (op < 9 || live.size() >= universe) {
      if (live.size() >= universe && !present) continue;
      const uint64_t version = present ? it->second + 1 : 1;
      map.insert_or_assign(key.data(), ValueFor(k, version, value_bytes).data());
      live[k] = version;
    } else {
      Expect(map.erase(key.data(), old.data()) == present,
             "erase disagrees with the model");
      Expect(old == (present ? ValueFor(k, it->second, value_bytes) : zeros),
             "erase returned the wrong old bytes");
      if (present) live.erase(it);
    }
  }
  for (const auto& kv : live) {
    const std::vector<uint8_t> key = WideKey(kv.first, key_bytes);
    Expect(map.find(key.data(), out.data()), "a live key vanished");
    Expect(out == ValueFor(kv.first, kv.second, value_bytes),
           "a live key holds a stale value");
  }
  map.drain_rebuilds();
}

// AN ALIASED EXCHANGE, which is the whole reason a copy of the caller's
// value exists anywhere.  The data pass writes `old_out` one value byte line
// at a time and reads the SAME line of the input back in immediately, so
// `exchange(k, buf, buf)` would feed the old value back as the new one unless
// somebody captured the input first.  Who does is the ENGINE's answer -- the threaded form always copies into
// its job slot, the synchronous one never does -- and this layer copies only
// when the engine does not AND the ranges really intersect.  So every shape
// of intersection has to work on every engine.
//
// `offset` places the two ranges relative to one another inside one buffer:
// 0 is the same pointer, a positive offset puts the input after the output
// and a negative one before it.
template <typename Map>
void CheckAliasedExchange(Map& map, size_t value_bytes, long offset,
                          uint64_t key_index, const char* what) {
  const std::vector<uint8_t> first = ValueFor(key_index, 1, value_bytes);
  const std::vector<uint8_t> second = ValueFor(key_index, 2, value_bytes);
  const std::vector<uint8_t> key = WideKey(key_index, 8);
  map.insert_or_assign(key.data(), first.data());

  const size_t span = value_bytes + static_cast<size_t>(std::abs(offset));
  std::vector<uint8_t> scratch(span, 0);
  uint8_t* out = scratch.data() + (offset < 0 ? static_cast<size_t>(-offset) : 0);
  uint8_t* in = scratch.data() + (offset > 0 ? static_cast<size_t>(offset) : 0);
  std::memcpy(in, second.data(), value_bytes);

  Expect(map.exchange(key.data(), in, out, /*insert=*/false) == true, what);
  Expect(std::memcmp(out, first.data(), value_bytes) == 0, what);
  // Whatever the overlap did to the input buffer afterwards, the value the
  // map now holds is what that buffer held when the call was made.
  std::memset(scratch.data(), 0xA5, scratch.size());
  std::vector<uint8_t> back(value_bytes);
  Expect(map.find(key.data(), back.data()), what);
  Expect(back == second, what);
}

// The four intersections, synchronous and with payload workers.
void TestAliasedExchange() {
  constexpr size_t kV = 256;
  struct Case {
    unsigned workers;
    const char* name;
  };
  const Case cases[] = {
      {0, "synchronous"},
      {2, "two payload workers"},
  };
  for (const Case& c : cases) {
    oram::TreeOptions options;
    options.position_map.deamortized_owner_threads = 0;
    options.payload_max_threads = c.workers;
    oram::TreeByteMap<> map(512, 8, kV, options);
    Expect(map.uses_payload_workers() == (c.workers != 0), c.name);
    uint64_t key = 1;
    // The same pointer; the input just after the output and just before it,
    // overlapping by all but one byte and by half the value.
    for (long offset : {0L, 1L, -1L, static_cast<long>(kV) / 2,
                        -static_cast<long>(kV) / 2}) {
      CheckAliasedExchange(map, kV, offset, key++, c.name);
    }
    // And a DISJOINT exchange still works, which is the path that skips the
    // copy entirely on the synchronous engine.
    const std::vector<uint8_t> a = ValueFor(key, 1, kV);
    const std::vector<uint8_t> b = ValueFor(key, 2, kV);
    const std::vector<uint8_t> k = WideKey(key, 8);
    std::vector<uint8_t> old(kV);
    map.insert_or_assign(k.data(), a.data());
    Expect(map.exchange(k.data(), b.data(), old.data(), false), c.name);
    Expect(old == a, c.name);
    std::vector<uint8_t> back(kV);
    Expect(map.find(k.data(), back.data()) && back == b, c.name);
  }
  std::puts("  aliased exchange: 5 intersections x 2 engines");
}

// THE UID: from the key when it fits in eight bytes, else from a counter.
// Both must be correct; only the position map's value width differs.
void TestUidFromKey() {
  oram::TreeOptions light;
  light.position_map.deamortized_owner_threads = 0;

  // Eight-byte keys: on by default, and the position map stores the
  // position alone, in as many bytes as the tree's depth needs
  // (cpu_tree_position_map.hpp's THE POSITION IS AS WIDE AS THE TREE).
  oram::TreeByteMap<> from_key(512, 8, 32, light);
  Expect(from_key.uid_from_key(), "the uid should come from an 8-byte key");
  const unsigned leaf_bits = from_key.engine().geometry().leaf_bits;
  const size_t position_bytes = (leaf_bits + 7) / 8;
  Expect(position_bytes >= 1 && position_bytes < 8,
         "a 512-entry tree should need fewer than eight position bytes");
  Expect(from_key.engine().position_map().byte_map().value_bytes() ==
             position_bytes,
         "the position map should store the position alone, at the tree's width");
  Expect(from_key.engine().position_map().PositionBits() >= leaf_bits,
         "the position map is narrower than the tree");
  ExerciseCommon(from_key, 8, 32, 3000, 61);

  // The same workload with the counter-derived uid: the position, then the
  // 8-byte uid.
  oram::TreeOptions counter = light;
  counter.uid_from_key = false;
  oram::TreeByteMap<> from_counter(512, 8, 32, counter);
  Expect(!from_counter.uid_from_key(), "the option was ignored");
  Expect(from_counter.engine().position_map().byte_map().value_bytes() ==
             position_bytes + 8,
         "the position map should store (position, uid)");
  ExerciseCommon(from_counter, 8, 32, 3000, 61);

  // A key too wide for the uid field falls back on its own.
  oram::TreeByteMap<> wide(512, 13, 32, light);
  Expect(!wide.uid_from_key(), "a 13-byte key cannot be the uid");
  Expect(wide.engine().position_map().byte_map().value_bytes() ==
             position_bytes + 8,
         "a wide key needs the stored uid");
  ExerciseCommon(wide, 13, 32, 2000, 62);

  // A larger tree crosses a byte boundary: 2^17 entries need 15 leaf bits,
  // i.e. two bytes, and every position must survive the round trip
  // through the narrow value -- which the workload's reads check.
  {
    oram::TreeByteMap<> deeper(1 << 17, 8, 16, light);
    const unsigned lb = deeper.engine().geometry().leaf_bits;
    Expect(lb > 8, "2^17 entries should need more than one byte of position");
    Expect(deeper.engine().position_map().byte_map().value_bytes() ==
               (lb + 7) / 8,
           "the deeper tree's position map has the wrong width");
    ExerciseCommon(deeper, 8, 16, 4000, 63);
  }
  // And a position map built for a shallower tree is refused rather than
  // truncating this tree's leaves.
  {
    microram::tree::TreeKnobs knobs;
    const microram::tree::TreeGeometry g =
        microram::tree::TreeGeometry::ForCapacity(1 << 12, knobs.fold, 16);
    Expect(g.leaf_bits > 8, "the probe tree should be deeper than a byte");
    ExpectThrows(
        [&] {
          microram::tree::CpuTreeMap<microram::tree::HierarchicalPositionMap<>> m(
              g, 8, knobs,
              microram::tree::HierarchicalPositionMap<>(
                  1 << 12, 8, light.position_map, /*uid_from_key=*/true,
                  /*leaf_bits=*/8),
              microram::crypto::SecretKeySeed::Fixed(1), /*uid_from_key=*/true);
        },
        "a position map narrower than the tree was accepted");
  }

  oram::TreeByteMap<> narrow(512, 4, 32, light);
  Expect(narrow.uid_from_key(), "a 4-byte key should be the uid");
  std::array<uint8_t, 4> all_ones{0xFF, 0xFF, 0xFF, 0xFF};
  std::array<uint8_t, 32> value{}, out{};
  value[0] = 7;
  narrow.insert_or_assign(all_ones.data(), value.data());
  Expect(narrow.find(all_ones.data(), out.data()) && out == value,
         "the all-ones 4-byte key did not round trip");
  std::array<uint8_t, 4> zero_key{};
  value[0] = 9;
  narrow.insert_or_assign(zero_key.data(), value.data());
  Expect(narrow.find(zero_key.data(), out.data()) && out == value,
         "the zero key did not round trip");

  // NO key value is reserved.  The uid is the key verbatim, and what marks a
  // slot as occupied is the top bit of its position, so a key whose uid is the
  // all-zero word is an ordinary key -- the case a uid-is-nonzero convention
  // could not have represented.  Both engines must agree on all three of the
  // corners: zero, all-ones, and 0x9E3779B97F4A7C15 (the golden-ratio
  // constant a reserved-sentinel uid convention would typically pick).
  const uint64_t corners[] = {0ull, ~uint64_t{0},
                              0x9E3779B97F4A7C15ull};
  for (uint64_t corner : corners) {
    std::array<uint8_t, 8> key{};
    std::memcpy(key.data(), &corner, 8);
    std::array<uint8_t, 32> v{};
    v[0] = static_cast<uint8_t>(corner + 1);
    v[31] = 0xAB;
    for (auto* map : {&from_key, &from_counter}) {
      std::array<uint8_t, 32> got{};
      // The workload above may already have touched key 0.
      (void)map->erase(key.data());
      Expect(!map->find(key.data(), got.data()), "an erased corner key is present");
      map->insert_or_assign(key.data(), v.data());
      Expect(map->find(key.data(), got.data()) && got == v,
             "a corner key did not round trip");
      Expect(map->erase(key.data()), "a corner key could not be erased");
      Expect(!map->contains(key.data()), "an erased corner key came back");
    }
  }
}

// THE HYBRID: the value width picks the engine, and both must behave the same.
void TestHybrid() {
  oram::HybridOptions small;
  small.hierarchical.deamortized_owner_threads = 0;
  small.tree.position_map.deamortized_owner_threads = 0;

  oram::HybridByteMap<> narrow(512, 8, 16, small);
  Expect(!narrow.uses_tree(), "a 16-byte value should stay on the hierarchy");
  Expect(!narrow.failed(), "a healthy hierarchy reports a failure");
  Expect(narrow.tree() == nullptr && narrow.hierarchical() != nullptr,
         "the unused engine was built");
  ExerciseCommon(narrow, 8, 16, 3000, 71);

  oram::HybridByteMap<> big(512, 8, oram::kHybridTreeValueThreshold, small);
  Expect(big.uses_tree(), "a value at the threshold should use the tree");
  Expect(big.hierarchical() == nullptr, "the unused engine was built");
  // THE CORE BUDGET the threshold is chosen for: the hybrid's tree runs
  // `kHybridTreePayloadWorkers` payload planes, and the threshold is only
  // meaningful if it does.
  Expect(big.tree()->uses_payload_workers(),
         "the hybrid's tree should run payload workers");
  Expect(big.tree()->payload_planes() ==
             oram::HybridPolicyPayloadWorkers(oram::kHybridTreeValueThreshold),
         "the hybrid's tree got the wrong number of payload planes");
  ExerciseCommon(big, 8, oram::kHybridTreeValueThreshold, 600, 72);

  // Just below the threshold is still the hierarchy.
  oram::HybridByteMap<> just_under(512, 8, oram::kHybridTreeValueThreshold - 1,
                                   small);
  Expect(!just_under.uses_tree(), "the threshold is inclusive on the wrong side");

  // The threshold moves.
  oram::HybridOptions forced = small;
  forced.tree_value_threshold = 16;
  oram::HybridByteMap<> forced_tree(512, 8, 16, forced);
  Expect(forced_tree.uses_tree(), "the threshold override was ignored");
  ExerciseCommon(forced_tree, 8, 16, 2000, 73);

  oram::HybridOptions never = small;
  never.tree_value_threshold = SIZE_MAX;
  oram::HybridByteMap<> forced_hier(512, 8, 4096, never);
  Expect(!forced_hier.uses_tree(), "the hierarchy could not be forced");

  // A plain Options still configures whichever engine is picked.
  oram::Options plain;
  plain.deamortized_owner_threads = 0;
  oram::HybridByteMap<> from_plain(512, 8, 16, plain);
  Expect(!from_plain.uses_tree(), "the default threshold changed");

  // The typed Map dispatches on sizeof(T).
  oram::Map<uint64_t, uint64_t> tiny(512, plain);
  Expect(!tiny.byte_map().uses_tree(), "a uint64 value should use the hierarchy");
  struct Big {
    std::array<uint8_t, oram::kHybridTreeValueThreshold> bytes;
    bool operator==(const Big& o) const { return bytes == o.bytes; }
  };
  oram::Map<uint64_t, Big> large(256, small);
  Expect(large.byte_map().uses_tree(), "a large value should use the tree");
  Big put{};
  put.bytes[0] = 42;
  put.bytes[oram::kHybridTreeValueThreshold - 1] = 7;
  large.insert_or_assign(9, put);
  Big got{};
  Expect(large.find(9, &got) && got == put, "the typed hybrid lost the value");
  large.drain_rebuilds();
  std::printf(
      "  hybrid: threshold %zu B at %u payload workers, typed Map over %zu B "
      "uses the tree\n",
      oram::kHybridTreeValueThreshold,
      oram::HybridPolicyPayloadWorkers(oram::kHybridTreeValueThreshold),
      sizeof(Big));

  // The default crossover runs one payload worker per started 32 bytes.
  Expect(oram::kHybridTreeValueThreshold == 96 &&
             oram::HybridPolicyPayloadWorkers(oram::kHybridTreeValueThreshold) == 3,
         "the default threshold changed");
}

// One level-1 publication failure, through the arena's pause hook.
std::atomic<int> g_level1_throws{0};
constexpr const char* kInjectedFailure = "injected level-1 publication failure";
void ThrowAtLevel1Install(la::ArenaPause point, unsigned who) {
  if (point == la::ArenaPause::kBeforePlanInstall && who == 1 &&
      g_level1_throws.fetch_sub(1) > 0) {
    throw std::runtime_error(kInjectedFailure);
  }
}

// THE HYBRID REPORTS A FAILED HIERARCHY.  The arena latches a failed rebuild
// and refuses every later access; the hybrid must forward that, not answer
// `failed() == false` from its own state.  Both latches:
// the requester's, from an inline step, and an owner thread's.  On both
// backends: a 128-byte value selects the tree, whose position map is the
// failing hierarchy, and the tree map must report it too.
void TestHybridReportsHierarchyFailure() {
  for (size_t value_bytes : {size_t{8}, size_t{128}})
  for (unsigned owners : {0u, 1u}) {
    oram::Options options;
    options.deamortized_owner_threads = owners;
    oram::HybridByteMap<> map(4096, 8, value_bytes, options);
    Expect(map.uses_tree() == (value_bytes == 128),
           "an 8-byte value should stay on the hierarchy, 128 bytes on the tree");
    Expect(!map.failed(), "a healthy hierarchy reports a failure");
    std::string what;
    std::vector<uint8_t> value(value_bytes, 42);
    g_level1_throws.store(1);
    la::SetArenaPauseHook(&ThrowAtLevel1Install);
    for (uint64_t i = 0; i < 20000 && what.empty(); ++i) {
      const uint64_t key = i % 1000 + 1;
      try {
        map.insert_or_assign(reinterpret_cast<const uint8_t*>(&key),
                             value.data());
      } catch (const std::exception& error) {
        what = error.what();
      }
    }
    la::SetArenaPauseHook(nullptr);
    Expect(what == kInjectedFailure,
           owners == 0 ? "the inline failure was not raised"
                       : "the owner's failure was not re-raised");
    Expect(map.failed(), owners == 0
                             ? "the hybrid hides the requester's failure latch"
                             : "the hybrid hides an owner's failure latch");
    const uint64_t key = 1;
    if (map.uses_tree()) {
      // Latched: the tree map refuses as a failed instance from now on,
      // not with the hierarchy's error that reads like a retryable one.
      ExpectThrowsAs<microram::tree::FailedInstanceError>([&] {
        map.find(reinterpret_cast<const uint8_t*>(&key), value.data());
      }, "a tree map over a failed position map is not a failed instance");
    } else {
      ExpectThrows([&] {
        map.find(reinterpret_cast<const uint8_t*>(&key), value.data());
      }, "a failed hierarchy answered a later access");
    }
    Expect(map.failed(), "the failure did not stay latched");
  }
}

// THE KEY-NORMALIZATION BUDGET IS PREFLIGHTED WITH THE HORIZON.  With keys of
// 16 bytes or more every position-map access spends one normalization, and a
// composed operation that cannot afford them all is refused before any user
// code runs or any position changes, as ByteMap refuses it; the map stays
// usable for what the remainder affords.
void TestKeyNormalizationPreflight() {
  std::vector<uint8_t> value(8, 5), out(8);
  std::array<uint8_t, 16> key{};
  {
    // Two writes spend two of four; a key-changing callback needs three.
    oram::TreeOptions options;
    options.position_map.max_key_normalizations = 4;
    oram::TreeByteMap<> map(1024, 16, 8, options);
    key[0] = 1;
    map.write(key.data(), value.data());
    key[0] = 2;
    map.write(key.data(), value.data());
    key[0] = 1;
    bool ran = false;
    ExpectThrowsAs<std::overflow_error>([&] {
      map.access(key.data(), [&](uint8_t* k, uint8_t* v) {
        ran = true;
        k[0] = 9;
        v[0] = 42;
      });
    }, "a key-changing callback past the normalization budget was not refused");
    Expect(!ran, "the callback ran although its accesses could not be afforded");
    Expect(!map.failed(), "a refused callback latched the map");
    Expect(map.find(key.data(), out.data()) && out == value,
           "a refused key-changing callback lost its source record");
  }
  {
    // A batch is refused whole, before any position is remapped.
    oram::TreeOptions options;
    options.position_map.max_key_normalizations = 20;
    oram::TreeByteMap<> map(1024, 16, 8, options);
    const size_t n = 40;
    std::vector<uint8_t> keys(16 * n, 0), values(8 * n, 7);
    std::vector<oram::BatchRequest> requests(n);
    for (size_t i = 0; i < n; ++i) {
      keys[16 * i] = static_cast<uint8_t>(i + 1);
      requests[i] = {oram::BatchOp::kWrite, false, &keys[16 * i],
                     &values[8 * i], nullptr};
    }
    ExpectThrowsAs<std::overflow_error>([&] {
      map.access_batch(n, requests.data(), nullptr);
    }, "a batch past the normalization budget was not refused");
    Expect(!map.failed(), "a refused batch latched the map");
    Expect(map.position_map_access_count() == 0,
           "a refused batch remapped positions");
    // The remainder affords exactly half of it.
    map.access_batch(n / 2, requests.data(), nullptr);
    Expect(!map.failed() && map.position_map_access_count() == n / 2,
           "the affordable half of the batch did not run");
  }
}

// set_batch_lanes VALIDATES ITS ARGUMENT ON BOTH BACKENDS, as the hierarchy
// does; the tree then ignores it (its batch width is fixed).
void TestSetBatchLanes() {
  oram::HybridByteMap<> hierarchy(4096, 8, 8), tree(4096, 8, 128);
  Expect(!hierarchy.uses_tree() && tree.uses_tree(), "unexpected backends");
  for (auto* map : {&hierarchy, &tree}) {
    ExpectThrowsAs<std::invalid_argument>([&] { map->set_batch_lanes(0); },
                                          "zero batch lanes accepted");
    ExpectThrowsAs<std::invalid_argument>([&] { map->set_batch_lanes(65); },
                                          "65 batch lanes accepted");
    map->set_batch_lanes(1);
    map->set_batch_lanes(64);
  }
  Expect(tree.batch_lanes() == 1, "the tree's batch width moved");
}

void TestByteMaps() {
  oram::TreeOptions amortized_options;
  amortized_options.position_map.max_accesses = uint64_t{1} << 24;
  oram::TreeByteMap<false> amortized(1000, 8, 64, amortized_options);
  // The capacity is the one asked for, not rounded to a power of two.
  Expect(amortized.capacity() == 1000, "capacity was not the one requested");
  ExerciseByteMap(amortized, 8, 64, 4000, 21);

  oram::TreeOptions deamortized_options;
  deamortized_options.position_map.deamortized_owner_threads = 0;
  oram::TreeByteMap<> deamortized(1000, 8, 64, deamortized_options);
  ExerciseByteMap(deamortized, 8, 64, 4000, 22);

  // A wide key, an odd value width and a deep fold.  A folded level is not
  // stored, so its slots come out of the stash region: fold 3 is 28 of the
  // 191 lanes.
  oram::TreeOptions wide_options;
  wide_options.fold = 3;
  oram::TreeByteMap<> wide(2000, 13, 300, wide_options);
  ExerciseByteMap(wide, 13, 300, 3000, 23);

  // Synchronous, then with payload workers -- one per started 32 value bytes
  // under the cap.
  oram::TreeOptions sync_options;
  sync_options.payload_max_threads = 0;
  oram::TreeByteMap<> sync(2000, 8, 100, sync_options);
  Expect(!sync.uses_payload_workers(), "workers with a cap of 0");
  Expect(sync.stash_capacity() == 192, "three stash registers by default");
  ExerciseByteMap(sync, 8, 100, 3000, 24);
  oram::TreeOptions workers_options;
  workers_options.payload_max_threads = 3;
  workers_options.payload_spin_micros = 2000;
  workers_options.position_map.deamortized_owner_threads = 0;
  oram::TreeByteMap<> workers(2000, 8, 100, workers_options);
  Expect(workers.payload_planes() ==
             microram::byteslice::HelpersThatFit(3, 1),
         "100 B under a cap of 3 is three workers");
  ExerciseByteMap(workers, 8, 100, 3000, 25);
  workers.drain_tree();

  // The default shape is binary, four slots, a load of one half: two tree
  // slots per entry less the stash, which is a large share of a small tree.
  oram::TreeOptions plain;
  plain.position_map.deamortized_owner_threads = 0;
  oram::TreeByteMap<> big(1 << 14, 8, 512, plain);
  Expect(big.tree_slots_per_entry() >= 2.0 && big.tree_slots_per_entry() < 2.2,
         "the default shape is two slots per entry");
  ExerciseByteMap(big, 8, 512, 3000, 26);

  // Overprovisioned leaves: `leaf_scale` halves the load, which is the knob
  // the stash measurement moves.
  oram::TreeOptions light = plain;
  light.leaf_scale = 1;
  oram::TreeByteMap<> dense(1 << 12, 8, 16, plain);
  oram::TreeByteMap<> sparse(1 << 12, 8, 16, light);
  const double ratio = sparse.tree_slots_per_entry() / dense.tree_slots_per_entry();
  Expect(ratio > 1.9 && ratio < 2.1, "leaf_scale 1 did not halve the load");
  ExerciseByteMap(sparse, 8, 16, 2000, 27);

  // An explicit four-register stash, over a one-register path.
  oram::TreeOptions four = plain;
  four.stash_registers = 4;
  oram::TreeByteMap<> wide_stash(1024, 8, 64, four);
  Expect(wide_stash.stash_capacity() == 256, "four stash registers");
  ExerciseByteMap(wide_stash, 8, 64, 3000, 28);
}

struct Record {
  uint64_t revision;
  std::array<uint8_t, 248> payload;
  bool operator==(const Record& other) const {
    return revision == other.revision && payload == other.payload;
  }
};

void TestTypedMap() {
  oram::TreeOptions options;
  options.position_map.deamortized_owner_threads = 0;
  oram::TreeMap<uint64_t, Record> map(500, options);
  Record first{3, {}};
  first.payload[7] = 9;
  Record second{4, {}};
  second.payload[200] = 11;

  map.insert_or_assign(7, first);
  Expect(map.contains(7), "typed contains missed");
  Expect(map.at(7) == first, "typed at returned the wrong value");
  map.insert_or_assign(7, second);
  Record actual{};
  Expect(map.find(7, &actual) && actual == second, "typed update failed");
  Expect(!map.find(99), "optional find found an absent key");
  ExpectThrows([&] { (void)map.at(99); }, "at did not throw for a missing key");
  Expect(map.erase(7), "typed erase missed");
  Expect(!map.contains(7), "typed erased key remained present");
  Expect(map.max_size() == map.capacity(), "max_size differs from capacity");
  Expect(map.capacity() >= 500, "typed capacity under-allocated");
}

void TestPayloadThreadSelection() {
  const oram::TreeOptions defaults;
  Expect(defaults.payload_max_threads == oram::kTreePayloadUncapped && defaults.payload_threshold == 32,
         "default payload policy");
  struct Case { size_t width; unsigned cap; size_t threshold; unsigned expected; };
  // Rounds up from the threshold on: no worker carries more than `threshold`
  // bytes of a slot while the cap allows.
  const Case cases[] = {{31, 4, 32, 0}, {32, 4, 32, 1}, {33, 4, 32, 2},
      {96, 4, 32, 3}, {127, 4, 32, 4}, {128, 4, 32, 4}, {256, 4, 32, 4},
      {512, 0, 32, 0}, {512, 2, 32, 2}, {63, 4, 64, 0}, {64, 4, 64, 1},
      {128, 4, 64, 2}, {192, 4, 64, 3}, {256, 4, 64, 4}, {127, 4, 128, 0},
      {129, 4, 128, 2}, {256, 5, 16, 5}};
  for (const auto& c : cases) {
    oram::TreeOptions options;
    options.payload_max_threads = c.cap;
    options.payload_threshold = c.threshold;
    options.payload_monitor_wait = c.cap == 2;
    options.position_map.deamortized_owner_threads = 0;
    oram::TreeByteMap<> map(128, 8, c.width, options);
    // A host with fewer physical cores cuts the count (the test below).
    const unsigned expected = microram::byteslice::HelpersThatFit(c.expected, 1);
    Expect(map.uses_payload_workers() == (expected != 0), "worker dispatch");
    Expect(map.payload_planes() == expected, "width-based worker count");
    Expect(map.engine().ValueBytes() == c.width &&
               map.engine().tree().PayloadPlanes() == expected,
           "the engine accessor returned the wrong engine");
    ExerciseByteMap(map, 8, c.width, 128, 97);
  }
  oram::TreeOptions invalid;
  invalid.payload_threshold = 0;
  bool rejected = false;
  try { oram::TreeByteMap<> map(128, 8, 128, invalid); }
  catch (const std::invalid_argument&) { rejected = true; }
  Expect(rejected, "zero payload threshold must be rejected");
}

// NO MORE THREADS THAN PHYSICAL CORES: the payload workers take the cores the
// caller and the position map's owner threads leave.
void TestPayloadWorkersFitThePhysicalCores() {
  const unsigned cores = microram::byteslice::HostPhysicalCores();
  for (unsigned owners : {0u, 2u}) {
    oram::TreeOptions options;
    options.payload_max_threads = 64;
    options.payload_threshold = 32;
    options.position_map.deamortized_owner_threads = owners;
    constexpr size_t width = 4096;
    oram::TreeByteMap<> map(128, 8, width, options);
    const unsigned fit = microram::byteslice::HelpersThatFit(64, 1 + owners, cores);
    Expect(map.payload_planes() <= fit && map.uses_payload_workers() == (fit != 0),
           "payload workers exceed the physical cores the caller and position map leave");
    ExerciseByteMap(map, 8, width, 128, 97);
  }
}

template <bool Deamortize>
void TestBatchOptionalOutputs() {
  for (unsigned workers : {0u, 2u}) {
    for (bool key_uid : {false, true}) {
      oram::TreeOptions options;
      options.payload_max_threads = workers;
      options.uid_from_key = key_uid;
      options.position_map.deamortized_owner_threads = 0;
      constexpr size_t width = 257;  // Includes a partial payload chunk.
      oram::TreeByteMap<Deamortize> map(128, 8, width, options);
      std::unordered_map<uint64_t, std::vector<uint8_t>> model;
      std::mt19937_64 rng(741);
      const std::vector<uint8_t> zeros(width);
      map.access_batch(0, nullptr, nullptr);
      for (unsigned round = 0; round < 24; ++round) {
        constexpr size_t n = 33;  // Cross two position-map cascade boundaries.
        std::array<uint64_t, n> keys{};
        std::array<std::vector<uint8_t>, n> inputs, outputs, expected;
        std::array<oram::BatchRequest, n> requests{};
        std::array<uint8_t, n> found{}, expected_found{};
        for (size_t i = 0; i < n; ++i) {
          keys[i] = rng() % 8;  // Repeated keys, including uid zero.
          inputs[i] = ValueFor(keys[i], round * n + i, width);
          outputs[i].assign(width, 0xa5);
          const oram::BatchOp ops[] = {oram::BatchOp::kRead,
              oram::BatchOp::kWrite, oram::BatchOp::kErase,
              oram::BatchOp::kExchange};
          const auto op = ops[rng() % 4];
          const bool insert = (rng() & 1) != 0;
          const unsigned output_kind = rng() % 3;
          uint8_t* out = output_kind == 0 ? nullptr :
              output_kind == 1 ? outputs[i].data() : inputs[i].data();
          const auto it = model.find(keys[i]);
          expected_found[i] = it != model.end();
          expected[i] = it == model.end() ? zeros : it->second;
          if (op == oram::BatchOp::kErase) model.erase(keys[i]);
          if (op == oram::BatchOp::kWrite ||
              (op == oram::BatchOp::kExchange && (insert || expected_found[i])))
            model[keys[i]] = inputs[i];
          requests[i] = {op, insert,
              reinterpret_cast<const uint8_t*>(&keys[i]), inputs[i].data(), out};
        }
        map.access_batch(n, requests.data(), round % 2 ? found.data() : nullptr);
        if (round % 2) Expect(found == expected_found, "batch membership differs");
        for (size_t i = 0; i < n; ++i)
          if (requests[i].value_out)
            Expect(std::memcmp(requests[i].value_out, expected[i].data(), width) == 0,
                   "batch old value differs");
      }
      Expect(map.access_count() == 24 * 33, "batch access count differs");
      std::vector<uint8_t> out(width);
      for (uint64_t key = 0; key < 8; ++key) {
        const bool found = map.find(reinterpret_cast<const uint8_t*>(&key), out.data());
        const auto it = model.find(key);
        Expect(found == (it != model.end()), "batch final membership differs");
        Expect(out == (it == model.end() ? zeros : it->second),
               "batch final value differs");
      }
      // Partial own-input/output overlap in both directions, with a chain
      // of updates to the same key spanning position-map cascade boundaries.
      for (bool forward : {false, true}) {
        constexpr size_t n = 17, offset = 7;
        uint64_t overlap_key = 99;
        auto previous = ValueFor(overlap_key, 1, width);
        map.insert_or_assign(reinterpret_cast<uint8_t*>(&overlap_key), previous.data());
        std::array<std::vector<uint8_t>, n> buffers, expected;
        std::array<oram::BatchRequest, n> req;
        std::array<uint8_t, n> found{};
        for (size_t i = 0; i < n; ++i) {
          buffers[i].resize(width + offset);
          uint8_t* input = buffers[i].data() + (forward ? 0 : offset);
          uint8_t* output = buffers[i].data() + (forward ? offset : 0);
          auto next = ValueFor(overlap_key, i + 2, width);
          std::memcpy(input, next.data(), width);
          expected[i] = previous;
          previous = next;
          req[i] = {oram::BatchOp::kExchange, false,
              reinterpret_cast<uint8_t*>(&overlap_key), input, output};
        }
        map.access_batch(n, req.data(), found.data());
        for (size_t i = 0; i < n; ++i)
          Expect(found[i] && std::memcmp(req[i].value_out, expected[i].data(), width) == 0,
                 "partial-overlap batch output differs");
        Expect(map.find(reinterpret_cast<uint8_t*>(&overlap_key), out.data()) && out == previous,
               "partial-overlap batch input lost");
      }
      // Validation remains per request: an earlier valid write completes.
      uint64_t key = 42;
      auto value = ValueFor(key, 1, width);
      oram::BatchRequest invalid[] = {
          {oram::BatchOp::kWrite, false, reinterpret_cast<uint8_t*>(&key), value.data(), nullptr},
          {oram::BatchOp::kExchange, true, reinterpret_cast<uint8_t*>(&key), nullptr, nullptr}};
      ExpectThrows([&] { map.access_batch(2, invalid, nullptr); },
                   "batch null input accepted");
      Expect(!map.failed(), "validation poisoned map");
      Expect(map.find(reinterpret_cast<uint8_t*>(&key), out.data()) && out == value,
             "batch lost write before invalid request");
      for (auto op : {oram::BatchOp::kRead, oram::BatchOp::kWrite,
                      oram::BatchOp::kErase, oram::BatchOp::kExchange}) {
        oram::BatchRequest bad{op, true, nullptr, value.data(), nullptr};
        ExpectThrows([&] { map.access_batch(1, &bad, nullptr); },
                     "batch null key accepted");
      }
      map.drain_tree();
    }
  }
}

void TestArgumentValidation() {
  ExpectThrows([] { oram::TreeByteMap<> map(0, 8, 8); },
               "zero capacity was accepted");
  ExpectThrows([] { oram::TreeByteMap<> map(64, 0, 8); },
               "zero key width was accepted");
  ExpectThrows([] { oram::TreeByteMap<> map(64, 8, 0); },
               "zero value width was accepted");
  ExpectThrows(
      [] {
        oram::TreeOptions options;
        options.stash_registers = 2;
        oram::TreeByteMap<> map(256, 8, 8, options);
      },
      "a two-register stash was accepted");
  ExpectThrows(
      [] {
        oram::TreeOptions options;
        options.fold = 6;
        oram::TreeByteMap<> map(256, 8, 8, options);
      },
      "fold 6 was accepted");
  ExpectThrows(
      [] {
        oram::TreeOptions options;
        options.fold = 5;
        options.stash_registers = 3;
        oram::TreeByteMap<> map(1 << 14, 8, 8, options);
      },
      "fold 5 with three stash registers was accepted");
  // Fold 0 -- the default -- is the default rule for the tree's depth:
  // 2^20 entries are 18 leaf bits and fold 3 (a root of 8 children, two path
  // buckets fewer than fold 1), and 2^19 are 17 leaf bits and fold 2
  // (cpu_tree_layout.hpp's DefaultFold).
  {
    oram::TreeOptions one;
    one.fold = 1;
    oram::TreeByteMap<> deep(size_t{1} << 20, 8, 8);
    oram::TreeByteMap<> deep_fold1(size_t{1} << 20, 8, 8, one);
    Expect(deep.path_levels() == 16 && deep.path_levels() + 2 == deep_fold1.path_levels(),
           "2^20 entries default to fold 3");
    Expect(deep.engine().tree().knobs().fold == 3 &&
               deep.engine().tree().knobs().shape.stash_registers == 3,
           "the engine's knobs do not report the fold and stash it was built with");
    oram::TreeByteMap<> shallow(size_t{1} << 19, 8, 8);
    oram::TreeByteMap<> shallow_fold1(size_t{1} << 19, 8, 8, one);
    Expect(shallow.path_levels() + 1 == shallow_fold1.path_levels(),
           "2^19 entries (17 leaf bits) default to fold 2");
    ExerciseByteMap(deep, 8, 8, 3000, 41);
  }
  // ONE SOLVE.  Just past these capacities the rule's tree is 20 leaf bits
  // at fold 5, while fold 5 with four stash registers given explicitly fits
  // 19 (the fourth register's lanes count toward the load), so the map must
  // build the geometry it solved rather than solve it again from the fold
  // and stash it chose.
  for (const auto c : {std::pair<size_t, unsigned>{2097247, 0}, {131078, 4}}) {
    oram::TreeOptions options;
    options.leaf_scale = c.second;
    oram::TreeByteMap<false> map(c.first, 8, 16, options);
    const microram::tree::TreeGeometry want =
        microram::tree::TreeGeometry::ForCapacity(c.first, 0, 16, c.second);
    const microram::tree::TreeGeometry& got = map.engine().geometry();
    Expect(want.leaf_bits == 20 && want.fold == 5 &&
               want.shape.stash_registers == 4 && want.path_buckets() == 16,
           "the rule's tree at the probe capacity moved");
    Expect(got.leaf_bits == want.leaf_bits && got.fold == want.fold &&
               got.shape.stash_registers == want.shape.stash_registers &&
               map.path_levels() == want.path_buckets(),
           "the map built a tree other than the one it solved");
    Expect(map.engine().tree().knobs().fold == 5 &&
               map.engine().tree().knobs().shape.stash_registers == 4,
           "the engine's knobs do not report the fold and stash it was built with");
    std::array<uint8_t, 8> key{5};
    std::array<uint8_t, 16> value{6}, out{};
    map.insert_or_assign(key.data(), value.data());
    Expect(map.find(key.data(), out.data()) && out == value,
           "the probe-capacity map did not round trip");
  }
  ExpectThrows(
      [] {
        // 2^35 entries need 33 path buckets at fold 1.
        oram::TreeOptions one;
        one.fold = 1;
        oram::TreeByteMap<> map(size_t{1} << 35, 8, 8, one);
      },
      "a capacity past the path-length bound was accepted");

  // The capacity floor: anything below 128 entries still builds a usable map.
  oram::TreeOptions tiny;
  tiny.position_map.deamortized_owner_threads = 0;
  oram::TreeByteMap<> small(1, 8, 8, tiny);
  Expect(small.capacity() >= oram::kTreeMinimumCapacity,
         "the capacity floor was not applied");
  std::array<uint8_t, 8> key{1}, value{2}, out{};
  small.insert_or_assign(key.data(), value.data());
  Expect(small.find(key.data(), out.data()) && out == value,
         "the floor-sized map does not work");

  oram::TreeByteMap<> map(256, 8, 8, tiny);
  std::array<uint8_t, 8> bytes{};
  ExpectThrows([&] { map.find(nullptr, bytes.data()); }, "null key accepted");
  ExpectThrows([&] { map.find(bytes.data(), nullptr); }, "null output accepted");
  ExpectThrows([&] { map.insert_or_assign(bytes.data(), nullptr); },
               "null value accepted");

  // An unknown operation is a malformed batch, rejected before remapping
  // any key, even when it follows an otherwise valid write.
  const oram::BatchRequest invalid[] = {
      {oram::BatchOp::kWrite, false, key.data(), value.data(), nullptr},
      {static_cast<oram::BatchOp>(255), false, key.data(), nullptr, nullptr}};
  std::array<uint8_t, 2> found{0xa5, 0xa5};
  ExpectThrows([&] { map.access_batch(2, invalid, found.data()); },
               "unknown batch operation accepted");
  Expect(map.access_count() == 0 && map.position_map_access_count() == 0 &&
             !map.failed() && found[0] == 0xa5 && found[1] == 0xa5,
         "invalid operation mutated the map or batch outputs");
  ExpectThrows([&] { map.access_batch(1, invalid + 1, found.data()); },
               "unknown scalar batch operation accepted");
}

}  // namespace

int main() {
  TestBatchOptionalOutputs<false>();
  TestBatchOptionalOutputs<true>();
  TestPayloadThreadSelection();
  TestPayloadWorkersFitThePhysicalCores();
  TestArgumentValidation();
  TestAliasedExchange();
  TestUidFromKey();
  TestHybrid();
  TestHybridReportsHierarchyFailure();
  TestKeyNormalizationPreflight();
  TestSetBatchLanes();
  TestTypedMap();
  TestByteMaps();
  std::puts("cpu_tree_map_test passed");
  return 0;
}
