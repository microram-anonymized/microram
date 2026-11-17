// The public hierarchical map (include/cpu_byteslice_oram/oram.hpp): ByteMap
// and the typed Map, in both storage modes (the default deamortized arena
// engine and the synchronous ByteMap<false>), against reference std::maps.
// Beyond lookup/update/erase correctness this checks the public contracts a
// caller relies on: capacity rounding and the option knobs reaching the
// engine, argument refusals that must fire before any allocation, the
// constant-shape output contract (a miss writes zeros rather than leaving the
// buffer untouched, so no branch on the secret result sits between the
// oblivious engine and the caller), exchange and batch semantics including
// aliased buffers, and the capacity contract: capacity() bounds the LIVE set,
// and tombstones left by misses and erases never consume it.
#include <cpu_byteslice_oram/oram.hpp>
#include "tests/oram/cpu_byteslice_test_support.hpp"

#include <array>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <limits>
#include <map>
#include <algorithm>
#include <memory>
#include <mutex>
#include <string>
#include <thread>
#include <tuple>
#include <vector>
#include <stdexcept>
#include <utility>

namespace {

namespace oram = cpu_byteslice_oram;
using microram::byteslice::test_support::Expect;
using microram::byteslice::test_support::ExpectThrows;
using microram::byteslice::test_support::ExpectThrowsAs;

static_assert(oram::ByteMap<>::deamortized,
              "ByteMap must be deamortized by default");
static_assert(!oram::ByteMap<false>::deamortized,
              "ByteMap<false> must select the synchronous storage mode");
static_assert(oram::Map<uint64_t, uint64_t>::deamortized,
              "Map must be deamortized by default");
static_assert(!oram::Map<uint64_t, uint64_t, false>::deamortized,
    "Map<Key, T, false> must select the synchronous storage mode");

template <size_t N>
std::array<uint8_t, N> Bytes(uint64_t seed) {
  std::array<uint8_t, N> bytes{};
  for (size_t i = 0; i < N; ++i) {
    seed = seed * 6364136223846793005ull + 1442695040888963407ull;
    bytes[i] = static_cast<uint8_t>(seed >> 32);
  }
  return bytes;
}

template <typename ByteMap>
void ExerciseByteMap(ByteMap& map) {
  Expect(map.requested_capacity() == 100, "requested capacity changed");
  Expect(map.capacity() >= map.requested_capacity(),
         "actual capacity is smaller than requested");
  Expect(map.key_bytes() == 13, "wrong public key width");
  Expect(map.value_bytes() == 7, "wrong public value width");

  for (uint64_t i = 0; i < 160; ++i) {
    const auto key = Bytes<13>(1000 + i);
    const auto value = Bytes<7>(2000 + i);
    map.insert_or_assign(key.data(), value.data());
  }

  for (uint64_t i = 0; i < 160; ++i) {
    const auto key = Bytes<13>(1000 + i);
    const auto expected = Bytes<7>(2000 + i);
    std::array<uint8_t, 7> actual{};
    Expect(map.find(key.data(), actual.data()), "byte-map lookup missed");
    Expect(actual == expected, "byte-map lookup returned wrong bytes");
  }

  const auto key = Bytes<13>(1042);
  const auto replacement = Bytes<7>(9999);
  map.insert_or_assign(key.data(), replacement.data());
  std::array<uint8_t, 7> actual{};
  Expect(map.find(key.data(), actual.data()), "updated key disappeared");
  Expect(actual == replacement, "insert_or_assign did not replace the value");
  Expect(map.contains(key.data()), "contains missed a present key");
  Expect(map.erase(key.data()), "erase missed a present key");
  Expect(!map.find(key.data(), actual.data()), "erased key remained present");
  Expect(!map.erase(key.data()), "second erase reported a present key");

  const auto missing = Bytes<13>(500000);
  Expect(!map.contains(missing.data()), "contains found an absent key");
  Expect(map.access_count() >= 327, "map accesses were not forwarded");
}

void TestByteMaps() {
  oram::Options amortized_options;
  amortized_options.max_accesses = uint64_t{1} << 24;
  oram::ByteMap<false> amortized(100, 13, 7, amortized_options);
  Expect(amortized.geometry_choice().capacity == amortized.capacity(),
         "the synchronous map was not built at its ladder's geometry");
  ExerciseByteMap(amortized);
  amortized.drain_rebuilds();  // Unified no-op in synchronous mode.

  oram::Options deamortized_options;
  deamortized_options.deamortized_owner_threads = 0;
  deamortized_options.deamortized_online_stash_entries = 64;  // this test states the 64-entry ladder
  oram::ByteMap<> deamortized(100, 13, 7, deamortized_options);
  // Capacity is (64 s) r0 D b_1 B^(L-2).  The arena ladder's floor is L = 2
  // -- a top and one level below it -- and its top digit floor is
  // D >= B/2 + 1 = 5, over the binary digits only a certified top takes, so
  // D = B = 8.  At s = 1 the smallest geometry covering 100 entries is
  // r0 = 2, b_1 = 2, D = 8: 64 * 2 * 8 * 2 = 2048.  A caller who wants a
  // tinier map lowers `min_top_digit`.
  Expect(deamortized.capacity() == 2048,
         "deamortized capacity was not rounded to the next hierarchy");
  ExerciseByteMap(deamortized);
  deamortized.drain_rebuilds();
}

struct Record {
  uint64_t revision;
  std::array<uint8_t, 8> payload;

  bool operator==(const Record& other) const {
    return revision == other.revision && payload == other.payload;
  }
};

static_assert(std::is_trivially_copyable<Record>::value,
              "the typed-map test value must be trivially copyable");

struct NonDefaultRecord {
  NonDefaultRecord() = delete;
  explicit NonDefaultRecord(uint64_t value_in) : value(value_in) {}
  uint64_t value;
};

static_assert(std::is_trivially_copyable<NonDefaultRecord>::value,
              "the non-default test value must be trivially copyable");

template <typename Map>
void ExerciseTypedMap(Map& map) {
  Record first{3, Bytes<8>(300)};
  Record second{4, Bytes<8>(400)};

  map.insert_or_assign(7, first);
  Expect(map.contains(7), "typed contains missed");
  Expect(map.at(7) == first, "typed at returned the wrong value");

  map.insert_or_assign(7, second);
  Record actual{};
  Expect(map.find(7, &actual), "typed find missed");
  Expect(actual == second, "typed update returned the wrong value");

  const auto optional = map.find(7);
  Expect(optional && *optional == second, "optional find returned wrong value");
  Expect(!map.find(99), "optional find found an absent key");
  // A miss WRITES the output -- all-zero bytes, the byte interface's contract
  // -- rather than leaving it alone.  A wrapper that copied only on a hit
  // would put a branch on the secret result between the oblivious engine and
  // the caller.
  Record poisoned{9, Bytes<8>(900)};
  Expect(!map.find(99, &poisoned), "typed pointer find found an absent key");
  Expect(poisoned == Record{}, "typed find on a miss did not zero the output");
  ExpectThrows([&] { (void)map.at(99); }, "at did not throw for a missing key");

  Expect(map.erase(7), "typed erase missed");
  Expect(!map.contains(7), "typed erased key remained present");
  Expect(map.max_size() == map.capacity(), "max_size differs from capacity");
}

void TestTypedMaps() {
  oram::Options amortized_options;
  amortized_options.max_accesses = uint64_t{1} << 24;
  oram::Map<uint64_t, Record, false> amortized(512, amortized_options);
  ExerciseTypedMap(amortized);
  amortized.drain_rebuilds();

  oram::Map<uint64_t, NonDefaultRecord, false> non_default(
      256, amortized_options);
  non_default.insert_or_assign(8, NonDefaultRecord(88));
  NonDefaultRecord non_default_out(0);
  Expect(non_default.find(8, &non_default_out) &&
             non_default_out.value == 88,
         "pointer find rejected a non-default-constructible value");

  oram::Options deamortized_options;
  deamortized_options.deamortized_owner_threads = 0;
  oram::Map<uint64_t, Record> deamortized(512, deamortized_options);
  ExerciseTypedMap(deamortized);
  deamortized.drain_rebuilds();

  // Wrappers are movable even though the underlying engines contain mutexes
  // and worker state and are deliberately non-movable.
  oram::Map<uint64_t, Record> moved(std::move(deamortized));
  moved.insert_or_assign(11, Record{5, Bytes<8>(500)});
  Expect(moved.contains(11), "moved map is unusable");
  moved.drain_rebuilds();
}

struct InitializationRecord {
  InitializationRecord() = delete;
  explicit InitializationRecord(uint64_t v) : value(v) {}
  InitializationRecord(const InitializationRecord&) = default;
  InitializationRecord& operator=(const InitializationRecord&) = delete;
  uint64_t value;
};
static_assert(std::is_trivially_copyable_v<InitializationRecord>);

void TestTypedInitializationWithoutDefaultOrAssignment() {
  const std::array<std::pair<uint64_t, InitializationRecord>, 2> records{{
      {7, InitializationRecord(71)}, {8, InitializationRecord(81)}}};
  oram::HierarchicalMap<uint64_t, InitializationRecord, false> map(128);
  map.initialize(records.begin(), records.size());
  InitializationRecord out(0);
  Expect(map.find(7, &out) && out.value == 71,
         "typed initialization requires neither default construction nor assignment");
  Expect(map.find(8, &out) && out.value == 81,
         "typed initializer keeps each converted value alive through consumption");
}

template <bool Deamortize>
void TestInvalidBatchOperation() {
  oram::Options options;
  options.deamortized_owner_threads = 0;
  oram::ByteMap<Deamortize> map(128, 8, 8, options);
  uint64_t key = 7, value = 71;
  const auto* key_bytes = reinterpret_cast<const uint8_t*>(&key);
  const auto* value_bytes = reinterpret_cast<const uint8_t*>(&value);
  const oram::BatchRequest requests[] = {
      {oram::BatchOp::kWrite, false, key_bytes, value_bytes, nullptr},
      {static_cast<oram::BatchOp>(255), false, key_bytes, nullptr, nullptr}};
  bool rejected = false;
  try { map.access_batch(2, requests, nullptr); }
  catch (const std::invalid_argument&) { rejected = true; }
  Expect(rejected && map.access_count() == 0,
         "invalid batch operation must reject before any access");
  Expect(!map.contains(key_bytes), "invalid batch executed its valid prefix");
}

void TestArgumentValidation() {
  for (double invalid : {-1.0, std::numeric_limits<double>::infinity(),
                         std::numeric_limits<double>::quiet_NaN()}) {
    oram::Options options;
    options.deamortized_slice_target_rate = invalid;
    ExpectThrows([&] { (void)oram::ByteMap<>::plan_geometry(128, 8, 8, options); },
                 "invalid public slice rate must not silently select automatic sizing");
    options.deamortized_slice_target_rate = 0.0;
    options.deamortized_inline_work_factor = invalid;
    ExpectThrows([&] { oram::ByteMap<> map(128, 8, 8, options); },
                 "invalid public inline factor must be rejected");
  }
  // A pinned top digit above the ladder's maximum -- and in particular above
  // 2^31, which would reach an invalid shift in CeilLog2 inside the geometry
  // search unless it is refused before the engine constructor runs.
  ExpectThrows(
      [] {
        oram::Options huge_cap;
        huge_cap.deamortized_top_digit = 3000000000u;
        oram::ByteMap<> map(1000, 8, 8, huge_cap);
      },
      "a top digit cap above 2^31 was not rejected before the geometry search");
  ExpectThrows(
      [] {
        oram::Options over_cap;
        over_cap.deamortized_top_digit = 9;  // the cap is 8: a binary top
        oram::ByteMap<> map(1000, 8, 8, over_cap);
      },
      "a top digit above the ladder's maximum of 8 was accepted");
  ExpectThrows(
      [] {
        oram::Options nonbinary;
        nonbinary.deamortized_top_digit = 6;  // no certified preparation
        oram::ByteMap<> map(1000, 8, 8, nonbinary);
      },
      "a nonbinary top digit was accepted");
  ExpectThrows([] { oram::ByteMap<false> map(0, 8, 8); },
               "zero capacity was accepted");
  ExpectThrows([] { oram::ByteMap<false> map(64, 0, 8); },
               "zero key width was accepted");
  ExpectThrows([] { oram::ByteMap<> map(64, 8, 0); },
               "zero value width was accepted");
  // A value width whose stored entry wraps size_t.  Unchecked, SIZE_MAX - 8
  // would reach a wrapped allocation and a memset of the caller's width into
  // it; the checks are refusals, so these must throw on every engine and
  // never allocate.
  for (size_t width : {std::numeric_limits<size_t>::max(),
                       std::numeric_limits<size_t>::max() - 8,
                       std::numeric_limits<size_t>::max() / 64}) {
    ExpectThrows([width] { oram::ByteMap<true> map(256, 8, width); },
                 "an unrepresentable value width reached the arena engine");
    ExpectThrows([width] { oram::ByteMap<false> map(256, 8, width); },
                 "an unrepresentable value width reached the synchronous "
                 "engine");
  }
  // Each bucket fits, but the dense ring needs exactly 2^64 bytes. The
  // multiplication must be refused before the bill sees a wrapped zero.
  ExpectThrows([] {
    oram::Options options;
    options.deamortized_top_digit = 1;
    options.deamortized_prefix_flushes = 2;
    options.deamortized_dense_prefixes = (1u << 24) - 1;
    (void)oram::ByteMap<>::plan_geometry(
        1024, 8, (size_t{1} << 33) - 10, options);
  }, "an overflowing dense ring was priced as zero bytes");
  ExpectThrows(
      [] {
        oram::Options options;
        options.deamortized_branching_factor = 3;
        oram::ByteMap<false> map(64, 8, 8, options);
      },
      "unsupported branching factor was accepted");

  oram::Options options;
  options.max_accesses = uint64_t{1} << 24;
  oram::ByteMap<false> map(64, 8, 8, options);
  std::array<uint8_t, 8> bytes{};
  ExpectThrows([&] { map.find(nullptr, bytes.data()); },
               "null key was accepted");
  ExpectThrows([&] { map.find(bytes.data(), nullptr); },
               "null output was accepted");
  ExpectThrows([&] { map.insert_or_assign(bytes.data(), nullptr); },
               "null value was accepted");

  for (unsigned branching : {4u, 8u}) {
    oram::Options branching_options;
    branching_options.deamortized_branching_factor = branching;
    branching_options.max_accesses = uint64_t{1} << 24;
    oram::ByteMap<false> branching_map(1000, 8, 8,
                                       branching_options);
    Expect(branching_map.capacity() >= 1000,
           "non-binary capacity selection under-allocated");
  }

  oram::Options tiny;
  tiny.deamortized_owner_threads = 0;
  oram::ByteMap<> tiny_map(100, 8, 8, tiny);
  tiny_map.insert_or_assign(bytes.data(), bytes.data());
  Expect(tiny_map.contains(bytes.data()),
         "small deamortized map is unusable");
  tiny_map.drain_rebuilds();
}

// The deamortized branching factor, through the PUBLIC api.
//
// It has to be checked here and cannot be inferred from the engine tests: the
// engine supports B in {2, 4, 8}, but a public map that reached it through a
// capacity ladder assuming 64*2^L and a tag sized for B = 2 would build a
// binary hierarchy whatever the caller asked for, and nothing in the engine
// suite could see that.
//
// The ladder itself (its objective is bytes, over the candidates
// `geometry_choice().candidates` counts) is owned by
// cpu_byteslice_level_arena_capacity_test.  What this file checks is that
// the PUBLIC knob reaches that ladder and then the engine, and that the
// synchronous map follows the same knob.
// EVERY OPTION OUTSIDE ITS STATED RANGE IS REFUSED BY NAME, with
// std::invalid_argument and before anything is planned, by the constructor
// and by plan_geometry alike, rather than accepted or refused as a geometry
// the ladder could not find.
void TestOptionRanges() {
  using Mutate = void (*)(oram::Options&);
  struct Case {
    const char* what;
    Mutate mutate;
    bool synchronous_too;  // an arena field rather than a thread knob
  };
  const Case cases[] = {
      {"zero wait limit",
       [](oram::Options& o) { o.deamortized_wait_limit_millis = 0; }, true},
      {"unknown batch result layout",
       [](oram::Options& o) {
         o.deamortized_batch_result_layout =
             static_cast<oram::BatchResultLayout>(9);
       }, true},
      {"unknown bank_first",
       [](oram::Options& o) {
         o.deamortized_bank_first = static_cast<oram::BankFirst>(7);
       }, true},
      {"unknown value kernel",
       [](oram::Options& o) {
         o.deamortized_value_kernel = static_cast<oram::ValueKernel>(9);
       }, true},
      {"unknown batch shape",
       [](oram::Options& o) {
         o.deamortized_batch_execution =
             static_cast<oram::BatchExecutionShape>(9);
       }, true},
      {"branching factor 3",
       [](oram::Options& o) { o.deamortized_branching_factor = 3; }, true},
      {"zero dense prefixes",
       [](oram::Options& o) { o.deamortized_dense_prefixes = 0; }, true},
      {"three prefix flushes",
       [](oram::Options& o) { o.deamortized_prefix_flushes = 3; }, true},
      {"top digit above B",
       [](oram::Options& o) {
         o.deamortized_branching_factor = 4;
         o.deamortized_top_digit = 8;
       }, true},
      {"tier wider than a residual stash",
       [](oram::Options& o) { o.deamortized_tier_buckets = 9; }, true},
      {"tier of SIZE_MAX",
       [](oram::Options& o) {
         o.deamortized_tier_buckets = std::numeric_limits<size_t>::max();
       }, true},
      {"insertion unit of 3 buckets",
       [](oram::Options& o) { o.deamortized_online_stash_entries = 192; }, true},
      {"insertion unit of 5 buckets",
       [](oram::Options& o) { o.deamortized_online_stash_entries = 320; }, true},
      {"insertion unit above 2^12 buckets",
       [](oram::Options& o) {
         o.deamortized_online_stash_entries = size_t{64} << 13;
       }, true},
      {"insertion unit of 100 entries",
       [](oram::Options& o) { o.deamortized_online_stash_entries = 100; }, true},
      {"65 value workers",
       [](oram::Options& o) { o.deamortized_value_workers = 65; }, true},
      {"zero batch lanes",
       [](oram::Options& o) { o.deamortized_batch_lanes = 0; }, true},
      {"nine batch participants",
       [](oram::Options& o) {
         o.deamortized_batch_execution =
             oram::BatchExecutionShape::kParallelTiles;
         o.deamortized_batch_participants = 9;
       }, true},
      {"participants under the chunked shape",
       [](oram::Options& o) { o.deamortized_batch_participants = 2; }, true},
      {"zero rebuild lanes",
       [](oram::Options& o) { o.deamortized_rebuild_lanes = 0; }, false},
      {"65 rebuild lanes",
       [](oram::Options& o) { o.deamortized_rebuild_lanes = 65; }, false},
      {"zero park retry",
       [](oram::Options& o) { o.deamortized_park_retry_micros = 0; }, false},
      {"more owner threads than any geometry has levels",
       [](oram::Options& o) { o.deamortized_owner_threads = 1000; }, false},
  };
  for (const Case& c : cases) {
    oram::Options options;
    c.mutate(options);
    ExpectThrowsAs<std::invalid_argument>(
        [&] { (void)oram::ByteMap<true>::plan_geometry(4096, 8, 8, options); },
        c.what);
    ExpectThrowsAs<std::invalid_argument>(
        [&] { oram::ByteMap<true> map(4096, 8, 8, options); }, c.what);
    if (c.synchronous_too) {
      ExpectThrowsAs<std::invalid_argument>(
          [&] { oram::ByteMap<false> map(4096, 8, 8, options); }, c.what);
    } else {
      // The synchronous mode ignores the thread knobs.
      oram::ByteMap<false> map(4096, 8, 8, options);
    }
  }
  // Keys are at most 64 bytes on every map, and the refusal comes before
  // anything is planned.
  ExpectThrowsAs<std::invalid_argument>(
      [] { (void)oram::ByteMap<>::plan_geometry(4096, 65, 8, {}); },
      "a 65-byte key was planned");
  ExpectThrowsAs<std::invalid_argument>(
      [] { oram::TreeByteMap<> map(4096, 65, 128); },
      "a 65-byte key reached the tree");
  {
    oram::ByteMap<false> widest(256, oram::kMaxUserKeyBytes, 8);
    std::array<uint8_t, oram::kMaxUserKeyBytes> key{};
    key[63] = 1;
    const std::array<uint8_t, 8> value{1, 2, 3};
    widest.insert_or_assign(key.data(), value.data());
    std::array<uint8_t, 8> out{};
    Expect(widest.find(key.data(), out.data()) && out == value,
           "a 64-byte key does not round-trip");
  }
  // The documented domains build: every power-of-two insertion unit up to
  // 2^12 buckets (planned only at the top, which is a 2^23-entry geometry),
  // the thread knobs a budget replaces, and lanes 64.
  for (size_t buckets = 1; buckets <= (size_t{1} << 12); buckets *= 2) {
    oram::Options options;
    options.deamortized_online_stash_entries = 64 * buckets;
    (void)oram::ByteMap<true>::plan_geometry(4096, 8, 8, options);
    (void)oram::ByteMap<false>::plan_geometry(4096, 8, 8, options);
  }
  {
    oram::Options options;
    options.deamortized_rebuild_threads = 2;
    options.deamortized_owner_threads = 1000;  // replaced by the budget
    (void)oram::ByteMap<true>::plan_geometry(4096, 8, 8, options);
    options = {};
    options.deamortized_rebuild_lanes = 64;
    options.deamortized_owner_threads = 1;
    (void)oram::ByteMap<true>::plan_geometry(4096, 8, 8, options);
  }
  // A limit that depends on the geometry stays the ladder's, and its
  // refusal says which constraint left no candidate.
  for (auto [owners, tier, needle] :
       {std::tuple{30u, size_t{0}, "levels (one per owner thread)"},
        std::tuple{0u, size_t{1}, "tier_buckets pinned at 1"}}) {
    oram::Options options;
    options.deamortized_owner_threads = owners;
    options.deamortized_tier_buckets = tier;
    bool named = false;
    try {
      (void)oram::ByteMap<true>::plan_geometry(size_t{1} << 24, 8, 8, options);
    } catch (const std::length_error& e) {
      named = std::string(e.what()).find(needle) != std::string::npos;
    }
    Expect(named, "a geometry-dependent refusal does not name its constraint");
  }
}

// A map assigned to itself keeps working (the memberwise default would
// empty its scratch buffer and the next contains() would hand the engine a
// null output), and so does a typed map over it.
void TestSelfMoveAssignment() {
  oram::ByteMap<> map(4096, 8, 8);
  const auto key = Bytes<8>(1);
  const auto value = Bytes<8>(2);
  map.insert_or_assign(key.data(), value.data());
  oram::ByteMap<>& alias = map;
  map = std::move(alias);
  std::array<uint8_t, 8> out{};
  Expect(map.capacity() >= 4096, "self-move lost the engine");
  Expect(map.find(key.data(), out.data()) && out == value,
         "self-move lost a record");
  Expect(map.contains(key.data()), "contains failed after a self-move");
  oram::ByteMap<> target(4096, 8, 8);
  target = std::move(map);
  Expect(target.contains(key.data()), "move assignment lost a record");

  oram::HierarchicalMap<uint64_t, uint64_t> typed(4096);
  typed.write(7, 8);
  auto& typed_alias = typed;
  typed = std::move(typed_alias);
  uint64_t typed_out = 0;
  Expect(typed.find(7, &typed_out) && typed_out == 8 && typed.contains(7),
         "a typed map failed after a self-move");
}

void TestDeamortizedBranchingFactor() {
  for (unsigned b : {2u, 4u, 8u}) {
    for (size_t requested : {size_t{1}, size_t{100}, size_t{5000},
                             size_t{200000}}) {
      oram::Options options;
      options.deamortized_branching_factor = b;
      options.deamortized_owner_threads = 0;
      options.deamortized_online_stash_entries = 64;  // this test states the 64-entry ladder
      oram::ByteMap<> map(requested, 8, 8, options);
      Expect(map.capacity() >= requested,
             "the deamortized ladder under-allocated");
      // The knob reached the LADDER: the geometry it chose is at the caller's
      // B.  Capacity alone cannot show this: with D free in [1, 8] at every B,
      // all three ladders answer 200000 with 229376, so the geometry the map
      // reports is what carries the claim.
      Expect(map.geometry_choice().geometry.branching == b,
             "the deamortized ladder did not build at the requested B");
    }
  }

  // A power-of-two request stops being rounded up. 2^k = 2^(k mod b) *
  // B^floor(k/b) in units, so uniform B lands every power-of-two scale EXACTLY
  // at some (L, D) once D is free; with D tied to B, odd scales would
  // overshoot 1.5x at B = 4 and even ones 3x.
  //
  // The scale ceiling is about the test's own footprint. Both parities appear
  // several times inside this range, which is what the claim needs.
  for (unsigned b : {2u, 4u, 8u}) {
    for (unsigned scale = 14; scale <= 18; ++scale) {
      const size_t requested = size_t{1} << scale;
      oram::Options options;
      options.deamortized_branching_factor = b;
      options.deamortized_owner_threads = 0;
      options.deamortized_online_stash_entries = 64;  // this test states the 64-entry ladder
      oram::ByteMap<> map(requested, 8, 8, options);
      Expect(map.capacity() == requested,
             "a power-of-two capacity request was still rounded up");
    }
  }

  // The D = 1 trap, as a claim rather than a hope: storage per entry is about
  // twice as bad there as at the D the ladder is free to pick, so the ladder
  // must never take it merely because it lands exactly on the request.
  // 64*4^L is such a request at B = 4 -- D = 1 fits it to the entry -- and the
  // answer has to be the (L-1, D = 4) that holds the same entries in half the
  // bytes.
  for (unsigned l = 3; l <= 6; ++l) {
    size_t power = 1;
    for (unsigned i = 0; i < l; ++i) power *= 4;
    oram::Options options;
    options.deamortized_branching_factor = 4;
    options.deamortized_owner_threads = 0;
    options.deamortized_online_stash_entries = 64;  // this test states the 64-entry ladder
    oram::ByteMap<> map(64 * power, 8, 8, options);
    Expect(map.capacity() == 64 * power,
           "the exact-fit request was not met exactly");
    // Same capacity, so the bytes per entry are the whole difference and the
    // comparison is visible through the public accessor.
    const double bytes_per_entry = static_cast<double>(map.arena_bytes()) /
                                   static_cast<double>(map.capacity());
    oram::Options pinned = options;
    pinned.deamortized_top_digit = 1;
    oram::ByteMap<> trap(64 * power, 8, 8, pinned);
    const double trap_bytes = static_cast<double>(trap.arena_bytes()) /
                              static_cast<double>(trap.capacity());
    Expect(map.capacity() == trap.capacity(),
           "the pinned D = 1 map is not capacity-matched, so the comparison "
           "below is not about D");
    Expect(bytes_per_entry < 0.75 * trap_bytes,
           "the ladder chose the D = 1 trap for an exact-fit request");
  }

  // And the default IS 8: a map built with untouched Options must build at
  // B = 8. Stated as the geometry the map got rather than as
  // `options.deamortized_branching_factor == 8` so it is a claim about what
  // the map does, not about the struct -- and as the geometry rather than as a
  // capacity, because with D free capacity has stopped identifying B.
  for (size_t requested : {size_t{1}, size_t{100}, size_t{5000},
                           size_t{200000}}) {
    oram::Options defaulted;
    defaulted.deamortized_owner_threads = 0;
    defaulted.deamortized_online_stash_entries = 64;  // this test states the 64-entry ladder
    oram::ByteMap<> map(requested, 8, 8, defaulted);
    Expect(map.geometry_choice().geometry.branching == 8,
           "the default deamortized map is not on the B = 8 ladder");
    Expect(map.capacity() >= requested, "the default ladder under-allocated");
  }

  // B has to reach the ENGINE, not just the ladder, and the cheapest proof
  // that it did is the byte bill: a wider B is strictly cheaper per entry at
  // matched capacity, and a B that never arrived would give three identical
  // figures.
  double binary_bytes = 0.0;
  for (unsigned b : {2u, 4u, 8u}) {
    oram::Options options;
    options.deamortized_branching_factor = b;
    options.deamortized_owner_threads = 0;
    oram::ByteMap<> map(20000, 8, 8, options);
    const double bytes = static_cast<double>(map.arena_bytes()) /
                         static_cast<double>(map.capacity());
    if (b == 2) {
      binary_bytes = bytes;
    } else {
      Expect(bytes < binary_bytes,
             "a non-binary deamortized map was no cheaper per entry than the "
             "binary one, so branching_factor did not reach the engine");
    }
    // And it works end to end, over more than one (B-1)*B^L cycle so the
    // mixed-radix absorb and the fixed merge both run.
    std::array<uint8_t, 8> key{};
    std::array<uint8_t, 8> value{};
    std::array<uint8_t, 8> out{};
    const size_t keys = map.capacity() / 4;
    for (size_t pass = 0; pass < 5; ++pass) {
      for (size_t i = 0; i < keys; ++i) {
        std::memcpy(key.data(), &i, sizeof(i));
        const size_t stamp = i * 31 + pass;
        std::memcpy(value.data(), &stamp, sizeof(stamp));
        map.insert_or_assign(key.data(), value.data());
      }
      for (size_t i = 0; i < keys; ++i) {
        std::memcpy(key.data(), &i, sizeof(i));
        const size_t stamp = i * 31 + pass;
        Expect(map.find(key.data(), out.data()),
               "a key written to a base-B deamortized map went missing");
        Expect(std::memcmp(out.data(), &stamp, sizeof(stamp)) == 0,
               "a base-B deamortized map returned a stale value");
      }
    }
    map.drain_rebuilds();
  }

  ExpectThrows(
      [] {
        oram::Options options;
        options.deamortized_branching_factor = 3;
        oram::ByteMap<> map(64, 8, 8, options);
      },
      "an unsupported deamortized branching factor was accepted");
  // ONE knob configures both instantiations: the synchronous map follows a
  // non-default B as well, and the GEOMETRY is what says so.
  {
    oram::Options options;
    options.deamortized_branching_factor = 4;
    options.max_accesses = uint64_t{1} << 24;
    oram::ByteMap<false> synchronous(200000, 8, 8, options);
    Expect(synchronous.geometry_choice().geometry.branching == 4,
           "the synchronous map did not follow the branching factor");
    Expect(synchronous.capacity() >= 200000,
           "the synchronous B = 4 ladder under-allocated");
  }
}

// THE PUBLIC DEFAULT INSERTION UNIT is 64 entries.  A larger unit is a loss
// for a serial caller (see byte_map.hpp), because this engine's dense side is
// not one stash -- a cascade scans the current unit, the frozen part of the
// prefix being assembled and every complete prefix not yet replaced -- so
// every access pays for the unit's size.  Capacity follows the unit,
// and this pins the default the map really gets rather than the constant a
// caller might quote.
void TestDeamortizedDefaultFlushUnit() {
  Expect(oram::Options{}.deamortized_online_stash_entries == 64,
         "the default insertion unit is not the measured 64 entries");
  {
    oram::Options options;
    options.deamortized_owner_threads = 0;
    oram::ByteMap<> tiny(100, 8, 8, options);
    Expect(tiny.capacity() >= 100,
           "a small default map did not cover its request");
    Expect(tiny.geometry_choice().geometry.stash_buckets == 1,
           "the default unit did not reach the geometry as one 64-entry "
           "bucket");
    std::array<uint8_t, 8> key{}, value{1, 2, 3}, out{};
    tiny.insert_or_assign(key.data(), value.data());
    Expect(tiny.find(key.data(), out.data()) && out == value,
           "small default map is unusable");
    tiny.drain_rebuilds();
  }
  for (unsigned scale = 14; scale <= 18; ++scale) {
    oram::Options options;
    options.deamortized_owner_threads = 0;
    oram::ByteMap<> map(size_t{1} << scale, 8, 8, options);
    Expect(map.capacity() == size_t{1} << scale,
           "a power-of-two request was rounded up under the default unit");
  }
  // A unit that is not a whole number of 64-entry buckets is refused rather
  // than rounded, and the message names the public knob.
  for (size_t bad : {size_t{0}, size_t{63}, size_t{65}, size_t{100}}) {
    oram::Options options;
    options.deamortized_online_stash_entries = bad;
    ExpectThrows([&] { oram::ByteMap<> map(1000, 8, 8, options); },
                 "an insertion unit that is not a multiple of 64 was accepted");
  }
}

// The per-access counters a latency analysis reads.  `last_probe_tables()` is
// the cascade the access just ran: the fixed last level is occupied for the
// whole run, so every access probes at least the online stash and it, and the
// list changes length as the levels above fill and empty.  `flush_count()`
// advances once per insertion unit.  The counters existing is not the point;
// the counters MOVING is.
void TestDeamortizedAccessCounters() {
  oram::Options options;
  options.deamortized_owner_threads = 0;
  options.deamortized_branching_factor = 4;
  options.secret_seed = microram::crypto::SecretKeySeed::Fixed(0x1A7Eull);
  constexpr size_t kCapacity = size_t{1} << 12;
  oram::ByteMap<true> map(kCapacity, 8, 16, options);
  std::array<uint8_t, 8> key{};
  std::array<uint8_t, 16> value{};
  for (uint64_t i = 0; i < kCapacity; ++i) {
    const uint64_t k = 1 + i;
    std::memcpy(key.data(), &k, sizeof(k));
    value[0] = static_cast<uint8_t>(i);
    map.insert_or_assign(key.data(), value.data());
  }
  const uint64_t flushes_before = map.flush_count();
  const size_t accesses = 4 * kCapacity;
  size_t min_tables = SIZE_MAX, max_tables = 0;
  for (uint64_t i = 0; i < accesses; ++i) {
    const uint64_t k = 1 + (i * 2654435761ull) % kCapacity;
    std::memcpy(key.data(), &k, sizeof(k));
    Expect(map.find(key.data(), value.data()), "a present key was not found");
    min_tables = std::min(min_tables, map.last_probe_tables());
    max_tables = std::max(max_tables, map.last_probe_tables());
  }
  Expect(map.flush_count() - flushes_before == accesses / 64,
         "the run did not flush once per 64 accesses");
  Expect(min_tables >= 2, "an access probed nothing but the online stash");
  Expect(max_tables > min_tables, "the probe list never changed length");
}

// exchange() is one access that reads and then writes, and the position map
// of the tree ORAM is built on it (src/oram/tree/cpu_tree_position_map.hpp).
// Its contract: the old value comes back (zeros when absent), the key ends up
// holding the new value iff it was present or `insert` was set, and otherwise
// stays absent exactly as after a find().  Checked through enough operations
// to cross several rebuilds, against a plain model map.
template <size_t KeyBytes, typename ByteMap>
void ExerciseExchange(ByteMap& map) {
  std::array<uint8_t, 8> old{};
  const auto k1 = Bytes<KeyBytes>(1);
  const auto v1 = Bytes<8>(101);
  const auto v2 = Bytes<8>(102);
  const std::array<uint8_t, 8> zeros{};

  // Absent, insert = false: behaves as find().
  Expect(!map.exchange(k1.data(), v1.data(), old.data(), false),
         "exchange reported an absent key as present");
  Expect(old == zeros, "exchange of an absent key returned nonzero bytes");
  Expect(!map.find(k1.data(), old.data()),
         "exchange without insert made an absent key present");

  // Absent, insert = true: behaves as insert_or_assign().
  Expect(!map.exchange(k1.data(), v1.data(), old.data(), true),
         "inserting exchange reported an absent key as present");
  Expect(old == zeros, "inserting exchange of an absent key returned bytes");
  Expect(map.find(k1.data(), old.data()) && old == v1,
         "inserting exchange did not store the value");

  // Present: the old value comes back and the new one is stored.
  Expect(map.exchange(k1.data(), v2.data(), old.data(), false),
         "exchange missed a present key");
  Expect(old == v1, "exchange returned the wrong previous value");
  Expect(map.find(k1.data(), old.data()) && old == v2,
         "exchange did not replace the value");

  // ALIASED buffers: the proposed value and old_out are one buffer, i.e.
  // exchange as a swap.  The probe writes old_out (the found value, or zeros)
  // before the new value is consumed, so an engine that reads `value` late
  // would rewrite a present key with its own old value and insert an absent
  // one as zeros.  Present, absent without insert, absent with insert.
  std::array<uint8_t, 8> swap = v1;  // the key holds v2
  Expect(map.exchange(k1.data(), swap.data(), swap.data(), false),
         "aliased exchange missed a present key");
  Expect(swap == v2, "aliased exchange returned the wrong previous value");
  Expect(map.find(k1.data(), old.data()) && old == v1,
         "aliased exchange stored the previous value instead of the new one");
  const auto k2 = Bytes<KeyBytes>(2);
  swap = v2;
  Expect(!map.exchange(k2.data(), swap.data(), swap.data(), false),
         "aliased exchange reported an absent key as present");
  Expect(swap == zeros, "aliased exchange of an absent key returned bytes");
  Expect(!map.find(k2.data(), old.data()),
         "aliased exchange without insert made an absent key present");
  swap = v2;
  Expect(!map.exchange(k2.data(), swap.data(), swap.data(), true),
         "aliased inserting exchange reported an absent key as present");
  Expect(swap == zeros, "aliased inserting exchange returned bytes");
  Expect(map.find(k2.data(), old.data()) && old == v2,
         "aliased inserting exchange stored zeros instead of the value");
  Expect(map.erase(k2.data()), "the aliased-insert key went missing");
  Expect(map.exchange(k1.data(), v2.data(), old.data(), false) && old == v1,
         "restoring the key after the aliasing checks failed");

  // erase(key, old): the erased value, then zeros.
  Expect(map.erase(k1.data(), old.data()), "value-returning erase missed");
  Expect(old == v2, "value-returning erase returned the wrong value");
  Expect(!map.erase(k1.data(), old.data()),
         "second value-returning erase reported a present key");
  Expect(old == zeros, "erase of an absent key returned nonzero bytes");
  Expect(!map.find(k1.data(), old.data()), "erased key remained present");

  // Through several rebuilds, against a model.
  std::array<std::array<uint8_t, 8>, 40> model{};
  std::array<bool, 40> live{};
  uint64_t state = 0x5EED;
  for (unsigned step = 0; step < 1200; ++step) {
    state = state * 6364136223846793005ull + 1442695040888963407ull;
    const unsigned i = static_cast<unsigned>((state >> 33) % 40);
    const unsigned op = static_cast<unsigned>((state >> 20) % 4);
    const auto key = Bytes<KeyBytes>(700 + i);
    const auto next = Bytes<8>(state);
    if (op == 3) {
      const bool present = map.erase(key.data(), old.data());
      Expect(present == live[i], "erase disagreed with the model");
      Expect(old == (live[i] ? model[i] : zeros),
             "erase returned the wrong previous value");
      live[i] = false;
      continue;
    }
    const bool insert = op != 0;
    const bool present = map.exchange(key.data(), next.data(), old.data(),
                                      insert);
    Expect(present == live[i], "exchange disagreed with the model");
    Expect(old == (live[i] ? model[i] : zeros),
           "exchange returned the wrong previous value in the loop");
    if (present || insert) {
      model[i] = next;
      live[i] = true;
    }
  }
  for (unsigned i = 0; i < 40; ++i) {
    const auto key = Bytes<KeyBytes>(700 + i);
    Expect(map.find(key.data(), old.data()) == live[i],
           "final presence disagreed with the model");
    if (live[i]) Expect(old == model[i], "final value disagreed with the model");
  }
}

void TestExchange() {
  oram::Options amortized_options;
  amortized_options.max_accesses = uint64_t{1} << 24;
  oram::ByteMap<false> amortized(100, 8, 8, amortized_options);
  ExerciseExchange<8>(amortized);

  oram::Options deamortized_options;
  deamortized_options.deamortized_owner_threads = 0;
  oram::ByteMap<> deamortized(100, 8, 8, deamortized_options);
  ExerciseExchange<8>(deamortized);

  // And with the real worker, wide keys and an odd value width.
  oram::Options threaded;
  oram::ByteMap<> wide(100, 13, 8, threaded);
  ExerciseExchange<13>(wide);
  wide.drain_rebuilds();
}

}  // namespace

// The batch API: the byte map's
// access_batch and the packed conveniences, and the typed map's array forms,
// against a reference std::map, on both storage modes -- which share one batch
// path -- with repeated keys inside one batch and every operation mixed.
template <bool Packed = true, typename ByteMap>
void ExerciseByteMapBatch(ByteMap& map, uint64_t seed, bool combined = false) {
  constexpr size_t kKey = 13, kValue = 7;
  std::map<std::array<uint8_t, kKey>, std::array<uint8_t, kValue>> model;
  uint64_t rng = seed;
  auto next = [&rng] {
    rng = rng * 6364136223846793005ull + 1442695040888963407ull;
    return rng >> 33;
  };
  const std::array<uint8_t, kValue> zeros{};
  for (int round = 0; round < 40; ++round) {
    const size_t boundaries[] = {0, 1, 63, 64, 65, 127, 128, 129, 511, 512, 513, 1025};
    const size_t n = combined ? boundaries[round % 12] : 1 + next() % 70;
    std::vector<std::array<uint8_t, kKey>> keys(n);
    std::vector<std::array<uint8_t, kValue>> in(n), out(n);
    std::vector<oram::BatchRequest> reqs(n);
    std::vector<oram::BatchOp> ops(n);
    std::vector<bool> inserts(n);
    for (size_t i = 0; i < n; ++i) {
      // A small pool so repeats are common; distinct per call, because the
      // same map is exercised twice and the model starts empty each time.
      keys[i] = Bytes<kKey>(seed * 1000 + next() % 30);
      in[i] = Bytes<kValue>(next());
      out[i].fill(0xEE);
      ops[i] = static_cast<oram::BatchOp>(next() % 4);
      inserts[i] = (next() & 1) != 0;
      reqs[i] = oram::BatchRequest{ops[i], inserts[i], keys[i].data(),
                                   in[i].data(), out[i].data()};
    }
    std::vector<uint8_t> found(n);
    map.access_batch(n, reqs.data(), found.data());
    for (size_t i = 0; i < n; ++i) {
      auto it = model.find(keys[i]);
      const bool present = it != model.end();
      const std::array<uint8_t, kValue> before = present ? it->second : zeros;
      switch (ops[i]) {
        case oram::BatchOp::kRead:
          Expect(found[i] == present && out[i] == before, "batch read");
          break;
        case oram::BatchOp::kWrite:
          Expect(found[i] == present && out[i] == before, "batch write previous value");
          model[keys[i]] = in[i];
          break;
        case oram::BatchOp::kErase:
          Expect(found[i] == present && out[i] == before, "batch erase");
          model.erase(keys[i]);
          break;
        case oram::BatchOp::kExchange:
          Expect(found[i] == present && out[i] == before, "batch exchange");
          if (present || inserts[i]) model[keys[i]] = in[i];
          break;
      }
    }
  }
  // The packed conveniences belong to ByteMap; hybrid exposes access_batch.
  if constexpr (Packed) {
    const size_t n = combined ? 513 : 25;
    std::vector<uint8_t> keys(n * kKey), values(n * kValue), got(n * kValue);
    for (size_t i = 0; i < n; ++i) {
      const auto k = Bytes<kKey>(5000 + i);
      const auto v = Bytes<kValue>(6000 + i);
      std::memcpy(keys.data() + i * kKey, k.data(), kKey);
      std::memcpy(values.data() + i * kValue, v.data(), kValue);
    }
    map.insert_or_assign_batch(n, keys.data(), values.data());
    std::vector<uint8_t> found(n, 0);
    map.find_batch(n, keys.data(), got.data(), found.data());
    for (size_t i = 0; i < n; ++i) {
      Expect(found[i] == 1, "packed find_batch missed");
    }
    Expect(got == values, "packed find_batch returned wrong bytes");
    map.erase_batch(n, keys.data(), found.data());
    for (size_t i = 0; i < n; ++i) Expect(found[i] == 1, "packed erase_batch");
    map.find_batch(n, keys.data(), got.data(), found.data());
    for (size_t i = 0; i < n; ++i) {
      Expect(found[i] == 0, "packed find_batch after erase");
      Expect(std::memcmp(got.data() + i * kValue, zeros.data(), kValue) == 0,
             "packed find_batch after erase returned nonzero bytes");
    }
  }
  // The model's survivors are still there after a drain.
  map.drain_rebuilds();
  for (const auto& kv : model) {
    std::array<uint8_t, kValue> v{};
    Expect(map.find(kv.first.data(), v.data()) && v == kv.second,
           "batch-written key lost after drain");
  }
}

template <typename Map>
void ExerciseTypedMapBatch(Map& map, size_t n = 40, size_t combined_width = 0) {
  struct Rec {
    uint64_t a;
    uint32_t b;
  };
  (void)sizeof(Rec);
  std::vector<uint64_t> keys(n);
  std::vector<std::array<uint8_t, 24>> vals(n), got(n);
  for (size_t i = 0; i < n; ++i) {
    keys[i] = 77 + (i % 30);  // repeats inside the batch
    vals[i] = Bytes<24>(900 + i);
  }
  map.insert_or_assign_batch(n, keys.data(), vals.data());
  std::unique_ptr<bool[]> found(new bool[n]());
  map.find_batch(n, keys.data(), got.data(), found.get());
  for (size_t i = 0; i < n; ++i) {
    Expect(found[i], "typed find_batch missed");
    // The LAST write of a repeated key in the batch is the one that stands.
    size_t last = i;
    for (size_t j = 0; j < n; ++j) if (keys[j] == keys[i]) last = j;
    Expect(got[i] == vals[last], "typed find_batch returned a stale value");
  }
  map.erase_batch(n, keys.data(), found.get());
  for (size_t i = 0; i < n; ++i) {
    // A repeated key's first erase in the batch finds it; later ones do not.
    bool first = true;
    for (size_t j = 0; j < i; ++j) if (keys[j] == keys[i]) first = false;
    Expect(found[i] == first, "typed erase_batch flag");
  }
  map.find_batch(n, keys.data(), got.data(), found.get());
  for (size_t i = 0; i < n; ++i) Expect(!found[i], "typed find after erase");
  Expect(map.batch_lanes() >= 1, "batch_lanes");
  Expect(map.max_combined_batch_lanes() ==
             (combined_width ? combined_width : map.batch_lanes()),
         "typed map combined width");
  map.drain_rebuilds();
  map.find_batch(n, keys.data(), got.data(), nullptr);
  for (const auto& v : got) Expect(v == std::array<uint8_t, 24>{}, "typed tombstone lost after drain");
}

// Independent requests may still use a swap buffer WITHIN one lane. Check
// both overlap directions, misses, tombstones, and forwarding from a write
// in the same batch, including the previous-value result of write itself.
template <typename ByteMap>
void ExerciseBatchUpdateOverlap(ByteMap& map) {
  const size_t n = map.value_bytes();
  const auto key = microram::byteslice::test_support::WideKey(0xA11A5, map.key_bytes());
  const std::vector<uint8_t> zeros(n, 0), before(n, 0x31), proposed(n, 0x72);
  for (auto op : {oram::BatchOp::kWrite, oram::BatchOp::kExchange}) {
    for (int offset : {-3, 0, 3}) {
      for (unsigned initial = 0; initial < 3; ++initial) {
        for (bool insert : {false, true}) {
          map.erase(key.data());  // leave a tombstone when initial == 0
          std::vector<uint8_t> storage(n + 3, 0xEE), out(n, 0xEE), first(n);
          uint8_t* in = storage.data() + (offset < 0 ? 3 : 0);
          uint8_t* old = storage.data() + (offset > 0 ? 3 : 0);
          std::memcpy(in, proposed.data(), n);
          if (initial == 1) map.insert_or_assign(key.data(), before.data());
          std::vector<oram::BatchRequest> requests;
          if (initial == 2) {
            requests.push_back({oram::BatchOp::kWrite, false, key.data(),
                                before.data(), first.data()});
          }
          requests.push_back({op, insert, key.data(), in, old});
          requests.push_back({oram::BatchOp::kRead, false, key.data(), nullptr, out.data()});
          std::vector<uint8_t> found(requests.size(), 0xEE);
          map.access_batch(requests.size(), requests.data(), found.data());
          const size_t lane = initial == 2 ? 1 : 0;
          const bool present = initial != 0;
          const bool stored = op == oram::BatchOp::kWrite || present || insert;
          Expect(found[lane] == present, "aliased batch update previous presence");
          Expect(std::memcmp(old, present ? before.data() : zeros.data(), n) == 0,
                 "aliased batch update previous value");
          Expect(found.back() == stored && out == (stored ? proposed : zeros),
                 "later batch read did not see the aliased update");
          if (initial == 2) {
            Expect(found[0] == 0 && first == zeros, "batch write over tombstone result");
          }
          Expect(map.find(key.data(), out.data()) == stored &&
                     out == (stored ? proposed : zeros),
                 "later call did not see the aliased update");
        }
      }
    }
  }
  // True misses (no existing entry), including a one-lane inserting exchange.
  uint64_t missing_id = 0xA11A6;
  for (auto op : {oram::BatchOp::kWrite, oram::BatchOp::kExchange}) {
    for (bool insert : {false, true}) {
      const auto missing = microram::byteslice::test_support::WideKey(
          missing_id++, map.key_bytes());
      std::vector<uint8_t> swap = proposed;
      oram::BatchRequest r{op, insert, missing.data(), swap.data(), swap.data()};
      uint8_t found = 0xEE;
      map.access_batch(1, &r, &found);
      Expect(found == 0 && swap == zeros, "batch update on a true miss result");
      const bool stored = op == oram::BatchOp::kWrite || insert;
      Expect(map.find(missing.data(), swap.data()) == stored &&
                 swap == (stored ? proposed : zeros),
             "batch update on a true miss lost its input");
    }
  }
}

template <typename ByteMap>
void ExerciseWorkerClassMap(ByteMap& map) {
  for (uint64_t i = 0; i < 600; ++i) {
    const auto key = Bytes<8>(7000 + i);
    const auto value = Bytes<8>(9000 + i);
    map.insert_or_assign(key.data(), value.data());
  }
  for (uint64_t i = 0; i < 600; ++i) {
    const auto key = Bytes<8>(7000 + i);
    const auto expected = Bytes<8>(9000 + i);
    std::array<uint8_t, 8> actual{};
    Expect(map.find(key.data(), actual.data()),
           "a two-class map lost a key");
    Expect(actual == expected, "a two-class map returned wrong bytes");
  }
}

// The OWNER-THREAD options reach the engine, and a boundary that means "ask
// this host" resolves to a level rather than being passed through as a
// sentinel.  The engine-level tests own the schedule
// (cpu_byteslice_level_arena_threads_test, _placement_test); this owns the
// plumbing, which is the part a caller sees.  The arena engine divides its
// levels into `deamortized_owner_threads` contiguous groups and the near/far
// boundary only moves where that division falls, so there is no separate
// worker-class count to validate against a pool size.
void TestOwnerThreadOptions() {
  // Two owner groups with the boundary named explicitly.
  oram::Options options;
  options.deamortized_owner_threads = 2;
  options.deamortized_near_max_level = 1;
  oram::ByteMap<true> split(500, 8, 8, options);
  Expect(split.geometry_choice().resolved_near_max_level >= 1,
         "an explicit near/far boundary did not reach the geometry");
  ExerciseWorkerClassMap(split);
  // The same pool with the boundary asked of THIS HOST, which the map answers
  // once, before it plans a geometry.
  options.deamortized_near_max_level = oram::kNearMaxLevelAuto;
  oram::ByteMap<true> host_resolved(500, 8, 8, options);
  Expect(host_resolved.geometry_choice().resolved_near_max_level >= 1,
         "the automatic boundary did not resolve to a level");
  ExerciseWorkerClassMap(host_resolved);
  // `worker_thread_init` runs once ON each owner thread, with its group index,
  // before it drives anything -- the only hook a caller can PLACE a group
  // with, and the one near/far pinning depends on.  It must run on first USE,
  // not at construction: the map defers its owner start so that `initialize`
  // stays available at every thread count.
  {
    std::vector<unsigned> groups;
    std::mutex groups_mutex;
    oram::Options placed = options;
    placed.worker_thread_init = [&](unsigned group) {
      std::lock_guard<std::mutex> lock(groups_mutex);
      groups.push_back(group);
    };
    oram::ByteMap<true> pinned(500, 8, 8, placed);
    Expect(groups.empty(),
           "the owner threads started before the map was used, which would "
           "make initialize() unavailable at this thread count");
    ExerciseWorkerClassMap(pinned);
    pinned.drain_rebuilds();
    std::lock_guard<std::mutex> lock(groups_mutex);
    Expect(groups.size() == 2,
           "worker_thread_init did not run once per owner group");
    std::sort(groups.begin(), groups.end());
    Expect(groups[0] == 0 && groups[1] == 1,
           "worker_thread_init did not get each group's own index");
  }
  // And the deterministic inline executor, which is the same answers with no
  // threads at all.
  options.deamortized_owner_threads = 0;
  options.deamortized_near_max_level = 0;
  oram::ByteMap<true> inline_map(500, 8, 8, options);
  ExerciseWorkerClassMap(inline_map);
}

void TestBatchApi() {
  oram::Options options;
  options.deamortized_batch_lanes = 8;
  oram::ByteMap<true> deamortized(500, 13, 7, options);
  Expect(deamortized.batch_lanes() == 8, "deamortized_batch_lanes not applied");
  ExerciseByteMapBatch(deamortized, 0xBA7C);
  ExerciseBatchUpdateOverlap(deamortized);
  deamortized.set_batch_lanes(64);
  Expect(deamortized.batch_lanes() == 64, "set_batch_lanes");
  Expect(deamortized.max_combined_batch_lanes() == 64, "combined width setter");
  ExerciseByteMapBatch(deamortized, 0xBA7D);
  ExpectThrows([&] { deamortized.set_batch_lanes(0); }, "set_batch_lanes(0)");
  // THE CHUNKED SHAPE RUNS ON THE CALLING THREAD ALONE, and says so rather
  // than quietly ignoring a participant pool it will not use.
  options.deamortized_batch_participants = 3;
  ExpectThrows([&] { oram::ByteMap<true> bad(500, 13, 7, options); },
               "the chunked shape accepted more than one participant");
  options.deamortized_batch_participants = 1;
  // The synchronous map shares the batch path and takes the same knobs.
  oram::ByteMap<false> amortized(500, 13, 7, options);
  Expect(amortized.batch_lanes() == 8, "synchronous batch_lanes not applied");
  Expect(amortized.max_combined_batch_lanes() == 8,
         "synchronous combined width");
  ExerciseByteMapBatch(amortized, 0xBA7E);
  ExerciseBatchUpdateOverlap(amortized);
  amortized.set_batch_lanes(3);
  Expect(amortized.batch_lanes() == 3, "synchronous set_batch_lanes");
  oram::Map<uint64_t, std::array<uint8_t, 24>> typed(500, options);
  ExerciseTypedMapBatch(typed);
  oram::Map<uint64_t, std::array<uint8_t, 24>, false> typed_sync(500, options);
  ExerciseTypedMapBatch(typed_sync);
  oram::TreeByteMap<true> tree(500, 13, 7);
  ExerciseBatchUpdateOverlap(tree);
  oram::TreeByteMap<false> tree_sync(500, 13, 7);
  ExerciseBatchUpdateOverlap(tree_sync);
  options.deamortized_batch_execution = oram::BatchExecutionShape::kParallelTiles;
  for (unsigned participants : {0u, 9u, 64u}) {
    options.deamortized_batch_participants = participants;
    ExpectThrows([&] { oram::ByteMap<true> bad(500, 8, 8, options); },
                 "invalid public online participant count accepted");
  }
  {
    options.deamortized_batch_participants = 3;
    oram::ByteMap<true> parallel(500, 13, 7, options);
    Expect(parallel.batch_participant_capacity() == 3,
           "the participant pool the map was built with was lost");
    Expect(parallel.batch_participants() == 3, "the initial participant count");
    Expect(parallel.max_combined_batch_lanes() == 3 * options.deamortized_batch_lanes,
           "parallel combined width lost through adapter");
    ExerciseBatchUpdateOverlap(parallel);
  }
  // Full combined jobs, boundary tails, packed APIs and both hybrid
  // selections. The tree selection retains its documented serial batch path.
  options.deamortized_batch_participants = 8;
  options.deamortized_batch_lanes = 64;
  {
    oram::ByteMap<true> parallel(2048, 13, 7, options);
    Expect(parallel.max_combined_batch_lanes() == 512, "ByteMap full combined width");
    ExerciseByteMapBatch(parallel, 0xBC04, true);
    oram::HybridByteMap<true> hybrid(2048, 13, 7, options);
    Expect(hybrid.max_combined_batch_lanes() == 512, "hybrid lost parallel options");
    ExerciseByteMapBatch<false>(hybrid, 0xBC05, true);
  }
  for (size_t count : {size_t{511}, size_t{512}, size_t{513}, size_t{1025}}) {
    oram::Map<uint64_t, std::array<uint8_t, 24>> typed_parallel(500, options);
    ExerciseTypedMapBatch(typed_parallel, count, 512);
  }
  {
    oram::HybridOptions tree_options(options);
    tree_options.tree_value_threshold = 1;
    tree_options.tree.payload_max_threads = 0;
    // The tree selection runs batches serially and refuses a participant
    // pool, so the hierarchical half's pool has to come back down first.
    tree_options.hierarchical.deamortized_batch_participants = 1;
    oram::HybridByteMap<true> tree_parallel(2048, 13, 7, tree_options);
    Expect(tree_parallel.max_combined_batch_lanes() == 1, "tree batch width changed");
    ExerciseByteMapBatch<false>(tree_parallel, 0xBC06, true);
    oram::Map<uint64_t, std::array<uint8_t, 24>> typed_tree(500, tree_options);
    ExerciseTypedMapBatch(typed_tree, 513, 1);
  }
  // A lane width past the tile is refused rather than clamped.  (An
  // out-of-range `deamortized_batch_execution` is not refused by this engine;
  // the two shapes it implements are covered above.)
  options.deamortized_batch_execution = oram::BatchExecutionShape::kChunkedCascade;
  options.deamortized_batch_participants = 1;
  options.deamortized_batch_lanes = 65;
  ExpectThrows([&] { oram::ByteMap<true> bad(500, 8, 8, options); },
               "deamortized_batch_lanes = 65 accepted");
  // Both result layouts the engine implements are public and fixed per
  // instance, and a map built at either answers a batch the same way.
  options.deamortized_batch_lanes = 16;
  for (auto layout : {oram::BatchResultLayout::kRows,
                      oram::BatchResultLayout::kSlicedPlaceAtLane}) {
    options.deamortized_batch_result_layout = layout;
    oram::ByteMap<true> laid_out(500, 13, 7, options);
    ExerciseByteMapBatch(laid_out, 0xBC07);
  }
}


// ABSENT-KEY AND ERASE TRAFFIC IS FREE.
//
// Capacity bounds the LIVE SET, and byte_map.hpp's capacity() comment is the
// contract: what would have to fit is |live keys| plus the distinct keys
// missed or erased since the last carry into the top, and both halves of that
// second term are free.  Two of the three reasons are asserted here; the
// third -- that a tombstone for a key the map does NOT hold is dropped at the
// top's finish -- is what TestUnshadowedTombstonesRemoveTheCapacityTerm below
// measures, because it is the one whose failure mode is a thrown overflow
// rather than a wrong answer.
//
//   1. Repeats are free.  The same key missed over and over is ONE tombstone,
//      because every rebuild's dedup collapses them.
//   2. ERASING A KEY THE MAP HOLDS is free.  The top's dedup is total, so that
//      tombstone is a duplicate of a live key and takes its slot: the key
//      moves from |live| to the tombstone term and the sum does not change.
//      The axis is present vs ABSENT, not miss vs erase, and this arm runs at
//      D = 1 -- the least forgiving digit there is -- to pin it.
//
// The D = 1 cases below are deliberately included: the top-level skip is the
// fix for the zero-headroom failure, not merely a documented limitation.
void TestMissTombstonesAreBoundedByTheDropCadence() {
  // Small enough to run a few capacity cycles quickly; the contract is scale
  // free, and the D = 1 arm below fails within the first window either way.
  constexpr size_t kRequested = 4096;
  // Keys that are never written, disjoint from the live set by construction.
  constexpr uint64_t kNeverWritten = uint64_t{1} << 40;
  auto key_bytes = [](uint64_t k) {
    std::array<uint8_t, 8> out{};
    std::memcpy(out.data(), &k, sizeof(k));
    return out;
  };

  // 1. Repeats are free.  One key, missed far more times than capacity: if a
  //    repeat cost a tombstone this would exhaust any hierarchy.
  {
    oram::ByteMap<true> map(kRequested, 8, 8);
    std::array<uint8_t, 8> value{};
    const auto key = key_bytes(kNeverWritten);
    for (size_t i = 0; i < 8 * map.capacity(); ++i) {
      Expect(!map.find(key.data(), value.data()),
             "a key that was never written was found");
    }
  }

  // 2. Erasing keys the map HOLDS is free, at the least forgiving D there is.
  //    Every erase here is a duplicate of a live key, so the sum it counts
  //    against is unchanged.
  {
    oram::Options options;
    options.deamortized_top_digit = 1;
    oram::ByteMap<true> map(kRequested, 8, 8, options);
    const size_t capacity = map.capacity();
    const std::array<uint8_t, 8> value{1, 2, 3, 4, 5, 6, 7, 8};
    for (uint64_t k = 1; k <= capacity; ++k) {
      const auto key = key_bytes(k);
      map.insert_or_assign(key.data(), value.data());
    }
    for (size_t i = 0; i < 4 * capacity; ++i) {
      // Cycles the live set: a re-insert would make this a write workload, so
      // the erase of a key already erased is deliberately included -- it is a
      // repeat, not a new distinct absent key, and arm 1 says repeats are
      // free.
      const auto key = key_bytes(1 + (i % capacity));
      map.erase(key.data());
    }
  }
}


// UNSHADOWED TOMBSTONES ARE DROPPED AT THE TOP.
//
// The third reason absent-key traffic is free is the cost of ONE class of
// tombstone: the one an access inserts after probing and finding NOTHING.  It
// shadows no older copy of its key -- there is none, anywhere, and no rebuild
// invents one -- so its only job is to keep the next access to that key off
// the buckets this one really probed, and that job is complete the moment
// every nonce family live at its insertion has retired.  A carry into the top
// is exactly that event, so the carry drops it when it READS its input instead
// of routing it through the merge and clearing it at the tail
// (byte_map.hpp's capacity(); `kDropErased` in the arena engine's top
// compaction, src/oram/levelarena/DESIGN.md, "Top compaction and residuals").
//
// These arms are the contract that buys.  Without the drop, the same
// workloads overflow the top's residual stash at a few multiples of the
// nominal load, which is why every arm runs several drop cycles at full fill.
void TestUnshadowedTombstonesRemoveTheCapacityTerm() {
  constexpr size_t kRequested = 4096;
  constexpr uint64_t kNeverWritten = uint64_t{1} << 40;
  auto key_bytes = [](uint64_t k) {
    std::array<uint8_t, 8> out{};
    std::memcpy(out.data(), &k, sizeof(k));
    return out;
  };
  auto options_at = [](unsigned digit) {
    oram::Options options;
    options.deamortized_top_digit = digit;
    return options;
  };
  const std::array<uint8_t, 8> value{1, 2, 3, 4, 5, 6, 7, 8};

  // Fills the map to `fill` of its capacity with live keys 1..n.
  auto fill_map = [&](oram::ByteMap<true>& map, double fill) {
    const auto n = static_cast<uint64_t>(fill * map.capacity());
    for (uint64_t k = 1; k <= n; ++k) {
      const auto key = key_bytes(k);
      map.insert_or_assign(key.data(), value.data());
    }
    return n;
  };

  // 1. THE HEADLINE.  A COMPLETELY FULL map survives distinct absent-key
  //    traffic several drop cycles long, including the D = 1 geometry (the
  //    narrowest top), and the live set is intact afterwards.
  {
    oram::ByteMap<true> map(kRequested, 8, 8, options_at(1));
    const size_t capacity = map.capacity();
    fill_map(map, 1.0);
    std::array<uint8_t, 8> discard{};
    for (size_t i = 0; i < 4 * capacity; ++i) {
      const auto key = key_bytes(kNeverWritten + i);
      Expect(!map.find(key.data(), discard.data()),
             "a never-written key was found");
    }
    for (uint64_t k = 1; k <= capacity; k += 97) {
      const auto key = key_bytes(k);
      std::array<uint8_t, 8> got{};
      Expect(map.find(key.data(), got.data()) && got == value,
             "the unshadowed skip lost or corrupted a live key");
    }
    std::printf("  unshadowed skip: D = 1, a FULL map of %zu, %zu distinct "
                "absent reads survived\n",
                capacity, 4 * capacity);
  }

  // 2. A LADDER of top digits and fill levels, from survivable to the
  //    tightest.  With the skip on, every row survives -- including rows
  //    that throw without it.
  {
    struct Row { unsigned digit; double fill; };
    const Row rows[] = {
      {1, 0.25}, {1, 0.50}, {1, 0.75}, {1, 1.00},
        {2, 1.00}, {4, 1.00}, {8, 1.00},
    };
    for (const Row& row : rows) {
      oram::ByteMap<true> map(kRequested, 8, 8, options_at(row.digit));
      const size_t capacity = map.capacity();
      fill_map(map, row.fill);
      std::array<uint8_t, 8> discard{};
      // Four drop cycles at the least forgiving digit.  Without the skip,
      // the full D = 1 rows overflow well within these four cycles.
      for (size_t i = 0; i < 4 * capacity; ++i) {
        const auto key = key_bytes(kNeverWritten + i);
        map.find(key.data(), discard.data());
      }
    }
    std::printf("  unshadowed skip: the digit/fill ladder, %zu rows, every "
                "one survives\n", sizeof(rows) / sizeof(rows[0]));
  }

  // 3. ERASING absent keys is the same class and is free too -- a workload
  //    that overflows at a small multiple of capacity without the skip.
  //    At D = 2, for the reason arm 1 gives.
  {
    oram::ByteMap<true> map(kRequested, 8, 8, options_at(2));
    const size_t capacity = map.capacity();
    fill_map(map, 1.0);
    for (size_t i = 0; i < 4 * capacity; ++i) {
      const auto key = key_bytes(kNeverWritten + i);
      Expect(!map.erase(key.data()), "a never-written key was erased");
    }
    for (uint64_t k = 1; k <= capacity; k += 97) {
      const auto key = key_bytes(k);
      std::array<uint8_t, 8> got{};
      Expect(map.find(key.data(), got.data()) && got == value,
             "absent-key erases lost a live key");
    }
  }
}

// The arm that matters most, because the failure mode of a wrongly marked
// tombstone is a SILENT RESURRECTION and not an exception.
//
// Two shapes.  The hand-written one is the specific sequence that would break
// if the mark ever landed on a tombstone that does shadow something: a live
// entry, an erase over it, and a MISS over that -- where the miss's probe finds
// the erase tombstone, so `found` is true and the mark must NOT be set.  The
// random one is a long mixed workload against a std::map oracle, spanning
// several last-level cycles, with the knob on and off and over several seeds.
void TestUnshadowedTombstonesNeverResurrect() {
  constexpr size_t kRequested = 4096;
  auto key_bytes = [](uint64_t k) {
    std::array<uint8_t, 8> out{};
    std::memcpy(out.data(), &k, sizeof(k));
    return out;
  };

  // The hand-written shape.
  {
    oram::ByteMap<true> map(kRequested, 8, 8);
    const size_t capacity = map.capacity();
    const std::array<uint8_t, 8> value{9, 8, 7, 6, 5, 4, 3, 2};
    const auto key = key_bytes(424242);
    std::array<uint8_t, 8> got{};

    map.insert_or_assign(key.data(), value.data());
    Expect(map.erase(key.data()), "the erase did not see the live entry");
    // The MISS over the erase tombstone: its probe finds that tombstone, so
    // `found` is true and the entry it re-inserts is a SHADOWING tombstone.
    // Mark it unshadowed and the live entry below comes back at the next
    // last-level carry.
    Expect(!map.find(key.data(), got.data()),
           "an erased key read back as present");
    // Past several carries into the last level, and with the three copies of
    // the key spread over levels by the traffic in between.
    for (size_t i = 0; i < 4 * capacity; ++i) {
      const auto filler = key_bytes(uint64_t{1} << 41 | (i % (capacity / 4)));
      map.find(filler.data(), got.data());
      Expect(!map.find(key.data(), got.data()),
             "an erased key resurrected while the hierarchy rebuilt");
    }
  }

  // The oracle.
  for (uint64_t seed : {1u, 2u, 3u}) {
    {
      oram::ByteMap<true> map(kRequested, 8, 8);
      const size_t capacity = map.capacity();
      // A key universe well inside capacity, so the LIVE set never presses on
      // it and the only thing being measured is agreement.  Absent keys come
      // from a second, disjoint range.
      const uint64_t universe = capacity / 8;
      std::map<uint64_t, std::array<uint8_t, 8>> oracle;
      uint64_t state = 0x9E3779B97F4A7C15ull ^ seed;
      auto next = [&] {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        return state;
      };
      // Several last-level cycles: a drop runs every capacity/D accesses.
      for (size_t i = 0; i < 6 * capacity; ++i) {
        const uint64_t draw = next();
        const bool absent_key = (draw & 1) != 0;
        const uint64_t k = (absent_key ? (uint64_t{1} << 42) : 0) +
                           (draw >> 8) % universe;
        const auto key = key_bytes(k);
        std::array<uint8_t, 8> got{};
        switch ((draw >> 1) & 3) {
          case 0: {  // write
            const auto v = Bytes<8>(k * 31 + i);
            map.insert_or_assign(key.data(), v.data());
            oracle[k] = v;
            break;
          }
          case 1: {  // erase, of a present or an absent key
            const auto it = oracle.find(k);
            const bool want = it != oracle.end();
            Expect(map.erase(key.data()) == want,
                   "erase disagreed with the oracle");
            oracle.erase(k);
            break;
          }
          default: {  // read, of a present or an absent key
            const auto it = oracle.find(k);
            const bool found = map.find(key.data(), got.data());
            Expect(found == (it != oracle.end()),
                   "find disagreed with the oracle on presence");
            Expect(!found || got == it->second,
                   "find disagreed with the oracle on the value");
            break;
          }
        }
      }
      // And the whole live set, once more, at the end.
      for (const auto& entry : oracle) {
        const auto key = key_bytes(entry.first);
        std::array<uint8_t, 8> got{};
        Expect(map.find(key.data(), got.data()) && got == entry.second,
               "a live key did not survive the mixed workload");
      }
    }
  }
  std::printf("  no resurrection: the write/erase/miss shape and 3 oracle runs "
              "agree on every answer\n");
}


// The BATCH path's half of the same contract.  It needs its own arm because
// the condition there is not the serial one: a chunk is probed in full before
// any of its lanes inserts, so a lane's `!found` means "nothing when the chunk
// started" and an earlier lane of the same key may have written one since.
// RunBatchChunk ands in `duplicates` for exactly that, and this is the arm
// that would catch it being dropped -- in BOTH directions.
//
//   too permissive  a repeated key inside one chunk would mark a shadowing
//                   tombstone, and the value it shadows resurrects.  The
//                   oracle arm below repeats keys inside every chunk on
//                   purpose.
//   too strict      nothing is dropped, the capacity term comes back, and the
//                   D = 1 arm throws again.
void TestUnshadowedTombstonesThroughTheBatchApi() {
  constexpr size_t kRequested = 4096;
  constexpr uint64_t kNeverWritten = uint64_t{1} << 40;
  constexpr size_t kLanes = 16;
  auto key_bytes = [](uint64_t k) {
    std::array<uint8_t, 8> out{};
    std::memcpy(out.data(), &k, sizeof(k));
    return out;
  };

  // 1. The capacity term, through find_batch: D = 1 on a full map -- the
  //    narrowest top there is, and so the one with no headroom to hide a
  //    lane whose mark this path failed to set (the serial twin is
  //    TestUnshadowedTombstonesRemoveTheCapacityTerm's arm 1).
  {
    oram::Options options;
    options.deamortized_top_digit = 1;
    oram::ByteMap<true> map(kRequested, 8, 8, options);
    const size_t capacity = map.capacity();
    const std::array<uint8_t, 8> value{1, 2, 3, 4, 5, 6, 7, 8};
    for (uint64_t k = 1; k <= capacity; ++k) {
      const auto key = key_bytes(k);
      map.insert_or_assign(key.data(), value.data());
    }
    std::vector<uint8_t> keys(kLanes * 8), out(kLanes * 8);
    std::vector<uint8_t> found(kLanes);
    auto sweep = [&] {
      for (size_t i = 0; i < 4 * capacity; i += kLanes) {
        for (size_t j = 0; j < kLanes; ++j) {
          // DISTINCT within the chunk and across it, so every lane is a
          // genuine unshadowed tombstone and none is a duplicate.
          const auto key = key_bytes(kNeverWritten + i + j);
          std::memcpy(keys.data() + j * 8, key.data(), 8);
        }
        map.find_batch(kLanes, keys.data(), out.data(), found.data());
        for (size_t j = 0; j < kLanes; ++j) {
          Expect(found[j] == 0, "a never-written key was found by a batch");
        }
      }
    };
    sweep();
    for (uint64_t k = 1; k <= capacity; k += 97) {
      const auto key = key_bytes(k);
      std::array<uint8_t, 8> got{};
      Expect(map.find(key.data(), got.data()) && got == value,
             "batched miss traffic lost a live key");
    }
  }

  // 2. The direction that resurrects: keys REPEATED inside a chunk, mixed with
  //    writes and erases, against a std::map oracle.  A lane whose `!found`
  //    was taken at face value here would mark a tombstone that shadows an
  //    earlier lane's write.
  for (uint64_t seed : {11u, 12u}) {
    oram::ByteMap<true> map(kRequested, 8, 8);
    const size_t capacity = map.capacity();
    // A key universe SMALLER than one chunk, so almost every chunk repeats
    // keys and the forwarding chain is exercised on every access.
    const uint64_t universe = 8;
    std::map<uint64_t, std::array<uint8_t, 8>> oracle;
    uint64_t state = 0x9E3779B97F4A7C15ull ^ seed;
    auto next = [&] {
      state ^= state << 13; state ^= state >> 7; state ^= state << 17;
      return state;
    };
    std::vector<uint8_t> keys(kLanes * 8), values(kLanes * 8), out(kLanes * 8);
    std::vector<uint8_t> found(kLanes);
    std::vector<oram::BatchRequest> reqs(kLanes);
    for (size_t i = 0; i < 6 * capacity; i += kLanes) {
      std::vector<int> ops(kLanes);
      std::vector<uint64_t> ks(kLanes);
      for (size_t j = 0; j < kLanes; ++j) {
        const uint64_t draw = next();
        ks[j] = (draw >> 8) % universe;
        ops[j] = static_cast<int>(draw & 3);
        const auto key = key_bytes(ks[j]);
        std::memcpy(keys.data() + j * 8, key.data(), 8);
        const auto v = Bytes<8>(ks[j] * 31 + i + j);
        std::memcpy(values.data() + j * 8, v.data(), 8);
        oram::BatchOp op = ops[j] == 0   ? oram::BatchOp::kWrite
                           : ops[j] == 1 ? oram::BatchOp::kErase
                                         : oram::BatchOp::kRead;
        reqs[j] = oram::BatchRequest{op, false, keys.data() + j * 8,
                                     values.data() + j * 8,
                                     out.data() + j * 8};
      }
      map.access_batch(kLanes, reqs.data(), found.data());
      // The oracle, in lane order: that is the batch API's own contract.
      for (size_t j = 0; j < kLanes; ++j) {
        const auto it = oracle.find(ks[j]);
        const bool want = it != oracle.end();
        Expect((found[j] != 0) == want,
               "a batched lane disagreed with the oracle on presence");
        if (want) {
          std::array<uint8_t, 8> got{};
          std::memcpy(got.data(), out.data() + j * 8, 8);
          Expect(got == it->second,
                 "a batched lane disagreed with the oracle on the value");
        }
        if (ops[j] == 0) {
          std::array<uint8_t, 8> v{};
          std::memcpy(v.data(), values.data() + j * 8, 8);
          oracle[ks[j]] = v;
        } else if (ops[j] == 1) {
          oracle.erase(ks[j]);
        }
      }
    }
  }
  std::printf("  the batch path: D = 1 survives batched absent-key traffic, "
              "and repeated keys inside a chunk agree with the oracle\n");
}

// BATCHES LONGER THAN ONE STAGING RUN (detail::BatchStagingRequests, 4096
// requests).  The adapters hand a long
// batch over a bounded run of whole engine jobs at a time instead of staging
// all of it, so each run's found flags and outputs must land at their own
// offset and the answers must be the unstaged ones: request order, earlier
// runs' effects visible to later ones.  Through the packed byte form and the
// typed one, each on a length that is not a multiple of the run.
void TestLongBatchesAreStagedInRuns() {
  constexpr size_t n = 3 * 4096 + 77;
  {
    oram::ByteMap<true> map(4 * n, 8, 8);
    std::vector<uint8_t> keys(n * 8), values(n * 8), out(n * 8);
    std::vector<uint8_t> found(n, 0xEE);
    // Every key at least twice, the repeats more than a run apart; the last
    // write of each is what every later read must see.
    const size_t distinct = n / 2;
    std::vector<size_t> last(distinct, 0);
    for (size_t i = 0; i < n; ++i) {
      const uint64_t k = i % distinct;
      std::memcpy(keys.data() + i * 8, &k, 8);
      const auto v = Bytes<8>(i);
      std::memcpy(values.data() + i * 8, v.data(), 8);
      last[k] = i;
    }
    map.insert_or_assign_batch(n, keys.data(), values.data());
    map.find_batch(n, keys.data(), out.data(), found.data());
    for (size_t i = 0; i < n; ++i) {
      Expect(found[i] == 1 &&
                 std::memcmp(out.data() + i * 8,
                             Bytes<8>(last[i % distinct]).data(), 8) == 0,
             "a long packed batch lost an answer across its staging runs");
    }
    map.erase_batch(n, keys.data(), found.data());
    for (size_t i = 0; i < n; ++i) {
      // Only each key's first erase finds it present.
      Expect(found[i] == (i < distinct ? 1 : 0),
             "a long erase batch put a found flag at the wrong offset");
    }
  }
  {
    oram::Map<uint64_t, uint64_t> typed(4 * n);
    std::vector<uint64_t> keys(n), values(n), out(n, 0);
    std::unique_ptr<bool[]> found(new bool[n]);
    for (size_t i = 0; i < n; ++i) {
      keys[i] = 1000 + i;
      values[i] = 7 * i + 3;
    }
    typed.insert_or_assign_batch(n, keys.data(), values.data());
    typed.find_batch(n, keys.data(), out.data(), found.get());
    for (size_t i = 0; i < n; ++i) {
      Expect(found[i] && out[i] == values[i],
             "a long typed batch lost an answer across its staging runs");
    }
    // Half present, half absent, interleaved, so a flag at the wrong offset
    // is wrong somewhere.
    for (size_t i = 0; i < n; ++i) keys[i] = 1000 + (i % 2 == 0 ? i : n + i);
    typed.erase_batch(n, keys.data(), found.get());
    for (size_t i = 0; i < n; ++i) {
      Expect(found[i] == (i % 2 == 0),
             "a long typed erase batch put a found flag at the wrong offset");
    }
  }
  std::printf("  batches longer than a staging run: packed and typed agree\n");
}

// Bulk initialization's two public promises, at the default owner count: an EMPTY input is
// a no-op -- it starts no owner, so a real initialization may still follow --
// and after one the online counters start from zero, although the engine
// seeds its own position to the synthetic run the load stands for.
void TestInitializationLeavesTheCountersAtZero() {
  struct Records {
    uint64_t key = 0;
    std::array<uint8_t, 8> value{};
    oram::InitializationEntry operator*() {
      value = Bytes<8>(key);
      return {reinterpret_cast<const uint8_t*>(&key), value.data()};
    }
    Records& operator++() {
      ++key;
      return *this;
    }
  };
  std::vector<unsigned> groups;
  std::mutex groups_mutex;
  oram::Options options;
  options.deamortized_owner_threads = 2;
  options.worker_thread_init = [&](unsigned group) {
    std::lock_guard<std::mutex> lock(groups_mutex);
    groups.push_back(group);
  };
  oram::ByteMap<true> map(1024, 8, 8, options);
  map.initialize(Records{}, 0);
  {
    std::lock_guard<std::mutex> lock(groups_mutex);
    Expect(groups.empty(), "an empty initialization started the owners");
  }
  const size_t n = map.capacity() / 2;
  map.initialize(Records{}, n);  // must not throw: no owner has started
  Expect(map.access_count() == 0 && map.flush_count() == 0,
         "an initialization counted as online accesses or flushes");
  std::array<uint8_t, 8> got{};
  const uint64_t key = n - 1;
  Expect(map.find(reinterpret_cast<const uint8_t*>(&key), got.data()) &&
             got == Bytes<8>(key),
         "an initialized record did not read back");
  Expect(map.access_count() == 1, "one find after an initialization is not "
                                  "one online access");
  for (uint64_t k = 0; k < 999; ++k) {
    map.find(reinterpret_cast<const uint8_t*>(&k), got.data());
  }
  Expect(map.access_count() == 1000, "the online access count drifted");
  Expect(map.flush_count() == 1000 / 64,
         "the online flush count does not follow the online accesses");
  map.drain_rebuilds();
}

// VALUE WORKERS NEED A DENSE PREFIX THEIR PROGRESS WORD CAN NAME: at most
// 4096 buckets, prefix_flushes * online_stash_entries / 64.  A longer one is
// refused at construction, not by every probe that later meets such a run.
template <bool Deamortize>
void TestValueWorkersRefuseLongDensePrefixes() {
  oram::Options options;
  options.deamortized_online_stash_entries = 64 * 1024;
  options.deamortized_prefix_flushes = 8;  // 8192 buckets
  options.deamortized_value_workers = 2;
  ExpectThrowsAs<std::invalid_argument>([&] {
    oram::ByteMap<Deamortize> map(size_t{1} << 22, 8, 16, options);
  }, "value workers accepted a dense prefix of more than 4096 buckets");
  options.deamortized_prefix_flushes = 4;  // 4096 buckets: the largest run
  oram::ByteMap<Deamortize> map(size_t{1} << 22, 8, 16, options);
  Expect(map.engine().ValueWorkers() == 2,
         "a 4096-bucket dense prefix lost its value workers");
}

// A FAILED DIRECT INITIALIZATION LEAVES NO LANE TO CLAIM.  Owner threads,
// top helpers and lanes, so the top's route runs through the shared-lane
// executor on the requester; repeated keys (outside the kDistinct promise)
// make a laned stage of that route overflow part-way.  The cancelled job
// must not hand the rest of that stage's lanes to a helper started later.
// Release builds only: a checked build asserts on the repeated keys first.
void TestFailedInitializationClosesItsLanes() {
#ifdef NDEBUG
  struct Repeating {
    uint64_t index = 0;
    uint64_t count = 0;
    uint64_t key = 0;
    std::array<uint8_t, 8> value{};
    oram::InitializationEntry operator*() {
      // Each half of the input holds its key set three times over, and both
      // halves hold the same keys.
      const uint64_t half = count / 2;
      key = (index % half) % (half / 3) + 1;
      value = Bytes<8>(key);
      return {reinterpret_cast<const uint8_t*>(&key), value.data()};
    }
    Repeating& operator++() {
      ++index;
      return *this;
    }
  };
  oram::Options options;
  options.deamortized_owner_threads = 1;
  options.deamortized_top_helpers = 2;
  options.deamortized_rebuild_lanes = 4;
  options.deamortized_lane_min_buckets = 1;
  options.deamortized_preroute = false;
  options.secret_seed = microram::crypto::SecretKeySeed::Fixed(2);
  oram::ByteMap<true> map(65536, 8, 8, options);
  auto& engine = map.engine();
  auto& job = const_cast<microram::byteslice::levelarena::LevelMergeJob&>(
      engine.level(engine.geometry().Levels()).job());
  Repeating records;
  records.count = map.capacity();
  ExpectThrows([&] { map.initialize(records, map.capacity()); },
               "the repeated-key initialization did not overflow a lane");
  Expect(!job.bound(), "the failed initialization left its top job bound");
  Expect(!job.HelpOnce(), "a failed initialization left lanes to claim");
  // The map stays usable: its first access starts the owners and helpers.
  const uint64_t key = 7;
  const std::array<uint8_t, 8> value = Bytes<8>(key);
  std::array<uint8_t, 8> got{};
  map.insert_or_assign(reinterpret_cast<const uint8_t*>(&key), value.data());
  Expect(map.find(reinterpret_cast<const uint8_t*>(&key), got.data()) &&
             got == value,
         "the map did not work after a failed initialization");
  map.drain_rebuilds();
  Expect(!map.failed(), "a failed initialization failed the map later");
#endif
}

// A DRAIN ON AN UNTOUCHED MAP HAS NOTHING TO DO, and leaves the map
// untouched: no owner started and no speculative rebuild begun, so that
// initialize() is still legal -- with and without owner threads, and through
// the typed adapter's finish_pending_work().  After an initialization the
// drain runs as it always does.
void TestDrainBeforeInitialization() {
  struct Records {
    uint64_t key = 0;
    std::array<uint8_t, 8> value{};
    oram::InitializationEntry operator*() {
      value = Bytes<8>(key);
      return {reinterpret_cast<const uint8_t*>(&key), value.data()};
    }
    Records& operator++() {
      ++key;
      return *this;
    }
  };
  for (const unsigned owners : {2u, 0u}) {
    oram::Options options;
    options.deamortized_owner_threads = owners;
    oram::ByteMap<true> map(1024, 8, 8, options);
    map.drain_rebuilds();
    map.finish_pending_work();
    Expect(map.access_count() == 0 && !map.failed(),
           "a drain on an untouched map changed it");
    const size_t n = map.capacity() / 2;
    bool initialized = true;
    try {
      map.initialize(Records{}, n);
    } catch (const std::exception&) {
      initialized = false;
    }
    Expect(initialized, "a drain on an untouched map made initialize() "
                        "refuse");
    map.finish_pending_work();
    std::array<uint8_t, 8> got{};
    const uint64_t key = n - 1;
    Expect(map.find(reinterpret_cast<const uint8_t*>(&key), got.data()) &&
               got == Bytes<8>(key),
           "an initialization after a drain did not read back");
  }
  oram::HierarchicalMap<uint64_t, uint64_t> typed(4096);
  typed.finish_pending_work();
  const std::array<std::pair<uint64_t, uint64_t>, 2> records{
      {{1, 10}, {2, 20}}};
  bool initialized = true;
  try {
    typed.initialize(records.begin(), records.size());
  } catch (const std::exception&) {
    initialized = false;
  }
  uint64_t out = 0;
  Expect(initialized && typed.find(2, &out) && out == 20,
         "finish_pending_work() on an untouched typed map made initialize() "
         "refuse");
}

// A SMALL WAIT LIMIT DOES NOT BOUND THREAD START.  Each pool's start waits
// for every init hook, and a thread still inside one can be neither joined
// nor released, so that wait ends the process on expiry; it is never shorter
// than 120 s, whatever the limit.  Here every hook takes 50 ms against a
// 5 ms limit: owners (started by the first access), batch participants and
// value workers (started by the constructor).
void TestSmallWaitLimitDoesNotEndThreadStart() {
  oram::Options options;
  options.deamortized_wait_limit_millis = 5;
  const auto slow = [](unsigned) {
    std::this_thread::sleep_for(std::chrono::milliseconds(50));
  };
  options.worker_thread_init = slow;
  options.deamortized_batch_execution =
      oram::BatchExecutionShape::kParallelTiles;
  options.deamortized_batch_participants = 2;
  options.deamortized_batch_thread_init = slow;
  options.deamortized_value_workers = 1;
  options.deamortized_value_thread_init = slow;
  oram::ByteMap<true> map(4096, 8, 8, options);
  const uint64_t key = 3;
  const auto value = Bytes<8>(key);
  map.insert_or_assign(reinterpret_cast<const uint8_t*>(&key), value.data());
  std::array<uint8_t, 8> got{};
  Expect(map.find(reinterpret_cast<const uint8_t*>(&key), got.data()) &&
             got == value,
         "a map whose hooks outlast its wait limit did not answer");
}

// A LIVE SET OF capacity() FITS WHATEVER TOMBSTONES ITS HISTORY LEFT, at the
// narrowest top there is. Every arm fills the map to capacity() (one fewer for the
// short-lived arm, whose insert uses that last slot) and runs a history whose
// live set never exceeds it but whose tombstones would, if each took a slot
// while the top compacts:
//
//   churn        erase half the keys and write as many new ones: each
//                tombstone meets its key's copy in the top (if tombstones
//                took slots, this would overflow at 1.5x the nominal load)
//   short-lived  write a new key and erase it at once, a capacity's worth of
//                times: each tombstone reaches the top with its only older
//                copy already resolved below it, and a top compaction's whole
//                input window is such pairs
//   miss pairs   read each of half a capacity of absent keys twice: the second
//                read finds the first one's tombstone
//   erase pairs  the same pattern through erase
//
// Twice over, so the second round's compactions meet the first round's
// tombstones, and serially as well as through the batch API, where the pairs
// share a chunk (and in round two, one pair in eight straddles two).  Every
// answer is checked against an oracle as it is given, and the whole key space
// once more at the end.
//
// D = 1 runs at 65536 because that is where a tombstone-capacity bug would
// show: the overflow is a per-bucket tail event, and a 4096-entry top has too
// few buckets at load 0.75 to exhaust its stash.  With tombstones taking
// slots, all four shapes throw there (short-lived only for some seeds with a
// single pass, which is why this shape runs two).
// D = 4 at 4096 is for the answers, on a top with a radix.
void TestTombstonesTakeNoTopCapacity() {
  constexpr size_t kLanes = 16;
  auto key_bytes = [](uint64_t k) {
    std::array<uint8_t, 8> out{};
    std::memcpy(out.data(), &k, sizeof(k));
    return out;
  };
  enum Shape { kChurn, kShortLived, kMissPairs, kErasePairs, kShapes };
  const char* const names[kShapes] = {"churn", "short-lived", "miss pairs",
                                      "erase pairs"};
  size_t runs = 0;
  auto check = [](bool condition, const std::string& message) {
    Expect(condition, message.c_str());
  };
  for (unsigned digit : {1u, 4u}) {
    for (int shape = 0; shape < kShapes; ++shape) {
      for (bool batched : {false, true}) {
        for (uint64_t seed : {1u, 2u}) {
          oram::Options options;
          options.deamortized_top_digit = digit;
          options.secret_seed = microram::crypto::SecretKeySeed::Fixed(seed);
          oram::ByteMap<true> map(digit == 1 ? 65536 : 4096, 8, 8, options);
          const size_t capacity = map.capacity();
          const std::string what = std::string(names[shape]) +
                                   (batched ? ", batched" : "") + ", D=" +
                                   std::to_string(digit);
          std::map<uint64_t, std::array<uint8_t, 8>> oracle;
          std::vector<uint64_t> touched;

          // One request at a time, or queued and issued as batches of
          // kLanes; either way the oracle answers in request order.
          struct Pending {
            oram::BatchOp op;
            uint64_t key;
            std::array<uint8_t, 8> value;
          };
          std::vector<Pending> queue;
          auto run = [&](const std::vector<Pending>& ops) {
            std::vector<std::array<uint8_t, 8>> keys(ops.size()),
                values(ops.size()), out(ops.size());
            std::vector<oram::BatchRequest> reqs(ops.size());
            std::vector<uint8_t> found(ops.size());
            for (size_t j = 0; j < ops.size(); ++j) {
              keys[j] = key_bytes(ops[j].key);
              values[j] = ops[j].value;
              reqs[j] = oram::BatchRequest{ops[j].op, false, keys[j].data(),
                                           values[j].data(), out[j].data()};
            }
            if (batched) {
              map.access_batch(ops.size(), reqs.data(), found.data());
            } else {
              for (size_t j = 0; j < ops.size(); ++j) {
                switch (ops[j].op) {
                  case oram::BatchOp::kWrite:
                    map.insert_or_assign(keys[j].data(), values[j].data());
                    found[j] = 0;
                    break;
                  case oram::BatchOp::kErase:
                    found[j] = map.erase(keys[j].data());
                    break;
                  default:
                    found[j] = map.find(keys[j].data(), out[j].data());
                    break;
                }
              }
            }
            for (size_t j = 0; j < ops.size(); ++j) {
              const auto it = oracle.find(ops[j].key);
              const bool want = it != oracle.end();
              if (ops[j].op != oram::BatchOp::kWrite || batched) {
                check((found[j] != 0) == want,
                       what + ": an answer disagreed with the oracle on "
                              "presence");
              }
              if (ops[j].op == oram::BatchOp::kRead && want) {
                check(out[j] == it->second,
                       what + ": a read disagreed with the oracle on the "
                              "value");
              }
              if (ops[j].op == oram::BatchOp::kWrite) {
                oracle[ops[j].key] = ops[j].value;
              } else if (ops[j].op == oram::BatchOp::kErase) {
                oracle.erase(ops[j].key);
              }
              check(oracle.size() <= capacity,
                     what + ": an intermediate live set exceeded capacity()");
            }
          };
          auto push = [&](oram::BatchOp op, uint64_t key) {
            queue.push_back({op, key, Bytes<8>(key * 7 + queue.size())});
            touched.push_back(key);
            if (queue.size() == kLanes) {
              run(queue);
              queue.clear();
            }
          };
          auto flush = [&] {
            if (!queue.empty()) run(queue);
            queue.clear();
          };

          const size_t initial = capacity - (shape == kShortLived ? 1 : 0);
          for (uint64_t k = 1; k <= initial; ++k) {
            push(oram::BatchOp::kWrite, k);
          }
          flush();
          uint64_t fresh = uint64_t{1} << 40;
          for (int round = 0; round < 2; ++round) {
            const size_t half = capacity / 2;
            switch (shape) {
              case kChurn: {
                std::vector<uint64_t> victims;
                for (const auto& entry : oracle) {
                  if (victims.size() == half) break;
                  victims.push_back(entry.first);
                }
                for (uint64_t k : victims) push(oram::BatchOp::kErase, k);
                for (size_t i = 0; i < half; ++i) {
                  push(oram::BatchOp::kWrite, fresh++);
                }
                break;
              }
              case kShortLived:
                for (size_t i = 0; i < capacity; ++i, ++fresh) {
                  push(oram::BatchOp::kWrite, fresh);
                  push(oram::BatchOp::kErase, fresh);
                }
                break;
              case kMissPairs:
              case kErasePairs: {
                const oram::BatchOp op = shape == kMissPairs
                                             ? oram::BatchOp::kRead
                                             : oram::BatchOp::kErase;
                // Round 1 starts one request late, so that one pair in eight
                // straddles two chunks instead of sharing one.
                if (round == 1) push(op, fresh++);
                for (size_t i = 0; i < half; ++i, ++fresh) {
                  push(op, fresh);
                  push(op, fresh);
                }
                break;
              }
            }
            flush();
          }
          map.drain_rebuilds();
          // The whole key space the history touched, once more.
          std::sort(touched.begin(), touched.end());
          touched.erase(std::unique(touched.begin(), touched.end()),
                        touched.end());
          size_t lost = 0, resurrected = 0;
          for (uint64_t k : touched) {
            const auto key = key_bytes(k);
            std::array<uint8_t, 8> got{};
            const bool found = map.find(key.data(), got.data());
            const auto it = oracle.find(k);
            if (it == oracle.end()) {
              resurrected += found ? 1 : 0;
            } else {
              lost += (!found || got != it->second) ? 1 : 0;
            }
          }
          check(lost == 0, what + ": live keys were lost or changed");
          check(resurrected == 0, what + ": erased or absent keys came back");
          check(oracle.size() <= capacity,
                 what + ": the history's live set exceeded capacity(), so it "
                        "tests nothing");
          ++runs;
        }
      }
    }
  }
  std::printf("  full-capacity tombstone histories: %zu runs (4 shapes, "
              "serial and batched, D = 1 at 65536 and D = 4 at 4096) fit and "
              "agree with the oracle\n",
              runs);
}

int main() {
  TestByteMaps();
  TestOwnerThreadOptions();
  TestBatchApi();
  TestTypedMaps();
  TestTypedInitializationWithoutDefaultOrAssignment();
  TestInvalidBatchOperation<false>();
  TestInvalidBatchOperation<true>();
  TestArgumentValidation();
  TestOptionRanges();
  TestSelfMoveAssignment();
  TestDeamortizedBranchingFactor();
  TestDeamortizedDefaultFlushUnit();
  TestDeamortizedAccessCounters();
  TestMissTombstonesAreBoundedByTheDropCadence();
  TestUnshadowedTombstonesRemoveTheCapacityTerm();
  TestUnshadowedTombstonesNeverResurrect();
  TestUnshadowedTombstonesThroughTheBatchApi();
  TestTombstonesTakeNoTopCapacity();
  TestInitializationLeavesTheCountersAtZero();
  TestFailedInitializationClosesItsLanes();
  TestValueWorkersRefuseLongDensePrefixes<true>();
  TestValueWorkersRefuseLongDensePrefixes<false>();
  TestDrainBeforeInitialization();
  TestSmallWaitLimitDoesNotEndThreadStart();
  TestLongBatchesAreStagedInRuns();
  TestExchange();
  std::printf("cpu_byteslice_oram_map_test passed\n");
  return 0;
}
