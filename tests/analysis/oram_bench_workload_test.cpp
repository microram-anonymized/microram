// Unit test for the benchmark workload and arrival generators
// (src/oram/support/benchmark_workload.hpp, benchmark_arrival.hpp): the key
// space and its inverse, dense keys, deterministic requests and values (fixed
// reference vectors pin the generator version), misses, and fixed-rate and
// grouped arrival times.
#include "src/oram/support/benchmark_arrival.hpp"
#include "src/oram/support/benchmark_workload.hpp"

#include <algorithm>
#include <array>
#include <iostream>
#include <set>
#include <vector>

namespace {
using namespace oram_bench;
void Check(bool condition, const char* message) {
  if (!condition) throw std::runtime_error(message);
}
template<class F> void Reject(F f) {
  bool rejected = false;
  try { f(); }
  catch (const std::invalid_argument&) { rejected = true; }
  catch (const std::overflow_error&) { rejected = true; }
  Check(rejected, "invalid input accepted");
}
bool Same(const WorkloadRequest& a, const WorkloadRequest& b) {
  return a.request_id == b.request_id && a.key_id == b.key_id &&
      a.write == b.write && a.expected_hit == b.expected_hit &&
      a.value_version == b.value_version;
}

void TestKeySpace() {
  WorkloadSpec s;
  s.key_bytes = 1; s.live_entries = 200; s.miss_key_count = 56;
  s.hit_ppm = 800000; s.read_ppm = 1000000;
  WorkloadGenerator g(s);
  std::set<uint8_t> keys;
  for (unsigned i = 0; i < 256; ++i) {
    uint8_t key; g.Key(i, &key, 1); keys.insert(key);
  }
  Check(keys.size() == 256, "narrow live/miss keys collided");
  ++s.miss_key_count; Reject([&] { WorkloadGenerator bad(s); });
  s.key_bytes = 4; s.live_entries = uint64_t{1} << 32; s.miss_key_count = 1;
  Reject([&] { WorkloadGenerator bad(s); });
  s.miss_key_count = 0; s.hit_ppm = 1000000;
  WorkloadGenerator full(s);
  std::array<uint8_t, 4> a{}, b{};
  full.Key(0, a.data(), a.size());
  full.Key(s.live_entries - 1, b.data(), b.size());
  Check(a != b, "4-byte boundary keys collided");
  Reject([&] { full.Key(s.live_entries, b.data(), b.size()); });
  s.key_bytes = 32; s.live_entries = std::numeric_limits<uint64_t>::max();
  WorkloadGenerator wide(s);  // No dataset allocation, even at uint64 limits.
  std::array<uint8_t, 32> wa{}, wb{};
  wide.Key(0, wa.data(), wa.size());
  wide.Key(s.live_entries - 1, wb.data(), wb.size());
  Check(wa != wb && !std::equal(wa.begin() + 8, wa.end(), wb.begin() + 8),
        "wide key suffix did not depend on full key id");
  s.miss_key_count = 1; s.hit_ppm = 500000;
  Reject([&] { WorkloadGenerator bad(s); });
}
// KeyId inverts Key's prefix at every width (the no-op backend's lookup).
void TestKeyInverse() {
  for (size_t width : {size_t{1}, size_t{2}, size_t{3}, size_t{4}, size_t{8}, size_t{32}}) {
    WorkloadSpec s;
    s.key_bytes = width; s.seed = 7 + width;
    s.live_entries = width == 1 ? 200 : 5000; s.miss_key_count = width == 1 ? 56 : 3;
    s.hit_ppm = 500000; s.read_ppm = 1000000;
    WorkloadGenerator g(s);
    std::vector<uint8_t> key(width);
    const uint64_t count = s.live_entries + s.miss_key_count;
    for (uint64_t id = 0; id < count; ++id) {
      g.Key(id, key.data(), width);
      Check(g.KeyId(key.data()) == id, "key inverse differs from key id");
    }
    if (width >= 8) {
      s.live_entries = std::numeric_limits<uint64_t>::max() - 1; s.miss_key_count = 1;
      WorkloadGenerator wide(s);
      for (uint64_t id : {uint64_t{0}, s.live_entries - 1, s.live_entries}) {
        wide.Key(id, key.data(), width);
        Check(wide.KeyId(key.data()) == id, "wide key inverse differs from key id");
      }
    }
  }
}

// Dense keys: key i is the integer i in little-endian order at every width.
void TestDenseKeys() {
  for (size_t width : {size_t{1}, size_t{2}, size_t{4}, size_t{8}, size_t{32}}) {
    WorkloadSpec s;
    s.key_bytes = width; s.key_layout = KeyLayout::kDense; s.seed = 3 + width;
    s.live_entries = width == 1 ? 200 : 5000; s.miss_key_count = width == 1 ? 56 : 3;
    s.hit_ppm = 500000; s.read_ppm = 1000000;
    WorkloadGenerator g(s);
    std::vector<uint8_t> key(width);
    const uint64_t count = s.live_entries + s.miss_key_count;
    for (uint64_t id = 0; id < count; ++id) {
      g.Key(id, key.data(), width);
      uint64_t value = 0;
      for (size_t i = 0; i < width; ++i) {
        if (i < 8) value |= uint64_t{key[i]} << (8 * i);
        else Check(key[i] == 0, "dense key has nonzero bytes above the integer");
      }
      Check(value == id, "dense key is not the little-endian key id");
      Check(g.KeyId(key.data()) == id, "dense key inverse differs from key id");
    }
    // Miss keys are the integers N, N+1, ...: every hit key is below N.
    for (uint64_t i = 0; i < 1000; ++i) {
      const auto r = g.At(i);
      g.Key(r.key_id, key.data(), width);
      Check((g.KeyId(key.data()) < s.live_entries) == r.expected_hit, "dense miss key below the live set");
    }
    // The layout changes only the key bytes, never the request sequence or values.
    auto permuted = s; permuted.key_layout = KeyLayout::kPermuted;
    WorkloadGenerator p(permuted);
    std::vector<uint8_t> a(8), b(8), other(width);
    size_t differing = 0;
    for (uint64_t i = 0; i < 100; ++i) {
      Check(Same(g.At(i), p.At(i)), "key layout changed the request sequence");
      g.Value(i, 7, a.data(), a.size()); p.Value(i, 7, b.data(), b.size());
      Check(a == b, "key layout changed a value");
      g.Key(i, key.data(), width); p.Key(i, other.data(), width);
      differing += key != other;
    }
    Check(differing > 90, "dense and permuted keys coincide");
  }
  // Key-width capacity is the same as for permuted keys.
  WorkloadSpec s; s.key_bytes = 1; s.key_layout = KeyLayout::kDense;
  s.live_entries = 256; WorkloadGenerator full(s);
  uint8_t key = 0; full.Key(255, &key, 1); Check(key == 255, "last dense one-byte key");
  s.live_entries = 257; Reject([&] { WorkloadGenerator bad(s); });
  s.key_bytes = 4; s.live_entries = (uint64_t{1} << 32) - 1; s.miss_key_count = 1; s.hit_ppm = 500000;
  s.read_ppm = 1000000;
  WorkloadGenerator edge(s);
  std::array<uint8_t, 4> last{};
  edge.Key(s.live_entries, last.data(), last.size());
  Check(last == std::array<uint8_t, 4>{0xff, 0xff, 0xff, 0xff}, "dense miss key at 2^32 - 1");
  s.miss_key_count = 2; Reject([&] { WorkloadGenerator bad(s); });
}

void TestRequestsAndValues() {
  for (const auto widths : {std::pair<size_t, size_t>{4, 8}, {8, 48}, {32, 1024}}) {
    WorkloadSpec s; s.key_bytes = widths.first; s.value_bytes = widths.second;
    s.live_entries = 17; s.buffer_requests = 64; s.read_ppm = 500000;
    WorkloadGenerator scalar(s);
    auto bs = s; bs.buffer_requests = 16;
    WorkloadGenerator batch(bs);
    std::vector<WorkloadRequest> requests(16);
    // Small reference workload: version tracking exists only in this fixture.
    std::vector<uint64_t> versions(s.live_entries, 0);
    std::vector<std::vector<uint8_t>> values(s.live_entries,
                                           std::vector<uint8_t>(s.value_bytes));
    for (size_t key = 0; key < values.size(); ++key)
      scalar.Value(key, 0, values[key].data(), s.value_bytes);
    size_t updates = 0, reads = 0, repeated_in_batch = 0;
    for (uint64_t first = 0; first < 1000; first += requests.size()) {
      const size_t count = std::min<uint64_t>(requests.size(), 1000 - first);
      for (size_t i = 0; i < count; ++i) requests[i] = batch.At(first + i);
      std::set<uint64_t> seen;
      for (size_t i = 0; i < count; ++i) {
        const auto r = scalar.At(first + i);
        Check(Same(r, requests[i]), "API batching changed the logical request sequence");
        Check(r.key_id < s.live_entries && r.expected_hit, "update workload left live set");
        repeated_in_batch += !seen.insert(r.key_id).second;
        auto& value = values[r.key_id];
        Check(scalar.MatchesValue(r.key_id, versions[r.key_id], value.data(), value.size()),
              "reference value did not match latest in-order update");
        if (r.write) {
          ++updates;
          Check(r.value_version == r.request_id + 1, "update version not request-derived");
          scalar.Value(r.key_id, r.value_version, value.data(), value.size());
          versions[r.key_id] = r.value_version;
        } else ++reads;
      }
    }
    Check(updates && reads && repeated_in_batch, "fixture did not cover reads/writes/repeated keys");
    for (size_t key = 0; key < values.size(); ++key) {
      auto& value = values[key];
      Check(scalar.MatchesValue(key, versions[key], value.data(), value.size()), "final value mismatch");
      value.back() ^= 1;
      Check(!scalar.MatchesValue(key, versions[key], value.data(), value.size()),
            "corruption at end of full-width value was missed");
    }
    Reject([&] { batch.At(std::numeric_limits<uint64_t>::max()); });
    Check(batch.At(std::numeric_limits<uint64_t>::max() - 1).request_id ==
          std::numeric_limits<uint64_t>::max() - 1, "last valid request rejected");
    std::vector<uint8_t> key(s.key_bytes);
    Reject([&] { batch.Key(0, key.data(), key.size() - 1); });
    Reject([&] { batch.Value(0, 0, nullptr, s.value_bytes); });
  }
}

// The per-byte reference formula for values; word-wise generation must stay
// byte-identical to it, including a partial final word.
uint8_t ReferenceValueByte(uint64_t seed, uint64_t id, uint64_t version, size_t offset) {
  using workload_detail::Mix;
  const uint64_t word = Mix(Mix(seed ^ 7) ^ Mix(id) ^
      Mix(version ^ UINT64_C(0xd1b54a32d192ed03)) ^ (offset / 8));
  return static_cast<uint8_t>(word >> (8 * (offset % 8)));
}
void TestWordwiseValues() {
  for (size_t width : {size_t{1}, size_t{7}, size_t{8}, size_t{13}, size_t{48}, size_t{1024}, size_t{1029}}) {
    WorkloadSpec s; s.value_bytes = width; s.live_entries = 5; s.seed = 99;
    WorkloadGenerator g(s);
    std::vector<uint8_t> value(width);
    for (uint64_t id = 0; id < s.live_entries; ++id) {
      for (uint64_t version : {uint64_t{0}, uint64_t{1}, uint64_t{123456789}}) {
        g.Value(id, version, value.data(), width);
        for (size_t i = 0; i < width; ++i)
          Check(value[i] == ReferenceValueByte(s.seed, id, version, i),
                "word-wise value generation changed the value encoding");
        Check(g.MatchesValue(id, version, value.data(), width), "generated value did not match");
        for (size_t i : {size_t{0}, width / 2, width - 1}) {
          value[i] ^= 0x80;
          Check(!g.MatchesValue(id, version, value.data(), width), "single-byte corruption missed");
          value[i] ^= 0x80;
        }
        Check(!g.MatchesValue(id, version + 1, value.data(), width), "stale version matched");
      }
    }
  }
}

void TestMissesAndReplay() {
  WorkloadSpec s; s.live_entries = 13; s.miss_key_count = 7;
  s.hit_ppm = 500000; s.read_ppm = 1000000;
  WorkloadGenerator g(s), replay(s);
  auto other = s; ++other.seed;
  WorkloadGenerator changed(other);
  size_t hits = 0, misses = 0, differences = 0;
  for (uint64_t i = 0; i < 1000; ++i) {
    auto r = g.At(i);
    Check(Same(r, replay.At(i)), "workload replay changed");
    differences += !Same(r, changed.At(i));
    Check(!r.write && r.key_id < 20, "miss policy generated a write or invalid key");
    Check(r.expected_hit == (r.key_id < 13), "hit/miss sets overlap");
    r.expected_hit ? ++hits : ++misses;
  }
  Check(hits && misses && differences, "seed/miss fixture lacked coverage");
  s.read_ppm = 950000; Reject([&] { WorkloadGenerator bad(s); });
  s.read_ppm = 1000000; s.miss_key_count = 0;
  Reject([&] { WorkloadGenerator bad(s); });
  s.hit_ppm = 1000001; Reject([&] { WorkloadGenerator bad(s); });
  s.hit_ppm = 1000000; s.buffer_requests = 0;
  Reject([&] { WorkloadGenerator bad(s); });
}

void TestGeneratorVersion() {
  // Independently encoded counter_permutation_v1 fixtures. Changing these
  // requires a new generator identity in the campaign schema.
  WorkloadSpec s; s.live_entries = 17; s.read_ppm = 500000; s.key_bytes = 8;
  WorkloadGenerator g(s);
  const uint64_t ids[] = {14, 0, 14, 15, 11, 1, 1, 0};
  for (uint64_t i = 0; i < 8; ++i) {
    auto r = g.At(i);
    Check(r.key_id == ids[i] && r.write == (i == 2 || i == 3),
          "counter_permutation_v1 request fixture changed");
  }
  std::array<uint8_t, 8> bytes{};
  g.Key(16, bytes.data(), bytes.size());
  Check(bytes == std::array<uint8_t, 8>{0xe4,0x86,0x0a,0x60,0x08,0x85,0x9a,0x23},
        "counter_permutation_v1 key encoding changed");
  g.Value(16, 43, bytes.data(), bytes.size());
  Check(bytes == std::array<uint8_t, 8>{0x7b,0xbc,0xd9,0x10,0xd2,0x3e,0x1b,0x5d},
        "counter_permutation_v1 value encoding changed");
}

// Request k arrives at floor(k * gap), exactly: fixed reference values for
// 100 kops, so a replayed run keeps its arrivals.
void TestArrivalReplay() {
  const FixedArrivals arrivals(100);
  for (uint64_t k = 0; k < 12; ++k) Check(arrivals.At(k) == k * 10000, "fixed arrival changed");
  // Before(limit) counts the arrivals strictly before it, a half-open horizon.
  Check(arrivals.Before(0) == 0 && arrivals.Before(1) == 1 && arrivals.Before(10000) == 1 &&
        arrivals.Before(10001) == 2 && arrivals.Before(70000) == 7, "arrival count before a horizon");
  // The count is exact against the arrival times for non-integer gaps too.
  const FixedArrivals third(3);  // 333333.33... ns apart
  for (uint64_t limit : {uint64_t{1}, uint64_t{333333}, uint64_t{333334}, uint64_t{1000000}, uint64_t{999999999}}) {
    const uint64_t n = third.Before(limit);
    Check(third.At(n) >= limit && (n == 0 || third.At(n - 1) < limit), "Before disagrees with At");
  }
}

// Grouped arrivals: request k arrives with the first of its group, and a
// horizon counts whole groups.
void TestArrivalGroups() {
  const FixedArrivals groups(100, 4);  // 10 us per request, a group of 4 every 40 us
  for (uint64_t k = 0; k < 12; ++k) Check(groups.At(k) == k / 4 * 40000, "grouped arrival time");
  Check(groups.Before(0) == 0 && groups.Before(1) == 4 && groups.Before(40000) == 4 &&
        groups.Before(40001) == 8 && groups.Before(80001) == 12, "grouped arrival count before a horizon");
  const FixedArrivals third(3, 64);
  for (uint64_t limit : {uint64_t{1}, uint64_t{21333333}, uint64_t{21333334}, uint64_t{999999999}}) {
    const uint64_t n = third.Before(limit);
    Check(n % 64 == 0 && third.At(n) >= limit && (n == 0 || third.At(n - 1) < limit),
          "grouped Before disagrees with At");
  }
  const FixedArrivals single(100, 1), plain(100);
  for (uint64_t k = 0; k < 12; ++k) Check(single.At(k) == plain.At(k), "group of one changed arrivals");
  Reject([] { FixedArrivals bad(100, 0); });
}

void TestArrivalLimits() {
  for (double rate : {0.0, -1.0, std::numeric_limits<double>::infinity(),
                      std::numeric_limits<double>::quiet_NaN(),
                      std::numeric_limits<double>::denorm_min()})
    Reject([&] { FixedArrivals bad(rate); });
  const FixedArrivals slow(1e-20);
  Check(slow.At(0) == 0, "first fixed arrival not zero");
  Reject([&] { slow.At(1); });  // 1e26 ns does not fit
  const FixedArrivals precise(1e6 / 9007199254740992.0);
  Check(precise.At(1) == UINT64_C(9007199254740992) && precise.Before(UINT64_C(9007199254740993)) == 2,
        "large integer horizon rounded into an excluded valid arrival");
}
}  // namespace

int main() {
  try {
    TestKeySpace(); TestKeyInverse(); TestDenseKeys(); TestRequestsAndValues(); TestWordwiseValues(); TestMissesAndReplay();
    TestGeneratorVersion();
    TestArrivalReplay(); TestArrivalGroups(); TestArrivalLimits();
    std::cout << "portable workload/arrival tests passed (synthetic, no clocks)\n";
  } catch (const std::exception& e) {
    std::cerr << e.what() << '\n';
    return 1;
  }
}
