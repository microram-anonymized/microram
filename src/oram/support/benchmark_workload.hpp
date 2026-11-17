#pragma once

// Portable synthetic public workload, counter_permutation_v1. No clocks,
// engine dependency, dataset-sized allocation, or standard-library distributions.
// Every request, key and value is a pure function of (seed, request or key ID),
// so any backend, any host and the offline verifier regenerate the identical
// sequence and can check returned values exactly without storing the dataset.
#include <cstddef>
#include <cstdint>
#include <limits>
#include <numeric>
#include <stdexcept>

namespace oram_bench {

namespace workload_detail {
inline uint64_t Mix(uint64_t x) {
  x = (x ^ (x >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
  x = (x ^ (x >> 27)) * UINT64_C(0x94d049bb133111eb);
  return x ^ (x >> 31);
}
inline void Require(bool condition, const char* message) {
  if (!condition) throw std::invalid_argument(message);
}

// Domain-separated counter stream. Unsigned wrap is intentional, including
// the odd stride, which visits every uint64 value before repeating.
class Random {
 public:
  Random(uint64_t seed, uint64_t request, uint64_t domain)
      : state_(Mix(seed ^ domain) + request * UINT64_C(0x9e3779b97f4a7c15)) {}
  uint64_t Next() {
    state_ += UINT64_C(0x9e3779b97f4a7c15);
    return Mix(state_);
  }
  uint64_t Below(uint64_t bound) {
    const uint64_t threshold = (uint64_t{0} - bound) % bound;
    uint64_t value;
    do { value = Next(); } while (value < threshold);
    return value % bound;
  }
 private:
  uint64_t state_;
};
}  // namespace workload_detail

// How key IDs become key bytes. `permuted` spreads the IDs over the key space;
// `dense` makes key i the integer i in little-endian order, so an index ORAM
// baseline receives the same key bytes as every other backend and its adapter
// can read the key's value as its index.
enum class KeyLayout : uint8_t { kPermuted, kDense };

struct WorkloadSpec {
  uint64_t live_entries = 1;
  uint64_t miss_key_count = 0;
  size_t key_bytes = 4;
  size_t value_bytes = 8;
  uint32_t read_ppm = 950000;
  uint32_t hit_ppm = 1000000;
  uint64_t seed = 1;
  size_t buffer_requests = 4096;
  KeyLayout key_layout = KeyLayout::kPermuted;
  // Request k touches live key k*S mod N (CounterKey): one add and compare per
  // request instead of the generator's random draws. The worker
  // (benchmarks/support/prepared_workload.hpp) takes request k's read/update
  // decision from a table of At(0..4095), entry k mod 4096, so the write share
  // is that of those 4096 draws (see WORKLOAD.md). S is about 0.618 N and coprime with N, so
  // every key comes up once per N requests and consecutive requests land far
  // apart: a table filled in key order (std::unordered_map's nodes, a dense
  // index's position array) is still read at random, not walked in order.
  bool counter_key = false;
};

struct WorkloadRequest {
  uint64_t request_id;
  uint64_t key_id;  // Public logical ID, never an address into a dataset buffer.
  bool write;
  bool expected_hit;
  // Initial values have version zero; updates use id+1, so a write's value
  // needs no per-key state (it is the same with verification off).
  uint64_t value_version;
};

class WorkloadGenerator {
 public:
  explicit WorkloadGenerator(WorkloadSpec spec) : spec_(spec) {
    using workload_detail::Require;
    Require(spec.live_entries > 0 && spec.key_bytes > 0 && spec.value_bytes > 0 &&
            spec.buffer_requests > 0, "workload sizes must be positive");
    Require(spec.read_ppm <= 1000000 && spec.hit_ppm <= 1000000,
            "workload fractions exceed one million ppm");
    Require((spec.hit_ppm == 1000000) == (spec.miss_key_count == 0),
            "miss workloads need a disjoint nonempty miss key set");
    Require(spec.hit_ppm == 1000000 || spec.read_ppm == 1000000,
            "miss workloads must be read-only; writes only update existing keys");
    // The counter visits live keys only, so it can only reproduce an all-hit sequence.
    Require(!spec.counter_key || spec.hit_ppm == 1000000,
            "the counter key pattern cannot issue misses");
    Require(spec.miss_key_count <= std::numeric_limits<uint64_t>::max() - spec.live_entries,
            "live and miss key counts exceed uint64 capacity");
    key_count_ = spec.live_entries + spec.miss_key_count;
    if (spec.key_bytes < 8) {
      Require(key_count_ <= (uint64_t{1} << (8 * spec.key_bytes)),
              "live and miss keys do not fit the declared key width");
    }
    if (spec.counter_key && spec.live_entries > 1) {
      const uint64_t n = spec.live_entries;
      counter_stride_ = static_cast<uint64_t>(
          (static_cast<unsigned __int128>(n) * UINT64_C(0x9e3779b97f4a7c15)) >> 64);
      if (!counter_stride_) counter_stride_ = 1;
      while (std::gcd(counter_stride_, n) != 1) ++counter_stride_;  // stops by n - 1
    }
  }

  const WorkloadSpec& spec() const { return spec_; }
  uint64_t counter_stride() const { return counter_stride_; }
  // The counter pattern's key for request k (a callee stepping through
  // consecutive requests adds the stride instead).
  uint64_t CounterKey(uint64_t request_id) const {
    return static_cast<uint64_t>(static_cast<unsigned __int128>(request_id) * counter_stride_ %
                                 spec_.live_entries);
  }

  WorkloadRequest At(uint64_t request_id) const {
    // Reserve UINT64_MAX rather than wrapping the update version to initial.
    workload_detail::Require(request_id != std::numeric_limits<uint64_t>::max(),
                             "request id exhausts the version space");
    workload_detail::Random hit(spec_.seed, request_id, 1);
    workload_detail::Random write(spec_.seed, request_id, 2);
    workload_detail::Random key(spec_.seed, request_id, 3);
    const bool found = hit.Below(1000000) < spec_.hit_ppm;
    const bool update = write.Below(1000000) >= spec_.read_ppm;
    const uint64_t key_id = found ? key.Below(spec_.live_entries)
        : spec_.live_entries + key.Below(spec_.miss_key_count);
    return {request_id, key_id, update, found, update ? request_id + 1 : 0};
  }

  // An odd affine permutation modulo 2^(8*min(width,8)) is injective over
  // the validated ID space. Wider keys retain that injective prefix and have
  // deterministic nonconstant suffix bytes; no unbounded counter truncation.
  // Dense keys are the ID itself, zero-extended to the key width.
  void Key(uint64_t key_id, uint8_t* output, size_t bytes) const {
    CheckBuffer(key_id, output, bytes, spec_.key_bytes);
    if (spec_.key_layout == KeyLayout::kDense) {
      for (size_t i = 0; i < bytes; ++i) output[i] = i < 8 ? static_cast<uint8_t>(key_id >> (8 * i)) : 0;
      return;
    }
    const uint64_t prefix = key_id * (workload_detail::Mix(spec_.seed ^ 4) | 1)
        + workload_detail::Mix(spec_.seed ^ 5);
    for (size_t i = 0; i < bytes; ++i) {
      const uint64_t word = i < 8 ? prefix
          : workload_detail::Mix(key_id ^ workload_detail::Mix(spec_.seed ^ 6) ^ (i / 8));
      output[i] = static_cast<uint8_t>(word >> (8 * (i % 8)));
    }
  }

  // Inverts Key's prefix in O(1) (the no-op backend's lookup). Suffix bytes
  // are not checked; a prefix outside the workload returns an ID >= the
  // live plus miss key count.
  uint64_t KeyId(const uint8_t* key) const {
    const size_t prefix_bytes = spec_.key_bytes < 8 ? spec_.key_bytes : 8;
    const uint64_t prefix = LoadWord(key, prefix_bytes);
    if (spec_.key_layout == KeyLayout::kDense) return prefix;
    const uint64_t scale = workload_detail::Mix(spec_.seed ^ 4) | 1;
    uint64_t inverse = scale;  // Newton: 3, 6, 12, 24, 48, 96 correct bits.
    for (int i = 0; i < 5; ++i) inverse *= 2 - scale * inverse;
    const uint64_t id = (prefix - workload_detail::Mix(spec_.seed ^ 5)) * inverse;
    return prefix_bytes == 8 ? id : id & ((uint64_t{1} << (8 * prefix_bytes)) - 1);
  }

  // One Mix per 8-byte word; byte i is byte (i % 8) of word i / 8.
  void Value(uint64_t key_id, uint64_t version, uint8_t* output, size_t bytes) const {
    CheckBuffer(key_id, output, bytes, spec_.value_bytes);
    const uint64_t base = ValueBase(key_id, version);
    size_t i = 0;
    for (; i + 8 <= bytes; i += 8) StoreWord(output + i, 8, ValueWord(base, i / 8));
    if (i < bytes) StoreWord(output + i, bytes - i, ValueWord(base, i / 8));
  }

  // Exact full-value comparison when the expected version is known (e.g.
  // initialization, read-only trials, or a small reference-map smoke test).
  // This does not infer the latest version of an arbitrary mixed workload.
  bool MatchesValue(uint64_t key_id, uint64_t version,
                    const uint8_t* value, size_t bytes) const {
    CheckBuffer(key_id, value, bytes, spec_.value_bytes);
    const uint64_t base = ValueBase(key_id, version);
    uint64_t differ = 0;
    size_t i = 0;
    for (; i + 8 <= bytes; i += 8) differ |= LoadWord(value + i, 8) ^ ValueWord(base, i / 8);
    if (i < bytes) {
      const unsigned tail = static_cast<unsigned>(bytes - i);
      differ |= (LoadWord(value + i, tail) ^ ValueWord(base, i / 8)) &
                (~uint64_t{0} >> (64 - 8 * tail));
    }
    return differ == 0;
  }

 private:
  void CheckBuffer(uint64_t id, const uint8_t* data, size_t bytes, size_t expected) const {
    workload_detail::Require(id < key_count_, "key id outside live/miss sets");
    workload_detail::Require(data != nullptr && bytes == expected, "incorrect record buffer width");
  }
  uint64_t ValueBase(uint64_t id, uint64_t version) const {
    return workload_detail::Mix(spec_.seed ^ 7) ^ workload_detail::Mix(id) ^
        workload_detail::Mix(version ^ UINT64_C(0xd1b54a32d192ed03));
  }
  static uint64_t ValueWord(uint64_t base, uint64_t word) {
    return workload_detail::Mix(base ^ word);
  }
  // Little-endian on every host, so values are byte-identical across hosts.
  static void StoreWord(uint8_t* out, size_t bytes, uint64_t word) {
    for (size_t i = 0; i < bytes; ++i) out[i] = static_cast<uint8_t>(word >> (8 * i));
  }
  static uint64_t LoadWord(const uint8_t* in, size_t bytes) {
    uint64_t word = 0;
    for (size_t i = 0; i < bytes; ++i) word |= uint64_t{in[i]} << (8 * i);
    return word;
  }
  WorkloadSpec spec_;
  uint64_t key_count_;
  uint64_t counter_stride_ = 0;
};

}  // namespace oram_bench
