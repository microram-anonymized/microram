#pragma once

#include "src/oram/support/benchmark_workload.hpp"
#include "src/oram/support/benchmark_statistics.hpp"
#include <algorithm>
#include <functional>
#include <unordered_map>
#include <vector>

namespace oram_bench {
// Portable correctness backend: it stores every value (live x value_bytes)
// and probes a hash index, so it is not a cost-free adapter; NoopBackend is.
// Keys and values are allocated only on fill; timed accesses only
// find/update existing entries. It is explicitly a synthetic backend and
// makes no claim to model an ORAM's cost or security.
class FakeBackend {
 public:
  struct Request {
    bool write = false;
    const uint8_t* key = nullptr;
    const uint8_t* value = nullptr;
    uint8_t* output = nullptr;
  };
  explicit FakeBackend(WorkloadSpec spec) : spec_(spec), values_(Bytes(spec)) {}
  static Request MakeRequest(bool write, const uint8_t* key,
                             const uint8_t* value, uint8_t* output) {
    return {write, key, write ? value : nullptr, output};
  }
  uint64_t Fill(const WorkloadGenerator& generator) {
    index_.reserve(spec_.live_entries);
    std::vector<uint8_t> key(spec_.key_bytes);
    for (uint64_t id = 0; id < spec_.live_entries; ++id) {
      generator.Key(id, key.data(), key.size());
      index_.emplace(Prefix(key.data()), id);
      generator.Value(id, 0, values_.data() + id * spec_.value_bytes, spec_.value_bytes);
    }
    return 0;
  }
  bool Find(const uint8_t* key, uint8_t* output) {
    const auto at = index_.find(Prefix(key));
    if (at == index_.end()) return false;
    const auto* value = values_.data() + at->second * spec_.value_bytes;
    std::copy_n(value, spec_.value_bytes, output);
    return true;
  }
  void Write(const uint8_t* key, const uint8_t* value) {
    const auto at = index_.find(Prefix(key));
    Require(at != index_.end(), "fake workload wrote an absent key");
    std::copy_n(value, spec_.value_bytes, values_.data() + at->second * spec_.value_bytes);
  }
  // The batch API's write: found is whether the key was present before it
  // ran, and `output` receives the value before the write (zeros when
  // absent). The fake cannot insert; an absent key reports found = false.
  bool Exchange(const uint8_t* key, const uint8_t* value, uint8_t* output) {
    const auto at = index_.find(Prefix(key));
    if (at == index_.end()) {
      if (output) std::fill_n(output, spec_.value_bytes, uint8_t{0});
      return false;
    }
    auto* stored = values_.data() + at->second * spec_.value_bytes;
    if (output) std::copy_n(stored, spec_.value_bytes, output);
    std::copy_n(value, spec_.value_bytes, stored);
    return true;
  }
  void Batch(size_t count, const Request* requests, uint8_t* found) {
    for (size_t i = 0; i < count; ++i) {
      const auto& r = requests[i];
      found[i] = r.write ? Exchange(r.key, r.value, r.output) : Find(r.key, r.output);
    }
  }
  void Finish() {}
 private:
  static size_t Bytes(const WorkloadSpec& spec) {
    Require(spec.value_bytes && spec.live_entries <= SIZE_MAX / spec.value_bytes,
            "fake storage size overflow");
    return spec.live_entries * spec.value_bytes;
  }
  uint64_t Prefix(const uint8_t* key) const {
    uint64_t result = 0;
    for (size_t i = 0; i < std::min<size_t>(spec_.key_bytes, 8); ++i)
      result |= uint64_t{key[i]} << (8 * i);
    return result;
  }
  WorkloadSpec spec_;
  std::vector<uint8_t> values_;
  std::unordered_map<uint64_t, uint64_t> index_;
};
}  // namespace oram_bench
