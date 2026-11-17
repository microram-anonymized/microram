#pragma once

#include "src/oram/support/benchmark_workload.hpp"
#include "src/oram/support/benchmark_statistics.hpp"
#include <algorithm>
#include <vector>

namespace oram_bench {
// Constant-space no-op backend: it stores no key or value. A read, or
// a batch write's old value, is generated from the workload at the version
// the caller's oracle expects, so verification succeeds by construction and
// the caller does exactly the work it does for a real map. It isolates the
// caller-side cost (generation, verification, checksum, trial loop, logging),
// which a real backend's numbers include, and runs at any capacity. Its own work is an O(1) key
// decode and one value generation per returned value, plus a scan of the
// current batch's earlier writes. Synthetic: no ORAM cost or security claim.
class NoopBackend {
 public:
  struct Request {
    bool write = false;
    const uint8_t* key = nullptr;
    const uint8_t* value = nullptr;
    uint8_t* output = nullptr;
  };
  // Scratch is one caller batch of write lanes, allocated here, not per call.
  NoopBackend(WorkloadSpec spec, size_t max_batch)
      : generator_(spec), write_ids_(max_batch), write_values_(max_batch) {}
  static Request MakeRequest(bool write, const uint8_t* key,
                             const uint8_t* value, uint8_t* output) {
    return {write, key, write ? value : nullptr, output};
  }
  // PreparedWorkload binds its version table (null with none: read-only or
  // verification off, when initial values are returned). Valid for the
  // adapter's lifetime; the table advances only after each call returns.
  void BindVersions(const uint64_t* versions) { versions_ = versions; }
  uint64_t Fill(const WorkloadGenerator&) { return 0; }
  bool Find(const uint8_t* key, uint8_t* output) {
    const uint64_t id = generator_.KeyId(key);
    if (!Live(id)) return false;
    generator_.Value(id, Version(id), output, generator_.spec().value_bytes);
    return true;
  }
  void Write(const uint8_t*, const uint8_t*) {}
  // A write is visible to later lanes of its own batch (the batch API's
  // contract), but the oracle has not seen it yet: such a lane copies the
  // latest earlier write of its key instead.
  void Batch(size_t count, const Request* requests, uint8_t* found) {
    Require(count <= write_ids_.size(), "no-op batch exceeds its scratch");
    const size_t width = generator_.spec().value_bytes;
    size_t writes = 0;
    for (size_t i = 0; i < count; ++i) {
      const auto& r = requests[i];
      const uint64_t id = generator_.KeyId(r.key);
      found[i] = Live(id);
      if (r.output) {
        size_t k = writes;
        while (k && write_ids_[k - 1] != id) --k;
        if (k) std::copy_n(write_values_[k - 1], width, r.output);
        else if (found[i]) generator_.Value(id, Version(id), r.output, width);
        else std::fill_n(r.output, width, uint8_t{0});
      }
      if (r.write && found[i]) {
        write_ids_[writes] = id;
        write_values_[writes++] = r.value;
      }
    }
  }
  void Finish() {}
 private:
  bool Live(uint64_t id) const { return id < generator_.spec().live_entries; }
  uint64_t Version(uint64_t id) const { return versions_ ? versions_[id] : 0; }
  WorkloadGenerator generator_;
  const uint64_t* versions_ = nullptr;
  std::vector<uint64_t> write_ids_;
  std::vector<const uint8_t*> write_values_;
};
}  // namespace oram_bench
