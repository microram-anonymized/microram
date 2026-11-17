#pragma once

// Timing and deterministic-data helpers shared by the small standalone
// microbenchmarks. Workload-specific setup stays in each benchmark.

#include <chrono>
#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

#include "src/oram/rebuild/cpu_byteslice_initialization.hpp"

namespace microram {
namespace byteslice {
namespace benchmark_support {

using Clock = std::chrono::steady_clock;

inline double SecondsSince(Clock::time_point start) {
  return std::chrono::duration<double>(Clock::now() - start).count();
}

struct PhaseTime {
  double seconds_per_rep = 0.0;
  int reps = 0;
};

// Runs at least two repetitions, then continues until 0.3 seconds of measured
// work or max_reps. The body returns the measured seconds for one repetition.
template <class Body>
inline PhaseTime Measure(int max_reps, Body&& body) {
  PhaseTime out;
  double total = 0.0;
  while (out.reps < max_reps && (out.reps < 2 || total < 0.3)) {
    total += body();
    ++out.reps;
  }
  out.seconds_per_rep = total / out.reps;
  return out;
}

inline uint64_t SplitMix64(uint64_t& state) {
  uint64_t z = (state += 0x9E3779B97F4A7C15ull);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
  return z ^ (z >> 31);
}

// ---------------------------------------------------------------------------
// Generated initialization input
// ---------------------------------------------------------------------------
//
// What a benchmark's fill hands to ORAM::Initialize (direct initialization:
// the largest level is built straight from the input stream by one routing
// network, see src/oram/rebuild/cpu_byteslice_initialization.hpp) in place of
// one online Write per record.  It holds ONE record -- the same two buffers an online fill filled
// -- and refills them at each dereference from the benchmark's own key and
// value writers, so the entries a converted fill produces are byte for byte
// the entries the online fill produced.  Nothing is buffered, nothing is
// replayed, and the keys are the same consecutive run.
//
// `write_key(key, uint8_t* out)` fills key_bytes and `write_value(key,
// uint8_t* out, size_t bytes)` fills value_bytes, which is exactly the pair
// every driver here already has.
template <class WriteKey, class WriteValue>
class GeneratedRecords {
 public:
  GeneratedRecords(uint64_t first_key, size_t key_bytes, size_t value_bytes,
                   WriteKey write_key, WriteValue write_value)
      : key_(first_key),
        key_buffer_(key_bytes),
        value_buffer_(value_bytes),
        write_key_(std::move(write_key)),
        write_value_(std::move(write_value)) {}

  InitializationEntry operator*() {
    write_key_(key_, key_buffer_.data());
    write_value_(key_, value_buffer_.data(), value_buffer_.size());
    return InitializationEntry{key_buffer_.data(), value_buffer_.data()};
  }
  GeneratedRecords& operator++() {
    ++key_;
    return *this;
  }

 private:
  uint64_t key_;
  std::vector<uint8_t> key_buffer_;
  std::vector<uint8_t> value_buffer_;
  WriteKey write_key_;
  WriteValue write_value_;
};

template <class WriteKey, class WriteValue>
GeneratedRecords<WriteKey, WriteValue> MakeGeneratedRecords(
    uint64_t first_key, size_t key_bytes, size_t value_bytes,
    WriteKey write_key, WriteValue write_value) {
  return GeneratedRecords<WriteKey, WriteValue>(
      first_key, key_bytes, value_bytes, std::move(write_key),
      std::move(write_value));
}

}  // namespace benchmark_support
}  // namespace byteslice
}  // namespace microram
