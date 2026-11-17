#pragma once
// The workload adapter between RunTrial and a backend: it pre-generates each
// request's key and value, issues scalar or batch calls, and checks every
// returned value against an exact per-key version oracle (the correctness
// check every benchmark row runs with by default).

#include "src/oram/support/benchmark_trial.hpp"
#include "src/oram/support/benchmark_workload.hpp"

#include <string>
#include <type_traits>
#include <vector>

namespace oram_bench {

inline size_t BufferProduct(size_t count, size_t width) {
  Require(!width || count <= SIZE_MAX / width, "record buffer size overflow");
  return count * width;
}

// `full` compares every returned value against an exact per-key
// version oracle; `off` allocates no oracle, compares no value and skips the
// final sweep. Both keep the free hit/miss (found) checks and the checksum.
enum class Verification { kFull, kOff };
inline const char* VerificationName(Verification mode) {
  return mode == Verification::kFull ? "full" : "off";
}
inline Verification ParseVerification(const std::string& name) {
  Require(name == "full" || name == "off", "unknown verification mode");
  return name == "full" ? Verification::kFull : Verification::kOff;
}

namespace prepared_detail {
// A backend that reads the caller's version oracle (the no-op backend).
template <typename B, typename = void> struct BindsVersions : std::false_type {};
template <typename B>
struct BindsVersions<B, std::void_t<decltype(std::declval<B&>().BindVersions(
    static_cast<const uint64_t*>(nullptr)))>> : std::true_type {};
}  // namespace prepared_detail

// Backend supplies Request, MakeRequest, Find, Write, Batch and Finish.
// Scratch is bounded by the caller batch. Exact mixed-workload verification
// additionally uses an explicitly accounted uint64 version per live key;
// read-only workloads and verification off need no reference table. Neither
// path stores values in the oracle. All of this memory is allocated before
// construction/fill timing.
template <typename Backend>
class PreparedWorkload {
 public:
  PreparedWorkload(Backend& backend, WorkloadSpec workload, size_t max_batch,
                   bool batched, Verification verification = Verification::kFull)
      : backend_(backend), generator_(workload), batched_(batched),
        verify_(verification == Verification::kFull),
        requests_(max_batch), logical_(max_batch), found_(max_batch),
        keys_(BufferProduct(max_batch, workload.key_bytes)),
        values_(BufferProduct(max_batch, workload.value_bytes)),
        output_(BufferProduct(max_batch, workload.value_bytes)),
        versions_(!verify_ || workload.read_ppm == 1000000 ? 0 : workload.live_entries, 0) {
    Require(max_batch > 0 && max_batch <= workload.buffer_requests,
            "caller batch exceeds workload buffer limit");
    Require(batched || max_batch == 1, "scalar adapter requires one scratch slot");
    if constexpr (prepared_detail::BindsVersions<Backend>::value)
      backend_.BindVersions(versions_.empty() ? nullptr : versions_.data());
    if (workload.counter_key) {
      // A table of the uniform workload's first 4096 read/update decisions:
      // request k takes entry k mod 4096, and the key comes from the counter.
      // The run's write share is therefore the share in these 4096 draws, set
      // by the seed, and when N is a multiple of 4096 every visit to a key
      // (N requests apart) takes the same decision, so each key is either
      // always read or always written. The generator rejects misses in this
      // mode, so every request is a hit.
      pattern_.resize(kPatternLength);
      for (size_t i = 0; i < pattern_.size(); ++i) pattern_[i] = generator_.At(i);
    }
  }
  PreparedWorkload(const PreparedWorkload&) = delete;  // a bound backend keeps this table
  const WorkloadGenerator& generator() const { return generator_; }
  Verification verification() const { return verify_ ? Verification::kFull : Verification::kOff; }
  uint64_t checksum() const { return checksum_; }
  uint64_t verified_reads() const { return verified_reads_; }
  uint64_t verified_old_values() const { return verified_old_values_; }
  size_t version_table_bytes() const { return versions_.size() * sizeof(uint64_t); }
  size_t scratch_bytes() const {
    return requests_.size() * sizeof(typename Backend::Request) +
        logical_.size() * sizeof(WorkloadRequest) + found_.size() + keys_.size() +
        values_.size() + output_.size() + version_table_bytes();
  }
  void Prepare(const PendingRequest* members, size_t count) {
    Require(count > 0 && count <= requests_.size(), "batch exceeds prepared storage");
    const auto& spec = generator_.spec();
    for (size_t i = 0; i < count; ++i) {
      logical_[i] = pattern_.empty() ? generator_.At(members[i].id) : CounterRequest(members[i].id);
      auto* key = keys_.data() + i * spec.key_bytes;
      auto* value = values_.data() + i * spec.value_bytes;
      generator_.Key(logical_[i].key_id, key, spec.key_bytes);
      if (logical_[i].write)
        generator_.Value(logical_[i].key_id, logical_[i].value_version,
                         value, spec.value_bytes);
      requests_[i] = Backend::MakeRequest(logical_[i].write, key, value,
                                         output_.data() + i * spec.value_bytes);
    }
  }
  template <typename Clock>
  InvocationTiming Invoke(Clock& clock, bool timed, size_t count) {
    if (batched_)
      return InvokePrepared(clock, timed, [&] {
        backend_.Batch(count, requests_.data(), found_.data());
      });
    if (logical_[0].write)
      return InvokePrepared(clock, timed, [&] {
        backend_.Write(keys_.data(), values_.data());
      });
    return InvokePrepared(clock, timed, [&] {
      found_[0] = backend_.Find(keys_.data(), output_.data());
    });
  }
  // In request order, so a repeated key sees earlier writes of the same batch.
  void Consume(size_t count) {
    const size_t width = generator_.spec().value_bytes;
    for (size_t i = 0; i < count; ++i) {
      const auto& request = logical_[i];
      const auto* output = output_.data() + i * width;
      if (request.write) {
        // Writes update existing keys only. A batch write reports presence
        // and the value before it, and both are checked here. A scalar write
        // goes through exchange(key, value, old, true) (see cpu_backend.hpp),
        // which also reads the old value in the same access, but the worker
        // checks neither that value nor whether the key was present. A scalar
        // write to a lost record therefore inserts it again unnoticed.
        if (batched_) {
          Require(found_[i], "correctness: write did not find its existing key");
          if (verify_) {
            Require(generator_.MatchesValue(request.key_id, Version(request.key_id), output, width),
                    "correctness: write returned an old value that differs from the expected version");
            ++verified_old_values_;
          }
        }
        if (!versions_.empty()) versions_[request.key_id] = request.value_version;
        last_written_key_ = request.key_id;
      } else {
        Require(bool(found_[i]) == request.expected_hit,
                "correctness: lookup hit/miss differs from workload");
        if (!request.expected_hit) continue;  // miss output has no value contract
        if (verify_) {
          Require(generator_.MatchesValue(request.key_id, Version(request.key_id), output, width),
                  "correctness: full returned value differs from expected version");
          ++verified_reads_;
        }
      }
      // Reads fold the returned value, writes the written one, so scalar and
      // batch runs of one sequence agree.
      checksum_ = Checksum(checksum_, request.write ? values_.data() + i * width : output, width);
    }
  }
  size_t verification_budget() const {
    return verify_ ? std::min<uint64_t>(64, generator_.spec().live_entries) + 1 : 0;
  }
  // Outside timing. With verification off there is no sweep and no drain.
  size_t VerifyFinal() {
    if (!verify_) return 0;
    const auto& spec = generator_.spec();
    auto verify = [&](uint64_t id) {
      generator_.Key(id, keys_.data(), spec.key_bytes);
      Require(backend_.Find(keys_.data(), output_.data()),
              "correctness: final verification key is missing");
      Require(generator_.MatchesValue(id, Version(id), output_.data(), spec.value_bytes),
              "correctness: final verification value differs");
    };
    const size_t count = std::min<uint64_t>(64, spec.live_entries);
    for (size_t i = 0; i < count; ++i) {
      // Small fixtures check every live record; large trials use deterministic
      // public sample keys in addition to the last actual write.
      const auto id = spec.live_entries <= 64 ? i
          : workload_detail::Mix(spec.seed ^ i) % spec.live_entries;
      verify(id);
    }
    if (last_written_key_) verify(*last_written_key_);
    backend_.Finish();
    return count + bool(last_written_key_);
  }
  void Finish() { backend_.Finish(); }
 private:
  uint64_t Version(uint64_t id) const { return versions_.empty() ? 0 : versions_[id]; }
  // Request k of the counter pattern. Requests come in id order, so the key
  // advances by one stride (no division) unless the id jumps.
  WorkloadRequest CounterRequest(uint64_t id) {
    WorkloadRequest request = pattern_[id & (kPatternLength - 1)];
    if (id != counter_id_) counter_key_ = generator_.CounterKey(id);
    request.request_id = id;
    request.key_id = counter_key_;
    request.value_version = request.write ? id + 1 : 0;
    const uint64_t live = generator_.spec().live_entries, stride = generator_.counter_stride();
    counter_id_ = id + 1;
    counter_key_ = counter_key_ >= live - stride ? counter_key_ - (live - stride) : counter_key_ + stride;
    return request;
  }
  // Keeps every returned byte observable without a byte-serial dependency
  // chain: four independent 8-byte lanes, folded once per record.
  static uint64_t Checksum(uint64_t state, const uint8_t* bytes, size_t width) {
    constexpr uint64_t kPrime = UINT64_C(0x100000001b3);
    auto load = [&](size_t at, size_t n) {
      uint64_t word = 0;
      for (size_t k = 0; k < n; ++k) word |= uint64_t{bytes[at + k]} << (8 * k);
      return word;
    };
    uint64_t lane[4] = {state, state ^ 1, state ^ 2, state ^ 3};
    size_t i = 0;
    for (; i + 32 <= width; i += 32)
      for (size_t k = 0; k < 4; ++k) lane[k] = (lane[k] ^ load(i + 8 * k, 8)) * kPrime;
    for (size_t k = 0; i < width; i += 8, ++k)
      lane[k] = (lane[k] ^ load(i, std::min<size_t>(8, width - i))) * kPrime;
    return (((lane[0] * kPrime) ^ lane[1]) * kPrime ^ lane[2]) * kPrime ^ lane[3];
  }
  static constexpr size_t kPatternLength = 4096;
  Backend& backend_;
  WorkloadGenerator generator_;
  std::vector<WorkloadRequest> pattern_;
  bool batched_, verify_;
  std::vector<typename Backend::Request> requests_;
  std::vector<WorkloadRequest> logical_;
  std::vector<uint8_t> found_, keys_, values_, output_;
  std::vector<uint64_t> versions_;
  uint64_t checksum_ = 0, verified_reads_ = 0, verified_old_values_ = 0;
  std::optional<uint64_t> last_written_key_;
  uint64_t counter_id_ = 0, counter_key_ = 0;  // the counter's next request and its key
};
}  // namespace oram_bench
