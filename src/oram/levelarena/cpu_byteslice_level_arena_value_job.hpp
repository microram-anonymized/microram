#pragma once

// The shared records of one VALUE-WORKER job
// (cpu_byteslice_level_arena_value_workers.hpp): what the requester hands each
// worker when a scalar access starts (ValueStart), what each worker hands back
// (ValueReply), and the one progress word through which the requester streams
// its probe cascade's results to every worker (ValueProgress).
//
// The progress word packs, under a 16-bit job tag:
//   ready  -- how many plan entries the requester's cascade has finished
//             (public: the cascade visits every entry in plan order);
//   hit    -- whether any finished entry matched the key (SECRET);
//   first  -- the winning entry, bucket and slot so far (SECRET);
//   final  -- the requester has finished every entry the workers own;
//   cancel -- the job is abandoned (an exception on the requester).
// Workers use the secret fields only as operands of constant-time selects,
// blends and in-register permutes.  The one address they influence is the
// real/dummy bucket of a hashed entry, which is the same choice the
// requester's own cascade makes (and is permitted to make) for that entry.

#include <atomic>
#include <cstdint>
#include "src/oram/table/cpu_byteslice_value_plane.hpp"
#include "src/oram/table/cpu_byteslice_probe_plan.hpp"

namespace microram::byteslice::levelarena {

// Sequence is a full-width start/done counter, separate from the progress
// tag. No ABA: one accepted job, joined before reuse, the word rewritten
// before its 16-bit tag could repeat (it is not reset per job), and overflow
// refused.
struct ValueProgress {
  static constexpr size_t kMaxEntries = 255;
  static constexpr size_t kMaxRun = 4096;
  static uint64_t Pack(uint64_t seq, size_t r, uint64_t hit, size_t f,
                       size_t w, unsigned s, bool final, bool cancel = false) {
    return (seq & 0xffff) | (uint64_t{r} << 16) | (hit << 24) |
        (uint64_t{f} << 25) | (uint64_t{w} << 33) |
        (uint64_t{s} << 45) | (uint64_t{final} << 51) |
        (uint64_t{cancel} << 52);
  }
  static size_t Ready(uint64_t p) { return (p >> 16) & 255; }
  static uint64_t Hit(uint64_t p) { return (p >> 24) & 1; }
  static size_t First(uint64_t p) { return (p >> 25) & 255; }
  static size_t Bucket(uint64_t p) { return (p >> 33) & 4095; }
  static unsigned Slot(uint64_t p) { return (p >> 45) & 63; }
  static bool Final(uint64_t p) { return (p >> 51) & 1; }
  static bool Cancel(uint64_t p) { return (p >> 52) & 1; }
};

// Written by the requester before it release-stores `sequence`; one per
// worker, on its own cache line.
struct alignas(64) ValueStart {
  std::atomic<uint64_t> sequence{0};
  const ProbePlan* plan = nullptr;
  KeyWords key{};
  uint64_t dummy_base = 0;
  uint8_t* pending_bucket = nullptr;
  uint32_t boundary = 0;
  uint32_t pending_slot = 0;
  // Pending existence depends only on the previous public operation/path.
};
static_assert(sizeof(ValueStart) == 64);
// Written by its worker: up to 56 value bytes inline (a wider column range
// uses the worker's own buffer), then `done` = the job's sequence.
struct alignas(64) ValueReply {
  std::atomic<uint64_t> done{0};
  uint8_t bytes[56]{};
};
static_assert(sizeof(ValueReply) == 64);

}  // namespace microram::byteslice::levelarena
