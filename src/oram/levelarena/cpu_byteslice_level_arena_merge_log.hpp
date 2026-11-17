#pragma once

// THE PER-MERGE LOG OF EVERY LEVEL (used by the deamortization
// microbenchmark).  Like the top log, it records public scheduling events and
// timings only, never table contents.
//
// One record per job a level absorbs -- a merge, or an adoption, which is a
// carry taken with no work -- kept in a bounded ring per level of the last
// `capacity` records.  Off unless the engine is built with a capacity
// (LevelArenaEngine::Options::merge_log_capacity), and then a handful of
// steady_clock reads per job and nothing on a per-access path but level 1's
// prefix completion stamp (DensePrefixRing::EnableCompletionStamps).
//
// WHAT IT ANSWERS.  How a merge's work divides between PREPARATION (routing
// the older partial, which needs no carry) and what runs after the carry
// arrives (installing it, the finish's fixed-merge sweep and residual pass,
// the publication), and when each of those happened against the carry's
// arrival.  The work is the job's PIECE time (LevelMergeCost), summed by
// phase and class over every thread that ran a piece, so it needs the job's
// stage timing on; the stamps do not.
//
// WHO WRITES.  A level's records are written by the thread driving that level
// (its owner, or the requester inline), one at a time.  READ ONLY AFTER THE
// RUN DRAINS, as the top log is (cpu_byteslice_level_arena_top_log.hpp).
// Every stamp is steady_clock nanoseconds since its epoch; zero means "not
// reached".

#include <atomic>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <vector>

namespace microram {
namespace byteslice {
namespace levelarena {

// A job's piece time and estimated bucket touches (PieceTouches), by phase
// (LevelMergePhase: prepare-older, install-carry, finish) and class.  Fold
// time is ordered work outside every piece and has no touches.
struct LevelMergeCost {
  enum Class : unsigned { kRoute, kSweep, kResidual, kFold, kClasses };
  static constexpr unsigned kPhases = 3;
  uint64_t nanos[kPhases][kClasses] = {};
  uint64_t touches[kPhases][kClasses] = {};

  LevelMergeCost Since(const LevelMergeCost& before) const {
    LevelMergeCost d;
    for (unsigned p = 0; p < kPhases; ++p) {
      for (unsigned c = 0; c < kClasses; ++c) {
        d.nanos[p][c] = nanos[p][c] - before.nanos[p][c];
        d.touches[p][c] = touches[p][c] - before.touches[p][c];
      }
    }
    return d;
  }
  uint64_t PhaseNanos(unsigned phase) const {
    uint64_t n = 0;
    for (unsigned c = 0; c < kClasses; ++c) n += nanos[phase][c];
    return n;
  }
  uint64_t PhaseTouches(unsigned phase) const {
    uint64_t n = 0;
    for (unsigned c = 0; c < kClasses; ++c) n += touches[phase][c];
    return n;
  }
};

struct LevelMergeRecord {
  unsigned level = 0;
  unsigned digit = 0;          // the carry's digit; the partial held k = digit - 1
  uint64_t ordinal = 0;        // the carry ordinal this job absorbed
  uint64_t output_buckets = 0;
  bool adoption = false;       // taken in place: no job, no work
  bool prepared_ahead = false; // the older half was routed before the merge began
  // STAMPS.  prepare_start <= prepare_end and prepare_start <= merge_start <=
  // publish; the carry stamps are unordered against the preparation's.
  uint64_t prepare_start_ns = 0;  // the job was bound
  uint64_t prepare_end_ns = 0;    // its preparation ended (job stamp; timing on)
  uint64_t carry_ready_ns = 0;    // the carry became available: the level
                                  // below's plan install, or a prefix's completion
  uint64_t carry_accept_ns = 0;   // this level took it (ring drained / prefix taken)
  uint64_t merge_start_ns = 0;    // the carry-dependent phases began
  uint64_t publish_ns = 0;        // the output's plan was installed
  // WORK.  The job's piece time and touches over its life (timing on), and
  // the publication transaction's own time, which is no piece.
  LevelMergeCost cost;
  uint64_t publish_active_ns = 0;
  // The owner's wall time inside this job's phase calls, waits excluded
  // (LevelStats::job_nanos's share): piece time plus planning and binding.
  uint64_t job_call_ns = 0;
};

// One ring per level, indexed 1..levels.
class LevelMergeLog {
 public:
  LevelMergeLog(unsigned levels, size_t capacity)
      : capacity_(capacity), rings_(levels + 1) {
    if (capacity == 0) {
      throw std::invalid_argument("level arena: a merge log needs a capacity");
    }
    for (Ring& ring : rings_) ring.cells.resize(capacity);
  }

  size_t capacity() const { return capacity_; }

  // Writer (the level's driving thread).
  void Store(const LevelMergeRecord& record) {
    Ring& ring = rings_.at(record.level);
    const uint64_t n = ring.count.load(std::memory_order_relaxed);
    ring.cells[static_cast<size_t>(n % capacity_)] = record;
    ring.count.store(n + 1, std::memory_order_release);
  }

  uint64_t count(unsigned level) const {
    return rings_.at(level).count.load(std::memory_order_acquire);
  }

  // Level `level`'s stored records, oldest first.  Quiescent reads.
  std::vector<LevelMergeRecord> Snapshot(unsigned level) const {
    const Ring& ring = rings_.at(level);
    const uint64_t n = ring.count.load(std::memory_order_acquire);
    const uint64_t first = n > capacity_ ? n - capacity_ : 0;
    std::vector<LevelMergeRecord> out;
    out.reserve(static_cast<size_t>(n - first));
    for (uint64_t i = first; i < n; ++i) {
      out.push_back(ring.cells[static_cast<size_t>(i % capacity_)]);
    }
    return out;
  }

 private:
  struct Ring {
    std::vector<LevelMergeRecord> cells;
    std::atomic<uint64_t> count{0};
  };
  size_t capacity_;
  std::vector<Ring> rings_;
};

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
