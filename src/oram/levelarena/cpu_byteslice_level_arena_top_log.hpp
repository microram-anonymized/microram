#pragma once

// THE TOP MERGE LIFECYCLE LOG.
//
// A diagnostic for the benchmarks: when each top merge was prepared, received
// its carry, published and had its replaced table reclaimed, and how much
// active work each phase took.  It records only public scheduling events and
// times, never table contents.  One record per top merge, kept in a bounded ring of the last kCapacity.  The
// top runs once per top cycle, so a handful of steady_clock reads per merge is
// negligible and nothing here is on a per-access path.  Every stamp is
// steady_clock nanoseconds since the clock's epoch; zero means "not reached".
//
// WHO WRITES.  The top level's state machine is driven by one thread at a time
// (its owner, or the requester in inline and synchronous modes), and every
// field but `retire_ns` is written by that thread before the record is stored.
// `retire_ns` is a relaxed atomic because an idle owner re-polls (and may
// stamp the retirement) while the benchmark reads.  READ ONLY AFTER THE RUN
// DRAINS: Snapshot() is meant for a quiescent engine (the benchmark calls
// drain_rebuilds() first); it is data-race free then, and may show a record
// whose retirement was not yet observed (retire_ns == 0, `complete() ==
// false`).  A record is not overwritten until kCapacity later merges.

#include <array>
#include <atomic>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <vector>

namespace microram {
namespace byteslice {
namespace levelarena {

inline uint64_t TopLogNowNanos() {
  return static_cast<uint64_t>(
      std::chrono::duration_cast<std::chrono::nanoseconds>(
          std::chrono::steady_clock::now().time_since_epoch())
          .count());
}

struct TopMergeRecord {
  uint64_t ordinal = 0;  // the top's carry ordinal this merge absorbed
  // STAMPS (order: prepare_start <= merge_start <= publish <= retire;
  // carry_ready <= carry_accept <= merge_start.  prepare_start and the carry
  // stamps are unordered: a speculative preparation may start before the
  // carry exists, and a carry may wait for the top's owner).
  uint64_t prepare_start_ns = 0;  // the job was bound: preparation may begin
  uint64_t carry_ready_ns = 0;    // the carry became available to the top
                                  // (level L-1's commit; sync: its return)
  uint64_t carry_accept_ns = 0;   // the top's owner took it from the ring
  uint64_t merge_start_ns = 0;    // the carry-dependent phases began
  uint64_t publish_ns = 0;        // the new top table is probeable
  uint64_t retire_ns = 0;         // the replaced table's storage was reclaimed
  // ACTIVE time of this merge, from the owner's phase timers (waits excluded).
  uint64_t prepare_active_ns = 0;
  uint64_t merge_active_ns = 0;
  uint64_t publish_active_ns = 0;
  uint64_t fold_ns = 0;           // lane-fold share; needs --stage-times
  bool prepared_ahead = false;    // the older half was routed before the carry
  bool retire_in_place = false;   // synchronous: no separate retirement;
                                  // retire_ns is publish_ns
  bool complete() const { return retire_ns != 0; }
  uint64_t active_ns() const {
    return prepare_active_ns + merge_active_ns + publish_active_ns;
  }
};

class TopMergeLog {
 public:
  static constexpr size_t kCapacity = 256;

  // Writer (one thread): stores a finished record and returns its cell.
  size_t Store(const TopMergeRecord& record) {
    const uint64_t n = count_.load(std::memory_order_relaxed);
    const size_t cell = static_cast<size_t>(n % kCapacity);
    cells_[cell].record = record;
    cells_[cell].retire_ns.store(record.retire_ns, std::memory_order_relaxed);
    count_.store(n + 1, std::memory_order_release);
    return cell;
  }
  // Writer: the retirement of the record in `cell`, if it still holds
  // `ordinal` (it may have been overwritten in a very long run).
  void StampRetire(size_t cell, uint64_t ordinal, uint64_t ns) {
    if (cells_[cell].record.ordinal == ordinal) {
      cells_[cell].retire_ns.store(ns, std::memory_order_relaxed);
    }
  }

  // Merges stored over the engine's life.
  uint64_t count() const { return count_.load(std::memory_order_acquire); }

  // The stored records, oldest first (at most kCapacity).  Quiescent reads.
  std::vector<TopMergeRecord> Snapshot() const {
    const uint64_t n = count();
    const uint64_t first = n > kCapacity ? n - kCapacity : 0;
    std::vector<TopMergeRecord> out;
    out.reserve(static_cast<size_t>(n - first));
    for (uint64_t i = first; i < n; ++i) {
      const Cell& cell = cells_[static_cast<size_t>(i % kCapacity)];
      TopMergeRecord r = cell.record;
      r.retire_ns = cell.retire_ns.load(std::memory_order_relaxed);
      out.push_back(r);
    }
    return out;
  }

 private:
  struct Cell {
    TopMergeRecord record;
    std::atomic<uint64_t> retire_ns{0};
  };
  std::array<Cell, kCapacity> cells_{};
  std::atomic<uint64_t> count_{0};
};

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
