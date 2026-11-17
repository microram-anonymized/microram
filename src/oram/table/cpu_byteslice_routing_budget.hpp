#pragma once

// The routing-evaluation budget: a hard cap on how many routing-tag AES
// messages one map instance may ever evaluate.  The cryptographic part of the
// failure bound is stated in terms of the number of PRF/PRP queries, so the
// engine enforces a declared limit instead of assuming one (levelarena
// DESIGN.md, "Routing budget").
#include <array>
#include <atomic>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <stdexcept>

namespace microram {
namespace byteslice {

// One instance-wide allowance for complete routing-message evaluations,
// including repeats and SIMD padding. Reserve before AES, never refund.
// A refused reservation permanently stops the instance: a background rebuild
// or value worker may already have changed state. Concurrent admitted work may
// finish, but all of it remains covered by the same limit.
//
// Every requester, batch participant, value worker, rebuild owner and helper
// reserves from this one budget, a few dozen evaluations at a time, so a
// single shared counter is contended by every thread.  With the default limit,
// UINT64_MAX, small reservations cannot reach the limit, so each thread adds
// them to its own cache line (a shard) and count() sums the shards: the count
// stays exact and nothing is refused that the single counter would admit.
// A finite limit, or any reservation above kShardedMax, uses the exact
// compare-and-swap counter; the first such reservation on an unlimited budget
// switches it to exact mode for good.  The switch and the shard additions
// order each other (sequentially consistent flag store and load around the
// shard add), so every shard addition is either seen by the exact path's sum
// or backed out and retried through the exact path.
class RoutingEvaluationBudget {
 public:
  explicit RoutingEvaluationBudget(uint64_t limit)
      : limit_(limit), exact_(limit != std::numeric_limits<uint64_t>::max()) {}

  uint64_t count() const {
    return Saturating(used_.load(std::memory_order_relaxed), ShardTotal());
  }
  uint64_t limit() const { return limit_; }
  bool exhausted() const { return exhausted_.load(std::memory_order_relaxed); }

  void RequireAvailable() const {
    if (exhausted()) ThrowExhausted();
  }

  void Reserve(uint64_t evaluations) {
    RequireAvailable();
    if (evaluations == 0) return;
    if (evaluations <= kShardedMax && !exact_.load(std::memory_order_relaxed)) {
      std::atomic<uint64_t>& shard = shards_[ThreadShard()].used;
      shard.fetch_add(evaluations, std::memory_order_seq_cst);
      if (!exact_.load(std::memory_order_seq_cst)) return;
      shard.fetch_sub(evaluations, std::memory_order_seq_cst);  // not yet spent
    }
    ReserveExact(evaluations);
  }

  [[noreturn]] void Refuse() {
    exhausted_.store(true, std::memory_order_relaxed);
    ThrowExhausted();
  }

 private:
  static constexpr size_t kShards = 64;
  // Above the leaf tag routines' reservations (32, or a count rounded to
  // four), far below the 2^64 the shards would need to reach the limit.
  static constexpr uint64_t kShardedMax = uint64_t{1} << 32;

  struct alignas(64) Shard {
    std::atomic<uint64_t> used{0};
  };

  void ReserveExact(uint64_t evaluations) {
    if (!exact_.load(std::memory_order_relaxed))
      exact_.store(true, std::memory_order_seq_cst);
    uint64_t used = used_.load(std::memory_order_relaxed);
    for (;;) {
      RequireAvailable();
      // After the switch no shard grows, so the sum is the spent count (or
      // above it while a racing addition backs out, which only refuses more).
      const uint64_t total = Saturating(used, ShardTotal());
      if (evaluations > limit_ - total) Refuse();
      if (used_.compare_exchange_weak(used, used + evaluations,
                                     std::memory_order_seq_cst)) return;
    }
  }

  static size_t ThreadShard() {
    static std::atomic<size_t> next{0};
    thread_local const size_t shard =
        next.fetch_add(1, std::memory_order_relaxed) % kShards;
    return shard;
  }

  uint64_t ShardTotal() const {
    uint64_t total = 0;
    for (const Shard& shard : shards_)
      total = Saturating(total, shard.used.load(std::memory_order_seq_cst));
    return total;
  }

  static uint64_t Saturating(uint64_t a, uint64_t b) {
    return b > std::numeric_limits<uint64_t>::max() - a
               ? std::numeric_limits<uint64_t>::max()
               : a + b;
  }

  [[noreturn]] static void ThrowExhausted() {
    throw std::overflow_error("level arena: routing evaluation budget exhausted; instance stopped");
  }

  const uint64_t limit_;
  std::atomic<bool> exact_;
  std::atomic<uint64_t> used_{0};
  std::atomic<bool> exhausted_{false};
  std::array<Shard, kShards> shards_{};
};

}  // namespace byteslice
}  // namespace microram
