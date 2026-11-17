#pragma once

// Typed trial statistics.  StatsAccumulator turns each completed public call
// into request-weighted response (completion - intended arrival) and queueing
// (dispatch - intended arrival) samples and one call-weighted service
// (completion - dispatch) sample, counts censored requests (rejected, timed
// out, still outstanding at the deadline), and can split the run into
// mergeable per-interval deltas (checkpoints).
#include "src/oram/support/benchmark_histogram.hpp"

#include <memory>
#include <utility>
#include <vector>

namespace oram_bench {

enum class StatisticsMode { kFullEvents, kCheckpoints };
enum class Outcome { kRejected, kTimedOut, kOutstanding };

// One serialized API call, including partial batches and the scalar case.
// Every member keeps its own intended arrival; service is observed ONCE.
struct CompletionEvent {
  std::vector<uint64_t> intended_arrivals_ns;
  uint64_t dispatch_ns = 0;
  uint64_t completion_ns = 0;
  bool diagnostic_only = false;
};
// Non-owning view into the caller's preallocated batch buffer.
struct CompletionView {
  const uint64_t* arrivals = nullptr;
  size_t count = 0;
  uint64_t dispatch_ns = 0;
  uint64_t completion_ns = 0;
  bool diagnostic_only = false;
};
struct OutcomeEvent {
  Outcome outcome = Outcome::kRejected;
  uint64_t requests = 1;
  bool diagnostic_only = false;
};

struct Statistics {
  Histogram response;
  Histogram queue;
  Histogram service;
  uint64_t completed_requests = 0;
  uint64_t completed_batches = 0;
  uint64_t rejected = 0;
  uint64_t timed_out = 0;
  uint64_t outstanding = 0;

  uint64_t offered() const {
    return CheckedAdd(CheckedAdd(completed_requests, rejected), CheckedAdd(timed_out, outstanding));
  }
  bool uncensored() const { return !rejected && !timed_out && !outstanding; }
  void Validate() const {
    Require(response.count() == completed_requests && queue.count() == completed_requests &&
            service.count() == completed_batches && completed_batches <= completed_requests &&
            (completed_requests == 0) == (completed_batches == 0),
            "statistics counts/weighting disagree");
    Require(queue.sum_ns() <= response.sum_ns(), "queue exceeds response sum");
    Require(service.sum_ns() <= response.sum_ns() - queue.sum_ns(),
            "batch service exceeds request-weighted service sum");
    if (completed_batches == completed_requests)
      Require(service.sum_ns() == response.sum_ns() - queue.sum_ns(),
              "scalar service/response/queue sums disagree");
    (void)offered();
  }
  // In place: a checkpoint can close on the request thread, and a whole-object
  // copy of this ~350 KB struct would lengthen that pause.  Every sum is
  // checked before anything is written, so a failure leaves *this unchanged.
  // (Two valid statistics merge to a valid one: every Validate relation is
  // linear in the counts and sums.)
  void Merge(const Statistics& other) {
    other.Validate();
    const uint64_t requests = CheckedAdd(completed_requests, other.completed_requests);
    const uint64_t batches = CheckedAdd(completed_batches, other.completed_batches);
    const uint64_t rejected_total = CheckedAdd(rejected, other.rejected);
    const uint64_t timed_out_total = CheckedAdd(timed_out, other.timed_out);
    const uint64_t outstanding_total = CheckedAdd(outstanding, other.outstanding);
    (void)CheckedAdd(CheckedAdd(requests, rejected_total), CheckedAdd(timed_out_total, outstanding_total));
    response.CheckMerge(other.response);
    queue.CheckMerge(other.queue);
    service.CheckMerge(other.service);
    response.Merge(other.response);
    queue.Merge(other.queue);
    service.Merge(other.service);
    completed_requests = requests;
    completed_batches = batches;
    rejected = rejected_total;
    timed_out = timed_out_total;
    outstanding = outstanding_total;
  }
};

// A delta, never a cumulative snapshot. The interval partitions the log, not
// request arrivals: a completed request belongs to its completion interval.
struct CheckpointEvent {
  uint64_t interval_id = 0;
  uint64_t begin_ns = 0;
  uint64_t end_ns = 0;
  Statistics statistics;
  void Validate() const {
    Require(begin_ns < end_ns, "empty/reversed checkpoint interval");
    statistics.Validate();
  }
};

class StatsAccumulator {
 public:
  explicit StatsAccumulator(StatisticsMode mode = StatisticsMode::kFullEvents) : mode_(mode) {
    Require(mode == StatisticsMode::kFullEvents || mode == StatisticsMode::kCheckpoints,
            "unknown statistics mode");
  }

  void observe(const CompletionEvent& event) {
    observe(CompletionView{event.intended_arrivals_ns.data(),
                           event.intended_arrivals_ns.size(), event.dispatch_ns,
                           event.completion_ns, event.diagnostic_only});
  }

  void observe(const CompletionView& event) {
    Require(event.arrivals != nullptr && event.count > 0, "empty completed batch");
    Require(event.dispatch_ns <= event.completion_ns, "completion precedes dispatch");
    uint64_t response_sum = 0, queue_sum = 0;
    for (size_t i = 0; i < event.count; ++i) {
      const uint64_t arrival = event.arrivals[i];
      Require(arrival <= event.dispatch_ns, "dispatch precedes intended arrival");
      response_sum = CheckedAdd(response_sum, event.completion_ns - arrival);
      queue_sum = CheckedAdd(queue_sum, event.dispatch_ns - arrival);
    }
    if (event.diagnostic_only) return;  // Never double count sampled traces.
    Require(mode_ == StatisticsMode::kFullEvents, "full events mixed with checkpoints");
    if (last_completion_)
      Require(event.dispatch_ns >= *last_completion_, "serialized calls overlap or run backwards");
    // Preflight every possible overflow before touching the accumulator.
    const auto n = static_cast<uint64_t>(event.count);
    (void)CheckedAdd(stats_->offered(), n);
    (void)CheckedAdd(stats_->completed_batches, 1);
    (void)CheckedAdd(stats_->response.sum_ns(), response_sum);
    (void)CheckedAdd(stats_->queue.sum_ns(), queue_sum);
    (void)CheckedAdd(stats_->service.sum_ns(), event.completion_ns - event.dispatch_ns);
    for (size_t i = 0; i < event.count; ++i) {
      const uint64_t arrival = event.arrivals[i];
      stats_->response.Add(event.completion_ns - arrival);
      stats_->queue.Add(event.dispatch_ns - arrival);
    }
    stats_->service.Add(event.completion_ns - event.dispatch_ns);
    stats_->completed_requests += n;
    ++stats_->completed_batches;
    last_completion_ = event.completion_ns;
  }

  // Exactly one terminal outcome per offered request. A provisional backlog
  // observation is not an outcome; do not emit outstanding then completed.
  void observe(const OutcomeEvent& event) {
    Require(event.requests > 0, "empty outcome event");
    Require(event.outcome == Outcome::kRejected || event.outcome == Outcome::kTimedOut ||
            event.outcome == Outcome::kOutstanding, "unknown outcome");
    if (event.diagnostic_only) return;
    Require(mode_ == StatisticsMode::kFullEvents, "full events mixed with checkpoints");
    (void)CheckedAdd(stats_->offered(), event.requests);
    auto& count = event.outcome == Outcome::kRejected ? stats_->rejected :
        (event.outcome == Outcome::kTimedOut ? stats_->timed_out : stats_->outstanding);
    count = CheckedAdd(count, event.requests);
  }

  void observe(const CheckpointEvent& event) {
    Require(mode_ == StatisticsMode::kCheckpoints, "checkpoints mixed with full events");
    event.Validate();
    Require(event.interval_id == next_interval_, "duplicate, missing, or reordered checkpoint");
    Require(!last_end_ || event.begin_ns == *last_end_, "checkpoint overlap or gap");
    auto next = CheckedAdd(next_interval_, 1);
    stats_->Merge(event.statistics);
    next_interval_ = next;
    last_end_ = event.end_ns;
  }

  // Whole-run totals. Until the first checkpoint this is the open interval
  // itself; afterwards it merges the closed intervals, outside the timed path.
  const Statistics& finish() const {
    if (!checkpoints_) {
      stats_->Validate();
      return *stats_;
    }
    total_ = closed_;
    total_.Merge(*stats_);
    return total_;
  }

  // The same close as checkpoint(), split so a second thread can do the copying
  // and merging: Rotate swaps a zeroed interval in (a pointer move, nothing is
  // copied) and returns the one that was open; the other thread builds the
  // CheckpointEvent from it and Absorb()s it. Between the two, only the thread
  // that calls observe() may touch the open interval, and only the other thread
  // may touch the closed totals; finish() is for after both are done.
  std::unique_ptr<Statistics> Rotate(uint64_t end_ns, std::unique_ptr<Statistics> fresh) {
    Require(mode_ == StatisticsMode::kFullEvents, "cannot checkpoint checkpoint totals as a delta");
    Require(!last_completion_ || *last_completion_ <= end_ns, "checkpoint ends before completion");
    std::swap(stats_, fresh);
    return fresh;
  }
  void Absorb(const Statistics& interval) {
    closed_.Merge(interval);
    ++checkpoints_;
  }

  // Returns what was observed since the previous checkpoint (a delta) and
  // opens the next interval; finish() still reports whole-run totals.
  CheckpointEvent checkpoint(uint64_t interval_id, uint64_t begin_ns, uint64_t end_ns) {
    Require(mode_ == StatisticsMode::kFullEvents, "cannot checkpoint checkpoint totals as a delta");
    Require(!last_completion_ || *last_completion_ <= end_ns, "checkpoint ends before completion");
    CheckpointEvent result{interval_id, begin_ns, end_ns, *stats_};
    result.Validate();
    closed_.Merge(*stats_);
    *stats_ = Statistics{};
    ++checkpoints_;
    return result;
  }

 private:
  StatisticsMode mode_;
  std::unique_ptr<Statistics> stats_ = std::make_unique<Statistics>();  // the open interval
  Statistics closed_;  // merged closed intervals
  mutable Statistics total_;
  uint64_t checkpoints_ = 0;
  std::optional<uint64_t> last_completion_;
  std::optional<uint64_t> last_end_;
  uint64_t next_interval_ = 0;
};

}  // namespace oram_bench
