#pragma once

// RunTrial: the phased trial loop of the benchmark worker.  It drives an
// adapter (one public map call per Invoke) either as a closed loop
// (kSaturating: issue the next call as soon as the last returns, count
// completions per elapsed time) or as an open loop at a fixed offered rate
// (requests arrive on a schedule computed from public parameters, wait in a
// bounded queue, and are dispatched in batches).  For every open-loop call it
// reads the clock at dispatch and completion, so each request's latency is
// completion minus its *intended* arrival (queueing plus service), and feeds
// the streaming statistics in benchmark_statistics.hpp.  See DESIGN.md in this
// directory for the timing semantics.  Measurement code only: nothing here is
// part of the oblivious map.
#include "src/oram/support/benchmark_arrival.hpp"
#include "src/oram/support/benchmark_invocation.hpp"
#include "src/oram/support/benchmark_statistics.hpp"

#include <chrono>
#include <cmath>
#include <ctime>
#include <algorithm>
#include <condition_variable>
#include <deque>
#include <exception>
#include <functional>
#include <future>
#include <memory>
#include <mutex>
#include <optional>
#include <thread>
#include <type_traits>
#include <vector>

namespace oram_bench {

// Portable monotonic fallback. Origin construction and every timed interval
// stay in the worker. A fake clock implements the same Now/WaitUntil contract.
class SteadyClock {
 public:
  uint64_t Now() const {
    return static_cast<uint64_t>(std::chrono::duration_cast<std::chrono::nanoseconds>(
        std::chrono::steady_clock::now() - origin_).count());
  }
  void WaitUntil(uint64_t deadline) const { while (Now() < deadline) {} }
  // Absolute steady_clock time of this timebase's zero, so OS-clock samples
  // (memory.csv) can be placed on the trial's time axis.
  uint64_t OriginNs() const {
    return static_cast<uint64_t>(std::chrono::duration_cast<std::chrono::nanoseconds>(
        origin_.time_since_epoch()).count());
  }
 private:
  std::chrono::steady_clock::time_point origin_ = std::chrono::steady_clock::now();
};
// A timebase's absolute origin when it exposes one (fake clocks do not).
template <typename Clock>
auto ClockOriginNs(const Clock& clock, int) -> decltype(std::optional<uint64_t>(clock.OriginNs())) {
  return clock.OriginNs();
}
template <typename Clock> std::optional<uint64_t> ClockOriginNs(const Clock&, long) { return std::nullopt; }
template <typename Clock> std::optional<uint64_t> ClockOriginNs(const Clock& clock) {
  return ClockOriginNs(clock, 0);
}

struct PendingRequest { uint64_t id = 0, arrival_ns = 0; };
// At this batch size a clock read per call is negligible next to the 16 or more
// accesses the call performs.
inline constexpr size_t kClockEveryCallBatch = 16;
// Bound on histogram checkpoint blocks per trial (each is about 350 KB).
inline constexpr uint64_t kMaxCheckpointBlocks = 4096;
struct TrialOptions {
  ScheduleSpec schedule;
  uint64_t horizon_ns = 1000000000;
  uint64_t drain_ns = 1000000000;  // deadline is horizon + drain_ns
  size_t batch_size = 1;
  size_t queue_limit = 65536;     // waiting requests, excluding active batch
  uint64_t batch_timeout_ns = 0; // zero means fixed_count
  // Saturation windows count requests, so a window's span does not grow with
  // the batch size. The clock is read at every window boundary, and on every
  // call at batch >= kClockEveryCallBatch, which bounds horizon overshoot.
  uint64_t window_requests = 1024;
  uint64_t minimum_tail_count = 100;
  bool service_timing = false;
  // A "settle" is an unmeasured pre-measurement phase of a fixed request
  // count (after warmup) that lets background maintenance reach steady state.
  // A settle's offered-load batches still flush at horizon_ns, so a settle
  // that should form full batches throughout passes horizon_ns = UINT64_MAX.
  bool stop_at_request_cap = false; // count-only settle, never a publication horizon
  bool finish_pending = true;   // false only for settle
  uint64_t first_request_id = 0;
  // Offered-load histogram checkpoints: one delta per nonoverlapping block of
  // this many ns of completion time (zero: one block), so per-block
  // uncertainty stays available without full events.
  bool checkpoints = false;
  uint64_t checkpoint_interval_ns = 0;
  // Close checkpoint blocks on a second thread: the request thread only swaps
  // in a zeroed interval (pointer move); the copy of the closed one (about
  // 350 KB), its validation and the merge into the totals happen elsewhere.
  // Inline closes (false) reserve every block of the trial before the clock
  // origin, so the checkpoint vector never reallocates on the request thread.
  bool checkpoint_thread = false;
  std::function<void()> checkpoint_thread_init;  // placement hook for that thread
};
struct TrialResult {
  uint64_t minimum_tail_count = 100;
  StatsAccumulator accumulator;
  std::vector<uint64_t> batch_size_counts;
  std::vector<CheckpointEvent> checkpoints;  // consecutive deltas, if requested
  Histogram saturated_service;
  // admitted = offered - rejected: a request is admitted when it enters the
  // queue, even if it is later censored as outstanding.
  uint64_t offered = 0, admitted = 0, completed = 0, calls = 0;
  uint64_t completed_during_horizon = 0;
  uint64_t peak_queue = 0;
  uint64_t caller_end_ns = 0, drain_end_ns = 0;
  bool request_cap_reached = false, deadline_exceeded = false;
  // Times the request thread had to wait for the checkpoint thread to return a
  // spare interval (a block closed before the last one was finished).
  uint64_t checkpoint_stalls = 0;
  uint64_t checkpoint_cpu_ns = 0;  // the checkpoint thread's CPU time (harness, not library)
};

struct NullTrialSink {
  void Begin(const TrialOptions&) {}
  template <typename Clock> void ClockInfo(const Clock&) {}
  void Offered(PendingRequest) {}
  void SaturatedService(uint64_t, size_t) {}
  void Completion(const PendingRequest*, size_t, InvocationTiming, uint64_t) {}
  void Censored(PendingRequest, Outcome) {}
  void Window(uint64_t, uint64_t, uint64_t) {}
  void Finish(const TrialResult&) {}
};

// Coarse lifecycle notifications only: observers must not block or allocate.
// Drain here means the final maintenance barrier, after the request cohort.
enum class TrialPhase { kMeasure, kDrain, kLogFlush };
struct NullTrialObserver {
  void operator()(TrialPhase) const {}
};

// A second thread that builds the checkpoint events. The request thread hands
// it each closed interval (one lock and a pointer move per block, about once a
// second) and takes a zeroed spare back; the thread copies the interval into
// its CheckpointEvent, merges it into the totals and zeroes it for reuse.
// The constructor returns once the thread has run its startup hook (for
// example placement), and rethrows the hook's failure.
class CheckpointThread {
 public:
  CheckpointThread(TrialResult& result, std::function<void()> init, size_t spares = 3)
      : result_(result) {
    for (size_t i = 0; i < spares; ++i) spare_.push_back(std::make_unique<Statistics>());
    std::promise<void> ready;
    auto started = ready.get_future();
    worker_ = std::thread([this, init = std::move(init), ready = std::move(ready)]() mutable {
      try { if (init) init(); }
      catch (...) { ready.set_exception(std::current_exception()); return; }
      ready.set_value();
      Run();
    });
    try { started.get(); }
    catch (...) { worker_.join(); throw; }
  }
  CheckpointThread(const CheckpointThread&) = delete;
  CheckpointThread& operator=(const CheckpointThread&) = delete;
  ~CheckpointThread() {
    try { Join(); } catch (...) {}
  }
  // Request thread: close the open interval as block `id` covering (begin, end].
  void Close(uint64_t id, uint64_t begin, uint64_t end) {
    std::unique_lock<std::mutex> lock(mutex_);
    if (spare_.empty() && !error_) {
      ++stalls_;
      changed_.wait(lock, [&] { return !spare_.empty() || error_; });
    }
    if (error_) { lock.unlock(); Join(); }  // rethrows
    auto fresh = std::move(spare_.back());
    spare_.pop_back();
    lock.unlock();
    auto filled = result_.accumulator.Rotate(end, std::move(fresh));
    lock.lock();
    jobs_.push_back(Job{id, begin, end, std::move(filled)});
    changed_.notify_all();
  }
  // Waits for every posted block, stops the thread and rethrows its failure.
  void Join() {
    if (worker_.joinable()) {
      {
        std::lock_guard<std::mutex> lock(mutex_);
        stop_ = true;
      }
      changed_.notify_all();
      worker_.join();
    }
    if (error_) { auto e = error_; error_ = nullptr; std::rethrow_exception(e); }
  }
  uint64_t stalls() const { return stalls_; }
  uint64_t cpu_ns() const { return cpu_ns_; }  // only after Join

 private:
  struct Job { uint64_t id, begin, end; std::unique_ptr<Statistics> filled; };
  void Run() {
    struct RecordCpu {
      uint64_t& out;
      ~RecordCpu() {
        timespec t{};
        if (!clock_gettime(CLOCK_THREAD_CPUTIME_ID, &t)) out = uint64_t(t.tv_sec) * 1000000000u + uint64_t(t.tv_nsec);
      }
    } record{cpu_ns_};
    try {
      for (;;) {
        Job job;
        {
          std::unique_lock<std::mutex> lock(mutex_);
          changed_.wait(lock, [&] { return !jobs_.empty() || stop_; });
          if (jobs_.empty()) return;
          job = std::move(jobs_.front());
          jobs_.pop_front();
        }
        CheckpointEvent event{job.id, job.begin, job.end, *job.filled};
        event.Validate();
        result_.accumulator.Absorb(*job.filled);
        result_.checkpoints.push_back(std::move(event));
        *job.filled = Statistics{};
        {
          std::lock_guard<std::mutex> lock(mutex_);
          spare_.push_back(std::move(job.filled));
        }
        changed_.notify_all();
      }
    } catch (...) {
      std::lock_guard<std::mutex> lock(mutex_);
      error_ = std::current_exception();
      changed_.notify_all();
    }
  }
  TrialResult& result_;
  std::mutex mutex_;
  std::condition_variable changed_;
  std::deque<Job> jobs_;
  std::vector<std::unique_ptr<Statistics>> spare_;
  std::exception_ptr error_;
  bool stop_ = false;
  uint64_t stalls_ = 0;
  uint64_t cpu_ns_ = 0;
  std::thread worker_;
};

// Closes every checkpoint block that ends before t: a block holds completions
// in (begin, end]. Out of line, and called only when a block is due: a
// checkpoint copies three whole histograms (about 350 KB) through temporaries.
// Inlined into the per-iteration test, its stack frame (over 1 MiB, probed
// page by page under -fstack-clash-protection) would be paid on every
// iteration of the offered-load loop and inflate every service bracket.
__attribute__((noinline))
inline void CloseCheckpointBlocks(uint64_t t, uint64_t interval, uint64_t& block_begin,
                                  uint64_t& next_block, uint64_t& next_id, TrialResult& result,
                                  CheckpointThread* thread = nullptr) {
  while (t > next_block) {
    if (thread) thread->Close(next_id, block_begin, next_block);
    else result.checkpoints.push_back(result.accumulator.checkpoint(next_id, block_begin, next_block));
    ++next_id;
    block_begin = next_block;
    next_block = next_block > UINT64_MAX - interval ? UINT64_MAX : next_block + interval;
  }
}

// A sink that records individual requests (arrivals, rejections, censoring)
// overrides Offered or Censored; the trial loop spends nothing on a sink that does not.
template <typename Sink>
struct LogsRequests : std::bool_constant<
    !std::is_same_v<decltype(&Sink::Offered), decltype(&NullTrialSink::Offered)> ||
    !std::is_same_v<decltype(&Sink::Censored), decltype(&NullTrialSink::Censored)>> {};

// Adapter contract: Prepare(PendingRequest*, count), Invoke(clock,timed,count),
// Consume(count), Finish(). Offered-load trials invoke untimed and take the
// dispatch/completion reads themselves. All buffers, including event storage,
// are created before Timebase's origin. Sink methods must copy into bounded
// storage only.
// A single public call cannot be interrupted; overruns are reported after it
// returns and the common finish barrier has completed, never hidden.
template <typename Timebase = SteadyClock, typename Adapter, typename Sink,
          typename Observer = NullTrialObserver>
TrialResult RunTrial(const TrialOptions& options, Adapter& adapter, Sink& sink,
                     Observer observer = {}) {
  const ScheduleSpec& spec = options.schedule;
  const bool saturated = spec.profile == ArrivalProfile::kSaturating;
  Require(options.horizon_ns && options.drain_ns && options.batch_size &&
          options.queue_limit >= options.batch_size && options.window_requests &&
          options.schedule.num_accesses && options.minimum_tail_count,
          "invalid trial horizon, capacity, batch or window limits");
  // A count-only settle has no deadline: it ends after its request count, however long that takes (the
  // coordinator's per-trial cap bounds it). A settle of a large, slow map can legitimately take longer
  // than the measurement window plus drain, so horizon + drain must not bound it.
  const uint64_t deadline = options.stop_at_request_cap ? UINT64_MAX
                                                        : CheckedAdd(options.horizon_ns, options.drain_ns);
  Require(options.schedule.num_accesses <= UINT64_MAX - options.first_request_id,
          "trial request IDs exhaust version space");
  std::vector<PendingRequest> batch(options.batch_size);
  std::vector<uint64_t> arrivals(options.batch_size);
  TrialResult result;
  result.minimum_tail_count = options.minimum_tail_count;
  result.batch_size_counts.resize(options.batch_size + 1);
  // Checkpoint storage and its thread are ready before the clock origin, so
  // their allocation and thread start are not an initial backlog. The
  // reservation is not touched here: each block's pages are faulted when the
  // block is written. A checkpoint holds three full histograms (about 350 KB).
  // Inline closes run on the request thread, so the vector is reserved for
  // every block up to the deadline and never moves while requests are served.
  // With the checkpoint thread the growth runs on that thread: the reservation
  // covers the horizon, at most 256 blocks, and later blocks may grow it.
  const bool blocks = !saturated && options.checkpoints;
  const uint64_t interval = options.checkpoint_interval_ns;
  // Each block holds about 350 KB, so the block count bounds this trial's memory.
  Require(!blocks || !interval || deadline / interval <= kMaxCheckpointBlocks,
          "checkpoint interval allows more than 4096 blocks over horizon plus drain");
  std::unique_ptr<CheckpointThread> checkpoint_thread;
  if (blocks)
    result.checkpoints.reserve(!interval ? 1
        : options.checkpoint_thread ? std::min<uint64_t>(options.horizon_ns / interval + 2, 256)
                                    : deadline / interval + 2);
  if (blocks && options.checkpoint_thread)  // after the reserve: the vector is theirs from here
    checkpoint_thread = std::make_unique<CheckpointThread>(result, options.checkpoint_thread_init);
  sink.Begin(options);
  observer(TrialPhase::kMeasure);
  Timebase clock;
  sink.ClockInfo(clock);
  if (saturated) {
    uint64_t window_begin = 0, window_count = 0;
    uint64_t now = 0;
    const bool read_every_call = options.batch_size >= kClockEveryCallBatch;
    // A count-only settle is bounded by its request count, not the horizon.
    const bool timed_horizon = !options.stop_at_request_cap;
    while (result.completed < options.schedule.num_accesses &&
           (!timed_horizon || now < options.horizon_ns)) {
      const size_t count = std::min<uint64_t>(options.batch_size,
          options.schedule.num_accesses - result.completed);
      for (size_t k = 0; k < count; ++k)
        batch[k] = {options.first_request_id + result.completed + k, 0};
      adapter.Prepare(batch.data(), count);
      const auto timing = adapter.Invoke(clock, options.service_timing, count);
      adapter.Consume(count);
      result.completed += count;
      ++result.batch_size_counts[count];
      ++result.calls;
      window_count += count;
      if (options.service_timing) {
        result.saturated_service.Add(timing.end - timing.start);
        sink.SaturatedService(timing.end - timing.start, count);
      }
      const bool window_full = window_count >= options.window_requests ||
          result.completed == options.schedule.num_accesses;
      if (window_full || read_every_call) now = clock.Now();
      if (window_full || (timed_horizon && now >= options.horizon_ns)) {
        sink.Window(window_begin, now, window_count);
        window_begin = now;
        window_count = 0;
      }
    }
    result.offered = result.admitted = result.completed;
    result.caller_end_ns = clock.Now();
    // No per-call completion timestamps: do not invent a precise count at T.
    result.request_cap_reached = !options.stop_at_request_cap &&
                                result.completed == options.schedule.num_accesses &&
                                result.caller_end_ns < options.horizon_ns;
  } else {
    // Request k arrives at arrival.At(k) (with its whole group when requests
    // arrive in groups). The waiting requests are therefore the id range
    // [completed, offered): nothing is stored or copied per request.
    const FixedArrivals arrival(spec.rate_kops, spec.arrival_group);
    const uint64_t cap = options.schedule.num_accesses;
    // The cohort: every arrival before the horizon (a count-only settle has no
    // horizon), at most `cap` of them. Whatever is unserved at the deadline is
    // censored, so the totals always add up to it.
    const uint64_t in_horizon = options.stop_at_request_cap ? UINT64_MAX : arrival.Before(options.horizon_ns);
    const uint64_t total = std::min(cap, in_horizon);
    result.request_cap_reached = !options.stop_at_request_cap && cap < in_horizon;
    constexpr bool logs_requests = LogsRequests<Sink>::value;
    uint64_t block_begin = 0, next_block = blocks && interval ? interval : UINT64_MAX, next_id = 0;
    // Close every block that ends before t, before observing anything at t.
    // The final block always starts before the drain end and ends exactly at it.
    auto close_blocks = [&](uint64_t t) {
      if (t > next_block)
        CloseCheckpointBlocks(t, interval, block_begin, next_block, next_id, result, checkpoint_thread.get());
    };
    // One clock read per served call. `now` is the read that completed the last
    // call (back to back while requests are waiting) or the one after the last
    // wait (idle, where a read costs nothing). A request that was already
    // waiting is dispatched at the previous completion, so its service bracket
    // also holds the harness's work between the two calls: the previous call's
    // Consume (hit checks, the checksum over every returned value, value
    // verification under `full`), the statistics and sink updates, and this
    // call's Prepare. For a 64-request batch that is on the order of a
    // microsecond or more; a call dispatched after an idle wait carries only
    // its own Prepare. Its response time, completion read less its computed
    // arrival, is exact.
    uint64_t offered = 0;
    uint64_t next_arrival = total ? arrival.At(0) : UINT64_MAX;  // arrival of id `offered`
    uint64_t now = clock.Now();
    while (result.completed < total) {
      if (next_arrival <= now) {  // implies offered < total
        if constexpr (logs_requests) {
          while (offered < total && next_arrival <= now) {
            sink.Offered({options.first_request_id + offered, next_arrival});
            ++offered;
            next_arrival = offered < total ? arrival.At(offered) : UINT64_MAX;
          }
        } else {
          // One step covers the usual single arrival. A longer backlog (after a
          // stall) is counted, not walked: stepping through it would delay the
          // next call, and the deadline check, by work proportional to it.
          ++offered;
          next_arrival = offered < total ? arrival.At(offered) : UINT64_MAX;
          if (next_arrival <= now) {
            offered = std::min(total, arrival.Before(now + 1));
            next_arrival = offered < total ? arrival.At(offered) : UINT64_MAX;
          }
        }
      }
      const uint64_t waiting = offered - result.completed;
      if (waiting > result.peak_queue) result.peak_queue = waiting;
      // A request log keeps every waiting request in memory when it is replayed.
      if constexpr (logs_requests)
        Require(waiting <= options.queue_limit, "request log would exceed its declared queue bound");
      if (now >= deadline) {
        result.deadline_exceeded = true;
        break;
      }
      if (!waiting) {
        clock.WaitUntil(std::min(next_arrival, deadline));
        now = clock.Now();
        continue;
      }
      uint64_t timeout_at = UINT64_MAX;
      if (options.batch_timeout_ns) {
        const uint64_t oldest = arrival.At(result.completed);
        timeout_at = options.batch_timeout_ns > UINT64_MAX - oldest ? UINT64_MAX : oldest + options.batch_timeout_ns;
      }
      const bool ready = waiting >= options.batch_size ||
          (options.stop_at_request_cap && offered == total) || now >= options.horizon_ns ||
          now >= timeout_at;
      if (!ready) {
        const uint64_t wake = std::min({offered < total ? std::min(next_arrival, options.horizon_ns) : options.horizon_ns,
                                        timeout_at, deadline});
        clock.WaitUntil(wake);
        now = clock.Now();
        continue;
      }
      const size_t count = std::min<uint64_t>(waiting, options.batch_size);
      for (size_t k = 0; k < count; ++k) {
        const uint64_t id = result.completed + k;
        arrivals[k] = arrival.At(id);
        batch[k] = {options.first_request_id + id, arrivals[k]};
      }
      adapter.Prepare(batch.data(), count);
      // `now` already passed the deadline check, so it is the dispatch time
      // (dispatch < deadline holds for live and replay alike); preparation
      // cost lands in the service bracket rather than in a second read.
      const uint64_t dispatched_at = now;
      adapter.Invoke(clock, false, count);
      now = clock.Now();
      const InvocationTiming timing{dispatched_at, now};
      adapter.Consume(count);
      if (timing.end > next_block) {
        close_blocks(timing.end);
        // An inline close (tens of us) must not land in the next call's
        // service bracket: re-read, so the next dispatch follows it.
        if (!checkpoint_thread) now = clock.Now();
      }
      result.accumulator.observe(CompletionView{arrivals.data(), count, timing.start, timing.end, false});
      sink.Completion(batch.data(), count, timing, result.calls);
      result.completed += count;
      if (timing.end < options.horizon_ns) result.completed_during_horizon += count;
      ++result.batch_size_counts[count];
      ++result.calls;
    }
    if (const uint64_t unserved = total - result.completed) {
      result.accumulator.observe(OutcomeEvent{Outcome::kOutstanding, unserved, false});
      if constexpr (logs_requests) {
        for (uint64_t id = result.completed; id < total; ++id) {
          const PendingRequest request{options.first_request_id + id, arrival.At(id)};
          if (id >= offered) sink.Offered(request);
          sink.Censored(request, Outcome::kOutstanding);
        }
      }
    }
    result.offered = result.admitted = total;
    // This rate's denominator covers the whole offered horizon, including idle
    // time after its last completion, and subsequent cohort result processing.
    if (!options.stop_at_request_cap) clock.WaitUntil(options.horizon_ns);
    result.caller_end_ns = clock.Now();
    if (options.finish_pending) {
      observer(TrialPhase::kDrain);
      adapter.Finish();
    }
    result.drain_end_ns = clock.Now();
    // Blocks keep the declared length through the drain; the last one ends at
    // the drain end and holds everything still open.
    if (blocks) close_blocks(result.drain_end_ns);
    if (checkpoint_thread) {
      checkpoint_thread->Join();
      result.checkpoint_stalls = checkpoint_thread->stalls();
      result.checkpoint_cpu_ns = checkpoint_thread->cpu_ns();
    }
    if (blocks)
      result.checkpoints.push_back(result.accumulator.checkpoint(next_id, block_begin,
          std::max(result.drain_end_ns, block_begin + 1)));  // max() only for a zero-length trial
    Require(result.accumulator.finish().offered() == result.offered,
            "trial cohort accounting mismatch");
  }
  if (saturated) {
    if (options.finish_pending) {
      observer(TrialPhase::kDrain);
      adapter.Finish();
    }
    result.drain_end_ns = clock.Now();
  }
  observer(TrialPhase::kLogFlush);
  result.deadline_exceeded |= result.drain_end_ns > deadline;
  sink.Finish(result);
  return result;
}
}  // namespace oram_bench
