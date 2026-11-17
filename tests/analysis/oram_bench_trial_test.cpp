// Unit test for the trial loop (src/oram/support/benchmark_trial.hpp) on a
// deterministic fake clock: dispatch and response timing, grouped and
// offered-load arrivals, overload censoring at the drain deadline, periodic
// checkpoints (inline and on the checkpoint thread), saturation limits,
// workload correctness checks and phase notifications.  No ORAM is built.
#include "src/oram/support/benchmark_trial.hpp"
#include "benchmarks/support/prepared_workload.hpp"
#include "benchmarks/support/fake_backend.hpp"
#include <algorithm>
#include <iostream>
#include <numeric>
#include <memory>

namespace ob = oram_bench;
void Check(bool b, const char* message) { if (!b) throw std::runtime_error(message); }
struct Clock {
  static inline uint64_t now = 0, reads = 0, read_cost = 0;
  Clock() { now = reads = 0; }
  uint64_t Now() { ++reads; const auto t = now; now += read_cost; return t; }
  void WaitUntil(uint64_t t) { now = std::max(now, t); }
};
struct Delayed {
  uint64_t prepare = 2, service = 3, consume = 5, finish = 7;
  size_t prepared = 0, invoked = 0, consumed = 0, finishes = 0;
  void Prepare(const ob::PendingRequest*, size_t n) { prepared += n; Clock::now += prepare; }
  ob::InvocationTiming Invoke(Clock& c, bool timed, size_t n) {
    return ob::InvokePrepared(c, timed, [&] { invoked += n; Clock::now += service * n; });
  }
  void Consume(size_t n) { consumed += n; Clock::now += consume; }
  void Finish() { ++finishes; Clock::now += finish; }
};
struct Sink : ob::NullTrialSink {
  std::vector<uint64_t> ids, starts, ends;
  std::vector<ob::Outcome> outcomes;
  void Completion(const ob::PendingRequest* p, size_t n, ob::InvocationTiming t, uint64_t) {
    for (size_t i = 0; i < n; ++i) {
      ids.push_back(p[i].id); starts.push_back(t.start); ends.push_back(t.end);
    }
  }
  void Censored(ob::PendingRequest p, ob::Outcome outcome) { ids.push_back(p.id); outcomes.push_back(outcome); }
};
ob::TrialOptions Options() {
  ob::TrialOptions o;
  o.horizon_ns = 100; o.drain_ns = 100; o.queue_limit = 4;
  o.schedule.num_accesses = 100;
  o.schedule.rate_kops = 100000; // 10 ns spacing
  return o;
}
void Timings() {
  for (size_t batch : {size_t{1}, size_t{4}}) {
    for (bool timeout : {false, true}) {
      auto o = Options(); o.batch_size = batch; o.batch_timeout_ns = timeout ? 12 : 0;
      Delayed adapter; Sink sink;
      const auto r = ob::RunTrial<Clock>(o, adapter, sink);
      Check(r.offered == 10 && r.completed == 10 && r.admitted == 10 &&
            r.accumulator.finish().uncensored(), "cohort count lost");
      Check(!r.request_cap_reached && !r.deadline_exceeded, "valid horizon marked incomplete");
      const uint64_t caller = batch == 1 ? 100 : timeout ? 105 : 113;
      Check(r.caller_end_ns == caller && r.drain_end_ns == caller + 7,
            "caller/drain denominators exclude adapter costs");
      const auto& stats = r.accumulator.finish();
      // Dispatch is the read that admitted the call, so the bracket holds the
      // adapter's preparation (2 per call) as well as the 3 per request of work.
      Check(stats.service.sum_ns() == 30 + 2 * r.calls && stats.service.count() == r.calls,
            "service bracket is not dispatch read to completion read, or uses request weighting");
      Check(sink.starts[0] == (batch == 1 ? 0 : timeout ? 12 : 30),
            "batch wait disappeared from dispatch");
      uint64_t batched = 0;
      for (size_t n = 1; n < r.batch_size_counts.size(); ++n) batched += n * r.batch_size_counts[n];
      Check(batched == 10 && adapter.finishes == 1, "partial batches or finish lost");
      if (batch == 4) Check(r.completed_during_horizon == 8, "horizon is not half-open");
    }
  }
}
// A batch whose requests arrive together is dispatched at its arrival, with
// no wait for later requests, and each response runs from that arrival.
void GroupArrivals() {
  auto o = Options(); o.batch_size = 4; o.schedule.arrival_group = 4;  // a group of 4 every 40 ns
  Delayed adapter; Sink sink;
  const auto r = ob::RunTrial<Clock>(o, adapter, sink);
  Check(r.offered == 12 && r.completed == 12 && r.batch_size_counts[4] == 3 && r.calls == 3,
        "groups before the horizon are not whole batches");
  Check(sink.starts[0] == 0 && sink.starts[4] == 40 && sink.starts[8] == 80, "a group waited to be dispatched");
  const auto& stats = r.accumulator.finish();
  // Each call: preparation 2 + service 3 x 4 = 14 ns from the group's arrival.
  Check(stats.response.sum_ns() == 12 * 14 && stats.queue.sum_ns() == 0, "grouped response not from arrival");
}
// Offered load beyond what the adapter serves is not shed: the waiting range
// grows, and whatever is unserved at the drain deadline is censored, so every
// scheduled request is accounted for. A sink that logs requests refuses it,
// because replaying such a log keeps every waiting request in memory.
void Overload() {
  auto o = Options(); o.drain_ns = 10;
  Delayed adapter; adapter.prepare = adapter.consume = 0; adapter.service = 30;
  ob::NullTrialSink quiet;
  const auto r = ob::RunTrial<Clock>(o, adapter, quiet);
  const auto& s = r.accumulator.finish();
  Check(r.offered == 10 && r.completed == 4 && s.rejected == 0 && s.outstanding == 6,
        "unbounded-backlog overload accounting differs");
  Check(r.admitted == 10 && r.peak_queue == 7 && r.deadline_exceeded && adapter.finishes == 1,
        "backlog peak or finish after overrun lost");
  // The log of the same trial would hold a seven-request backlog against a limit of two.
  o.queue_limit = 2;
  adapter = {}; adapter.prepare = adapter.consume = 0; adapter.service = 30;
  bool refused = false;
  Sink logging;
  try { ob::RunTrial<Clock>(o, adapter, logging); } catch (const std::invalid_argument&) { refused = true; }
  Check(refused, "a request log exceeded its declared queue bound");
  // Preparation that crosses the drain deadline is not hidden: the call was
  // admitted before it, so it is served and the overrun is reported.
  o = Options(); o.drain_ns = 10;
  adapter = {}; adapter.prepare = 111;
  const auto late = ob::RunTrial<Clock>(o, adapter, quiet);
  Check(late.completed == 1 && late.deadline_exceeded && adapter.finishes == 1 &&
        late.accumulator.finish().outstanding == 9,
        "preparation crossing the drain deadline was not reported as an overrun");
}
// One clock read per served call: the dispatch time is the previous completion
// read (or the wait's read), never a read of its own, so every call's bracket is
// the time from its dispatch to its completion read, preparation included.
void DispatchIsPreviousRead() {
  struct Recording : ob::NullTrialSink {
    std::vector<uint64_t> starts;
    uint64_t deadline = 0;
    void Begin(const ob::TrialOptions& o) { deadline = o.horizon_ns + o.drain_ns; }
    void Completion(const ob::PendingRequest*, size_t, ob::InvocationTiming t, uint64_t) {
      starts.push_back(t.start);
    }
  };
  for (uint64_t prepare = 0; prepare < 40; ++prepare) {
    auto o = Options(); o.queue_limit = 2; o.drain_ns = 10;
    Delayed adapter; adapter.prepare = prepare; adapter.consume = 0; adapter.service = 30;
    Recording sink;
    Clock::read_cost = 1;
    const auto r = ob::RunTrial<Clock>(o, adapter, sink);
    Clock::read_cost = 0;
    Check(r.calls == sink.starts.size(), "completion count differs from calls");
    for (auto start : sink.starts) Check(start < sink.deadline, "dispatch at or after the drain deadline");
    Check(r.accumulator.finish().service.sum_ns() == r.calls * (prepare + 30 + 1),
          "service bracket is not dispatch read to completion read");
  }
}
// Histogram checkpoints per time block are consecutive deltas whose merge is
// exactly the uncheckpointed result; the last block ends at the drain end.
void PeriodicCheckpoints() {
  for (uint64_t interval : {uint64_t{0}, uint64_t{30}, uint64_t{7}}) {
    auto o = Options(); o.checkpoints = true; o.checkpoint_interval_ns = interval;
    Delayed adapter; Sink sink;
    const auto r = ob::RunTrial<Clock>(o, adapter, sink);
    const size_t expected = interval ? (r.drain_end_ns + interval - 1) / interval : 1;
    Check(r.checkpoints.size() == expected, "checkpoint block count differs from the interval");
    auto merged = std::make_unique<ob::StatsAccumulator>(ob::StatisticsMode::kCheckpoints);
    for (const auto& checkpoint : r.checkpoints) merged->observe(checkpoint);
    const auto& whole = r.accumulator.finish();
    const auto& parts = merged->finish();
    Check(parts.response.bins() == whole.response.bins() && parts.queue.bins() == whole.queue.bins() &&
          parts.service.bins() == whole.service.bins() && parts.offered() == whole.offered(),
          "merged checkpoint deltas differ from the trial totals");
    Check(r.checkpoints.front().begin_ns == 0 && r.checkpoints.back().end_ns == r.drain_end_ns,
          "checkpoint blocks do not cover the trial");
  }
}
// Closing checkpoint blocks on a second thread must give exactly the inline
// result (the deterministic clock is only read by the request thread), in
// ordinary, overloaded and long trials with many more blocks than spare
// intervals, so the request thread has to wait for returned ones.
void SameStatistics(const ob::TrialResult& a, const ob::TrialResult& b, const char* what) {
  const auto& x = a.accumulator.finish();
  const auto& y = b.accumulator.finish();
  Check(x.response.bins() == y.response.bins() && x.queue.bins() == y.queue.bins() &&
        x.service.bins() == y.service.bins() && x.completed_requests == y.completed_requests &&
        x.completed_batches == y.completed_batches && x.rejected == y.rejected &&
        x.timed_out == y.timed_out && x.outstanding == y.outstanding &&
        x.response.sum_ns() == y.response.sum_ns(), what);
  Check(a.checkpoints.size() == b.checkpoints.size(), what);
  for (size_t i = 0; i < a.checkpoints.size(); ++i) {
    const auto &p = a.checkpoints[i], &q = b.checkpoints[i];
    Check(p.interval_id == q.interval_id && p.begin_ns == q.begin_ns && p.end_ns == q.end_ns &&
          p.statistics.response.bins() == q.statistics.response.bins() &&
          p.statistics.service.bins() == q.statistics.service.bins() &&
          p.statistics.rejected == q.statistics.rejected &&
          p.statistics.outstanding == q.statistics.outstanding, what);
  }
  Check(a.offered == b.offered && a.completed == b.completed && a.calls == b.calls &&
        a.drain_end_ns == b.drain_end_ns, what);
}
struct Completions : ob::NullTrialSink {  // does not log requests, so overload is allowed
  std::vector<uint64_t> ids;
  void Completion(const ob::PendingRequest* p, size_t n, ob::InvocationTiming, uint64_t) {
    for (size_t i = 0; i < n; ++i) ids.push_back(p[i].id);
  }
};
void CheckpointThreadMatchesInline() {
  for (uint64_t interval : {uint64_t{0}, uint64_t{30}, uint64_t{7}}) {
    for (size_t batch : {size_t{1}, size_t{4}}) {
      for (int scenario = 0; scenario < 4; ++scenario) {
        auto o = Options(); o.checkpoints = true; o.checkpoint_interval_ns = interval; o.batch_size = batch;
        Delayed delayed;
        if (scenario == 1) { o.queue_limit = batch == 1 ? 2 : 4; o.drain_ns = 10; delayed.prepare = delayed.consume = 0; delayed.service = 30; }
        if (scenario == 2) { o.queue_limit = batch == 1 ? 2 : 4; o.drain_ns = 10; delayed.prepare = 111; }
        if (scenario == 3) {  // hundreds of blocks
          o.horizon_ns = 400000; o.drain_ns = 100000; o.queue_limit = 64;
          o.schedule.num_accesses = 40000; o.schedule.rate_kops = 100000;
          o.checkpoint_interval_ns = interval ? interval * 100 : 0;  // 166 or 714 blocks, under the 4096 cap
        }
        Delayed inline_adapter = delayed, threaded_adapter = delayed;
        Completions s1, s2;
        const auto inline_result = ob::RunTrial<Clock>(o, inline_adapter, s1);
        o.checkpoint_thread = true;
        const auto threaded = ob::RunTrial<Clock>(o, threaded_adapter, s2);
        SameStatistics(inline_result, threaded, "checkpoint thread changed the statistics");
        Check(s1.ids == s2.ids, "checkpoint thread changed what the sink saw");
        if (scenario == 3 && interval) Check(threaded.checkpoints.size() > 100, "many-block scenario did not run");
      }
    }
  }
}
// The checkpoint thread is placed and running before the clock origin, and a
// failure of its startup hook fails the trial instead of terminating.
bool checkpoint_thread_started = false;
struct OriginSink : Completions {
  bool started_at_origin = false;
  template <typename C> void ClockInfo(const C&) { started_at_origin = checkpoint_thread_started; }
};
void CheckpointThreadStartup() {
  {  // The block count bounds checkpoint memory (about 350 KB a block), in the trial itself.
    auto o = Options(); o.checkpoints = true; o.checkpoint_interval_ns = 1;
    o.horizon_ns = 4096; o.drain_ns = 1;
    Delayed adapter; Completions sink;
    bool refused = false;
    try { ob::RunTrial<Clock>(o, adapter, sink); } catch (const std::invalid_argument&) { refused = true; }
    Check(refused, "a trial accepted more than 4096 checkpoint blocks");
  }
  auto o = Options(); o.checkpoints = true; o.checkpoint_thread = true;
  o.checkpoint_thread_init = [] { checkpoint_thread_started = true; };
  Delayed adapter; OriginSink sink;
  ob::RunTrial<Clock>(o, adapter, sink);
  Check(sink.started_at_origin, "checkpoint thread started after the clock origin");
  o.checkpoint_thread_init = [] { throw std::invalid_argument("duplicate placed role or CPU"); };
  bool failed = false;
  try { ob::RunTrial<Clock>(o, adapter, sink); } catch (const std::invalid_argument&) { failed = true; }
  Check(failed, "checkpoint thread startup failure was not propagated");
}
// A sink that logs nothing counts a backlog instead of walking it: a stall far
// past the deadline is accounted for in full.
void LongStallBacklog() {
  auto o = Options();
  o.horizon_ns = 50000000; o.drain_ns = 50000000;
  o.schedule.num_accesses = 100000000; o.schedule.rate_kops = 1000000;  // 1 ns spacing
  Delayed adapter; adapter.prepare = adapter.consume = 0; adapter.service = 200000000;
  ob::NullTrialSink quiet;
  const auto r = ob::RunTrial<Clock>(o, adapter, quiet);
  Check(r.completed == 1 && r.offered == 50000000 && r.peak_queue == 50000000 - 1 &&
        r.deadline_exceeded && r.accumulator.finish().outstanding == 50000000 - 1,
        "a counted backlog differs from the cohort");
}
void SaturationAndLimits() {
  auto o = Options(); o.schedule.profile = ob::ArrivalProfile::kSaturating;
  o.window_requests = 8; o.batch_size = 2;
  for (bool timed : {false, true}) {
    o.service_timing = timed;
    Delayed adapter; ob::NullTrialSink sink;
    const auto r = ob::RunTrial<Clock>(o, adapter, sink);
    Check(r.calls == 8 && r.completed == 16 && r.caller_end_ns == 104 && r.drain_end_ns == 111,
          "coarse saturation window lost caller costs");
    Check(Clock::reads == (timed ? 20 : 4), "saturation added per-call timestamps");
    Check(r.accumulator.finish().response.count() == 0 &&
          r.saturated_service.count() == (timed ? 8 : 0), "invented saturated latency");
  }
  struct Windows : ob::NullTrialSink {
    std::vector<uint64_t> counts;
    void Window(uint64_t, uint64_t, uint64_t n) { counts.push_back(n); }
  };
  // Batch >= 16 reads the clock every call: the loop stops after the first
  // call that crosses the horizon instead of at the next 1024-request window.
  o = Options(); o.schedule.profile = ob::ArrivalProfile::kSaturating;
  o.schedule.num_accesses = 1000000; o.batch_size = 32; o.queue_limit = 32; o.window_requests = 1024;
  {
    Delayed wide; Windows windows;
    const auto r = ob::RunTrial<Clock>(o, wide, windows);  // one call costs 2 + 3*32 + 5
    Check(r.calls == 1 && r.caller_end_ns == 103 && windows.counts == std::vector<uint64_t>{32},
          "saturated horizon checked with a stale clock or window lost");
  }
  // Windows count requests: at batch 2, 8-request windows close every 4 calls.
  o.batch_size = 2; o.window_requests = 8; o.schedule.num_accesses = 20;
  o.horizon_ns = 1000000;
  {
    Delayed narrow; Windows windows;
    ob::RunTrial<Clock>(o, narrow, windows);
    Check(windows.counts == std::vector<uint64_t>{8, 8, 4}, "windows do not count requests");
  }
  // A count-only settle is not truncated by the horizon.
  o = Options(); o.schedule.profile = ob::ArrivalProfile::kSaturating;
  o.schedule.num_accesses = 64; o.batch_size = 2; o.stop_at_request_cap = true; o.finish_pending = false;
  {
    Delayed settle; ob::NullTrialSink none;
    const auto r = ob::RunTrial<Clock>(o, settle, none);
    Check(r.completed == 64 && r.caller_end_ns > o.horizon_ns, "saturated settle stopped at the horizon");
    // ...nor flagged when it outlasts horizon + drain (64 x 13 ns against 100 + 100).
    Check(r.drain_end_ns > o.horizon_ns + o.drain_ns && !r.deadline_exceeded && !r.request_cap_reached,
          "a long count-only settle was flagged as over its deadline");
  }
  // The same for an offered-load settle that falls behind its arrivals past horizon + drain.
  o = Options(); o.schedule.num_accesses = 64; o.stop_at_request_cap = true; o.finish_pending = false;
  {
    Delayed settle; ob::NullTrialSink none;
    const auto r = ob::RunTrial<Clock>(o, settle, none);
    Check(r.completed == 64 && r.offered == 64 && r.caller_end_ns > o.horizon_ns + o.drain_ns &&
              !r.deadline_exceeded && !r.request_cap_reached,
          "an offered-load count-only settle stopped at horizon + drain");
  }
  o = Options(); o.schedule.num_accesses = 10;
  Delayed adapter; ob::NullTrialSink sink;
  Check(!ob::RunTrial<Clock>(o, adapter, sink).request_cap_reached,
        "exact cohort size confused with truncation");
  o.schedule.num_accesses = 9;
  Check(ob::RunTrial<Clock>(o, adapter, sink).request_cap_reached,
        "truncated offered schedule reported complete");
  o = Options(); o.finish_pending = false;
  adapter = {};
  ob::RunTrial<Clock>(o, adapter, sink);
  Check(adapter.finishes == 0, "settle drained the warmed pipeline");
}
void WorkloadCorrectness() {
  for (auto widths : {std::pair<size_t,size_t>{4,8}, {8,48}, {16,16}, {32,1024}}) {
    for (bool misses : {false, true}) {
      ob::WorkloadSpec spec;
      spec.live_entries = 3; spec.key_bytes = widths.first; spec.value_bytes = widths.second;
      spec.read_ppm = misses ? 1000000 : 500000;
      spec.hit_ppm = misses ? 500000 : 1000000;
      spec.miss_key_count = misses ? 2 : 0;
      uint64_t reference_checksum = 0;
      for (size_t chunk : {size_t{1}, size_t{7}}) {
        ob::FakeBackend backend(spec);
        ob::PreparedWorkload<ob::FakeBackend> adapter(backend, spec, chunk, chunk > 1);
        backend.Fill(adapter.generator());
        for (uint64_t first = 0; first < 301;) {
          const size_t n = std::min<uint64_t>(chunk, 301-first);
          ob::PendingRequest members[7];
          for (size_t i = 0; i < n; ++i) members[i] = {first+i, 0};
          adapter.Prepare(members, n);
          Clock clock;
          adapter.Invoke(clock, true, n);
          adapter.Consume(n);
          first += n;
        }
        Check(adapter.verified_reads() > 0, "workload never verified full returned values");
        if (chunk == 1) reference_checksum = adapter.checksum();
        else Check(reference_checksum == adapter.checksum(), "scalar/batch workload results differ");
      }
    }
  }
  // The counter visits live keys only, so it cannot reproduce a miss: misses are refused.
  ob::WorkloadSpec misses;
  misses.live_entries = 3; misses.read_ppm = 1000000; misses.hit_ppm = 0;
  misses.miss_key_count = 2; misses.counter_key = true;
  bool refused = false;
  try { ob::WorkloadGenerator generator(misses); } catch (const std::exception&) { refused = true; }
  Check(refused, "counter key accepted a miss workload");
}
// Records the key ID of every access, in order.
struct KeyLog : ob::FakeBackend {
  ob::WorkloadGenerator generator;
  std::vector<uint64_t> ids;
  explicit KeyLog(ob::WorkloadSpec spec) : ob::FakeBackend(spec), generator(spec) {}
  bool Find(const uint8_t* key, uint8_t* output) { ids.push_back(generator.KeyId(key)); return ob::FakeBackend::Find(key, output); }
  void Write(const uint8_t* key, const uint8_t* value) { ids.push_back(generator.KeyId(key)); ob::FakeBackend::Write(key, value); }
  void Batch(size_t count, const Request* requests, uint8_t* found) {
    for (size_t i = 0; i < count; ++i) ids.push_back(generator.KeyId(requests[i].key));
    ob::FakeBackend::Batch(count, requests, found);
  }
};
// The counter key steps through every live key once per N requests, far apart,
// and the adapter's stepping agrees with the direct formula across id jumps.
void CounterKeys() {
  for (uint64_t live : {uint64_t{1}, uint64_t{2}, uint64_t{3}, uint64_t{10}, uint64_t{1000}, uint64_t{1} << 20}) {
    ob::WorkloadSpec spec; spec.live_entries = live; spec.counter_key = true;
    const ob::WorkloadGenerator generator(spec);
    const uint64_t stride = generator.counter_stride();
    Check(live == 1 || (stride > 0 && stride < live && std::gcd(stride, live) == 1), "counter stride not coprime");
    if (live >= 1000) Check(stride > live / 2 && stride < live - live / 4, "counter stride is not about 0.618 N");
    std::vector<bool> seen(live);
    for (uint64_t k = 0; k < live; ++k) seen[generator.CounterKey(k)] = true;
    Check(std::all_of(seen.begin(), seen.end(), [](bool b) { return b; }), "counter misses a live key");
  }
  for (auto widths : {std::pair<size_t,size_t>{4,8}, {8,48}, {16,16}}) {
    ob::WorkloadSpec spec;
    spec.live_entries = 37; spec.key_bytes = widths.first; spec.value_bytes = widths.second;
    spec.read_ppm = 500000; spec.counter_key = true;
    uint64_t reference_checksum = 0;
    for (size_t chunk : {size_t{1}, size_t{7}}) {
      KeyLog backend(spec);
      ob::PreparedWorkload<KeyLog> adapter(backend, spec, chunk, chunk > 1);
      backend.Fill(adapter.generator());
      // Two runs of ids with a jump between them (a warmup, then measurement).
      std::vector<uint64_t> expected;
      for (uint64_t begin : {uint64_t{0}, uint64_t{1000}})
        for (uint64_t id = begin; id < begin + 301; ++id) expected.push_back(adapter.generator().CounterKey(id));
      for (uint64_t begin : {uint64_t{0}, uint64_t{1000}}) {
        for (uint64_t first = begin; first < begin + 301;) {
          const size_t n = std::min<uint64_t>(chunk, begin + 301 - first);
          ob::PendingRequest members[7];
          for (size_t i = 0; i < n; ++i) members[i] = {first + i, 0};
          adapter.Prepare(members, n);
          Clock clock;
          adapter.Invoke(clock, true, n);
          adapter.Consume(n);
          first += n;
        }
      }
      Check(backend.ids == expected, "stepped counter keys differ from k*S mod N");
      Check(adapter.verified_reads() > 0, "counter workload never verified returned values");
      Check(adapter.VerifyFinal() > 0, "counter workload skipped the final sweep");
      if (chunk == 1) reference_checksum = adapter.checksum();
      else Check(reference_checksum == adapter.checksum(), "scalar/batch counter results differ");
    }
  }
}
void FinalWriteValidation() {
  struct Corrupt : ob::FakeBackend {
    size_t width;
    explicit Corrupt(ob::WorkloadSpec s) : ob::FakeBackend(s), width(s.value_bytes) {}
    bool Find(const uint8_t* key, uint8_t* out) {
      const bool found = ob::FakeBackend::Find(key, out);
      if (found) out[width - 1] ^= 1;
      return found;
    }
  };
  ob::WorkloadSpec spec; spec.live_entries = 3; spec.read_ppm = 0;
  Corrupt backend(spec);
  ob::PreparedWorkload<Corrupt> adapter(backend,spec,1,false);
  backend.Fill(adapter.generator());
  ob::PendingRequest request{0,0};
  adapter.Prepare(&request,1);
  Clock clock; adapter.Invoke(clock,true,1); adapter.Consume(1);
  bool rejected = false;
  try { adapter.VerifyFinal(); } catch (const std::exception&) { rejected = true; }
  Check(rejected, "write-only trial accepted corrupted final full-width value");
}
void PhaseNotifications() {
  for (auto profile : {ob::ArrivalProfile::kSaturating, ob::ArrivalProfile::kFixedRate}) {
    for (bool finish : {false, true}) {
      auto o=Options(); o.schedule.profile=profile; o.finish_pending=finish;
      o.window_requests=8;
      Delayed adapter; ob::NullTrialSink sink;
      std::vector<ob::TrialPhase> phases;
      uint64_t drain_start=0, drain_end=0;
      const auto result=ob::RunTrial<Clock>(o,adapter,sink,[&](ob::TrialPhase phase) {
        phases.push_back(phase);
        if (phase==ob::TrialPhase::kDrain) {
          Check(adapter.finishes==0,"drain notification came after finish");
          drain_start=Clock::now;
        }
        if (phase==ob::TrialPhase::kLogFlush) {
          Check(adapter.finishes==size_t(finish),"log flushing began before finish");
          drain_end=Clock::now;
        }
      });
      const std::vector<ob::TrialPhase> expected=finish
          ? std::vector<ob::TrialPhase>{ob::TrialPhase::kMeasure,ob::TrialPhase::kDrain,ob::TrialPhase::kLogFlush}
          : std::vector<ob::TrialPhase>{ob::TrialPhase::kMeasure,ob::TrialPhase::kLogFlush};
      Check(phases==expected,"phase ordering changed or settle invented a drain");
      Check(drain_end==result.drain_end_ns && (!finish ||
            (drain_start==result.caller_end_ns && drain_end-drain_start==adapter.finish)),
            "phase notifications do not bracket maintenance");
    }
  }
}
int main() {
  Timings(); GroupArrivals(); Overload(); DispatchIsPreviousRead(); PeriodicCheckpoints(); CheckpointThreadMatchesInline(); CheckpointThreadStartup(); LongStallBacklog(); SaturationAndLimits(); WorkloadCorrectness(); CounterKeys(); FinalWriteValidation(); PhaseNotifications();
  std::cout << "oram_bench_trial_test passed\n";
}
