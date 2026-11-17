// Unit test for the benchmark worker's raw-event log
// (benchmarks/support/event_writer.hpp): events recorded during a trial on a
// deterministic fake clock are chunked, written with checksums, and replayed;
// the replay must reproduce the live trial's statistics exactly, and lost,
// duplicate or corrupted chunks must be rejected.  No ORAM and no real clock.
#include "benchmarks/support/event_writer.hpp"
#include "benchmarks/support/memory.hpp"
#include <iostream>
#include <sstream>
#include <future>
namespace ob=oram_bench;
struct Clock {
  static inline uint64_t now=0, read_cost=0;
  Clock() { now=0; }
  uint64_t Now() { const auto t=now; now+=read_cost; return t; }
  void WaitUntil(uint64_t t) { now=std::max(now,t); }
};
struct Adapter {
  uint64_t prepare=2;
  void Prepare(const ob::PendingRequest*,size_t) { Clock::now+=prepare; }
  ob::InvocationTiming Invoke(Clock& c,bool timed,size_t n) {
    return ob::InvokePrepared(c,timed,[&] { Clock::now+=20*n; });
  }
  void Consume(size_t) { Clock::now+=3; }
  void Finish() { Clock::now+=7; }
};
struct MemoryWriter {
  std::vector<ob::RawEvent> events;
  void Push(ob::RawEvent e) { events.push_back(e); }
};
template <typename F> void Reject(F fn) {
  bool rejected=false; try { fn(); } catch (const std::exception&) { rejected=true; }
  ob::Require(rejected,"malformed event stream accepted");
}
void Replay(const std::vector<ob::RawEvent>& events, const ob::TrialResult& live) {
  ob::EventReplay replay;
  // Every event is its own chunk, exercising batches split across chunks.
  for (size_t i=0; i<events.size(); ++i) {
    std::stringstream encoded;
    ob::WriteEventChunk(encoded,i,&events[i],1);
    replay.Observe(ob::ReadEventChunk(encoded));
  }
  replay.ValidateComplete();
  const auto& stats=replay.statistics();
  const auto& original=live.accumulator.finish();
  ob::Require(stats.response.bins()==original.response.bins() &&
              stats.queue.bins()==original.queue.bins() &&
              stats.service.bins()==original.service.bins() &&
              stats.offered()==original.offered() &&
              replay.caller_ns()==live.caller_end_ns && replay.drained_ns()==live.drain_end_ns,
              "replay differs from live counts, bins or boundaries");
}
int main() {
  ob::Require(ob::ProcKiB("VmRSS: 12 kB\nVmSwap: 0 kB\n", "VmRSS")==12288 &&
              ob::ProcKiB("VmSwap: 0 kB\n", "VmSwap")==0 &&
              !ob::ProcKiB("VmRSS: 12 MB\n", "VmRSS"), "memory units/null semantics changed");
  const auto temporary=std::filesystem::temp_directory_path()/
      ("oram-event-error-"+std::to_string(std::chrono::steady_clock::now().time_since_epoch().count()));
  std::filesystem::create_directory(temporary);
  {
    // Telemetry startup hooks run on the telemetry thread; failure propagates.
    ob::MemoryRecorder memory(temporary/"memory.csv",1000000,[](bool) { return ob::MemorySnapshot{}; });
    bool initialized=false;
    const auto caller=std::this_thread::get_id();
    ob::TelemetryThread telemetry(memory,[&] {
      ob::Require(std::this_thread::get_id()!=caller,"telemetry init ran on caller");
      initialized=true;
    });
    ob::Require(initialized,"telemetry returned before startup hook completed");
    telemetry.Stop();
    ob::Require(telemetry.error().empty(),"telemetry failed");
    Reject([&] {
      ob::TelemetryThread failing(memory,[] { throw std::runtime_error("injected affinity failure"); });
    });
    ob::MemoryRecorder broken(temporary/"broken.csv",1000,[](bool) -> ob::MemorySnapshot {
      throw std::runtime_error("injected telemetry failure");
    });
    ob::TelemetryThread faulty(broken);
    faulty.Stop();
    ob::Require(!faulty.error().empty(),"telemetry failure disappeared");
  }
  {
    // A full whole-trial buffer counts losses instead of blocking or growing.
    ob::EventBuffer bounded(2);
    bounded.Push(ob::Event(ob::EventKind::kArrival,1,1));
    bounded.Push(ob::Event(ob::EventKind::kArrival,2,2));
    bounded.Push(ob::Event(ob::EventKind::kArrival,3,3));
    ob::Require(bounded.lost()==1 && bounded.size()==2 && bounded.capacity()==2,
                "full event buffer blocked, grew or silently lost an event");
    // Chunks are written after the trial and split at the chunk size.
    bounded.Write(temporary/"events",64);
    ob::Require(bounded.written()==2,"post-trial write lost records");
    size_t chunks=0;
    for (const auto& entry:std::filesystem::directory_iterator(temporary/"events")) {
      std::ifstream in(entry.path(),std::ios::binary);
      ob::Require(ob::ReadEventChunk(in).events.size()==1,"chunk size bound ignored");
      ++chunks;
    }
    ob::Require(chunks==2,"expected one chunk per record at a 64-byte chunk size");
    Reject([&] { bounded.Write(temporary/"events",64); });  // never overwrite evidence
  }
  std::filesystem::remove_all(temporary);

  ob::TrialOptions options;
  options.horizon_ns=100; options.drain_ns=20; options.batch_size=2; options.queue_limit=16;
  options.schedule.num_accesses=100; options.schedule.rate_kops=100000;
  Adapter adapter; MemoryWriter writer; writer.events.reserve(100);
  ob::BasicEventSink<MemoryWriter> sink(writer);
  const auto result=ob::RunTrial<Clock>(options,adapter,sink);
  Replay(writer.events,result);
  auto validate=[](const auto& events) {
    ob::EventReplay replay; for (const auto& event:events) replay.Observe(event); replay.ValidateComplete();
  };
  auto broken=writer.events; broken.pop_back(); Reject([&] { validate(broken); });
  broken=writer.events; broken.back()[5]++; Reject([&] { validate(broken); });
  // The fixture overloads the adapter, so the deadline censors what is still waiting.
  ob::Require(result.admitted==result.offered && result.accumulator.finish().rejected==0 &&
              result.accumulator.finish().outstanding>0,"overload fixture lost censoring accounting");
  broken=writer.events; broken.back()[4]--; Reject([&] { validate(broken); });
  broken=writer.events; broken[1][1]++; Reject([&] { validate(broken); });
  broken=writer.events; broken[1][7]=1; Reject([&] { validate(broken); });
  broken=writer.events; broken.erase(broken.begin()+2); Reject([&] { validate(broken); });
  ob::EventReplay replay; ob::EventChunk chunk{0,writer.events}; replay.Observe(chunk);
  Reject([&] { replay.Observe(chunk); });
  std::stringstream bytes; ob::WriteEventChunk(bytes,0,writer.events.data(),writer.events.size());
  auto corrupt=bytes.str(); corrupt.back()^=1;
  Reject([&] { std::stringstream in(corrupt); ob::ReadEventChunk(in); });
  // Clock reads cost time: a dispatch admitted before the deadline must not
  // be timestamped at it, or the live log would fail replay.
  for (uint64_t prepare=0; prepare<60; ++prepare) {
    auto late=options; late.drain_ns=7;
    Adapter slow; slow.prepare=prepare; MemoryWriter events;
    ob::BasicEventSink<MemoryWriter> recording(events);
    Clock::read_cost=1;
    const auto live=ob::RunTrial<Clock>(late,slow,recording);
    Clock::read_cost=0;
    Replay(events.events,live);
  }
  std::cout << "oram_bench_events_test passed\n";
}
