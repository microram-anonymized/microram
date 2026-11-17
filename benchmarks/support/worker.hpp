#pragma once
// The single-trial benchmark worker shared by every worker executable (ours in
// benchmarks/oram, the baselines in benchmarks/baselines): option parsing
// (ParseWorker), the resolved request a campaign records, the per-trial output
// directory, and ExecuteWorker, which fills one backend and runs warmup,
// settle, measurement and the final drain through RunTrial, then writes
// events, memory telemetry, maintenance markers and worker.json.  The protocol
// is documented in analysis/oram_bench/WORKER.md.  A backend is any type with
// Fill/Find/Write/Batch/Finish (fake_backend.hpp is the model); AccessCount()
// and Markers() are optional.
#include "benchmarks/support/clock_check.hpp"
#include "benchmarks/support/event_writer.hpp"
#include "benchmarks/support/fake_backend.hpp"
#include "benchmarks/support/maintenance_markers.hpp"
#include "benchmarks/support/memory.hpp"
#include "benchmarks/support/noop_backend.hpp"
#include "benchmarks/support/prepared_workload.hpp"
#include "src/oram/support/benchmark_summary.hpp"
#include <charconv>
#include <climits>
#include <iostream>
#include <map>
#include <memory>

namespace oram_bench {
inline uint64_t Integer(const std::string& text) {
  uint64_t value=0;
  auto r=std::from_chars(text.data(),text.data()+text.size(),value);
  Require(r.ec==std::errc{} && r.ptr==text.data()+text.size(),"expected unsigned integer");
  return value;
}
inline std::string JsonQuote(const std::string& text) {
  std::ostringstream out; out << '"';
  for (unsigned char c : text) {
    if (c=='"' || c=='\\') out << '\\' << c;
    else if (c<32) out << "\\u" << std::hex << std::setw(4) << std::setfill('0') << unsigned(c) << std::dec;
    else out << c;
  }
  out << '"'; return out.str();
}
struct WorkerOptions {
  std::string scheme="fake", output, logging="full_events";
  WorkloadSpec workload;
  TrialOptions trial;
  uint64_t capacity=256, warmup_ns=0, settle_requests=0, max_accesses=uint64_t{1}<<32;
  uint64_t buffer_bytes=64u<<20, chunk_bytes=4u<<20, memory_interval_ns=100000000;
  uint64_t checkpoint_interval_ns=0;  // histogram checkpoint blocks; 0 = one block
  unsigned cores=2;
  unsigned cache_domains=1;  // declared, split evenly; caps a near/far rebuild budget
  std::string monitor_wait="none";  // declared idle-wait capability: none|umwait|mwaitx
  uint64_t spin_before_park_ns=0;  // one spin for every waiting library thread; 0 keeps the defaults
  uint64_t rate_ops_per_second=100000;
  std::vector<unsigned> cpu_ids;
  std::string placement="unplaced";
  Verification verification=Verification::kFull;  // see prepared_workload.hpp
  bool batched=false, resolve_only=false;
  std::map<std::string,std::string> overrides;
  std::vector<std::string> arguments;
  // From the resolved plan, not the command line: accesses between carries into
  // each hierarchy level (level 1 first); empty where the scheme has none.
  std::vector<uint64_t> carry_periods;
};
inline WorkerOptions ParseWorker(int argc,char** argv) {
  WorkerOptions o;
  o.arguments.assign(argv+1,argv+argc);
  o.trial.schedule.profile=ArrivalProfile::kSaturating;
  o.trial.schedule.num_accesses=100000000;
  std::map<std::string,std::string> fields;
  for (int i=1;i<argc;++i) {
    std::string key=argv[i];
    Require(key.size()>2 && key.substr(0,2)=="--", "expected named worker option");
    Require(i+1<argc,"worker option requires a value");
    Require(fields.emplace(key.substr(2),argv[++i]).second,"duplicate worker option");
  }
  auto number=[&](const char* key,uint64_t fallback) {
    auto at=fields.find(key); if (at==fields.end()) return fallback;
    auto value=Integer(at->second); fields.erase(at); return value;
  };
  auto string=[&](const char* key,std::string fallback) {
    auto at=fields.find(key); if (at==fields.end()) return fallback;
    auto value=at->second; fields.erase(at); return value;
  };
  o.scheme=string("scheme",o.scheme); o.output=string("output","");
  o.logging=string("logging",o.logging);
  Require(o.logging=="full_events" || o.logging=="histogram_checkpoints","unknown logging mode");
  o.verification=ParseVerification(string("verification","full"));
  o.capacity=number("capacity",o.capacity);
  o.workload.live_entries=number("live-entries",o.capacity);
  o.workload.key_bytes=number("key-bytes",4); o.workload.value_bytes=number("value-bytes",8);
  const auto read=number("read-ppm",950000), hit=number("hit-ppm",1000000);
  Require(read<=1000000 && hit<=1000000,"read/hit ratios exceed one million");
  o.workload.read_ppm=read; o.workload.hit_ppm=hit;
  o.workload.miss_key_count=number("miss-keys",0);
  o.workload.seed=number("workload-seed",1);
  o.workload.buffer_requests=number("buffer-requests",4096);
  const auto layout=string("key-layout","permuted");
  Require(layout=="permuted" || layout=="dense","unknown key layout");
  o.workload.key_layout=layout=="dense" ? KeyLayout::kDense : KeyLayout::kPermuted;
  const auto pattern=string("key-pattern","uniform");
  Require(pattern=="uniform" || pattern=="counter","unknown key pattern");
  o.workload.counter_key=pattern=="counter";
  o.trial.batch_size=number("batch-size",1);
  const auto api=string("api","scalar");
  Require(api=="scalar" || api=="batch","unknown API mode"); o.batched=api=="batch";
  Require(o.batched || o.trial.batch_size==1,"scalar API requires batch size one");
  o.trial.batch_timeout_ns=number("batch-timeout-ns",0);
  o.trial.queue_limit=number("queue-limit",65536);
  o.trial.horizon_ns=number("measurement-ns",1000000000);
  o.trial.drain_ns=number("drain-ns",1000000000);
  o.trial.window_requests=number("window-requests",1024);
  o.trial.minimum_tail_count=number("minimum-tail-count",100);
  const auto service=number("service-timing",0), resolve=number("resolve-only",0);
  Require(service<=1 && resolve<=1,"boolean worker options must be 0 or 1");
  o.trial.service_timing=service; o.resolve_only=resolve;
  const auto checkpoint_thread=number("checkpoint-thread",0);
  Require(checkpoint_thread<=1,"boolean worker options must be 0 or 1");
  o.trial.checkpoint_thread=checkpoint_thread;
  o.trial.schedule.num_accesses=number("max-requests",100000000);
  o.trial.schedule.seed=number("arrival-seed",1);
  o.rate_ops_per_second=number("rate",100000);
  o.trial.schedule.rate_kops=o.rate_ops_per_second/1000.0;
  const auto arrival=string("arrival","saturated");
  if (arrival=="fixed") o.trial.schedule.profile=ArrivalProfile::kFixedRate;
  else Require(arrival=="saturated","unknown arrival profile");
  o.trial.schedule.arrival_group=number("arrival-group",1);
  Require(o.trial.schedule.arrival_group>=1 &&
          (o.trial.schedule.arrival_group==1 || (arrival=="fixed" && o.batched)),
          "arrival groups need fixed arrivals and the batch API");
  o.warmup_ns=number("warmup-ns",0); o.settle_requests=number("settle-requests",0);
  o.max_accesses=number("max-accesses",o.max_accesses);
  o.buffer_bytes=number("event-buffer-bytes",o.buffer_bytes);
  o.chunk_bytes=number("chunk-bytes",o.chunk_bytes);
  o.memory_interval_ns=number("memory-interval-ns",o.memory_interval_ns);
  o.checkpoint_interval_ns=number("checkpoint-interval-ns",o.checkpoint_interval_ns);
  const auto cores=number("cores",2); Require(cores && cores<=UINT_MAX,"invalid core budget"); o.cores=cores;
  const auto domains=number("cache-domains",1);
  Require(domains && cores%domains==0,"cache domains must split the core budget evenly");
  o.cache_domains=static_cast<unsigned>(domains);
  o.monitor_wait=string("monitor-wait","none");
  Require(o.monitor_wait=="none" || o.monitor_wait=="umwait" || o.monitor_wait=="mwaitx",
          "unknown monitor-wait capability");
  o.spin_before_park_ns=number("spin-before-park-ns",0);
  const bool explicit_cpu_ids=fields.count("cpu-ids")!=0;
  const auto cpu_ids=string("cpu-ids","");
  o.placement=string("placement",explicit_cpu_ids ? "explicit" : "unplaced");
  Require(o.placement=="unplaced" || o.placement=="explicit" || o.placement=="near_far",
          "unknown placement policy");
  Require((o.placement=="explicit")==explicit_cpu_ids,
          "explicit placement requires --cpu-ids; other policies reject it");
  Require(o.scheme!="fake" || o.placement=="unplaced","fake backend does not support CPU placement");
  Require(!explicit_cpu_ids || !cpu_ids.empty(),"explicit CPU list must not be empty");
  if (!cpu_ids.empty()) {
    std::istringstream input(cpu_ids); std::string token;
    while (std::getline(input,token,',')) {
      const auto cpu=Integer(token); Require(cpu<=UINT_MAX,"CPU ID exceeds unsigned range");
      o.cpu_ids.push_back(static_cast<unsigned>(cpu));
    }
    Require(cpu_ids.back()!=',' && o.cpu_ids.size()==o.cores,"CPU IDs must cover all cores including harness");
    auto unique=o.cpu_ids; std::sort(unique.begin(),unique.end());
    Require(std::adjacent_find(unique.begin(),unique.end())==unique.end(),"duplicate CPU ID");
  }
  for (auto at=fields.begin();at!=fields.end();) {
    if (at->first.rfind("override.",0)==0) {
      o.overrides.emplace(at->first.substr(9),at->second); at=fields.erase(at);
    } else ++at;
  }
  Require(fields.empty(),"unknown worker option");
  Require(o.scheme!="noop" || o.placement=="unplaced","noop backend does not support CPU placement");
  Require(o.capacity && o.workload.live_entries<=o.capacity && o.max_accesses &&
          (o.resolve_only || !o.output.empty()),"invalid capacity/access horizon or missing --output");
  (void)WorkloadGenerator(o.workload);
  Require(o.trial.batch_size && o.trial.batch_size<=o.workload.buffer_requests &&
          o.trial.queue_limit>=o.trial.batch_size,"invalid caller/queue/buffer size");
  Require(CheckedAdd(o.trial.queue_limit,o.trial.batch_size)<=kMaxReplayQueuedRequests,
          "queue limit plus batch size exceeds the 2^24-request replay bound");
  Require(o.trial.horizon_ns && o.trial.drain_ns && o.trial.window_requests &&
          o.trial.schedule.num_accesses && o.trial.minimum_tail_count && o.memory_interval_ns &&
          o.chunk_bytes>=64 && o.chunk_bytes<=o.buffer_bytes && o.chunk_bytes<=(64u<<20),
          "invalid timing, statistics or logging limits");
  Require(o.memory_interval_ns<=kMaxMemoryIntervalNs,
          "memory interval must be 1 ns to one day (86400000000000 ns)");
  (void)CheckedAdd(o.trial.horizon_ns,o.trial.drain_ns);
  // Each checkpoint block holds about 350 KB of histograms.
  Require(!o.checkpoint_interval_ns ||
          (o.trial.horizon_ns+o.trial.drain_ns)/o.checkpoint_interval_ns<=kMaxCheckpointBlocks,
          "checkpoint interval allows more than 4096 blocks over horizon plus drain");
  return o;
}

// Public inputs used by the native resolver, excluding trial output paths and
// resolve-only controls. Override spelling is retained; offline binding uses
// the campaign's types to compare integer/boolean aliases semantically.
inline std::string ResolverRequestJson(const WorkerOptions& o) {
  std::ostringstream out;
  out << "{\"resolver_request_schema_version\":1,\"scheme\":" << JsonQuote(o.scheme)
      << ",\"requested_capacity\":" << o.capacity << ",\"key_bytes\":" << o.workload.key_bytes
      << ",\"value_bytes\":" << o.workload.value_bytes
      << ",\"key_layout\":" << JsonQuote(o.workload.key_layout==KeyLayout::kDense ? "dense" : "permuted")
      << ",\"max_accesses\":" << o.max_accesses
      << ",\"api_mode\":" << JsonQuote(o.batched ? "batch" : "scalar")
      << ",\"caller_batch_size\":" << o.trial.batch_size << ",\"cores\":" << o.cores
      << ",\"cache_domains\":" << o.cache_domains << ",\"monitor_wait\":" << JsonQuote(o.monitor_wait);
  // Present only when set, so a request that leaves it unset keeps the same
  // serialized form.
  if (o.spin_before_park_ns) out << ",\"spin_before_park_ns\":" << o.spin_before_park_ns;
  out << ",\"harness_cores\":1,\"overrides\":[";
  bool first=true;
  for (const auto& [name,value]:o.overrides) {
    if (!first) out << ','; first=false;
    out << "{\"field\":" << JsonQuote(name) << ",\"value\":" << JsonQuote(value) << '}';
  }
  out << "]}";
  return out.str();
}
inline void WorkerHelp() {
  std::cout << "One serialized C++ trial; all times are nanoseconds.\n"
      "--scheme fake|noop|hierarchical_incremental|hierarchical_synchronous|tree|auto|std_unordered_map\n"
      "--output NEW_DIRECTORY --capacity N --live-entries N --key-bytes N --value-bytes N\n"
      "--api scalar|batch --batch-size N --batch-timeout-ns N --queue-limit N\n"
      "--arrival saturated|fixed --rate INTEGER_OPS_PER_SECOND --arrival-group N (requests arriving together)\n"
      "--measurement-ns N --warmup-ns N --settle-requests N --drain-ns N\n"
      "--max-requests N --max-accesses N --window-requests N --service-timing 0|1 --key-pattern uniform|counter --checkpoint-thread 0|1\n"
      "--workload-seed N --arrival-seed N --read-ppm N --hit-ppm N --miss-keys N\n"
      "--key-layout permuted|dense (dense: key i is the little-endian integer i)\n"
      "--buffer-requests N --event-buffer-bytes N --chunk-bytes N --checkpoint-interval-ns N\n"
      "--memory-interval-ns N (1 ns to one day) --minimum-tail-count N\n"
      "--logging full_events|histogram_checkpoints --verification full|off --cores N --resolve-only 0|1\n"
      "--cache-domains N (declared L3 domains splitting --cores evenly; default 1)\n"
      "--monitor-wait none|umwait|mwaitx (declared idle-wait capability; checked against the CPU)\n"
      "--spin-before-park-ns N (one spin for every waiting library thread the overrides leave unset)\n"
      "--cpu-ids CPU,CPU,... (native explicit slots; last CPU is reserved for telemetry)\n"
      "--placement unplaced|explicit|near_far (near_far selects exposed physical cores automatically)\n"
      "--override.NAMESPACE.FIELD VALUE (real backend resolver options)\n"
      "--compiled-isa (alone: print the compiled-in ISA extensions as JSON)\n"
      "--clock-check (alone: cross-check the TSC against the OS clocks, as JSON)\n"
      "Attestation (tdx, snp) and publication gates are the Python framework's, not this worker's.\n";
}

// Create before the backend so failed construction retains its invocation and
// baseline. Resolve-only callers never instantiate this artifact owner.
class WorkerArtifacts {
 public:
  WorkerArtifacts(const WorkerOptions& o,const std::string& resolved,
                  MemorySampler sampler = ProcessMemory)
      : directory_(CreateDirectory(o.output)),
        memory(directory_/"memory.csv",o.memory_interval_ns,std::move(sampler)) {
    Write("resolved.json",resolved+"\n");
    std::ostringstream invocation;
    invocation<<"{\"worker_schema_version\":1,\"argv\":[";
    for (size_t i=0; i<o.arguments.size(); ++i) {
      if (i) invocation<<',';
      invocation<<JsonQuote(o.arguments[i]);
    }
    invocation<<"]}\n"; Write("invocation.json",invocation.str());
    memory.Sample("before_construction");
  }
  void Write(const char* name,const std::string& bytes) {
    std::ofstream out(directory_/name); out << bytes;
    out.close(); if (!out) throw std::runtime_error("cannot write worker artifact");
  }
 private:
  static std::filesystem::path CreateDirectory(const std::string& path) {
    Require(std::filesystem::create_directory(path),"worker output directory already exists");
    return path;
  }
  std::filesystem::path directory_;
 public:
  MemoryRecorder memory;
};

// Carries into each level issued while the library's access counter moved from
// `begin` to `end`: the unit maintenance coverage is counted in. At least two
// top-level carries put one whole top rebuild period inside the window.
inline std::vector<uint64_t> CarriesInWindow(const std::vector<uint64_t>& periods,
                                             uint64_t begin, uint64_t end) {
  Require(begin<=end,"access counter moved backwards");
  std::vector<uint64_t> carries;
  for (const uint64_t period:periods) {
    Require(period>0,"zero carry period");
    carries.push_back(end/period-begin/period);
  }
  return carries;
}
// The library's own access counter where a backend exposes one.
template <typename Backend>
auto BackendAccessCount(const Backend& b, int) -> decltype(b.AccessCount()) { return b.AccessCount(); }
template <typename Backend>
std::optional<uint64_t> BackendAccessCount(const Backend&, long) { return std::nullopt; }
template <typename Backend>
auto BackendAccessCounter(const Backend& b, int) -> decltype(b.AccessCounter()) { return b.AccessCounter(); }
template <typename Backend>
const char* BackendAccessCounter(const Backend&, long) { return "map_accesses"; }

// Maintenance spans (maintenance_markers.hpp); a backend without Markers() has none.
template <typename Backend>
auto BackendMarkers(Backend& b, int) -> decltype(b.Markers()) { return b.Markers(); }
template <typename Backend>
MaintenanceMarkers BackendMarkers(Backend&, long) { return {"", "the backend has no maintenance phases", {}}; }

// The worker's own threads, both on the reserved harness slot. The values are
// their placement roles (library roles are nonnegative), index 0.
enum class HarnessThread : int { kTelemetry=-1, kCheckpoint=-2 };
// Runs first on each harness thread (for example to pin it); a throw fails the trial.
using HarnessThreadInit=std::function<void(HarnessThread)>;
// Whether the measurement trial starts a checkpoint thread: histogram
// checkpoints on an offered-load trial, with --checkpoint-thread 1.
inline bool RunsCheckpointThread(const WorkerOptions& o) {
  return o.trial.checkpoint_thread && o.logging!="full_events" &&
         o.trial.schedule.profile!=ArrivalProfile::kSaturating;
}

// One adapter lives across fill/warmup/settle/measure so the exact value oracle
// follows every update. A new process/adapter is required for each repetition.
template <typename Backend>
int ExecuteWorker(const WorkerOptions& o,Backend& backend,WorkerArtifacts& artifacts,
                  HarnessThreadInit harness_thread_init = {}) {
  namespace fs=std::filesystem;
  auto& memory=artifacts.memory;
  auto write=[&](const char* name,const std::string& bytes) { artifacts.Write(name,bytes); };
  memory.Sample("after_construction");
  // The whole-trial event buffer (event_writer.hpp) is allocated and pre-faulted
  // before fill and warmup. Saturation keeps its coarse windows in either mode;
  // histogram-checkpoint offered-load trials allocate no event buffer.
  const bool full_events=o.logging=="full_events";
  std::unique_ptr<EventBuffer> events;
  if (full_events || o.trial.schedule.profile==ArrivalProfile::kSaturating)
    events=std::make_unique<EventBuffer>(o.buffer_bytes/sizeof(RawEvent));
  PreparedWorkload<Backend> adapter(backend,o.workload,o.trial.batch_size,o.batched,o.verification);
  const uint64_t verification_budget=adapter.verification_budget();
  Require(o.max_accesses>verification_budget,"access budget cannot cover final verification");
  const uint64_t workload_access_limit=o.max_accesses-verification_budget;
  const auto begin=std::chrono::steady_clock::now();
  uint64_t used=backend.Fill(adapter.generator()), request_id=0;
  const auto filled=std::chrono::steady_clock::now();
  memory.Sample("after_fill");
  Require(used<workload_access_limit,"fill exhausted the library access horizon");
  auto phase=[&](TrialOptions options) {
    Require(used<workload_access_limit,"phases exhausted the library access horizon");
    options.schedule.num_accesses=std::min<uint64_t>(options.schedule.num_accesses,workload_access_limit-used);
    options.first_request_id=request_id;
    NullTrialSink sink;
    auto r=RunTrial(options,adapter,sink);
    used=CheckedAdd(used,r.completed); request_id=CheckedAdd(request_id,r.offered);
    Require(!r.request_cap_reached && !r.deadline_exceeded,"warmup/settle exceeded access or time budget");
    Require(!options.stop_at_request_cap || r.offered==options.schedule.num_accesses,
            "settle issued fewer requests than requested");
  };
  // Warmup and settle keep background maintenance running, so measurement
  // never starts from a drained pipeline; the final drain is the only one.
  if (o.warmup_ns) {
    auto options=o.trial; options.horizon_ns=o.warmup_ns; options.finish_pending=false;
    phase(options); memory.Sample("after_warmup");
  }
  if (o.settle_requests) {
    auto options=o.trial;
    options.schedule.num_accesses=o.settle_requests;
    options.stop_at_request_cap=true; options.finish_pending=false;
    // No horizon: an offered-load batch flushes whatever waits once the clock
    // passes horizon_ns, so a settle longer than the measurement window would
    // otherwise end in calls of one request each instead of full batches.
    options.horizon_ns=UINT64_MAX;
    Require(o.settle_requests<=workload_access_limit-used,"settle exceeds remaining access budget");
    phase(options);
    memory.Sample("after_settle");
  }
  Require(used<workload_access_limit,"no access budget remains for measurement");
  auto options=o.trial;
  options.schedule.num_accesses=std::min<uint64_t>(options.schedule.num_accesses,workload_access_limit-used);
  options.first_request_id=request_id;
  const bool saturated=options.schedule.profile==ArrivalProfile::kSaturating;
  // Histogram-checkpoint offered-load trials keep only per-block checkpoints.
  options.checkpoints=!full_events && !saturated;
  options.checkpoint_interval_ns=o.checkpoint_interval_ns;
  options.checkpoint_thread=RunsCheckpointThread(o);
  if (harness_thread_init)
    options.checkpoint_thread_init=[harness_thread_init] { harness_thread_init(HarnessThread::kCheckpoint); };
  memory.Sample("before_measure");
  auto observe_phase=[&](TrialPhase phase) {
    switch (phase) {
      case TrialPhase::kMeasure: memory.SetPhase("measure"); break;
      case TrialPhase::kDrain: memory.SetPhase("final_drain"); break;
      case TrialPhase::kLogFlush: memory.SetPhase("log_flush"); break;
    }
  };
  TrialResult result;
  std::optional<uint64_t> clock_origin;
  std::string error;
  const std::optional<uint64_t> access_begin=BackendAccessCount(backend,0);
  // CPU time over the trial call (measurement and drain). The library's
  // share (process less the caller and telemetry threads) is its idle CPU at
  // low rates. Two clock reads each side, outside every timed phase.
  const uint64_t process_cpu_begin=CpuClockNs(CLOCK_PROCESS_CPUTIME_ID);
  const uint64_t caller_cpu_begin=CpuClockNs(CLOCK_THREAD_CPUTIME_ID);
  const auto trial_wall_begin=std::chrono::steady_clock::now();
  uint64_t telemetry_cpu=0;
  {
    // Telemetry samples on its own thread (bound to the harness slot) while
    // requests are served; the event buffer is only appended to.
    std::function<void()> telemetry_init;
    if (harness_thread_init)
      telemetry_init=[harness_thread_init] { harness_thread_init(HarnessThread::kTelemetry); };
    TelemetryThread telemetry(memory,std::move(telemetry_init));
    if (events) {
      EventSink sink(*events); result=RunTrial(options,adapter,sink,observe_phase); clock_origin=sink.origin_ns;
    } else {
      OriginSink sink; result=RunTrial(options,adapter,sink,observe_phase); clock_origin=sink.origin_ns;
    }
    telemetry.Stop();
    error=telemetry.error();
    telemetry_cpu=telemetry.cpu_ns();
  }
  const uint64_t caller_cpu=CpuClockNs(CLOCK_THREAD_CPUTIME_ID)-caller_cpu_begin;
  const uint64_t process_cpu=CpuClockNs(CLOCK_PROCESS_CPUTIME_ID)-process_cpu_begin;
  const uint64_t trial_wall=std::chrono::duration_cast<std::chrono::nanoseconds>(
      std::chrono::steady_clock::now()-trial_wall_begin).count();
  const std::optional<uint64_t> access_end=BackendAccessCount(backend,0);
  memory.Sample("after_drain");
  // Post-trial encoding, checksums and writes: never inside a timed phase.
  const auto write_begin=std::chrono::steady_clock::now();
  try {
    if (events) {
      events->Write(fs::path(o.output)/"events",o.chunk_bytes);
    } else if (!saturated) {
      Require(fs::create_directory(fs::path(o.output)/"checkpoints"),"checkpoint directory already exists");
      for (size_t i=0; i<result.checkpoints.size(); ++i) {
        std::ostringstream name; name << std::setw(6) << std::setfill('0') << i << ".bin";
        std::ofstream out(fs::path(o.output)/"checkpoints"/name.str(),std::ios::binary);
        WriteCheckpoint(out,result.checkpoints[i]);
        out.close(); if (!out) throw std::runtime_error("cannot close checkpoint");
      }
    }
  } catch (const std::exception& failure) {
    if (error.empty()) error=failure.what();
  }
  const auto write_ns=std::chrono::duration_cast<std::chrono::nanoseconds>(
      std::chrono::steady_clock::now()-write_begin).count();
  const size_t final_verified=adapter.VerifyFinal();
  // Maintenance spans as worker/markers.csv on the trial clock (measurement start = 0),
  // spans that end after it; read after the trial, never inside a timed phase.
  const MaintenanceMarkers markers=BackendMarkers(backend,0);
  size_t markers_written=0;
  if (markers.unavailable.empty() && clock_origin) {
    std::ostringstream csv; csv << "role,level,start_ns,end_ns\n";
    for (const auto& span:markers.spans) {
      if (span.end_ns<*clock_origin) continue;
      csv << span.role << ',' << span.level << ',' << int64_t(span.start_ns-*clock_origin) << ','
          << (span.end_ns-*clock_origin) << '\n';
      ++markers_written;
    }
    write("markers.csv",csv.str());
  }
  memory.Sample("after_verify"); memory.Close();
  std::ostringstream summary; TrialSummaryJson(summary,result,saturated);
  write("summary.json",summary.str());
  const uint64_t lost=events ? events->lost() : 0;
  std::ostringstream metadata;
  metadata << "{\"worker_schema_version\":1,\"scheme\":" << JsonQuote(o.scheme)
      << ",\"clock\":\"steady_clock\",\"logging\":" << JsonQuote(o.logging)
      // An `off` trial never claims verified correctness.
      << ",\"verification\":" << JsonQuote(VerificationName(adapter.verification()))
      << ",\"correctness_verified\":" << (adapter.verification()==Verification::kFull ? "true" : "false")
      << ",\"key_pattern\":" << JsonQuote(o.workload.counter_key ? "counter" : "uniform")
      << ",\"checkpoint_thread\":" << (RunsCheckpointThread(o) ? "true" : "false")
      << ",\"arrival_group\":" << o.trial.schedule.arrival_group
      << ",\"checkpoint_stalls\":" << result.checkpoint_stalls
      << ",\"verified_reads\":" << adapter.verified_reads()
      << ",\"verified_old_values\":" << adapter.verified_old_values()
      << ",\"final_verification_reads\":" << final_verified
      << ",\"version_table_bytes\":" << adapter.version_table_bytes()
      << ",\"minimum_tail_count\":" << options.minimum_tail_count
      << ",\"memory_csv_schema_version\":1,\"memory_interval_ns\":" << o.memory_interval_ns
      << ",\"checksum\":" << adapter.checksum() << ",\"adapter_bytes\":" << adapter.scratch_bytes()
      << ",\"fill_ns\":" << std::chrono::duration_cast<std::chrono::nanoseconds>(filled-begin).count()
      << ",\"lost_events\":" << lost << ",\"writer_error\":" << JsonQuote(error)
      << ",\"trial_boundaries\":[" << result.offered << ',' << result.completed << ','
      << result.completed_during_horizon << ',' << result.caller_end_ns << ',' << result.drain_end_ns << ','
      << (uint64_t(result.request_cap_reached) | (uint64_t(result.deadline_exceeded)<<1)) << ']'
      << ",\"trial_cpu_ns\":{\"process\":" << process_cpu << ",\"caller_thread\":" << caller_cpu
      << ",\"telemetry_thread\":" << telemetry_cpu << ",\"checkpoint_thread\":" << result.checkpoint_cpu_ns
      << ",\"wall\":" << trial_wall << '}'
      << ",\"written_events\":" << (events ? events->written() : 0)
      << ",\"peak_queue_requests\":" << result.peak_queue
      << ",\"peak_event_records\":" << (events ? events->size() : 0)
      << ",\"event_buffer_records\":" << (events ? events->capacity() : 0)
      << ",\"checkpoints\":" << result.checkpoints.size()
      << ",\"post_trial_write_ns\":" << write_ns
      << ",\"clock_origin_steady_ns\":"; JsonNumber(metadata,clock_origin); metadata
      << ",\"maintenance_coverage\":";
  if (access_begin && access_end && !o.carry_periods.empty()) {
    const auto carries=CarriesInWindow(o.carry_periods,*access_begin,*access_end);
    metadata << "{\"counter\":" << JsonQuote(BackendAccessCounter(backend,0))
             << ",\"access_begin\":" << *access_begin << ",\"access_end\":" << *access_end
             << ",\"carry_period_accesses\":[";
    for (size_t i=0; i<o.carry_periods.size(); ++i) metadata << (i ? "," : "") << o.carry_periods[i];
    metadata << "],\"carries_by_level\":[";
    for (size_t i=0; i<carries.size(); ++i) metadata << (i ? "," : "") << carries[i];
    metadata << "]}";
  } else {
    metadata << "null";
  }
  metadata << ",\"maintenance_markers\":";
  if (markers.unavailable.empty() && clock_origin)
    metadata << "{\"source\":" << JsonQuote(markers.source) << ",\"spans\":" << markers_written << '}';
  else
    metadata << "{\"unavailable\":" << JsonQuote(markers.unavailable.empty() ? "no clock origin"
                                                                            : markers.unavailable) << '}';
  metadata << ",\"batch_sizes\":[";
  bool first_batch=true;
  for (size_t n=1; n<result.batch_size_counts.size(); ++n) {
    if (!result.batch_size_counts[n]) continue;
    if (!first_batch) metadata<<',';
    first_batch=false;
    metadata<<'['<<n<<','<<result.batch_size_counts[n]<<']';
  }
  metadata << "],\"publication_validated\":false}\n";
  write("worker.json",metadata.str());
  std::cout << summary.str();
  // An offered-load row that reaches the drain deadline with a backlog is overload, not a failed trial: the
  // unserved requests are censored (outstanding) and the reducer labels the row overloaded. A saturated row
  // whose drain overruns the deadline has no complete drained window, so that one stays invalid.
  const bool overran=result.deadline_exceeded && saturated;
  return lost || !error.empty() || result.request_cap_reached || overran ? 3 : 0;
}

// The instruction-set extensions this binary was compiled for, named as
// /proc/cpuinfo names them. -march=native bakes in the build host's, so the
// doctor checks that a run host exposes every one (a guest may filter CPUID).
inline std::vector<const char*> CompiledIsa() {
  std::vector<const char*> isa;
#define ORAM_BENCH_ISA(macro, name) isa.push_back(name);
#ifdef __AES__
  ORAM_BENCH_ISA(__AES__, "aes")
#endif
#ifdef __PCLMUL__
  ORAM_BENCH_ISA(__PCLMUL__, "pclmulqdq")
#endif
#ifdef __POPCNT__
  ORAM_BENCH_ISA(__POPCNT__, "popcnt")
#endif
#ifdef __BMI__
  ORAM_BENCH_ISA(__BMI__, "bmi1")
#endif
#ifdef __BMI2__
  ORAM_BENCH_ISA(__BMI2__, "bmi2")
#endif
#ifdef __AVX2__
  ORAM_BENCH_ISA(__AVX2__, "avx2")
#endif
#ifdef __AVX512F__
  ORAM_BENCH_ISA(__AVX512F__, "avx512f")
#endif
#ifdef __AVX512BW__
  ORAM_BENCH_ISA(__AVX512BW__, "avx512bw")
#endif
#ifdef __AVX512VL__
  ORAM_BENCH_ISA(__AVX512VL__, "avx512vl")
#endif
#ifdef __AVX512DQ__
  ORAM_BENCH_ISA(__AVX512DQ__, "avx512dq")
#endif
#ifdef __AVX512CD__
  ORAM_BENCH_ISA(__AVX512CD__, "avx512cd")
#endif
#ifdef __AVX512VBMI__
  ORAM_BENCH_ISA(__AVX512VBMI__, "avx512vbmi")
#endif
#ifdef __AVX512VBMI2__
  ORAM_BENCH_ISA(__AVX512VBMI2__, "avx512_vbmi2")
#endif
#ifdef __AVX512BITALG__
  ORAM_BENCH_ISA(__AVX512BITALG__, "avx512_bitalg")
#endif
#ifdef __AVX512VPOPCNTDQ__
  ORAM_BENCH_ISA(__AVX512VPOPCNTDQ__, "avx512_vpopcntdq")
#endif
#ifdef __AVX512VNNI__
  ORAM_BENCH_ISA(__AVX512VNNI__, "avx512_vnni")
#endif
#ifdef __AVX512IFMA__
  ORAM_BENCH_ISA(__AVX512IFMA__, "avx512ifma")
#endif
#ifdef __AVX512BF16__
  ORAM_BENCH_ISA(__AVX512BF16__, "avx512_bf16")
#endif
#ifdef __AVX512VP2INTERSECT__
  ORAM_BENCH_ISA(__AVX512VP2INTERSECT__, "avx512_vp2intersect")
#endif
#ifdef __VAES__
  ORAM_BENCH_ISA(__VAES__, "vaes")
#endif
#ifdef __VPCLMULQDQ__
  ORAM_BENCH_ISA(__VPCLMULQDQ__, "vpclmulqdq")
#endif
#ifdef __GFNI__
  ORAM_BENCH_ISA(__GFNI__, "gfni")
#endif
#undef ORAM_BENCH_ISA
  return isa;
}
// `--compiled-isa` alone prints CompiledIsa() as a JSON array.
inline bool PrintCompiledIsa(int argc, char** argv) {
  if (argc!=2 || std::string(argv[1])!="--compiled-isa") return false;
  std::cout << '[';
  const auto isa=CompiledIsa();
  for (size_t i=0; i<isa.size(); ++i) std::cout << (i ? "," : "") << JsonQuote(isa[i]);
  std::cout << "]\n";
  return true;
}

inline bool SyntheticScheme(const std::string& scheme) { return scheme=="fake" || scheme=="noop"; }
// The synthetic backends shared by both worker executables: fake stores
// values (the correctness fake), noop stores nothing (caller overhead).
inline int RunSyntheticWorker(const WorkerOptions& o) {
  Require(SyntheticScheme(o.scheme) && o.overrides.empty(),
          "synthetic backends (fake, noop) accept no library overrides");
  const std::string resolved="{\"worker_schema_version\":1,\"scheme\":"+JsonQuote(o.scheme)+",\"synthetic\":true}";
  if (o.resolve_only) { std::cout << resolved << '\n'; return 0; }
  WorkerArtifacts artifacts(o,resolved);
  if (o.scheme=="noop") {
    NoopBackend backend(o.workload,o.trial.batch_size); return ExecuteWorker(o,backend,artifacts);
  }
  FakeBackend backend(o.workload); return ExecuteWorker(o,backend,artifacts);
}
}  // namespace oram_bench
