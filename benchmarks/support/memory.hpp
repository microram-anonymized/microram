#pragma once
// Process memory telemetry for a trial: /proc RSS, high-water mark and swap,
// the cgroup's limit and usage, sampled at named phase boundaries and
// periodically on a harness-slot thread, written to worker/memory.csv.
#include "src/oram/support/benchmark_statistics.hpp"
#include <chrono>
#include <atomic>
#include <condition_variable>
#include <functional>
#include <future>
#include <mutex>
#include <thread>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <string>
#ifdef __linux__
#include <sys/resource.h>
#include <time.h>
#endif

namespace oram_bench {
inline std::optional<uint64_t> ProcKiB(const std::string& text,const std::string& field) {
  std::istringstream lines(text); std::string line;
  while (std::getline(lines,line)) {
    std::istringstream words(line); std::string key,unit; uint64_t value;
    if (words>>key && key==field+":" && words>>value>>unit && unit=="kB") {
      Require(value<=UINT64_MAX/1024,"process memory value exceeds byte range");
      return value*1024;
    }
  }
  return std::nullopt;
}
inline std::string ReadProc(const std::filesystem::path& path) {
  std::ifstream in(path); std::ostringstream out; out<<in.rdbuf(); return out.str();
}
inline std::string ProcWord(const std::filesystem::path& path) {
  std::ifstream in(path); std::string value; in>>value; return value;
}
inline std::optional<uint64_t> DecimalNumber(const std::string& value) {
  if (value.empty()) return std::nullopt;
  uint64_t number=0;
  for (char c:value) {
    if (c<'0' || c>'9' || number>(UINT64_MAX-uint64_t(c-'0'))/10) return std::nullopt;
    number=number*10+uint64_t(c-'0');
  }
  return number;
}
inline std::optional<uint64_t> ProcNumber(const std::filesystem::path& path) {
  return DecimalNumber(ProcWord(path));
}
struct MemorySnapshot {
  std::optional<uint64_t> rss,pss,high_water,swap,minor_faults,major_faults;
  // cgroup_peak is memory.peak: the lifetime peak of the coordinator's cgroup.
  std::optional<uint64_t> cgroup_current,cgroup_peak,cgroup_limit;
  // No level up to the hierarchy root sets memory.max; written as "unlimited".
  // A blank limit with this false is unknown (R39).
  bool cgroup_unlimited=false;
};
// The cgroup-v2 group named by /proc/self/cgroup under `root`, the hierarchy's
// mount. The limit is the tightest memory.max up to `root`. A level reading
// "max" sets none, and neither does the hierarchy root, which has no
// memory.max. It is told apart from a cgroup-namespace root (whose hidden
// ancestors may limit) by cgroup.type, which only non-root groups have.
inline void CgroupMemory(MemorySnapshot& result,const std::string& self_cgroup,
                         const std::filesystem::path& root="/sys/fs/cgroup") {
  auto present=[](const std::filesystem::path& path) {
    std::error_code error; return std::filesystem::exists(path,error);
  };
  std::istringstream groups(self_cgroup); std::string line;
  while (std::getline(groups,line)) {
    if (line.rfind("0::",0)!=0) continue;
    const auto relative=std::filesystem::path(line.substr(3)).relative_path();
    bool safe=true;
    for (const auto& part:relative) if (part=="..") safe=false;
    if (!safe) continue;
    auto group=relative.empty() ? root : root/relative;
    result.cgroup_current=ProcNumber(group/"memory.current");
    result.cgroup_peak=ProcNumber(group/"memory.peak");
    bool unlimited=true;
    for (;;) {
      const auto text=ProcWord(group/"memory.max");
      const auto limit=DecimalNumber(text);
      if (limit && (!result.cgroup_limit || *limit<*result.cgroup_limit)) result.cgroup_limit=limit;
      if (group==root) {
        unlimited&=(text.empty() || text=="max") && present(group/"cgroup.controllers") &&
                   !present(group/"cgroup.type");
        break;
      }
      unlimited&=text=="max";
      group=group.parent_path();
    }
    result.cgroup_unlimited=unlimited && !result.cgroup_limit;
  }
}
// smaps_rollup walks the page tables: tens to hundreds of ms at 4 KiB pages
// and many GiB, next to a bandwidth-bound workload. Periodic samples skip it;
// for one process of private anonymous memory PSS equals RSS anyway.
inline MemorySnapshot ProcessMemory(bool include_pss) {
  MemorySnapshot result;
#ifdef __linux__
  const auto status=ReadProc("/proc/self/status");
  result.rss=ProcKiB(status,"VmRSS");
  if (include_pss) result.pss=ProcKiB(ReadProc("/proc/self/smaps_rollup"),"Pss");
  result.high_water=ProcKiB(status,"VmHWM"); result.swap=ProcKiB(status,"VmSwap");
  rusage usage{};
  if (getrusage(RUSAGE_SELF,&usage)==0) {
    result.minor_faults=usage.ru_minflt; result.major_faults=usage.ru_majflt;
  }
  CgroupMemory(result,ReadProc("/proc/self/cgroup"));
#else
  (void)include_pss;
#endif
  return result;
}
// CPU time of a POSIX clock (CLOCK_PROCESS_CPUTIME_ID, CLOCK_THREAD_CPUTIME_ID).
inline uint64_t CpuClockNs(clockid_t clock) {
  timespec t{};
  if (clock_gettime(clock, &t) != 0) throw std::runtime_error("cannot read CPU clock");
  return uint64_t(t.tv_sec) * 1000000000ull + uint64_t(t.tv_nsec);
}
using MemorySampler = std::function<MemorySnapshot(bool include_pss)>;
// The longest periodic sampling interval, one day. The telemetry thread waits
// with std::chrono::nanoseconds (int64): a larger value could wrap negative or
// overflow the clock's deadline arithmetic and turn the wait into a busy loop.
inline constexpr uint64_t kMaxMemoryIntervalNs = UINT64_C(86400000000000);
// Sampled by the telemetry thread during measurement; sampled synchronously
// only before it starts and after it stops. These process/cgroup observations are
// separate scopes from the library and harness bills and must never be added.
class MemoryRecorder {
 public:
  MemoryRecorder(const std::filesystem::path& path,uint64_t interval_ns,
                 MemorySampler sampler = ProcessMemory)
      : out_(path),interval_ns_(interval_ns),sampler_(std::move(sampler)) {
    Require(interval_ns>0 && interval_ns<=kMaxMemoryIntervalNs,
            "memory interval must be 1 ns to one day (86400000000000 ns)");
    out_<<"phase,monotonic_ns,rss_bytes,pss_bytes,high_water_rss_bytes,swap_bytes,minor_faults,major_faults,cgroup_current_bytes,cgroup_peak_bytes,cgroup_limit_bytes\n";
    if (!out_) throw std::runtime_error("cannot create memory observations");
  }
  void Sample(const char* phase) {
    WriteSample(phase, false);
  }
  // The caller only publishes a label; the existing writer owns sampling/I/O.
  // Labels must have static lifetime and change monotonically within a trial.
  void SetPhase(const char* phase) { phase_.store(phase, std::memory_order_release); }
  void SampleCurrentPhase() { WriteSample(nullptr, true); }
  uint64_t interval_ns() const { return interval_ns_; }
  void Close() { out_.close(); if (!out_) throw std::runtime_error("memory observations close failed"); }
 private:
  void WriteSample(const char* phase, bool current) {
    if (current) phase=phase_.load(std::memory_order_acquire);
    const auto now=std::chrono::steady_clock::now();
    const auto snapshot=sampler_(!current);  // PSS at phase boundaries only
    // /proc reads are not atomic. Never assign a straddling read to one phase.
    if (current && phase!=phase_.load(std::memory_order_acquire)) phase="phase_transition";
    out_<<phase<<','<<std::chrono::duration_cast<std::chrono::nanoseconds>(now.time_since_epoch()).count();
    for (const auto& value:{snapshot.rss,snapshot.pss,snapshot.high_water,snapshot.swap,
          snapshot.minor_faults,snapshot.major_faults,snapshot.cgroup_current,
          snapshot.cgroup_peak,snapshot.cgroup_limit}) {
      out_<<','; if (value) out_<<*value;
    }
    if (!snapshot.cgroup_limit && snapshot.cgroup_unlimited) out_<<"unlimited";
    out_<<'\n';
    // Retain synchronous boundaries if construction/initialization fails.
    // Periodic samples keep buffered I/O on the telemetry thread.
    if (!current) out_.flush();
    if (!out_) throw std::runtime_error("memory observations write failed");
  }
  std::ofstream out_;
  uint64_t interval_ns_;
  MemorySampler sampler_;
  std::atomic<const char*> phase_{"before_measure"};
};
// Periodic memory telemetry on its own thread (the request thread only
// appends events, so nothing else runs beside it). It samples at start and then every
// interval until Stop(). The start sample always happens, even when Stop()
// comes first, so a started thread records at least one sample (or its
// failure) before Stop() returns. The startup hook runs on this thread (for
// example to pin it to the reserved harness core); a hook failure propagates
// from the constructor. A sampling failure is retained in error() after Stop().
class TelemetryThread {
 public:
  TelemetryThread(MemoryRecorder& memory, std::function<void()> thread_init = {})
      : memory_(memory) {
    std::promise<void> ready;
    auto started = ready.get_future();
    thread_ = std::thread([this, init = std::move(thread_init), ready = std::move(ready)]() mutable {
      try { if (init) init(); }
      catch (...) { ready.set_exception(std::current_exception()); return; }
      ready.set_value();
      Run();
    });
    try { started.get(); }
    catch (...) { Stop(); throw; }
  }
  TelemetryThread(const TelemetryThread&) = delete;
  ~TelemetryThread() { Stop(); }
  void Stop() {
    { std::lock_guard<std::mutex> lock(mutex_); stop_ = true; }
    wake_.notify_all();
    if (thread_.joinable()) thread_.join();
  }
  const std::string& error() const { return error_; }  // only after Stop
  uint64_t cpu_ns() const { return cpu_ns_; }  // the thread's CPU time; only after Stop
 private:
  void Run() noexcept {
    struct RecordCpu {
      uint64_t& out;
      ~RecordCpu() { try { out = CpuClockNs(CLOCK_THREAD_CPUTIME_ID); } catch (...) {} }
    } record{cpu_ns_};
    try {
      // The start sample must not depend on stop_. The constructor returns
      // (and a caller may call Stop()) as soon as ready is set, before this
      // thread has necessarily run again; checking stop_ first let such a
      // Stop() skip the start sample, and with it any sampling failure.
      // Stop() joins, so this sample always finishes before Stop() returns.
      memory_.SampleCurrentPhase();
      std::unique_lock<std::mutex> lock(mutex_);
      while (!wake_.wait_for(lock, std::chrono::nanoseconds(memory_.interval_ns()), [&] { return stop_; })) {
        lock.unlock();
        memory_.SampleCurrentPhase();
        lock.lock();
      }
    } catch (const std::exception& error) {
      error_ = error.what();
    } catch (...) {
      error_ = "unknown telemetry failure";
    }
  }
  MemoryRecorder& memory_;
  std::mutex mutex_;
  std::condition_variable wake_;
  bool stop_ = false;
  std::thread thread_;
  std::string error_;
  uint64_t cpu_ns_ = 0;
};
}  // namespace oram_bench
