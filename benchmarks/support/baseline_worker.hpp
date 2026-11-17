#pragma once
// Shared by the workers that run a baseline (benchmarks/baselines/README.md):
// the library and harness slots, the resolved envelope, confining a process
// whose pools start their own threads, and the /proc scan that is the placement
// evidence for those pools. No baseline code is included here.
//
// Every baseline runs in the same core budget as our library: library slots
// (the caller's first) plus one harness slot. The baselines start their own
// thread pools (TBB, OpenMP, SONIC's pthreads) and do not take our
// thread-start hook, so a worker restricts its allowed CPUs before those pools
// start (threads inherit the mask) and then proves the placement by scanning
// /proc/self/task: a library thread allowed or run outside the library slots
// fails the trial.
#include "benchmarks/support/placement.hpp"
#include "benchmarks/support/worker.hpp"
#include <filesystem>
#ifdef __linux__
#include <sched.h>
#include <sys/syscall.h>
#include <unistd.h>
#endif

namespace oram_bench::baseline {

// The envelope role of a baseline pool slot (schema.py BASELINE_POOL_ROLE).
constexpr int kPoolRole = 10;

struct Choice { std::string field, value, source, reason; };

// Library slots first (the caller's at 0), the harness slot last. Empty when
// unplaced. Slots are whole physical cores, one CPU each (NearFarSlots).
struct Slots {
  std::vector<unsigned> cpus;
  std::vector<topology::Cpu> topology;  // the original allowed set, for evidence
  std::string policy = "unplaced";
  bool placed() const { return !cpus.empty(); }
  std::vector<unsigned> library() const { return {cpus.begin(), cpus.end() - 1}; }
  unsigned harness() const { return cpus.back(); }
};

// `library_threads` slots are the caller's and the pool's; the rest of the
// library budget stays idle. Self-placed pools report baseline_self_placed.
inline Slots ChooseSlots(const WorkerOptions& o, unsigned library_threads, bool self_placed) {
  Require(library_threads >= 1 && library_threads + 1 <= o.cores,
          "baseline threads exceed the core budget (one core is the harness's)");
  Slots s;
  if (o.placement == "unplaced") return s;
  s.topology = topology::Discover();
  if (o.placement == "explicit") {
    s.cpus = o.cpu_ids;
  } else {
    std::vector<PlacementLocality> roles{PlacementLocality::kCaller};
    roles.resize(library_threads, PlacementLocality::kBackground);
    s.cpus = NearFarSlots(s.topology, roles, o.cores, 1);
  }
  topology::Resolve(s.topology, s.cpus, {}, {}, true);  // distinct physical cores, in the mask
  s.policy = self_placed ? "baseline_self_placed" : o.placement == "near_far" ? "near_far_v2" : o.placement;
  return s;
}

struct Envelope {
  std::string scheme, policy_identity, configuration_key;
  uint64_t actual_capacity = 0, modeled_buffer_bytes = 0;
  bool supports_direct_initialization = false;
  unsigned library_threads = 1;  // the caller plus pool slots
  std::vector<uint64_t> carry_periods;
  std::vector<Choice> choices;
};

// The resolved.json a baseline worker prints for --resolve-only and saves
// per trial (schema.py WorkerResolution).
inline std::string EnvelopeJson(const WorkerOptions& o, const Envelope& e, const Slots& s) {
  std::ostringstream out;
  out << "{\"worker_schema_version\":2,\"resolver_request\":" << ResolverRequestJson(o)
      << ",\"scheme\":" << JsonQuote(e.scheme) << ",\"requested_capacity\":" << o.capacity
      << ",\"actual_capacity\":" << e.actual_capacity << ",\"policy_identity\":" << JsonQuote(e.policy_identity)
      << ",\"configuration_key\":" << JsonQuote(e.configuration_key)
      << ",\"supports_direct_initialization\":" << (e.supports_direct_initialization ? "true" : "false")
      << ",\"modeled_buffer_bytes\":" << e.modeled_buffer_bytes << ",\"carry_period_accesses\":[";
  for (size_t i = 0; i < e.carry_periods.size(); ++i) out << (i ? "," : "") << e.carry_periods[i];
  out << "],\"choices\":[";
  for (size_t i = 0; i < e.choices.size(); ++i) {
    const auto& c = e.choices[i];
    out << (i ? "," : "") << "{\"field\":" << JsonQuote(c.field) << ",\"value\":" << JsonQuote(c.value)
        << ",\"source\":" << JsonQuote(c.source) << ",\"reason\":" << JsonQuote(c.reason) << '}';
  }
  out << "],\"library_threads\":" << e.library_threads
      << ",\"reserved_harness_cores\":1,\"placement_verified\":false,\"threads\":[";
  for (unsigned i = 0; i < e.library_threads; ++i) {
    out << (i ? "," : "") << "{\"role\":" << (i ? kPoolRole : 0) << ",\"index\":" << (i ? i - 1 : 0)
        << ",\"cpu\":";
    if (s.placed()) out << s.cpus[i]; else out << "null";
    out << '}';
  }
  out << "],\"placement_policy\":" << JsonQuote(s.policy) << ",\"cpu_slots\":[";
  for (size_t i = 0; i < s.cpus.size(); ++i) out << (i ? "," : "") << s.cpus[i];
  out << "]}";
  return out.str();
}

#ifdef __linux__
inline long ThreadId() { return syscall(SYS_gettid); }
// Threads the calling thread starts inherit this mask, which is how a worker
// confines pools that start their own threads.
inline void SetAffinity(const std::vector<unsigned>& cpus) {
  cpu_set_t mask; CPU_ZERO(&mask);
  for (const unsigned cpu : cpus) {
    Require(cpu < CPU_SETSIZE, "CPU exceeds affinity mask capacity");
    CPU_SET(cpu, &mask);
  }
  if (sched_setaffinity(0, sizeof(mask), &mask)) throw std::runtime_error("cannot install thread affinity");
}
#endif

// One thread of this process as /proc shows it: its allowed CPUs and the CPU
// it last ran on.
struct Task {
  long tid = 0;
  std::string name;
  std::vector<unsigned> allowed;
  int last_cpu = -1;
};
inline std::vector<Task> ScanTasks() {
  std::vector<Task> tasks;
  std::error_code error;
  for (const auto& entry : std::filesystem::directory_iterator("/proc/self/task", error)) {
    Task task;
    task.tid = std::stol(entry.path().filename().string());
    std::istringstream status(ReadProc(entry.path() / "status"));
    std::string line;
    bool have_mask = false;
    while (std::getline(status, line)) {
      if (line.rfind("Name:", 0) == 0) task.name = line.substr(line.find_first_not_of(" \t", 5));
      if (line.rfind("Cpus_allowed_list:", 0) == 0) {
        const auto list = line.substr(line.find_first_not_of(" \t", 18));
        for (const unsigned cpu : TopologyCpuList(list)) task.allowed.push_back(cpu);
        have_mask = true;
      }
    }
    // Field 39 of stat, counted after the parenthesized command name.
    const auto stat = ReadProc(entry.path() / "stat");
    const auto close = stat.rfind(')');
    if (!have_mask || close == std::string::npos) continue;  // the thread exited meanwhile
    std::istringstream fields(stat.substr(close + 2));
    std::string field;
    for (int i = 3; i <= 39 && fields >> field; ++i)
      if (i == 39) task.last_cpu = std::stoi(field);
    tasks.push_back(std::move(task));
  }
  std::sort(tasks.begin(), tasks.end(), [](const Task& a, const Task& b) { return a.tid < b.tid; });
  return tasks;
}

// Placement evidence for pools that place themselves: /proc scans at
// named phases. A thread allowed or last run outside the library slots is a
// violation, except the harness threads (telemetry and checkpoints), which must
// be on the harness slot.
class TaskEvidence {
 public:
  explicit TaskEvidence(const Slots& slots) : slots_(slots) {}
  void AddHarnessThread(long tid) { std::lock_guard<std::mutex> lock(mutex_); harness_tids_.push_back(tid); }
  void Snapshot(const char* phase) {
    if (!slots_.placed()) return;
    const auto tasks = ScanTasks();
    std::lock_guard<std::mutex> lock(mutex_);
    const auto library = slots_.library();
    const std::set<unsigned> allowed(library.begin(), library.end());
    for (const auto& task : tasks) {
      const bool harness = std::count(harness_tids_.begin(), harness_tids_.end(), task.tid) != 0;
      const bool inside = harness
          ? task.allowed == std::vector<unsigned>{slots_.harness()} && task.last_cpu == int(slots_.harness())
          : std::all_of(task.allowed.begin(), task.allowed.end(), [&](unsigned c) { return allowed.count(c); }) &&
            task.last_cpu >= 0 && allowed.count(unsigned(task.last_cpu));
      if (!inside) violations_.push_back(std::string(phase) + ": thread " + std::to_string(task.tid) + " (" +
                                         task.name + ") outside its slots");
    }
    snapshots_.emplace_back(phase, tasks);
  }
  bool clean() const { std::lock_guard<std::mutex> lock(mutex_); return violations_.empty(); }
  std::string Json(bool complete) const {
    std::lock_guard<std::mutex> lock(mutex_);
    std::ostringstream out;
    auto list = [&](const std::vector<unsigned>& cpus) {
      out << '[';
      for (size_t i = 0; i < cpus.size(); ++i) out << (i ? "," : "") << cpus[i];
      out << ']';
    };
    out << "{\"placement_schema_version\":1,\"placement_policy\":" << JsonQuote(slots_.policy)
        << ",\"all_planned_roles_verified\":" << (complete && violations_.empty() ? "true" : "false")
        << ",\"physical_host_topology_verified\":false,\"library_slots\":";
    list(slots_.library());
    out << ",\"harness_slot\":" << slots_.harness() << ",\"harness_tids\":[";
    for (size_t i = 0; i < harness_tids_.size(); ++i) out << (i ? "," : "") << harness_tids_[i];
    out << "],\"snapshots\":[";
    for (size_t i = 0; i < snapshots_.size(); ++i) {
      out << (i ? "," : "") << "{\"phase\":" << JsonQuote(snapshots_[i].first) << ",\"tasks\":[";
      const auto& tasks = snapshots_[i].second;
      for (size_t k = 0; k < tasks.size(); ++k) {
        out << (k ? "," : "") << "{\"tid\":" << tasks[k].tid << ",\"name\":" << JsonQuote(tasks[k].name)
            << ",\"last_cpu\":" << tasks[k].last_cpu << ",\"allowed\":";
        list(tasks[k].allowed);
        out << '}';
      }
      out << "]}";
    }
    out << "],\"violations\":[";
    for (size_t i = 0; i < violations_.size(); ++i) out << (i ? "," : "") << JsonQuote(violations_[i]);
    out << "],\"original_allowed_topology\":[";
    for (size_t i = 0; i < slots_.topology.size(); ++i) {
      const auto& cpu = slots_.topology[i];
      out << (i ? "," : "") << "{\"cpu\":" << cpu.id << ",\"package\":" << cpu.package << ",\"core\":" << cpu.core
          << ",\"l3_shared_cpus\":" << JsonQuote(cpu.l3) << ",\"thread_siblings\":" << JsonQuote(cpu.siblings)
          << '}';
    }
    out << "]}\n";
    return out.str();
  }
 private:
  Slots slots_;
  mutable std::mutex mutex_;
  std::vector<long> harness_tids_;
  std::vector<std::pair<std::string, std::vector<Task>>> snapshots_;
  std::vector<std::string> violations_;
};

// --build-info, alone: which files beside the executable a campaign must
// freeze with it (resolution.py freeze_build), and the fetch record.
inline bool PrintBuildInfo(int argc, char** argv, const std::string& baseline, const std::string& fetch_record,
                           const std::vector<std::string>& side_files) {
  if (argc != 2 || std::string(argv[1]) != "--build-info") return false;
  std::cout << "{\"build_info_schema_version\":1,\"baseline\":" << JsonQuote(baseline) << ",\"side_files\":[";
  for (size_t i = 0; i < side_files.size(); ++i) std::cout << (i ? "," : "") << JsonQuote(side_files[i]);
  std::cout << "],\"fetch_record\":" << (fetch_record.empty() ? "null" : fetch_record) << "}\n";
  return true;
}
}  // namespace oram_bench::baseline
