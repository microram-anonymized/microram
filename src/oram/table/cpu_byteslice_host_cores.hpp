#pragma once

// HOW MANY PHYSICAL CORES THIS PROCESS MAY RUN ON, in one place.
//
// The library never starts more threads than this: the level arena caps the
// top's helper threads so that the caller, the batch participants, the owner
// threads and the helpers each get a core (ArenaEngineOptions in
// include/cpu_byteslice_oram/byte_map.hpp), the synchronous engine caps its rebuild pool, and a
// tree leaves its caller and position map a core each before it counts
// payload workers.  Two threads of one map on one core are busy at the same
// moments by construction, so sharing a core measures the scheduler, not the
// ORAM (the same argument the near/far planner refuses by).
//
// The count is the distinct physical cores -- CPUs that share a
// `thread_siblings_list` are one core -- among the CPUs that are online and in
// this process's cgroup-v2 cpuset.  It deliberately does NOT read the calling
// thread's affinity mask: a request thread commonly pins itself to its own
// core before it builds its map, and that mask would say one.  So a `taskset`
// restriction of the whole process is not seen; a container's cpuset is.
// Where the topology cannot be read (no sysfs, or not Linux) the logical CPU
// count stands in.
// A guest that hides its SMT siblings shows each vCPU as a core, and the cap
// is then the vCPU count.
//
// Computed once per process and cached.

#include <algorithm>
#include <fstream>
#include <set>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

namespace microram {
namespace byteslice {
namespace host_cores_detail {

inline bool ReadLine(const std::string& path, std::string* out) {
  std::ifstream stream(path);
  return static_cast<bool>(std::getline(stream, *out));
}

// A kernel CPU list, "0-3,8,10-11", as its members; empty on a parse error.
inline std::vector<unsigned> ParseCpuList(const std::string& text) {
  std::vector<unsigned> cpus;
  std::stringstream items(text);
  std::string item;
  while (std::getline(items, item, ',')) {
    if (item.empty()) continue;
    const size_t dash = item.find('-');
    try {
      const unsigned long first = std::stoul(item.substr(0, dash));
      const unsigned long last =
          dash == std::string::npos ? first : std::stoul(item.substr(dash + 1));
      if (last < first || last >= (1u << 20)) return {};
      for (unsigned long cpu = first; cpu <= last; ++cpu) {
        cpus.push_back(static_cast<unsigned>(cpu));
      }
    } catch (...) {
      return {};
    }
  }
  return cpus;
}

// This process's cgroup-v2 effective cpuset, or empty when there is none to
// read (no cgroup v2, or no cpuset controller on the path).
inline std::vector<unsigned> CgroupCpus() {
  std::ifstream cgroup("/proc/self/cgroup");
  std::string line;
  while (std::getline(cgroup, line)) {
    if (line.rfind("0::", 0) != 0) continue;
    std::string cpus;
    if (ReadLine("/sys/fs/cgroup" + line.substr(3) + "/cpuset.cpus.effective",
                 &cpus)) {
      return ParseCpuList(cpus);
    }
  }
  return {};
}

inline unsigned LogicalCpus() {
  return std::max(1u, std::thread::hardware_concurrency());
}

inline unsigned CountPhysicalCores() {
  std::string online_text;
  if (!ReadLine("/sys/devices/system/cpu/online", &online_text)) {
    return LogicalCpus();
  }
  std::vector<unsigned> cpus = ParseCpuList(online_text);
  const std::vector<unsigned> allowed = CgroupCpus();
  if (!allowed.empty()) {
    const std::set<unsigned> in_cgroup(allowed.begin(), allowed.end());
    cpus.erase(std::remove_if(cpus.begin(), cpus.end(),
                              [&](unsigned cpu) {
                                return in_cgroup.count(cpu) == 0;
                              }),
               cpus.end());
  }
  std::set<std::string> cores;
  for (const unsigned cpu : cpus) {
    std::string siblings;
    if (!ReadLine("/sys/devices/system/cpu/cpu" + std::to_string(cpu) +
                      "/topology/thread_siblings_list",
                  &siblings) ||
        siblings.empty()) {
      return LogicalCpus();
    }
    cores.insert(siblings);
  }
  return cores.empty() ? LogicalCpus() : static_cast<unsigned>(cores.size());
}

}  // namespace host_cores_detail

inline unsigned HostPhysicalCores() {
  static const unsigned cores = host_cores_detail::CountPhysicalCores();
  return cores;
}

// The most helper threads that fit beside `used` threads that already need a
// core each; zero when they already fill the host.
inline unsigned HelpersThatFit(unsigned requested, unsigned used,
                               unsigned cores = HostPhysicalCores()) {
  return std::min(requested, cores > used ? cores - used : 0u);
}

}  // namespace byteslice
}  // namespace microram
