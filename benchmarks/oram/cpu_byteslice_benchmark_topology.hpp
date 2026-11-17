#pragma once

// CPU-topology discovery and placement validation for the benchmark drivers.
// Discover() reads the process affinity mask and, for each allowed CPU, its
// package, physical core, die, NUMA node and unified L3 from Linux sysfs.
// Resolve() checks a requested placement: the online (caller) CPUs share one
// L3 group unless explicitly allowed otherwise, "near" workers share that L3,
// "far" workers sit outside it, and no two engine threads share a physical
// core (no SMT siblings).  Linux's exposed topology is the placement unit; it
// is not a claim about the physical CCD/die layout of a virtualized host.
// Kept independent of ORAM geometry so runners and focused tests can reuse it.
#include <algorithm>
#include <filesystem>
#include <fstream>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>
#ifdef __linux__
#include <sched.h>
#endif

namespace microram::byteslice::benchmark_topology {
struct Cpu {
  unsigned id = 0;
  int package = -1, core = -1, die = -1, numa = -1;
  std::string l3, siblings;
  size_t l3_bytes = 0;
};
struct Placement {
  unsigned local_cores = 0;
  size_t l3_bytes = 0;
  std::vector<Cpu> cpus;  // Requested CPUs in online, near, far order.
};
inline std::string Read(const std::filesystem::path& path) {
  std::ifstream stream(path);
  std::string value;
  if (!(stream >> value)) throw std::runtime_error("unavailable CPU topology: " + path.string());
  return value;
}
inline std::vector<Cpu> Discover() {
#ifdef __linux__
  cpu_set_t allowed;
  if (sched_getaffinity(0, sizeof(allowed), &allowed))
    throw std::runtime_error("cannot read process affinity mask");
  std::vector<Cpu> cpus;
  for (unsigned id = 0; id < CPU_SETSIZE; ++id) {
    if (!CPU_ISSET(id, &allowed)) continue;
    Cpu cpu; cpu.id = id;
    const auto root = std::filesystem::path("/sys/devices/system/cpu") /
                      ("cpu" + std::to_string(id));
    cpu.package = std::stoi(Read(root / "topology/physical_package_id"));
    cpu.core = std::stoi(Read(root / "topology/core_id"));
    if (cpu.package < 0 || cpu.core < 0)
      throw std::runtime_error("untrustworthy exposed physical core identity");
    cpu.siblings = Read(root / "topology/thread_siblings_list");
    if (std::filesystem::exists(root / "topology/die_id"))
      cpu.die = std::stoi(Read(root / "topology/die_id"));
    for (const auto& entry : std::filesystem::directory_iterator(root)) {
      const auto name = entry.path().filename().string();
      if (name.rfind("node", 0) == 0) cpu.numa = std::stoi(name.substr(4));
    }
    for (const auto& entry : std::filesystem::directory_iterator(root / "cache")) {
      if (entry.path().filename().string().rfind("index", 0) != 0) continue;
      if (Read(entry.path() / "level") != "3" ||
          Read(entry.path() / "type") != "Unified") continue;
      if (!cpu.l3.empty()) throw std::runtime_error("ambiguous exposed L3 topology");
      cpu.l3 = Read(entry.path() / "shared_cpu_list");
      const auto size = Read(entry.path() / "size");
      size_t used = 0;
      cpu.l3_bytes = std::stoull(size, &used);
      const auto unit = size.substr(used);
      if (unit == "K") cpu.l3_bytes *= 1024;
      else if (unit == "M") cpu.l3_bytes *= 1024 * 1024;
      else if (!unit.empty()) throw std::runtime_error("unknown L3 size unit");
    }
    if (cpu.l3.empty() || !cpu.l3_bytes)
      throw std::runtime_error("no exposed unified L3 for CPU " + std::to_string(id));
    cpus.push_back(cpu);
  }
  return cpus;
#else
  throw std::runtime_error("CPU topology placement is supported only on Linux");
#endif
}
inline Placement Resolve(const std::vector<Cpu>& available,
                         const std::vector<unsigned>& online,
                         const std::vector<unsigned>& near,
                         const std::vector<unsigned>& far,
                         bool allow_cross_l3 = false) {
  Placement result;
  std::map<unsigned, Cpu> by_id;
  for (const auto& cpu : available) by_id.emplace(cpu.id, cpu);
  std::set<std::pair<int, int>> used;
  std::string selected;
  auto add = [&](unsigned id, unsigned role) {
    const auto it = by_id.find(id);
    if (it == by_id.end()) throw std::invalid_argument("CPU outside process affinity mask");
    const auto& cpu = it->second;
    if (cpu.package < 0 || cpu.core < 0 || cpu.l3.empty() || !cpu.l3_bytes)
      throw std::invalid_argument("incomplete exposed CPU topology");
    if (!used.emplace(cpu.package, cpu.core).second)
      throw std::invalid_argument("engine threads must use distinct physical cores (no SMT sharing)");
    if (selected.empty() && role == 0) {
      selected = cpu.l3; result.l3_bytes = cpu.l3_bytes;
    }
    if (role == 0 && cpu.l3 != selected && !allow_cross_l3)
      throw std::invalid_argument("online CPUs span L3 groups");
    if (role == 1 && cpu.l3 != selected)
      throw std::invalid_argument("near worker must share the caller's L3");
    if (role == 2 && cpu.l3 == selected)
      throw std::invalid_argument("far worker must be outside the caller's L3");
    if (cpu.l3 == selected && cpu.l3_bytes != result.l3_bytes)
      throw std::invalid_argument("inconsistent exposed L3 size");
    result.cpus.push_back(cpu);
  };
  for (auto id : online) add(id, 0);
  if ((!near.empty() || !far.empty()) && online.empty())
    throw std::invalid_argument("near/far CPU lists require an online CPU list");
  for (auto id : near) add(id, 1);
  for (auto id : far) add(id, 2);
  std::set<std::pair<int, int>> local;
  for (const auto& cpu : available)
    if (cpu.l3 == selected) local.emplace(cpu.package, cpu.core);
  result.local_cores = local.size();
  return result;
}
}  // namespace microram::byteslice::benchmark_topology
