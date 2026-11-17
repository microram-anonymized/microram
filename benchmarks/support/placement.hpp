#pragma once

// Explicit placement for configured maps. Discover before the caller is pinned:
// new helpers inherit its narrow mask, but must be assigned from the ORIGINAL
// allowed set. No claim about physical host CCDs or protected execution is made.
#include "benchmarks/oram/cpu_byteslice_benchmark_topology.hpp"
#include <functional>
#include <charconv>
#include <mutex>
#include <optional>

namespace oram_bench {
namespace topology = microram::byteslice::benchmark_topology;

// Pure placement policy (near_far_v2): online roles, and rebuild threads on the
// near side of an explicit near/far boundary, share the caller's exposed L3.
// Other roles prefer a different L3, spilling locally when remote cores run
// out. The lowest-numbered physical cores are the harness's: CPU 0 usually
// takes most interrupts and housekeeping, so the caller takes the highest core
// of its L3 instead. This is an uncalibrated policy, not a claim about optimal
// placement.
enum class PlacementLocality { kCaller, kOnline, kBackground };

inline std::set<unsigned> TopologyCpuList(const std::string& value) {
  std::set<unsigned> result;
  size_t begin = 0;
  auto number = [](const std::string& text) {
    unsigned n = 0;
    const auto parsed = std::from_chars(text.data(), text.data() + text.size(), n);
    if (parsed.ec != std::errc{} || parsed.ptr != text.data() + text.size() || n >= (1u << 20))
      throw std::invalid_argument("malformed topology CPU number");
    return n;
  };
  do {
    const auto end = value.find(',', begin);
    const auto part = value.substr(begin, end == std::string::npos ? end : end - begin);
    const auto dash = part.find('-');
    const auto first = number(part.substr(0, dash));
    const auto last = dash == std::string::npos ? first : number(part.substr(dash + 1));
    if (first > last || last - first >= 65536)
      throw std::invalid_argument("invalid topology CPU range");
    for (unsigned cpu = first; cpu <= last; ++cpu)
      if (!result.insert(cpu).second || result.size() > 65536)
        throw std::invalid_argument("overlapping or excessive topology CPU ranges");
    if (end == std::string::npos) break;
    begin = end + 1;
  } while (true);
  return result;
}

inline std::vector<unsigned> NearFarSlots(const std::vector<topology::Cpu>& available,
                                        const std::vector<PlacementLocality>& roles,
                                        unsigned cores, unsigned harness_cores = 1) {
  if (roles.empty() || roles.front() != PlacementLocality::kCaller ||
      cores <= harness_cores || roles.size() > cores - harness_cores)
    throw std::invalid_argument("invalid placement role/core budget");
  size_t online_count = 0;
  for (size_t i = 1; i < roles.size(); ++i) {
    if (roles[i] == PlacementLocality::kOnline) ++online_count;
    else if (roles[i] != PlacementLocality::kBackground)
      throw std::invalid_argument("placement needs exactly one caller");
  }
  struct Evidence { topology::Cpu cpu; std::set<unsigned> siblings, l3; };
  std::map<unsigned, Evidence> by_cpu;
  for (const auto& cpu : available) {
    auto siblings = TopologyCpuList(cpu.siblings), l3 = TopologyCpuList(cpu.l3);
    if (cpu.package < 0 || cpu.core < 0 || !cpu.l3_bytes ||
        !siblings.count(cpu.id) || !l3.count(cpu.id) ||
        !by_cpu.emplace(cpu.id, Evidence{cpu, siblings, l3}).second)
      throw std::invalid_argument("incomplete or duplicate topology evidence");
  }
  // Cross-check all exposed siblings/domains before selecting one SMT sibling.
  // Unexposed CPUs may occur in sysfs groups but can never become slots.
  std::map<std::pair<int, int>, Evidence> physical;
  for (const auto& [id, entry] : by_cpu) {
    for (const auto& [other_id, other] : by_cpu) {
      const bool same_core = std::make_pair(entry.cpu.package, entry.cpu.core) ==
                             std::make_pair(other.cpu.package, other.cpu.core);
      if (bool(entry.siblings.count(other_id)) != same_core ||
          (same_core && (entry.siblings != other.siblings || entry.l3 != other.l3)) ||
          (entry.l3.count(other_id) &&
           (entry.l3 != other.l3 || entry.cpu.l3_bytes != other.cpu.l3_bytes)))
        throw std::invalid_argument("inconsistent exposed core or L3 topology");
    }
    physical.emplace(std::make_pair(entry.cpu.package, entry.cpu.core), entry);
  }
  if (physical.size() < cores)
    throw std::invalid_argument("insufficient exposed physical cores for placement budget");
  std::vector<Evidence> candidates;
  for (const auto& [key, entry] : physical) candidates.push_back(entry);
  std::sort(candidates.begin(), candidates.end(), [](const auto& a, const auto& b) {
    return a.cpu.id < b.cpu.id;
  });
  std::vector<unsigned> harness;
  for (unsigned i = 0; i < harness_cores; ++i) harness.push_back(candidates[i].cpu.id);
  candidates.erase(candidates.begin(), candidates.begin() + harness_cores);
  // Each domain is tried once, in order of its lowest core; the caller takes
  // its highest.
  for (size_t d = 0; d < candidates.size(); ++d) {
    const auto& first = candidates[d];
    if (std::any_of(candidates.begin(), candidates.begin() + d,
                    [&](const auto& e) { return e.l3 == first.l3; }))
      continue;
    const Evidence* caller = &first;
    for (const auto& entry : candidates)
      if (entry.l3 == first.l3) caller = &entry;
    std::vector<unsigned> local, remote;
    for (const auto& entry : candidates) {
      if (entry.cpu.id == caller->cpu.id) continue;
      (entry.l3 == caller->l3 ? local : remote).push_back(entry.cpu.id);
    }
    if (local.size() < online_count) continue;
    std::vector<unsigned> slots(cores);
    slots[0] = caller->cpu.id;
    size_t next_local = 0, next_remote = 0;
    for (size_t i = 1; i < roles.size(); ++i)
      if (roles[i] == PlacementLocality::kOnline) slots[i] = local[next_local++];
    auto background = [&] {
      return next_remote < remote.size() ? remote[next_remote++] : local.at(next_local++);
    };
    for (size_t i = 1; i < roles.size(); ++i)
      if (roles[i] == PlacementLocality::kBackground) slots[i] = background();
    // Unused library budget precedes the reserved harness slots; the one-trial
    // worker uses the final slot for telemetry even with inactive pools.
    for (size_t i = roles.size(); i < slots.size() - harness_cores; ++i) slots[i] = background();
    std::copy(harness.begin(), harness.end(), slots.end() - harness_cores);
    return slots;
  }
  throw std::invalid_argument("no exposed L3 can hold caller and online helpers");
}

struct AffinityAccess {
  std::function<void(unsigned)> set;
  std::function<std::vector<unsigned>()> get;
};
inline AffinityAccess LinuxAffinity() {
#ifdef __linux__
  return {
    [](unsigned cpu) {
      if (cpu >= CPU_SETSIZE) throw std::invalid_argument("CPU exceeds affinity mask capacity");
      cpu_set_t mask; CPU_ZERO(&mask); CPU_SET(cpu, &mask);
      if (sched_setaffinity(0, sizeof(mask), &mask))
        throw std::runtime_error("cannot install thread affinity");
    },
    [] {
      cpu_set_t mask;
      if (sched_getaffinity(0, sizeof(mask), &mask))
        throw std::runtime_error("cannot verify thread affinity");
      std::vector<unsigned> result;
      for (unsigned cpu = 0; cpu < CPU_SETSIZE; ++cpu)
        if (CPU_ISSET(cpu, &mask)) result.push_back(cpu);
      return result;
    }};
#else
  throw std::runtime_error("verified affinity requires Linux");
#endif
}

struct PlacementObservation {
  int role;
  unsigned index, cpu;
  std::vector<unsigned> inherited, applied;
};

// Own this object for at least the map's lifetime. Bind is compatible with
// ConstructionHooks::thread_init. Snapshot returns only successful assignments;
// a partial snapshot is never evidence that all planned roles were placed.
class VerifiedPlacement {
 public:
  VerifiedPlacement(const std::vector<topology::Cpu>& available,
                    const std::vector<unsigned>& slots, AffinityAccess affinity)
      : affinity_(std::move(affinity)) {
    if (slots.empty() || !affinity_.set || !affinity_.get)
      throw std::invalid_argument("placement needs explicit slots and affinity operations");
    // Validate every slot, including reserved harness cores, for mask membership,
    // complete exposed topology, and distinct physical core identities.
    topology::Resolve(available, slots, {}, {}, true);
    slots_.insert(slots.begin(), slots.end());
  }

  template <class Thread> void Bind(const Thread& thread) {
    std::lock_guard<std::mutex> lock(mutex_);
    if (!thread.cpu || !slots_.count(*thread.cpu))
      throw std::invalid_argument("planned role has no validated CPU slot");
    // Negative roles are the harness's threads, which share its reserved slot;
    // a library role needs a CPU of its own.
    const int role = static_cast<int>(thread.role);
    for (const auto& old : observations_)
      if ((old.role == role && old.index == thread.index) ||
          (old.cpu == *thread.cpu && (old.role >= 0 || role >= 0)))
        throw std::invalid_argument("duplicate placed role or CPU");
    PlacementObservation observation{role, thread.index,
                                     *thread.cpu, affinity_.get(), {}};
    // Do not reject based on the inherited mask: that recreates the inherited
    // caller-affinity trap. The kernel applies current cgroup restrictions.
    affinity_.set(*thread.cpu);
    observation.applied = affinity_.get();
    if (observation.applied != std::vector<unsigned>{*thread.cpu})
      throw std::runtime_error("thread affinity differs from planned singleton mask");
    observations_.push_back(std::move(observation));
  }

  std::vector<PlacementObservation> Snapshot() const {
    std::lock_guard<std::mutex> lock(mutex_);
    auto result = observations_;
    std::sort(result.begin(), result.end(), [](const auto& a, const auto& b) {
      return std::make_pair(a.role, a.index) < std::make_pair(b.role, b.index);
    });
    return result;
  }

  template <class Threads> void VerifyComplete(const Threads& planned) const {
    const auto observed = Snapshot();
    if (observed.size() != planned.size())
      throw std::runtime_error("placement evidence does not cover every planned role");
    std::set<std::pair<int, unsigned>> seen;
    for (const auto& thread : planned) {
      const auto key = std::make_pair(static_cast<int>(thread.role), thread.index);
      if (!thread.cpu || !seen.insert(key).second ||
          std::none_of(observed.begin(), observed.end(), [&](const auto& record) {
            return record.role == key.first && record.index == key.second && record.cpu == *thread.cpu;
          }))
        throw std::runtime_error("placement evidence differs from planned roles");
    }
  }

 private:
  AffinityAccess affinity_;
  std::set<unsigned> slots_;
  mutable std::mutex mutex_;
  std::vector<PlacementObservation> observations_;
};
}  // namespace oram_bench
