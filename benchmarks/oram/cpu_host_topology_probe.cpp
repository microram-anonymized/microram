// Where the guest landed on the host: a per-boot probe for cloud VMs.
//
// WHY THIS EXISTS.  On a multi-die server part (for example several compute
// dies per socket behind one large shared L3) the same binary can measure
// noticeably differently on different boots of the same VM type, depending
// on which dies the vCPUs and the guest memory were placed on.  The guest
// often sees one socket and one NUMA node, so it cannot be told directly which die its
// vCPUs run on or where its memory lives.  These tests infer it:
//
//   c2c      cache-line ping-pong between every pair of physical cores.  Cores
//            on one die answer each other in tens of ns; a pair across dies
//            pays the die-to-die crossing, so a VM split over dies shows two
//            blocks in the matrix.
//   core     idle DRAM load-to-use latency from each physical core (one
//            dependent chain through a buffer far larger than the L3).  If
//            vCPUs sit on dies at different distances from the memory, the
//            per-core numbers split.
//   llc      latency against working set (1 MiB .. 4 GiB) from one core: L3 hit
//            latency and how much of the shared L3 the neighbours leave us.
//   region   the same chase from one core over a large buffer, every hop timed
//            and charged to the 1 GiB of GUEST-PHYSICAL address it landed in
//            (/proc/self/pagemap, needs root).  If part of the guest's memory is
//            backed by a remote die or socket, those regions are slower.
//   freq     a dependent add chain per core: the effective clock, so a slower
//            boot can be told apart from a slower part or a lower turbo.
//   llcpar   the llc chase on several cores at once, each through its own
//            working set: the L3 a whole CCD's cores get together (the share
//            co-tenants or a cache partition leave the VM).
//
// Bandwidth is cpu_mem_bandwidth_benchmark --sweep; run it beside this one to
// characterize a boot.
//
// Usage: cpu_host_topology_probe [options]
//   --tests c2c,core,llc,region,freq  which tests (default all)
//   --chase-mib 4096               buffer for the per-core chase
//   --hops 8388608                 chase hops per core
//   --region-gib 64                buffer for the region map (needs root)
//   --region-lines-per-page 512    sampled lines per 2 MiB page in the map
//   --c2c-round-trips 20000        ping-pong round trips per pair
//   --region-core 1                core that runs the region chase (and llc)
//   --llc-mib 1,8,32,...           llc working sets (MiB; default 1 .. 4096)
//   --llcpar-cores 0,2,4           cores of the llcpar test (default: the first 8 physical cores)
//   --llcpar-mib 1,2,4             per-core working sets of the llcpar test (MiB)
//
// The cores are the first thread of each physical core among the ONLINE CPUs
// (/sys/devices/system/cpu/online); both lists are printed first.  c2c needs
// two physical cores, and the per-core tests at least one.
//
// Prints human-readable tables, then one `PROBE_SUMMARY {json}` line.

#include <algorithm>
#include <atomic>
#include <cctype>
#include <chrono>
#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <map>
#include <random>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>

#include <fcntl.h>
#include <pthread.h>
#include <sched.h>
#include <sys/mman.h>
#include <unistd.h>
#include <x86intrin.h>

namespace {

using Clock = std::chrono::steady_clock;
constexpr size_t kLine = 64;
constexpr size_t kHugePage = size_t{2} << 20;

double SecondsSince(Clock::time_point start) {
  return std::chrono::duration<double>(Clock::now() - start).count();
}

void Pin(int cpu) {
  cpu_set_t set;
  CPU_ZERO(&set);
  CPU_SET(static_cast<unsigned>(cpu), &set);
  if (pthread_setaffinity_np(pthread_self(), sizeof(set), &set) != 0) {
    std::fprintf(stderr, "cannot pin to cpu %d\n", cpu);
    std::exit(1);
  }
}

std::string ReadFirstLine(const std::string& path) {
  std::ifstream f(path);
  std::string s;
  std::getline(f, s);
  return s;
}

// The CPUs of a sysfs list such as "0-3,8,10-11".
std::vector<int> ParseCpuList(const std::string& text) {
  std::vector<int> cpus;
  std::stringstream ss(text);
  for (std::string part; std::getline(ss, part, ',');) {
    int lo = 0, hi = 0;
    const int got = std::sscanf(part.c_str(), "%d-%d", &lo, &hi);
    if (got < 1) continue;
    if (got == 1) hi = lo;
    for (int cpu = std::max(lo, 0); cpu <= hi && cpu < CPU_SETSIZE; ++cpu) cpus.push_back(cpu);
  }
  return cpus;
}

// The lowest-numbered hardware thread of each physical core, in core order,
// over the `online` CPUs (every CPU number below CPU_SETSIZE when that list is
// empty).  Linux removes an offline CPU's topology/ directory, so a CPU whose
// sibling list cannot be read is skipped -- and named in `skipped` when it
// was listed online -- rather than ending the walk.
std::vector<int> PhysicalCores(const std::vector<int>& online, std::vector<int>* skipped) {
  std::set<int> seen;
  std::vector<int> cores;
  const int end = online.empty() ? CPU_SETSIZE : static_cast<int>(online.size());
  for (int i = 0; i < end; ++i) {
    const int cpu = online.empty() ? i : online[i];
    const std::string base = "/sys/devices/system/cpu/cpu" + std::to_string(cpu);
    const std::string sib = ReadFirstLine(base + "/topology/thread_siblings_list");
    if (sib.empty()) {
      if (!online.empty()) skipped->push_back(cpu);
      continue;
    }
    const int first = std::atoi(sib.c_str());  // "a,b" or "a-b": first id
    if (seen.insert(first).second) cores.push_back(first);
  }
  std::sort(cores.begin(), cores.end());
  return cores;
}

double TscPerNs() {
  const Clock::time_point t0 = Clock::now();
  const uint64_t c0 = __rdtsc();
  while (SecondsSince(t0) < 0.2) {
  }
  const uint64_t c1 = __rdtsc();
  return static_cast<double>(c1 - c0) / (SecondsSince(t0) * 1e9);
}

void* MapHuge(size_t bytes) {
  void* p = mmap(nullptr, bytes, PROT_READ | PROT_WRITE,
                 MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (p == MAP_FAILED) {
    std::perror("mmap");
    std::exit(1);
  }
  madvise(p, bytes, MADV_HUGEPAGE);
  std::memset(p, 1, bytes);  // fault (and, in a TD, accept) every page now
  return p;
}

double Median(std::vector<double> v) {
  std::sort(v.begin(), v.end());
  return v.empty() ? 0.0 : v[v.size() / 2];
}

// ---- c2c ------------------------------------------------------------------

struct alignas(64) PingLine {
  std::atomic<uint64_t> v{0};
};

// One-way latency in ns: the two threads hand a counter back and forth.
double PingPong(int a, int b, unsigned round_trips) {
  PingLine line;
  std::atomic<bool> ready{false};
  std::thread peer([&] {
    Pin(b);
    ready.store(true, std::memory_order_release);
    for (uint64_t i = 1; i <= 2ull * (round_trips + 1000); i += 2) {
      while (line.v.load(std::memory_order_acquire) != i) _mm_pause();
      line.v.store(i + 1, std::memory_order_release);
    }
  });
  Pin(a);
  while (!ready.load(std::memory_order_acquire)) _mm_pause();
  Clock::time_point start{};
  for (uint64_t i = 1, n = 0; n < round_trips + 1000; i += 2, ++n) {
    if (n == 1000) start = Clock::now();  // warm-up round trips not timed
    line.v.store(i, std::memory_order_release);
    while (line.v.load(std::memory_order_acquire) != i + 1) _mm_pause();
  }
  const double ns = SecondsSince(start) * 1e9;
  peer.join();
  return ns / (2.0 * round_trips);
}

// ---- chase ----------------------------------------------------------------

// A single random cycle (Sattolo) through `count` line slots; each slot holds
// the address of the next, so every load depends on the previous one.
void BuildCycle(uint8_t* const* slots, size_t count, uint64_t seed) {
  std::vector<uint32_t> order(count);
  for (size_t i = 0; i < count; ++i) order[i] = static_cast<uint32_t>(i);
  std::mt19937_64 rng(seed);
  for (size_t i = count - 1; i > 0; --i) {
    std::uniform_int_distribution<size_t> pick(0, i - 1);
    std::swap(order[i], order[pick(rng)]);
  }
  for (size_t i = 0; i < count; ++i) {
    *reinterpret_cast<uint8_t**>(slots[order[i]]) = slots[order[(i + 1) % count]];
  }
}

double ChaseNs(uint8_t* start, size_t hops, size_t warm = 0) {
  uint8_t* p = start;
  if (warm == 0) warm = hops / 8;
  for (size_t i = 0; i < warm; ++i) p = *reinterpret_cast<uint8_t**>(p);
  const Clock::time_point t0 = Clock::now();
  for (size_t i = 0; i < hops; ++i) p = *reinterpret_cast<uint8_t**>(p);
  const double ns = SecondsSince(t0) * 1e9;
  asm volatile("" : : "r"(p));
  return ns / static_cast<double>(hops);
}

// ---- freq -----------------------------------------------------------------

// Dependent 64-bit multiplies: three cycles each on every recent x86 core.
// (Not add-immediate: Golden Cove and later fold those chains at rename, and
// the measured "clock" then comes out several times too high.)
double EffectiveGhz() {
  constexpr uint64_t kIters = 50'000'000;
  uint64_t x = 3;
  const Clock::time_point t0 = Clock::now();
  for (uint64_t i = 0; i < kIters; ++i) {
    asm volatile(
        "imul %0, %0\n\timul %0, %0\n\timul %0, %0\n\timul %0, %0\n\t"
        "imul %0, %0\n\timul %0, %0\n\timul %0, %0\n\timul %0, %0"
        : "+r"(x));
  }
  const double ns = SecondsSince(t0) * 1e9;
  return 3.0 * 8.0 * kIters / ns;
}

std::vector<std::string> Split(const std::string& s) {
  std::vector<std::string> out;
  std::stringstream ss(s);
  for (std::string t; std::getline(ss, t, ',');) out.push_back(t);
  return out;
}

// An option's value: a whole decimal number in [lo, hi].  A sign, a trailing
// character or an empty value is refused rather than read as a prefix.
size_t Count(const std::string& flag, const std::string& v, size_t lo, size_t hi = SIZE_MAX) {
  size_t used = 0;
  unsigned long long x = 0;
  if (!v.empty() && std::isdigit(static_cast<unsigned char>(v[0]))) {
    try {
      x = std::stoull(v, &used);
    } catch (const std::exception&) {
      used = 0;
    }
  }
  if (used == 0 || used != v.size() || x < lo || x > hi) {
    throw std::invalid_argument(flag + " " + v + ": expected a whole number from " + std::to_string(lo) +
                                (hi == SIZE_MAX ? std::string(" up") : " to " + std::to_string(hi)));
  }
  return static_cast<size_t>(x);
}

// A comma-separated list of such numbers, at least one.
std::vector<size_t> Counts(const std::string& flag, const std::string& v, size_t lo, size_t hi = SIZE_MAX) {
  std::vector<size_t> out;
  for (const std::string& t : Split(v)) out.push_back(Count(flag, t, lo, hi));
  if (out.empty()) throw std::invalid_argument(flag + " needs at least one value");
  return out;
}

}  // namespace

int main(int argc, char** argv) {
  std::set<std::string> tests{"c2c", "core", "llc", "region", "freq"};
  std::vector<size_t> llc_mibs{1, 8, 32, 64, 128, 192, 256, 320, 384, 448, 512, 1024, 4096};
  std::vector<size_t> par_mibs{1, 2, 3, 4, 6, 8};
  std::vector<int> par_cores;
  size_t chase_mib = 4096, hops = size_t{1} << 23, region_gib = 64;
  size_t lines_per_page = 512;
  unsigned round_trips = 20000;
  int region_core = 1;
  if (argc % 2 == 0) {
    std::fprintf(stderr, "cpu_host_topology_probe: %s needs a value\n", argv[argc - 1]);
    return 2;
  }
  // A CPU number must fit a cpu_set_t; a region stride must hold a line.
  const size_t max_cpu = CPU_SETSIZE - 1;
  try {
    for (int i = 1; i + 1 < argc; i += 2) {
      const std::string k = argv[i], v = argv[i + 1];
      if (k == "--tests") {
        auto l = Split(v);
        tests = {l.begin(), l.end()};
        for (const std::string& t : tests) {
          if (t != "c2c" && t != "core" && t != "llc" && t != "region" && t != "freq" && t != "llcpar") {
            throw std::invalid_argument("--tests: unknown test " + t);
          }
        }
      }
      else if (k == "--chase-mib") chase_mib = Count(k, v, 1);
      else if (k == "--hops") hops = Count(k, v, 1);
      else if (k == "--region-gib") region_gib = Count(k, v, 0);
      else if (k == "--region-lines-per-page") lines_per_page = Count(k, v, 1, kHugePage / kLine);
      else if (k == "--c2c-round-trips") round_trips = static_cast<unsigned>(Count(k, v, 1, UINT32_MAX));
      else if (k == "--region-core") region_core = static_cast<int>(Count(k, v, 0, max_cpu));
      else if (k == "--llc-mib") llc_mibs = Counts(k, v, 1);
      else if (k == "--llcpar-mib") par_mibs = Counts(k, v, 1);
      else if (k == "--llcpar-cores") {
        par_cores.clear();
        for (size_t c : Counts(k, v, 0, max_cpu)) par_cores.push_back(static_cast<int>(c));
      }
      else { std::fprintf(stderr, "unknown option %s\n", k.c_str()); return 2; }
    }
  } catch (const std::exception& e) {
    std::fprintf(stderr, "cpu_host_topology_probe: %s\n", e.what());
    return 2;
  }
  const std::string online = ReadFirstLine("/sys/devices/system/cpu/online");
  std::vector<int> skipped;
  const std::vector<int> cores = PhysicalCores(ParseCpuList(online), &skipped);
  std::printf("cpu_host_topology_probe: online CPUs %s",
              online.empty() ? "unknown (no /sys/devices/system/cpu/online; tried every CPU number)"
                             : online.c_str());
  if (!skipped.empty()) {
    std::printf("; skipped, no readable topology:");
    for (int c : skipped) std::printf(" %d", c);
  }
  std::printf("\n");
  std::printf("cpu_host_topology_probe: %zu physical cores (first thread of each):", cores.size());
  for (int c : cores) std::printf(" %d", c);
  std::printf("\n");
  // The per-core tests need cores to run on, and c2c needs a pair of them.
  if (cores.empty() && (tests.count("freq") || tests.count("core") || tests.count("c2c") ||
                        (tests.count("llcpar") && par_cores.empty()))) {
    std::fprintf(stderr, "cpu_host_topology_probe: no physical core found (no readable "
                         "/sys/devices/system/cpu/cpuN/topology/thread_siblings_list)\n");
    return 2;
  }
  if (tests.count("c2c") && cores.size() < 2) {
    std::fprintf(stderr, "cpu_host_topology_probe: c2c needs two physical cores, found %zu; "
                         "leave c2c out of --tests\n", cores.size());
    return 2;
  }
  std::ostringstream js;
  js << "{\"cores\":" << cores.size();

  if (tests.count("freq")) {
    std::vector<double> ghz;
    std::printf("\n[freq] effective GHz per core (dependent adds)\n");
    for (int c : cores) {
      Pin(c);
      ghz.push_back(EffectiveGhz());
      std::printf("  cpu %2d  %.3f\n", c, ghz.back());
    }
    js << ",\"freq_ghz_min\":" << *std::min_element(ghz.begin(), ghz.end())
       << ",\"freq_ghz_median\":" << Median(ghz)
       << ",\"freq_ghz_max\":" << *std::max_element(ghz.begin(), ghz.end());
  }

  if (tests.count("c2c")) {
    const size_t n = cores.size();
    std::vector<double> m(n * n, 0.0), all;
    for (size_t i = 0; i < n; ++i)
      for (size_t j = i + 1; j < n; ++j) {
        // Best of three: an interrupt or a host-side preemption only lengthens a run.
        m[i * n + j] = m[j * n + i] = std::min({PingPong(cores[i], cores[j], round_trips),
                                                PingPong(cores[i], cores[j], round_trips),
                                                PingPong(cores[i], cores[j], round_trips)});
        all.push_back(m[i * n + j]);
      }
    std::printf("\n[c2c] one-way core-to-core latency, ns (row/column = cpu)\n     ");
    for (size_t j = 0; j < n; ++j) std::printf("%5d", cores[j]);
    std::printf("\n");
    for (size_t i = 0; i < n; ++i) {
      std::printf("%4d ", cores[i]);
      for (size_t j = 0; j < n; ++j) {
        if (i == j) std::printf("    -");
        else std::printf("%5.0f", m[i * n + j]);
      }
      std::printf("\n");
    }
    std::sort(all.begin(), all.end());
    // Largest relative gap in the sorted pair latencies: a split VM shows a
    // jump between its on-die and cross-die pairs.
    double gap = 1.0;
    size_t at = 0;
    for (size_t k = 1; k < all.size(); ++k)
      if (all[k] / all[k - 1] > gap) { gap = all[k] / all[k - 1]; at = k; }
    std::printf("  pairs %zu: min %.1f median %.1f max %.1f ns; largest jump x%.2f at %.1f -> %.1f ns "
                "(%zu pairs below, %zu above)\n",
                all.size(), all.front(), Median(all), all.back(), gap,
                at ? all[at - 1] : 0.0, all[at], at, all.size() - at);
    js << ",\"c2c_ns_min\":" << all.front() << ",\"c2c_ns_median\":" << Median(all)
       << ",\"c2c_ns_max\":" << all.back() << ",\"c2c_largest_jump\":" << gap
       << ",\"c2c_pairs_above_jump\":" << all.size() - at;
  }

  if (tests.count("core")) {
    const size_t bytes = chase_mib << 20;
    uint8_t* buf = static_cast<uint8_t*>(MapHuge(bytes));
    // One slot per 256 B: a 16 Mi-slot cycle for 4 GiB, well beyond the L3
    // even of large server parts, so a cyclic walk misses the L3 on (nearly)
    // every hop.
    const size_t count = bytes / 256;
    std::vector<uint8_t*> slots(count);
    for (size_t i = 0; i < count; ++i) slots[i] = buf + i * 256;
    BuildCycle(slots.data(), count, 0x51ced);
    std::vector<double> lat;
    std::printf("\n[core] idle DRAM load-to-use latency per core, ns (%zu MiB, %zu hops)\n",
                chase_mib, hops);
    for (int c : cores) {
      Pin(c);
      lat.push_back(ChaseNs(slots[0], hops));
      std::printf("  cpu %2d  %.1f\n", c, lat.back());
    }
    munmap(buf, bytes);
    js << ",\"core_dram_ns_min\":" << *std::min_element(lat.begin(), lat.end())
       << ",\"core_dram_ns_median\":" << Median(lat)
       << ",\"core_dram_ns_max\":" << *std::max_element(lat.begin(), lat.end());
  }

  if (tests.count("llc")) {
    // Latency against working set from one core: L2, L3 hit latency, and where
    // the curve leaves the L3 -- the share of the shared L3 the neighbours
    // leave us.
    std::vector<size_t> mibs = llc_mibs;
    std::sort(mibs.begin(), mibs.end());
    uint8_t* buf = static_cast<uint8_t*>(MapHuge(mibs.back() << 20));
    Pin(region_core);
    std::printf("\n[llc] load-to-use latency against working set, cpu %d (one slot per 128 B)\n", region_core);
    js << ",\"llc_ns\":{";
    for (size_t k = 0; k < mibs.size(); ++k) {
      const size_t count = (mibs[k] << 20) / 128;
      std::vector<uint8_t*> slots(count);
      for (size_t i = 0; i < count; ++i) slots[i] = buf + i * 128;
      BuildCycle(slots.data(), count, 0x11c + k);
      // Two laps (capped) first, so a cache-sized set is resident when timed.
      const double ns = ChaseNs(slots[0], size_t{1} << 22, std::min<size_t>(2 * count, size_t{1} << 24));
      std::printf("  %5zu MiB  %.1f\n", mibs[k], ns);
      js << (k ? "," : "") << "\"" << mibs[k] << "\":" << ns;
    }
    js << "}";
    munmap(buf, mibs.back() << 20);
  }

  if (tests.count("llcpar")) {
    // The llc chase on every listed core at once, each through its own working set
    // (its own huge-page buffer): when the cores' sets together exceed the L3 the
    // VM really gets, every core's latency leaves the L3 value at once.
    if (par_cores.empty())
      for (size_t i = 0; i < std::min<size_t>(8, cores.size()); ++i) par_cores.push_back(cores[i]);
    std::printf("\n[llcpar] llc chase on %zu cores at once (one slot per 128 B), ns per core:", par_cores.size());
    for (int c : par_cores) std::printf(" %d", c);
    std::printf("\n");
    js << ",\"llcpar_ns\":{";
    for (size_t k = 0; k < par_mibs.size(); ++k) {
      const size_t bytes = par_mibs[k] << 20, count = bytes / 128;
      std::vector<double> lat(par_cores.size());
      std::atomic<size_t> ready{0};
      std::atomic<bool> go{false};
      std::vector<std::thread> threads;
      for (size_t t = 0; t < par_cores.size(); ++t) {
        threads.emplace_back([&, t] {
          Pin(par_cores[t]);
          uint8_t* b = static_cast<uint8_t*>(MapHuge(bytes));
          std::vector<uint8_t*> slots(count);
          for (size_t i = 0; i < count; ++i) slots[i] = b + i * 128;
          BuildCycle(slots.data(), count, 0x9a7 + 31 * t + k);
          ready.fetch_add(1);
          while (!go.load(std::memory_order_acquire)) _mm_pause();
          lat[t] = ChaseNs(slots[0], size_t{1} << 22, std::min<size_t>(2 * count, size_t{1} << 24));
          munmap(b, bytes);
        });
      }
      while (ready.load() < par_cores.size()) std::this_thread::yield();
      go.store(true, std::memory_order_release);
      for (auto& th : threads) th.join();
      std::printf("  %3zu MiB each (%4zu MiB together)  median %.1f  max %.1f\n", par_mibs[k],
                  par_mibs[k] * par_cores.size(), Median(lat), *std::max_element(lat.begin(), lat.end()));
      js << (k ? "," : "") << "\"" << par_mibs[k] << "\":" << Median(lat);
    }
    js << "}";
  }

  if (tests.count("region") && region_gib > 0) {
    const int pm = open("/proc/self/pagemap", O_RDONLY);
    Pin(region_core);
    const size_t bytes = region_gib << 30;
    std::printf("\n[region] faulting %zu GiB ...\n", region_gib);
    std::fflush(stdout);
    uint8_t* buf = static_cast<uint8_t*>(MapHuge(bytes));
    const size_t pages = bytes / kHugePage;
    // Guest-physical GiB of every 2 MiB page (first 4 KiB entry; a THP is
    // physically contiguous, and the GiB bin is what we report).
    std::vector<int64_t> gib(pages, -1);
    size_t resolved = 0;
    for (size_t p = 0; p < pages && pm >= 0; ++p) {
      uint64_t e = 0;
      const uintptr_t va = reinterpret_cast<uintptr_t>(buf + p * kHugePage);
      if (pread(pm, &e, 8, static_cast<off_t>(va / 4096 * 8)) == 8 && (e >> 63) && (e & ((1ull << 55) - 1))) {
        gib[p] = static_cast<int64_t>(((e & ((1ull << 55) - 1)) * 4096) >> 30);
        ++resolved;
      }
    }
    const bool physical = resolved * 2 > pages;
    if (!physical) {
      std::printf("  pagemap gave no frame numbers (run as root); binning by VIRTUAL GiB instead\n");
      for (size_t p = 0; p < pages; ++p) gib[p] = static_cast<int64_t>(p * kHugePage >> 30);
    }
    const size_t count = pages * lines_per_page;
    std::vector<uint8_t*> slots(count);
    // Evenly spaced strides, one line at a random offset inside each stride.
    std::mt19937_64 rng(0xa11ce);
    const size_t stride = kHugePage / lines_per_page;
    for (size_t p = 0, k = 0; p < pages; ++p)
      for (size_t l = 0; l < lines_per_page; ++l, ++k)
        slots[k] = buf + p * kHugePage + l * stride + (rng() % (stride / kLine)) * kLine;
    BuildCycle(slots.data(), count, 0xbeef);
    // Bin of each slot, looked up by address after each timed hop.
    const uintptr_t base = reinterpret_cast<uintptr_t>(buf);
    std::map<int64_t, std::pair<double, uint64_t>> bins;  // GiB -> (cycles, hops)
    std::vector<double> cyc(pages, 0.0);
    std::vector<uint64_t> cnt(pages, 0);
    const double tsc_per_ns = TscPerNs();
    uint8_t* q = slots[0];
    for (size_t i = 0; i < count / 8; ++i) q = *reinterpret_cast<uint8_t**>(q);  // warm
    unsigned aux;
    for (size_t i = 0; i < count; ++i) {
      // RDTSCP waits for every earlier load to complete, so [t0, t1] holds
      // exactly this hop's load.
      const uint64_t t0 = __rdtscp(&aux);
      uint8_t* next = *reinterpret_cast<uint8_t**>(q);
      asm volatile("" : : "r"(next) : "memory");
      const uint64_t t1 = __rdtscp(&aux);
      const size_t page = (reinterpret_cast<uintptr_t>(q) - base) / kHugePage;
      cyc[page] += static_cast<double>(t1 - t0);
      ++cnt[page];
      q = next;
    }
    for (size_t p = 0; p < pages; ++p) {
      auto& b = bins[gib[p]];
      b.first += cyc[p];
      b.second += cnt[p];
    }
    std::vector<double> means;
    std::printf("  %s GiB | ns per hop (rdtscp-bracketed, includes ~constant stamp cost) | hops\n",
                physical ? "guest-physical" : "virtual");
    for (const auto& [g, b] : bins) {
      if (b.second == 0) continue;
      const double ns = b.first / b.second / tsc_per_ns;
      means.push_back(ns);
      std::printf("  %6" PRId64 " | %6.1f | %" PRIu64 "\n", g, ns, b.second);
    }
    const double lo = *std::min_element(means.begin(), means.end());
    const double hi = *std::max_element(means.begin(), means.end());
    size_t slow = 0;
    for (double v : means) slow += v > 1.10 * lo;
    std::printf("  regions %zu: min %.1f median %.1f max %.1f ns; %zu regions > 1.10x min\n",
                means.size(), lo, Median(means), hi, slow);
    munmap(buf, bytes);
    if (pm >= 0) close(pm);
    js << ",\"region_physical\":" << (physical ? "true" : "false")
       << ",\"region_ns_min\":" << lo << ",\"region_ns_median\":" << Median(means)
       << ",\"region_ns_max\":" << hi << ",\"region_slow_gib\":" << slow;
  }
  js << "}";
  std::printf("\nPROBE_SUMMARY %s\n", js.str().c_str());
  return 0;
}
