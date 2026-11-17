// How much cache one core can actually use, in a few seconds: load-to-use
// latency against working set, from 4 KiB to beyond the L3, on one pinned core.
//
// WHY.  The guest's sysfs reports the hardware's cache sizes, but a VM gets
// whatever share of the L3 its co-tenants (or a cache partition) leave it.
// On a shared cloud host the usable L3 can be a small fraction of the size
// sysfs reports, and it can differ from one boot to the next, so it is worth
// checking before every measurement session.
//
// HOW.  One random cycle through the 64-byte lines of a working set, each
// line holding the address of the next, so every load depends on the one
// before and no prefetcher can guess it.  One lap (or 50 ms) warms the set,
// then three runs of `--ms`/3 each are timed and the median is kept.  The
// buffer is one huge-page-advised mapping made resident before any timing, so
// a large working set pays the TLB misses of 2 MiB pages where the host
// provides them, and no page faults.
//
// TRANSLATION.  Where the host maps guest memory in 4 KiB units, a
// 4096-entry L2 TLB (as on AMD Zen 5) reaches 16 MiB: past that a random
// line chase pays a nested page walk on most loads, which looks like a
// smaller L3.
// `--stride 4096` chases one random line per 4 KiB page, so the sizes are
// spans and the lines touched are 1/64 of them: at a 32 MiB span the data
// sit in the L2 and the latency above the L2's is the page walk.  (Visiting
// a page's lines together instead lets the prefetchers fetch them early, and
// the "DRAM" latency then reads far too low.)
//
// WATCH.  `--watch-mib W` chases one working set of W MiB for `--watch-s`
// seconds and times every 1024 loads.  A cache that keeps the set reads a
// flat line; a whole-cache flush shows as a burst of DRAM-latency loads that
// fades as the set is refetched; a neighbour sharing the L3 raises and
// roughens the whole line.  `--watch-out FILE` writes the series.
//
// WHAT IT REPORTS.  The curve, then: the L1, L2 and L3 hit latencies (at half
// the L1d, half the L2, and the smaller of 4x the L2 and half the L3, sizes
// from sysfs), DRAM latency (the largest working set), and the USABLE CACHE:
// the largest working set before the first one whose latency exceeds a
// quarter of DRAM's.  With hit latency h and miss latency M, a mean latency
// of M/4 means at least (3/4) M / (M - h), about 75-80 %, of random line
// loads still hit, so this is the working set the caches still mostly serve.
// It counts the L2 too; subtract it for the L3's share.
//
// Usage: cpu_cache_latency_benchmark [--cpu N] [--max-mib M] [--per-octave K]
//            [--ms T] [--seed S] [--stride B]
//            [--watch-mib W [--watch-s S] [--watch-out FILE]]
// Prints a table, then one `CACHE_SUMMARY {json}` line (with --watch-mib: a
// summary, then one `WATCH_SUMMARY {json}` line).

#include <sched.h>
#include <sys/mman.h>

#include <algorithm>
#include <cctype>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {

using Clock = std::chrono::steady_clock;

double SecondsSince(Clock::time_point t) {
  return std::chrono::duration<double>(Clock::now() - t).count();
}

std::string ReadLine(const std::string& path) {
  std::ifstream in(path);
  std::string s;
  std::getline(in, s);
  return s;
}

struct Caches {
  size_t l1d = 0, l2 = 0, l3 = 0;
};

// The sizes sysfs reports for `cpu` ("48K", "1024K", "32768K").
Caches SysfsCaches(int cpu) {
  Caches c;
  for (int i = 0;; ++i) {
    const std::string base = "/sys/devices/system/cpu/cpu" + std::to_string(cpu) +
                             "/cache/index" + std::to_string(i) + "/";
    const std::string level = ReadLine(base + "level");
    if (level.empty()) break;
    const std::string type = ReadLine(base + "type");
    const std::string size = ReadLine(base + "size");
    size_t bytes = std::strtoull(size.c_str(), nullptr, 10);
    if (!size.empty() && size.back() == 'K') bytes <<= 10;
    if (!size.empty() && size.back() == 'M') bytes <<= 20;
    if (level == "1" && type == "Data") c.l1d = bytes;
    if (level == "2") c.l2 = bytes;
    if (level == "3") c.l3 = bytes;
  }
  return c;
}

uint64_t SplitMix64(uint64_t& state) {
  uint64_t z = (state += 0x9E3779B97F4A7C15ull);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
  return z ^ (z >> 31);
}

// Links one 64-byte line in each of the first `slots` `stride`-byte slots of
// `buf` into one random cycle (Sattolo); the line inside a slot is random.
// Returns a line on the cycle.
uint8_t* BuildCycle(uint8_t* buf, size_t slots, size_t stride, std::vector<uint32_t>& order, uint64_t seed) {
  const auto line = [&](size_t slot) {
    uint64_t s = seed ^ (slot * 0x2545F4914F6CDD1Dull);
    return buf + slot * stride + SplitMix64(s) % (stride / 64) * 64;
  };
  order.resize(slots);
  for (size_t i = 0; i < slots; ++i) order[i] = static_cast<uint32_t>(i);
  for (size_t i = slots - 1; i > 0; --i) {  // Sattolo: a single cycle
    std::swap(order[i], order[SplitMix64(seed) % i]);
  }
  for (size_t i = 0; i < slots; ++i) {
    *reinterpret_cast<uint8_t**>(line(order[i])) = line(order[(i + 1) % slots]);
  }
  return line(order[0]);
}

// Follows the chain in chunks until `seconds` pass or `max_hops` are done;
// returns ns per hop, and the position in *p.
double Chase(uint8_t** p, double seconds, uint64_t max_hops) {
  constexpr unsigned kChunk = 4096;
  uint8_t* q = *p;
  uint64_t hops = 0;
  const Clock::time_point t0 = Clock::now();
  double elapsed = 0;
  do {
    for (unsigned i = 0; i < kChunk; ++i) q = *reinterpret_cast<uint8_t**>(q);
    hops += kChunk;
    elapsed = SecondsSince(t0);
  } while (elapsed < seconds && hops < max_hops);
  *p = q;
  return elapsed * 1e9 / double(hops);
}

// An option's value, the whole of it: a trailing character, an empty value
// or (for a count) a sign is refused rather than read as a prefix.
uint64_t Count(const std::string& flag, const std::string& v, uint64_t max = UINT64_MAX) {
  size_t used = 0;
  uint64_t x = 0;
  if (!v.empty() && std::isdigit(static_cast<unsigned char>(v[0]))) {
    try {
      x = std::stoull(v, &used);
    } catch (const std::exception&) {
      used = 0;
    }
  }
  if (used == 0 || used != v.size() || x > max) {
    throw std::invalid_argument(flag + " " + v + ": not a whole number up to " + std::to_string(max));
  }
  return x;
}

double Number(const std::string& flag, const std::string& v) {
  size_t used = 0;
  double x = 0;
  try {
    x = std::stod(v, &used);
  } catch (const std::exception&) {
    used = 0;
  }
  if (used == 0 || used != v.size() || !std::isfinite(x)) {
    throw std::invalid_argument(flag + " " + v + ": not a number");
  }
  return x;
}

uint64_t AnonHugeBytes() {
  std::ifstream in("/proc/self/smaps_rollup");
  for (std::string line; std::getline(in, line);) {
    if (line.rfind("AnonHugePages:", 0) == 0) {
      return std::strtoull(line.c_str() + 14, nullptr, 10) << 10;
    }
  }
  return 0;
}

// The watch: chases `bytes` of `buf` for `seconds`, timing every kHops loads.
// A burst starts at a chunk above 4x the median and ends at the first chunk
// back under 2x.
int Watch(uint8_t* buf, size_t bytes, size_t stride, double seconds, uint64_t seed, int cpu,
          const std::string& out) {
  constexpr unsigned kHops = 1024;
  std::vector<uint32_t> order;
  uint8_t* p = BuildCycle(buf, bytes / stride, stride, order, seed);
  Chase(&p, 0.05, bytes / stride);  // one lap, or 50 ms
  std::vector<float> ns, at_ms;
  ns.reserve(size_t(seconds * 2e5));
  at_ms.reserve(size_t(seconds * 2e5));
  const Clock::time_point t0 = Clock::now();
  Clock::time_point prev = t0;
  for (;;) {
    for (unsigned i = 0; i < kHops; ++i) p = *reinterpret_cast<uint8_t**>(p);
    const Clock::time_point now = Clock::now();
    ns.push_back(float(std::chrono::duration<double, std::nano>(now - prev).count() / kHops));
    at_ms.push_back(float(std::chrono::duration<double, std::milli>(now - t0).count()));
    prev = now;
    if (at_ms.back() >= seconds * 1e3) break;
  }
  asm volatile("" : : "r"(p));

  std::vector<float> sorted = ns;
  std::sort(sorted.begin(), sorted.end());
  const auto q = [&](double f) { return double(sorted[size_t(f * double(sorted.size() - 1))]); };
  const double med = q(0.5), total_ms = at_ms.back();
  double slow_ms = 0, longest_us = 0;
  std::vector<double> starts, lengths;
  bool in_burst = false;
  for (size_t i = 0; i < ns.size(); ++i) {
    const double chunk_ms = ns[i] * kHops * 1e-6;
    longest_us = std::max(longest_us, chunk_ms * 1e3);
    if (ns[i] > 2 * med) slow_ms += chunk_ms;
    if (!in_burst && ns[i] > 4 * med) {
      in_burst = true;
      starts.push_back(at_ms[i] - chunk_ms);
    } else if (in_burst && ns[i] <= 2 * med) {
      in_burst = false;
      lengths.push_back(at_ms[i] - chunk_ms - starts.back());
    }
  }
  std::vector<double> gaps;
  for (size_t i = 1; i < starts.size(); ++i) gaps.push_back(starts[i] - starts[i - 1]);
  const auto median = [](std::vector<double> v) {
    if (v.empty()) return 0.0;
    std::sort(v.begin(), v.end());
    return v[v.size() / 2];
  };
  std::printf("watch: %.1f MiB on cpu %d for %.1f s, %zu chunks of %u loads\n", bytes / 1048576.0, cpu,
              total_ms / 1e3, ns.size(), kHops);
  std::printf("  ns/load median %.2f, p90 %.2f, p99 %.2f, p99.9 %.2f, max %.2f; longest chunk %.0f us\n",
              med, q(0.9), q(0.99), q(0.999), q(1.0), longest_us);
  std::printf("  time above 2x median %.2f %%; bursts above 4x median %zu (%.2f/s), median gap %.1f ms, "
              "median burst %.2f ms\n",
              100 * slow_ms / total_ms, starts.size(), starts.size() / (total_ms / 1e3), median(gaps),
              median(lengths));
  std::printf("WATCH_SUMMARY {\"cpu\":%d,\"bytes\":%zu,\"stride_bytes\":%zu,\"seconds\":%.2f,\"median_ns\":%.2f,"
              "\"p90_ns\":%.2f,\"p99_ns\":%.2f,\"p999_ns\":%.2f,\"max_ns\":%.2f,\"longest_chunk_us\":%.0f,"
              "\"slow_time_share\":%.4f,\"bursts\":%zu,\"median_gap_ms\":%.1f,\"median_burst_ms\":%.2f}\n",
              cpu, bytes, stride, total_ms / 1e3, med, q(0.9), q(0.99), q(0.999), q(1.0), longest_us,
              slow_ms / total_ms, starts.size(), median(gaps), median(lengths));
  if (!out.empty()) {
    FILE* f = std::fopen(out.c_str(), "w");
    if (!f) { std::perror(out.c_str()); return 1; }
    std::fprintf(f, "t_ms,ns_per_load\n");
    for (size_t i = 0; i < ns.size(); ++i) std::fprintf(f, "%.3f,%.2f\n", at_ms[i], ns[i]);
    std::fclose(f);
  }
  return 0;
}

}  // namespace

int main(int argc, char** argv) {
  int cpu = -1;
  size_t max_mib = 1024;
  unsigned per_octave = 4;
  double ms = 20;
  uint64_t seed = 1;
  size_t stride = 64;
  double watch_mib = 0, watch_s = 10;
  std::string watch_out;
  try {
    for (int a = 1; a + 1 < argc; a += 2) {
      const std::string k = argv[a], v = argv[a + 1];
      if (k == "--cpu") cpu = int(Count(k, v, CPU_SETSIZE - 1));
      else if (k == "--max-mib") max_mib = Count(k, v, SIZE_MAX >> 20);
      else if (k == "--per-octave") per_octave = unsigned(Count(k, v, UINT32_MAX));
      else if (k == "--ms") ms = Number(k, v);
      else if (k == "--seed") seed = Count(k, v);
      else if (k == "--stride") stride = Count(k, v);
      else if (k == "--watch-mib") watch_mib = Number(k, v);
      else if (k == "--watch-s") watch_s = Number(k, v);
      else if (k == "--watch-out") watch_out = v;
      else { std::fprintf(stderr, "unknown option %s\n", k.c_str()); return 2; }
    }
  } catch (const std::exception& e) {
    std::fprintf(stderr, "cpu_cache_latency_benchmark: %s\n", e.what());
    return 2;
  }
  if (argc % 2 == 0 || per_octave == 0 || max_mib == 0 || watch_mib < 0 || watch_s <= 0 || stride < 64 ||
      stride % 64 != 0) {
    std::fprintf(stderr, "usage: cpu_cache_latency_benchmark [--cpu N] [--max-mib M] "
                         "[--per-octave K] [--ms T] [--seed S] [--stride B]\n"
                         "           [--watch-mib W [--watch-s S] [--watch-out FILE]]\n");
    return 2;
  }
  if (cpu < 0) cpu = sched_getcpu();
  cpu_set_t set;
  CPU_ZERO(&set);
  CPU_SET(cpu, &set);
  if (sched_setaffinity(0, sizeof(set), &set) != 0) { std::perror("sched_setaffinity"); return 1; }
  const Caches nominal = SysfsCaches(cpu);

  const Clock::time_point start = Clock::now();
  const size_t watch_bytes = size_t(watch_mib * 1048576) / stride * stride;
  if (watch_bytes > 0) max_mib = (watch_bytes + (1 << 20) - 1) >> 20;
  const size_t max_bytes = max_mib << 20;
  if (stride > max_bytes || (watch_mib > 0 && watch_bytes == 0)) {
    std::fprintf(stderr, "cpu_cache_latency_benchmark: --stride %zu does not fit the %s\n", stride,
                 watch_mib > 0 ? "--watch-mib working set" : "--max-mib buffer");
    return 2;
  }
  void* map = mmap(nullptr, max_bytes, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (map == MAP_FAILED) { std::perror("mmap"); return 1; }
  uint8_t* buf = static_cast<uint8_t*>(map);
  madvise(buf, max_bytes, MADV_HUGEPAGE);
  if (madvise(buf, max_bytes, MADV_POPULATE_WRITE) != 0) std::memset(buf, 1, max_bytes);
  const uint64_t huge = AnonHugeBytes();
  if (watch_bytes > 0) return Watch(buf, watch_bytes, stride, watch_s, seed, cpu, watch_out);

  std::vector<size_t> sizes;
  for (unsigned i = 0;; ++i) {
    const double bytes = 4096.0 * std::exp2(double(i) / per_octave);
    const size_t w = std::max(size_t(bytes) / stride, size_t{1}) * stride;
    if (w > max_bytes) break;
    if (sizes.empty() || w != sizes.back()) sizes.push_back(w);
  }
  if (sizes.back() != max_bytes) sizes.push_back(max_bytes);

  std::printf("cpu %d; sysfs L1d %zu KiB, L2 %zu KiB, L3 %zu KiB; buffer %zu MiB, %llu MiB on huge pages; "
              "one line per %zu B\n",
              cpu, nominal.l1d >> 10, nominal.l2 >> 10, nominal.l3 >> 10, max_mib,
              (unsigned long long)(huge >> 20), stride);
  std::printf("  working set    ns/load\n");
  std::vector<uint32_t> order;
  std::vector<double> ns(sizes.size());
  for (size_t s = 0; s < sizes.size(); ++s) {
    const size_t lines = sizes[s] / stride;
    uint8_t* p = BuildCycle(buf, lines, stride, order, seed + s);
    Chase(&p, 0.05, lines);  // one lap, or 50 ms
    double runs[3];
    for (double& r : runs) r = Chase(&p, ms / 3e3, ~uint64_t{0});
    std::sort(runs, runs + 3);
    ns[s] = runs[1];
    asm volatile("" : : "r"(p));
    if (sizes[s] < (size_t{1} << 20)) {
      std::printf("  %8.1f KiB  %8.2f\n", sizes[s] / 1024.0, ns[s]);
    } else {
      std::printf("  %8.1f MiB  %8.2f\n", sizes[s] / 1048576.0, ns[s]);
    }
  }
  munmap(map, max_bytes);

  // The latency at the largest measured working set not above `bytes`.
  const auto at = [&](size_t bytes) {
    size_t s = 0;
    while (s + 1 < sizes.size() && sizes[s + 1] <= bytes) ++s;
    return ns[s];
  };
  const double dram = ns.back();
  size_t usable = 0;
  for (size_t s = 0; s < sizes.size() && ns[s] <= dram / 4; ++s) usable = sizes[s];
  const size_t l3_probe = nominal.l3 ? std::min(4 * nominal.l2, nominal.l3 / 2) : 4 * nominal.l2;
  char json[1024];
  std::snprintf(json, sizeof(json),
                "{\"cpu\":%d,\"sysfs_l1d_bytes\":%zu,\"sysfs_l2_bytes\":%zu,\"sysfs_l3_bytes\":%zu,"
                "\"l1_ns\":%.2f,\"l2_ns\":%.2f,\"l3_ns\":%.2f,\"l3_probe_bytes\":%zu,"
                "\"dram_ns\":%.2f,\"dram_probe_bytes\":%zu,\"usable_cache_bytes\":%zu,"
                "\"huge_page_bytes\":%llu,\"stride_bytes\":%zu,\"seconds\":%.2f}",
                cpu, nominal.l1d, nominal.l2, nominal.l3, at(nominal.l1d / 2), at(nominal.l2 / 2),
                at(l3_probe), l3_probe, dram, sizes.back(), usable, (unsigned long long)huge,
                stride, SecondsSince(start));
  std::printf("L1 %.2f ns, L2 %.2f ns, L3 %.2f ns (at %zu KiB), DRAM %.2f ns (at %zu MiB); "
              "usable cache %.1f MiB (latency <= DRAM/4)\n",
              at(nominal.l1d / 2), at(nominal.l2 / 2), at(l3_probe), l3_probe >> 10, dram,
              sizes.back() >> 20, usable / 1048576.0);
  std::printf("CACHE_SUMMARY %s\n", json);
  return 0;
}
