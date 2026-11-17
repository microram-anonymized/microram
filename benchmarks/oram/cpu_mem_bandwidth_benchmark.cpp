// The host's memory bandwidth, and how much of it is left over while
// something else runs.
//
// WHY THIS EXISTS.  The ORAM's own byte counters are bucket-touch BOUNDS:
// they count a line the same whether it came from DRAM or from L2, so
// multiplying them by a throughput overstates the DRAM traffic and cannot say
// whether a run is bandwidth bound.
//
// The PMU does not answer it reliably either.  `PERF_COUNT_HW_CACHE_LL` with
// a MISS result is refused on some hosts (perf_event_open returns -1 under
// many hypervisors), and the generic `PERF_COUNT_HW_CACHE_MISSES` counts only
// DEMAND misses: a sequential stream is served by the hardware prefetcher, and
// a prefetched line is not a miss, so a counter-based bandwidth figure for a
// streaming loop understates the traffic by more than an order of magnitude.
//
// What works is subtraction, which is what this benchmark does:
//
//   --sweep    reads a large buffer with 1, 2, 4, ... threads and reports the
//              bandwidth each width achieves.  That is the CEILING, and the
//              shape of the curve says where it saturates.
//   --compete  runs N streaming threads for S seconds and reports what they
//              achieved.  Run it BESIDE another process (the ORAM benchmark,
//              say) and the bandwidth the competitor loses against its --sweep
//              figure is the bandwidth that process was using; what the other
//              process loses is how much it cared.
//
// Measure for seconds, not milliseconds: a short loop still pays first-touch
// page faults and reports a bandwidth well below the ceiling.
//
// READING A --compete RUN.  A process that gives up a much larger share of
// its throughput than the share of the bandwidth ceiling it was consuming is
// waiting on memory LATENCY, not starved of bandwidth: the ORAM's probes and
// its rebuild's routing are dependent random accesses, and when the memory
// controller is busy every one of them takes longer.  Extra rebuild threads
// that are latency-bound in the same way buy little, and more memory channels
// raise the ceiling but not the latency.
//
// Usage: cpu_mem_bandwidth_benchmark [options]
//   --sweep 1,2,4,8        thread counts to measure (default)
//   --compete 2            run this many streaming threads and report, for use
//                          beside another process
//   --seconds 10           how long --compete runs (and the minimum a --sweep
//                          width runs)
//   --mib-per-thread 512   buffer per thread; must exceed the last-level cache
//   --first-core -1        pin thread i to core first-core + i; -1 = the OS
//
// On a multi-CCD (multi-L3) host it also serves as a per-CCD and cross-CCD
// bandwidth probe: pin the threads to one CCD with --first-core, then spread
// them, and compare.

#include <immintrin.h>

#include <atomic>
#include <cctype>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>

#if defined(__linux__)
#include <pthread.h>
#include <sched.h>
#endif

namespace {

using Clock = std::chrono::steady_clock;

double SecondsSince(Clock::time_point start) {
  return std::chrono::duration<double>(Clock::now() - start).count();
}

void PinCurrentThread(int core) {
#if defined(__linux__)
  if (core < 0) return;
  cpu_set_t set;
  CPU_ZERO(&set);
  CPU_SET(static_cast<unsigned>(core), &set);
  if (pthread_setaffinity_np(pthread_self(), sizeof(set), &set) != 0) {
    std::fprintf(stderr, "cannot pin to cpu %d\n", core);
    std::exit(1);
  }
#else
  (void)core;
#endif
}

// One thread's streaming read.  Ordinary loads, not `_mm512_stream_load_si512`:
// non-temporal loads bypass the cache hierarchy and can read noticeably
// slower than ordinary ones, so they would understate the ceiling the ORAM
// actually competes for.  The accumulator is reduced into a sink so the loop
// cannot be optimised away.
double StreamRead(uint8_t* base, size_t bytes, double until, int core) {
  PinCurrentThread(core);
  __m512i acc = _mm512_setzero_si512();
  double read = 0.0;
  const Clock::time_point start = Clock::now();
  do {
    for (size_t off = 0; off < bytes; off += 64) {
      acc = _mm512_add_epi64(
          acc, _mm512_load_si512(reinterpret_cast<const void*>(base + off)));
    }
    read += static_cast<double>(bytes);
  } while (SecondsSince(start) < until);
  // Summed as unsigned lanes: the sum wraps by design, and a signed
  // reduction (`_mm512_reduce_add_epi64`) would overflow.
  alignas(64) uint64_t lanes[8];
  _mm512_store_si512(lanes, acc);
  uint64_t sum = 0;
  for (uint64_t lane : lanes) sum += lane;
  volatile uint64_t sink = sum;
  (void)sink;
  return read;
}

struct Args {
  std::vector<unsigned> sweep = {1, 2, 4, 8};
  unsigned compete = 0;
  double seconds = 10.0;
  size_t mib_per_thread = 512;
  int first_core = -1;
};

// An option's value, the whole of it, in [lo, hi]: a trailing character or
// an empty value is refused rather than read as a prefix.
long long Whole(const std::string& flag, const std::string& v, long long lo, long long hi) {
  size_t used = 0;
  long long x = 0;
  if (!v.empty() && (std::isdigit(static_cast<unsigned char>(v[0])) || v[0] == '-')) {
    try {
      x = std::stoll(v, &used);
    } catch (const std::exception&) {
      used = 0;
    }
  }
  if (used == 0 || used != v.size() || x < lo || x > hi) {
    throw std::invalid_argument(flag + " " + v + ": expected a whole number from " +
                                std::to_string(lo) + " to " + std::to_string(hi));
  }
  return x;
}

std::vector<unsigned> ParseList(const std::string& text) {
  std::vector<unsigned> out;
  size_t start = 0;
  while (start <= text.size()) {
    const size_t comma = text.find(',', start);
    const std::string token = text.substr(
        start, comma == std::string::npos ? std::string::npos : comma - start);
    if (!token.empty()) out.push_back(static_cast<unsigned>(Whole("--sweep", token, 1, CPU_SETSIZE)));
    if (comma == std::string::npos) break;
    start = comma + 1;
  }
  if (out.empty()) throw std::invalid_argument("--sweep needs at least one thread count");
  return out;
}

// One measurement at `threads` width: each thread owns its own buffer, so the
// widths differ in nothing but how many streams the controller is serving.
double Measure(unsigned threads, const Args& a) {
  const size_t bytes = a.mib_per_thread * 1024 * 1024;
  std::vector<uint8_t*> buffers(threads);
  for (unsigned t = 0; t < threads; ++t) {
    buffers[t] = static_cast<uint8_t*>(std::aligned_alloc(64, bytes));
    if (buffers[t] == nullptr) {
      std::fprintf(stderr, "out of memory at %u threads\n", threads);
      std::exit(1);
    }
    std::memset(buffers[t], 1, bytes);  // fault the pages in before timing
  }
  std::vector<double> read(threads, 0.0);
  std::vector<std::thread> pool;
  pool.reserve(threads);
  const Clock::time_point start = Clock::now();
  for (unsigned t = 0; t < threads; ++t) {
    const int core = a.first_core < 0 ? -1 : a.first_core + static_cast<int>(t);
    pool.emplace_back([&, t, core] {
      read[t] = StreamRead(buffers[t], bytes, a.seconds, core);
    });
  }
  for (std::thread& th : pool) th.join();
  const double wall = SecondsSince(start);
  double total = 0.0;
  for (double r : read) total += r;
  for (uint8_t* buffer : buffers) std::free(buffer);
  return total / 1e9 / wall;
}

}  // namespace

int main(int argc, char** argv) {
  Args a;
  bool sweep_given = false;
  if (argc % 2 == 0) {
    std::fprintf(stderr, "cpu_mem_bandwidth_benchmark: %s needs a value\n", argv[argc - 1]);
    return 2;
  }
  try {
    for (int i = 1; i + 1 < argc; i += 2) {
      const std::string k = argv[i];
      const std::string v = argv[i + 1];
      if (k == "--sweep") { a.sweep = ParseList(v); sweep_given = true; }
      else if (k == "--compete") a.compete = static_cast<unsigned>(Whole(k, v, 0, CPU_SETSIZE));
      else if (k == "--seconds") {
        size_t used = 0;
        try {
          a.seconds = std::stod(v, &used);
        } catch (const std::exception&) {
          used = 0;
        }
        if (used == 0 || used != v.size() || !std::isfinite(a.seconds) || !(a.seconds > 0)) {
          throw std::invalid_argument("--seconds " + v + ": expected a positive number");
        }
      }
      else if (k == "--mib-per-thread") a.mib_per_thread = static_cast<size_t>(Whole(k, v, 1, 1ll << 30));
      else if (k == "--first-core") a.first_core = static_cast<int>(Whole(k, v, -1, CPU_SETSIZE - 1));
      else {
        std::fprintf(stderr, "unknown option %s\n", k.c_str());
        return 2;
      }
    }
  } catch (const std::exception& e) {
    std::fprintf(stderr, "cpu_mem_bandwidth_benchmark: %s\n", e.what());
    return 2;
  }
  if (a.compete != 0 && !sweep_given) a.sweep.clear();

  if (!a.sweep.empty()) {
    std::printf("cpu_mem_bandwidth_benchmark: streaming reads, %zu MiB per "
                "thread, %.1f s per width, cores %s\n",
                a.mib_per_thread, a.seconds,
                a.first_core < 0 ? "left to the OS" : "pinned from --first-core");
    std::printf("threads |   GB/s | per thread\n");
    for (unsigned threads : a.sweep) {
      const double gbs = Measure(threads, a);
      std::printf("%7u | %6.1f | %6.1f\n", threads, gbs, gbs / threads);
      std::fflush(stdout);
    }
  }
  if (a.compete != 0) {
    // The competitor: report what it achieved, so a run beside another process
    // can be subtracted from a --sweep row of the same width.
    const double gbs = Measure(a.compete, a);
    std::printf("competitor: %u threads achieved %.1f GB/s over %.1f s\n",
                a.compete, gbs, a.seconds);
  }
  return 0;
}
