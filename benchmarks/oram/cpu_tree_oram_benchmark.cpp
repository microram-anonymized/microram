// The comparison the tree ORAM exists to win or lose: at each value width,
// one steady-state cycle of reads through
//
//   (a) TreeByteMap  -- a hierarchical-ORAM position map over the byte-sliced
//                       read-path tree ORAM, values in the tree;
//   (b) ByteMap<>    -- the hierarchical ORAM holding the values directly;
//
// and, in cpu_tree_oram_benchmark_phase_timed (built with
// MICRORAM_TREE_PHASE_TIMER, refused by release builds), (a) split into its position-map and
// tree phases as timed inside every read of the cycle (three clock reads per
// access).  The plain build prints "-" there.
//
// Both engines are filled by writing every key once (which for (b) drives the
// whole rebuild cascade including the fixed last level), then drained, then
// timed over `capacity` reads in a fixed permuted order.  Arena is each map's
// own report, so the storage column is bytes actually reserved and not a model.
//
// Usage:
//   cpu_tree_oram_benchmark [min_log2_n] [max_log2_n] [value_list]
//                           [memory_limit_gib] [reps] [key_bytes]
//                           [max_cycle_accesses] [mode]
// mode 0 (the default) is the comparison above, with TreeOptions{} -- so the
// tree runs its width-selected payload workers.  mode 2 is the payload
// workers at K = 0..12, mode 5 the crossover at equal request-side cores.
// Defaults: 16 .. 20, "64,256,1024,4096", 12 GiB, 3 reps, 8-byte keys, a
// 131072-access cap on the TIMED cycle (the fill is always the full capacity,
// so the hierarchy's last-level rebuild always runs; the cap only bounds how
// many steady-state reads are then timed, which at a 4 KiB value is minutes
// per repetition otherwise).
// A configuration whose estimated arena exceeds the limit is reported skipped.
// `--help` prints the usage; a malformed or out-of-range argument (min_log2_n
// above max_log2_n, zero reps, an unknown mode) prints it to stderr and exits 2.

#include <cpu_byteslice_oram/tree_oram.hpp>

#include "benchmarks/oram/cpu_byteslice_benchmark_support.hpp"

#include <algorithm>
#include <charconv>
#include <chrono>
#include <climits>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <vector>

namespace {

namespace oram = cpu_byteslice_oram;
using microram::byteslice::benchmark_support::Clock;
using microram::byteslice::benchmark_support::SplitMix64;

double Seconds(Clock::time_point t0) {
  return std::chrono::duration<double>(Clock::now() - t0).count();
}

// A whole unsigned decimal in [min, max]: no sign, no trailing text.
uint64_t ParseCount(const std::string& name, const std::string& text,
                    uint64_t min, uint64_t max) {
  uint64_t value = 0;
  const auto r = std::from_chars(text.data(), text.data() + text.size(), value);
  if (text.empty() || r.ec != std::errc{} || r.ptr != text.data() + text.size() ||
      value < min || value > max) {
    throw std::invalid_argument(name + " must be an integer in [" + std::to_string(min) +
                                ", " + std::to_string(max) + "], not '" + text + "'");
  }
  return value;
}

std::vector<size_t> ParseList(const char* text) {
  std::vector<size_t> out;
  const std::string s(text);
  size_t pos = 0;
  while (pos <= s.size()) {
    size_t comma = s.find(',', pos);
    if (comma == std::string::npos) comma = s.size();
    out.push_back(static_cast<size_t>(
        ParseCount("value_list entry", s.substr(pos, comma - pos), 1, SIZE_MAX)));
    pos = comma + 1;
  }
  return out;
}

void Usage(std::FILE* out) {
  std::fprintf(out,
               "usage: cpu_tree_oram_benchmark [min_log2_n] [max_log2_n] [value_list]\n"
               "           [memory_limit_gib] [reps] [key_bytes] [max_cycle_accesses] [mode]\n"
               "  positional; defaults 16 20 64,256,1024,4096 12 3 8 131072 0.\n"
               "  mode 0 compares the tree and the hierarchy, 2 sweeps payload workers,\n"
               "  5 compares both at equal request-side cores (see the file header).\n");
}

// A fixed odd-multiplier permutation of [1, n], truncated to `cap`.
std::vector<uint64_t> PermutedKeys(size_t n, size_t cap) {
  std::vector<uint64_t> keys;
  keys.reserve(n);
  size_t pot = 1;
  while (pot < n) pot <<= 1;
  constexpr uint64_t kOdd = 0x9E3779B97F4A7C15ull;
  for (size_t i = 0; keys.size() < n; ++i) {
    const uint64_t k = ((uint64_t{i} * kOdd) & (pot - 1)) + 1;
    if (k <= n) keys.push_back(k);
  }
  if (keys.size() > cap) keys.resize(cap);
  return keys;
}

void MakeValue(uint64_t key, uint8_t* value, size_t bytes) {
  uint64_t state = key;
  for (size_t i = 0; i < bytes; ++i) value[i] = static_cast<uint8_t>(SplitMix64(state));
}

struct Result {
  double fill_ns = 0;
  double read_ns = 0;
  size_t arena = 0;
  size_t arena_tree = 0;
  size_t arena_posmap = 0;
  size_t capacity = 0;
  unsigned max_stash = 0;
  uint64_t checksum = 0;
  double position_map_ns = 0;  // phase timer builds: per read of the cycle
  double tree_phase_ns = 0;
};

// The phase clocks of a tree map in a MICRORAM_TREE_PHASE_TIMER build.
template <typename Map>
auto PhaseOf(const Map& map, int) -> decltype(map.phase_nanos()) { return map.phase_nanos(); }
template <typename Map>
std::nullptr_t PhaseOf(const Map&, long) { return nullptr; }

template <typename Map>
Result FillAndCycle(Map& map, size_t n, size_t key_bytes, size_t value_bytes,
                    const std::vector<uint64_t>& keys) {
  Result r;
  std::vector<uint8_t> key(key_bytes, 0), value(value_bytes);
  const auto fill0 = Clock::now();
  for (uint64_t k = 1; k <= n; ++k) {
    std::memcpy(key.data(), &k, std::min<size_t>(8, key_bytes));
    MakeValue(k, value.data(), value_bytes);
    map.insert_or_assign(key.data(), value.data());
  }
  map.drain_rebuilds();
  r.fill_ns = Seconds(fill0) * 1e9 / n;
  const auto phase0 = PhaseOf(map, 0);
  const auto read0 = Clock::now();
  for (uint64_t k : keys) {
    std::memcpy(key.data(), &k, std::min<size_t>(8, key_bytes));
    if (!map.find(key.data(), value.data())) {
      std::fprintf(stderr, "benchmark read missed key %llu\n",
                   static_cast<unsigned long long>(k));
      std::exit(1);
    }
    r.checksum += value[0];
  }
  r.read_ns = Seconds(read0) * 1e9 / keys.size();
  if constexpr (!std::is_same_v<decltype(phase0), const std::nullptr_t>) {
    const auto phase1 = PhaseOf(map, 0);
    r.position_map_ns = double(phase1.position_map - phase0.position_map) / keys.size();
    r.tree_phase_ns = double(phase1.tree - phase0.tree) / keys.size();
  }
  r.arena = map.arena_bytes();
  r.capacity = map.capacity();
  return r;
}

// Conservative pre-allocation estimates, so a row that would swap is skipped
// instead of taken.  The tree holds two slots per entry at a power-of-two
// capacity (load 0.5, the stash lanes counted), a slot being the entry
// rounded up to its 16-byte chunks, with 10% of margin; its position map is
// a hierarchy of (key, 16-byte) entries.  The hierarchy's is the 2 + (S+2)/D
// closed form at its worst reachable D.
double TreeGiB(size_t n, size_t value_bytes, size_t key_bytes) {
  const double slot = static_cast<double>((16 + value_bytes + 15) / 16 * 16);
  return (2.2 * n * slot + 5.6 * n * (key_bytes + 16.0)) / (1024.0 * 1024 * 1024);
}
double HierarchyGiB(size_t n, size_t value_bytes, size_t key_bytes) {
  return 5.6 * n * (key_bytes + value_bytes + 6.0) / (1024.0 * 1024 * 1024);
}

// ---------------------------------------------------------------------------
// mode 2: the payload workers (src/oram/tree/DESIGN.md, "Parallel payload")
// ---------------------------------------------------------------------------
//
// The same fill and the same steady cycle, over the synchronous engine and
// over the byte-column split at several K, threaded.  Two times per row:
//
//   read ns   the access as a caller sees it -- the return, which under the
//             workers happens while their write-back is still running;
//   done ns   the same cycle with a DRAIN inside the timed loop, so the
//             write-back is paid for on the critical path.  `read` is the
//             latency a dependent caller sees and `done` bounds the
//             sustained interval; the truth for a paced load is between
//             them, and they coincide when the workers are the bottleneck.
struct WorkerResult {
  double read_ns = 0;
  double done_ns = 0;
  size_t arena = 0;
  unsigned stash = 0;
  unsigned planes = 0;
  uint64_t checksum = 0;
};

template <typename Map>
WorkerResult CycleWithDrain(Map& map, size_t n, size_t key_bytes,
                            size_t value_bytes,
                            const std::vector<uint64_t>& keys) {
  WorkerResult r;
  std::vector<uint8_t> key(key_bytes, 0), value(value_bytes);
  for (uint64_t k = 1; k <= n; ++k) {
    std::memcpy(key.data(), &k, std::min<size_t>(8, key_bytes));
    MakeValue(k, value.data(), value_bytes);
    map.insert_or_assign(key.data(), value.data());
  }
  map.drain_rebuilds();
  map.drain_tree();
  for (unsigned phase = 0; phase < 2; ++phase) {
    const bool drain = phase == 1;
    const auto t0 = Clock::now();
    for (uint64_t k : keys) {
      std::memcpy(key.data(), &k, std::min<size_t>(8, key_bytes));
      if (!map.find(key.data(), value.data())) {
        std::fprintf(stderr, "benchmark read missed key %llu\n",
                     static_cast<unsigned long long>(k));
        std::exit(1);
      }
      if (drain) map.drain_tree();
      r.checksum += value[0];
    }
    const double ns = Seconds(t0) * 1e9 / keys.size();
    if (drain) r.done_ns = ns; else r.read_ns = ns;
    map.drain_tree();
  }
  r.arena = map.arena_bytes();
  r.stash = map.max_stash_occupancy();
  r.planes = map.payload_planes();
  return r;
}

int RunPayloadWorkers(unsigned min_log2, unsigned max_log2,
                      const std::vector<size_t>& widths, double limit_gib,
                      unsigned reps, size_t key_bytes, size_t cycle_cap) {
  struct Variant {
    const char* name;
    unsigned workers;
  };
  const Variant variants[] = {
      {"sync", 0},        // the shipped engine; every ratio is to it
      {"workers K=1", 1},
      {"workers K=2", 2},
      {"workers K=3", 3},
      {"workers K=4", 4},
      {"workers K=6", 6},
      {"workers K=8", 8},
      {"workers K=10", 10},
      {"workers K=12", 12},
  };
  constexpr unsigned kVariants =
      static_cast<unsigned>(sizeof(variants) / sizeof(variants[0]));
  std::printf(
      "payload workers, one steady-state cycle each, best of %u.  `sync` is "
      "the synchronous engine (payload_max_threads = 0). `workers K` gives each payload "
      "plane a thread; the main thread keeps the metadata plane, the "
      "position map and the planning, so the row costs K + 1 cores.  `read` "
      "is the access as the caller sees it, `done` the same cycle with a "
      "drain inside, i.e. with the workers' write-back on the critical "
      "path.  Ratios are against `sync`'s read.\n",
      reps);
  std::printf("%8s %6s %3s | %-12s %6s %9s %9s %9s %8s %6s\n", "entries", "V",
              "P", "variant", "planes", "read ns", "done ns", "x sync",
              "MiB", "peak");
  for (unsigned log2_n = min_log2; log2_n <= max_log2; ++log2_n) {
    const size_t n = size_t{1} << log2_n;
    const std::vector<uint64_t> keys = PermutedKeys(n, cycle_cap);
    for (size_t v : widths) {
      if (TreeGiB(n, v, key_bytes) > limit_gib) {
        std::printf("%8zu %6zu | skipped (%.1f GiB estimated)\n", n, v,
                    TreeGiB(n, v, key_bytes));
        continue;
      }
      WorkerResult best[kVariants];
      unsigned path_levels = 0;
      uint64_t checksum = 0;
      for (unsigned rep = 0; rep < reps; ++rep) {
        for (unsigned vi = 0; vi < kVariants; ++vi) {
          oram::TreeOptions options;
          options.payload_max_threads = variants[vi].workers;
          options.payload_threshold = 1;
          // The workers are meant to be hot: the cycle's arrival gap is a
          // few microseconds and a wake is ~15, so a parked worker would
          // measure the wake and nothing else.
          options.payload_spin_micros = 100000;
          oram::TreeByteMap<> map(n, key_bytes, v, options);
          const WorkerResult r = CycleWithDrain(map, n, key_bytes, v, keys);
          if (rep == 0 || r.read_ns < best[vi].read_ns) best[vi] = r;
          path_levels = map.path_levels();
          checksum += r.checksum;
        }
      }
      for (unsigned vi = 0; vi < kVariants; ++vi) {
        std::printf("%8zu %6zu %3u | %-12s %6u %9.0f %9.0f %8.2fx %8.0f %6u\n",
                    n, v, path_levels, variants[vi].name, best[vi].planes,
                    best[vi].read_ns, best[vi].done_ns,
                    best[0].read_ns / best[vi].read_ns,
                    best[vi].arena / 1048576.0, best[vi].stash);
      }
      (void)checksum;
      std::fflush(stdout);
    }
  }
  return 0;
}

// ---------------------------------------------------------------------------
// mode 5: the crossover at the same core budget
// ---------------------------------------------------------------------------
//
// `K` payload workers are `K` more busy cores, and the hierarchy has its own
// way to spend cores: `deamortized_batch_participants` gives a batch its
// parallel tiles, one per request-side core.  Comparing the tree's worker
// rows against a SERIAL hierarchy would be the wrong comparison, so this mode
// runs both sides at several core counts and reports the request-side thread
// count with each.
//
// The participant count INCLUDES the calling thread, so the `threads` column
// below is exactly the knob, not one more than it.
//
// The hierarchy's rows use the batch API over the same permuted key order,
// which is a different contract -- a caller who has only one request at a
// time cannot use it -- so the serial hierarchy row is kept as the
// like-for-like one.
int RunCrossover(unsigned min_log2, unsigned max_log2,
                 const std::vector<size_t>& widths, double limit_gib,
                 unsigned reps, size_t key_bytes, size_t cycle_cap) {
  struct Row {
    const char* name;
    bool tree;
    unsigned workers;   // tree: payload planes; hierarchy: batch participants
    unsigned lanes;     // hierarchy only: batch lanes, 0 = serial
    unsigned threads;   // request-side threads the row occupies
  };
  const Row rows[] = {
      {"tree sync", true, 0, 0, 1},
      {"tree K=1", true, 1, 0, 2},
      {"tree K=2", true, 2, 0, 3},
      {"tree K=3", true, 3, 0, 4},
      {"tree K=4", true, 4, 0, 5},
      {"hier serial", false, 1, 0, 1},
      {"hier batch x1", false, 1, 16, 1},
      {"hier batch x2", false, 2, 16, 2},
      {"hier batch x4", false, 4, 16, 4},
  };
  constexpr unsigned kRows = static_cast<unsigned>(sizeof(rows) / sizeof(rows[0]));
  std::printf(
      "the crossover at equal cores, best of %u.  `tree K` is the "
      "byte-column split: K payload planes plus this thread, so K + 1 "
      "request-side cores.  `hier batch xT` is ByteMap's batch API at 16 "
      "lanes over T parallel tiles, the calling thread included, so T "
      "request-side cores.  `hier serial` is the like-for-like "
      "single-request contract.  Ratios are tree/hier at the same thread "
      "count, so below 1.00 the tree wins.\n",
      reps);
  std::printf("%8s %6s | %-14s %7s %9s %9s\n", "entries", "V", "row",
              "threads", "ns", "MiB");
  for (unsigned log2_n = min_log2; log2_n <= max_log2; ++log2_n) {
    const size_t n = size_t{1} << log2_n;
    const std::vector<uint64_t> keys = PermutedKeys(n, cycle_cap);
    for (size_t v : widths) {
      if (TreeGiB(n, v, key_bytes) > limit_gib ||
          HierarchyGiB(n, v, key_bytes) > limit_gib) {
        std::printf("%8zu %6zu | skipped\n", n, v);
        continue;
      }
      double best[kRows] = {};
      size_t arena[kRows] = {};
      uint64_t checksum = 0;
      std::vector<uint8_t> key(key_bytes, 0), value(v);
      for (unsigned rep = 0; rep < reps; ++rep) {
        for (unsigned ri = 0; ri < kRows; ++ri) {
          double ns = 0;
          if (rows[ri].tree) {
            oram::TreeOptions options;
            options.payload_max_threads = rows[ri].workers;
            options.payload_threshold = 1;
            options.payload_spin_micros = 100000;
            oram::TreeByteMap<> map(n, key_bytes, v, options);
            const WorkerResult r = CycleWithDrain(map, n, key_bytes, v, keys);
            ns = r.read_ns;
            arena[ri] = r.arena;
            checksum += r.checksum;
          } else {
            oram::Options options;
            // The tiles are the hierarchy's request-side cores.  More than
            // one needs the parallel shape: the chunked cascade runs on the
            // calling thread alone and REFUSES extra participants.
            options.deamortized_batch_participants = rows[ri].workers;
            if (rows[ri].workers > 1) {
              options.deamortized_batch_execution =
                  oram::BatchExecutionShape::kParallelTiles;
            }
            if (rows[ri].lanes != 0) {
              options.deamortized_batch_lanes = rows[ri].lanes;
            }
            oram::ByteMap<> map(n, key_bytes, v, options);
            for (uint64_t k = 1; k <= n; ++k) {
              std::memcpy(key.data(), &k, std::min<size_t>(8, key_bytes));
              MakeValue(k, value.data(), v);
              map.insert_or_assign(key.data(), value.data());
            }
            map.drain_rebuilds();
            // Every key of the cycle was filled: the found bits the calls
            // return are summed (one add per read) and checked after the
            // timed cycle, as the tree rows check theirs.  Values are not
            // compared.
            uint64_t hits = 0;
            const auto t0 = Clock::now();
            if (rows[ri].lanes == 0) {
              for (uint64_t k : keys) {
                std::memcpy(key.data(), &k, std::min<size_t>(8, key_bytes));
                hits += map.find(key.data(), value.data());
                checksum += value[0];
              }
            } else {
              // One batch of `lanes` requests at a time, which is what the
              // batch API is for: its chunk's DRAM misses overlap.
              const size_t lanes = rows[ri].lanes;
              std::vector<std::vector<uint8_t>> keybuf(lanes,
                                                       std::vector<uint8_t>(key_bytes, 0));
              std::vector<std::vector<uint8_t>> valbuf(lanes,
                                                       std::vector<uint8_t>(v));
              std::vector<oram::BatchRequest> reqs(lanes);
              std::vector<uint8_t> found(lanes);
              for (size_t i = 0; i < keys.size(); i += lanes) {
                const size_t m = std::min(lanes, keys.size() - i);
                for (size_t j = 0; j < m; ++j) {
                  std::memcpy(keybuf[j].data(), &keys[i + j],
                              std::min<size_t>(8, key_bytes));
                  reqs[j] = oram::BatchRequest{};
                  reqs[j].op = oram::BatchOp::kRead;
                  reqs[j].key = keybuf[j].data();
                  reqs[j].value_out = valbuf[j].data();
                }
                map.access_batch(m, reqs.data(), found.data());
                for (size_t j = 0; j < m; ++j) {
                  checksum += valbuf[j][0];
                  hits += found[j];
                }
              }
            }
            ns = Seconds(t0) * 1e9 / keys.size();
            if (hits != keys.size()) {
              std::fprintf(stderr, "benchmark read missed %llu of %zu keys (%s)\n",
                           static_cast<unsigned long long>(keys.size() - hits),
                           keys.size(), rows[ri].name);
              std::exit(1);
            }
            arena[ri] = map.arena_bytes();
          }
          if (rep == 0 || ns < best[ri]) best[ri] = ns;
        }
      }
      for (unsigned ri = 0; ri < kRows; ++ri) {
        std::printf("%8zu %6zu | %-14s %7u %9.0f %9.0f\n", n, v,
                    rows[ri].name, rows[ri].threads, best[ri],
                    arena[ri] / 1048576.0);
      }
      (void)checksum;
      std::fflush(stdout);
    }
  }
  return 0;
}

}  // namespace

int main(int argc, char** argv) {
  unsigned min_log2 = 16, max_log2 = 20;
  std::vector<size_t> widths = {64, 256, 1024, 4096};
  double limit_gib = 12.0;
  unsigned reps = 3;
  size_t key_bytes = 8;
  size_t cycle_cap = 131072;
  unsigned mode = 0;
  if (argc > 1 && (std::strcmp(argv[1], "--help") == 0 || std::strcmp(argv[1], "-h") == 0)) {
    Usage(stdout);
    return 0;
  }
  // Strict positional arguments: a malformed one is a usage error, never 0.
  try {
    if (argc > 9) throw std::invalid_argument("at most 8 arguments");
    if (argc > 1) min_log2 = static_cast<unsigned>(ParseCount("min_log2_n", argv[1], 0, 63));
    if (argc > 2) max_log2 = static_cast<unsigned>(ParseCount("max_log2_n", argv[2], 0, 63));
    if (min_log2 > max_log2) throw std::invalid_argument("min_log2_n exceeds max_log2_n");
    if (argc > 3) widths = ParseList(argv[3]);
    if (argc > 4) {
      char* end = nullptr;
      limit_gib = std::strtod(argv[4], &end);
      if (end == argv[4] || *end != '\0' || !(limit_gib > 0) || !std::isfinite(limit_gib))
        throw std::invalid_argument(std::string("memory_limit_gib must be a positive number, not '") +
                                    argv[4] + "'");
    }
    if (argc > 5) reps = static_cast<unsigned>(ParseCount("reps", argv[5], 1, UINT_MAX));
    if (argc > 6) key_bytes = static_cast<size_t>(ParseCount("key_bytes", argv[6], 1, SIZE_MAX));
    if (argc > 7) cycle_cap = static_cast<size_t>(ParseCount("max_cycle_accesses", argv[7], 1, SIZE_MAX));
    if (argc > 8) mode = static_cast<unsigned>(ParseCount("mode", argv[8], 0, UINT_MAX));
    if (mode != 0 && mode != 2 && mode != 5) throw std::invalid_argument("mode must be 0, 2 or 5");
  } catch (const std::exception& e) {
    std::fprintf(stderr, "cpu_tree_oram_benchmark: %s\n", e.what());
    Usage(stderr);
    return 2;
  }
  if (mode == 2) {
    return RunPayloadWorkers(min_log2, max_log2, widths, limit_gib, reps,
                             key_bytes, cycle_cap);
  }
  if (mode == 5) {
    return RunCrossover(min_log2, max_log2, widths, limit_gib, reps, key_bytes,
                        cycle_cap);
  }

  std::printf("cpu_tree_oram_benchmark: one steady-state cycle of reads after a "
              "full fill, %zu-byte keys, medians of %u.  tree = "
              "TreeByteMap<> (hierarchical position map + tree ORAM); hier = "
              "ByteMap<> holding the values; pm phase / tree phase = ns per "
              "read inside `tree`'s accesses, from the phase timer "
              "(cpu_tree_oram_benchmark_phase_timed only; '-' otherwise).  "
              "The fill is always the full capacity; the timed "
              "cycle is capped at %zu reads.\n",
              key_bytes, reps, cycle_cap);
  std::printf("%8s %6s | %9s %9s %6s | %9s %9s %6s | %8s %8s | %9s\n",
              "entries", "V", "tree MiB", "hier MiB", "ratio", "tree ns",
              "hier ns", "ratio", "pm phase", "tree ph", "tree MB/s");
  for (unsigned log2_n = min_log2; log2_n <= max_log2; ++log2_n) {
    const size_t n = size_t{1} << log2_n;
    const std::vector<uint64_t> keys = PermutedKeys(n, cycle_cap);
    for (size_t v : widths) {
      const double tree_gib = TreeGiB(n, v, key_bytes);
      const double hier_gib = HierarchyGiB(n, v, key_bytes);
      if (tree_gib > limit_gib && hier_gib > limit_gib) {
        std::printf("%8zu %6zu | %s (%.1f / %.1f GiB estimated, limit %.1f)\n",
                    n, v, "skipped", tree_gib, hier_gib, limit_gib);
        continue;
      }
      std::vector<double> tree_ns, hier_ns, pm_ns, tp_ns;
      size_t tree_arena = 0, hier_arena = 0;
      unsigned max_stash = 0;
      uint64_t checksum = 0;
      for (unsigned rep = 0; rep < reps; ++rep) {
        if (tree_gib <= limit_gib) {
          oram::TreeOptions options;
          oram::TreeByteMap<> map(n, key_bytes, v, options);
          const Result r = FillAndCycle(map, n, key_bytes, v, keys);
          tree_ns.push_back(r.read_ns);
          pm_ns.push_back(r.position_map_ns);
          tp_ns.push_back(r.tree_phase_ns);
          tree_arena = map.arena_bytes();
          max_stash = std::max(max_stash, map.max_stash_occupancy());
          checksum += r.checksum;
        }
        if (hier_gib <= limit_gib) {
          oram::Options options;
          oram::ByteMap<> map(n, key_bytes, v, options);
          const Result r = FillAndCycle(map, n, key_bytes, v, keys);
          hier_ns.push_back(r.read_ns);
          hier_arena = map.arena_bytes();
          checksum += r.checksum;
        }
      }
      auto median = [](std::vector<double>& xs) {
        if (xs.empty()) return 0.0;
        std::sort(xs.begin(), xs.end());
        return xs[xs.size() / 2];
      };
      const double t = median(tree_ns), h = median(hier_ns), p = median(pm_ns), tp = median(tp_ns);
      std::printf("%8zu %6zu | ", n, v);
      if (t > 0) std::printf("%9.1f ", tree_arena / 1048576.0);
      else std::printf("%9s ", "-");
      if (h > 0) std::printf("%9.1f ", hier_arena / 1048576.0);
      else std::printf("%9s ", "-");
      if (t > 0 && h > 0) std::printf("%6.2f | ", double(tree_arena) / hier_arena);
      else std::printf("%6s | ", "-");
      if (t > 0) std::printf("%9.0f ", t); else std::printf("%9s ", "-");
      if (h > 0) std::printf("%9.0f ", h); else std::printf("%9s ", "-");
      if (t > 0 && h > 0) std::printf("%6.2f | ", t / h);
      else std::printf("%6s | ", "-");
      if (p > 0) std::printf("%8.0f %8.0f | ", p, tp);
      else std::printf("%8s %8s | ", "-", "-");
      if (t > 0) std::printf("%9.0f", v / (t * 1e-9) / 1e6);
      else std::printf("%9s", "-");
      std::printf("   [%llu, max stash %u]\n",
                  static_cast<unsigned long long>(checksum & 0xffff), max_stash);
      std::fflush(stdout);
    }
  }
  return 0;
}
