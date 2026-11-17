// Occupancy observer: occupancy of every residual structure of the level-arena
// engine (the stashes that absorb records a bucket cannot hold), at the
// unchanged public capacities, over a long saturated run.
//
// DIAGNOSTIC ONLY.  The target is compiled with
// MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER, whose hook receives secret-dependent
// occupancies (src/oram/levelarena/cpu_byteslice_level_arena_occupancy.hpp);
// the macro is refused by CPU_BYTESLICE_ORAM_RELEASE, and nothing this binary
// prints is a performance row.  Its timing says only how long the run took.
//
// WHAT IS OBSERVED, and where each is at its maximum, is in that header: stage
// stashes and radix/merge/retained-carry stashes at
// the start of the pass that consumes them, DFS range-table leaves right after
// the build, and published tiers when their job ends.  Capacities are the
// engine's own (the same ORAM, never reduced or forced), so an occupancy above
// its capacity is unrepresentable: a natural overflow shows up as a thrown,
// declared failure, which this driver records and stops on.
//
// WORKLOAD ("H", the label in the JSON output): the map is initialized full
// (every key present), then `settle` unobserved accesses let the hierarchy
// leave its initial state, then `accesses` observed ones: 95 % reads and 5 %
// updates of uniformly drawn EXISTING keys, back to back (saturation, no
// external arrivals).  `--batch N` issues them through access_batch in groups
// of N.
//
// EXECUTION MODE (labelled in the output): one caller thread, owners 0,
// helpers 0, lanes 1 by default -- the requester drives every rebuild state
// machine at flush boundaries.  The flags change the mode and the label.
//
// Output: one JSON object.  Per structure identity (kind, level, index) it has
// the capacity, exposure count, maximum, histogram of occupancy (entries) and
// the per-job maximum sequence, from which analysis/occupancy_tail.py forms
// block-based tails.  Range leaves are aggregated per (level, pass) over all
// their leaves; a job's value is the maximum over its leaves.
//
// Usage: cpu_byteslice_occupancy_observer [flags]
//   --capacity N (2^16)  --key-bytes K (4)  --value-bytes V (8)
//   --branching B (8)  --top-digit D (0 = planner)  --prefix-flushes N (0)
//   --accesses N (default max(10^7, capacity))   --settle N (default capacity)
//   --update-percent P (5)  --batch N (0 = scalar)
//   --owners N (0)  --top-helpers N (0)  --bottom-helpers N (0)  --lanes N (1)
//   --rebuild-threads N (library default)  --seed S  --access-seed S
//   --out FILE (default stdout)

#ifndef MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER
#error "cpu_byteslice_occupancy_observer must be built with MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER (see CMakeLists.txt)"
#endif

#include "include/cpu_byteslice_oram/oram.hpp"

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <exception>
#include <map>
#include <memory>
#include <mutex>
#include <random>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>

#include "benchmarks/oram/cpu_byteslice_benchmark_support.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_occupancy.hpp"

namespace {

namespace oram = cpu_byteslice_oram;
namespace bs = microram::byteslice;
namespace la = microram::byteslice::levelarena;

struct Args {
  size_t capacity = size_t{1} << 16;
  size_t key_bytes = 4, value_bytes = 8;
  unsigned branching = 8, top_digit = 0, prefix_flushes = 0;
  uint64_t accesses = 0;  // 0: max(10^7, capacity)
  int64_t settle = -1;    // -1: capacity
  unsigned update_percent = 5;
  unsigned batch = 0;
  unsigned owners = 0, top_helpers = 0, bottom_helpers = 0, lanes = 1;
  int rebuild_threads = -1;
  uint64_t seed = 20260831, access_seed = 7;
  std::string out;
};

// One structure identity's record.
struct Stat {
  size_t capacity = 0;
  uint64_t events = 0;
  size_t max = 0;
  uint64_t overflows = 0;  // occupancy > capacity; unrepresentable, kept to say so
  std::vector<uint64_t> hist;
  std::vector<uint16_t> job_max;  // per job that exposed this structure
  uint64_t cur_job = 0;
  size_t cur_max = 0;
  bool open = false;
};

using Key = std::tuple<unsigned, unsigned, unsigned>;  // kind, level, index

std::mutex g_mutex;
bool g_measuring = false;
std::map<Key, Stat> g_stats;

void Hook(const la::OccupancyEvent& e) {
  std::lock_guard<std::mutex> lock(g_mutex);
  if (!g_measuring) return;
  Stat& s = g_stats[Key{static_cast<unsigned>(e.kind), e.level, e.index}];
  s.capacity = std::max(s.capacity, e.capacity);
  if (s.hist.size() < e.capacity + 1) s.hist.resize(e.capacity + 1, 0);
  ++s.events;
  if (e.occupancy > e.capacity) ++s.overflows;
  const size_t occ = std::min(e.occupancy, e.capacity);
  ++s.hist[occ];
  s.max = std::max(s.max, e.occupancy);
  if (!s.open || s.cur_job != e.job) {
    if (s.open) s.job_max.push_back(static_cast<uint16_t>(s.cur_max));
    s.open = true;
    s.cur_job = e.job;
    s.cur_max = 0;
  }
  s.cur_max = std::max(s.cur_max, e.occupancy);
}

Args ParseArgs(int argc, char** argv) {
  Args a;
  for (int i = 1; i < argc; ++i) {
    const std::string arg = argv[i];
    auto next = [&]() -> uint64_t {
      if (i + 1 >= argc) throw std::invalid_argument(arg + " needs a value");
      return std::strtoull(argv[++i], nullptr, 10);
    };
    if (arg == "--capacity") a.capacity = next();
    else if (arg == "--key-bytes") a.key_bytes = next();
    else if (arg == "--value-bytes") a.value_bytes = next();
    else if (arg == "--branching") a.branching = unsigned(next());
    else if (arg == "--top-digit") a.top_digit = unsigned(next());
    else if (arg == "--prefix-flushes") a.prefix_flushes = unsigned(next());
    else if (arg == "--accesses") a.accesses = next();
    else if (arg == "--settle") a.settle = int64_t(next());
    else if (arg == "--update-percent") a.update_percent = unsigned(next());
    else if (arg == "--batch") a.batch = unsigned(next());
    else if (arg == "--owners") a.owners = unsigned(next());
    else if (arg == "--top-helpers") a.top_helpers = unsigned(next());
    else if (arg == "--bottom-helpers") a.bottom_helpers = unsigned(next());
    else if (arg == "--lanes") a.lanes = unsigned(next());
    else if (arg == "--rebuild-threads") a.rebuild_threads = int(next());
    else if (arg == "--seed") a.seed = next();
    else if (arg == "--access-seed") a.access_seed = next();
    else if (arg == "--out") {
      if (i + 1 >= argc) throw std::invalid_argument("--out needs a value");
      a.out = argv[++i];
    } else {
      throw std::invalid_argument("unknown flag " + arg);
    }
  }
  if (a.update_percent > 100) throw std::invalid_argument("--update-percent > 100");
  return a;
}

void EncodeKey(uint64_t key, uint8_t* out, size_t key_bytes) {
  std::memset(out, 0, key_bytes);
  std::memcpy(out, &key, std::min(key_bytes, sizeof(key)));
}

std::string JsonEscape(const std::string& s) {
  std::string out;
  for (char c : s) {
    if (c == '"' || c == '\\') out += '\\';
    out += (c == '\n') ? ' ' : c;
  }
  return out;
}

}  // namespace

int main(int argc, char** argv) {
  Args args;
  try {
    args = ParseArgs(argc, argv);
  } catch (const std::exception& e) {
    std::fprintf(stderr, "%s\n", e.what());
    return 2;
  }
  oram::Options options;
  options.deamortized_branching_factor = args.branching;
  options.deamortized_top_digit = args.top_digit;
  options.deamortized_prefix_flushes = args.prefix_flushes;
  options.deamortized_owner_threads = args.owners;
  options.deamortized_top_helpers = args.top_helpers;
  options.deamortized_bottom_helpers = args.bottom_helpers;
  options.deamortized_rebuild_lanes = args.lanes;
  if (args.rebuild_threads >= 0) {
    options.deamortized_rebuild_threads = static_cast<unsigned>(args.rebuild_threads);
  }
  options.secret_seed = microram::crypto::SecretKeySeed::Fixed(args.seed);

  // A shape no geometry supports is refused before anything runs.  The fill
  // and the accesses use the ids 0 .. capacity() - 1 as keys, so the ROUNDED
  // capacity must fit the key space (`initialize` takes distinct keys).  The
  // output is opened before the run, so a bad --out costs no run.
  la::LevelArenaCapacityChoice choice;
  std::unique_ptr<oram::ByteMap<>> built;
  try {
    choice = oram::ByteMap<>::plan_geometry(args.capacity, args.key_bytes,
                                            args.value_bytes, options);
    if (args.key_bytes < 8 &&
        choice.capacity > (uint64_t{1} << (8 * args.key_bytes))) {
      throw std::invalid_argument(
          "capacity " + std::to_string(choice.capacity) + " (requested " +
          std::to_string(args.capacity) + ") exceeds the key space");
    }
    built = std::make_unique<oram::ByteMap<>>(args.capacity, args.key_bytes,
                                              args.value_bytes, options);
  } catch (const std::exception& e) {
    std::fprintf(stderr, "%s\n", e.what());
    return 2;
  }
  oram::ByteMap<>& map = *built;
  std::FILE* f = args.out.empty() ? stdout : std::fopen(args.out.c_str(), "w");
  if (f == nullptr) {
    std::fprintf(stderr, "cannot open %s\n", args.out.c_str());
    return 2;
  }
  const size_t capacity = map.capacity();
  const uint64_t accesses =
      args.accesses ? args.accesses
                    : std::max<uint64_t>(10000000, capacity);
  const uint64_t settle =
      args.settle < 0 ? capacity : static_cast<uint64_t>(args.settle);
  const la::LevelArenaCertification cert = map.certification();

  std::fprintf(stderr,
               "occupancy observer: capacity %zu (requested %zu), B=%u r0=%u "
               "D=%u L=%u, K%zu/V%zu, owners %u helpers %u/%u lanes %u, "
               "batch %u; settle %llu + observe %llu accesses\n",
               capacity, args.capacity, choice.geometry.branching,
               choice.geometry.prefix_flushes, choice.geometry.top_digit,
               choice.geometry.levels, args.key_bytes, args.value_bytes,
               args.owners, args.top_helpers, args.bottom_helpers, args.lanes,
               args.batch, static_cast<unsigned long long>(settle),
               static_cast<unsigned long long>(accesses));

  la::SetOccupancyHook(&Hook);
  std::string failure;
  uint64_t done_settle = 0, done_observed = 0;
  const auto t0 = std::chrono::steady_clock::now();
  try {
    auto records = bs::benchmark_support::MakeGeneratedRecords(
        0, args.key_bytes, args.value_bytes,
        [&](uint64_t id, uint8_t* o) { EncodeKey(id, o, args.key_bytes); },
        [&](uint64_t id, uint8_t*o, size_t n) {
          std::memset(o, 0, n);
          std::memcpy(o, &id, std::min(n, sizeof(id)));
        });
    map.initialize(records, capacity);  // fills are not observed

    std::mt19937_64 rng(args.access_seed);
    std::vector<uint8_t> key(args.key_bytes), value(args.value_bytes, 0x5a),
        out(args.value_bytes);
    const unsigned group = std::max(1u, args.batch);
    std::vector<uint8_t> keys(group * args.key_bytes);
    std::vector<uint8_t> values(group * args.value_bytes, 0x5a);
    std::vector<uint8_t> outs(group * args.value_bytes);
    std::vector<bs::BatchRequest> reqs(group);
    auto run = [&](uint64_t count, uint64_t* done) {
      uint64_t i = 0;
      while (i < count) {
        if (args.batch == 0) {
          EncodeKey(rng() % capacity, key.data(), args.key_bytes);
          if (rng() % 100 < args.update_percent) {
            value[0] = static_cast<uint8_t>(i);
            map.insert_or_assign(key.data(), value.data());
          } else {
            map.find(key.data(), out.data());
          }
          ++i;
        } else {
          const size_t n = static_cast<size_t>(std::min<uint64_t>(group, count - i));
          for (size_t j = 0; j < n; ++j) {
            EncodeKey(rng() % capacity, keys.data() + j * args.key_bytes,
                      args.key_bytes);
            const bool update = rng() % 100 < args.update_percent;
            reqs[j] = bs::BatchRequest{
                update ? bs::BatchOp::kWrite : bs::BatchOp::kRead, false,
                keys.data() + j * args.key_bytes,
                update ? values.data() + j * args.value_bytes : nullptr,
                update ? nullptr : outs.data() + j * args.value_bytes};
          }
          map.access_batch(n, reqs.data(), nullptr);
          i += n;
        }
        *done = i;
      }
    };
    run(settle, &done_settle);
    {
      std::lock_guard<std::mutex> lock(g_mutex);
      g_measuring = true;
    }
    run(accesses, &done_observed);
    map.drain_rebuilds();
  } catch (const std::exception& e) {
    failure = e.what();
  }
  {
    std::lock_guard<std::mutex> lock(g_mutex);
    g_measuring = false;
  }
  la::SetOccupancyHook(nullptr);
  const double seconds =
      std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  const bool natural_overflow =
      !failure.empty() && (failure.find("ran out of room") != std::string::npos ||
                           failure.find("overflow") != std::string::npos ||
                           failure.find("certified depth") != std::string::npos);

  std::fprintf(f, "{\"schema\":\"occupancy_observer_v1\",\n \"meta\":{");
  std::fprintf(f,
               "\"capacity\":%zu,\"requested_capacity\":%zu,\"key_bytes\":%zu,"
               "\"value_bytes\":%zu,\"branching\":%u,\"prefix_flushes\":%u,"
               "\"top_digit\":%u,\"levels\":%u,\"workload\":\"H\","
               "\"update_percent\":%u,\"batch\":%u,"
               "\"mode\":\"one caller, owners=%u, top_helpers=%u, "
               "bottom_helpers=%u, lanes=%u%s\","
               "\"settle_accesses\":%llu,\"observed_accesses\":%llu,"
               "\"requested_observed_accesses\":%llu,\"seed\":%llu,"
               "\"access_seed\":%llu,\"wall_seconds\":%.3f,",
               capacity, args.capacity, args.key_bytes, args.value_bytes,
               choice.geometry.branching, choice.geometry.prefix_flushes,
               choice.geometry.top_digit, choice.geometry.levels,
               args.update_percent, args.batch, args.owners, args.top_helpers,
               args.bottom_helpers, args.lanes,
               args.batch ? ", batched" : ", scalar",
               static_cast<unsigned long long>(done_settle),
               static_cast<unsigned long long>(done_observed),
               static_cast<unsigned long long>(accesses),
               static_cast<unsigned long long>(args.seed),
               static_cast<unsigned long long>(args.access_seed), seconds);
  {
    std::string ladder;
    for (unsigned b : choice.geometry.level_fanouts) {
      ladder += (ladder.empty() ? "" : ",") + std::to_string(b);
    }
    std::fprintf(f, "\"level_fanouts\":[%s],", ladder.c_str());
  }
  std::fprintf(f,
               "\"certification_status\":\"%s\",\"certification_record\":\"%s\","
               "\"certification_bound_log2\":%s,",
               la::LevelArenaCertificationStatusName(cert.status),
               JsonEscape(cert.record).c_str(),
               cert.failure_bound_log2()
                   ? std::to_string(*cert.failure_bound_log2()).c_str()
                   : "null");
  std::fprintf(f,
               "\"failure\":\"%s\",\"natural_overflow\":%s,"
               "\"limitation\":\"observed occupancies of one seed and one run;"
               " zero overflows do not establish 2^-64\"},\n",
               JsonEscape(failure).c_str(), natural_overflow ? "true" : "false");
  std::fprintf(f, " \"structures\":[");
  bool first = true;
  for (auto& kv : g_stats) {
    Stat& s = kv.second;
    if (s.open) s.job_max.push_back(static_cast<uint16_t>(s.cur_max));
    std::fprintf(f, "%s\n  {\"kind\":\"%s\",\"level\":%u,\"index\":%u,"
                    "\"capacity\":%zu,\"events\":%llu,\"max\":%zu,"
                    "\"overflows\":%llu,\"jobs\":%zu,\"hist\":[",
                 first ? "" : ",",
                 la::OccupancyKindName(static_cast<la::OccupancyKind>(std::get<0>(kv.first))),
                 std::get<1>(kv.first), std::get<2>(kv.first), s.capacity,
                 static_cast<unsigned long long>(s.events), s.max,
                 static_cast<unsigned long long>(s.overflows), s.job_max.size());
    first = false;
    for (size_t i = 0; i < s.hist.size(); ++i) {
      std::fprintf(f, "%s%llu", i ? "," : "",
                   static_cast<unsigned long long>(s.hist[i]));
    }
    std::fprintf(f, "],\"job_max\":[");
    for (size_t i = 0; i < s.job_max.size(); ++i) {
      std::fprintf(f, "%s%u", i ? "," : "", unsigned(s.job_max[i]));
    }
    std::fprintf(f, "]}");
  }
  std::fprintf(f, "\n ]}\n");
  if (f != stdout) std::fclose(f);
  if (!failure.empty()) {
    std::fprintf(stderr, "run stopped: %s\n", failure.c_str());
    return 1;
  }
  return 0;
}
