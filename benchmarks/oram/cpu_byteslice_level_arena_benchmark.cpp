// THE LEVEL-ARENA BENCHMARK.
//
// It measures ONE engine -- `cpu_byteslice_oram::ByteMap`, the per-level arena
// engine of src/oram/levelarena/ -- under a closed-loop read/write workload,
// and reports what that engine is doing while it runs: the completed request
// rate, the cascade it probes, the buffer byte bill by role, per-level phase
// time, and every wait anybody did and why.
//
// A single-engine rate on a shared machine carries the machine's drift in it.
// `--reps` runs the whole measurement several times on freshly built engines
// and reports the MEDIAN rate, which controls for a rep that lands on a busy
// moment; it cannot control for a trend over the life of the process, which
// only an interleaved pair of arms can (the campaign harness in
// analysis/oram_bench alternates arms for that reason).  Treat a difference
// smaller than the spread between reps as nothing.
//
// WHAT IS REPORTED:
//
//   - completed request rate and the accesses and capacity behind it;
//   - the per-request CASCADE counters -- tables and buckets the last access
//     probed -- which are a function of the published plan alone and so are
//     public;
//   - the buffer byte bill by role (mains, dense storage, tiers, masks and
//     scratch), with requested and allocator-reserved kept apart.  NOTE that
//     `byte_bill()` is the whole engine's bill and `arena_bytes()` reports its
//     requested total, which is NOT the geometry-only arena figure of the
//     closed-form storage model -- that one is `main_arena_bytes()`, printed
//     beside it below;
//   - per-LEVEL phase time (prepare / merge / publish) and the preparation hit
//     rate, which is what says whether speculative preparation is paying;
//   - wait-reason parks and their durations, per owner group;
//   - per-(level, digit) JOB COST -- count, mean and worst of one carry's
//     preparation + merge + publication -- which is what worst-case grouping
//     and deadline scheduling of rebuild jobs are judged on;
//   - with `--latency`, the REQUESTER'S per-call wall time as a histogram:
//     p50 .. p99.99, the maximum, and how many calls stalled past 1, 10 and
//     100 ms.  One clock read per call; off by default.
//
// RESULTS: every probing request draws a key the warm-up inserted, so the
// benchmark sums the found bits its calls return (one add per request) and
// refuses, after the settle or the window, a run in which any lookup missed.
// Returned values are not compared.
//
// EVERY COUNTER IS OVER THE MEASURED WINDOW ONLY: the warm-up's work is
// snapshotted after its drain and subtracted.  The one exception is a job's
// WORST cost, which is a lifetime maximum; a job's work is a function of its
// public shape, so warm-up jobs of the same digit are the same work.
// `--accesses` defaults to one capacity, because a level's per-access cost is
// only an average over whole cycles of its digits.
//
// THE BATCH PATH: `--batch N` issues the same workload N requests at a time
// through `access_batch`, at the chosen lane width and participant count, and
// `--batch 0` is the scalar surface it is to be read against.  `--place`
// additionally pins the request thread and its batch participants to one
// cache domain and the FAR owner groups (the owners of the large, DRAM-bound
// levels) to another, so their streaming does not evict the small levels the
// requester probes from the shared L3.  Its control is simply leaving it off:
// the near/far split of the owner groups and the placement are one decision,
// and moving the whole owner pool across, without the split, does not help.
//
// AN OFFERED RATE (`--rate KOPS`, scalar only): each request has an arrival
// time -- fixed rate -- the request thread waits for it, and the latency histogram records every request's RESPONSE
// time, from its arrival to its completion.  So a stall is counted as the
// queue it builds: every request that arrived during it is late by what is
// left of it.  A closed loop instead turns a stall into a lower rate, and its
// stall counts say little.  `--settle N` runs N unmeasured requests at the
// same rate first, so the window opens on a running pipeline and not on the
// empty one the warm-up's drain leaves.  The window then starts its own
// arrival schedule with an empty queue: a backlog the settle ends with is not
// carried into the window's response times.  With `--write-only` this is the
// high-demand case of many requesters on one cache domain and the rebuild
// owners on another, at a load the owners can sustain on average.
//
// REQUEST-CORRELATED BACKPRESSURE, under `--rate` or `--latency`:
// the engine counts the requester's slow-path wait for a dense prefix slot,
// the benchmark reads that count around every request, and a request with a
// nonzero delta was delayed by rebuild by exactly that much.  Reported: the
// delayed requests, all completed requests, their ratio, the maximum and p99
// attributed stall and the total, beside the response times and per-level
// parks.  In batch mode a batch's delta is charged to every request in it.
//
// THE REBUILD-SERVICE THROTTLE, `--rebuild-slowdown K`, exists only
// in cpu_byteslice_level_arena_benchmark_throttled, the same source built with
// MICRORAM_BYTESLICE_LEVEL_ARENA_PAUSE.  It slows every OWNER thread to 1/K of
// its speed (after each group poll, spin (K-1) times the time since the last
// poll, parked time excluded) and nothing else: run it with helpers 0 and
// lanes 1, since helper threads are not slowed.  The control arm is inline or
// unthrottled in the SAME binary (K = 1 installs no hook).  A slowdown factor
// is NOT a measured rate: the rebuild records/s at each K must be measured
// independently, e.g. this binary's closed-loop `--write-only` rate at that K,
// and the run reports its own completed records/s and flush rate for it.
//
// NOT REPORTED, and each is a limitation rather than an omission: offered-rate
// sweeps of the batch path (the one-trial worker, cpu_oram_benchmark.cpp,
// covers them with reads and probed writes), and FIFO stalls (the
// level-arena engine has no rebuild FIFO; its equivalent is the requester's
// prefix-slot backpressure, reported as requester parks).

#include <cpu_byteslice_oram/oram.hpp>

#include "benchmarks/oram/cpu_byteslice_benchmark_topology.hpp"
#include "src/oram/support/benchmark_arrival.hpp"

#include <immintrin.h>

#ifdef MICRORAM_BYTESLICE_LEVEL_ARENA_PAUSE
#include "src/oram/levelarena/cpu_byteslice_level_arena_pause.hpp"
#endif

#ifdef __linux__
#include <pthread.h>
#include <sched.h>
#endif

#include <algorithm>
#include <array>
#include <cerrno>
#include <charconv>
#include <chrono>
#include <climits>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

namespace {

namespace oram = cpu_byteslice_oram;
namespace bs = microram::byteslice;
namespace la = microram::byteslice::levelarena;

using Clock = std::chrono::steady_clock;

double SecondsSince(Clock::time_point start) {
  return std::chrono::duration<double>(Clock::now() - start).count();
}

uint64_t SplitMix64(uint64_t& state) {
  uint64_t z = (state += 0x9E3779B97F4A7C15ull);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
  return z ^ (z >> 31);
}

// THE REQUESTER'S PER-CALL WALL TIME, log-linear: every power of two of
// nanoseconds is cut into 16 sub-buckets, so a percentile is exact to within
// 1/16 of its own magnitude.  The maximum and the stall counts are exact.
class LatencyHistogram {
 public:
  void Record(uint64_t nanos) {
    ++counts_[Index(nanos)];
    ++count_;
    max_ = std::max(max_, nanos);
    for (size_t t = 0; t < kStallThresholds; ++t) {
      if (nanos > kStallNanos[t]) {
        ++stalls_[t];
        stall_nanos_[t] += nanos;
      }
    }
  }
  uint64_t count() const { return count_; }
  uint64_t max() const { return max_; }
  // The upper edge of the bucket holding the p-quantile.
  uint64_t Percentile(double p) const {
    if (count_ == 0) return 0;
    const uint64_t rank = static_cast<uint64_t>(p * double(count_ - 1)) + 1;
    uint64_t seen = 0;
    for (size_t i = 0; i < counts_.size(); ++i) {
      seen += counts_[i];
      if (seen >= rank) return std::min(UpperEdge(i), max_);
    }
    return max_;
  }
  static constexpr size_t kStallThresholds = 3;
  static constexpr uint64_t kStallNanos[kStallThresholds] = {
      1000000, 10000000, 100000000};
  uint64_t stalls(size_t t) const { return stalls_[t]; }
  uint64_t stall_nanos(size_t t) const { return stall_nanos_[t]; }

 private:
  static constexpr unsigned kSubBits = 4;
  static constexpr uint64_t kSub = uint64_t{1} << kSubBits;
  static size_t Index(uint64_t nanos) {
    if (nanos < kSub) return static_cast<size_t>(nanos);
    const unsigned k = 63u - static_cast<unsigned>(__builtin_clzll(nanos));
    const uint64_t sub = (nanos >> (k - kSubBits)) & (kSub - 1);
    return static_cast<size_t>((k - kSubBits + 1) * kSub + sub);
  }
  static uint64_t UpperEdge(size_t index) {
    if (index < kSub) return index + 1;
    const unsigned k = static_cast<unsigned>(index / kSub) + kSubBits - 1;
    const uint64_t sub = index % kSub;
    return (kSub + sub + 1) << (k - kSubBits);
  }
  std::array<uint64_t, 64 * kSub> counts_{};
  uint64_t count_ = 0;
  uint64_t max_ = 0;
  uint64_t stalls_[kStallThresholds] = {};
  uint64_t stall_nanos_[kStallThresholds] = {};
};

// REQUEST-CORRELATED REBUILD BACKPRESSURE.  The engine counts, on
// the slow path of AwaitPrefixSlots only, the episodes and nanoseconds the
// requester spent waiting for a dense prefix slot (LevelArenaEngine::
// requester_backpressure).  The request thread reads that pair before and
// after each request; a request whose delta is nonzero was delayed by rebuild,
// and the delta is the delay DIRECTLY attributed to it -- unlike a response
// time, which also holds the queue an earlier stall built.  A BATCH call is
// one unit: every request in it is charged the call's delta, so its delayed
// count is the batch size times the delayed calls and its stall total counts
// the delta once per request.  The maximum is exact; the p99 is the
// histogram's and is over the DELAYED requests only.
struct Backpressure {
  LatencyHistogram delays;  // attributed ns of each delayed request
  uint64_t requests = 0;    // every completed request in the window
  uint64_t delayed = 0;
  uint64_t nanos = 0;       // total attributed, ns
  uint64_t episodes = 0;
  bool enabled = false;
  void Record(size_t covered, uint64_t delta_nanos, uint64_t delta_episodes) {
    requests += covered;
    if (delta_nanos == 0 && delta_episodes == 0) return;
    delayed += covered;
    episodes += delta_episodes;
    nanos += delta_nanos * covered;
    for (size_t j = 0; j < covered; ++j) delays.Record(delta_nanos);
  }
  double delayed_percent() const {
    return requests ? 100.0 * double(delayed) / double(requests) : 0.0;
  }
};

// ---------------------------------------------------------------------------
// The configuration, all of it from the command line
// ---------------------------------------------------------------------------

struct Config {
  uint64_t capacity = 1u << 19;
  size_t key_bytes = 8;
  unsigned value_workers = 0, value_tail = 2;
  bs::ValueKernel value_kernel = bs::ValueKernel::kAuto;
  uint64_t value_spin_ns = 200000;
  bool value_pause = true, value_demote = false, value_profile = false;
  std::vector<int> value_cpus, rebuild_cpus;
  size_t value_bytes = 16;
  unsigned branching = 4;       // B, in {2, 4, 8}
  unsigned top_digit = 0;       // D; 0 lets the ladder choose
  size_t stash_entries = 64;    // the insertion unit (online stash entries)
  // r0, the stash flushes per dense prefix; 0 lets the ladder choose.  It
  // matters because what a serial or batched access scans on the dense side is
  // `r0 * s` buckets and not `s`, and because it and the insertion unit
  // are one tuning axis with two spellings.
  unsigned prefix_flushes = 0;
  unsigned dense_prefixes = 2;  // q, complete prefixes allowed outstanding
  unsigned owner_threads = 0;   // 0 inline, otherwise grouped/dedicated owners
  // A thread budget for the heuristic to divide (deamortized_rebuild_threads),
  // replacing `owner_threads`; 0 uses `owner_threads` as given.
  unsigned rebuild_threads = 0;
  // An explicit division, highest group first ("5-6,1-4"); empty lets the
  // heuristic choose.
  std::vector<la::LevelGroupPlan> groups;
  uint64_t accesses = 0;        // 0 is one capacity() of the built map
  bool latency = false;         // record the requester's per-call wall time
  // The per-request backpressure reads under --rate/--latency; 0 is the
  // control arm (analysis/arena_harness_gate.py) that times the same
  // requests without them, to show the reads do not perturb the timing.
  bool attribution = true;
  // The rate the owner groups' rebuild pieces are sized
  // for (0 is the saturated sequential rate), or a fixed piece size in bucket
  // touches.
  double slice_rate = 0.0;
  size_t slice_touches = 0;
  // The inline executor's per-flush work factor.
  double inline_share = la::kLevelArenaInlineWorkFactor;
  // Lanes per level (and the table size below which a
  // level takes one), and helper threads for the top's owner group.
  size_t rebuild_lanes = 1;
  size_t lane_min_buckets = size_t{1} << 15;
  unsigned top_helpers = 0;
  // Helpers for level 1's owner group, when it is not the top's.
  unsigned bottom_helpers = 0;
  // Every access a blind upsert (write): the requester
  // then costs almost nothing, and the rate is the rebuild's capacity.
  bool write_only = false;
  // Every access a find over the warmed keys.  A find inserts one entry at the
  // top like any access, so the rebuild work per access is the same.
  bool read_only = false;
  bool stage_times = false;  // time rebuild pieces by kind and stage class
  // The deamortization microbenchmark.  `preroute` false is --no-preroute:
  // no preparation starts before its carry is available, at any level.
  // `merge_rows` is the per-level ring of --merge-rows (0 keeps none): its
  // stamps need nothing else, its work by phase is piece time and needs
  // --stage-times too.
  // `probe_counts` tallies the tables, main tables and buckets every probing
  // request's cascade had; with `batch`, every lane of a call (one plan).
  bool preroute = true;
  size_t merge_rows = 0;
  bool probe_counts = false;
  // --storage synchronous: ByteMap<false>, the engine's synchronous storage
  // mode (every merge on the requester).  `--owners 0` alone is the
  // incremental INLINE executor, not this.
  bool synchronous = false;
  // The fanout ladder below the top: the half-fanout prefix at B = 8 (the
  // default), or B everywhere but a bottom fanout chosen by bytes.
  bool half_fanout_prefix = true;
  // One JSON line per level and per run, every repetition, for the rebuild
  // cost model's tuner (analysis/oram_bench/tuner.py): the model's features
  // as the library counts them, beside what was measured.
  bool fit_rows = false;
  // Bank-first: build each cycle's first digits in the idle odd bank.
  // The engine's default, kNoClone.
  la::BankFirst bank_first = la::BankFirst::kNoClone;
  // THE OFFERED RATE, in k accesses per second; 0 is the closed loop.  Scalar
  // only.  `settle` requests run at the same rate, unmeasured, before the window.
  double rate_kops = 0.0;
  // The rebuild-service throttle: every owner thread runs at 1/K of its
  // speed; 1 is unthrottled.
  // Accepted only by the throttled build.
  double rebuild_slowdown = 1.0;
  uint64_t settle = 0;
  unsigned repetitions = 3;     // fresh engines; the reported rate is the median
  uint64_t seed = 0x11E6;

  // ---- the batch path and placement ----
  // Requests per access_batch call; 0 drives the scalar surface, which is
  // the control the batch rows are read against.
  size_t batch = 0;
  unsigned lanes = 16;          // chunk width, per participant
  unsigned participants = 1;    // tiles, the calling thread included
  std::vector<int> cpus;       // explicit caller, helpers, rebuild owners
  bool profile_batch = false;
  bool bucket_scan = false;
  bool parallel_tiles = false;  // the execution shape at participants > 1
  bool place = false;           // pin near and far (multi-CCD hosts only)
  // The near/far boundary, or 0 for this host's own answer.  Only read when
  // `place` is set.
  unsigned near_max_level = 0;
};

// ---------------------------------------------------------------------------
// Placement
// ---------------------------------------------------------------------------

namespace topology = microram::byteslice::benchmark_topology;

// The host's CPUs grouped by L3 domain -- one CCD on a Zen part, one mesh
// (a socket or a sub-NUMA cluster's share of it) on a Xeon -- in a shape the
// library's pure placement policy can take.  ONE CPU PER PHYSICAL CORE, the
// lowest-numbered sibling, as the campaign harness places (near_far_v2): two
// threads on SMT siblings would share a core's execution units and halve
// what each measures.  The domain holding the lowest-numbered CPU comes first
// and becomes NEAR, which is where the request thread is put.
la::HostCacheDomains DiscoverDomains() {
  la::HostCacheDomains host;
  std::vector<std::string> names;
  std::vector<std::pair<int, int>> cores;  // (package, core) already taken
  for (const topology::Cpu& cpu : topology::Discover()) {
    const std::pair<int, int> core{cpu.package, cpu.core};
    if (std::find(cores.begin(), cores.end(), core) != cores.end()) continue;
    cores.push_back(core);
    const auto at = std::find(names.begin(), names.end(), cpu.l3);
    if (at == names.end()) {
      names.push_back(cpu.l3);
      host.domains.push_back({static_cast<int>(cpu.id)});
    } else {
      host.domains[at - names.begin()].push_back(static_cast<int>(cpu.id));
    }
  }
  for (std::vector<int>& domain : host.domains) {
    std::sort(domain.begin(), domain.end());
  }
  std::sort(host.domains.begin(), host.domains.end(),
            [](const std::vector<int>& a, const std::vector<int>& b) {
              return a.front() < b.front();
            });
  return host;
}

void PinTo(int cpu) {
  if (cpu < 0) return;
#ifdef __linux__
  cpu_set_t set;
  CPU_ZERO(&set);
  CPU_SET(static_cast<unsigned>(cpu), &set);
  if (pthread_setaffinity_np(pthread_self(), sizeof(set), &set) != 0) {
    throw std::runtime_error("could not pin a thread to its CPU");
  }
#else
  throw std::runtime_error("thread placement is supported only on Linux");
#endif
}

// A scope that puts the CALLING thread back where it was.  Every repetition
// runs on this thread, so one that pinned it and left would hand the next a
// placement it never asked for -- and `--place` on a single-domain host, which
// pins nothing, would then inherit the previous rep's affinity.
class RestoreAffinity {
 public:
#ifdef __linux__
  RestoreAffinity() {
    if (pthread_getaffinity_np(pthread_self(), sizeof(mask_), &mask_) != 0) {
      throw std::runtime_error("could not read this thread's affinity");
    }
  }
  ~RestoreAffinity() {
    pthread_setaffinity_np(pthread_self(), sizeof(mask_), &mask_);
  }

 private:
  cpu_set_t mask_{};
#else
  RestoreAffinity() = default;
#endif
};

// What the run was placed at, for the report.  Empty when nothing was pinned.
struct Placement {
  bool placed = false;
  unsigned near_max_level = 0;
  std::string describe;
};

// What one repetition produced.  Everything here is public: rates, counts of
// published work, and the shape of the cascade -- never occupancy, which is a
// function of the secret keys.  The one occupancy this benchmark prints, the
// live tier entries after the window (RunOnceWith), is a labelled
// diagnostic and is not kept here.
struct Result {
  double seconds = 0.0;
  uint64_t accesses = 0;
  size_t capacity = 0;
  size_t cascade_tables = 0;
  size_t cascade_buckets = 0;
  // The inline executor's share per flush and the estimate it is a multiple
  // of: routing and residual touches per flush (LevelArenaFlushTouches).
  uint64_t inline_flush_touches = 0;
  uint64_t inline_touches_charged = 0;  // over the window
  double routing_flush_touches = 0;
  double residual_flush_touches = 0;
  size_t requested_bytes = 0;
  size_t reserved_bytes = 0;
  size_t main_arena_bytes = 0;
  la::LevelArenaByteBill bill;
  std::vector<la::LevelStats> levels;
  uint64_t parks = 0;
  uint64_t park_nanos = 0;
  uint64_t requester_waits = 0;
  uint64_t requester_park_nanos = 0;
  std::vector<uint64_t> parks_by_reason;
  std::vector<uint64_t> park_nanos_by_reason;
  uint64_t flushes = 0;
  Placement placement;
  // The batch participants' waits: how often the request thread had to wait
  // for a phase to retire, and how often a participant had to wait for one
  // to arrive.  Zero on a scalar run.
  uint64_t batch_waits = 0;
  uint64_t batch_parks = 0;
  uint64_t preemptions = 0;  // phases stopped between pieces, all groups
  uint64_t declined = 0;  // signals a running phase did not stop for
  uint64_t credit_stops = 0;  // ... and stops to return an owed credit
  uint64_t helper_lanes = 0;  // lanes the top group's helpers ran
  std::string rebuild;  // the division, helpers, lanes and piece rate built
  std::string geometry;  // L, r0, D, the fanout ladder and the tier widths
  // Per level, over the window: [0] ordered, [1] divisible, [2..5] the phase
  // walls and counts, then per kind, then the folds' share of [0].
  std::vector<std::vector<uint64_t>> stage_nanos;
  std::vector<std::string> long_waits;  // what the long requester waits saw
  std::vector<std::string> fit_rows;    // --fit-rows: JSON, one line each
  // The execution mode, and the top merges that completed in the
  // window (ordinal above the last one before it), with their TOP_MERGE rows.
  std::string mode;
  std::vector<la::TopMergeRecord> top_merges;
  std::vector<std::string> top_rows;
  std::string compare_row;  // merge comparison counts, _compare_counted build only
  bool latency = false;
  size_t batch = 0;  // the requests per call the histogram's calls carried
  // Paced: `calls` holds response times from each request's arrival, and
  // this is the offered rate in k accesses/s (0 for the closed loop).
  double offered_kops = 0.0;
  LatencyHistogram calls;
  Backpressure backpressure;  // enabled under --rate or --latency
  uint64_t flushes_per_window = 0;
  double rebuild_slowdown = 1.0;
  bool accesses_whole_capacity = true;
  // --merge-rows: MERGE_ROW lines (window, merges, owners), and the measured
  // window's steady_clock bounds the merges are placed against.
  std::vector<std::string> merge_rows;
  uint64_t window_start_ns = 0;
  uint64_t window_end_ns = 0;
  // --probe-counts: the window's probing requests and their cascades.
  struct ProbeTally {
    uint64_t lookups = 0, tables = 0, buckets = 0, mains = 0;
    uint64_t max_tables = 0, max_buckets = 0, max_mains = 0;
    // `lanes` lookups that probed one plan of `t` tables, `b` buckets and
    // `plan_mains` main tables; `mains_probed` is the engine's count over
    // all of them.
    void Record(size_t lanes, size_t t, size_t b, uint64_t mains_probed,
                size_t plan_mains) {
      lookups += lanes;
      tables += lanes * t;
      buckets += lanes * b;
      mains += mains_probed;
      max_tables = std::max<uint64_t>(max_tables, t);
      max_buckets = std::max<uint64_t>(max_buckets, b);
      max_mains = std::max<uint64_t>(max_mains, plan_mains);
    }
  } probes;
  // Every owner group's idle time over the window (LevelGroup::idle_nanos).
  uint64_t owner_idle_nanos = 0;

  double kops() const {
    return seconds > 0 ? double(accesses) / seconds / 1000.0 : 0.0;
  }
};

// ---------------------------------------------------------------------------
// The workload
// ---------------------------------------------------------------------------
//
// Half-capacity warm-up, then a mixed read/write stream over the warmed keys.
// The workload is kept fixed on purpose, so that rows measured with different
// engine knobs stay comparable.

template <class Map>
void Warm(Map& map, const Config& config, size_t capacity) {
  std::vector<uint8_t> key(config.key_bytes, 0);
  std::vector<uint8_t> value(config.value_bytes, 0);
  const uint64_t warm = capacity / 2;
  for (uint64_t i = 0; i < warm; ++i) {
    std::memcpy(key.data(), &i, std::min(sizeof(i), config.key_bytes));
    std::memcpy(value.data(), &i, std::min(sizeof(i), config.value_bytes));
    map.insert_or_assign(key.data(), value.data());
  }
  map.drain_rebuilds();
}

// With `latency` non-null each call's wall time is recorded, from the end
// of the previous call to the end of this one: one clock read per call, and
// the key generation between two calls is charged to the later one.
//
// PACED (`config.rate_kops` > 0), request i is not issued before its arrival
// and what is recorded is its RESPONSE time, arrival to completion, so a
// request that waited behind a stall is charged the wait.  `first` is the
// index of the first request: it continues the read/write alternation and
// reseeds the key stream (seed + first), which is not where a settle's
// stream left off.  Each call starts its own arrival schedule at its own
// start, so a window run after a settle opens on an empty queue: a backlog
// the settle ended with is not carried into the window.
//
// `hits`, if given, receives how many probing requests found their key: the
// found bit each find or exchange returns, summed in a register and stored
// after the clock is read.  Every key drawn was warmed, so every one must hit.
template <class Map>
double RunScalar(Map& map, const Config& config, size_t capacity,
                 uint64_t accesses, LatencyHistogram* latency,
                 uint64_t first = 0, Backpressure* bp = nullptr,
                 Result::ProbeTally* probes = nullptr,
                 uint64_t* hits = nullptr) {
  std::vector<uint8_t> key(config.key_bytes, 0);
  std::vector<uint8_t> value(config.value_bytes, 0);
  std::vector<uint8_t> out(config.value_bytes, 0);
  const uint64_t span = std::max<uint64_t>(1, capacity / 2);
  uint64_t state = config.seed + first;
  const bool paced = config.rate_kops > 0;
  const oram_bench::FixedArrivals arrival(paced ? config.rate_kops : 1.0);
  uint64_t found = 0;
  const Clock::time_point start = Clock::now();
  Clock::time_point last = start;
  for (uint64_t n = 0; n < accesses; ++n) {
    const uint64_t i = first + n;
    if (paced) {
      last = start + std::chrono::nanoseconds(arrival.At(n));
      while (Clock::now() < last) _mm_pause();
    }
    const uint64_t k = SplitMix64(state) % span;
    std::memcpy(key.data(), &k, std::min(sizeof(k), config.key_bytes));
    const uint64_t bp_nanos = bp ? map.engine().requester_backpressure().nanos.get() : 0;
    const uint64_t bp_episodes = bp ? map.engine().requester_backpressure().episodes.get() : 0;
    const uint64_t mains = map.probe_mains();
    if (config.write_only) {
      // Preserve the sequential write-only workload. Blind writes also
      // support repeated keys within the same insertion unit.
      const uint64_t w = i % span;
      std::memcpy(key.data(), &w, std::min(sizeof(w), config.key_bytes));
      std::memcpy(value.data(), &i, std::min(sizeof(i), config.value_bytes));
      map.write(key.data(), value.data());
    } else if (config.read_only || (i & 1) == 0) {
      found += map.find(key.data(), out.data());
    } else {
      std::memcpy(value.data(), &i, std::min(sizeof(i), config.value_bytes));
      found += map.exchange(key.data(), value.data(), out.data(), true);
    }
    // Mixed writes read the old value too; write-only requests skip probing.
    if (probes != nullptr && !config.write_only) {
      probes->Record(1, map.last_probe_tables(), map.last_probe_buckets(),
                     map.probe_mains() - mains, map.last_probe_mains());
    }
    if (bp != nullptr) {
      bp->Record(1,
                 map.engine().requester_backpressure().nanos.get() - bp_nanos,
                 map.engine().requester_backpressure().episodes.get() - bp_episodes);
    }
    if (latency != nullptr) {
      const Clock::time_point now = Clock::now();
      latency->Record(static_cast<uint64_t>(
          std::chrono::duration_cast<std::chrono::nanoseconds>(now - last)
              .count()));
      last = now;
    }
  }
  const double seconds = SecondsSince(start);
  if (hits != nullptr) *hits = found;
  return seconds;
}

// THE SAME WORKLOAD, `config.batch` REQUESTS AT A TIME.  Same keys in the
// same order, same read/write alternation, same number of accesses; the only
// difference is that they are handed over together.  Building the request
// array OUTSIDE the timed region is not an option -- a real caller builds it
// too -- so it is built inside and the cost is counted, which is the honest
// accounting and is what makes a one-request "batch" comparable with the
// scalar row above.
//
// It ignores `first`: a batch window replays the settle's keys.  `hits` is
// as in RunScalar, summed from the found bytes access_batch writes.
template <class Map>
double RunBatched(Map& map, const Config& config, size_t capacity,
                  uint64_t accesses, LatencyHistogram* latency,
                  Backpressure* bp = nullptr,
                  Result::ProbeTally* probes = nullptr,
                  uint64_t* hits = nullptr) {
  const size_t n = config.batch;
  std::vector<uint8_t> keys(n * config.key_bytes, 0);
  std::vector<uint8_t> values(n * config.value_bytes, 0);
  std::vector<uint8_t> out(n * config.value_bytes, 0);
  std::vector<uint8_t> found(n, 0);
  std::vector<oram::BatchRequest> requests(n);
  const uint64_t span = std::max<uint64_t>(1, capacity / 2);
  uint64_t state = config.seed;
  uint64_t found_total = 0;
  const Clock::time_point start = Clock::now();
  Clock::time_point last = start;
  for (uint64_t done = 0; done < accesses; done += n) {
    const size_t m = static_cast<size_t>(
        std::min<uint64_t>(n, accesses - done));
    for (size_t j = 0; j < m; ++j) {
      const uint64_t i = done + j;
      const uint64_t k = SplitMix64(state) % span;
      uint8_t* const key = keys.data() + j * config.key_bytes;
      std::memcpy(key, &k, std::min(sizeof(k), config.key_bytes));
      requests[j].key = key;
      requests[j].insert = false;
      if (config.read_only || (i & 1) == 0) {
        requests[j].op = oram::BatchOp::kRead;
        requests[j].value_in = nullptr;
        requests[j].value_out = out.data() + j * config.value_bytes;
      } else {
        uint8_t* const value = values.data() + j * config.value_bytes;
        std::memcpy(value, &i, std::min(sizeof(i), config.value_bytes));
        requests[j].op = oram::BatchOp::kReadThenWrite;
        requests[j].value_in = value;
        requests[j].value_out = nullptr;
      }
    }
    const uint64_t bp_nanos = bp ? map.engine().requester_backpressure().nanos.get() : 0;
    const uint64_t bp_episodes = bp ? map.engine().requester_backpressure().episodes.get() : 0;
    const uint64_t mains = map.probe_mains();
    map.access_batch(m, requests.data(), found.data());
    for (size_t j = 0; j < m; ++j) found_total += found[j];
    if (probes != nullptr) {
      probes->Record(m, map.last_probe_tables(), map.last_probe_buckets(),
                     map.probe_mains() - mains, map.last_probe_mains());
    }
    if (bp != nullptr) {
      bp->Record(m,
                 map.engine().requester_backpressure().nanos.get() - bp_nanos,
                 map.engine().requester_backpressure().episodes.get() - bp_episodes);
    }
    if (latency != nullptr) {
      const Clock::time_point now = Clock::now();
      latency->Record(static_cast<uint64_t>(
          std::chrono::duration_cast<std::chrono::nanoseconds>(now - last)
              .count()));
      last = now;
    }
  }
  const double seconds = SecondsSince(start);
  if (hits != nullptr) *hits = found_total;
  return seconds;
}

template <class Map>
double Run(Map& map, const Config& config, size_t capacity,
           uint64_t accesses, LatencyHistogram* latency, uint64_t first = 0,
           Backpressure* bp = nullptr, Result::ProbeTally* probes = nullptr,
           uint64_t* hits = nullptr) {
  return config.batch == 0
             ? RunScalar(map, config, capacity, accesses, latency, first, bp,
                         probes, hits)
             : RunBatched(map, config, capacity, accesses, latency, bp, probes,
                          hits);
}

// THE RESULT CHECK: Warm inserts every key a request can draw (0 .. capacity/2
// - 1), so every probing request must find its key.  A run whose lookups
// missed is refused rather than reported as a rate.  Only presence is
// checked; returned values are not compared.  Write-only requests are blind
// writes and return nothing to check.
void RequireHits(const Config& config, size_t capacity, uint64_t accesses,
                 uint64_t hits, const char* phase) {
  if (config.write_only || capacity / 2 == 0 || hits == accesses) return;
  throw std::runtime_error(std::string("the ") + phase + "'s lookups missed " +
                           std::to_string(accesses - hits) + " of " +
                           std::to_string(accesses) + " warmed keys");
}

// The measured window's share of a lifetime counter set: everything is a
// running total except the per-digit worst, which stays the lifetime maximum
// (see the file header).
la::LevelStats Since(const la::LevelStats& after, const la::LevelStats& before) {
  la::LevelStats d = after;
  d.steps -= before.steps;
  d.merges -= before.merges;
  d.adoptions -= before.adoptions;
  d.preparations -= before.preparations;
  d.publications -= before.publications;
  d.forwards -= before.forwards;
  d.inbox_partials -= before.inbox_partials;
  for (size_t i = 0; i < la::kLevelBlockCount; ++i) {
    d.blocked[i] -= before.blocked[i];
  }
  d.prepare_nanos -= before.prepare_nanos;
  d.merge_nanos -= before.merge_nanos;
  d.publish_nanos -= before.publish_nanos;
  d.prepared_merges -= before.prepared_merges;
  for (unsigned j = 0; j <= la::kMaxLevelDigit; ++j) {
    d.job_count[j] -= before.job_count[j];
    d.job_nanos[j] -= before.job_nanos[j];
  }
  return d;
}

// The waits every thread did, as running totals, so that the window's can be
// taken as a difference.
struct WaitTotals {
  uint64_t preemptions = 0;
  uint64_t declined = 0;
  uint64_t credit_stops = 0;
  uint64_t parks = 0;
  uint64_t park_nanos = 0;
  // The request thread's own backpressure waits (a full dense ring), apart
  // from the owners': how often it waited for level 1, and for how long.
  uint64_t requester_waits = 0;
  uint64_t requester_park_nanos = 0;
  std::vector<uint64_t> parks_by_reason;
  std::vector<uint64_t> park_nanos_by_reason;
  uint64_t batch_waits = 0;
  uint64_t batch_parks = 0;
};

WaitTotals ReadWaits(const la::LevelArenaEngine& engine, const Config& config) {
  WaitTotals w;
  w.parks = engine.requester_waits().parks.get();
  w.park_nanos = engine.requester_waits().park_nanos.get();
  w.requester_waits = engine.requester_waits().waits();
  w.requester_park_nanos = engine.requester_waits().park_nanos.get();
  w.parks_by_reason.assign(la::kLevelBlockCount, 0);
  w.park_nanos_by_reason.assign(la::kLevelBlockCount, 0);
  if (engine.threaded()) {
    for (size_t g = 0; g < engine.owner_groups(); ++g) {
      const la::LevelGroup& group = engine.group_driver(g);
      w.preemptions += group.preemptions();
      w.declined += group.preemptions_declined();
      w.credit_stops += group.stops_for_credit();
      w.parks += group.waits().parks.get();
      w.park_nanos += group.waits().park_nanos.get();
      for (size_t r = 0; r < la::kLevelBlockCount; ++r) {
        const la::LevelBlock block = static_cast<la::LevelBlock>(r);
        w.parks_by_reason[r] += group.parks_blocked_on(block);
        w.park_nanos_by_reason[r] += group.park_nanos_blocked_on(block);
      }
    }
  }
  if (config.batch != 0) {
    for (unsigned t = 0; t < config.participants; ++t) {
      w.batch_waits += engine.batch_waits(t).waits();
      w.batch_parks += engine.batch_waits(t).parks.get();
    }
  }
  return w;
}

// The geometry the ladder chose: L, r0, D, the fanout of every level below
// the top, and the published tier width.
std::string DescribeGeometry(const la::LevelArenaEngine& engine) {
  const la::LevelArenaGeometry& g = engine.geometry();
  std::string out = "L=" + std::to_string(g.Levels()) +
                    ", r0=" + std::to_string(g.PrefixFlushes()) +
                    ", D=" + std::to_string(g.TopDigit()) + ", fanouts";
  for (unsigned l = 1; l < g.Levels(); ++l) {
    out += (l == 1 ? " " : ",") + std::to_string(g.Fanout(l));
  }
  if (g.HasTierProfile()) {
    out += ", tiers";
    for (unsigned l = 1; l <= g.Levels(); ++l) {
      out += (l == 1 ? " " : ",") + std::to_string(g.TierBucketsOf(l));
    }
  } else {
    out += ", tier " + std::to_string(g.TierBuckets()) + " bucket(s)";
  }
  return out;
}

// What the rebuild was built with: the division, the top's helpers and
// lanes, and the rate its pieces are sized for -- or the inline share.
std::string DescribeRebuild(const la::LevelArenaEngine& engine) {
  char buffer[160];
  if (!engine.threaded()) {
    std::snprintf(buffer, sizeof(buffer),
                  "inline, a share of %llu touches per flush",
                  (unsigned long long)engine.inline_flush_touches());
    return buffer;
  }
  std::string out = "groups";
  for (size_t g = 0; g < engine.owner_groups(); ++g) {
    const la::LevelGroupPlan& group = engine.owner_group(g);
    out += " {" + std::to_string(group.first) +
           (group.last != group.first ? "-" + std::to_string(group.last)
                                      : std::string()) +
           "}";
  }
  std::snprintf(buffer, sizeof(buffer),
                ", %u top helper(s), lanes %zu from %zu buckets, pieces for "
                "%.2f M accesses/s",
                engine.top_helper_threads(), engine.lane_config().lanes,
                engine.lane_config().min_buckets,
                engine.slice_target_rate() / 1e6);
  return out + buffer;
}

// ---------------------------------------------------------------------------
// Fit rows (--fit-rows)
// ---------------------------------------------------------------------------
//
// WHAT THE TUNER FITS.  A level's measured cost is its owner's time inside the
// job's phases (LevelStats::job_nanos, summed over digits) per access; the
// model prices it as touch_lines x line + residual_lines x residual_line +
// offer_lines x offer_line + jobs x job (LevelRebuildFeatures): the routing's
// lines, and the residual passes' and their offers'.
// With top helpers the owner's time is only its share, so the tuner fits the
// line and job terms on rows with one thread per group, and the helper speedup
// from the top's phase wall time (prepare + finish, --stage-times) across
// helper counts.  The run row carries the requester's side: elapsed time per
// access against the probe model's features (SaturatedProbeFeatures), and how
// long it waited on the rebuild, which a probe fit must exclude.  Keys and
// numbers only; no secret-dependent quantity is printed.

std::string JsonNumber(double value) {
  char buffer[64];
  std::snprintf(buffer, sizeof(buffer), "%.17g", value);
  return buffer;
}

std::vector<std::string> FitRows(const la::LevelArenaEngine& engine,
                                 const Config& config, const Result& result) {
  const la::LevelArenaGeometry& geometry = engine.geometry();
  const bs::Layout& layout = engine.layout();
  const unsigned levels = geometry.Levels();
  const la::LevelArenaRebuildCost defaults;
  const bool laned = engine.lane_config().lanes > 1;
  const unsigned helpers = engine.top_helper_threads();
  const std::string common =
      "\"capacity\":" + std::to_string(result.capacity) +
      ",\"key_bytes\":" + std::to_string(config.key_bytes) +
      ",\"value_bytes\":" + std::to_string(config.value_bytes) +
      ",\"branching\":" + std::to_string(geometry.Branching()) +
      ",\"levels\":" + std::to_string(levels) +
      ",\"bucket_bytes\":" + std::to_string(layout.BucketBytes()) +
      ",\"owners\":" + std::to_string(engine.owner_groups()) +
      // owner_groups() is 1 for the inline executor too; the request says which.
      ",\"inline\":" + (config.owner_threads == 0 && config.groups.empty() &&
                         config.rebuild_threads == 0 && !config.synchronous ? "true" : "false") +
      ",\"top_helpers\":" + std::to_string(helpers) +
      ",\"lanes\":" + std::to_string(engine.lane_config().lanes) +
      ",\"write_only\":" + (config.write_only ? "true" : "false") +
      ",\"read_only\":" + (config.read_only ? "true" : "false") +
      ",\"preroute\":" + (config.preroute ? "true" : "false") +
      ",\"batch\":" + std::to_string(config.batch) +
      ",\"offered_kops\":" + JsonNumber(config.rate_kops) +
      ",\"accesses\":" + std::to_string(result.accesses);
  std::vector<std::string> rows;
  const la::ProbeCostFeatures probe = la::SaturatedProbeFeatures(geometry, layout);
  rows.push_back(
      "{\"fit_row\":\"run\"," + common +
      ",\"seconds\":" + JsonNumber(result.seconds) +
      ",\"rebuild_slowdown\":" + JsonNumber(result.rebuild_slowdown) +
      ",\"completed_records_per_s\":" +
      JsonNumber(result.seconds > 0 ? double(result.accesses) / result.seconds : 0.0) +
      ",\"flushes\":" + std::to_string(result.flushes) +
      ",\"flushes_per_s\":" +
      JsonNumber(result.seconds > 0 ? double(result.flushes) / result.seconds : 0.0) +
      ",\"response_count\":" + std::to_string(result.calls.count()) +
      ",\"response_p50_ns\":" + std::to_string(result.calls.Percentile(0.5)) +
      ",\"response_p99_ns\":" + std::to_string(result.calls.Percentile(0.99)) +
      ",\"response_p999_ns\":" + std::to_string(result.calls.Percentile(0.999)) +
      ",\"response_max_ns\":" + std::to_string(result.calls.max()) +
      ",\"backpressure_measured\":" + (result.backpressure.enabled ? "true" : "false") +
      ",\"backpressure_batch_charged_to_each\":" + (config.batch != 0 ? "true" : "false") +
      ",\"backpressure_requests\":" + std::to_string(result.backpressure.requests) +
      ",\"backpressure_delayed\":" + std::to_string(result.backpressure.delayed) +
      ",\"backpressure_episodes\":" + std::to_string(result.backpressure.episodes) +
      ",\"backpressure_total_ns\":" + std::to_string(result.backpressure.nanos) +
      ",\"backpressure_max_ns\":" + std::to_string(result.backpressure.delays.max()) +
      ",\"backpressure_p99_ns\":" + std::to_string(result.backpressure.delays.Percentile(0.99)) +
      ",\"requester_waits\":" + std::to_string(result.requester_waits) +
      ",\"requester_park_nanos\":" + std::to_string(result.requester_park_nanos) +
      ",\"credit_stops\":" + std::to_string(result.credit_stops) +
      ",\"probe_buckets\":" + JsonNumber(probe.buckets) +
      ",\"probe_bucket_lines\":" + JsonNumber(probe.bucket_lines) +
      ",\"last_probe_buckets\":" + std::to_string(result.cascade_buckets) +
      ",\"owner_idle_nanos\":" + std::to_string(result.owner_idle_nanos) +
      ",\"lookups_counted\":" + std::to_string(result.probes.lookups) +
      ",\"lookup_tables_mean\":" +
      JsonNumber(result.probes.lookups ? double(result.probes.tables) /
                                             double(result.probes.lookups)
                                       : 0.0) +
      ",\"lookup_tables_max\":" + std::to_string(result.probes.max_tables) +
      ",\"lookup_buckets_mean\":" +
      JsonNumber(result.probes.lookups ? double(result.probes.buckets) /
                                             double(result.probes.lookups)
                                       : 0.0) +
      ",\"lookup_buckets_max\":" + std::to_string(result.probes.max_buckets) +
      ",\"lookup_mains_mean\":" +
      JsonNumber(result.probes.lookups ? double(result.probes.mains) /
                                             double(result.probes.lookups)
                                       : 0.0) +
      ",\"lookup_mains_max\":" + std::to_string(result.probes.max_mains) +
      ",\"model_rate\":" + JsonNumber(la::SaturatedOnlineRate(geometry, layout)) +
      ",\"slice_target_rate\":" + JsonNumber(engine.slice_target_rate()) + "}");
  // The group each level is driven by: the top's group gets the helpers.
  std::vector<unsigned> group_of(levels + 1, 0);
  for (size_t g = 0; g < engine.owner_groups(); ++g) {
    const la::LevelGroupPlan& group = engine.owner_group(g);
    for (unsigned l = group.first; l <= group.last; ++l) group_of[l] = unsigned(g);
  }
  for (unsigned l = 1; l <= levels; ++l) {
    const la::LevelStats& stats = result.levels.at(l - 1);
    double job_nanos = 0;
    uint64_t jobs = 0;
    for (unsigned d = 0; d <= la::kMaxLevelDigit; ++d) {
      job_nanos += double(stats.job_nanos[d]);
      jobs += stats.job_count[d];
    }
    const la::LevelCostFeatures f =
        la::LevelRebuildFeatures(geometry, layout, engine.sizing(), l);
    const bool in_top_group =
        engine.owner_groups() != 0 && group_of[l] == group_of[levels];
    const bool takes_lanes =
        laned && la::LevelLaneCount(geometry, l, engine.lane_config()) > 1;
    std::string row =
        "{\"fit_row\":\"level\"," + common +
        ",\"level\":" + std::to_string(l) +
        ",\"group\":" + std::to_string(group_of[l]) +
        ",\"in_top_group\":" + (in_top_group ? "true" : "false") +
        ",\"takes_lanes\":" + (takes_lanes ? "true" : "false") +
        ",\"touch_lines_per_access\":" + JsonNumber(f.touch_lines) +
        ",\"residual_lines_per_access\":" + JsonNumber(f.residual_lines) +
        ",\"offer_lines_per_access\":" + JsonNumber(f.offer_lines) +
        ",\"jobs_per_access\":" + JsonNumber(f.jobs) +
        ",\"jobs\":" + std::to_string(jobs) +
        ",\"job_nanos\":" + JsonNumber(job_nanos) +
        ",\"measured_ns_per_access\":" +
        JsonNumber(result.accesses ? job_nanos / double(result.accesses) : 0.0) +
        ",\"model_ns_per_access\":" +
        JsonNumber(la::LevelRebuildNanos(f, defaults));
    if (!result.stage_nanos.empty()) {
      const std::vector<uint64_t>& stage = result.stage_nanos.at(l - 1);
      row += ",\"prepare_wall_nanos\":" + std::to_string(stage[2]) +
             ",\"prepares\":" + std::to_string(stage[3]) +
             ",\"finish_wall_nanos\":" + std::to_string(stage[4]) +
             ",\"finishes\":" + std::to_string(stage[5]) +
             ",\"fold_nanos\":" +
             std::to_string(stage[6 + la::LevelMergeJob::kTimedKinds]) +
             ",\"laned_stages\":" +
             std::to_string(stage[7 + la::LevelMergeJob::kTimedKinds]);
    }
    rows.push_back(row + "}");
  }
  return rows;
}

// ---------------------------------------------------------------------------
// Merge rows (--merge-rows)
// ---------------------------------------------------------------------------
//
// THE DEAMORTIZATION MICROBENCHMARK'S RAW DATA (analysis/preroute_rows.py
// reads it).  One "window" row: the measured window's steady_clock bounds,
// its access rate and each level's carry positions, so a carry interval is
// positions / rate.  One "merge" row per record of the engine's per-merge log
// (the last --merge-rows=N jobs of every level, top included and marked),
// each marked in or out of the window by its publication.  A merge's work is
// the job's piece time over every thread that ran a piece, by phase --
// prepare (routing the older partial), install (the carry), finish -- and
// class -- route, sweep (the fixed merge's offers), residual, fold -- plus
// the publication transaction; each piece's estimated bucket touches
// (PieceTouches) beside it, so the shares can be stated without timing
// noise.  One "owner" row per owner group: its idle time over the window.
// Public quantities only: stamps, counts and shapes.

uint64_t OwnerIdleNanos(const la::LevelArenaEngine& engine) {
  uint64_t idle = 0;
  if (engine.threaded()) {
    for (size_t g = 0; g < engine.owner_groups(); ++g) {
      idle += engine.group_driver(g).idle_nanos();
    }
  }
  return idle;
}

std::vector<std::string> MergeRows(
    const la::LevelArenaEngine& engine, const Config& config,
    const Result& result,
    const std::vector<std::pair<uint64_t, uint64_t>>& warm_idle,
    const std::vector<uint64_t>& window_idle) {
  const la::LevelArenaGeometry& g = engine.geometry();
  const unsigned levels = g.Levels();
  const std::string common =
      "\"capacity\":" + std::to_string(result.capacity) +
      ",\"key_bytes\":" + std::to_string(config.key_bytes) +
      ",\"value_bytes\":" + std::to_string(config.value_bytes) +
      ",\"branching\":" + std::to_string(g.Branching()) +
      ",\"levels\":" + std::to_string(levels) +
      ",\"inline\":" + (engine.threaded() ? "false" : "true") +
      ",\"owners\":" + std::to_string(engine.threaded() ? engine.owner_groups() : 0) +
      ",\"write_only\":" + (config.write_only ? "true" : "false") +
      ",\"read_only\":" + (config.read_only ? "true" : "false") +
      ",\"preroute\":" + (config.preroute ? "true" : "false") +
      ",\"offered_kops\":" + JsonNumber(config.rate_kops);
  std::vector<std::string> rows;
  std::string fanouts, positions, carry_buckets;
  for (unsigned l = 1; l <= levels; ++l) {
    const char* sep = l == 1 ? "" : ",";
    fanouts += sep + std::to_string(l < levels ? g.Fanout(l) : g.TopDigit());
    positions += sep + std::to_string(la::LevelCarryPositions(g, l));
    carry_buckets += sep + std::to_string(g.CarryBuckets(l));
  }
  rows.push_back(
      "{\"merge_row\":\"window\"," + common +
      ",\"accesses\":" + std::to_string(result.accesses) +
      ",\"seconds\":" + JsonNumber(result.seconds) +
      ",\"window_start_ns\":" + std::to_string(result.window_start_ns) +
      ",\"window_end_ns\":" + std::to_string(result.window_end_ns) +
      ",\"fanouts\":[" + fanouts + "],\"carry_positions\":[" + positions +
      "],\"carry_buckets\":[" + carry_buckets + "]" +
      ",\"log_capacity\":" + std::to_string(config.merge_rows) +
      // Whether the work columns were measured (piece time needs it); the
      // stamps are there either way.
      ",\"stage_times\":" + (config.stage_times ? "true" : "false") +
      ",\"bucket_bytes\":" + std::to_string(engine.layout().BucketBytes()) + "}");
  const auto u = [](uint64_t v) { return std::to_string(v); };
  constexpr unsigned kPrep = 0, kInstall = 1, kFinish = 2;
  for (unsigned l = 1; l <= levels; ++l) {
    const bool top = l == levels;
    for (const la::LevelMergeRecord& r : engine.LevelMergeRecords(l)) {
      const la::LevelMergeCost& c = r.cost;
      // After the carry: the install and the finish, by class.
      uint64_t post[la::LevelMergeCost::kClasses] = {};
      uint64_t post_touches = 0;
      for (unsigned k = 0; k < la::LevelMergeCost::kClasses; ++k) {
        post[k] = c.nanos[kInstall][k] + c.nanos[kFinish][k];
      }
      post_touches = c.PhaseTouches(kInstall) + c.PhaseTouches(kFinish);
      const uint64_t post_active = c.PhaseNanos(kInstall) +
                                   c.PhaseNanos(kFinish) + r.publish_active_ns;
      const bool in_window = r.publish_ns >= result.window_start_ns &&
                             r.publish_ns <= result.window_end_ns;
      const uint64_t cycle =
          top ? r.ordinal : (r.ordinal - 1) / g.Fanout(l);
      rows.push_back(
          "{\"merge_row\":\"merge\"," + common +
          ",\"level\":" + u(l) + ",\"top\":" + (top ? "true" : "false") +
          ",\"ordinal\":" + u(r.ordinal) + ",\"cycle\":" + u(cycle) +
          ",\"digit\":" + u(r.digit) + ",\"k\":" + u(r.digit - 1) +
          ",\"adoption\":" + (r.adoption ? "true" : "false") +
          ",\"output_buckets\":" + u(r.output_buckets) +
          ",\"in_window\":" + (in_window ? "true" : "false") +
          ",\"prepared_ahead\":" + (r.prepared_ahead ? "true" : "false") +
          ",\"prepare_start_ns\":" + u(r.prepare_start_ns) +
          ",\"prepare_end_ns\":" + u(r.prepare_end_ns) +
          ",\"carry_ready_ns\":" + u(r.carry_ready_ns) +
          ",\"carry_accept_ns\":" + u(r.carry_accept_ns) +
          ",\"merge_start_ns\":" + u(r.merge_start_ns) +
          ",\"publish_ns\":" + u(r.publish_ns) +
          ",\"prepare_active_ns\":" + u(c.PhaseNanos(kPrep)) +
          ",\"prepare_route_ns\":" + u(c.nanos[kPrep][la::LevelMergeCost::kRoute]) +
          ",\"prepare_sweep_ns\":" + u(c.nanos[kPrep][la::LevelMergeCost::kSweep]) +
          ",\"prepare_residual_ns\":" + u(c.nanos[kPrep][la::LevelMergeCost::kResidual]) +
          ",\"prepare_fold_ns\":" + u(c.nanos[kPrep][la::LevelMergeCost::kFold]) +
          ",\"post_arrival_active_ns\":" + u(post_active) +
          ",\"install_ns\":" + u(c.PhaseNanos(kInstall)) +
          ",\"post_route_ns\":" + u(post[la::LevelMergeCost::kRoute]) +
          ",\"post_sweep_ns\":" + u(post[la::LevelMergeCost::kSweep]) +
          ",\"post_residual_ns\":" + u(post[la::LevelMergeCost::kResidual]) +
          ",\"post_fold_ns\":" + u(post[la::LevelMergeCost::kFold]) +
          ",\"publish_active_ns\":" + u(r.publish_active_ns) +
          ",\"job_call_ns\":" + u(r.job_call_ns) +
          ",\"prepare_touches\":" + u(c.PhaseTouches(kPrep)) +
          ",\"prepare_route_touches\":" + u(c.touches[kPrep][la::LevelMergeCost::kRoute]) +
          ",\"prepare_sweep_touches\":" + u(c.touches[kPrep][la::LevelMergeCost::kSweep]) +
          ",\"prepare_residual_touches\":" + u(c.touches[kPrep][la::LevelMergeCost::kResidual]) +
          ",\"post_touches\":" + u(post_touches) +
          ",\"install_touches\":" + u(c.PhaseTouches(kInstall)) +
          ",\"post_route_touches\":" +
          u(c.touches[kInstall][la::LevelMergeCost::kRoute] +
            c.touches[kFinish][la::LevelMergeCost::kRoute]) +
          ",\"post_sweep_touches\":" +
          u(c.touches[kInstall][la::LevelMergeCost::kSweep] +
            c.touches[kFinish][la::LevelMergeCost::kSweep]) +
          ",\"post_residual_touches\":" +
          u(c.touches[kInstall][la::LevelMergeCost::kResidual] +
            c.touches[kFinish][la::LevelMergeCost::kResidual]) +
          "}");
    }
  }
  // One row per owner group, over the window (its idle time stops at the
  // window's end; the drain's waits are not counted).
  for (size_t i = 0; i < window_idle.size(); ++i) {
    const la::LevelGroupPlan& plan = engine.owner_group(i);
    const la::LevelGroup& group = engine.group_driver(i);
    const uint64_t idle = window_idle[i] - warm_idle.at(i).first;
    rows.push_back(
        "{\"merge_row\":\"owner\"," + common + ",\"group\":" + u(i) +
        ",\"first_level\":" + u(plan.first) + ",\"last_level\":" + u(plan.last) +
        ",\"idle_ns\":" + u(idle) +
        ",\"idle_share\":" +
        JsonNumber(result.seconds > 0 ? double(idle) / (result.seconds * 1e9) : 0.0) +
        ",\"idle_waits_lifetime\":" + u(group.idle_waits() - warm_idle.at(i).second) +
        "}");
  }
  return rows;
}

// ---------------------------------------------------------------------------
// The engine under test
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Top merge lifecycle
// ---------------------------------------------------------------------------
//
// One TopMergeRecord per top merge (the engine's log, written by whichever
// thread runs the top; read here after drain_rebuilds()).  elapsed is prepare
// start to the replaced table's retirement; carry-to-publication is the carry
// becoming available to the top to the new table being probeable; active is
// the owner's prepare + merge + publish phase timers, which contain no waiting;
// wait is elapsed minus active (carry, reader epoch, helpers, preemption).
// The last merge of a run may have no retirement yet (nothing reads after it
// to advance the epoch): it is marked incomplete and left out of the elapsed
// and wait statistics.

// The stamp order every record must have.  prepare_start and the carry stamps
// are NOT ordered against each other (a speculative preparation may start
// before the carry exists, and a carry may wait for the top's owner).
void CheckTopMergeOrder(const std::vector<la::TopMergeRecord>& records) {
  const auto fail = [](const la::TopMergeRecord& r, const char* what) {
    throw std::runtime_error(
        "top merge " + std::to_string(r.ordinal) + ": stamp order violated: " + what);
  };
  for (size_t i = 0; i < records.size(); ++i) {
    const la::TopMergeRecord& r = records[i];
    if (r.prepare_start_ns == 0 || r.merge_start_ns == 0 || r.publish_ns == 0 ||
        r.carry_ready_ns == 0 || r.carry_accept_ns == 0)
      fail(r, "a stamp was never taken");
    if (r.prepare_start_ns > r.merge_start_ns) fail(r, "prepare start > merge start");
    if (r.carry_ready_ns > r.carry_accept_ns) fail(r, "carry ready > carry accepted");
    if (r.carry_accept_ns > r.merge_start_ns) fail(r, "carry accepted > merge start");
    if (r.merge_start_ns > r.publish_ns) fail(r, "merge start > publication");
    if (r.complete() && r.publish_ns > r.retire_ns) fail(r, "publication > retirement");
    if (i == 0) continue;
    const la::TopMergeRecord& prev = records[i - 1];
    if (r.ordinal != prev.ordinal + 1) fail(r, "ordinals are not consecutive");
    if (r.publish_ns < prev.publish_ns) fail(r, "publication before the previous merge's");
    // The top alternates two banks: this merge's destination is the bank the
    // previous merge replaced, so it cannot be bound before that came back.
    if (prev.complete() && r.prepare_start_ns < prev.retire_ns)
      fail(r, "prepare start before the previous retirement");
  }
}

struct Spread {
  double min = 0, max = 0, mean = 0;
  size_t n = 0;
};
Spread SpreadOf(const std::vector<double>& v) {
  Spread s;
  s.n = v.size();
  if (v.empty()) return s;
  s.min = *std::min_element(v.begin(), v.end());
  s.max = *std::max_element(v.begin(), v.end());
  double sum = 0;
  for (double x : v) sum += x;
  s.mean = sum / double(v.size());
  return s;
}
double Ms(uint64_t ns) { return double(ns) / 1e6; }

// The columns of one merge, in ms.  elapsed and wait are -1 when incomplete.
struct TopMergeCols {
  double elapsed, carry_to_publish, prepare, merge, publish, fold, active, wait;
};
TopMergeCols ColsOf(const la::TopMergeRecord& r) {
  TopMergeCols c;
  c.elapsed = r.complete() ? Ms(r.retire_ns - r.prepare_start_ns) : -1.0;
  c.carry_to_publish = Ms(r.publish_ns - r.carry_ready_ns);
  c.prepare = Ms(r.prepare_active_ns);
  c.merge = Ms(r.merge_active_ns);
  c.publish = Ms(r.publish_active_ns);
  c.fold = Ms(r.fold_ns);
  c.active = Ms(r.active_ns());
  c.wait = r.complete() ? c.elapsed - c.active : -1.0;
  return c;
}

std::vector<std::string> TopMergeRows(const Result& result, const Config& config) {
  std::vector<std::string> rows;
  const std::string common =
      "\"mode\":\"" + result.mode + "\",\"capacity\":" + std::to_string(result.capacity) +
      ",\"value_bytes\":" + std::to_string(config.value_bytes) +
      ",\"accesses\":" + std::to_string(result.accesses);
  const auto num = [](double v) { return JsonNumber(v); };
  std::vector<std::vector<double>> col(8);
  for (const la::TopMergeRecord& r : result.top_merges) {
    const TopMergeCols c = ColsOf(r);
    const double v[8] = {c.elapsed, c.carry_to_publish, c.prepare, c.merge,
                         c.publish, c.fold, c.active, c.wait};
    for (int i = 0; i < 8; ++i) {
      if ((i == 0 || i == 7) && v[i] < 0) continue;
      col[i].push_back(v[i]);
    }
    rows.push_back(
        "{\"top_merge\":\"merge\"," + common +
        ",\"ordinal\":" + std::to_string(r.ordinal) +
        ",\"complete\":" + (r.complete() ? "true" : "false") +
        ",\"prepared_ahead\":" + (r.prepared_ahead ? "true" : "false") +
        ",\"retire_in_place\":" + (r.retire_in_place ? "true" : "false") +
        ",\"prepare_start_ns\":" + std::to_string(r.prepare_start_ns) +
        ",\"carry_ready_ns\":" + std::to_string(r.carry_ready_ns) +
        ",\"carry_accept_ns\":" + std::to_string(r.carry_accept_ns) +
        ",\"merge_start_ns\":" + std::to_string(r.merge_start_ns) +
        ",\"publish_ns\":" + std::to_string(r.publish_ns) +
        ",\"retire_ns\":" + std::to_string(r.retire_ns) +
        ",\"elapsed_ms\":" + (c.elapsed < 0 ? "null" : num(c.elapsed)) +
        ",\"carry_to_publication_ms\":" + num(c.carry_to_publish) +
        ",\"prepare_ms\":" + num(c.prepare) + ",\"merge_ms\":" + num(c.merge) +
        ",\"publish_ms\":" + num(c.publish) + ",\"fold_ms\":" + num(c.fold) +
        ",\"active_ms\":" + num(c.active) +
        ",\"wait_ms\":" + (c.wait < 0 ? "null" : num(c.wait)) + "}");
  }
  static const char* const names[8] = {"elapsed", "carry_to_publication", "prepare",
                                       "merge", "publish", "fold", "active", "wait"};
  std::string summary = "{\"top_merge\":\"summary\"," + common +
                        ",\"merges\":" + std::to_string(result.top_merges.size());
  for (int i = 0; i < 8; ++i) {
    const Spread sp = SpreadOf(col[i]);
    summary += std::string(",\"") + names[i] + "_ms\":{\"n\":" + std::to_string(sp.n) +
               ",\"min\":" + num(sp.min) + ",\"max\":" + num(sp.max) +
               ",\"mean\":" + num(sp.mean) + "}";
  }
  rows.push_back(summary + "}");
  return rows;
}

void PrintTopMerges(const Result& result) {
  if (result.stage_nanos.empty()) return;
  std::printf("  top merges, mode: %s; %zu in the window\n",
              result.mode.c_str(), result.top_merges.size());
  if (result.top_merges.empty()) {
    std::printf("    none completed; run at least two top cycles\n");
    return;
  }
  std::printf("    ordinal |  elapsed | carry->pub |  prepare |    merge |  publish |     fold |   active |     wait | ahead\n");
  std::vector<std::vector<double>> col(8);
  const auto cell = [](double v) {
    char b[24];
    if (v < 0) std::snprintf(b, sizeof(b), "%8s", "n/a");
    else std::snprintf(b, sizeof(b), "%8.3f", v);
    return std::string(b);
  };
  for (const la::TopMergeRecord& r : result.top_merges) {
    const TopMergeCols c = ColsOf(r);
    const double v[8] = {c.elapsed, c.carry_to_publish, c.prepare, c.merge,
                         c.publish, c.fold, c.active, c.wait};
    for (int i = 0; i < 8; ++i) {
      if (v[i] < 0) continue;
      col[i].push_back(v[i]);
    }
    std::printf("    %7llu | %s | %10.3f | %s | %s | %s | %s | %s | %s | %s%s\n",
                (unsigned long long)r.ordinal, cell(c.elapsed).c_str(),
                c.carry_to_publish, cell(c.prepare).c_str(), cell(c.merge).c_str(),
                cell(c.publish).c_str(), cell(c.fold).c_str(), cell(c.active).c_str(),
                cell(c.wait).c_str(), r.prepared_ahead ? "yes" : "no",
                r.complete() ? "" : "  (retirement not observed)");
  }
  static const char* const labels[3] = {"min", "max", "mean"};
  for (int k = 0; k < 3; ++k) {
    std::printf("    %7s | ", labels[k]);
    for (int i = 0; i < 8; ++i) {
      const Spread sp = SpreadOf(col[i]);
      const double x = k == 0 ? sp.min : k == 1 ? sp.max : sp.mean;
      if (i == 1) std::printf("%10.3f | ", x);
      else std::printf("%s | ", cell(sp.n ? x : -1).c_str());
    }
    std::printf("\n");
  }
  std::printf("    (ms; elapsed = prepare start -> retirement of the replaced table%s; "
              "wait = elapsed - active)\n",
              result.mode == "synchronous" ? "; in place, so retirement = publication" : "");
}

// Per level, over the window: the active phase time (waits excluded) and the
// spread of its jobs.
void PrintLevelActive(const Result& result) {
  if (result.stage_nanos.empty() || result.levels.empty()) return;
  std::printf("  per-level active time (waits excluded), mode: %s\n", result.mode.c_str());
  std::printf("    level |   jobs | prepare ms | merge ms | publish ms | fold ms | job mean ms | job max ms (lifetime)\n");
  for (size_t i = 0; i < result.levels.size(); ++i) {
    const la::LevelStats& s = result.levels[i];
    uint64_t jobs = 0, nanos = 0, worst = 0;
    for (unsigned d = 0; d <= la::kMaxLevelDigit; ++d) {
      jobs += s.job_count[d];
      nanos += s.job_nanos[d];
      worst = std::max<uint64_t>(worst, s.job_max_nanos[d]);
    }
    const uint64_t fold = result.stage_nanos[i][6 + la::LevelMergeJob::kTimedKinds];
    std::printf("    %5zu | %6llu | %10.3f | %8.3f | %10.3f | %7.3f | %11.3f | %10.3f\n",
                i + 1, (unsigned long long)jobs, Ms(s.prepare_nanos), Ms(s.merge_nanos),
                Ms(s.publish_nanos), Ms(fold), jobs ? Ms(nanos) / double(jobs) : 0.0,
                Ms(worst));
  }
}

// The level counters and jobs, whichever storage mode the engine runs in.
la::LevelStats LevelStatsOf(const la::LevelArenaEngine& engine, unsigned l) {
  return engine.synchronous() ? engine.synchronous_levels()->stats(l)
                              : engine.level(l).stats();
}
const la::LevelMergeJob& LevelJobOf(const la::LevelArenaEngine& engine,
                                    unsigned l) {
  return engine.synchronous() ? engine.synchronous_levels()->job(l)
                              : engine.level(l).job();
}

// The label every top-merge row carries.
std::string ModeLabel(const la::LevelArenaEngine& engine) {
  if (engine.synchronous()) return "synchronous";
  if (!engine.threaded()) return "incremental inline";
  return "incremental background, " + std::to_string(engine.owner_groups()) +
         " owner" + (engine.owner_groups() == 1 ? "" : "s") + ", " +
         std::to_string(engine.top_helper_threads()) + " top helper(s)";
}

oram::Options MakeOptions(const Config& config) {
  oram::Options options;
  options.deamortized_branching_factor = config.branching;
  options.deamortized_top_digit = config.top_digit;
  options.deamortized_online_stash_entries = config.stash_entries;
  options.deamortized_prefix_flushes = config.prefix_flushes;
  options.deamortized_dense_prefixes = config.dense_prefixes;
  options.deamortized_owner_threads =
      config.groups.empty() ? config.owner_threads
                            : static_cast<unsigned>(config.groups.size());
  options.deamortized_rebuild_threads = config.rebuild_threads;
  options.deamortized_level_groups = config.groups;
  options.deamortized_slice_target_rate = config.slice_rate;
  options.deamortized_slice_touches = config.slice_touches;
  options.deamortized_inline_work_factor = config.inline_share;
  options.deamortized_rebuild_lanes = config.rebuild_lanes;
  options.deamortized_lane_min_buckets = config.lane_min_buckets;
  options.deamortized_top_helpers = config.top_helpers;
  options.deamortized_bottom_helpers = config.bottom_helpers;
  options.deamortized_time_rebuild_stages = config.stage_times;
  options.deamortized_preroute = config.preroute;
  options.deamortized_merge_log_capacity = config.merge_rows;
  options.deamortized_half_fanout_prefix = config.half_fanout_prefix;
  options.deamortized_bank_first = config.bank_first;
  options.deamortized_batch_bucket_scan = config.bucket_scan;
  options.deamortized_batch_profile = config.profile_batch;
  options.deamortized_batch_lanes = config.lanes;
  options.deamortized_batch_participants = config.participants;
  options.deamortized_batch_execution =
      config.parallel_tiles ? oram::BatchExecutionShape::kParallelTiles
                            : oram::BatchExecutionShape::kChunkedCascade;
  options.secret_seed = microram::crypto::SecretKeySeed::Fixed(config.seed);
  return options;
}

// THE PLACEMENT.  The grouping is a function of the geometry and the boundary,
// and both are known before anything is built -- which is why `plan_geometry`
// exists -- so the hooks can be handed to the constructor rather than
// discovered from a half-built engine.
Placement Place(const Config& config, oram::Options& options) {
  Placement report;
  // NOTHING ASKED FOR: the engine's default grouping, unpinned, which is the
  // control.
  if (!config.place && config.near_max_level == 0) return report;
  options.deamortized_near_max_level =
      config.near_max_level == 0 ? oram::kLevelArenaNearMaxLevelAuto
                                 : config.near_max_level;
  const la::LevelArenaCapacityChoice choice = oram::ByteMap<>::plan_geometry(
      config.capacity, config.key_bytes, config.value_bytes, options);
  const unsigned boundary = choice.resolved_near_max_level;
  // From here on the boundary is EXPLICIT, so the constructor's own ladder
  // run prices exactly the division these hooks are indexed by.
  options.deamortized_near_max_level = boundary;
  report.near_max_level = boundary;
  // THE SPLIT WITHOUT THE PLACEMENT, which is the middle arm of the
  // decomposition and the one that says how much of a placement's effect is
  // the PINNING and how much is the different division of the levels.
  // `--near-max-level N` alone asks for exactly that.
  if (!config.place) {
    report.describe = "near boundary level " + std::to_string(boundary) +
                      ", grouping only (nothing pinned)";
    report.placed = true;
    return report;
  }
  const la::HostCacheDomains host = DiscoverDomains();
  // The division and helpers the map will build, from the options it will
  // build with.
  const la::LevelArenaEngine::Options engine_options =
      oram::detail::ArenaEngineOptions(choice, config.key_bytes,
                                       config.value_bytes, options);
  const std::vector<la::LevelGroupPlan> groups =
      la::LevelArenaEngine::PlannedLevelGroups(engine_options);
  const la::NearFarPlacement placement = la::PlanNearFarPlacement(
      host, groups, boundary, config.participants,
      engine_options.lanes.lanes > 1 ? engine_options.top_helpers : 0);
  if (!placement.split) {
    // ONE DOMAIN: nothing to place -- and the boundary goes back to zero with
    // it, so that a `--place` run on a single-domain host is the SAME engine
    // as the run it is compared against rather than the same engine with a
    // different division of its levels.
    options.deamortized_near_max_level = 0;
    report.placed = false;
    report.describe.clear();
    return report;
  }
  options.worker_thread_init = [placement](unsigned group) {
    PinTo(placement.groups.at(group));
  };
  options.deamortized_helper_thread_init = [placement](unsigned helper) {
    PinTo(placement.helpers.at(helper));
  };
  options.deamortized_batch_thread_init = [placement](unsigned participant) {
    PinTo(placement.participants.at(participant));
  };
  // Value workers start in the map's constructor and inherit this thread's
  // affinity: pinned here, they would all share the request thread's CPU.
  if (config.value_workers != 0 && config.value_cpus.empty())
    throw std::invalid_argument(
        "--place pins the request thread, and value workers would share its "
        "CPU: give them --value-cpus");
  PinTo(placement.requester);
  report.placed = true;
  report.describe = placement.Describe();
  return report;
}

#ifdef MICRORAM_BYTESLICE_LEVEL_ARENA_PAUSE
// The throttle.  K lives in a global because the hook is a plain function
// pointer; it is written before the owners start and never again.  Per owner
// thread: the time of its previous poll, and whether it parked since, because
// an interval that held a park is idleness and not service.  Spinning idle
// before a park is counted as service time; it only slows an owner that has
// nothing to do, which a slower server would also be slow to leave.
double g_rebuild_slowdown = 1.0;

void ThrottleHook(la::ArenaPause point, unsigned) {
  thread_local Clock::time_point previous{};
  thread_local bool have_previous = false;
  thread_local bool parked = false;
  if (point == la::ArenaPause::kBeforeGroupPark) { parked = true; return; }
  if (point != la::ArenaPause::kAfterGroupPoll) return;
  const Clock::time_point now = Clock::now();
  if (have_previous && !parked) {
    const double extra =
        (g_rebuild_slowdown - 1.0) *
        std::chrono::duration<double, std::nano>(now - previous).count();
    const Clock::time_point until =
        now + std::chrono::nanoseconds(static_cast<int64_t>(extra));
    while (Clock::now() < until) _mm_pause();
    previous = Clock::now();  // the spin is not service time either
  } else {
    previous = now;
  }
  have_previous = true;
  parked = false;
}

// Clears the hook when the engine (declared before it) is about to go.
struct ThrottleGuard {
  ~ThrottleGuard() { la::SetArenaPauseHook(nullptr); }
};
#endif

template <class Map>
Result RunOnceWith(const Config& config) {
  const RestoreAffinity restore;
  oram::Options options = MakeOptions(config);
  options.deamortized_value_workers = config.value_workers;
  options.deamortized_value_tail = config.value_tail;
  options.deamortized_value_kernel = config.value_kernel;
  options.deamortized_value_spin_nanos = config.value_spin_ns;
  options.deamortized_value_pause = config.value_pause;
  options.deamortized_value_demote = config.value_demote;
  options.deamortized_value_profile = config.value_profile;
  if (!config.value_cpus.empty()) {
    if (config.value_cpus.size() != config.value_workers)
      throw std::invalid_argument("--value-cpus needs one CPU per value worker");
    options.deamortized_value_thread_init = [&config](unsigned t) { PinTo(config.value_cpus.at(t)); };
  }
  Placement placement;
  if (!config.cpus.empty()) {
    if (config.rebuild_threads != 0)
      throw std::invalid_argument("--cpus pins --owners threads; the heuristic's helpers under --rebuild-threads are not placed");
    // The owners MakeOptions asks for (one per --groups entry when a division
    // is given), then the helpers: the top's first, then level 1's.
    const unsigned owners = config.groups.empty()
                                ? config.owner_threads
                                : static_cast<unsigned>(config.groups.size());
    if (config.cpus.size() != size_t{config.participants} + owners +
                                  config.top_helpers + config.bottom_helpers)
      throw std::invalid_argument(
          "--cpus needs one CPU per participant, rebuild owner (one per --groups "
          "entry), top helper and bottom helper");
    for (size_t i = 0; i < config.cpus.size(); ++i) {
#ifdef __linux__
      if (config.cpus[i] < 0 || config.cpus[i] >= CPU_SETSIZE)
#else
      if (config.cpus[i] < 0)
#endif
        throw std::invalid_argument("--cpus CPU outside affinity mask");
      if (std::find(config.cpus.begin(), config.cpus.begin() + i, config.cpus[i]) !=
          config.cpus.begin() + i)
        throw std::invalid_argument("--cpus must use distinct CPUs");
    }
    PinTo(config.cpus[0]);
    options.deamortized_batch_thread_init = [&config](unsigned t) { PinTo(config.cpus.at(t)); };
    options.worker_thread_init = [&config](unsigned t) {
      PinTo(config.cpus.at(config.participants + t));
    };
    options.deamortized_helper_thread_init = [&config, owners](unsigned h) {
      PinTo(config.cpus.at(config.participants + owners + h));
    };
    placement.placed = true;
    placement.describe = config.bottom_helpers == 0
        ? "explicit CPUs (caller, batch helpers, rebuild owners, top helpers):"
        : "explicit CPUs (caller, batch helpers, rebuild owners, top helpers, bottom helpers):";
    for (int cpu : config.cpus) placement.describe += " " + std::to_string(cpu);
  } else {
    placement = Place(config, options);
  }
  if (!config.rebuild_cpus.empty()) {
    const auto choice = Map::plan_geometry(config.capacity,config.key_bytes,config.value_bytes,options);
    const auto resolved = oram::detail::ArenaEngineOptions(choice,config.key_bytes,config.value_bytes,options);
    const unsigned owners = resolved.owner_threads;
    if (config.rebuild_cpus.size() < owners + resolved.top_helpers + resolved.bottom_helpers)
      throw std::invalid_argument("--rebuild-cpus needs at least one CPU per resolved owner and helper");
    options.worker_thread_init = [&config](unsigned t) { PinTo(config.rebuild_cpus.at(t)); };
    options.deamortized_helper_thread_init = [&config,owners](unsigned t) { PinTo(config.rebuild_cpus.at(owners+t)); };
    placement.placed = true;
    placement.describe += " rebuild CPUs:";
    for (int cpu : config.rebuild_cpus) placement.describe += " " + std::to_string(cpu);
  }
#ifdef MICRORAM_BYTESLICE_LEVEL_ARENA_PAUSE
  if (config.rebuild_slowdown > 1.0) {
    g_rebuild_slowdown = config.rebuild_slowdown;
    la::SetArenaPauseHook(&ThrottleHook);
  }
#endif
  Map map(config.capacity, config.key_bytes, config.value_bytes, options);
#ifdef MICRORAM_BYTESLICE_LEVEL_ARENA_PAUSE
  ThrottleGuard throttle_guard;  // destroyed before `map`: hook cleared first
#endif
  Result result;
  result.placement = placement;
  result.capacity = map.capacity();
  Warm(map, config, map.capacity());
  // The settle: the window's own rate, unmeasured, so that the window opens
  // on a running pipeline.  Everything below is snapshotted after it.
  if (config.settle != 0) {
    uint64_t settle_hits = 0;
    (void)Run(map, config, map.capacity(), config.settle, nullptr, 0, nullptr,
              nullptr, &settle_hits);
    RequireHits(config, map.capacity(), config.settle, settle_hits, "settle");
  }
  const la::LevelArenaEngine& engine = map.engine();
  // The window's top merges are those after the last one the warm-up and
  // settle completed.
  uint64_t warm_top_ordinal = 0;
  {
    const std::vector<la::TopMergeRecord> before = engine.TopMergeRecords();
    if (!before.empty()) warm_top_ordinal = before.back().ordinal;
  }
  const auto warm_value_request = engine.ValueRequestProfile();
  std::vector<la::ValueTiming> warm_value_workers;
  for (unsigned i=0;i<engine.ValueWorkers();++i) warm_value_workers.push_back(engine.ValueWorkerProfile(i));
  const auto tsc_start_wall = Clock::now(); const uint64_t tsc_start = la::ValueStamp();
  // The warm-up's own work, subtracted below (every counter is over the
  // measured window only).
  std::vector<la::LevelStats> warm_levels;
  for (unsigned l = 1; l <= engine.geometry().Levels(); ++l) {
    warm_levels.push_back(LevelStatsOf(engine, l));
  }
  const WaitTotals warm_waits = ReadWaits(engine, config);
  std::vector<std::pair<uint64_t, uint64_t>> warm_idle_by_group;
  if (engine.threaded()) {
    for (size_t g = 0; g < engine.owner_groups(); ++g) {
      const la::LevelGroup& group = engine.group_driver(g);
      warm_idle_by_group.emplace_back(group.idle_nanos(), group.idle_waits());
    }
  }
#ifdef MICRORAM_BYTESLICE_COMPARE_COUNT
  uint64_t warm_compares[unsigned(bs::CompareKind::kKinds)];
  for (unsigned k = 0; k < unsigned(bs::CompareKind::kKinds); ++k)
    warm_compares[k] = bs::CompareCount(bs::CompareKind(k));
#endif
  const auto stage_snapshot = [&] {
    std::vector<std::vector<uint64_t>> out;
    for (unsigned l = 1; l <= engine.geometry().Levels(); ++l) {
      const la::LevelMergeJob& job = LevelJobOf(engine, l);
      std::vector<uint64_t> row = {job.ordered_nanos(), job.divisible_nanos()};
      for (la::LevelMergePhase phase :
           {la::LevelMergePhase::kPrepareOlder, la::LevelMergePhase::kFinish}) {
        row.push_back(job.phase_wall_nanos(phase));
        row.push_back(job.phases_ended(phase));
      }
      for (size_t k = 0; k < la::LevelMergeJob::kTimedKinds; ++k) {
        row.push_back(job.kind_nanos(static_cast<bs::Subtask::Kind>(k)));
      }
      row.push_back(job.fold_nanos());
      // A stage divided into lanes ends in one fold, so this counts
      // the folds that fold_nanos sums.
      row.push_back(job.laned_stages());
      out.push_back(row);
    }
    return out;
  };
  const std::vector<std::vector<uint64_t>> warm_stages = stage_snapshot();
  const uint64_t warm_flushes = map.flush_count();
  const uint64_t warm_charged = engine.inline_touches_charged();
  const uint64_t accesses =
      config.accesses != 0 ? config.accesses : map.capacity();
  result.accesses_whole_capacity = accesses % map.capacity() == 0;
  result.latency = config.latency;
  result.batch = config.batch;
  result.offered_kops = config.rate_kops;
  const uint64_t run_tsc = la::ValueStamp();
  result.backpressure.enabled = config.attribution && (config.rate_kops > 0 || config.latency);
  result.rebuild_slowdown = config.rebuild_slowdown;
  const uint64_t warm_idle = OwnerIdleNanos(engine);
  result.window_start_ns = la::TopLogNowNanos();
  uint64_t window_hits = 0;
  result.seconds = Run(map, config, map.capacity(), accesses,
                       config.latency ? &result.calls : nullptr,
                       config.settle,
                       result.backpressure.enabled ? &result.backpressure
                                                   : nullptr,
                       config.probe_counts ? &result.probes : nullptr,
                       &window_hits);
  result.window_end_ns = la::TopLogNowNanos();
  // Before the drain, whose waits are not the window's.
  result.owner_idle_nanos = OwnerIdleNanos(engine) - warm_idle;
  std::vector<uint64_t> window_idle;
  if (config.merge_rows != 0 && engine.threaded()) {
    for (size_t g = 0; g < engine.owner_groups(); ++g) {
      window_idle.push_back(engine.group_driver(g).idle_nanos());
    }
  }
  const uint64_t elapsed_tsc = la::ValueStamp() - run_tsc;
  RequireHits(config, map.capacity(), accesses, window_hits, "window");
  std::printf("value benchmark: W=%u k=%u kernel=%u ns/access=%.3f TSC/access=%.3f\n",
      engine.ValueWorkers(),config.value_tail,unsigned(config.value_kernel),
      result.seconds * 1e9 / accesses,double(elapsed_tsc)/accesses);
  {
    // The tiers' live entries after the window: what a skipped-tier run
    // could have answered wrongly (it is an incomplete lookup either way).
    // The plan's tables, tiers and groups are public; the live entry count is
    // a residual occupancy, which depends on the secret keys (here synthetic
    // ones), and is printed as a diagnostic only, never as a result.
    const bs::ProbePlanSnapshot shape = map.engine().PlanSnapshot();
    size_t tiers = 0, tier_entries = 0, groups = 0;
    for (size_t i = 0; i < shape.tables.size(); ++i) {
      if (shape.tables[i].tier != 1) continue;
      ++tiers;
      tier_entries += shape.occupancy[i];
      groups += i > 0 && shape.tables[i - 1].kind == bs::TableKind::kHashed;
    }
    std::printf("tier cascade: plan %zu tables, %zu tiers (%zu main/tier groups), "
                "%zu live tier entries at the window's end (diagnostic: depends on "
                "the secret keys)\n",
                shape.tables.size(), tiers, groups, tier_entries);
  }
  map.drain_rebuilds();  // a barrier, so the counters below are of a settled
                         // hierarchy and not of one mid-merge
  result.accesses = accesses;
#ifdef MICRORAM_BYTESLICE_COMPARE_COUNT
  {
    // The window's merge comparisons by kind (the same window as the
    // level stats' job_nanos), to be priced by the dedup kernel benchmark.
    static const char* const kNames[] = {
        "pair_q8", "pair_d4", "self_q8", "self_d4", "pair_wide", "self_wide"};
    static_assert(sizeof(kNames) / sizeof(kNames[0]) ==
                  unsigned(bs::CompareKind::kKinds));
    result.compare_row = "{\"compare_count\":\"run\",\"capacity\":" + std::to_string(map.capacity()) +
        ",\"key_bytes\":" + std::to_string(config.key_bytes) +
        ",\"value_bytes\":" + std::to_string(config.value_bytes) +
        ",\"accesses\":" + std::to_string(accesses) +
        ",\"vp2intersect\":" + (MICRORAM_BYTESLICE_USE_VP2INTERSECT ? "true" : "false");
    for (unsigned k = 0; k < unsigned(bs::CompareKind::kKinds); ++k)
      result.compare_row += std::string(",\"") + kNames[k] + "\":" +
          std::to_string(bs::CompareCount(bs::CompareKind(k)) - warm_compares[k]);
    result.compare_row += "}";
  }
#endif
  result.cascade_tables = map.last_probe_tables();
  result.cascade_buckets = map.last_probe_buckets();
  result.inline_flush_touches = engine.inline_flush_touches();
  result.inline_touches_charged =
      engine.inline_touches_charged() - warm_charged;
  for (unsigned l = 1; l <= engine.geometry().Levels(); ++l) {
    const double flushes = double(engine.geometry().PrefixFlushes());
    result.routing_flush_touches +=
        la::LevelArenaPrefixTouches(engine.geometry(), engine.layout(), l) /
        flushes;
    result.residual_flush_touches +=
        la::LevelArenaResidualPrefixTouches(engine.geometry(), engine.layout(),
                                            engine.sizing(), l) /
        flushes;
  }
  result.bill = map.byte_bill();
  result.requested_bytes = result.bill.requested();
  result.reserved_bytes = result.bill.reserved();
  // The arenas ALONE, which is the quantity the closed-form storage model is
  // stated over and is NOT what `arena_bytes()` reports.
  result.main_arena_bytes = map.main_arena_bytes();
  result.flushes = map.flush_count() - warm_flushes;

  if (config.profile_batch) {
    std::printf("  batch stage clocks (diagnostic overhead; joined-phase includes work and waiting)\n");
    std::printf("    participant stage             calls    total ms    mean us     max us\n");
    for (unsigned t = 0; t < config.participants; ++t) {
      const auto& profile = engine.batch_profile(t);
      for (size_t stage = 0; stage < la::kBatchStages; ++stage) {
        const auto& stats = profile.stages[stage];
        if (!stats.calls) continue;
        std::printf("    %11u %-13s %9llu %11.3f %10.3f %10.3f\n", t,
                    la::BatchStageName(stage), (unsigned long long)stats.calls,
                    stats.nanos / 1e6, stats.nanos / (1e3 * stats.calls),
                    stats.max_nanos / 1e3);
      }
    }
  }
  for (unsigned l = 1; l <= engine.geometry().Levels(); ++l) {
    result.levels.push_back(Since(LevelStatsOf(engine, l), warm_levels[l - 1]));
  }
  const WaitTotals waits = ReadWaits(engine, config);
  result.preemptions = waits.preemptions - warm_waits.preemptions;
  result.declined = waits.declined - warm_waits.declined;
  result.credit_stops = waits.credit_stops - warm_waits.credit_stops;
  result.long_waits = engine.long_waits();
  result.helper_lanes = engine.helper_lanes() + engine.bottom_helper_lanes();
  result.rebuild = DescribeRebuild(engine);
  result.geometry = DescribeGeometry(engine);
  result.mode = ModeLabel(engine);
  for (const la::TopMergeRecord& r : engine.TopMergeRecords()) {
    if (r.ordinal > warm_top_ordinal) result.top_merges.push_back(r);
  }
  CheckTopMergeOrder(result.top_merges);
  if (config.stage_times) {
    result.stage_nanos = stage_snapshot();
    for (size_t l = 0; l < result.stage_nanos.size(); ++l) {
      for (size_t i = 0; i < result.stage_nanos[l].size(); ++i) {
        result.stage_nanos[l][i] -= warm_stages[l][i];
      }
    }
  }
  result.batch_waits = waits.batch_waits - warm_waits.batch_waits;
  result.batch_parks = waits.batch_parks - warm_waits.batch_parks;
  result.parks = waits.parks - warm_waits.parks;
  result.park_nanos = waits.park_nanos - warm_waits.park_nanos;
  result.requester_waits = waits.requester_waits - warm_waits.requester_waits;
  result.requester_park_nanos =
      waits.requester_park_nanos - warm_waits.requester_park_nanos;
  result.parks_by_reason.assign(la::kLevelBlockCount, 0);
  result.park_nanos_by_reason.assign(la::kLevelBlockCount, 0);
  for (size_t r = 0; r < la::kLevelBlockCount; ++r) {
    result.parks_by_reason[r] =
        waits.parks_by_reason[r] - warm_waits.parks_by_reason[r];
    result.park_nanos_by_reason[r] =
        waits.park_nanos_by_reason[r] - warm_waits.park_nanos_by_reason[r];
  }
  if (config.fit_rows) result.fit_rows = FitRows(engine, config, result);
  if (config.value_profile && engine.ValueWorkers()) {
    const double ticks_ns = double(la::ValueStamp()-tsc_start) /
        std::chrono::duration<double,std::nano>(Clock::now()-tsc_start_wall).count();
    const auto& r = engine.ValueRequestProfile();
    const auto delta = [](uint64_t a,uint64_t b) { return a-b; };
    const double samples = double(delta(r.samples,warm_value_request.samples));
    std::printf("value profile: W=%u k=%u kernel=%u ticks/ns=%.6f samples=%.0f tail=%.1fns wait=%.1fns inserts=%llu insert=%.1fns drains=%llu drain=%.1fns\n",
        engine.ValueWorkers(),config.value_tail,unsigned(config.value_kernel),ticks_ns,samples,
        delta(r.tail,warm_value_request.tail)/(samples*ticks_ns), delta(r.wait,warm_value_request.wait)/(samples*ticks_ns),
        (unsigned long long)delta(r.inserts,warm_value_request.inserts),
        delta(r.insert_ticks,warm_value_request.insert_ticks)/(double(delta(r.inserts,warm_value_request.inserts))*ticks_ns),
        (unsigned long long)delta(r.drains,warm_value_request.drains),
        delta(r.drain_ticks,warm_value_request.drain_ticks)/(double(delta(r.drains,warm_value_request.drains))*ticks_ns));
    for (unsigned i=0;i<engine.ValueWorkers();++i) {
      const auto w=engine.ValueWorkerProfile(i), a=warm_value_workers[i];
      std::printf("value worker %u: samples=%llu start=%.1fns address=%.1fns final=%.1fns pending=%.1fns\n",i,
          (unsigned long long)delta(w.samples,a.samples), double(int64_t(delta(w.stamp,a.stamp)-delta(r.publish,warm_value_request.publish)))/(samples*ticks_ns),
          delta(w.address,a.address)/(samples*ticks_ns),
          double(int64_t(delta(w.final_stamp,a.final_stamp)-delta(r.boundary,warm_value_request.boundary)))/(samples*ticks_ns),
          delta(w.insertion,a.insertion)/(samples*ticks_ns));
    }
  }
  if (config.stage_times) result.top_rows = TopMergeRows(result, config);
  if (config.merge_rows != 0) {
    result.merge_rows = MergeRows(engine, config, result, warm_idle_by_group,
                                  window_idle);
  }
  return result;
}

Result RunOnce(const Config& config) {
  return config.synchronous ? RunOnceWith<oram::ByteMap<false>>(config)
                            : RunOnceWith<oram::ByteMap<>>(config);
}

// ---------------------------------------------------------------------------
// Reporting
// ---------------------------------------------------------------------------

double Median(std::vector<double> values) {
  if (values.empty()) return 0.0;
  std::sort(values.begin(), values.end());
  const size_t n = values.size();
  return n % 2 == 1 ? values[n / 2]
                    : 0.5 * (values[n / 2 - 1] + values[n / 2]);
}

void PrintBill(const Result& result) {
  const la::LevelArenaByteBill& bill = result.bill;
  std::printf("  buffer bill (excludes objects/runtime), requested %.2f MiB / reserved %.2f MiB in "
              "%zu allocations; arenas alone %.2f MiB\n",
              bill.requested() / 1048576.0, bill.reserved() / 1048576.0,
              bill.allocated().allocations,
              result.main_arena_bytes / 1048576.0);
  for (size_t i = 0; i < la::kByteRoleCount; ++i) {
    const la::ByteRole role = static_cast<la::ByteRole>(i);
    if (bill.At(role) == 0) continue;
    std::printf("    %-20s %10.3f MiB  %5.2f %%\n", la::ByteRoleName(role),
                bill.At(role) / 1048576.0,
                100.0 * bill.At(role) / bill.requested());
  }
}

// One row per level: how many jobs of each digit ran in the window, their
// mean, and the lifetime worst (see the file header).  In ms, because the
// questions it answers -- which digit's job a deadline window must absorb,
// how long a phase blocks a group -- are asked in ms.
void PrintJobCosts(const Result& result) {
  if (result.levels.empty()) return;
  std::printf("  per-(level, digit) job cost: count / mean ms / worst ms "
              "(worst is a lifetime max)\n");
  for (size_t i = 0; i < result.levels.size(); ++i) {
    const la::LevelStats& s = result.levels[i];
    std::string row;
    double total = 0.0;
    for (unsigned d = 0; d <= la::kMaxLevelDigit; ++d) {
      if (s.job_count[d] == 0) continue;
      char cell[96];
      std::snprintf(cell, sizeof(cell), "  d%u %llu/%.3f/%.3f", d,
                    (unsigned long long)s.job_count[d],
                    s.job_nanos[d] / 1e6 / double(s.job_count[d]),
                    s.job_max_nanos[d] / 1e6);
      row += cell;
      total += double(s.job_nanos[d]);
    }
    if (row.empty()) continue;
    std::printf("    L%-2zu %7.1f ns/access%s\n", i + 1,
                result.accesses != 0 ? total / double(result.accesses) : 0.0,
                row.c_str());
  }
}

// Where each level's rebuild time went, by stage class and by kernel kind,
// over the window and summed over every thread that ran a piece.  The ORDERED
// share is what lanes cannot divide.
void PrintStageTimes(const Result& result) {
  if (result.stage_nanos.empty()) return;
  std::printf("  rebuild piece time by stage class (all threads): ordered / "
              "divisible ms, ordered share, heaviest kinds\n");
  for (size_t l = 0; l < result.stage_nanos.size(); ++l) {
    const std::vector<uint64_t>& row = result.stage_nanos[l];
    const double total = double(row[0] + row[1]);
    if (total == 0) continue;
    std::vector<std::pair<uint64_t, size_t>> kinds;
    for (size_t k = 0; k < la::LevelMergeJob::kTimedKinds; ++k) {
      kinds.push_back({row[6 + k], k});
    }
    std::sort(kinds.rbegin(), kinds.rend());
    std::string heavy;
    for (size_t i = 0; i < 4 && kinds[i].first != 0; ++i) {
      char cell[96];
      std::snprintf(cell, sizeof(cell), " %s %.1f%%",
                    bs::SubtaskKindName(static_cast<bs::Subtask::Kind>(
                        kinds[i].second)),
                    100.0 * double(kinds[i].first) / total);
      heavy += cell;
    }
    const uint64_t fold = row[6 + la::LevelMergeJob::kTimedKinds];
    std::printf("    L%-2zu %10.2f / %10.2f ms  %5.2f%% ordered (%.2f%% "
                "lane folds) ;%s\n",
                l + 1, row[0] / 1e6, row[1] / 1e6,
                100.0 * double(row[0]) / total, 100.0 * double(fold) / total,
                heavy.c_str());
    std::printf("         phase wall: prepare %.3f ms x %llu, finish %.3f ms "
                "x %llu\n",
                row[3] ? row[2] / 1e6 / double(row[3]) : 0.0,
                (unsigned long long)row[3],
                row[5] ? row[4] / 1e6 / double(row[5]) : 0.0,
                (unsigned long long)row[5]);
  }
}

void PrintLatency(const Result& result) {
  if (!result.latency) return;
  const LatencyHistogram& h = result.calls;
  if (result.offered_kops > 0) {
    std::printf("  offered %.1f kops/s, completed %.1f kops/s\n",
                result.offered_kops, result.kops());
  }
  std::printf("  requester %s per %s (%llu calls): p50 %.2f us, p99 "
              "%.2f us, p99.9 %.2f us, p99.99 %.2f us, max %.3f ms\n",
              result.offered_kops > 0 ? "response time from arrival"
                                      : "wall time",
              result.batch == 0 ? "access" : "batch call",
              (unsigned long long)h.count(), h.Percentile(0.5) / 1e3,
              h.Percentile(0.99) / 1e3, h.Percentile(0.999) / 1e3,
              h.Percentile(0.9999) / 1e3, h.max() / 1e6);
  for (size_t t = 0; t < LatencyHistogram::kStallThresholds; ++t) {
    std::printf("    stalls over %5.0f ms: %8llu calls, %9.2f ms in total\n",
                LatencyHistogram::kStallNanos[t] / 1e6,
                (unsigned long long)h.stalls(t), h.stall_nanos(t) / 1e6);
  }
}

void PrintBackpressure(const Result& result) {
  const Backpressure& b = result.backpressure;
  if (!b.enabled) return;
  std::printf("  rebuild backpressure, request-correlated%s: %llu of %llu "
              "requests delayed (%.4f %%), %llu episodes; attributed stall "
              "max %.3f us, p99 %.3f us (over delayed requests), total %.3f us\n",
              result.batch != 0 ? " (each request charged its whole batch "
                                  "call's delay)" : "",
              (unsigned long long)b.delayed, (unsigned long long)b.requests,
              b.delayed_percent(), (unsigned long long)b.episodes,
              b.delays.max() / 1e3, b.delays.Percentile(0.99) / 1e3,
              b.nanos / 1e3);
  if (result.rebuild_slowdown > 1.0) {
    std::printf("  rebuild throttle: owners at 1/%.3f speed; completed %.0f "
                "records/s, %.0f flushes/s (a rebuild rate only when "
                "saturated: run --write-only without --rate)\n",
                result.rebuild_slowdown,
                result.seconds > 0 ? double(result.accesses) / result.seconds : 0.0,
                result.seconds > 0 ? double(result.flushes) / result.seconds : 0.0);
  }
}

void PrintLevels(const Result& result) {
  if (result.levels.empty()) return;
  std::printf("  per-level phase time and preparation\n");
  // `in-inbox` counts even partials published into the level above's inbox,
  // under the lease the level holds from its first lease digit to digit b_l.
  std::printf("    %-6s %9s %9s %9s %9s %9s %9s %9s\n", "level", "merges",
              "prep(ms)", "merge(ms)", "pub(ms)", "prepared", "adoptions",
              "in-inbox");
  for (size_t i = 0; i < result.levels.size(); ++i) {
    const la::LevelStats& s = result.levels[i];
    std::printf("    %-6zu %9llu %9.2f %9.2f %9.2f %8.1f%% %9llu %9llu\n",
                i + 1, (unsigned long long)s.merges, s.prepare_nanos / 1e6,
                s.merge_nanos / 1e6, s.publish_nanos / 1e6,
                s.merges != 0 ? 100.0 * double(s.prepared_merges) /
                                    double(s.merges)
                              : 0.0,
                (unsigned long long)s.adoptions,
                (unsigned long long)s.inbox_partials);
  }
}

// The per-reason rows SUM TO MORE than the park total, by construction and not
// by a counting error: a group parks when no member can proceed, so one park is
// charged to every blocked member's reason at once (see
// LevelGroup::parks_blocked_on).  Read a reason's share against the others, not
// against the total.
void PrintWaits(const Result& result) {
  std::printf("  waits: %llu parks, %.2f ms parked in total; %llu phases "
              "stopped between pieces (%llu tests stopped for a credit), "
              "%llu not stopped for; %llu lanes run by helpers (lifetime)\n",
              (unsigned long long)result.parks, result.park_nanos / 1e6,
              (unsigned long long)result.preemptions,
              (unsigned long long)result.credit_stops,
              (unsigned long long)result.declined,
              (unsigned long long)result.helper_lanes);
  std::printf("    of which the requester's backpressure (a full dense "
              "ring): %llu waits, %.2f ms parked\n",
              (unsigned long long)result.requester_waits,
              result.requester_park_nanos / 1e6);
  for (size_t r = 0; r < result.parks_by_reason.size(); ++r) {
    if (result.parks_by_reason[r] == 0) continue;
    std::printf("    blocked on %-18s %8llu parks  %9.2f ms\n",
                la::LevelBlockName(static_cast<la::LevelBlock>(r)),
                (unsigned long long)result.parks_by_reason[r],
                result.park_nanos_by_reason[r] / 1e6);
  }
}

void PrintResult(const Result& result) {
  std::printf("level arena: %.1f kops/s  (%llu accesses in %.3f s, capacity "
              "%zu)\n", result.kops(),
              (unsigned long long)result.accesses, result.seconds,
              result.capacity);
  std::printf("  geometry: %s\n", result.geometry.c_str());
  std::printf("  rebuild: %s\n", result.rebuild.c_str());
  if (result.placement.placed) {
    std::printf("  placement: %s\n", result.placement.describe.c_str());
  }
  if (result.batch_waits != 0 || result.batch_parks != 0) {
    std::printf("  batch participants: %llu waits, %llu of them parks\n",
                (unsigned long long)result.batch_waits,
                (unsigned long long)result.batch_parks);
  }
  if (result.cascade_tables != 0) {
    std::printf("  cascade: %zu tables, %zu buckets per access; %llu flushes\n",
                result.cascade_tables, result.cascade_buckets,
                (unsigned long long)result.flushes);
  }
  if (result.inline_flush_touches != 0) {
    std::printf("  inline budget: %llu touches per flush, over an estimate of "
                "%.0f routing + %.0f residual; %.0f charged per flush\n",
                (unsigned long long)result.inline_flush_touches,
                result.routing_flush_touches, result.residual_flush_touches,
                result.flushes != 0 ? double(result.inline_touches_charged) /
                                          double(result.flushes)
                                    : 0.0);
  }
  if (!result.accesses_whole_capacity) {
    std::printf("  WARNING: %llu accesses is not a whole number of capacities "
                "(%zu), so per-level costs are not averages over whole digit "
                "cycles\n", (unsigned long long)result.accesses,
                result.capacity);
  }
  PrintLatency(result);
  PrintBackpressure(result);
  PrintBill(result);
  PrintLevels(result);
  PrintJobCosts(result);
  PrintStageTimes(result);
  PrintTopMerges(result);
  PrintLevelActive(result);
  PrintWaits(result);
  if (!result.long_waits.empty()) {
    std::printf("  requester waits past 10 ms (warm-up included), what every "
                "level was blocked on:\n");
    for (const std::string& line : result.long_waits) {
      std::printf("    %s\n", line.c_str());
    }
  }
}

// ---------------------------------------------------------------------------

// STRICT NUMBERS: the whole argument must be the number, so "2.5e6" or "1e8"
// for an integer flag, trailing text, a sign or a value past the flag's type
// are refused rather than read as some other value.
uint64_t ParseUnsigned(const std::string& flag, const std::string& text,
                       uint64_t max = UINT64_MAX) {
  uint64_t value = 0;
  const auto r = std::from_chars(text.data(), text.data() + text.size(), value);
  if (text.empty() || r.ec != std::errc{} || r.ptr != text.data() + text.size() ||
      value > max) {
    throw std::invalid_argument(flag + " needs an unsigned integer" +
                                (max == UINT64_MAX ? std::string()
                                                   : " of at most " + std::to_string(max)) +
                                ", not '" + text + "'");
  }
  return value;
}
double ParseReal(const std::string& flag, const std::string& text) {
  char* end = nullptr;
  errno = 0;
  const double value = std::strtod(text.c_str(), &end);
  if (text.empty() || end != text.c_str() + text.size() || errno == ERANGE ||
      !std::isfinite(value)) {
    throw std::invalid_argument(flag + " needs a finite real number, not '" + text + "'");
  }
  return value;
}

// "5-6,1-4" -> {5,6},{1,4}; a single level may be written alone ("6").
std::vector<la::LevelGroupPlan> ParseGroups(const std::string& text) {
  std::vector<la::LevelGroupPlan> groups;
  size_t at = 0;
  while (at < text.size()) {
    const size_t end = std::min(text.find(',', at), text.size());
    const std::string item = text.substr(at, end - at);
    const size_t dash = item.find('-');
    la::LevelGroupPlan group;
    group.first = unsigned(ParseUnsigned("--groups", item.substr(0, dash), UINT_MAX));
    group.last = dash == std::string::npos
                     ? group.first
                     : unsigned(ParseUnsigned("--groups", item.substr(dash + 1), UINT_MAX));
    if (group.first > group.last) std::swap(group.first, group.last);
    groups.push_back(group);
    at = end + 1;
  }
  return groups;
}

void Usage() {
  std::printf(
      "usage: cpu_byteslice_level_arena_benchmark [options]\n"
      "  --capacity N        requested entries (default 524288)\n"
      "  --value-workers N  synchronous value workers (default 0)\n"
      "  --value-tail N     requester tail entries (default 2; clamped)\n"
      "  --value-kernel K   auto, accumulate or permute\n"
      "  --value-cpus LIST  one CPU per value worker (required with --cpus,\n"
      "                     and with --place on a multi-domain host)\n"
      "  --rebuild-cpus LIST resolved owners followed by helpers (budget allowed)\n"
      "  --value-profile   hashed per-thread phase sampling\n"
      "  --value-spin-ns N  idle spin window; --value-no-pause, --value-demote\n"
      "  --value N           value bytes (default 16)\n"
      "  --key N             key bytes (default 8)\n"
      "  --branching N       B in {2,4,8} (default 4)\n"
      "  --digit N           D in {1,2,4,8}, at most B; 0 lets the ladder\n"
      "                      choose\n"
      "  --stash N           insertion unit in entries, a multiple of 64\n"
      "                      (default 64)\n"
      "  --flushes N         r0, stash flushes per dense prefix;\n"
      "                      0 lets the ladder choose\n"
      "  --dense-prefixes N  q, complete prefixes outstanding before the\n"
      "                      requester waits (default 2)\n"
      "  --owners N          owner threads; 0 is the inline executor\n"
      "  --rebuild-threads N a thread budget the heuristic divides into\n"
      "                      owner groups, top helpers and lanes; replaces\n"
      "                      --owners\n"
      "  --groups LIST       an explicit division, highest group first,\n"
      "                      e.g. 6-6,1-5 (top level alone at L=6)\n"
      "  --accesses N        measured accesses per repetition; 0, the\n"
      "                      default, is one capacity() of the built map\n"
      "  --latency           record the requester's per-call wall time\n"
      "  --slice-rate R      size the owners' rebuild pieces for R accesses/s;\n"
      "                      0 is the saturated sequential rate\n"
      "  --slice-touches N   fixed piece size in bucket touches instead\n"
      "  --inline-share F    with --owners 0, run at most F times the average\n"
      "                      rebuild work per flush (default %.1f)\n"
      "  --rebuild-lanes N   lanes per level for rebuild stages (1 = none)\n"
      "  --lane-min-buckets N  levels with smaller tables take one lane\n"
      "  --top-helpers N     helper threads for the top's owner group\n"
      "  --write-only        every access an unprobed insert: rebuild capacity\n"
      "  --read-only         every access a find (default: find and\n"
      "                      exchange alternate)\n"
      "  --stage-times       time rebuild pieces by kind and stage class; also\n"
      "                      the per-top-merge lifecycle table and TOP_MERGE_ROW lines\n"
      "  --merge-rows[=N]    MERGE_ROW lines: the last N (4096) jobs of every level\n"
      "                      with their stamps, and each owner's idle time; their\n"
      "                      work by phase needs --stage-times as well\n"
      "                      (analysis/preroute_rows.py)\n"
      "  --no-preroute       start no preparation before its carry is available,\n"
      "                      at any level: only WHEN preparation runs changes\n"
      "  --probe-counts      tally the tables, main tables and buckets each\n"
      "                      probing request's cascade had (FIT_ROW run:\n"
      "                      lookup_tables_mean/max, lookup_mains_mean/max)\n"
      "  --storage MODE      incremental (default; --owners 0 is its inline\n"
      "                      executor) or synchronous (ByteMap<false>: every merge\n"
      "                      on the requester; takes no owners, helpers or lanes)\n"
      "  --bottom-helpers N  helper threads for level 1's owner group (needs\n"
      "                      lanes at level 1 and a group of its own)\n"
      "  --fanout-ladder F   half-prefix (default: fanout B/2 at the lowest 1-3\n"
      "                      levels, B = 8) or bottom (B everywhere but a bottom\n"
      "                      fanout chosen by bytes)\n"
      "  --fit-rows          print FIT_ROW JSON lines for the rebuild cost tuner\n"
      "  --rebuild-slowdown K  (cpu_byteslice_level_arena_benchmark_throttled only)\n"
      "                      run every owner thread at 1/K speed, K >= 1 real\n"
      "  --rate KOPS         offered rate in k accesses/s, scalar only; 0 (the\n"
      "                      default) is the closed loop.  Paced, the latency\n"
      "                      histogram (implied) holds response times from\n"
      "                      each request's arrival\n"
      "  --attribution 0|1   per-request backpressure reads under --rate or\n"
      "                      --latency (default 1); 0 is the harness-gate\n"
      "                      control arm\n"
      "  --settle N          N unmeasured requests at the same rate before\n"
      "                      the window\n"
      "  --bank-first MODE   off or no-clone (default): build each\n"
      "                      cycle's first digits in the idle odd bank\n"
      "  --reps N            repetitions on fresh engines; the reported rate\n"
      "                      is their median\n"
      "  --seed N            fixes the engine's key schedule\n"
      "  --batch N           requests per access_batch call; 0 is the scalar\n"
      "                      surface, which is the control\n"
      "  --lanes N           chunk width per participant, 1..64\n"
      "  --participants N    batch tiles, the calling thread included\n"
      "  --parallel          run the participants as parallel tiles rather\n"
      "                      than one chunked cascade\n"
      "  --profile-batch     report per-participant stage times (adds overhead)\n"
      "  --cpus LIST         comma-separated caller, batch helpers, rebuild\n"
      "                      owners (one per --groups entry), top helpers, then\n"
      "                      bottom helpers\n"
      "  --bucket-scan       opt-in bucket-owned dense prefix scan (implies --parallel)\n"
      "  --place             pin near and far on a multi-CCD host;\n"
      "                      its own control is simply leaving it off\n"
      "  --near-max-level N  the near/far boundary.  With --place it is what\n"
      "                      the pinning is planned against; WITHOUT it, the\n"
      "                      grouping changes and nothing is pinned, which is\n"
      "                      the middle arm of the decomposition\n",
      la::kLevelArenaInlineWorkFactor);
}

}  // namespace

int Main(int argc, char** argv) {
  Config config;
  for (int i = 1; i < argc; ++i) {
    const std::string arg = argv[i];
    const auto value = [&]() -> std::string {
      if (i + 1 >= argc) throw std::invalid_argument(arg + " needs a value");
      return argv[++i];
    };
    // A whole unsigned integer, at most `max` (the flag's type).
    const auto next = [&](uint64_t max = UINT64_MAX) -> uint64_t {
      return ParseUnsigned(arg, value(), max);
    };
    const auto real = [&]() -> double { return ParseReal(arg, value()); };
    if (arg == "--capacity") config.capacity = next();
    else if (arg == "--value-workers") config.value_workers = unsigned(next(UINT_MAX));
    else if (arg == "--value-tail") config.value_tail = unsigned(next(UINT_MAX));
    else if (arg == "--value-spin-ns") config.value_spin_ns = next();
    else if (arg == "--value-no-pause") config.value_pause = false;
    else if (arg == "--value-profile") config.value_profile = true;
    else if (arg == "--value-demote") config.value_demote = true;
    else if (arg == "--value-kernel") {
      if (i + 1 >= argc) throw std::invalid_argument("--value-kernel needs auto, accumulate or permute");
      const std::string k = argv[++i];
      if (k == "auto") config.value_kernel = bs::ValueKernel::kAuto;
      else if (k == "accumulate") config.value_kernel = bs::ValueKernel::kAccumulate;
      else if (k == "permute") config.value_kernel = bs::ValueKernel::kPermute;
      else throw std::invalid_argument("unknown value kernel");
    }
    else if (arg == "--value-cpus" || arg == "--rebuild-cpus") {
      if (i + 1 >= argc) throw std::invalid_argument("--value-cpus needs a list");
      std::string list = argv[++i];
      size_t at = 0;
      while (at < list.size()) {
        const size_t end = list.find(',', at);
        (arg == "--value-cpus" ? config.value_cpus : config.rebuild_cpus).push_back(
            int(ParseUnsigned(arg, list.substr(at, end - at), INT_MAX)));
        if (end == std::string::npos) break;
        at = end + 1;
      }
    }
    else if (arg == "--value") config.value_bytes = size_t(next(SIZE_MAX));
    else if (arg == "--key") config.key_bytes = size_t(next(SIZE_MAX));
    else if (arg == "--branching") config.branching = unsigned(next(UINT_MAX));
    else if (arg == "--digit") config.top_digit = unsigned(next(UINT_MAX));
    else if (arg == "--stash") config.stash_entries = size_t(next(SIZE_MAX));
    else if (arg == "--flushes") config.prefix_flushes = unsigned(next(UINT_MAX));
    else if (arg == "--dense-prefixes") config.dense_prefixes = unsigned(next(UINT_MAX));
    else if (arg == "--owners") config.owner_threads = unsigned(next(UINT_MAX));
    else if (arg == "--accesses") config.accesses = next();
    else if (arg == "--latency") config.latency = true;
    else if (arg == "--attribution") config.attribution = next(1) != 0;
    else if (arg == "--slice-rate") {
      config.slice_rate = real();  // a rate in accesses/s, not an integer
      if (config.slice_rate < 0) throw std::invalid_argument("--slice-rate must not be negative");
    }
    else if (arg == "--slice-touches") config.slice_touches = size_t(next(SIZE_MAX));
    else if (arg == "--rebuild-lanes") config.rebuild_lanes = size_t(next(SIZE_MAX));
    else if (arg == "--rebuild-threads") config.rebuild_threads = unsigned(next(UINT_MAX));
    else if (arg == "--groups") {
      if (i + 1 >= argc) throw std::invalid_argument("--groups needs a list");
      config.groups = ParseGroups(argv[++i]);
    }
    else if (arg == "--lane-min-buckets") config.lane_min_buckets = size_t(next(SIZE_MAX));
    else if (arg == "--top-helpers") config.top_helpers = unsigned(next(UINT_MAX));
    else if (arg == "--bottom-helpers") config.bottom_helpers = unsigned(next(UINT_MAX));
    else if (arg == "--write-only") config.write_only = true;
    else if (arg == "--read-only") config.read_only = true;
    else if (arg == "--stage-times") config.stage_times = true;
    else if (arg == "--no-preroute") config.preroute = false;
    else if (arg == "--merge-rows") config.merge_rows = 4096;
    else if (arg.rfind("--merge-rows=", 0) == 0) {
      config.merge_rows = size_t(ParseUnsigned("--merge-rows", arg.substr(13), SIZE_MAX));
      if (config.merge_rows == 0)
        throw std::invalid_argument("--merge-rows=N needs N > 0");
    }
    else if (arg == "--probe-counts") config.probe_counts = true;
    else if (arg == "--storage") {
      if (i + 1 >= argc) throw std::invalid_argument("--storage needs synchronous or incremental");
      const std::string v = argv[++i];
      if (v == "synchronous") config.synchronous = true;
      else if (v == "incremental") config.synchronous = false;
      else throw std::invalid_argument("--storage is synchronous or incremental");
    }
    else if (arg == "--fanout-ladder") {
      if (i + 1 >= argc) throw std::invalid_argument("--fanout-ladder needs half-prefix or bottom");
      const std::string v = argv[++i];
      if (v == "half-prefix") config.half_fanout_prefix = true;
      else if (v == "bottom") config.half_fanout_prefix = false;
      else throw std::invalid_argument("--fanout-ladder is half-prefix or bottom");
    }
    else if (arg == "--fit-rows") config.fit_rows = true;
    else if (arg == "--rate") {
      if (i + 1 >= argc) throw std::invalid_argument("--rate needs KOPS");
      config.rate_kops = real();
    }
    else if (arg == "--rebuild-slowdown") {
#ifdef MICRORAM_BYTESLICE_LEVEL_ARENA_PAUSE
      if (i + 1 >= argc) throw std::invalid_argument("--rebuild-slowdown needs K");
      config.rebuild_slowdown = real();
      if (!(config.rebuild_slowdown >= 1.0))
        throw std::invalid_argument("--rebuild-slowdown K must be a real >= 1");
#else
      throw std::invalid_argument(
          "--rebuild-slowdown needs the pause points compiled in: use "
          "cpu_byteslice_level_arena_benchmark_throttled");
#endif
    }
    else if (arg == "--settle") config.settle = next();
    else if (arg == "--bank-first") {
      if (i + 1 >= argc) throw std::invalid_argument("--bank-first needs a mode");
      const std::string mode = argv[++i];
      if (mode == "off") config.bank_first = la::BankFirst::kOff;
      else if (mode == "no-clone") config.bank_first = la::BankFirst::kNoClone;
      else throw std::invalid_argument("--bank-first is off or no-clone");
    }
    else if (arg == "--inline-share") {
      if (i + 1 >= argc) throw std::invalid_argument("--inline-share needs F");
      config.inline_share = real();
    }
    else if (arg == "--reps") config.repetitions = unsigned(next(UINT_MAX));
    else if (arg == "--seed") config.seed = next();
    else if (arg == "--batch") config.batch = size_t(next(SIZE_MAX));
    else if (arg == "--lanes") config.lanes = unsigned(next(UINT_MAX));
    else if (arg == "--participants") config.participants = unsigned(next(UINT_MAX));
    else if (arg == "--profile-batch") config.profile_batch = true;
    else if (arg == "--cpus") {
      if (i + 1 >= argc) throw std::invalid_argument("--cpus needs a list");
      std::string cpus = argv[++i];
      size_t start = 0;
      do {
        const size_t end = cpus.find(',', start);
        const std::string token = cpus.substr(start, end - start);
        size_t used = 0;
        const int cpu = std::stoi(token, &used);
        if (used != token.size()) throw std::invalid_argument("invalid CPU list");
        config.cpus.push_back(cpu);
        if (end == std::string::npos) break;
        start = end + 1;
      } while (true);
    }
    else if (arg == "--bucket-scan") { config.bucket_scan = true; config.parallel_tiles = true; }
    else if (arg == "--parallel") config.parallel_tiles = true;
    else if (arg == "--place") config.place = true;
    else if (arg == "--near-max-level") config.near_max_level = unsigned(next(UINT_MAX));
    else if (arg == "--help" || arg == "-h") { Usage(); return 0; }
    else { Usage(); return 2; }
  }
  if (!config.cpus.empty() && config.place)
    throw std::invalid_argument("choose --cpus or --place");
  // --cpus pins the request thread before the map starts its value workers,
  // which inherit that affinity and would all share the caller's CPU.
  if (!config.cpus.empty() && config.value_workers != 0 && config.value_cpus.empty())
    throw std::invalid_argument(
        "--cpus pins the request thread, and value workers would share its "
        "CPU: give them --value-cpus");
  if (config.write_only && config.read_only)
    throw std::invalid_argument("choose --write-only or --read-only");
  if (config.rate_kops < 0)
    throw std::invalid_argument("--rate must not be negative");
  if (config.rate_kops > 0) {
    if (config.batch != 0)
      throw std::invalid_argument("--rate paces the scalar surface only");
    config.latency = true;  // a paced run is a latency measurement
  }
  if (config.repetitions == 0) config.repetitions = 1;
  if (config.merge_rows != 0 && config.synchronous)
    throw std::invalid_argument("--merge-rows needs incremental storage");
  if (!config.preroute && config.synchronous)
    throw std::invalid_argument(
        "--no-preroute: synchronous storage prepares nothing ahead");
  // A call must be one chunk, so that its lanes share the plan the tally
  // reads afterwards.
  if (config.probe_counts && config.batch != 0 &&
      config.batch > config.lanes * (config.parallel_tiles ? config.participants : 1))
    throw std::invalid_argument(
        "--probe-counts: a batch must fit one chunk (--lanes x --participants)");
  if (config.synchronous &&
      (config.owner_threads != 0 || config.rebuild_threads != 0 ||
       !config.groups.empty() || config.top_helpers != 0 ||
       config.bottom_helpers != 0 || config.rebuild_lanes > 1))
    throw std::invalid_argument(
        "--storage synchronous runs every merge on the requester: no "
        "--owners, --rebuild-threads, --groups, helpers or lanes");
  if (config.participants > 1 && !config.parallel_tiles) {
    // The chunked shape runs on the calling thread alone and REFUSES
    // participants rather than allocating idle ones, so say why here instead
    // of letting the engine's constructor say it a repetition in.
    std::fprintf(stderr,
                 "--participants above 1 needs --parallel: the chunked "
                 "cascade runs on the calling thread alone\n");
    return 2;
  }

  const std::string accesses =
      config.accesses == 0 ? std::string("1x capacity")
                           : std::to_string(config.accesses);
  std::printf(
      "level arena: %s storage, capacity %llu, %zu B key / %zu B value, B=%u, D=%u, "
      "unit %zu, owners %u, rebuild threads %u, %s accesses x %u reps, slice "
      "rate %.0f touches %zu, lanes %zu (from %zu buckets), top helpers "
      "%u, bank-first %s, bottom helpers %u%s%s%s%s\n",
      config.synchronous ? "synchronous" : "incremental",
      (unsigned long long)config.capacity, config.key_bytes,
      config.value_bytes, config.branching, config.top_digit,
      config.stash_entries, config.owner_threads, config.rebuild_threads,
      accesses.c_str(), config.repetitions, config.slice_rate,
      config.slice_touches, config.rebuild_lanes, config.lane_min_buckets,
      config.top_helpers, la::BankFirstName(config.bank_first),
      config.bottom_helpers,
      config.write_only ? ", WRITE-ONLY" : "",
      config.read_only ? ", READ-ONLY" : "",
      config.preroute ? "" : ", NO PRE-ROUTING",
      config.rate_kops > 0
          ? (std::string(", rebuild slowdown ") +
             std::to_string(config.rebuild_slowdown) + ", offered " + std::to_string(config.rate_kops) +
             " kops/s " + "fixed" +
             ", settle " + std::to_string(config.settle))
                .c_str()
          : "");
  if (config.batch == 0) {
    std::printf("  access shape: SCALAR (one request per call)\n");
  } else {
    std::printf("  access shape: BATCH of %zu, %u lanes x %u %s%s\n",
                config.batch, config.lanes, config.participants,
                config.bucket_scan ? "bucket scan" : config.parallel_tiles ? "parallel tiles" : "chunked (caller "
                                                           "only)",
                config.place ? ", near/far placement" : "");
  }
#ifdef MICRORAM_BYTESLICE_LEVEL_ARENA_PAUSE
  // The throttled build names its slowdown on every run, closed loop
  // included, so a saved log says which arm it is.
  std::printf("  rebuild slowdown %.3f (throttled build; 1 installs no hook)\n",
              config.rebuild_slowdown);
#endif

  std::vector<double> rates;
  Result last;
  for (unsigned rep = 0; rep < config.repetitions; ++rep) {
    last = RunOnce(config);
    rates.push_back(last.kops());
    for (const std::string& row : last.fit_rows) {
      std::printf("FIT_ROW %s\n", row.c_str());
    }
    for (const std::string& row : last.top_rows) {
      std::printf("TOP_MERGE_ROW %s\n", row.c_str());
    }
    for (const std::string& row : last.merge_rows) {
      std::printf("MERGE_ROW %s\n", row.c_str());
    }
    if (!last.compare_row.empty()) std::printf("COMPARE_COUNT %s\n", last.compare_row.c_str());
    if (config.rate_kops > 0) {
      const LatencyHistogram& h = last.calls;
      const Backpressure& bp = last.backpressure;
      std::printf("  rep %u backpressure: %llu/%llu requests delayed "
                  "(%.4f %%), attributed max %.3f us, total %.3f us\n",
                  rep + 1, (unsigned long long)bp.delayed,
                  (unsigned long long)bp.requests, bp.delayed_percent(),
                  bp.delays.max() / 1e3, bp.nanos / 1e3);
      std::printf("  rep %u: %.1f kops/s offered %.1f; response p99 %.2f us, "
                  "p99.9 %.2f us, p99.99 %.2f us, max %.3f ms; over 1/10/100 "
                  "ms: %llu/%llu/%llu\n",
                  rep + 1, rates.back(), config.rate_kops,
                  h.Percentile(0.99) / 1e3, h.Percentile(0.999) / 1e3,
                  h.Percentile(0.9999) / 1e3, h.max() / 1e6,
                  (unsigned long long)h.stalls(0),
                  (unsigned long long)h.stalls(1),
                  (unsigned long long)h.stalls(2));
    } else {
      std::printf("  rep %u: %.1f kops/s\n", rep + 1, rates.back());
    }
    std::fflush(stdout);
  }

  std::printf("\n");
  PrintResult(last);
  std::printf("\nMEDIAN RATE OVER %u REPETITIONS: %.1f kops/s  "
              "(spread %.1f .. %.1f)\n",
              config.repetitions, Median(rates),
              *std::min_element(rates.begin(), rates.end()),
              *std::max_element(rates.begin(), rates.end()));
  std::printf("The instrument dump above is the LAST repetition's, not the "
              "median's.  This harness has no A/B arm any more (see the file "
              "header); do not read a difference smaller than that spread.\n");
  return 0;
}

// A refused configuration (a bad flag, a placement the host cannot hold) is a
// message and exit status 2, as in cpu_oram_benchmark, not std::terminate and
// a core dump: `fit-rebuild` reports this stderr when a grid row fails.
int main(int argc, char** argv) {
  try {
    return Main(argc, argv);
  } catch (const std::exception& error) {
    std::fprintf(stderr, "cpu_byteslice_level_arena_benchmark: %s\n",
                 error.what());
    return 2;
  }
}
