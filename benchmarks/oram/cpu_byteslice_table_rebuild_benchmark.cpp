// The cost of building ONE hashed table, residual recovery included: our side
// of the rebuild comparison with H2O2RAM, whose `OHashBucket::build`
// (benchmarks/baselines/h2o2ram_routing_bench.cpp) builds one level from the
// records of every level below it.  H2O2RAM's input never repeats a key -- an
// access marks the entry it found as a dummy -- so there are two settings:
//
// --mode init: DUPLICATE-FREE.  The direct initializer
//   (ByteMap<false>::initialize, src/oram/rebuild/cpu_byteslice_initialization.hpp)
//   builds a table of `capacity()` distinct records: scatter, tag, route, and
//   the residual pass.  Each repetition gets a fresh map whose memory is
//   prefaulted outside the timer (MADV_POPULATE_WRITE): a running engine
//   rebuilds into storage it already owns.  The input is a prebuilt array
//   (keys 0..n-1, random values), as in the H2O2RAM driver.
//
// --mode chain: TABLES MAY SHARE KEYS.  A branching-2 synchronous map
//   (ByteMap<false>, every merge on the requester) is initialized full and then
//   written with keys of that same set, so the tables it merges hold copies of
//   one another's keys.  The write that completes a dense prefix runs every
//   merge it carries into before it returns, so its wall time is one cascade:
//   a cascade that reaches level k builds level k's table, of U_k buckets, from
//   the prefix and the tables at levels 1..k-1 -- sources of x, x, 2x, ...,
//   2^(k-2) x entries -- deduplicating them freshest first, exactly H2O2RAM's
//   "rebuild level L from every level below".  Each cascade is timed as that
//   one write (the merges dominate it: an unprobed write is tens of ns).  The
//   per-(level, digit) job samples give the breakdown: a digit-2 job below
//   the top merges two tables of U_l buckets (the level's older table and the
//   carry) into one of 2 U_l, the `merge` setting of the comparators below.
//   Our kernels are data oblivious, so the cost does not depend on how many
//   keys repeat.
//
// Three conventional (not oblivious) comparators build a table of
// `--capacity` entries, K4/V8.  Keys are distinct and random-looking (a
// bijection of the 32-bit words), fresh in every repetition, so none
// deduplicates.  All hash every key inside the timer, with MurmurHash3's
// 32-bit finalizer.
//
// --mode umap-init / umap-merge: std::unordered_map<uint32_t, uint64_t>,
//   default constructed (it grows by rehashing) and filled by try_emplace,
//   one record at a time, from an array (init) or from two maps of half the
//   entries (merge).  Freed memory stays in the process (no trimming, no
//   mmap), so after the first repetition the timed region takes no page
//   faults; the halves' destruction is outside the timer.
// --mode sort-merge / direct-merge: a table of 64-slot buckets at load 1/2
//   (cpu_bucket_table.hpp) rebuilt from half-loaded tables of the same shape,
//   32 records in each bucket, n records in all (two tables of n/2, or one of
//   n: the same bytes).  sort: in place, std::sort and one placement pass;
//   direct: each record hashed straight into its bucket in separate storage.
//
// --cpu LIST runs one identical instance per listed CPU, side by side
// (benchmarks/support/parallel_instances.hpp), to measure a rebuild while
// others compete for memory bandwidth.  The instances start every timed
// region together; chain mode keeps them in lockstep at every prefix flush.
//
// One JSON object per line on stdout; lines starting with '#' are comments.

#include <malloc.h>
#include <sys/mman.h>
#include <sys/resource.h>

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <map>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

#include <cpu_byteslice_oram/oram.hpp>

#include "benchmarks/oram/cpu_byteslice_benchmark_support.hpp"
#include "benchmarks/oram/cpu_bucket_table.hpp"
#include "benchmarks/support/parallel_instances.hpp"

namespace {

namespace oram = cpu_byteslice_oram;
namespace la = microram::byteslice::levelarena;
using benchmark_support::ParallelInstances;
using benchmark_support::BucketTable;
using microram::byteslice::benchmark_support::SplitMix64;
using Clock = std::chrono::steady_clock;
using Map = oram::ByteMap<false>;

struct Config {
  std::string mode;
  uint64_t capacity = uint64_t{1} << 20;
  size_t key_bytes = 4;
  size_t value_bytes = 8;
  unsigned top_digit = 0;  // 0: the ladder's choice
  unsigned reps = 5;       // init and the comparators
  unsigned window = 3;     // chain: measured periods of the deepest cascade
  uint64_t seed = 1;
  std::string cpus;
};

oram::Options MakeOptions(const Config& c) {
  oram::Options options;
  options.deamortized_branching_factor = 2;
  options.deamortized_top_digit = c.top_digit;
  options.secret_seed = microram::crypto::SecretKeySeed::Fixed(c.seed);
  return options;
}

// Every anonymous read-write mapping, made resident and writable without
// changing a byte of it.  Returns the bytes advised.  Under AddressSanitizer
// those mappings include its shadow, terabytes reserved without backing that
// this would commit, so a sanitizer build skips the prefault (and times
// nothing worth it).
size_t PrefaultAnonymousMemory() {
#if defined(__SANITIZE_ADDRESS__)
  return 0;
#else
  std::ifstream maps("/proc/self/maps");
  std::string line;
  size_t bytes = 0;
  while (std::getline(maps, line)) {
    std::istringstream in(line);
    std::string range, perms, offset, dev, inode, path;
    in >> range >> perms >> offset >> dev >> inode >> path;
    if (perms != "rw-p" || (!path.empty() && path != "[heap]")) continue;
    const size_t dash = range.find('-');
    const uintptr_t begin = std::stoull(range.substr(0, dash), nullptr, 16);
    const uintptr_t end = std::stoull(range.substr(dash + 1), nullptr, 16);
    if (::madvise(reinterpret_cast<void*>(begin), end - begin,
                  MADV_POPULATE_WRITE) != 0) {
      throw std::runtime_error("madvise(MADV_POPULATE_WRITE) failed");
    }
    bytes += end - begin;
  }
  return bytes;
#endif
}

// Page faults this process has taken: the prefault's check.
uint64_t MinorFaults() {
  rusage usage;
  getrusage(RUSAGE_SELF, &usage);
  return uint64_t(usage.ru_minflt) + uint64_t(usage.ru_majflt);
}

void WriteWord(uint8_t* out, size_t bytes, uint64_t word) {
  std::memset(out, 0, bytes);
  std::memcpy(out, &word, std::min(sizeof(word), bytes));
}

// A prebuilt input, one record after another.
class ArrayRecords {
 public:
  ArrayRecords(const uint8_t* data, size_t key_bytes, size_t value_bytes)
      : p_(data), key_bytes_(key_bytes), stride_(key_bytes + value_bytes) {}
  oram::InitializationEntry operator*() const {
    return oram::InitializationEntry{p_, p_ + key_bytes_};
  }
  ArrayRecords& operator++() {
    p_ += stride_;
    return *this;
  }

 private:
  const uint8_t* p_;
  size_t key_bytes_;
  size_t stride_;
};

std::string GeometryJson(const Map& map) {
  const la::LevelArenaGeometry& g = map.engine().geometry();
  std::string fanouts, tiers, carries;
  for (unsigned l = 1; l <= g.Levels(); ++l) {
    const char* sep = l == 1 ? "" : ",";
    fanouts += sep + std::to_string(l < g.Levels() ? g.Fanout(l) : g.TopDigit());
    tiers += sep + std::to_string(g.TierBucketsOf(l));
    carries += sep + std::to_string(g.CarryBuckets(l));
  }
  return "\"branching\":2,\"capacity\":" + std::to_string(map.capacity()) +
         ",\"levels\":" + std::to_string(g.Levels()) +
         ",\"top_digit\":" + std::to_string(g.TopDigit()) +
         ",\"top_buckets\":" + std::to_string(g.TopBuckets()) +
         ",\"prefix_flushes\":" + std::to_string(g.PrefixFlushes()) +
         ",\"stash_buckets\":" + std::to_string(g.StashBuckets()) +
         ",\"prefix_entries\":" + std::to_string(g.PrefixPositions()) +
         ",\"fanouts\":[" + fanouts + "],\"carry_buckets\":[" + carries +
         "],\"tier_buckets\":[" + tiers + "]" +
         ",\"entry_bytes\":" + std::to_string(map.engine().layout().EntryBytes()) +
         ",\"requested_bytes\":" + std::to_string(map.byte_bill().requested());
}

struct Summary {
  double median = 0, mean = 0, min = 0, max = 0;
};

Summary Summarize(std::vector<double> ms) {
  Summary s;
  if (ms.empty()) return s;
  std::sort(ms.begin(), ms.end());
  s.median = ms.size() % 2 ? ms[ms.size() / 2]
                           : (ms[ms.size() / 2 - 1] + ms[ms.size() / 2]) / 2;
  for (double v : ms) s.mean += v;
  s.mean /= double(ms.size());
  s.min = ms.front();
  s.max = ms.back();
  return s;
}

std::string Num(double v) {
  char buf[64];
  std::snprintf(buf, sizeof(buf), "%.6g", v);
  return buf;
}

std::string Common(const Config& c, const ParallelInstances& group) {
  return "\"driver\":\"table_rebuild\",\"mode\":\"" + c.mode +
         "\",\"key_bytes\":" + std::to_string(c.key_bytes) +
         ",\"value_bytes\":" + std::to_string(c.value_bytes) +
         ",\"threads\":1,\"instance\":" + std::to_string(group.index()) +
         ",\"instances\":" + std::to_string(group.count()) +
         ",\"cpu\":" + std::to_string(group.cpu());
}

std::string SamplesJson(const std::vector<double>& ms) {
  std::string out;
  for (size_t i = 0; i < ms.size(); ++i) out += (i ? "," : "") + Num(ms[i]);
  return out;
}

// ---- init -----------------------------------------------------------------

int RunInit(const Config& c, ParallelInstances& group) {
  const oram::Options options = MakeOptions(c);
  std::vector<uint8_t> input;
  std::vector<double> ms;
  size_t n = 0, prefaulted = 0, checked = 0;
  uint64_t timed_faults = 0;
  std::string geometry;
  for (unsigned rep = 0; rep < c.reps; ++rep) {
    Map map(c.capacity, c.key_bytes, c.value_bytes, options);
    const size_t stride = c.key_bytes + c.value_bytes;
    if (rep == 0) {
      n = map.capacity();
      geometry = GeometryJson(map);
      input.resize(n * stride);
      uint64_t state = c.seed;
      for (size_t i = 0; i < n; ++i) {
        uint8_t* r = input.data() + i * stride;
        WriteWord(r, c.key_bytes, i);
        for (size_t b = 0; b < c.value_bytes; ++b) r[c.key_bytes + b] = uint8_t(SplitMix64(state));
      }
    }
    prefaulted = PrefaultAnonymousMemory();
    group.Sync();
    const uint64_t faults = MinorFaults();
    const Clock::time_point t0 = Clock::now();
    map.initialize(ArrayRecords(input.data(), c.key_bytes, c.value_bytes), n);
    ms.push_back(std::chrono::duration<double, std::milli>(Clock::now() - t0).count());
    timed_faults += MinorFaults() - faults;
    if (rep != 0) continue;
    // Outside the timer: a spread of keys reads back its value.
    std::vector<uint8_t> out(c.value_bytes);
    const size_t samples = std::min<size_t>(n, 4096);
    for (size_t j = 0; j < samples; ++j) {
      const size_t i = j * (n / samples);
      const uint8_t* r = input.data() + i * stride;
      if (!map.find(r, out.data()) ||
          std::memcmp(out.data(), r + c.key_bytes, c.value_bytes) != 0) {
        std::fprintf(stderr, "init: key %zu did not read back\n", i);
        return 3;
      }
      ++checked;
    }
  }
  const Summary s = Summarize(ms);
  group.InTurn([&] {
    std::printf("{%s,%s,\"table_entries\":%zu,\"reps\":%zu,\"median_ms\":%s,"
                "\"min_ms\":%s,\"max_ms\":%s,\"ns_per_entry\":%s,"
                "\"samples_ms\":[%s],\"prefaulted_bytes\":%zu,"
                "\"page_faults_timed\":%llu,\"checked\":%zu}\n",
                Common(c, group).c_str(), geometry.c_str(), n, ms.size(),
                Num(s.median).c_str(), Num(s.min).c_str(), Num(s.max).c_str(),
                Num(s.median * 1e6 / double(n)).c_str(), SamplesJson(ms).c_str(),
                prefaulted, (unsigned long long)timed_faults, checked);
  });
  return 0;
}

// ---- chain ----------------------------------------------------------------

// Write i's key: a block of 64 keys chosen at random from the map's key set,
// and slot i mod 64 within it, so any 64 consecutive writes are distinct
// keys (all an unprobed write asks) while blocks repeat across tables.
uint64_t ChainKey(uint64_t i, uint64_t blocks, uint64_t seed) {
  uint64_t state = seed ^ (i >> 6);
  return (SplitMix64(state) % blocks) * 64 + (i & 63);
}

int RunChain(const Config& c, ParallelInstances& group) {
  Map map(c.capacity, c.key_bytes, c.value_bytes, MakeOptions(c));
  const la::LevelArenaEngine& engine = map.engine();
  const la::LevelArenaGeometry& g = engine.geometry();
  const la::SynchronousLevels& sync = *engine.synchronous_levels();
  const unsigned levels = g.Levels();
  const uint64_t n = map.capacity();
  if (n % 64 != 0) throw std::logic_error("capacity is not a multiple of 64");
  const size_t prefaulted = PrefaultAnonymousMemory();

  // Full, with distinct keys 0..n-1: every later write repeats one of them.
  double init_ms = 0;
  {
    std::vector<uint8_t> key(c.key_bytes), value(c.value_bytes);
    auto records = microram::byteslice::benchmark_support::MakeGeneratedRecords(
        0, c.key_bytes, c.value_bytes,
        [&](uint64_t k, uint8_t* out) { WriteWord(out, c.key_bytes, k); },
        [&](uint64_t k, uint8_t* out, size_t bytes) { WriteWord(out, bytes, ~k); });
    const Clock::time_point t0 = Clock::now();
    map.initialize(records, n);
    init_ms = std::chrono::duration<double, std::milli>(Clock::now() - t0).count();
  }

  // The deepest cascade below the top ends at level L-1 with digit 1, once
  // every 2^(L-1) prefixes; the top's every 2^(L-1) prefixes too.
  const uint64_t prefix = g.PrefixPositions();
  const uint64_t period = (uint64_t{1} << (levels - 1)) * prefix;
  const uint64_t blocks = n / 64;
  std::vector<uint8_t> key(c.key_bytes), value(c.value_bytes);
  // cascades[k]: wall ms of each write whose cascade ran k jobs (levels 1..k).
  std::vector<std::vector<double>> cascades(levels + 1);
  // jobs[l][d]: ms of each job at level l and digit d, from the level's
  // counters around the write (preparation to publication).
  std::vector<std::vector<std::vector<double>>> jobs(
      levels + 1, std::vector<std::vector<double>>(la::kMaxLevelDigit + 1));
  std::vector<la::LevelStats> before(levels + 1);
  uint64_t i = 0;
  uint64_t first_flush = UINT64_MAX;  // the first write that merged
  const auto run = [&](uint64_t count, bool record) {
    const Clock::time_point start = Clock::now();
    for (const uint64_t end = i + count; i < end; ++i) {
      // Every instance flushes at the same writes: meeting there keeps their
      // merges of each size running at the same time.
      const bool flush = first_flush != UINT64_MAX && (i - first_flush) % prefix == 0;
      if (record && flush) {
        group.Sync();
        for (unsigned l = 1; l <= levels; ++l) before[l] = sync.stats(l);
      }
      WriteWord(key.data(), c.key_bytes, ChainKey(i, blocks, c.seed));
      WriteWord(value.data(), c.value_bytes, i);
      const uint64_t merges = sync.merges();
      const Clock::time_point t0 = Clock::now();
      map.insert_without_probe(key.data(), value.data());
      const Clock::time_point t1 = Clock::now();
      const uint64_t ran = sync.merges() - merges;
      if (ran == 0) continue;
      if (first_flush == UINT64_MAX) first_flush = i;
      if (!flush && i != first_flush) throw std::logic_error("a merge ran between prefix flushes");
      if (!record) continue;
      if (ran > levels) throw std::logic_error("a cascade ran more jobs than levels");
      cascades[ran].push_back(std::chrono::duration<double, std::milli>(t1 - t0).count());
      for (unsigned l = 1; l <= ran; ++l) {
        const la::LevelStats after = sync.stats(l);
        for (unsigned d = 1; d <= la::kMaxLevelDigit; ++d) {
          const uint64_t count = after.job_count[d] - before[l].job_count[d];
          if (count == 0) continue;
          if (count != 1) throw std::logic_error("a level ran two jobs in one cascade");
          jobs[l][d].push_back(double(after.job_nanos[d] - before[l].job_nanos[d]) / 1e6);
        }
      }
    }
    return std::chrono::duration<double>(Clock::now() - start).count();
  };
  // Settle: one whole period, so every level has merged at least once.
  run(period, false);
  group.Sync();
  const uint64_t window = uint64_t{c.window} * period;
  const double seconds = run(window, true);

  // Outside every timer: the window's last 4096 writes read back.
  size_t checked = 0;
  {
    std::map<uint64_t, uint64_t> last;
    for (uint64_t j = i - std::min<uint64_t>(i, 4096); j < i; ++j) {
      last[ChainKey(j, blocks, c.seed)] = j;
    }
    std::vector<uint8_t> out(c.value_bytes), want(c.value_bytes);
    for (const auto& [k, j] : last) {
      WriteWord(key.data(), c.key_bytes, k);
      WriteWord(want.data(), c.value_bytes, j);
      if (!map.find(key.data(), out.data()) || out != want) {
        std::fprintf(stderr, "chain: key %llu did not read back\n", (unsigned long long)k);
        return 3;
      }
      ++checked;
    }
  }

  const std::string common = Common(c, group) + "," + GeometryJson(map);
  group.InTurn([&] {
    std::printf("{%s,\"row\":\"window\",\"init_ms\":%s,\"settle_accesses\":%llu,"
                "\"accesses\":%llu,\"seconds\":%s,\"ns_per_access\":%s,"
                "\"prefaulted_bytes\":%zu,\"checked\":%zu}\n",
                common.c_str(), Num(init_ms).c_str(), (unsigned long long)period,
                (unsigned long long)window, Num(seconds).c_str(),
                Num(seconds * 1e9 / double(window)).c_str(), prefaulted, checked);
    // One row per cascade depth: the table it builds and what it was built from.
    for (unsigned k = 1; k <= levels; ++k) {
      if (cascades[k].empty()) continue;
      const bool top = k == levels;
      const uint64_t entries = 32 * uint64_t(top ? g.TopBuckets() : g.CarryBuckets(k));
      std::string sources = std::to_string(g.PrefixPositions());
      for (unsigned l = 1; l < k; ++l) {
        sources += "," + std::to_string(32 * uint64_t(g.CarryBuckets(l)));
      }
      if (top) sources += "," + std::to_string(entries);  // the top absorbs itself
      const Summary s = Summarize(cascades[k]);
      std::printf("{%s,\"row\":\"cascade\",\"levels_merged\":%u,\"top\":%s,"
                  "\"table_entries\":%llu,\"source_entries\":[%s],\"cascades\":%zu,"
                  "\"median_ms\":%s,\"mean_ms\":%s,\"min_ms\":%s,\"max_ms\":%s,"
                  "\"ns_per_entry\":%s}\n",
                  common.c_str(), k, top ? "true" : "false",
                  (unsigned long long)entries, sources.c_str(), cascades[k].size(),
                  Num(s.median).c_str(), Num(s.mean).c_str(), Num(s.min).c_str(),
                  Num(s.max).c_str(), Num(s.median * 1e6 / double(entries)).c_str());
    }
    // Each level's jobs by digit (the binding before a job is not in these
    // counters).  Below the top, digit 2 merges two tables of U_l buckets.
    for (unsigned l = 1; l <= levels; ++l) {
      for (unsigned d = 1; d <= la::kMaxLevelDigit; ++d) {
        if (jobs[l][d].empty()) continue;
        const bool top = l == levels;
        const uint64_t out = 32 * uint64_t(top ? g.TopBuckets() : d * g.CarryBuckets(l));
        const Summary s = Summarize(jobs[l][d]);
        std::printf("{%s,\"row\":\"job\",\"level\":%u,\"top\":%s,\"digit\":%u,"
                    "\"output_entries\":%llu,\"jobs\":%zu,\"median_ms\":%s,"
                    "\"mean_ms\":%s,\"min_ms\":%s,\"max_ms\":%s,\"ns_per_entry\":%s}\n",
                    common.c_str(), l, top ? "true" : "false", d,
                    (unsigned long long)out, jobs[l][d].size(), Num(s.median).c_str(),
                    Num(s.mean).c_str(), Num(s.min).c_str(), Num(s.max).c_str(),
                    Num(s.median * 1e6 / double(out)).c_str());
      }
    }
  });
  return 0;
}

// ---- conventional comparators -----------------------------------------------

struct Record {
  uint32_t key;
  uint8_t value[8];
};

// Distinct, random-looking keys: a bijection of the 32-bit words.
uint32_t RandomKey(uint64_t i) {
  uint32_t x = uint32_t(i) * 0x9E3779B1u;
  x ^= x >> 15;
  x *= 0x2C1B3C6Du;
  return x ^ (x >> 12);
}

// The records a repetition builds from: key RandomKey(base + i), value word
// i.  A merge's two halves hold records 0..n/2-1 and n/2..n-1.  Each
// repetition takes fresh keys: on one input repeated, the branch predictor
// learns a small sort's branches.
void FillRecords(std::vector<Record>* records, uint64_t base) {
  for (uint64_t i = 0; i < records->size(); ++i) {
    (*records)[i].key = RandomKey(base + i);
    WriteWord((*records)[i].value, sizeof((*records)[i].value), i);
  }
}

uint64_t ComparatorEntries(const Config& c) {
  const uint64_t n = c.capacity;
  if (n < 1024 || (n & (n - 1)) != 0) throw std::invalid_argument("--capacity must be a power of two >= 1024");
  if (c.key_bytes != 4 || c.value_bytes != 8) throw std::invalid_argument("the comparators take --key 4 --value 8");
  if (uint64_t{c.reps + 1} * n > (uint64_t{1} << 32)) throw std::invalid_argument("too many repetitions for fresh keys");
  return n;
}

uint64_t Word(const uint8_t* value) {
  uint64_t word;
  std::memcpy(&word, value, sizeof(word));
  return word;
}

// Reads back, outside the timer, a spread of the first repetition's n keys
// (record i holds value i), then as many absent ones.
template <class Find>
size_t ReadBack(uint64_t n, Find find) {
  const uint64_t samples = std::min<uint64_t>(n, 4096);
  for (uint64_t j = 0; j < samples; ++j) {
    const uint64_t i = j * (n / samples);
    uint64_t value = 0;
    if (!find(RandomKey(i), &value) || value != i) return 0;
  }
  for (uint64_t j = 0; j < samples; ++j) {
    uint64_t value = 0;
    if (find(RandomKey(n + j), &value)) return 0;
  }
  return size_t(2 * samples);
}

// `input_records`: the real records the first repetition's input held.
void PrintComparatorRow(const Config& c, const ParallelInstances& group, uint64_t n,
                        uint64_t input_records, const std::string& shape,
                        const std::vector<double>& ms, uint64_t timed_faults, size_t checked) {
  const Summary s = Summarize(ms);
  std::printf("{%s,%s,\"table_entries\":%llu,\"input_records\":%llu,\"reps\":%zu,\"median_ms\":%s,\"min_ms\":%s,"
              "\"max_ms\":%s,\"ns_per_entry\":%s,\"samples_ms\":[%s],\"page_faults_timed\":%llu,"
              "\"checked\":%zu}\n",
              Common(c, group).c_str(), shape.c_str(), (unsigned long long)n,
              (unsigned long long)input_records, ms.size(),
              Num(s.median).c_str(), Num(s.min).c_str(), Num(s.max).c_str(),
              Num(s.median * 1e6 / double(n)).c_str(), SamplesJson(ms).c_str(),
              (unsigned long long)timed_faults, checked);
}

// The bucket table's hash: std::hash<uint32_t> is the identity, which would
// leave the map no hashing to do.
struct MixHash {
  size_t operator()(uint32_t key) const noexcept { return BucketTable::Tag(key); }
};

int RunUmap(const Config& c, ParallelInstances& group, bool merge) {
  using Umap = std::unordered_map<uint32_t, uint64_t, MixHash>;
  // Freed memory stays mapped and resident for the next repetition.
  mallopt(M_MMAP_MAX, 0);
  mallopt(M_TRIM_THRESHOLD, INT32_MAX);
  const uint64_t n = ComparatorEntries(c);
  std::vector<Record> input(n);
  std::vector<double> ms;
  uint64_t timed_faults = 0;
  size_t checked = 0, buckets = 0;
  uint64_t input_records = 0;
  for (unsigned rep = 0; rep < c.reps; ++rep) {
    FillRecords(&input, rep * n);
    Umap halves[2];
    for (uint64_t i = 0; merge && i < n; ++i) {
      halves[i < n / 2 ? 0 : 1].try_emplace(input[i].key, Word(input[i].value));
    }
    if (rep == 0) input_records = merge ? halves[0].size() + halves[1].size() : input.size();
    group.Sync();
    const uint64_t faults = MinorFaults();
    const Clock::time_point t0 = Clock::now();
    Umap map;
    if (merge) {
      for (const Umap& half : halves) {
        for (const auto& [k, v] : half) map.try_emplace(k, v);
      }
    } else {
      for (const Record& r : input) map.try_emplace(r.key, Word(r.value));
    }
    ms.push_back(std::chrono::duration<double, std::milli>(Clock::now() - t0).count());
    timed_faults += MinorFaults() - faults;
    if (rep != 0) continue;
    buckets = map.bucket_count();
    checked = map.size() == n ? ReadBack(n, [&](uint32_t key, uint64_t* value) {
      const auto it = map.find(key);
      if (it == map.end()) return false;
      *value = it->second;
      return true;
    }) : 0;
    if (checked == 0) {
      std::fprintf(stderr, "umap: %zu entries or a key did not read back\n", map.size());
      return 3;
    }
  }
  group.InTurn([&] {
    PrintComparatorRow(c, group, n, input_records, "\"bucket_count\":" + std::to_string(buckets),
                       ms, timed_faults, checked);
  });
  return 0;
}

// Half-loaded tables of `buckets` buckets: records base+32b .. base+32b+31
// in the first 32 slots of bucket b (value word 32b+j), the rest empty.
void FillHalfLoaded(BucketTable::Slot* slots, size_t buckets, uint64_t base) {
  for (size_t b = 0; b < buckets; ++b) {
    for (size_t j = 0; j < BucketTable::kSlots; ++j) {
      BucketTable::Slot& s = slots[b * BucketTable::kSlots + j];
      const uint64_t i = 32 * b + j;
      s.tag = j < 32 ? 0 : BucketTable::kEmpty;
      s.key = RandomKey(base + i);
      WriteWord(s.value, sizeof(s.value), i);
    }
  }
}

int RunBucketTable(const Config& c, ParallelInstances& group, bool sort) {
  using Slot = BucketTable::Slot;
  const uint64_t n = ComparatorEntries(c);
  const size_t buckets = n / 32;
  std::vector<Slot> storage(buckets * BucketTable::kSlots);
  std::vector<Slot> source(sort ? 0 : storage.size());  // direct's input
  std::vector<uint32_t> counts(sort ? 0 : buckets, 0);
  std::vector<double> ms;
  uint64_t timed_faults = 0;
  size_t checked = 0, stashed = 0;
  uint64_t input_records = 0;
  for (unsigned rep = 0; rep < c.reps; ++rep) {
    BucketTable table(storage.data(), buckets);
    const std::vector<Slot>& input = sort ? storage : source;
    FillHalfLoaded(sort ? storage.data() : source.data(), buckets, rep * n);
    if (rep == 0) {
      for (const Slot& s : input) input_records += !(s.tag & BucketTable::kEmpty);
    }
    group.Sync();
    const uint64_t faults = MinorFaults();
    const Clock::time_point t0 = Clock::now();
    if (sort) {
      table.SortRebuild();
    } else {
      table.DirectRebuild(source.data(), source.size(), counts.data());
    }
    ms.push_back(std::chrono::duration<double, std::milli>(Clock::now() - t0).count());
    timed_faults += MinorFaults() - faults;
    if (rep != 0) continue;
    stashed = table.stash().size();
    checked = table.Count() == n ? ReadBack(n, [&](uint32_t key, uint64_t* value) {
      uint8_t bytes[8];
      if (!table.Find(key, bytes)) return false;
      *value = Word(bytes);
      return true;
    }) : 0;
    if (checked == 0) {
      std::fprintf(stderr, "%s: %zu entries or a key did not read back\n", c.mode.c_str(), table.Count());
      return 3;
    }
  }
  group.InTurn([&] {
    PrintComparatorRow(c, group, n, input_records,
                       "\"buckets\":" + std::to_string(buckets) + ",\"slot_bytes\":" +
                           std::to_string(sizeof(Slot)) + ",\"stashed\":" + std::to_string(stashed),
                       ms, timed_faults, checked);
  });
  return 0;
}

void Usage() {
  std::printf(
      "usage: cpu_byteslice_table_rebuild_benchmark --mode MODE [options]\n"
      "  --mode M       init | chain (ours); umap-init | umap-merge |\n"
      "                 sort-merge | direct-merge (the comparators)\n"
      "  --capacity N   entries (default 2^20): init builds a table of the\n"
      "                 map's capacity(), chain's cascades build every table\n"
      "                 size below its top, the comparators a table of N (a\n"
      "                 power of two >= 1024)\n"
      "  --key N        key bytes (default 4; the comparators take 4)\n"
      "  --value N      value bytes (default 8; the comparators take 8)\n"
      "  --digit N      top digit D in {1,2}; 0 (default) lets the ladder choose\n"
      "  --reps N       init and comparators: timed repetitions (default 5)\n"
      "  --window N     chain: measured periods of the deepest cascade (default 3)\n"
      "  --seed N       secret seed and input seed (default 1)\n"
      "  --cpu LIST     one instance per listed CPU, side by side, pinned\n"
      "                 (\"3\", \"1,2,3\", \"1-4\"); default one unpinned instance\n");
}

}  // namespace

int main(int argc, char** argv) {
  Config c;
  try {
    for (int a = 1; a < argc; ++a) {
      const std::string arg = argv[a];
      if (arg == "--help" || arg == "-h") {
        Usage();
        return 0;
      }
      if (a + 1 >= argc) throw std::invalid_argument(arg + " needs a value");
      const std::string v = argv[++a];
      if (arg == "--mode") c.mode = v;
      else if (arg == "--capacity") c.capacity = std::stoull(v);
      else if (arg == "--key") c.key_bytes = std::stoul(v);
      else if (arg == "--value") c.value_bytes = std::stoul(v);
      else if (arg == "--digit") c.top_digit = unsigned(std::stoul(v));
      else if (arg == "--reps") c.reps = unsigned(std::stoul(v));
      else if (arg == "--window") c.window = unsigned(std::stoul(v));
      else if (arg == "--seed") c.seed = std::stoull(v);
      else if (arg == "--cpu") c.cpus = v;
      else throw std::invalid_argument("unknown option " + arg);
    }
    const bool ours = c.mode == "init" || c.mode == "chain";
    if (!ours && c.mode != "umap-init" && c.mode != "umap-merge" && c.mode != "sort-merge" &&
        c.mode != "direct-merge") {
      throw std::invalid_argument("unknown --mode " + c.mode);
    }
    if (c.reps == 0 || c.window == 0) throw std::invalid_argument("--reps and --window must be positive");
    return ParallelInstances::Run(ParallelInstances::ParseCpus(c.cpus), [&](ParallelInstances& group) {
      if (c.mode == "init") return RunInit(c, group);
      if (c.mode == "chain") return RunChain(c, group);
      if (c.mode == "umap-init" || c.mode == "umap-merge") return RunUmap(c, group, c.mode == "umap-merge");
      return RunBucketTable(c, group, c.mode == "sort-merge");
    });
  } catch (const std::exception& e) {
    std::fprintf(stderr, "error: %s\n", e.what());
    return 2;
  }
}
