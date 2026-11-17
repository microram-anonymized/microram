// oram_baseline_h2o2ram (patch P-H3, `oblivious`) and oram_baseline_h2o2ram_shipped
// (as published apart from P-H1/P-H2, `not_oblivious`): one source, two builds
// of one patched H2O2RAM tree (README.md in this directory lists the patches).
// The pair measures what the shipped build's secret-dependent branches buy.
//
// The shared one-trial harness drives an adapter over ORAM::ObliviousRAM. The
// index is the key's value (dense keys, or 8-byte keys with bit 63 cleared) or
// a keyed 63-bit AES-CMAC digest of a wider key (h2o2ram_index.hpp). --resolve-only reads
// the planner cache and never constructs a map; --prepare-planner 1 writes it.
#include "benchmarks/support/baseline_worker.hpp"
#include "fetch_record.hpp"
#include "benchmarks/baselines/h2o2ram_index.hpp"

#include <hash_planner.hpp>  // defines determine_hash; every H2O2RAM program needs it
#include <oram.hpp>

#include <omp.h>
#include <openssl/evp.h>
#include <tbb/blocked_range.h>
#include <tbb/global_control.h>
#include <tbb/parallel_for.h>

#include <cstdlib>
#include <cstring>

#ifdef ORAM_BASELINE_ALLOCATION_AUDIT
#include "benchmarks/support/baseline_allocation_audit.hpp"
#define ORAM_HARNESS_SCOPE() ::audit::HarnessScope harness_scope_
#else
#define ORAM_HARNESS_SCOPE() static_cast<void>(0)
#endif

namespace {
namespace ob = oram_bench;
namespace bl = oram_bench::baseline;
using namespace oram_bench::h2o2ram;

#ifdef H2O2RAM_CONSTANT_TIME_CMOV
constexpr const char* kScheme = "h2o2ram";
constexpr const char* kBuild = "patched";
#else
constexpr const char* kScheme = "h2o2ram_shipped";
constexpr const char* kBuild = "shipped";
#endif
void Check(bool condition, const std::string& message) {
  if (!condition) throw std::invalid_argument(message);
}
constexpr uint64_t kDelta = DELTA_INV_LOG2;          // their failure parameter, 2^-64
constexpr uint64_t kMinCapacity = MIN_CAPACITY;      // 65536

// ---- The planner cache: hash_map.bin<block bytes> beside the executable. ----
struct PlannerEntry { std::string type; uint64_t a = 0, b = 0; };
using PlannerKey = std::tuple<uint64_t, uint64_t, uint64_t>;
using PlannerCache = std::map<PlannerKey, PlannerEntry>;
std::string CachePath(size_t block_bytes) {
  return ORAM::getExecutablePath() + CONFIG_FILE + std::to_string(block_bytes);
}
// Parsed as determine_hash parses it; a later line wins, as there.
PlannerCache ReadCache(size_t block_bytes) {
  PlannerCache cache;
  std::ifstream file(CachePath(block_bytes));
  uint64_t n, op, delta;
  while (file >> n >> op >> delta) {
    PlannerEntry entry;
    file >> entry.type;
    if (entry.type == "bucket") file >> entry.a >> entry.b;         // bucket_num, bucket_size
    else if (entry.type == "two_tier") file >> entry.a;             // epsilon_inv
    else ob::Require(entry.type == "linear" || entry.type == "cuckoo", "unknown planner cache entry");
    cache[{n, op, delta}] = entry;
  }
  return cache;
}
std::string Sha256File(const std::string& path) {
  std::ifstream in(path, std::ios::binary);
  std::string bytes((std::istreambuf_iterator<char>(in)), std::istreambuf_iterator<char>());
  unsigned char digest[32]; unsigned length = 0;
  ob::Require(EVP_Digest(bytes.data(), bytes.size(), digest, &length, EVP_sha256(), nullptr) == 1,
              "sha256 failed");
  std::ostringstream out;
  for (unsigned i = 0; i < length; ++i) out << std::hex << std::setw(2) << std::setfill('0') << unsigned(digest[i]);
  return out.str();
}

// ---- The levels construction will build (ObliviousRAM's constructor, and
// insert's growth, which asks for the same sizes). ----
struct Table {
  uint64_t n = 0, op = 0;
  PlannerEntry entry;
  std::vector<Table> nested;  // a two-tier table's major bin, then its overflow bin
};
struct Levels {
  uint64_t capacity = 0, buffer = 0;
  std::vector<Table> tables;  // kept levels, smallest first; the top is last
  std::vector<PlannerKey> missing;
};
Table Plan(const PlannerCache& cache, uint64_t n, uint64_t op, std::vector<PlannerKey>& missing) {
  Table table{n, op, {}, {}};
  const auto at = cache.find({n, op, kDelta});
  if (at == cache.end()) { missing.emplace_back(n, op, kDelta); return table; }
  table.entry = at->second;
  if (table.entry.type == "two_tier") {  // OTwoTierHash's constructor
    const uint64_t eps = table.entry.a, bin_size = eps * eps * 1024;
    const uint64_t bins = n > bin_size ? 2 * n / bin_size : 1;
    table.nested.push_back(Plan(cache, bins == 1 ? n : bin_size / 2, n / bins, missing));
    if (bins > 1 && n / eps) table.nested.push_back(Plan(cache, n / eps, n, missing));
  }
  return table;
}
// With P-H4: a leading run of linear scans merges into the buffer, a later one
// stays a level, and the buffer is the smallest kept level (the top if none).
Levels PlanLevels(const PlannerCache& cache, uint64_t requested, uint64_t threshold) {
  Levels levels;
  uint64_t capacity = threshold;
  const uint64_t target = std::max(requested, kMinCapacity);
  for (; capacity < target; capacity <<= 1) {
    auto table = Plan(cache, capacity, capacity, levels.missing);
    if (!(levels.tables.empty() && table.entry.type == "linear")) levels.tables.push_back(std::move(table));
  }
  levels.buffer = levels.tables.empty() ? capacity : capacity >> levels.tables.size();
  levels.tables.push_back(Plan(cache, capacity, capacity, levels.missing));
  levels.capacity = capacity;
  return levels;
}
// Rebuild merges the buffer and levels 0..L-1 at offsets equal to their sizes,
// so the kept levels must be buffer x 2^i. The shipped constructor broke this
// whenever the planner kept a table below a linear one (P-H4); keep checking.
void CheckLayout(const Levels& levels) {
  for (size_t i = 0; i < levels.tables.size(); ++i)
    ob::Require(levels.tables[i].n == (levels.buffer << i), "h2o2ram: planned levels break its rebuild layout");
}
// Level i < top is rebuilt every buffer x 2^(i+1) appends, the top every
// capacity appends (a binary counter over the levels; the top absorbs).
std::vector<uint64_t> CarryPeriods(const Levels& levels) {
  std::vector<uint64_t> periods;
  for (size_t i = 0; i + 1 < levels.tables.size(); ++i) periods.push_back(levels.buffer << (i + 1));
  periods.push_back(levels.capacity);
  return periods;
}
// Bytes a table holds between rebuilds (its entries vector), block bytes B.
uint64_t TableBytes(const Table& t, uint64_t block) {
  const auto& type = t.entry.type;
  if (type == "linear") return t.n * block;
  if (type == "bucket") return t.entry.a * t.entry.b * block;
  if (type == "cuckoo") return 2 * t.n * block;
  // two_tier: every major bin, the overflow bin, and extracted_data's capacity.
  const uint64_t eps = t.entry.a, bin_size = eps * eps * 1024, bins = t.n > bin_size ? 2 * t.n / bin_size : 1;
  uint64_t bytes = bins * TableBytes(t.nested[0], block) + t.n * block + 4 * bins;
  if (t.nested.size() > 1) bytes += TableBytes(t.nested[1], block);
  return bytes;
}
std::string Describe(const Table& t) {
  std::ostringstream out;
  out << t.entry.type << " n=" << t.n;
  if (t.op != t.n) out << " op=" << t.op;
  if (t.entry.type == "bucket") out << " buckets=" << t.entry.a << " bucket_size=" << t.entry.b;
  if (t.entry.type == "two_tier") out << " epsilon_inv=" << t.entry.a;
  for (const auto& inner : t.nested) out << " [" << Describe(inner) << ']';
  return out.str();
}

// ---- Options. ----
struct Settings {
  uint64_t threshold = LINEAR_SCAN_THRESHOLD;
  std::string omp_wait_policy;      // empty: libgomp's default
  unsigned digest_bits = 63;        // test_digest_bits plants collisions
  bool prepare = false;
  unsigned library_threads = 1;     // TBB's and OpenMP's thread count
};
Settings ParseSettings(ob::WorkerOptions& o) {
  Settings s;
  for (const auto& [name, value] : o.overrides) {
    if (name == "h2o2ram.linear_scan_threshold") {
      s.threshold = ob::Integer(value);
      ob::Require(s.threshold == 128 || s.threshold == 256, "h2o2ram: linear_scan_threshold is 128 or 256");
    } else if (name == "h2o2ram.omp_wait_policy") {
      ob::Require(value == "active" || value == "passive", "h2o2ram: omp_wait_policy is active or passive");
      s.omp_wait_policy = value;
    } else if (name == "h2o2ram.test_digest_bits") {
      s.digest_bits = static_cast<unsigned>(ob::Integer(value));
      ob::Require(s.digest_bits >= 1 && s.digest_bits <= 63, "h2o2ram: test_digest_bits is 1..63");
    } else {
      throw std::invalid_argument("h2o2ram: unknown override " + name);
    }
  }
  Check(o.scheme == kScheme, std::string("this worker runs scheme ") + kScheme);
  ob::Require(!o.batched, "h2o2ram has one caller and no batch API; batch rows are not emulated");
  ob::Require(o.workload.hit_ppm == 1000000, "h2o2ram cannot report a miss (rule 6)");
  ob::Require(s.digest_bits == 63 || ModeFor(o.workload) == IndexMode::kDigest,
              "h2o2ram: test_digest_bits applies only to digest indices");
  s.library_threads = o.cores - 1;  // every library slot; the harness keeps its own
  return s;
}

// libgomp reads its environment when it loads, before main: a policy or thread
// count that differs from the environment's needs a fresh process image.
void ExecWithOpenMpEnvironment(const Settings& s, char** argv) {
  const std::map<std::string, std::string> wanted = {
      {"OMP_NUM_THREADS", std::to_string(s.library_threads)}, {"OMP_WAIT_POLICY", s.omp_wait_policy},
      {"OMP_PROC_BIND", ""}, {"OMP_PLACES", ""}, {"GOMP_CPU_AFFINITY", ""}, {"GOMP_SPINCOUNT", ""},
      {"OMP_DYNAMIC", ""}};
  bool same = true;
  for (const auto& [name, value] : wanted) {
    const char* current = std::getenv(name.c_str());
    same &= value.empty() ? current == nullptr : current && value == current;
  }
  if (same) return;
  ob::Require(std::getenv("H2O2RAM_WORKER_REEXEC") == nullptr, "h2o2ram: OpenMP environment did not take");
  for (const auto& [name, value] : wanted) {
    if (value.empty()) unsetenv(name.c_str());
    else setenv(name.c_str(), value.c_str(), 1);
  }
  setenv("H2O2RAM_WORKER_REEXEC", "1", 1);
  execv("/proc/self/exe", argv);
  throw std::runtime_error("h2o2ram: cannot re-execute with the OpenMP environment");
}

// Start TBB's workers and OpenMP's team while the caller's mask is still the
// library slots, so that every pool thread inherits it (baseline_worker.hpp).
bool StartPools(unsigned threads) {
  std::atomic<unsigned> arrived{0};
  const auto deadline = std::chrono::steady_clock::now() + std::chrono::seconds(10);
  tbb::parallel_for(tbb::blocked_range<unsigned>(0, threads, 1), [&](const tbb::blocked_range<unsigned>& r) {
    for (unsigned i = r.begin(); i != r.end(); ++i) {
      arrived.fetch_add(1);
      while (arrived.load() < threads && std::chrono::steady_clock::now() < deadline) std::this_thread::yield();
    }
  }, tbb::simple_partitioner());
  const bool tbb_complete = arrived.load() >= threads;
  unsigned team = 0;
#pragma omp parallel num_threads(threads)
  {
#pragma omp single
    team = omp_get_num_threads();
  }
  return tbb_complete && team == threads;
}

// ---- The adapter. ----
template <size_t V>
class H2O2RAMBackend {
 public:
  struct Value { uint8_t bytes[V]; };
  using Oram = ORAM::ObliviousRAM<uint64_t, Value>;
  struct Request { bool write = false; const uint8_t* key = nullptr; const uint8_t* value = nullptr; uint8_t* output = nullptr; };
  static Request MakeRequest(bool write, const uint8_t* key, const uint8_t* value, uint8_t* output) {
    return {write, key, write ? value : nullptr, output};
  }
  H2O2RAMBackend(const ob::WorkloadSpec& w, const Settings& s, const Levels& levels, bl::TaskEvidence& evidence)
      : key_bytes_(w.key_bytes), dense_(w.key_layout == ob::KeyLayout::kDense), mode_(ModeFor(w)),
        settings_(s), capacity_(levels.capacity), buffer_(levels.buffer),
        tables_(static_cast<unsigned>(levels.tables.size())),
        evidence_(evidence) {
    if (mode_ == IndexMode::kDigest) digest_ = std::make_unique<Digest>(s.digest_bits);
  }
  uint64_t Fill(const ob::WorkloadGenerator& generator) {
    const auto& spec = generator.spec();
    if (dense_) {
      // Direct initialization: key i is index i; slots above the live set hold
      // zero values, as every slot of their range constructor holds a block.
      std::vector<Value> values;
      {
        ORAM_HARNESS_SCOPE();  // the dataset handed to the constructor is the harness's (allocation audit)
        values.assign(capacity_, Value{});
      }
      for (uint64_t id = 0; id < spec.live_entries; ++id) generator.Value(id, 0, values[id].bytes, V);
      oram_ = std::make_unique<Oram>(values.begin(), values.end(), settings_.threshold);
      evidence_.Snapshot("after_fill");
      return 0;
    }
    std::vector<uint8_t> key(spec.key_bytes);
    if (mode_ == IndexMode::kDigest) {
      // Comparison rule 4 (README.md): H2O2RAM stores no key, so two keys with
      // one digest would share a block; fail an aliased map before the trial
      // rather than measure it.
      std::vector<uint64_t> digests;
      {
        ORAM_HARNESS_SCOPE();
        digests.resize(spec.live_entries);
      }
      for (uint64_t id = 0; id < spec.live_entries; ++id) {
        generator.Key(id, key.data(), key.size());
        digests[id] = Index(key.data());
      }
      collisions_ = CountCollisions(std::move(digests));
      Check(collisions_ == 0, "h2o2ram: " + std::to_string(collisions_) +
                                        " fill keys share a 63-bit index digest; the row would alias records");
    }
    oram_ = std::make_unique<Oram>(0, Value{}, settings_.threshold);
    Value value;
    for (uint64_t id = 0; id < spec.live_entries; ++id) {
      generator.Key(id, key.data(), key.size());
      generator.Value(id, 0, value.bytes, V);
      oram_->insert(Index(key.data()), value);
    }
    appends_ = spec.live_entries;
    // insert doubles from 65536 on a full map; the resolver planned the requested capacity.
    uint64_t grown = kMinCapacity;
    while (grown < spec.live_entries) grown <<= 1;
    ob::Require(grown == capacity_, "h2o2ram: occupancy leaves the map below its resolved capacity");
    evidence_.Snapshot("after_fill");
    return spec.live_entries;
  }
  bool Find(const uint8_t* key, uint8_t* output) {
    const uint64_t begin = RebuildBegin();
    const auto& slot = (*oram_)[Index(key)];
    RebuildEnd(begin);
    ++appends_;
    std::memcpy(output, slot.bytes, V);
    return true;  // an index ORAM cannot tell a miss (comparison rule 6: all hits)
  }
  // The same oblivious access; the old value is readable through the reference.
  void Write(const uint8_t* key, const uint8_t* value) {
    const uint64_t begin = RebuildBegin();
    auto& slot = (*oram_)[Index(key)];
    RebuildEnd(begin);
    ++appends_;
    std::memcpy(slot.bytes, value, V);
  }
  void Batch(size_t, const Request*, uint8_t*) { throw std::logic_error("h2o2ram is scalar only"); }
  void Finish() {}
  // Every buffer append (fill inserts and accesses) moves the rebuild clock.
  std::optional<uint64_t> AccessCount() const { return appends_; }
  const char* AccessCounter() const { return "buffer_appends"; }
  uint64_t collisions() const { return collisions_; }
  // Maintenance markers: H2O2RAM has no rebuild events. Its operator[] rebuilds first when
  // it finds the buffer full (clear_buffer_if_full), i.e. on the access that
  // starts at a positive multiple of `buffer` appends; that whole access is the
  // span, so it includes the access's own lookup. The k-th rebuild builds
  // table min(ctz(k), top), as its loop finds the first empty table below the
  // always-full top (0 = the smallest kept level).
  ob::MaintenanceMarkers Markers() const {
    return {"bracketed_buffer_full_access_includes_lookup", "", spans_};
  }
 private:
  uint64_t RebuildBegin() const {
    return appends_ != 0 && appends_ % buffer_ == 0 ? ob::SteadyNanos() : 0;
  }
  void RebuildEnd(uint64_t begin) {
    if (!begin) return;
    const uint64_t end = ob::SteadyNanos();
    const unsigned level = std::min<unsigned>(__builtin_ctzll(appends_ / buffer_), tables_ - 1);
    ORAM_HARNESS_SCOPE();
    spans_.push_back({"h2o2ram_rebuild", level, begin, end});
  }
  uint64_t Index(const uint8_t* key) {
    return mode_ == IndexMode::kDigest ? (*digest_)(key, key_bytes_) : ValueIndex(key, key_bytes_, mode_);
  }
  size_t key_bytes_;
  bool dense_;
  IndexMode mode_;
  Settings settings_;
  uint64_t capacity_, buffer_, appends_ = 0, collisions_ = 0;
  unsigned tables_;
  std::vector<ob::MaintenanceSpan> spans_;
  std::unique_ptr<Digest> digest_;
  std::unique_ptr<Oram> oram_;
  bl::TaskEvidence& evidence_;
};

template <size_t... Widths> struct WidthList {};
using CampaignWidths = WidthList<8, 16, 32, 48, 64, 128, 192, 256, 512, 1024, 2048, 4096>;
template <class F, size_t... V> bool Dispatch(size_t width, F&& f, WidthList<V...>) {
  return ((width == V && (f(std::integral_constant<size_t, V>{}), true)) || ...);
}
template <class F> void DispatchWidth(size_t width, F&& f) {
  ob::Require(Dispatch(width, f, CampaignWidths{}), "h2o2ram: value width outside the instantiated campaign widths");
}

std::vector<std::string> SideFiles() {
  std::vector<std::string> names;
  std::error_code error;
  for (const auto& entry : std::filesystem::directory_iterator(ORAM::getExecutablePath(), error)) {
    const auto name = entry.path().filename().string();
    if (entry.is_regular_file() && name.rfind(CONFIG_FILE, 0) == 0) names.push_back(name);
  }
  std::sort(names.begin(), names.end());
  return names;
}

struct Resolution {
  Levels levels;
  size_t block_bytes = 0;
  std::string cache_sha256;
  bl::Envelope envelope;
};
Resolution Resolve(const ob::WorkerOptions& o, const Settings& s) {
  Resolution r;
  r.block_bytes = o.workload.value_bytes + sizeof(uint64_t);  // Block<uint64_t, sizeof(Value) + 8>
  const auto cache = ReadCache(r.block_bytes);
  r.levels = PlanLevels(cache, o.capacity, s.threshold);
  if (!r.levels.missing.empty()) {
    std::ostringstream out;
    out << "h2o2ram: planner cache " << CachePath(r.block_bytes) << " has no entry for";
    for (const auto& [n, op, delta] : r.levels.missing) out << " (n " << n << ", op " << op << ", delta " << delta << ')';
    out << "; run `oram_bench prepare-h2o2ram` on this host first";
    throw std::runtime_error(out.str());
  }
  CheckLayout(r.levels);
  r.cache_sha256 = Sha256File(CachePath(r.block_bytes));
  const auto& L = r.levels;
  auto& e = r.envelope;
  e.scheme = kScheme;
  e.policy_identity = "baseline_h2o2ram_v1";
  e.actual_capacity = L.capacity;
  e.supports_direct_initialization = o.workload.key_layout == ob::KeyLayout::kDense;
  e.library_threads = s.library_threads;
  e.carry_periods = CarryPeriods(L);
  // Between rebuilds: every level's table and the buffer. The worst transient is
  // a top rebuild's, which builds the new tables beside the old ones and
  // extracts the blocks: steady plus about three blocks per entry. The model
  // reserves steady plus that transient; peak RSS (VmHWM) shows that a flat
  // four-blocks-per-entry model would underestimate it.
  uint64_t steady = L.buffer * r.block_bytes;
  for (const auto& table : L.tables) steady += TableBytes(table, r.block_bytes);
  const uint64_t transient = steady + L.capacity * r.block_bytes * 3 +
      (e.supports_direct_initialization ? L.capacity * o.workload.value_bytes : 0);
  e.modeled_buffer_bytes = steady + transient;
  const auto mode = ModeFor(o.workload);
  const char* layout = o.workload.key_layout == ob::KeyLayout::kDense ? "dense" : "permuted";
  const std::string policy = s.omp_wait_policy.empty() ? "default" : s.omp_wait_policy;
  std::ostringstream key;
  key << kScheme << ";build=" << kBuild << ";k=" << o.workload.key_bytes << ";v=" << o.workload.value_bytes
      << ";key_layout=" << layout << ";index=" << IndexModeName(mode) << ";digest_bits=" << s.digest_bits
      << ";capacity=" << L.capacity << ";threshold=" << s.threshold << ";delta=" << kDelta
      << ";threads=" << s.library_threads << ";omp_wait_policy=" << policy << ";planner=" << r.cache_sha256;
  e.configuration_key = key.str();
  const auto source = [&](bool explicit_value) { return explicit_value ? "explicit" : "derived"; };
  e.choices = {{"scheme", kScheme, "explicit", std::string("requested baseline, ") + kBuild + " build"},
               {"index", IndexModeName(mode), "derived", "rule 4, from the key width and layout"},
               {"linear_scan_threshold", std::to_string(s.threshold),
                source(s.threshold != LINEAR_SCAN_THRESHOLD), "their LINEAR_SCAN_THRESHOLD, or the override"},
               {"delta_inv_log2", std::to_string(kDelta), "derived", "their DELTA_INV_LOG2"},
               {"buffer_entries", std::to_string(L.buffer), "derived", "linear-scan buffer: the smallest kept level (P-H4)"},
               {"library_threads", std::to_string(s.library_threads), "derived", "TBB and OpenMP threads: every library slot"},
               {"omp_wait_policy", policy, source(!s.omp_wait_policy.empty()), "OpenMP idle policy"}};
  if (s.digest_bits != 63)
    e.choices.push_back({"test_digest_bits", std::to_string(s.digest_bits), "explicit", "test only: plants collisions"});
  for (size_t i = 0; i < L.tables.size(); ++i)
    e.choices.push_back({"level." + std::to_string(i), Describe(L.tables[i]), "derived",
                         "planner cache " CONFIG_FILE + std::to_string(r.block_bytes)});
  e.choices.push_back({"planner_cache", CONFIG_FILE + std::to_string(r.block_bytes) + " sha256=" + r.cache_sha256,
                       "derived", "frozen beside the worker by resolve; a miss fails the trial (P-H2)"});
  e.choices.push_back({"modeled_steady_bytes", std::to_string(steady), "derived",
                       "tables and buffer between rebuilds; the model adds a top rebuild's transient"});
  return r;
}

// Plan every level a campaign row will construct, on this host: determine_hash
// times what the cache lacks and appends its choice (P-H1 prints to stderr).
template <size_t B> void PrepareLevels(uint64_t requested, uint64_t threshold) {
  uint64_t capacity = threshold;
  for (; capacity < std::max(requested, kMinCapacity); capacity <<= 1)
    delete ORAM::determine_hash<uint64_t, B>(capacity, capacity, kDelta);
  delete ORAM::determine_hash<uint64_t, B>(capacity, capacity, kDelta);
}

// Set only by --allocation-audit, which only the counted build accepts.
bool g_allocation_audit = false;

int Run(ob::WorkerOptions o, const Settings& s, char** argv) {
  if (s.prepare) {
    const auto slots = bl::ChooseSlots(o, s.library_threads, true);
    if (slots.placed()) bl::SetAffinity(slots.library());
    tbb::global_control control(tbb::global_control::max_allowed_parallelism, s.library_threads);
    ORAM::planner_frozen() = false;
    const auto begin = std::chrono::steady_clock::now();
    DispatchWidth(o.workload.value_bytes, [&](auto v) { PrepareLevels<v() + sizeof(uint64_t)>(o.capacity, s.threshold); });
    const auto ns = std::chrono::duration_cast<std::chrono::nanoseconds>(std::chrono::steady_clock::now() - begin).count();
    ORAM::planner_frozen() = true;
    const auto r = Resolve(o, s);  // the cache must now cover the row
    std::cout << "{\"prepared\":" << ob::JsonQuote(CachePath(r.block_bytes)) << ",\"planner_ns\":" << ns
              << ",\"planner_cache_sha256\":" << ob::JsonQuote(r.cache_sha256) << "}\n";
    return 0;
  }
  const auto r = Resolve(o, s);
  auto slots = bl::ChooseSlots(o, s.library_threads, true);
  const auto resolved = bl::EnvelopeJson(o, r.envelope, slots);
  if (o.resolve_only) { std::cout << resolved << '\n'; return 0; }
  (void)argv;
  // Before any TBB or OpenMP call: the pools start inside the library slots,
  // then the caller takes its own.
  if (slots.placed()) bl::SetAffinity(slots.library());
  tbb::global_control control(tbb::global_control::max_allowed_parallelism, s.library_threads);
  omp_set_num_threads(static_cast<int>(s.library_threads));
  const bool pools_started = StartPools(s.library_threads);
  if (slots.placed()) bl::SetAffinity({slots.cpus[0]});
#ifdef ORAM_BASELINE_ALLOCATION_AUDIT
  if (g_allocation_audit) {
    // Counted allocations (benchmarks/support/baseline_allocation_audit.hpp):
    // the baseline is taken here, after the pools started.
    bl::TaskEvidence quiet(slots);
    bl::AllocationAuditor auditor(o, kScheme, kBuild);
    DispatchWidth(o.workload.value_bytes, [&](auto v) {
      H2O2RAMBackend<v()> backend(o.workload, s, r.levels, quiet);
      auditor.Run(backend);
    });
    auditor.Emit(r.levels.capacity);
    return pools_started ? 0 : 3;
  }
#endif
  ob::WorkerArtifacts artifacts(o, resolved);
  bl::TaskEvidence evidence(slots);
  evidence.Snapshot("after_pool_start");
  auto trial = o;
  trial.carry_periods = r.envelope.carry_periods;
  ob::HarnessThreadInit harness_init;
  if (slots.placed())
    harness_init = [&](ob::HarnessThread) { bl::SetAffinity({slots.harness()}); evidence.AddHarnessThread(bl::ThreadId()); };
  int result = 0;
  uint64_t collisions = 0;
  try {
    DispatchWidth(o.workload.value_bytes, [&](auto v) {
      H2O2RAMBackend<v()> backend(o.workload, s, r.levels, evidence);
      try {
        result = ob::ExecuteWorker(trial, backend, artifacts, harness_init);
      } catch (...) {
        collisions = backend.collisions();
        throw;
      }
      collisions = backend.collisions();
    });
  } catch (...) {
    artifacts.Write("baseline.json", "{\"digest_collisions\":" + std::to_string(collisions) + "}\n");
    evidence.Snapshot("after_failure");
    if (slots.placed()) artifacts.Write("placement.json", evidence.Json(false));
    throw;
  }
  evidence.Snapshot("after_trial");
  std::ostringstream info;
  info << "{\"baseline\":" << ob::JsonQuote(kScheme) << ",\"build\":" << ob::JsonQuote(kBuild)
       << ",\"index\":" << ob::JsonQuote(IndexModeName(ModeFor(o.workload))) << ",\"digest_collisions\":" << collisions
       << ",\"pools_started_in_slots\":" << (pools_started ? "true" : "false") << "}\n";
  artifacts.Write("baseline.json", info.str());
  if (slots.placed()) {
    artifacts.Write("placement.json", evidence.Json(pools_started));
    ob::Require(evidence.clean(), "h2o2ram: a thread ran outside the library slots (placement.json)");
  }
  return result;
}
}  // namespace

int main(int argc, char** argv) {
  try {
    if (argc == 1 || (argc == 2 && std::string(argv[1]) == "--help")) {
      ob::WorkerHelp();
      std::cout << "--prepare-planner 1: time and cache the planner's table choices for this row\n"
                   "--override.h2o2ram.linear_scan_threshold 128|256, --override.h2o2ram.omp_wait_policy "
                   "active|passive\n--build-info (alone: side files and fetch record)\n";
      return 0;
    }
    if (ob::PrintCompiledIsa(argc, argv)) return 0;
    if (ob::PrintClockCheck(argc, argv)) return 0;
    if (bl::PrintBuildInfo(argc, argv, kScheme, bl::FetchRecord(), SideFiles())) return 0;
    // Our one option; the rest are the shared harness's.
    std::vector<char*> args(argv, argv + argc);
    bool prepare = false;
    for (size_t i = 1; i + 1 < args.size(); ++i) {
      if (std::string(args[i]) != "--prepare-planner") continue;
      ob::Require(std::string(args[i + 1]) == "1" || std::string(args[i + 1]) == "0", "--prepare-planner 0|1");
      prepare = std::string(args[i + 1]) == "1";
      args.erase(args.begin() + i, args.begin() + i + 2);
      break;
    }
    // Preparing writes no trial output: it parses as a resolve-only call.
    std::string resolve_flag = "--resolve-only", one = "1";
    const bool has_resolve = std::any_of(args.begin(), args.end(), [](char* a) { return std::string(a) == "--resolve-only"; });
    if (prepare) {
      ob::Require(!has_resolve, "--prepare-planner and --resolve-only are separate steps");
      args.push_back(resolve_flag.data()); args.push_back(one.data());
    }
#ifdef ORAM_BASELINE_ALLOCATION_AUDIT
    g_allocation_audit = bl::TakeAuditFlag(args);
    ob::Require(!(g_allocation_audit && (prepare || has_resolve)), "--allocation-audit is its own step");
    if (g_allocation_audit) { args.push_back(resolve_flag.data()); args.push_back(one.data()); }
#endif
    auto o = ob::ParseWorker(static_cast<int>(args.size()), args.data());
    if (prepare || g_allocation_audit) o.resolve_only = false;
    auto s = ParseSettings(o);
    s.prepare = prepare;
    ExecWithOpenMpEnvironment(s, argv);
    return Run(o, s, argv);
  } catch (const std::exception& error) {
    std::cerr << "oram_baseline_h2o2ram: " << error.what() << '\n';
    return 2;
  }
}
