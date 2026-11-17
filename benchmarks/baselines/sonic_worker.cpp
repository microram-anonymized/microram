// oram_baseline_sonic: SONIC's ZingORAM (README.md in this directory) in
// the shared one-trial harness, as `sonic_zingoram` (position map outside) or
// `sonic_zingoram_recursive` (a recursive position map of ZingORAM trees). One
// Clang build with SONIC's optional AVX-512 primitives on, compiled with
// SONIC's own flags.
//
// Rows take the paper's configurations unless overridden: Ser (T=1, Z=8, S=12,
// R=3, E=1) for scalar rows and Par8 (T=8, Z=16, S=16, R=3, E=2) for batch
// rows, with every map tree at the data tree's parameters, b = 16 and C = 2^11.
// Keys must be dense (key i is the integer i < N): SONIC addresses blocks 0..N-1.
#include "benchmarks/support/baseline_worker.hpp"
#include "fetch_record.hpp"
#include "benchmarks/baselines/sonic_map.hpp"

#include "sonic/oram/zingoram/threading.hpp"
#include "sonic/threads/platform/pthread_thread_pool.hpp"
#include "sonic/threads/tuning.hpp"
#include "sonic/util/log.hpp"

#include <sstream>

#ifdef ORAM_BASELINE_ALLOCATION_AUDIT
#include "benchmarks/support/baseline_allocation_audit.hpp"
#endif

namespace {
namespace ob = oram_bench;
namespace bl = oram_bench::baseline;
namespace sm = oram_bench::sonic;

void Check(bool condition, const std::string& message) {
  if (!condition) throw std::invalid_argument(message);
}

struct Settings {
  bool recursive = false;
  sm::TreeParams data, map;
  uint32_t routing = 3;
  unsigned access_threads = 1, eviction_threads = 0;  // 0: 2^R
  unsigned branching = 16;
  uint64_t top_entries = 2048;  // C = 2^11, the paper's runs
  std::string preset;
  std::set<std::string> explicit_fields;
};

Settings ParseSettings(const ob::WorkerOptions& o) {
  Settings s;
  Check(o.scheme == "sonic_zingoram" || o.scheme == "sonic_zingoram_recursive",
        "this worker runs sonic_zingoram and sonic_zingoram_recursive");
  s.recursive = o.scheme == "sonic_zingoram_recursive";
  // The paper's fixed configurations: Ser for one caller, Par8 for batches.
  if (o.batched) { s.preset = "Par8"; s.data = {16, 16, 0, 2}; s.access_threads = 8; }
  else { s.preset = "Ser"; s.data = {8, 12, 0, 1}; s.access_threads = 1; }
  std::map<std::string, uint64_t> values;
  for (const auto& [name, value] : o.overrides) {
    Check(name.rfind("sonic.", 0) == 0, "sonic: unknown override " + name);
    values[name.substr(6)] = ob::Integer(value);
    s.explicit_fields.insert(name.substr(6));
  }
  auto take = [&](const char* field, auto& target) {
    if (auto at = values.find(field); at != values.end()) {
      target = static_cast<std::decay_t<decltype(target)>>(at->second);
      values.erase(at);
    }
  };
  take("bucket_real_size", s.data.real); take("bucket_dummy_size", s.data.dummy);
  take("eviction_rate", s.data.rate); take("evict_batch", s.data.batch);
  take("routing_depth", s.routing); take("access_threads", s.access_threads);
  take("eviction_threads", s.eviction_threads);
  s.map = s.data;  // map trees default to the data tree's parameters
  take("map_bucket_real_size", s.map.real); take("map_bucket_dummy_size", s.map.dummy);
  take("map_eviction_rate", s.map.rate); take("map_evict_batch", s.map.batch);
  take("map_branching_factor", s.branching); take("map_top_entries", s.top_entries);
  Check(values.empty(), "sonic: unknown override sonic." + (values.empty() ? "" : values.begin()->first));
  const bool map_field = std::any_of(s.explicit_fields.begin(), s.explicit_fields.end(),
                                     [](const std::string& f) { return f.rfind("map_", 0) == 0; });
  Check(s.recursive || !map_field, "sonic: map_* overrides belong to sonic_zingoram_recursive");
  Check(s.branching == 16 || s.branching == 32 || s.branching == 64 || s.branching == 128 || s.branching == 256,
        "sonic: map_branching_factor is 16, 32, 64, 128 or 256");
  Check(s.top_entries >= 1 && s.top_entries <= (uint64_t{1} << 24), "sonic: map_top_entries is 1..2^24");
  for (const auto* p : {&s.data, &s.map})
    Check(p->real >= 1 && p->dummy >= 1 && p->batch >= 1, "sonic: Z, S and E must be positive");
  Check(s.routing <= 16, "sonic: routing_depth is at most 16");
  Check(s.access_threads >= 1 && s.access_threads < sm::kMaxLanes, "sonic: access_threads is 1..15");
  Check(o.batched || s.access_threads == 1, "sonic: a scalar row has one caller; access_threads must be 1");
  if (!s.eviction_threads) s.eviction_threads = 1u << s.routing;
  Check((1u << s.routing) % s.eviction_threads == 0, "sonic: eviction_threads must divide 2^routing_depth");
  // Comparison rules 4 and 6 (README.md): dense keys only, and every request a hit.
  Check(o.workload.key_layout == ob::KeyLayout::kDense && o.workload.key_bytes <= 8,
        "sonic addresses blocks 0..N-1: it needs dense keys of at most 8 bytes");
  Check(o.workload.hit_ppm == 1000000, "sonic cannot report a miss (rule 6)");
  return s;
}

// The caller plus T-1 access workers; the eviction leader is an access thread,
// so eviction adds its team's other E-1 threads.
unsigned LibraryThreads(const Settings& s) { return s.access_threads + s.eviction_threads - 1; }

size_t DataBytes(size_t value_bytes) { return (value_bytes + 7) / 8 * 8; }  // ZingORAM blocks: multiples of 8

struct Resolution {
  std::vector<sm::Geometry> trees;  // data first, then map levels 1..L
  unsigned levels = 0;
  uint64_t top = 0;
  bl::Envelope envelope;
};
Resolution Resolve(const ob::WorkerOptions& o, const Settings& s) {
  Resolution r;
  const uint64_t n = o.capacity;
  const size_t data_bytes = DataBytes(o.workload.value_bytes);
  const unsigned threads = LibraryThreads(s);
  Check(threads + 1 <= o.cores, "sonic: the thread plan needs " + std::to_string(threads) + " library cores (" +
                                    std::to_string(s.access_threads) + " access, " +
                                    std::to_string(s.eviction_threads - 1) + " more for eviction); the budget has " +
                                    std::to_string(o.cores - 1));
  r.trees.push_back(sm::TreeGeometry(n, s.data, s.routing, data_bytes));
  Check(r.trees[0].routing == s.routing, "sonic: routing_depth exceeds the data tree's height");
  uint64_t blocks = n;
  if (s.recursive) {
    r.levels = sm::MapLevels(n, s.branching, s.top_entries);
    const uint64_t map_rate = s.map.rate ? s.map.rate : sm::zo::analysis::max_eviction_rate(s.map.real);
    for (unsigned level = 1; level <= r.levels; ++level) {
      blocks = (blocks + s.branching - 1) / s.branching;
      Check(2 * blocks > map_rate, "sonic: map tree " + std::to_string(level) + " would hold " +
                                       std::to_string(blocks) + " blocks, at most A/2 = " +
                                       std::to_string(map_rate / 2) +
                                       "; raise map_top_entries or lower map_branching_factor");
      r.trees.push_back(sm::TreeGeometry(blocks, s.map, s.routing, 4 * s.branching));
    }
    r.top = blocks;  // ceil(N / b^L): the level-L blocks whose labels the top map holds
  }
  auto& e = r.envelope;
  e.scheme = o.scheme;
  e.policy_identity = "baseline_sonic_v1";
  e.actual_capacity = n;
  e.library_threads = threads;
  uint64_t bytes = 0;
  for (const auto& tree : r.trees) bytes += tree.bytes;
  bytes += s.recursive ? 4 * r.top : 4 * n;                                   // top map, or position map
  bytes += size_t{sm::kMaxLanes} * sm::kMaxLanes * data_bytes + 4 * sm::kMaxLanes * data_bytes;  // window rows
  e.modeled_buffer_bytes = bytes;
  std::ostringstream key;
  const auto params = [](const sm::TreeParams& p) {
    return std::to_string(p.real) + "/" + std::to_string(p.dummy) + "/" + std::to_string(p.rate) + "/" +
           std::to_string(p.batch);
  };
  key << o.scheme << ";n=" << n << ";k=" << o.workload.key_bytes << ";v=" << o.workload.value_bytes
      << ";block=" << data_bytes << ";key_layout=dense;api=" << (o.batched ? "batch" : "scalar")
      << ";T=" << s.access_threads << ";R=" << s.routing << ";eviction_threads=" << s.eviction_threads
      << ";data=" << params(s.data);
  if (s.recursive) key << ";b=" << s.branching << ";C=" << s.top_entries << ";L=" << r.levels << ";map=" << params(s.map);
  e.configuration_key = key.str();
  const auto source = [&](const char* field) { return s.explicit_fields.count(field) ? "explicit" : "derived"; };
  e.choices = {{"scheme", o.scheme, "explicit", s.recursive ? "requested baseline, recursive position map (ours)"
                                                             : "requested baseline, position map outside"},
               {"preset", s.preset, "derived", "the paper's configuration for this API; overrides replace fields"},
               {"access_threads", std::to_string(s.access_threads), source("access_threads"), "T"},
               {"routing_depth", std::to_string(s.routing), source("routing_depth"), "R"},
               {"eviction_threads", std::to_string(s.eviction_threads), source("eviction_threads"), "divides 2^R"},
               {"library_threads", std::to_string(threads), "derived", "T + eviction threads - 1"}};
  for (size_t t = 0; t < r.trees.size(); ++t) {
    const auto& g = r.trees[t];
    const auto& p = t ? s.map : s.data;
    std::ostringstream tree;
    tree << "blocks=" << g.blocks << " Z=" << p.real << " S=" << p.dummy << " A=" << g.base_rate << " E=" << p.batch
         << " height=" << g.height << " R=" << g.routing << " stash_bound=" << g.stash_bound;
    e.choices.push_back({t ? "map_tree." + std::to_string(t) : "data_tree", tree.str(), "derived",
                         "SONIC's analysis: A is its largest for Z unless set; the stash meets 2^-80"});
  }
  if (s.recursive)
    e.choices.push_back({"map", "b=" + std::to_string(s.branching) + " C=" + std::to_string(s.top_entries) +
                                    " levels=" + std::to_string(r.levels) + " top_entries=" + std::to_string(r.top),
                         s.explicit_fields.count("map_branching_factor") || s.explicit_fields.count("map_top_entries")
                             ? "explicit" : "derived",
                         "the smallest L with ceil(N / b^L) <= C"});
  return r;
}

template <size_t... Widths> struct WidthList {};
using BlockWidths = WidthList<8, 16, 32, 48, 64, 128, 192, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768>;
template <size_t... W>
std::unique_ptr<sm::Tree> MakeTreeOf(size_t bytes, uint64_t blocks, const sm::TreeParams& p, uint32_t routing,
                                     unsigned access, sn::threads::thread_pool& eviction, unsigned eviction_threads,
                                     WidthList<W...>) {
  std::unique_ptr<sm::Tree> tree;
  const auto geometry = sm::TreeGeometry(blocks, p, routing, bytes);
  // Each tree's eviction team is a view of the shared pool, at most its 2^R subtrees wide.
  const unsigned team = std::min<unsigned>(eviction_threads, 1u << geometry.routing);
  const unsigned workers = sm::kMaxLanes;
  ((bytes == W && (tree = std::make_unique<sm::ZingTree<W>>(blocks, p, routing, access,
                                                             sn::threads::thread_team(eviction, team), workers),
                   true)) || ...);
  Check(tree != nullptr, "sonic: block width " + std::to_string(bytes) + " outside the instantiated widths");
  return tree;
}

// A dense key is its little-endian value.
uint64_t LoadKey(const uint8_t* key, size_t bytes) {
  uint64_t value = 0;
  for (size_t i = 0; i < bytes; ++i) value |= uint64_t{key[i]} << (8 * i);
  return value;
}

// The adapter: one window per scalar call, windows of T lanes per batch.
class SonicBackend {
 public:
  struct Request { bool write = false; const uint8_t* key = nullptr; const uint8_t* value = nullptr; uint8_t* output = nullptr; };
  static Request MakeRequest(bool write, const uint8_t* key, const uint8_t* value, uint8_t* output) {
    return {write, key, write ? value : nullptr, output};
  }
  SonicBackend(sm::Engine& engine, const ob::WorkloadSpec& w, size_t block_bytes, unsigned lanes,
               bl::TaskEvidence& evidence)
      : engine_(engine), key_bytes_(w.key_bytes), value_bytes_(w.value_bytes), block_(block_bytes), lanes_(lanes),
        values_(sm::kMaxLanes * block_bytes / 8 + 1), results_(sm::kMaxLanes * block_bytes / 8 + 1),
        evidence_(evidence) {}
  // N writes in key order, T at a time (a map block's first access creates it).
  uint64_t Fill(const ob::WorkloadGenerator& generator) {
    const uint64_t n = generator.spec().live_entries;
    for (uint64_t id = 0; id < n;) {
      sm::Window window;
      window.lanes = static_cast<unsigned>(std::min<uint64_t>(lanes_, n - id));
      for (unsigned w = 0; w < window.lanes; ++w, ++id) {
        window.key[w] = id;
        window.write[w] = true;
        Clear(Value(w));
        generator.Value(id, 0, Value(w), value_bytes_);
      }
      engine_.Run(window, Bytes(values_), Bytes(results_));
    }
    evidence_.Snapshot("after_fill");
    fill_times_ = engine_.phase_times();
    return n;
  }
  bool Find(const uint8_t* key, uint8_t* output) {
    sm::Window window;
    window.lanes = 1;
    window.key[0] = LoadKey(key, key_bytes_);
    engine_.Run(window, Bytes(values_), Bytes(results_));
    std::memcpy(output, Bytes(results_), value_bytes_);
    return true;  // an index ORAM cannot tell a miss (rule 6)
  }
  void Write(const uint8_t* key, const uint8_t* value) {
    sm::Window window;
    window.lanes = 1;
    window.key[0] = LoadKey(key, key_bytes_);
    window.write[0] = true;
    Clear(Value(0));
    std::memcpy(Value(0), value, value_bytes_);
    engine_.Run(window, Bytes(values_), Bytes(results_));
  }
  // Windows of T lanes in request order; a write returns the value before it.
  void Batch(size_t count, const Request* requests, uint8_t* found) {
    for (size_t first = 0; first < count; first += lanes_) {
      sm::Window window;
      window.lanes = static_cast<unsigned>(std::min<size_t>(lanes_, count - first));
      for (unsigned w = 0; w < window.lanes; ++w) {
        const auto& r = requests[first + w];
        window.key[w] = LoadKey(r.key, key_bytes_);
        window.write[w] = r.write;
        Clear(Value(w));
        if (r.write) std::memcpy(Value(w), r.value, value_bytes_);
      }
      engine_.Run(window, Bytes(values_), Bytes(results_));
      for (unsigned w = 0; w < window.lanes; ++w) {
        const auto& r = requests[first + w];
        if (r.output) std::memcpy(r.output, Bytes(results_) + size_t{w} * block_, value_bytes_);
        found[first + w] = 1;
      }
    }
  }
  void Finish() {}
  // Maintenance markers: SONIC's eviction runs inside each access; marking it needs a patch
  // inside its eviction, which the campaign does not apply.
  ob::MaintenanceMarkers Markers() const {
    return {"", "SONIC's eviction runs inside its accesses and is not instrumented (no patch inside its eviction)", {}};
  }
 private:
  friend std::string PhaseTimesJson(const SonicBackend& backend);
  static uint8_t* Bytes(std::vector<uint64_t>& words) { return reinterpret_cast<uint8_t*>(words.data()); }
  uint8_t* Value(unsigned lane) { return Bytes(values_) + size_t{lane} * block_; }
  void Clear(uint8_t* value) { std::memset(value, 0, block_); }
  sm::Engine& engine_;
  size_t key_bytes_, value_bytes_, block_;
  unsigned lanes_;
  std::vector<uint64_t> values_, results_;  // 8-byte aligned, as SONIC's word ops need
  bl::TaskEvidence& evidence_;
  sm::PhaseTimes fill_times_;
};

#ifdef ORAM_BASELINE_ALLOCATION_AUDIT
bool g_allocation_audit = false;
#endif
bool AuditOn() {
#ifdef ORAM_BASELINE_ALLOCATION_AUDIT
  return g_allocation_audit;
#else
  return false;
#endif
}

// The engine's map / data-tree time split, for the fill and for everything after it (warmup, settle,
// measurement, drain, final verification), written as sonic_phases.json beside the worker's summary.
std::string PhaseTimesJson(const SonicBackend& backend) {
  const sm::PhaseTimes& fill = backend.fill_times_;
  const sm::PhaseTimes& all = backend.engine_.phase_times();
  auto part = [](uint64_t windows, uint64_t accesses, uint64_t map_ns, uint64_t data_ns) {
    std::ostringstream out;
    out << "{\"windows\":" << windows << ",\"accesses\":" << accesses << ",\"map_ns\":" << map_ns
        << ",\"data_ns\":" << data_ns << "}";
    return out.str();
  };
  std::ostringstream out;
  out << "{\"schema\":\"sonic-phases-v1\",\"note\":\"wall ns on the calling thread; map = top scan + map trees "
         "(plain: the position array), data = the data tree\",\"fill\":"
      << part(fill.windows, fill.accesses, fill.map_ns, fill.data_ns) << ",\"after_fill\":"
      << part(all.windows - fill.windows, all.accesses - fill.accesses, all.map_ns - fill.map_ns,
              all.data_ns - fill.data_ns)
      << "}\n";
  return out.str();
}

int Run(const ob::WorkerOptions& o, const Settings& s) {
  const auto r = Resolve(o, s);
  const unsigned threads = LibraryThreads(s);
  auto slots = bl::ChooseSlots(o, threads, true);
  const auto resolved = bl::EnvelopeJson(o, r.envelope, slots);
  if (o.resolve_only) { std::cout << resolved << '\n'; return 0; }
  // SONIC's dedicated affinity takes one core per pool thread from the calling
  // thread's mask: give it the library slots other than the caller's, then
  // put the caller on its own slot (baseline_worker.hpp).
  if (slots.placed() && threads > 1) {
    const auto library = slots.library();
    bl::SetAffinity({library.begin() + 1, library.begin() + threads});
  }
  sn::threads::thread_policy policy{};
  policy.affinity = slots.placed() ? sn::threads::thread_affinity::dedicated : sn::threads::thread_affinity::inherit;
  sn::threads::thread_context context(policy);
  sn::threads::pthread_thread_pool access_pool(context, s.access_threads - 1, "access");
  sn::threads::pthread_thread_pool eviction_pool(context, s.eviction_threads - 1, "evict");
  if (slots.placed()) bl::SetAffinity({slots.cpus[0]});
#ifdef ORAM_BASELINE_ALLOCATION_AUDIT
  if (g_allocation_audit) {
    // Counted allocations (benchmarks/support/baseline_allocation_audit.hpp):
    // the baseline is taken here, after the thread pools started.
    bl::TaskEvidence quiet(slots);
    bl::AllocationAuditor auditor(o, o.scheme, "sonic");
    {
      sn::threads::thread_team access(access_pool.pool(), s.access_threads);
      std::unique_ptr<sm::Tree> data = MakeTreeOf(DataBytes(o.workload.value_bytes), o.capacity, s.data, s.routing,
                                                  s.access_threads, eviction_pool.pool(), s.eviction_threads, BlockWidths{});
      std::vector<std::unique_ptr<sm::Tree>> maps;
      for (unsigned level = 1; level <= r.levels; ++level)
        maps.push_back(MakeTreeOf(4 * s.branching, r.trees[level].blocks, s.map, s.routing, s.access_threads,
                                  eviction_pool.pool(), s.eviction_threads, BlockWidths{}));
      sm::EngineConfig config;
      config.entries = o.capacity;
      config.block_bytes = DataBytes(o.workload.value_bytes);
      config.recursive = s.recursive;
      config.branching = s.branching;
      config.top_entries = s.top_entries;
      sm::Engine engine(config, std::move(data), std::move(maps), s.access_threads > 1 ? &access : nullptr);
      auditor.Checkpoint("constructed");
      SonicBackend backend(engine, o.workload, config.block_bytes, s.access_threads, quiet);
      auditor.Run(backend);
    }
    auditor.Emit(o.capacity);
    return 0;
  }
#endif
  ob::WorkerArtifacts artifacts(o, resolved);
  bl::TaskEvidence evidence(slots);
  sn::threads::thread_team access(access_pool.pool(), s.access_threads);
  std::unique_ptr<sm::Tree> data = MakeTreeOf(DataBytes(o.workload.value_bytes), o.capacity, s.data, s.routing,
                                              s.access_threads, eviction_pool.pool(), s.eviction_threads, BlockWidths{});
  std::vector<std::unique_ptr<sm::Tree>> maps;
  for (unsigned level = 1; level <= r.levels; ++level)
    maps.push_back(MakeTreeOf(4 * s.branching, r.trees[level].blocks, s.map, s.routing, s.access_threads,
                              eviction_pool.pool(), s.eviction_threads, BlockWidths{}));
  sm::EngineConfig config;
  config.entries = o.capacity;
  config.block_bytes = DataBytes(o.workload.value_bytes);
  config.recursive = s.recursive;
  config.branching = s.branching;
  config.top_entries = s.top_entries;
  sm::Engine engine(config, std::move(data), std::move(maps), s.access_threads > 1 ? &access : nullptr);
  evidence.Snapshot("after_construction");
  ob::HarnessThreadInit harness_init;
  if (slots.placed())
    harness_init = [&](ob::HarnessThread) { bl::SetAffinity({slots.harness()}); evidence.AddHarnessThread(bl::ThreadId()); };
  SonicBackend backend(engine, o.workload, config.block_bytes, s.access_threads, evidence);
  int result = 0;
  try {
    result = ob::ExecuteWorker(o, backend, artifacts, harness_init);
  } catch (...) {
    evidence.Snapshot("after_failure");
    if (slots.placed()) artifacts.Write("placement.json", evidence.Json(false));
    throw;
  }
  evidence.Snapshot("after_trial");
  artifacts.Write("sonic_phases.json", PhaseTimesJson(backend));
  if (slots.placed()) {
    artifacts.Write("placement.json", evidence.Json(true));
    ob::Require(evidence.clean(), "sonic: a thread ran outside the library slots (placement.json)");
  }
  return result;
}
}  // namespace

int main(int argc, char** argv) {
  try {
    // SONIC's logger writes to std::cout, the worker's JSON channel.
    sn::util::log::global_logger().set_verbosity(sn::util::log::level::critical);
    if (argc == 1 || (argc == 2 && std::string(argv[1]) == "--help")) {
      ob::WorkerHelp();
      std::cout << "--scheme sonic_zingoram|sonic_zingoram_recursive, dense keys only\n"
                   "--override.sonic.FIELD N: bucket_real_size bucket_dummy_size eviction_rate evict_batch "
                   "routing_depth access_threads eviction_threads map_branching_factor map_top_entries "
                   "map_bucket_real_size map_bucket_dummy_size map_eviction_rate map_evict_batch\n";
      return 0;
    }
    if (ob::PrintCompiledIsa(argc, argv)) return 0;
    if (ob::PrintClockCheck(argc, argv)) return 0;
    if (bl::PrintBuildInfo(argc, argv, "sonic", bl::FetchRecord(), {})) return 0;
    std::vector<char*> args(argv, argv + argc);
    std::string resolve_flag = "--resolve-only", one = "1";
#ifdef ORAM_BASELINE_ALLOCATION_AUDIT
    g_allocation_audit = bl::TakeAuditFlag(args);
    if (g_allocation_audit) { args.push_back(resolve_flag.data()); args.push_back(one.data()); }
#endif
    auto o = ob::ParseWorker(static_cast<int>(args.size()), args.data());
    if (AuditOn()) o.resolve_only = false;
    return Run(o, ParseSettings(o));
  } catch (const std::exception& error) {
    std::cerr << "oram_baseline_sonic: " << error.what() << '\n';
    return 2;
  }
}
