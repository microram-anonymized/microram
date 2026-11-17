// The single-trial campaign worker: one resolved public-API trial of the
// library or of a baseline, driven by analysis/oram_bench (its command line
// and output protocol are documented in analysis/oram_bench/WORKER.md).
//
// For a library scheme (auto, hierarchical_incremental,
// hierarchical_synchronous, tree) it turns the worker's arguments into a
// public MapSpec, ResourceBudget, WorkloadHint and option overrides, resolves
// them with resolve_options, places the caller, harness and engine threads
// on the requested CPUs (verifying the placement afterwards), builds the map
// with make_map and runs the shared trial loop (fill, settle, timed scalar or
// batch window, telemetry).  `std_unordered_map` runs the same trial over a
// plain unordered_map as the non-oblivious throughput ceiling, and the
// synthetic schemes exercise the harness without a map.

#include "benchmarks/support/worker.hpp"
#include "benchmarks/support/fake_backend.hpp"
#include "benchmarks/support/cpu_backend.hpp"
#include "benchmarks/support/placement.hpp"
#include "benchmarks/support/baseline_worker.hpp"
#include <string_view>
#include <unordered_map>

namespace {
namespace ob=oram_bench;
namespace api=cpu_byteslice_oram;

// The throughput ceiling: a plain hash map of fixed-width records, one
// thread, no maintenance, no security.  Keys hash as their bytes, so dense keys
// cost what any others do. reserve(N) before the fill, at the library's default
// maximum load factor (1.0), keeps rehashing out of the measured window.
template <size_t K, size_t V, bool NoexceptHash=false>
class StdUnorderedMapBackend {
 public:
  struct Key {
    std::array<uint8_t,K> bytes;
    bool operator==(const Key& other) const { return bytes==other.bytes; }
  };
  struct Value { std::array<uint8_t,V> bytes; };
  // By default not noexcept, like std::hash<std::string>: libstdc++ then caches
  // each node's hash. NoexceptHash drops the cache (8 B per node) and rehashes a
  // visited node's key to find where its bucket ends.
  struct Hash {
    size_t operator()(const Key& key) const noexcept(NoexceptHash) {
      return std::hash<std::string_view>{}(std::string_view(reinterpret_cast<const char*>(key.bytes.data()),K));
    }
  };
  using Map=std::unordered_map<Key,Value,Hash>;
  struct Request { bool write=false; const uint8_t* key=nullptr; const uint8_t* value=nullptr; uint8_t* output=nullptr; };
  static Request MakeRequest(bool write,const uint8_t* key,const uint8_t* value,uint8_t* output) {
    return {write,key,write ? value : nullptr,output};
  }
  // The bucket count reserve(entries) gives at the default maximum load factor.
  static uint64_t Buckets(uint64_t entries) {
#ifdef __GLIBCXX__
    const std::__detail::_Prime_rehash_policy policy(1.0f);
    return policy._M_next_bkt(policy._M_bkt_for_elements(entries));
#else
    return entries;
#endif
  }
  // One node: its next pointer, the record and (unless NoexceptHash) the cached
  // hash, in a glibc chunk (8-byte size field, 16-byte granule, 32 minimum); 8 B
  // per bucket.
  static uint64_t ModeledBytes(uint64_t entries) {
#ifdef __GLIBCXX__
    static_assert(std::__cache_default<Key,Hash>::value==!NoexceptHash,"the byte model's hash cache");
    constexpr uint64_t node=sizeof(std::__detail::_Hash_node<std::pair<const Key,Value>,!NoexceptHash>);
#else
    constexpr uint64_t node=(NoexceptHash ? 1 : 2)*sizeof(void*)+K+V;
#endif
    const uint64_t chunk=std::max<uint64_t>(32,(node+8+15)/16*16);
    return entries*chunk+Buckets(entries)*sizeof(void*);
  }
  explicit StdUnorderedMapBackend(uint64_t capacity) : capacity_(capacity) {}
  uint64_t Fill(const ob::WorkloadGenerator& generator) {
    const auto& spec=generator.spec();
    map_.reserve(capacity_);
    Key key; Value value;
    for (uint64_t id=0; id<spec.live_entries; ++id) {
      generator.Key(id,key.bytes.data(),K); generator.Value(id,0,value.bytes.data(),V);
      ob::Require(map_.emplace(key,value).second,"std_unordered_map: duplicate fill key");
    }
    ob::Require(map_.bucket_count()==Buckets(capacity_),"std_unordered_map: the fill rehashed");
    return 0;
  }
  bool Find(const uint8_t* key,uint8_t* output) {
    const auto at=map_.find(Load(key));
    if (at==map_.end()) return false;
    std::copy_n(at->second.bytes.data(),V,output);
    return true;
  }
  void Write(const uint8_t* key,const uint8_t* value) {
    const auto at=map_.find(Load(key));
    ob::Require(at!=map_.end(),"std_unordered_map: the workload wrote an absent key");
    std::copy_n(value,V,at->second.bytes.data());
  }
  // One thread, the requests in order in one loop: nothing between two lookups,
  // so the core overlaps their cache misses. A write returns the value before it.
  void Batch(size_t count,const Request* requests,uint8_t* found) {
    for (size_t i=0; i<count; ++i) {
      const auto& r=requests[i];
      const auto at=map_.find(Load(r.key));
      ob::Require(at!=map_.end() || !r.write,"std_unordered_map: the workload wrote an absent key");
      found[i]=at!=map_.end();
      if (!found[i]) continue;
      std::copy_n(at->second.bytes.data(),V,r.output);
      if (r.write) std::copy_n(r.value,V,at->second.bytes.data());
    }
  }
  void Finish() {}
 private:
  static Key Load(const uint8_t* bytes) { Key key; std::copy_n(bytes,K,key.bytes.data()); return key; }
  uint64_t capacity_;
  Map map_;
};

template <size_t... Values> struct WidthList {};
// The campaign's value widths, at its key widths (4, 8 and 32 bytes).
using CampaignValues=WidthList<8,16,32,48,64,128,192,256,512,1024,2048,4096>;
template <size_t K,class F,size_t... V>
bool DispatchValue(size_t value_bytes,F&& f,WidthList<V...>) {
  return ((value_bytes==V && (f(std::integral_constant<size_t,K>{},std::integral_constant<size_t,V>{}),true)) || ...);
}
template <class F> bool DispatchWidths(size_t key_bytes,size_t value_bytes,F&& f) {
  switch (key_bytes) {
    case 4: return DispatchValue<4>(value_bytes,f,CampaignValues{});
    case 8: return DispatchValue<8>(value_bytes,f,CampaignValues{});
    case 32: return DispatchValue<32>(value_bytes,f,CampaignValues{});
  }
  return false;
}
template <class T> struct Tag { using type=T; };
// f(Tag<StdUnorderedMapBackend<K,V,noexcept_hash>>) at the row's widths.
template <class F> bool DispatchUnorderedMap(const ob::WorkerOptions& o,bool noexcept_hash,F&& f) {
  return DispatchWidths(o.workload.key_bytes,o.workload.value_bytes,[&](auto k,auto v) {
    if (noexcept_hash) f(Tag<StdUnorderedMapBackend<k(),v(),true>>{});
    else f(Tag<StdUnorderedMapBackend<k(),v(),false>>{});
  });
}

int RunStdUnorderedMap(const ob::WorkerOptions& o) {
  // The one knob: whether the hash is noexcept (no cached hash per node).
  bool noexcept_hash=false;
  for (const auto& [name,value]:o.overrides) {
    ob::Require(name=="unordered_map.hash_noexcept",
                "std_unordered_map: the only override is unordered_map.hash_noexcept");
    ob::Require(value=="true" || value=="false","std_unordered_map: hash_noexcept is true or false");
    noexcept_hash=value=="true";
  }
  uint64_t modeled=0, buckets=0;
  ob::Require(DispatchUnorderedMap(o,noexcept_hash,[&](auto tag) {
    using Backend=typename decltype(tag)::type;
    modeled=Backend::ModeledBytes(o.capacity);
    buckets=Backend::Buckets(o.capacity);
  }),"std_unordered_map: key or value width outside the campaign's instantiated widths");
  const auto slots=ob::baseline::ChooseSlots(o,1,false);
  ob::baseline::Envelope e;
  e.scheme="std_unordered_map"; e.policy_identity="baseline_std_unordered_map_v1";
  e.actual_capacity=o.capacity; e.modeled_buffer_bytes=modeled; e.library_threads=1;
  const char* layout=o.workload.key_layout==ob::KeyLayout::kDense ? "dense" : "permuted";
  std::ostringstream key;
  key << "std_unordered_map;k=" << o.workload.key_bytes << ";v=" << o.workload.value_bytes
      << ";reserve=" << o.capacity << ";key_layout=" << layout;
  if (noexcept_hash) key << ";hash_noexcept=1";
#ifdef __GLIBCXX__
  key << ";libstdc++=" << __GLIBCXX__;
#endif
  e.configuration_key=key.str();
  e.choices={{"scheme","std_unordered_map","explicit","requested baseline"},
             {"hash_noexcept",noexcept_hash ? "true" : "false",noexcept_hash ? "explicit" : "derived",
              noexcept_hash ? "requested override: no cached hash per node" : "default: libstdc++ caches each node's hash"},
             {"reserve",std::to_string(o.capacity),"derived","requested capacity, before the fill"},
             {"buckets",std::to_string(buckets),"derived","reserve(capacity) at the default maximum load factor (1.0)"}};
  const auto resolved=ob::baseline::EnvelopeJson(o,e,slots);
  if (o.resolve_only) { std::cout << resolved << '\n'; return 0; }
  ob::WorkerArtifacts artifacts(o,resolved);
  std::unique_ptr<ob::VerifiedPlacement> placement;
  ob::HarnessThreadInit harness_init;
  struct Role { int role; unsigned index; std::optional<unsigned> cpu; };
  std::vector<Role> expected;
  if (slots.placed()) {
    placement=std::make_unique<ob::VerifiedPlacement>(slots.topology,slots.cpus,ob::LinuxAffinity());
    placement->Bind(Role{0,0,slots.cpus[0]});
    harness_init=[&](ob::HarnessThread thread) { placement->Bind(Role{int(thread),0,slots.harness()}); };
    expected={{0,0,slots.cpus[0]},{int(ob::HarnessThread::kTelemetry),0,slots.harness()}};
    if (ob::RunsCheckpointThread(o)) expected.push_back({int(ob::HarnessThread::kCheckpoint),0,slots.harness()});
  }
  int result=0;
  DispatchUnorderedMap(o,noexcept_hash,[&](auto tag) {
    typename decltype(tag)::type backend(o.capacity);
    result=ob::ExecuteWorker(o,backend,artifacts,harness_init);
  });
  if (placement) {
    placement->VerifyComplete(expected);
    std::ostringstream out;
    out << "{\"placement_schema_version\":1,\"all_planned_roles_verified\":true,\"placement_policy\":"
        << ob::JsonQuote(slots.policy) << ",\"physical_host_topology_verified\":false,\"observations\":[";
    bool first=true;
    for (const auto& record:placement->Snapshot()) {
      out << (first ? "" : ",") << "{\"role\":" << record.role << ",\"index\":" << record.index
          << ",\"cpu\":" << record.cpu << '}';
      first=false;
    }
    out << "]}\n";
    artifacts.Write("placement.json",out.str());
  }
  return result;
}
api::Scheme Scheme(const std::string& value) {
  if (value=="auto") return api::Scheme::kAuto;
  if (value=="hierarchical_incremental") return api::Scheme::kHierarchicalIncremental;
  if (value=="hierarchical_synchronous") return api::Scheme::kHierarchicalSynchronous;
  if (value=="tree") return api::Scheme::kTree;
  throw std::invalid_argument("unknown scheme");
}
const char* SchemeName(api::Scheme scheme) {
  switch (scheme) {
    case api::Scheme::kAuto: return "auto";
    case api::Scheme::kHierarchicalIncremental: return "hierarchical_incremental";
    case api::Scheme::kHierarchicalSynchronous: return "hierarchical_synchronous";
    case api::Scheme::kTree: return "tree";
  }
  throw std::logic_error("invalid scheme");
}
template <class T> T Parse(const std::string& value) {
  if constexpr (std::is_same_v<T,bool>) {
    ob::Require(value=="true" || value=="false" || value=="0" || value=="1","invalid boolean override");
    return value=="true" || value=="1";
  } else if constexpr (std::is_same_v<T,api::BatchExecutionShape>) {
    ob::Require(value=="chunked_cascade" || value=="parallel_tiles","invalid batch execution shape");
    return value=="parallel_tiles" ? api::BatchExecutionShape::kParallelTiles : api::BatchExecutionShape::kChunkedCascade;
  } else if constexpr (std::is_same_v<T,api::BatchResultLayout>) {
    ob::Require(value=="rows" || value=="sliced_place_at_lane","invalid batch result layout");
    return value=="rows" ? api::BatchResultLayout::kRows : api::BatchResultLayout::kSlicedPlaceAtLane;
  } else if constexpr (std::is_same_v<T,api::BankFirst>) {
    ob::Require(value=="off" || value=="no_clone","invalid bank_first layout");
    return value=="off" ? api::BankFirst::kOff : api::BankFirst::kNoClone;
  } else if constexpr (std::is_same_v<T,std::vector<microram::byteslice::levelarena::LevelGroupPlan>>) {
    // "first-last,first-last,...", highest group first; the resolver checks coverage.
    T groups; std::istringstream input(value); std::string group;
    while (std::getline(input,group,',')) {
      const auto dash=group.find('-');
      ob::Require(dash!=std::string::npos,"level group must be first-last");
      groups.push_back({Parse<unsigned>(group.substr(0,dash)),Parse<unsigned>(group.substr(dash+1))});
    }
    ob::Require(!groups.empty() && value.back()!=',',"empty level group list");
    return groups;
  } else {
    const auto result=ob::Integer(value);
    ob::Require(result<=std::numeric_limits<T>::max(),"override exceeds destination integer width");
    return static_cast<T>(result);
  }
}
template <class T> void Assign(std::optional<T>& field,const std::string& value) { field=Parse<T>(value); }
template <class T> T& Block(std::optional<T>& field) { if (!field) field.emplace(); return *field; }
// The arena fields, shared by the incremental and synchronous blocks (top-level
// or a tree's position map).
template <class B> bool Arena(B& b,const std::string& f,const std::string& v) {
#define CPU_ORAM_FIELD(name) if (f==#name) { Assign(b.name,v); return true; }
  CPU_ORAM_FIELD(branching_factor) CPU_ORAM_FIELD(online_stash_entries) CPU_ORAM_FIELD(prefix_flushes)
  CPU_ORAM_FIELD(top_digit) CPU_ORAM_FIELD(dense_prefixes) CPU_ORAM_FIELD(half_fanout_prefix)
  CPU_ORAM_FIELD(tier_buckets) CPU_ORAM_FIELD(bank_first) CPU_ORAM_FIELD(batch_lanes)
  CPU_ORAM_FIELD(batch_execution) CPU_ORAM_FIELD(batch_participants) CPU_ORAM_FIELD(batch_bucket_scan)
  CPU_ORAM_FIELD(batch_profile) CPU_ORAM_FIELD(batch_result_layout) CPU_ORAM_FIELD(batch_spin_ns)
  CPU_ORAM_FIELD(wait_limit_ms)
  return false;
}
bool Incremental(api::IncrementalOverrides& b,const std::string& f,const std::string& v) {
  if (Arena(b,f,v)) return true;
  CPU_ORAM_FIELD(owner_threads) CPU_ORAM_FIELD(rebuild_threads)
  CPU_ORAM_FIELD(level_groups) CPU_ORAM_FIELD(top_helpers)
  CPU_ORAM_FIELD(bottom_helpers) CPU_ORAM_FIELD(rebuild_lanes)
  CPU_ORAM_FIELD(lane_min_buckets) CPU_ORAM_FIELD(slice_target_rate) CPU_ORAM_FIELD(slice_touches)
  CPU_ORAM_FIELD(inline_work_factor_ppm) CPU_ORAM_FIELD(time_rebuild_stages)
  CPU_ORAM_FIELD(near_max_level) CPU_ORAM_FIELD(owner_spin_ns)
  CPU_ORAM_FIELD(park_retry_us)
  CPU_ORAM_FIELD(rebuild_cost_line_picos) CPU_ORAM_FIELD(rebuild_cost_residual_line_picos)
  CPU_ORAM_FIELD(rebuild_cost_offer_line_picos) CPU_ORAM_FIELD(rebuild_cost_job_nanos)
  CPU_ORAM_FIELD(rebuild_cost_middle_burst_ppm) CPU_ORAM_FIELD(rebuild_cost_helper_speedup_ppm)
  CPU_ORAM_FIELD(rebuild_cost_max_top_threads) CPU_ORAM_FIELD(rebuild_cost_thread_gain_floor_ppm)
  CPU_ORAM_FIELD(rebuild_cost_probe_bucket_picos) CPU_ORAM_FIELD(rebuild_cost_probe_line_picos)
  CPU_ORAM_FIELD(rebuild_cost_slice_line_picos)
  return false;
}
bool Tree(api::TreeOverrides& b,const std::string& f,const std::string& v) {
  CPU_ORAM_FIELD(fold) CPU_ORAM_FIELD(leaf_scale) CPU_ORAM_FIELD(max_load_ppm)
  CPU_ORAM_FIELD(stash_registers) CPU_ORAM_FIELD(max_folded_slots)
  CPU_ORAM_FIELD(prefetch_ahead) CPU_ORAM_FIELD(uid_from_key) CPU_ORAM_FIELD(payload_max_threads)
  CPU_ORAM_FIELD(payload_threshold) CPU_ORAM_FIELD(payload_spin_us) CPU_ORAM_FIELD(payload_monitor_wait)
  CPU_ORAM_FIELD(payload_near)
#undef CPU_ORAM_FIELD
  return false;
}
api::OptionOverrides Overrides(const ob::WorkerOptions& o) {
  api::OptionOverrides result; result.scheme=Scheme(o.scheme);
  for (const auto& entry:o.overrides) {
    const auto& name=entry.first; const auto& value=entry.second;
    auto under=[&](const char* prefix,std::string& field) {
      if (name.rfind(prefix,0)!=0) return false;
      field=name.substr(std::strlen(prefix)); return true;
    };
    std::string f;
    if (name=="tree.position_map.mode") { Block(result.tree).position_map.mode=Scheme(value); continue; }
    if (under("tree.position_map.incremental.",f) &&
        Incremental(Block(Block(result.tree).position_map.incremental),f,value)) continue;
    if (under("tree.position_map.synchronous.",f) &&
        Arena(Block(Block(result.tree).position_map.synchronous),f,value)) continue;
    if (under("incremental.",f) && Incremental(Block(result.incremental),f,value)) continue;
    if (under("synchronous.",f) && Arena(Block(result.synchronous),f,value)) continue;
    if (under("tree.",f) && Tree(Block(result.tree),f,value)) continue;
    throw std::invalid_argument("unknown override: "+name);
  }
  return result;
}
std::string PlanJson(const api::ResolvedPlan& p, const ob::WorkerOptions& options) {
  std::ostringstream out;
  out << "{\"worker_schema_version\":2,\"resolver_request\":" << ob::ResolverRequestJson(options)
      << ",\"scheme\":" << ob::JsonQuote(SchemeName(p.scheme()))
      << ",\"requested_capacity\":" << p.spec().requested_capacity
      << ",\"actual_capacity\":" << p.actual_capacity()
      << ",\"policy_identity\":" << ob::JsonQuote(p.policy_id())
      << ",\"configuration_key\":" << ob::JsonQuote(p.configuration_key()+
          (options.workload.key_layout==ob::KeyLayout::kDense ? ";key_layout=dense" : ""))
      << ",\"supports_direct_initialization\":" << (p.capabilities().direct_initialization ? "true" : "false")
      << ",\"modeled_buffer_bytes\":"
      << p.modeled_buffer_bytes()
      << ",\"modeled_reserved_bytes\":" << p.modeled_reserved_bytes()
      << ",\"memory_components\":[";
  for (size_t i=0;i<p.memory_components().size();++i) {
    const auto& m=p.memory_components()[i];
    out << (i ? "," : "") << "{\"component\":" << ob::JsonQuote(m.component)
        << ",\"requested_bytes\":" << m.requested_bytes
        << ",\"coverage\":" << ob::JsonQuote(api::MemoryCoverageName(m.coverage)) << '}';
  }
  out << "],\"carry_period_accesses\":[";
  for (size_t i=0;i<p.carry_period_accesses().size();++i)
    out << (i ? "," : "") << p.carry_period_accesses()[i];
  out << "],\"choices\":[";
  bool first=true;
  for (const auto& c:p.choices()) {
    if (!first) out << ','; first=false;
    const char* source=c.source==api::ChoiceSource::kExplicit ? "explicit" :
        c.source==api::ChoiceSource::kFallback ? "fallback" : "derived";
    out << "{\"field\":" << ob::JsonQuote(c.field) << ",\"value\":" << ob::JsonQuote(c.value)
        << ",\"source\":" << ob::JsonQuote(source) << ",\"reason\":" << ob::JsonQuote(c.reason) << '}';
  }
  out << "],\"library_threads\":" << p.threads().size()
      << ",\"reserved_harness_cores\":1,\"placement_verified\":false,\"threads\":[";
  first=true;
  for (const auto& thread:p.threads()) {
    if (!first) out << ','; first=false;
    out << "{\"role\":" << static_cast<int>(thread.role) << ",\"index\":" << thread.index << ",\"cpu\":";
    if (thread.cpu) out << *thread.cpu; else out << "null";
    if (thread.near) out << ",\"near\":" << (*thread.near ? "true" : "false");
    out << '}';
  }
  out << "],\"placement_policy\":" << ob::JsonQuote(options.placement=="near_far" ? "near_far_v2" : options.placement)
      << ",\"cpu_slots\":[";
  for (size_t i=0;i<p.budget().cpu_ids.size();++i) {
    if (i) out << ',';
    out << p.budget().cpu_ids[i];
  }
  out << "]}";
  return out.str();
}
}  // namespace
int main(int argc,char** argv) {
  try {
    if (argc==1 || (argc==2 && std::string(argv[1])=="--help")) { ob::WorkerHelp(); return 0; }
    if (ob::PrintCompiledIsa(argc,argv)) return 0;
    if (ob::PrintClockCheck(argc,argv)) return 0;
    if (ob::baseline::PrintBuildInfo(argc,argv,"none","",{})) return 0;
    const auto o=ob::ParseWorker(argc,argv);
    if (ob::SyntheticScheme(o.scheme)) return ob::RunSyntheticWorker(o);
    if (o.scheme=="std_unordered_map") return RunStdUnorderedMap(o);
    api::MapSpec spec{o.capacity,o.workload.key_bytes,o.workload.value_bytes,o.max_accesses};
    api::ResourceBudget budget; budget.cores=o.cores; budget.harness_cores=1; budget.cpu_ids=o.cpu_ids;
    budget.cache_domains=o.cache_domains;
    budget.spin_before_park_ns=o.spin_before_park_ns;
    // The declaration is a public input; a CPU that does not offer it would
    // fall back to a futex park, so the run would not be the arm it claims.
    const auto offered=microram::core::DetectMonitorWait();
    if (o.monitor_wait!="none") {
      ob::Require(o.monitor_wait==microram::core::MonitorWaitKindName(offered),
                  "declared --monitor-wait differs from what this CPU offers");
      budget.monitor_wait=offered;
    }
    api::WorkloadHint hint;
    hint.api_mode=o.batched ? api::ApiMode::kBatch : api::ApiMode::kScalar;
    hint.expected_batch_size=o.trial.batch_size;
    const auto overrides=Overrides(o);
    auto plan=api::resolve_options(spec,budget,hint,overrides);
    std::vector<ob::topology::Cpu> topology_snapshot;
    // Resolve public roles first; topology discovery and slot selection never
    // construct a map, start helpers, change affinity, or read a timer.
    if (o.placement!="unplaced") topology_snapshot=ob::topology::Discover();
    if (o.placement=="near_far") {
      // The declared domains size the rebuild's near/far caps; placing them
      // on a host with other domains would put a side on the wrong cores.
      if (o.cache_domains>1) {
        std::set<std::string> domains;
        for (const auto& cpu:topology_snapshot) domains.insert(cpu.l3);
        ob::Require(domains.size()==o.cache_domains,"exposed L3 domains differ from --cache-domains");
      }
      std::vector<ob::PlacementLocality> roles;
      for (const auto& thread:plan.threads()) {
        switch (thread.role) {
          case api::ThreadRole::kCaller: roles.push_back(ob::PlacementLocality::kCaller); break;
          case api::ThreadRole::kOnlineHelper:
          case api::ThreadRole::kPositionOnlineHelper:
            roles.push_back(ob::PlacementLocality::kOnline); break;
          // Rebuild threads below an explicit near/far boundary want the caller's L3.
          default: roles.push_back(thread.near.value_or(false) ? ob::PlacementLocality::kOnline
                                                             : ob::PlacementLocality::kBackground); break;
        }
      }
      budget.cpu_ids=ob::NearFarSlots(topology_snapshot,roles,budget.cores,budget.harness_cores);
      // Slot assignment must not change fallback geometry/roles when rerunning
      // the pure resolver.
      auto placed=api::resolve_options(spec,budget,hint,overrides);
      ob::Require(placed.scheme()==plan.scheme() && placed.actual_capacity()==plan.actual_capacity() &&
                  placed.modeled_buffer_bytes()==plan.modeled_buffer_bytes() &&
                  placed.choices().size()==plan.choices().size() &&
                  placed.threads().size()==plan.threads().size(),"placement changed resolved configuration");
      for (size_t i=0;i<plan.choices().size();++i)
        ob::Require(placed.choices()[i].field==plan.choices()[i].field &&
                    placed.choices()[i].value==plan.choices()[i].value &&
                    placed.choices()[i].source==plan.choices()[i].source,
                    "placement changed resolved choices");
      for (size_t i=0;i<plan.threads().size();++i)
        ob::Require(placed.threads()[i].role==plan.threads()[i].role &&
                    placed.threads()[i].index==plan.threads()[i].index,"placement changed resolved roles");
      plan=std::move(placed);
    }
    if (!budget.cpu_ids.empty()) ob::topology::Resolve(topology_snapshot,budget.cpu_ids,{},{},true);
    const auto resolved=PlanJson(plan,o);
    if (o.resolve_only) { std::cout << resolved << '\n'; return 0; }
    // Freeze the resolved plan, then use the shared prepared trial path.
    ob::WorkerArtifacts artifacts(o,resolved);
    auto trial=o; trial.carry_periods=plan.carry_period_accesses();
    std::unique_ptr<ob::VerifiedPlacement> placement;
    api::ConstructionHooks hooks;
    ob::HarnessThreadInit harness_init;
    // Discovery precedes caller pinning, preserving the original allowed set.
    struct Role { int role; unsigned index; std::optional<unsigned> cpu; };
    std::vector<Role> expected;
    for (const auto& thread:plan.threads())
      expected.push_back({static_cast<int>(thread.role),thread.index,thread.cpu});
    if (!budget.cpu_ids.empty()) {
      placement=std::make_unique<ob::VerifiedPlacement>(topology_snapshot,budget.cpu_ids,ob::LinuxAffinity());
      hooks.thread_init=[&](const api::PlannedThread& thread) { placement->Bind(thread); };
      // The harness threads (negative roles) share the harness slot.
      const unsigned harness=budget.cpu_ids.back();
      expected.push_back({int(ob::HarnessThread::kTelemetry),0,harness});
      if (ob::RunsCheckpointThread(trial)) expected.push_back({int(ob::HarnessThread::kCheckpoint),0,harness});
      harness_init=[&,harness](ob::HarnessThread thread) { placement->Bind(Role{int(thread),0,harness}); };
    }
    auto save_placement=[&](bool complete) {
      if (!placement) return;
      std::ostringstream out;
      out << "{\"placement_schema_version\":1,\"all_planned_roles_verified\":"
          << (complete ? "true" : "false") << ",\"placement_policy\":"
          << ob::JsonQuote(o.placement=="near_far" ? "near_far_v2" : o.placement)
          << ",\"physical_host_topology_verified\":false,\"observations\":[";
      bool first=true;
      for (const auto& record:placement->Snapshot()) {
        if (!first) out << ','; first=false;
        out << "{\"role\":" << record.role << ",\"index\":" << record.index << ",\"cpu\":" << record.cpu;
        auto mask=[&](const char* name,const std::vector<unsigned>& cpus) {
          out << ",\"" << name << "\":[";
          for (size_t i=0;i<cpus.size();++i) { if (i) out << ','; out << cpus[i]; }
          out << ']';
        };
        mask("inherited",record.inherited); mask("applied",record.applied); out << '}';
      }
      out << "],\"original_allowed_topology\":[";
      first=true;
      for (const auto& cpu:topology_snapshot) {
        if (!first) out << ','; first=false;
        out << "{\"cpu\":" << cpu.id << ",\"package\":" << cpu.package << ",\"core\":" << cpu.core
            << ",\"die\":" << (cpu.die<0 ? "null" : std::to_string(cpu.die))
            << ",\"numa\":" << (cpu.numa<0 ? "null" : std::to_string(cpu.numa)) << ",\"l3_shared_cpus\":" << ob::JsonQuote(cpu.l3)
            << ",\"thread_siblings\":" << ob::JsonQuote(cpu.siblings) << ",\"l3_bytes\":" << cpu.l3_bytes << '}';
      }
      out << "]}\n"; artifacts.Write("placement.json",out.str());
    };
    try {
      auto map=api::make_map(plan,hooks);
      // Pools started by construction; incremental owners start at the first
      // access, so only the final snapshot can cover them.
      save_placement(false);
      const int result=map.with_backend([&](auto& concrete) {
        ob::CpuBackend<std::decay_t<decltype(concrete)>> backend(concrete);
        return ob::ExecuteWorker(trial,backend,artifacts,harness_init);
      });
      if (placement) placement->VerifyComplete(expected);
      save_placement(true);
      return result;
    } catch (...) { save_placement(false); throw; }
  } catch (const std::exception& error) {
    std::cerr << "cpu_oram_benchmark: " << error.what() << '\n'; return 2;
  }
}
