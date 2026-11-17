// The configuration resolver of include/cpu_byteslice_oram/configuration.hpp:
// `resolve_options` turns a map specification (capacity, key and value
// widths), a resource budget (cores, memory, declared CPU capabilities) and
// optional explicit overrides into a ResolvedPlan -- scheme (hierarchical
// incremental, hierarchical synchronous, or tree), geometry, thread roles and
// a memory bill -- and `make_map` builds exactly that plan.
//
// What it checks:
//   * the automatic choices follow the library's default rule (the value-width
//     crossover between hierarchy and tree, the default geometry) at every
//     core budget, and default-constructed maps build what `auto` plans;
//   * explicit overrides win, are recorded as explicit, and pinning a plan's
//     answer replays the same geometry and memory bill;
//   * knobs that cannot take effect, or that contradict another knob, are
//     refused by name instead of silently ignored;
//   * memory budgets hold at their exact boundary for every scheme, and
//     geometry arithmetic that would overflow rejects a candidate instead of
//     aborting resolution;
//   * the rebuild thread budget is divided among owner and helper threads by
//     the library's heuristic, capped by declared cache domains and physical
//     cores, and real helper threads report the roles the plan assigned.
// Only plans and constructed maps are inspected; nothing is timed.

#include <cpu_byteslice_oram/configuration.hpp>
#include <cpu_byteslice_oram/oram.hpp>
#include "benchmarks/support/placement.hpp"

#include <array>
#include <atomic>
#include <cstdio>
#include <cstring>
#include <limits>
#include <mutex>
#include <set>
#include <thread>

namespace {
namespace o = cpu_byteslice_oram;
int failures = 0;
void Expect(bool value, const char* what) {
  if (!value) { std::fprintf(stderr, "FAIL: %s\n", what); ++failures; }
}
template <class F> void Reject(F&& fn, const char* what) {
  try { fn(); Expect(false, what); }
  catch (const std::invalid_argument&) {}
  catch (const std::length_error&) {}
}
o::OptionOverrides Pin(o::Scheme scheme) { o::OptionOverrides p; p.scheme = scheme; return p; }
const o::ResolvedChoice& Choice(const o::ResolvedPlan& plan, const char* field) {
  for (const auto& c : plan.choices()) if (c.field == field) return c;
  throw std::runtime_error(std::string("missing choice: ") + field);
}
std::string Signature(const o::ResolvedPlan& plan) {
  std::string s;
  for (const auto& choice : plan.choices()) s += choice.field + "=" + choice.value + ";";
  for (const auto& memory : plan.memory_components()) s += memory.component + "=" + std::to_string(memory.requested_bytes) + ";";
  return s;
}

void TestLegacyThreadAccounting() {
  o::Options options;
  options.deamortized_batch_participants = 3;
  options.deamortized_value_workers = 4;
  options.deamortized_owner_threads = 2;
  options.deamortized_top_helpers = 1;
  options.deamortized_bottom_helpers = 2;
  Expect(o::detail::ThreadsBesideCaller<true>(options) == 11,
         "tree payload budget reserves all position-map worker pools");
  Expect(o::detail::ThreadsBesideCaller<false>(options) == 6,
         "synchronous position-map value workers reserve cores too");
  options.deamortized_rebuild_threads = 7;
  Expect(o::detail::ThreadsBesideCaller<true>(options) == 13,
         "a rebuild budget replaces explicit owner and helper counts");

  options.deamortized_value_workers = std::numeric_limits<unsigned>::max();
  Expect(o::detail::ThreadsBesideCaller<true>(options) ==
             std::numeric_limits<unsigned>::max() &&
             o::detail::ThreadsBesideCaller<false>(options) ==
             std::numeric_limits<unsigned>::max(),
         "excessive thread requests cannot wrap the core reservation");

  // Test helper clamping without creating workers. Reserving every host core
  // for value workers must leave no room for top or bottom helpers.
  options = {};
  options.deamortized_owner_threads = 1;
  const auto geometry = o::ByteMap<>::plan_geometry(128, 8, 16, options);
  options.deamortized_value_workers = microram::byteslice::HostPhysicalCores();
  options.deamortized_top_helpers = 2;
  options.deamortized_bottom_helpers = 2;
  const auto engine_options =
      o::detail::ArenaEngineOptions(geometry, 8, 16, options);
  Expect(engine_options.top_helpers == 0 && engine_options.bottom_helpers == 0,
         "value workers consume the cores available to rebuild helpers");
}

void TestResolution() {
  const o::MapSpec spec{128, 4, 8};
  auto p = o::resolve_options(spec, {1});
  Expect(p.scheme() == o::Scheme::kHierarchicalIncremental, "small-value auto fallback");
  Expect(p.threads().size() == 1, "one-core fallback has no hidden helper pools");
  Expect(p.capabilities().direct_initialization, "hierarchy direct fill capability");
  auto explicit_options = Pin(o::Scheme::kHierarchicalIncremental);
  explicit_options.incremental.emplace();
  explicit_options.incremental->owner_threads = 0;
  explicit_options.incremental->half_fanout_prefix = false;
  explicit_options.incremental->batch_spin_ns = 0;
  auto e = o::resolve_options(spec, {4}, {}, explicit_options);
  Expect(Choice(e, "hierarchy.owner_threads").source == o::ChoiceSource::kExplicit, "explicit zero provenance");
  Expect(Choice(e, "hierarchy.half_fanout_prefix").value == "false", "explicit false retained");
  Expect(Choice(e, "hierarchy.batch_spin_ns").value == "0", "zero spin retained");
  Expect(e.threads().size() == 1, "explicit inline beats extra available cores");
  Expect(Choice(e, "hierarchy.prefix_flushes").value != "0", "geometry search resolved to concrete flushes");
  Expect(Choice(e, "hierarchy.tier_buckets").value == "1" &&
             Choice(e, "hierarchy.tier_buckets").source == o::ChoiceSource::kDerived,
         "automatic tier width is concrete in the public plan");
  auto large_tiers = explicit_options;
  large_tiers.incremental->branching_factor = 8;
  large_tiers.incremental->prefix_flushes = 8;
  large_tiers.incremental->top_digit = 8;
  const auto large_plan = o::resolve_options({size_t{1} << 27, 8, 16},
                                            {1}, {}, large_tiers);
  Expect(Choice(large_plan, "hierarchy.tier_buckets").value == "2",
         "large public plan retained an insufficient default tier");
  large_tiers.incremental->tier_buckets = 1;
  Reject([&] { o::resolve_options({size_t{1} << 27, 8, 16},
                                  {1}, {}, large_tiers); },
         "large public plan accepted an undersized explicit tier");
  large_tiers.incremental->tier_buckets = 3;
  const auto wide_plan = o::resolve_options({size_t{1} << 27, 8, 16},
                                           {1}, {}, large_tiers);
  Expect(Choice(wide_plan, "hierarchy.tier_buckets").value == "3" &&
             Choice(wide_plan, "hierarchy.tier_buckets").source == o::ChoiceSource::kExplicit,
         "adequate explicit tier width lost its value or provenance");
  Expect(Signature(e) == Signature(o::resolve_options(spec, {4}, {}, explicit_options)), "deterministic resolved choices");
  auto changed_policy = microram::byteslice::CurrentHugePagePolicy();
  microram::byteslice::SetHugePagePolicy(microram::byteslice::HugePagePolicy::kOff);
  auto off = o::resolve_options({32768, 8, 48}, {4}, {}, explicit_options);
  microram::byteslice::SetHugePagePolicy(microram::byteslice::HugePagePolicy::kOn);
  auto on = o::resolve_options({32768, 8, 48}, {4}, {}, explicit_options);
  microram::byteslice::SetHugePagePolicy(changed_policy);
  Expect(Signature(off) == Signature(on), "allocator rounding does not affect public resolution");

  o::ResourceBudget memory{4};
  memory.modeled_buffer_limit_bytes = e.modeled_buffer_bytes();
  Expect(o::resolve_options(spec, memory, {}, explicit_options).modeled_buffer_bytes() == *memory.modeled_buffer_limit_bytes,
         "exact modeled buffer budget accepted");
  --*memory.modeled_buffer_limit_bytes;
  Reject([&] { o::resolve_options(spec, memory, {}, explicit_options); }, "modeled buffer budget boundary");
  // The synchronous hierarchy's figure is a complete bill of what it
  // allocates too, so the same budget holds for it at the same boundary.
  {
    o::OptionOverrides sync;
    sync.scheme = o::Scheme::kHierarchicalSynchronous;
    const auto planned = o::resolve_options(spec, {4}, {}, sync);
    o::ResourceBudget limit{4};
    limit.modeled_buffer_limit_bytes = planned.modeled_buffer_bytes();
    Expect(o::resolve_options(spec, limit, {}, sync).modeled_buffer_bytes() == planned.modeled_buffer_bytes(),
           "exact synchronous buffer budget accepted");
    --*limit.modeled_buffer_limit_bytes;
    Reject([&] { o::resolve_options(spec, limit, {}, sync); }, "synchronous buffer budget boundary");
    for (const auto& component : planned.memory_components())
      Expect(component.coverage == o::MemoryCoverage::kTallied, "synchronous components are tallied");
  }
  auto small = o::resolve_options({128, 8, 256}, {1});
  auto parallel = o::resolve_options({128, 8, 256}, {4});
  // The 96-byte crossover does not move with the core budget.
  Expect(small.scheme() == o::Scheme::kTree && parallel.scheme() == o::Scheme::kTree &&
             parallel.payload_workers() == 3,
         "the crossover is the same at every core budget");
  Expect(o::resolve_options({128, 8, 64}, {1}).scheme() == o::Scheme::kHierarchicalIncremental,
         "below the crossover the hierarchy");
  Expect(o::resolve_options({128, 8, 95}, {4}).scheme() == o::Scheme::kHierarchicalIncremental &&
             o::resolve_options({128, 8, 96}, {4}).scheme() == o::Scheme::kTree,
         "the crossover is at 96 bytes");
  Expect(o::resolve_options({128, 32, 1024}, {1}).scheme() == o::Scheme::kTree, "wide-value one-core tree fallback");
  // Auto stands in for the default hybrid map, so an auto-selected tree takes
  // the hybrid's payload spin; a pinned tree keeps the tree engine's default.
  Expect(Choice(parallel, "tree.payload_spin_us").value == std::to_string(o::kHybridTreePayloadSpinMicros) &&
         Choice(parallel, "tree.payload_spin_us").source == o::ChoiceSource::kDerived,
         "auto-selected tree uses the hybrid payload spin");
  auto pinned_tree = o::resolve_options({128, 8, 256}, {4}, {}, Pin(o::Scheme::kTree));
  Expect(Choice(pinned_tree, "tree.payload_spin_us").value == "200", "pinned tree keeps the tree spin default");
  Expect(pinned_tree.configuration_key() != parallel.configuration_key(), "auto and pinned tree are distinct configurations");
  auto auto_spin = o::OptionOverrides{}; auto_spin.tree.emplace(); auto_spin.tree->payload_spin_us = 50;
  Expect(Choice(o::resolve_options({128, 8, 256}, {4}, {}, auto_spin), "tree.payload_spin_us").value == "50",
         "explicit spin wins on auto");
  auto auto_hierarchy = o::resolve_options({128, 4, 8}, {4});
  auto pinned_hierarchy = o::resolve_options({128, 4, 8}, {4}, {}, Pin(o::Scheme::kHierarchicalIncremental));
  Expect(auto_hierarchy.configuration_key() == pinned_hierarchy.configuration_key(),
         "auto selecting a pinned arm's configuration shares its key");
}

// An explicit knob that cannot take effect is rejected by name.
void TestIneffectiveKnobs() {
  const o::MapSpec spec{128, 4, 8};
  auto p = Pin(o::Scheme::kHierarchicalIncremental);
  p.incremental.emplace(); p.incremental->owner_threads = 0; p.incremental->near_max_level = 1;
  Reject([&] { o::resolve_options(spec, {4}, {}, p); }, "near boundary without owners");
  p.incremental->near_max_level.reset(); p.incremental->owner_spin_ns = 0;
  Reject([&] { o::resolve_options(spec, {4}, {}, p); }, "owner spin without owners");
  p.incremental->owner_threads = 1;
  Expect(Choice(o::resolve_options(spec, {4}, {}, p), "hierarchy.owner_spin_ns").value == "0",
         "owner spin with an owner is accepted");
  // The fallback spins are the library's own defaults, not a resolver choice.
  p.incremental->owner_spin_ns.reset();
  const auto spun = o::resolve_options(spec, {4}, {}, p);
  Expect(Choice(spun, "hierarchy.owner_spin_ns").value ==
             std::to_string(o::Options{}.deamortized_owner_spin_nanos) &&
         Choice(spun, "hierarchy.batch_spin_ns").value ==
             std::to_string(o::Options{}.deamortized_batch_spin_nanos),
         "the resolver's spin windows differ from the library's");
  auto tree = Pin(o::Scheme::kTree);
  tree.tree.emplace(); tree.tree->payload_max_threads = 0; tree.tree->payload_spin_us = 10;
  Reject([&] { o::resolve_options({128, 8, 256}, {4}, {}, tree); }, "payload spin without payload workers");
  tree.tree->payload_spin_us.reset(); tree.tree->payload_threshold = 64;
  Reject([&] { o::resolve_options({128, 8, 256}, {4}, {}, tree); }, "payload threshold with zero cap");
  auto helpers = Pin(o::Scheme::kHierarchicalIncremental);
  helpers.incremental.emplace(); helpers.incremental->batch_participants = 2;
  o::WorkloadHint batch; batch.api_mode = o::ApiMode::kBatch; batch.expected_batch_size = 64;
  Expect(Choice(o::resolve_options(spec, {4}, batch, helpers), "hierarchy.batch_execution").source ==
         o::ChoiceSource::kDerived, "tiles forced by helpers are derived, not fallback");
}

// Checked geometry arithmetic that overflows rejects that candidate
// instead of aborting auto resolution.
void TestOverflowCandidate() {
  try {
    (void)o::resolve_options({size_t{1} << 34, 8, size_t{1} << 30}, {4});
  } catch (const std::overflow_error&) {
    Expect(false, "candidate overflow aborted auto resolution");
  } catch (const std::invalid_argument&) {  // no eligible candidate is a valid answer
  } catch (const std::length_error&) {
  }
}

void TestInvalidInputs() {
  const o::MapSpec spec{128, 4, 8};
  Reject([&] { o::resolve_options({0,4,8}, {1}); }, "zero capacity");
  Reject([&] { o::resolve_options({128,0,8}, {1}); }, "zero key width");
  Reject([&] { o::resolve_options({128,4,0}, {1}); }, "zero value width");
  Reject([&] { o::resolve_options({128,4,8,0}, {1}); }, "zero horizon");
  Reject([&] { o::resolve_options(spec, {0}); }, "zero cores");
  Reject([&] { o::resolve_options(spec, {2,2}); }, "harness consumes all cores");
  Reject([&] { o::resolve_options(spec, {2,0,{7,7}}); }, "duplicate CPU IDs");
  Reject([&] { o::resolve_options(spec, {2,0,{7}}); }, "CPU slots cannot prove declared budget");
  o::WorkloadHint hint; hint.expected_batch_size = 16;
  Reject([&] { o::resolve_options(spec, {1}, hint); }, "scalar caller batch must be one");
  hint.expected_batch_size = 1;
  o::resolve_options(spec, {1}, hint);
  auto p = Pin(o::Scheme::kTree); p.incremental.emplace();
  Reject([&] { o::resolve_options(spec, {4}, {}, p); }, "irrelevant pinned overrides");
  p = Pin(o::Scheme::kHierarchicalIncremental); p.incremental.emplace();
  p.incremental->batch_participants = 2; p.incremental->batch_execution = o::BatchExecutionShape::kChunkedCascade;
  Reject([&] { o::resolve_options(spec, {4}, {}, p); }, "chunked helper conflict");
  p.incremental = o::IncrementalOverrides{}; p.incremental->prefix_flushes = 0;
  Reject([&] { o::resolve_options(spec, {4}, {}, p); }, "explicit legacy zero sentinel");
  p.incremental = o::IncrementalOverrides{}; p.incremental->owner_threads = 4;
  Reject([&] { o::resolve_options(spec, {4}, {}, p); }, "caller must also fit budget");
  p.incremental = o::IncrementalOverrides{}; p.incremental->batch_execution = static_cast<o::BatchExecutionShape>(99);
  Reject([&] { o::resolve_options(spec, {4}, {}, p); }, "invalid enum");
  p.incremental = o::IncrementalOverrides{}; p.incremental->near_max_level = o::kNearMaxLevelAuto;
  Reject([&] { o::resolve_options(spec, {4}, {}, p); }, "host discovery sentinel refused");
  {
    // The ranges every construction path shares, refused by name and as
    // std::invalid_argument rather than as a geometry the ladder missed.
    auto named = [](auto&& fn, const char* field, const char* what) {
      std::string message;
      try { fn(); } catch (const std::invalid_argument& e) { message = e.what(); } catch (...) {}
      Expect(message.find(field) != std::string::npos, what);
    };
    named([&] { o::resolve_options({128, 65, 8}, {4}); }, "key_bytes", "a 65-byte key resolved");
    for (o::Scheme scheme : {o::Scheme::kHierarchicalIncremental, o::Scheme::kHierarchicalSynchronous}) {
      auto q = Pin(scheme);
      auto& fields = scheme == o::Scheme::kHierarchicalIncremental ? q.incremental.emplace().online_stash_entries
                                                                    : q.synchronous.emplace().online_stash_entries;
      fields = size_t{64} << 13;
      named([&] { o::resolve_options(spec, {4}, {}, q); }, "deamortized_online_stash_entries",
            "an insertion unit above 2^12 buckets resolved");
    }
    auto q = Pin(o::Scheme::kHierarchicalIncremental); q.incremental.emplace();
    q.incremental->owner_threads = 1; q.incremental->rebuild_lanes = 0;
    named([&] { o::resolve_options(spec, {4}, {}, q); }, "deamortized_rebuild_lanes", "zero rebuild lanes resolved");
    q.incremental->rebuild_lanes.reset(); q.incremental->wait_limit_ms = 0;
    named([&] { o::resolve_options(spec, {4}, {}, q); }, "deamortized_wait_limit_millis", "zero wait limit resolved");
  }
  p = Pin(o::Scheme::kTree); p.tree.emplace(); p.tree->uid_from_key = true;
  Reject([&] { o::resolve_options({128,32,48}, {4}, {}, p); }, "explicit wide-key UID must not be ignored");
  p.tree = o::TreeOverrides{}; p.tree->stash_registers = 2;
  Reject([&] { o::resolve_options(spec, {4}, {}, p); }, "unsupported stash width");
  p.tree = o::TreeOverrides{}; p.tree->max_load_ppm = 750000;
  Reject([&] { o::resolve_options(spec, {4}, {}, p); }, "unsupported load policy");
  p.tree = o::TreeOverrides{}; p.tree->max_folded_slots = 256;
  Reject([&] { o::resolve_options(spec, {4}, {}, p); }, "fold budget past the stash lanes");
  p.tree = o::TreeOverrides{}; p.tree->payload_monitor_wait = true;
  Reject([&] { o::resolve_options(spec, {4}, {}, p); }, "monitor wait requires a declared capability");
  {
    // A declared capability is a public input, so this resolves on
    // any host and names the instruction it was promised.
    o::ResourceBudget waits{4}; waits.monitor_wait = microram::core::MonitorWaitKind::kUmwait;
    const auto plan = o::resolve_options({4096,8,1024}, waits, {}, p);
    Expect(Choice(plan, "tree.payload_monitor_wait_kind").value == "umwait", "declared monitor-wait kind recorded");
    auto q = Pin(o::Scheme::kHierarchicalIncremental); q.incremental.emplace();
    q.incremental->value_workers = 1; q.incremental->value_monitor_wait = true;
    Reject([&] { o::resolve_options(spec, {4}, {}, q); }, "value monitor wait requires a declared capability");
    waits.monitor_wait = microram::core::MonitorWaitKind::kMwaitx;
    Expect(Choice(o::resolve_options(spec, waits, {}, q), "hierarchy.value_monitor_wait_kind").value == "mwaitx",
           "declared value monitor-wait kind recorded");
  }
  {
    // payload_near marks only the payload workers near and is
    // recorded; without payload workers it is refused as ineffective.
    auto q = Pin(o::Scheme::kTree); q.tree.emplace(); q.tree->payload_near = true;
    const auto plan = o::resolve_options({4096,8,1024}, {8}, {}, q);
    const auto base = o::resolve_options({4096,8,1024}, {8}, {}, Pin(o::Scheme::kTree));
    Expect(plan.payload_workers() > 0 && plan.threads().size() == base.threads().size(), "payload_near keeps roles");
    for (size_t i = 0; i < plan.threads().size(); ++i)
      Expect(plan.threads()[i].near == (plan.threads()[i].role == o::ThreadRole::kPayload
                                            ? std::optional<bool>(true) : base.threads()[i].near),
             "payload_near marks payload workers near and nothing else");
    Expect(Choice(plan, "tree.payload_near").value == "true" &&
           Choice(plan, "tree.payload_near").source == o::ChoiceSource::kExplicit, "payload_near recorded");
    q.tree->payload_max_threads = 0;
    Reject([&] { o::resolve_options({4096,8,1024}, {8}, {}, q); }, "payload_near needs payload workers");
  }
  Reject([&] { o::resolve_options({128,8,1024,uint64_t{1}<<33}, {4}, {}, Pin(o::Scheme::kTree)); },
         "tree horizon cannot silently extend security policy");
  p = {}; p.incremental.emplace(); p.incremental->owner_threads = 100;
  auto fallback = o::resolve_options(spec, {1}, {}, p);
  Expect(!fallback.rejected_candidates().empty(), "auto preserves candidate rejection reasons");
}

void TestNestedBudget() {
  auto p = Pin(o::Scheme::kTree); p.tree.emplace();
  p.tree->payload_max_threads = 2;
  p.tree->position_map.incremental.emplace();
  p.tree->position_map.incremental->owner_threads = 2;
  p.tree->position_map.incremental->batch_participants = 2;
  Reject([&] { o::resolve_options({128,8,1024}, {5}, {}, p); }, "nested helpers plus caller exceed five cores");
  auto fit = o::resolve_options({128,8,1024}, {7,1}, {}, p);
  Expect(fit.threads().size() == 6 && fit.payload_workers() == 2, "all nested pools plus caller fit library six");
  p.tree->position_map.mode = o::Scheme::kHierarchicalSynchronous;
  p.tree->position_map.incremental.reset(); p.tree->position_map.synchronous.emplace();
  p.tree->position_map.synchronous->batch_participants = 3;
  auto sync = o::resolve_options({128,8,1024}, {5}, {}, p);
  Expect(sync.threads().size() == 5, "synchronous position-map count includes shared caller");
  Expect(sync.capabilities().batch_position_map, "synchronous position map batches");

}

void TestPlanningBoundaries() {
  for (size_t n : {size_t{1}, size_t{127}, size_t{128}, size_t{129}, size_t{257}, size_t{1024}, size_t{1} << 20}) {
    for (auto widths : {std::pair<size_t,size_t>{4,8}, {8,48}, {32,1024}}) {
      for (auto scheme : {o::Scheme::kAuto, o::Scheme::kHierarchicalIncremental,
                          o::Scheme::kHierarchicalSynchronous, o::Scheme::kTree}) {
        for (unsigned cores : {1u, 6u}) {
          const auto p = o::resolve_options({n,widths.first,widths.second}, {cores}, {}, Pin(scheme));
          Expect(p.actual_capacity() >= n, "capacity boundary covered");
          Expect(p.threads().size() <= cores, "boundary plan inside total core budget");
          size_t bytes = 0;
          for (const auto& component : p.memory_components()) bytes += component.requested_bytes;
          Expect(bytes == p.modeled_buffer_bytes(), "component totals reconcile at planning boundaries");
          std::set<std::string> names;
          for (const auto& choice : p.choices()) Expect(names.insert(choice.field).second, "unique provenance fields");
          // Every plan carries the certification report, map-level and under
          // its hierarchy's prefix, and flags rather than refuses.
          const std::string prefix = p.scheme() == o::Scheme::kTree ? "position_map." : "hierarchy.";
          for (const std::string& f : {std::string(), prefix}) {
            Expect(names.count(f + "certification") && names.count(f + "failure_bound_log2"),
                   "certification report in the choices");
            if (!names.count(f + "certification")) continue;
            const auto& c = Choice(p, (f + "certification").c_str());
            Expect(c.value == "certified" || c.value == "above_target" || c.value == "not_covered",
                   "certification status is one of three");
            Expect(!c.reason.empty(), "certification status carries a reason");
          }
          Expect(p.certification().status == p.hierarchy_certification().status ||
                     p.scheme() != o::Scheme::kHierarchicalIncremental,
                 "an incremental map's certification is its hierarchy's");
        }
      }
    }
  }
  // One worker per started 32 value bytes from 32 on, capped by the budget's three.
  for (size_t width : {31u,32u,33u,63u,64u,65u,95u,96u,97u,256u,1024u}) {
    auto plan = o::resolve_options({129,8,width}, {4}, {}, Pin(o::Scheme::kTree));
    Expect(plan.payload_workers() == std::min(size_t{3}, width < 32 ? 0 : (width + 31) / 32),
           "payload threshold boundary");
  }
}

struct Records {
  std::vector<uint8_t> key, value;
  size_t index = 0;
  Records(size_t k, size_t v) : key(k), value(v) {}
  o::InitializationEntry operator*() {
    std::fill(key.begin(), key.end(), 0); key[0] = static_cast<uint8_t>(index);
    std::fill(value.begin(), value.end(), static_cast<uint8_t>(index + 1));
    return {key.data(), value.data()};
  }
  Records& operator++() { ++index; return *this; }
};

void CheckMap(const o::ResolvedPlan& plan, o::ConstructionHooks hooks = {}) {
  auto map = o::make_map(plan, hooks);
  Expect(map.capacity() == plan.actual_capacity(), "construction agrees with plan");
  const auto k = map.key_bytes(), v = map.value_bytes();
  Records records(k, v);
  if (map.supports_direct_initialization()) map.initialize(records, 16);
  else {
    Reject([&] { map.initialize(records, 16); }, "tree does not falsely advertise direct initialize");
    for (unsigned i = 0; i < 16; ++i, ++records) {
      auto record = *records; map.insert_or_assign(record.key, record.value);
    }
  }
  std::vector<uint8_t> key(k), value(v), old(v), output(v);
  for (unsigned i = 0; i < 16; ++i) {
    key[0] = i;
    Expect(map.find(key.data(), output.data()), "fill find membership");
    Expect(std::all_of(output.begin(), output.end(), [i](uint8_t b) { return b == i + 1; }), "full-width value check");
  }
  key[0] = 7; std::fill(value.begin(), value.end(), 91);
  // The repeated key must observe the preceding write in request order.
  std::array<o::BatchRequest,3> requests{};
  requests[0].op = o::BatchOp::kRead; requests[0].key = key.data(); requests[0].value_out = old.data();
  requests[1].op = o::BatchOp::kWrite; requests[1].key = key.data(); requests[1].value_in = value.data();
  requests[2].op = o::BatchOp::kRead; requests[2].key = key.data(); requests[2].value_out = output.data();
  std::array<uint8_t,3> found{};
  map.access_batch(requests.size(), requests.data(), found.data());
  Expect(found[0] && found[1] && found[2], "repeated-key batch membership");
  Expect(old[0] == 8 && output == value, "repeated-key batch ordering and full payload");
  map.finish_pending_work();
  Expect(map.exchange(key.data(), old.data(), output.data(), false) && output == value, "exchange old value");
  Expect(map.erase(key.data(), output.data()) && output == old, "erase old value");
  Expect(!map.contains(key.data()), "erase membership");
  map.finish_pending_work(); map.finish_pending_work();
}

void TestRealEngines() {
  for (const auto widths : {std::pair<size_t,size_t>{4,8}, {8,48}, {32,1024}}) {
    for (auto scheme : {o::Scheme::kHierarchicalIncremental, o::Scheme::kHierarchicalSynchronous, o::Scheme::kTree}) {
      auto p = Pin(scheme);
      // Keep correctness fixtures small; binary sync's minimum ladder is smaller.
      if (scheme == o::Scheme::kHierarchicalSynchronous) { p.synchronous.emplace(); p.synchronous->branching_factor = 2; }
      auto resolved = o::resolve_options({128,widths.first,widths.second}, {1}, {}, p);
      CheckMap(resolved);
      auto replay = o::make_map(resolved);
      Expect(replay.capacity() == resolved.actual_capacity(), "same plan can construct a fresh exact replay");
    }
  }
  auto tree = Pin(o::Scheme::kTree); tree.tree.emplace();
  tree.tree->position_map.mode = o::Scheme::kHierarchicalSynchronous;
  tree.tree->position_map.synchronous.emplace();
  tree.tree->position_map.synchronous->branching_factor = 2;
  CheckMap(o::resolve_options({128,8,48}, {1}, {}, tree));
  // Actual threaded payload and position-map helpers, with observed role hooks.
  tree.tree->position_map.mode = o::Scheme::kHierarchicalIncremental;
  tree.tree->position_map.synchronous.reset(); tree.tree->position_map.incremental.emplace();
  tree.tree->payload_max_threads = 2;
  tree.tree->position_map.incremental->owner_threads = 1;
  tree.tree->position_map.incremental->batch_participants = 2;
  std::mutex mutex; std::set<std::pair<int,unsigned>> observed;
  o::ConstructionHooks hooks;
  hooks.thread_init = [&](const o::PlannedThread& role) {
    std::lock_guard<std::mutex> lock(mutex);
    Expect(observed.emplace(static_cast<int>(role.role),role.index).second, "each thread init called once");
  };
  auto threaded = o::resolve_options({128,8,1024}, {5}, {}, tree);
  CheckMap(threaded, hooks);
  Expect(observed.size() == threaded.threads().size(), "actual worker roles match joint plan");
  // Synchronous helpers report zero-based planned roles from their own threads.
  for (bool nested : {false, true}) {
    observed.clear();
    auto options = Pin(nested ? o::Scheme::kTree : o::Scheme::kHierarchicalSynchronous);
    if (nested) {
      options.tree.emplace();
      options.tree->payload_max_threads = 1;
      options.tree->position_map.mode = o::Scheme::kHierarchicalSynchronous;
      options.tree->position_map.synchronous.emplace();
      options.tree->position_map.synchronous->batch_participants = 3;
      options.tree->position_map.synchronous->branching_factor = 2;
    } else {
      options.synchronous.emplace();
      options.synchronous->batch_participants = 3;
      options.synchronous->branching_factor = 2;
    }
    auto plan = o::resolve_options({128,8,48}, {4,0,{3,7,11,15}}, {}, options);
    std::vector<oram_bench::topology::Cpu> topology;
    for (unsigned cpu : {3u,7u,11u,15u}) {
      oram_bench::topology::Cpu entry;
      entry.id = cpu; entry.core = cpu; entry.package = 0;
      entry.l3 = "3,7,11,15"; entry.l3_bytes = 32u << 20;
      topology.push_back(entry);
    }
    // Synthetic masks on real helper threads: no host affinity is changed.
    // Every thread reaches its mask through Get(), which runs the declaration
    // on that thread, so each thread's copy is constructed and destroyed.
    struct Mask {
      static std::vector<unsigned>& Get() {
        static thread_local std::vector<unsigned> mask{3};
        return mask;
      }
    };
    oram_bench::VerifiedPlacement placement(topology, {3,7,11,15}, {
      [](unsigned cpu) { Mask::Get() = {cpu}; }, [] { return Mask::Get(); }});
    const auto caller = std::this_thread::get_id();
    auto checking = hooks;
    checking.thread_init = [&](const o::PlannedThread& role) {
      placement.Bind(role);
      hooks.thread_init(role);
      if (role.role != o::ThreadRole::kCaller && std::this_thread::get_id() == caller)
        throw std::logic_error("helper hook ran on caller");
    };
    CheckMap(plan, checking);
    Expect(observed.size() == plan.threads().size(), "synchronous roles match plan");
    placement.VerifyComplete(plan.threads());
    o::ConstructionHooks failing;
    failing.thread_init = [](const o::PlannedThread& role) {
      if (role.role == o::ThreadRole::kOnlineHelper || role.role == o::ThreadRole::kPositionOnlineHelper)
        throw std::invalid_argument("simulated helper affinity failure");
    };
    Reject([&] { o::make_map(plan, failing); }, "helper failure joins pool and propagates");
  }
  auto placement = o::resolve_options({128,4,8}, {1,0,{42}});
  Reject([&] { o::make_map(placement); }, "explicit CPU slots require a verification hook");
  o::ConstructionHooks failure;
  failure.thread_init = [](const o::PlannedThread&) { throw std::invalid_argument("simulated affinity failure"); };
  Reject([&] { o::make_map(placement, failure); }, "hook failure prevents construction");
}

std::vector<microram::byteslice::levelarena::LevelGroupPlan> Groups(const std::string& text) {
  std::vector<microram::byteslice::levelarena::LevelGroupPlan> groups;
  for (size_t at = 0; at < text.size();) {
    const size_t dash = text.find('-', at), comma = std::min(text.find(',', at), text.size());
    groups.push_back({unsigned(std::stoul(text.substr(at, dash - at))),
                      unsigned(std::stoul(text.substr(dash + 1, comma - dash - 1)))});
    at = comma + 1;
  }
  return groups;
}
unsigned Number(const o::ResolvedPlan& plan, const char* field) {
  return unsigned(std::stoul(Choice(plan, field).value));
}
size_t Count(const o::ResolvedPlan& plan, o::ThreadRole role) {
  return std::count_if(plan.threads().begin(), plan.threads().end(),
                       [&](const o::PlannedThread& t) { return t.role == role; });
}

// The rebuild thread budget: by default the hierarchy's rebuild takes every
// core the caller and batch helpers leave, divided by the library's load
// heuristic, and the plan names that division, its helpers and lanes.
void TestRebuildBudget() {
  const o::MapSpec large{size_t{1} << 20, 4, 8};
  const o::ResourceBudget sixteen{16, 1};
  auto p = o::resolve_options(large, sixteen, {}, Pin(o::Scheme::kHierarchicalIncremental));
  Expect(Choice(p, "hierarchy.rebuild_threads").value == "14" &&
         Choice(p, "hierarchy.rebuild_threads").source == o::ChoiceSource::kFallback,
         "the budget is every core the caller and harness leave");
  const unsigned owners = Number(p, "hierarchy.owner_threads"), used = Number(p, "hierarchy.rebuild_threads_used");
  Expect(Choice(p, "hierarchy.owner_threads").source == o::ChoiceSource::kDerived && owners > 2 &&
         owners <= Number(p, "hierarchy.levels"), "the heuristic divides the levels among more than two owners");
  Expect(used == owners + Number(p, "hierarchy.top_helpers") && used <= 14, "threads spent are within the budget");
  Expect(p.threads().size() == 1 + used && Count(p, o::ThreadRole::kOwner) == owners &&
         Count(p, o::ThreadRole::kTopHelper) == used - owners, "every rebuild thread is a planned role");
  Expect(Groups(Choice(p, "hierarchy.level_groups").value).size() == owners, "the division is named");
  Expect(Number(p, "hierarchy.slice_target_rate") > 0, "the slice rate is resolved");
  const auto& periods = p.carry_period_accesses();
  Expect(periods.size() == Number(p, "hierarchy.levels") && periods.front() > 0 &&
         std::is_sorted(periods.begin(), periods.end()) &&
         periods.back() * std::stoull(Choice(p, "hierarchy.top_digit").value) <= p.actual_capacity() * 2,
         "carry periods grow with the level and the top's is about capacity / D");
  // A tree's periods are its position map's; a synchronous map's are the
  // arena's, exactly as for the incremental scheme.
  const auto tree_periods = o::resolve_options(large, sixteen, {}, Pin(o::Scheme::kTree)).carry_period_accesses();
  Expect(!tree_periods.empty() && std::is_sorted(tree_periods.begin(), tree_periods.end()),
         "a tree reports its position map's carry periods");
  const auto sync = o::resolve_options(large, sixteen, {}, Pin(o::Scheme::kHierarchicalSynchronous));
  const auto& sync_periods = sync.carry_period_accesses();
  Expect(sync_periods.size() == Number(sync, "hierarchy.levels") && sync_periods.front() > 0 &&
         std::is_sorted(sync_periods.begin(), sync_periods.end()) &&
         sync_periods.back() * std::stoull(Choice(sync, "hierarchy.top_digit").value) <=
             sync.actual_capacity() * 2,
         "synchronous periods are the arena's");
  // Pinning that answer replays the same geometry and bill.
  const auto replays = [&](const o::MapSpec& spec, const o::ResolvedPlan& plan) {
    auto pin = Pin(o::Scheme::kHierarchicalIncremental); pin.incremental.emplace();
    pin.incremental->owner_threads = Number(plan, "hierarchy.owner_threads");
    pin.incremental->level_groups = Groups(Choice(plan, "hierarchy.level_groups").value);
    pin.incremental->top_helpers = Number(plan, "hierarchy.top_helpers");
    pin.incremental->rebuild_lanes = Number(plan, "hierarchy.rebuild_lanes");
    if (Number(plan, "hierarchy.rebuild_lanes") > 1)
      pin.incremental->lane_min_buckets = Number(plan, "hierarchy.lane_min_buckets");
    pin.incremental->dense_prefixes = Number(plan, "hierarchy.dense_prefixes");
    auto replay = o::resolve_options(spec, sixteen, {}, pin);
    return replay.modeled_buffer_bytes() == plan.modeled_buffer_bytes() &&
           Choice(replay, "hierarchy.levels").value == Choice(plan, "hierarchy.levels").value &&
           Choice(replay, "hierarchy.top_digit").value == Choice(plan, "hierarchy.top_digit").value &&
           Choice(replay, "hierarchy.prefix_flushes").value == Choice(plan, "hierarchy.prefix_flushes").value &&
           replay.threads().size() == plan.threads().size();
  };
  Expect(replays(large, p), "a pinned division replays the budget's plan");
  // At 2^16 entries, 4 B keys, 2 B values and three dense prefixes the
  // division cycles: two groups bill r0 = 4, which divides into three, which
  // bill r0 = 8, which divides into two.  The budget is cut to the cycle's two
  // owners, and that answer replays too.  The cycle sits on a byte margin, so
  // a change to the memory bill can move it to another shape.
  const o::MapSpec cycling{size_t{1} << 16, 4, 2};
  auto cycling_pin = Pin(o::Scheme::kHierarchicalIncremental);
  cycling_pin.incremental.emplace();
  cycling_pin.incremental->dense_prefixes = 3;
  auto cut = o::resolve_options(cycling, sixteen, {}, cycling_pin);
  Expect(Number(cut, "hierarchy.owner_threads") == 2 && Number(cut, "hierarchy.prefix_flushes") == 4 &&
         Number(cut, "hierarchy.rebuild_threads_used") == 2 && replays(cycling, cut),
         "a cycling division is cut to its fewer owners and replays");
  // The budget answers "how many threads" once; the pieces of one answer are refused next to it.
  auto both = Pin(o::Scheme::kHierarchicalIncremental); both.incremental.emplace();
  both.incremental->rebuild_threads = 4; both.incremental->owner_threads = 2;
  Reject([&] { o::resolve_options(large, sixteen, {}, both); }, "rebuild budget and owner count conflict");
  both.incremental->owner_threads.reset(); both.incremental->top_helpers = 1;
  Reject([&] { o::resolve_options(large, sixteen, {}, both); }, "top helpers need an explicit owner count");
  both.incremental->top_helpers.reset(); both.incremental->rebuild_threads = 15;
  Reject([&] { o::resolve_options(large, sixteen, {}, both); }, "budget beyond the cores left");
  both.incremental->rebuild_threads = 3;
  auto three = o::resolve_options(large, sixteen, {}, both);
  Expect(Choice(three, "hierarchy.rebuild_threads").source == o::ChoiceSource::kExplicit &&
         Number(three, "hierarchy.rebuild_threads_used") <= 3, "an explicit budget bounds the threads");
  both.incremental->rebuild_threads = used;
  auto smaller = o::resolve_options(large, sixteen, {}, both);
  const bool same_division = Choice(smaller, "hierarchy.level_groups").value == Choice(p, "hierarchy.level_groups").value &&
      Choice(smaller, "hierarchy.top_helpers").value == Choice(p, "hierarchy.top_helpers").value &&
      Choice(smaller, "hierarchy.rebuild_lanes").value == Choice(p, "hierarchy.rebuild_lanes").value;
  Expect(same_division == (smaller.configuration_key() == p.configuration_key()),
         "the budget itself is not part of the configuration, its division is");
  Expect(three.configuration_key() != p.configuration_key(), "a different division is a different configuration");
  both.incremental->rebuild_threads = 0;
  auto inline_plan = o::resolve_options(large, sixteen, {}, both);
  Expect(Number(inline_plan, "hierarchy.owner_threads") == 0 && inline_plan.threads().size() == 1,
         "a zero budget runs the rebuild inline");
  both.incremental->slice_target_rate = 1000000;
  Reject([&] { o::resolve_options(large, sixteen, {}, both); }, "slice rate without owners");
  both.incremental->slice_target_rate.reset(); both.incremental->inline_work_factor_ppm = 2000000;
  Expect(Choice(o::resolve_options(large, sixteen, {}, both), "hierarchy.inline_work_factor_ppm").value == "2000000",
         "inline share with the inline executor");
  both.incremental->rebuild_threads = 2;
  Reject([&] { o::resolve_options(large, sixteen, {}, both); }, "inline share with owners");
  // A tree's position map keeps its fixed two rebuild threads.
  auto tree = o::resolve_options({size_t{1} << 16, 8, 1024}, sixteen, {}, Pin(o::Scheme::kTree));
  Expect(Choice(tree, "position_map.rebuild_threads").value == "2", "nested position map keeps two threads");
  // Explicit helpers must have a laned table to share.
  auto helpers = Pin(o::Scheme::kHierarchicalIncremental); helpers.incremental.emplace();
  helpers.incremental->owner_threads = 2; helpers.incremental->top_helpers = 1;
  Reject([&] { o::resolve_options({4096, 4, 8}, {8}, {}, helpers); }, "helpers without lanes do nothing");
  helpers.incremental->rebuild_lanes = 4; helpers.incremental->lane_min_buckets = 1;
  auto laned = o::resolve_options({4096, 4, 8}, {8}, {}, helpers);
  Expect(laned.threads().size() == 4 && laned.threads()[1].role == o::ThreadRole::kOwner &&
         laned.threads()[2].role == o::ThreadRole::kTopHelper, "the top group's helper follows its owner");
  // Explicit owners and helpers together must fit the declared cores.
  helpers.incremental->top_helpers = 5;
  Expect(o::resolve_options({4096, 4, 8}, {8}, {}, helpers).threads().size() == 8,
         "owners and helpers that fill the budget are accepted");
  helpers.incremental->top_helpers = 6;
  Reject([&] { o::resolve_options({4096, 4, 8}, {8}, {}, helpers); },
         "owners and helpers beyond the core budget");
  helpers.incremental->top_helpers = 1;
  // Real helper threads call their own hook, off the caller's thread.
  std::mutex mutex; std::set<std::pair<int,unsigned>> observed;
  const auto caller = std::this_thread::get_id();
  o::ConstructionHooks hooks;
  hooks.thread_init = [&](const o::PlannedThread& role) {
    std::lock_guard<std::mutex> lock(mutex);
    Expect(observed.emplace(static_cast<int>(role.role), role.index).second, "each thread init called once");
    Expect(role.role == o::ThreadRole::kCaller || std::this_thread::get_id() != caller, "helper hook off caller");
  };
  CheckMap(laned, hooks);
  Expect(observed.size() == laned.threads().size(), "owner and helper hooks all ran");
  CheckMap(o::resolve_options({4096, 4, 8}, sixteen, {}, Pin(o::Scheme::kHierarchicalIncremental)));
  // An explicit boundary marks each rebuild thread's side for placement.
  auto split = Pin(o::Scheme::kHierarchicalIncremental); split.incremental.emplace();
  split.incremental->owner_threads = 2; split.incremental->near_max_level = 1;
  auto sides = o::resolve_options(large, sixteen, {}, split);
  Expect(sides.threads()[1].near == std::optional<bool>(false) && sides.threads()[2].near == std::optional<bool>(true) &&
         !sides.threads()[0].near, "top group far, level 1 near, caller unmarked");
  Expect(!p.threads()[1].near, "no boundary, no side");
  auto bank = Pin(o::Scheme::kHierarchicalIncremental); bank.incremental.emplace();
  bank.incremental->bank_first = o::BankFirst::kOff;
  Expect(Choice(o::resolve_options(large, sixteen, {}, bank), "hierarchy.bank_first").source ==
         o::ChoiceSource::kExplicit, "bank-first layout is an explicit geometry knob");
}

// Declared cache domains cap a budget's sides under an explicit boundary, so
// near/far placement never spills one side onto the other's cores.
// A target's rebuild cost model (the tuner's fit) arrives as overrides: it is
// the heuristic's input, so it changes the division and slice rate it
// resolves to, and only those enter the configuration key.
void TestRebuildCostModel() {
  const o::MapSpec large{size_t{1} << 22, 4, 8};
  const o::ResourceBudget sixteen{16, 1};
  const auto base = o::resolve_options(large, sixteen, {}, Pin(o::Scheme::kHierarchicalIncremental));
  Expect(Choice(base, "hierarchy.rebuild_cost_line_picos").value == "845" &&
         Choice(base, "hierarchy.rebuild_cost_line_picos").source == o::ChoiceSource::kFallback,
         "the default cost model is the development host's, and named");
  auto same = Pin(o::Scheme::kHierarchicalIncremental); same.incremental.emplace();
  same.incremental->rebuild_cost_line_picos = 845;
  Expect(o::resolve_options(large, sixteen, {}, same).configuration_key() == base.configuration_key(),
         "an explicit default model is the same configuration");
  // A slower probe halves the slice rate: a different configuration.
  auto probe = Pin(o::Scheme::kHierarchicalIncremental); probe.incremental.emplace();
  probe.incremental->rebuild_cost_probe_bucket_picos = 40000;
  probe.incremental->rebuild_cost_probe_line_picos = 900;
  const auto slow = o::resolve_options(large, sixteen, {}, probe);
  const double ratio = double(Number(base, "hierarchy.slice_target_rate")) /
                       double(Number(slow, "hierarchy.slice_target_rate"));
  Expect(ratio > 1.99 && ratio < 2.01, "the probe constants do not set the resolved slice rate");
  Expect(slow.configuration_key() != base.configuration_key(), "a different slice rate is a different configuration");
  // Costly jobs weigh level 1, which runs one per prefix, and that moves the
  // division of three owners.
  auto owners = Pin(o::Scheme::kHierarchicalIncremental); owners.incremental.emplace();
  owners.incremental->owner_threads = 3;
  const auto priced = o::resolve_options(large, sixteen, {}, owners);
  owners.incremental->rebuild_cost_job_nanos = 60000;
  const auto unpriced = o::resolve_options(large, sixteen, {}, owners);
  Expect(Choice(unpriced, "hierarchy.level_groups").value != Choice(priced, "hierarchy.level_groups").value,
         "the cost model does not move an explicit owner count's division");
  Expect(unpriced.configuration_key() != priced.configuration_key(), "a different division is a different configuration");
  // Where nothing is chosen by it, an explicit model is refused, not ignored.
  auto pinned = owners;
  pinned.incremental->level_groups = Groups(Choice(priced, "hierarchy.level_groups").value);
  Reject([&] { o::resolve_options(large, sixteen, {}, pinned); }, "line/job cost with an explicit division");
  auto rated = Pin(o::Scheme::kHierarchicalIncremental); rated.incremental.emplace();
  rated.incremental->slice_target_rate = 1000000;
  rated.incremental->rebuild_cost_probe_line_picos = 900;
  Reject([&] { o::resolve_options(large, sixteen, {}, rated); }, "probe cost with an explicit slice rate");
  auto inline_cost = Pin(o::Scheme::kHierarchicalIncremental); inline_cost.incremental.emplace();
  inline_cost.incremental->rebuild_threads = 0;
  inline_cost.incremental->rebuild_cost_job_nanos = 5000;
  Reject([&] { o::resolve_options(large, sixteen, {}, inline_cost); }, "cost model on the inline executor");
  auto cap = Pin(o::Scheme::kHierarchicalIncremental); cap.incremental.emplace();
  cap.incremental->owner_threads = 3;
  cap.incremental->rebuild_cost_max_top_threads = 16;
  Reject([&] { o::resolve_options(large, sixteen, {}, cap); }, "top-thread cap without a budget");
  auto broken = Pin(o::Scheme::kHierarchicalIncremental); broken.incremental.emplace();
  broken.incremental->rebuild_cost_max_top_threads = 0;
  Reject([&] { o::resolve_options(large, sixteen, {}, broken); }, "a cost model with no top thread");
  // A budget capped at two top threads never gives the top more than one helper.
  auto held = Pin(o::Scheme::kHierarchicalIncremental); held.incremental.emplace();
  held.incremental->rebuild_cost_max_top_threads = 2;
  held.incremental->rebuild_cost_helper_speedup_ppm = 200000;
  Expect(Number(o::resolve_options(large, sixteen, {}, held), "hierarchy.top_helpers") <= 1,
         "the resolved budget ignores the model's top-thread cap");
}

void TestDomainCaps() {
  auto domains = [](unsigned cores, unsigned count) {
    o::ResourceBudget budget{cores, 1}; budget.cache_domains = count; return budget;
  };
  const o::ResourceBudget one = domains(16, 1), two = domains(16, 2);
  Reject([&] { o::resolve_options({4096, 4, 8}, domains(16, 3), {}); }, "uneven cache domains");
  Reject([&] { o::resolve_options({4096, 4, 8}, domains(2, 2), {}); }, "domain holds only the harness");
  // Without a boundary the domains change nothing.
  auto plain = Pin(o::Scheme::kHierarchicalIncremental);
  Expect(Signature(o::resolve_options({size_t{1} << 20, 4, 8}, one, {}, plain)) ==
         Signature(o::resolve_options({size_t{1} << 20, 4, 8}, two, {}, plain)), "no boundary, no caps");
  bool bound = false;
  // 2^26 is where an uncapped far side first outgrows its domain.
  for (const size_t entries : {size_t{1} << 20, size_t{1} << 24, size_t{1} << 26}) {
    const unsigned levels = Number(o::resolve_options({entries, 4, 8}, two, {}, plain), "hierarchy.levels");
    for (unsigned boundary = 1; boundary < levels; ++boundary) {
      auto split = Pin(o::Scheme::kHierarchicalIncremental); split.incremental.emplace();
      split.incremental->near_max_level = boundary;
      auto side_counts = [](const o::ResolvedPlan& plan) {
        std::pair<unsigned, unsigned> counts{0, 0};
        for (const auto& thread : plan.threads())
          if (thread.near) ++(*thread.near ? counts.first : counts.second);
        return counts;
      };
      const auto capped = o::resolve_options({entries, 4, 8}, two, {}, split);
      const auto uncapped = o::resolve_options({entries, 4, 8}, one, {}, split);
      const auto [near, far] = side_counts(capped);
      Expect(Number(capped, "hierarchy.near_rebuild_threads_cap") == 6 &&
             Number(capped, "hierarchy.far_rebuild_threads_cap") == 8,
             "caller's domain less harness and caller; the other domain whole");
      Expect(near <= 6 && far <= 8, "neither side holds more threads than its domain has cores");
      const auto [loose_near, loose_far] = side_counts(uncapped);
      bound = bound || loose_near > 6 || loose_far > 8;
      const bool same_division = Choice(capped, "hierarchy.level_groups").value ==
                                     Choice(uncapped, "hierarchy.level_groups").value &&
                                 Number(capped, "hierarchy.top_helpers") == Number(uncapped, "hierarchy.top_helpers");
      Expect(same_division == (capped.configuration_key() == uncapped.configuration_key()),
             "the caps, like the budget, are not configuration; the division is");
    }
  }
  Expect(bound, "some uncapped division puts more threads on a side than a domain holds");
  // Batch helpers sit with the caller and shrink the near side.
  auto helped = Pin(o::Scheme::kHierarchicalIncremental); helped.incremental.emplace();
  helped.incremental->near_max_level = 1; helped.incremental->batch_participants = 3;
  Expect(Number(o::resolve_options({size_t{1} << 20, 4, 8}, two, {}, helped), "hierarchy.near_rebuild_threads_cap") == 4,
         "near cap excludes the caller's batch helpers");
  // Tree payload workers fill the caller's domain (6 cores past the harness and
  // the caller); only a value of at least kTreePayloadSpreadBytes also takes
  // the far domain's cores left after the position map's two rebuild threads.
  auto payload = [](const o::ResolvedPlan& plan) {
    std::pair<unsigned, unsigned> counts{0, 0};  // near, background
    for (const auto& thread : plan.threads())
      if (thread.role == o::ThreadRole::kPayload) ++(thread.near.value_or(false) ? counts.first : counts.second);
    return counts;
  };
  const auto tree = Pin(o::Scheme::kTree);
  const size_t wide = o::kTreePayloadSpreadBytes;
  Expect(payload(o::resolve_options({4096, 8, 1024}, one, {}, tree)) == std::make_pair(0u, 12u),
         "one domain: every core past the caller and two rebuild threads, no placement hint");
  Expect(payload(o::resolve_options({4096, 8, 1024}, two, {}, tree)) == std::make_pair(6u, 0u),
         "narrow value: the caller's domain only");
  Expect(payload(o::resolve_options({4096, 8, 64}, two, {}, tree)) == std::make_pair(2u, 0u),
         "the width still bounds the count");
  Expect(payload(o::resolve_options({4096, 8, wide - 1}, two, {}, tree)) == std::make_pair(6u, 0u),
         "just below the spread width");
  const auto spread = o::resolve_options({4096, 8, wide}, two, {}, tree);
  Expect(payload(spread) == std::make_pair(6u, 6u), "wide value: both domains, near first");
  Expect(Number(spread, "tree.payload_near_workers") == 6, "near count recorded");
  Expect(spread.threads().size() == 15, "the whole library budget");
  auto explicit_far = tree; explicit_far.tree.emplace(); explicit_far.tree->payload_near = false;
  Expect(payload(o::resolve_options({4096, 8, 1024}, two, {}, explicit_far)) == std::make_pair(0u, 6u),
         "payload_near = false keeps every worker background");
  auto capped = tree; capped.tree.emplace(); capped.tree->payload_max_threads = 8;
  Expect(payload(o::resolve_options({4096, 8, 1024}, two, {}, capped)) == std::make_pair(6u, 2u),
         "an explicit cap past the near side spills to the far one");
}

void TestBottomHelperPlans() {
  for (bool tree : {false, true}) {
    for (unsigned top_helpers : {0u, 1u}) {
      auto overrides = Pin(tree ? o::Scheme::kTree : o::Scheme::kHierarchicalIncremental);
      o::IncrementalOverrides settings;
      settings.owner_threads = 2;
      settings.top_helpers = top_helpers;
      settings.bottom_helpers = 1;
      settings.rebuild_lanes = 4;
      settings.lane_min_buckets = 1;
      settings.near_max_level = 1;
      if (tree) {
        overrides.tree.emplace();
        overrides.tree->position_map.incremental = settings;
      } else {
        overrides.incremental = settings;
      }
      const auto plan = o::resolve_options({4096, 4, tree ? 512u : 8u}, {8}, {}, overrides);
      const auto role = tree ? o::ThreadRole::kPositionBottomHelper : o::ThreadRole::kBottomHelper;
      Expect(Count(plan, role) == 1, "bottom helper has a planned role");
      Expect(plan.threads().size() == 4 + top_helpers + plan.payload_workers(),
             "thread plan includes both helper pools");
      Expect(Number(plan, tree ? "position_map.rebuild_threads_used" : "hierarchy.rebuild_threads_used") ==
                 3 + top_helpers, "rebuild total includes bottom helpers");
      for (const auto& thread : plan.threads())
        if (thread.role == role)
          Expect(thread.index == 0 && thread.near == std::optional<bool>(true),
                 "bottom helper uses a local pool index and level 1 locality");
      std::mutex mutex;
      std::set<std::pair<int, unsigned>> observed;
      const auto caller = std::this_thread::get_id();
      o::ConstructionHooks hooks;
      hooks.thread_init = [&](const o::PlannedThread& thread) {
        std::lock_guard<std::mutex> lock(mutex);
        Expect(observed.emplace(static_cast<int>(thread.role), thread.index).second,
               "each bottom/top helper hook runs once");
        Expect(thread.role == o::ThreadRole::kCaller || std::this_thread::get_id() != caller,
               "helper initialization runs on its worker");
      };
      CheckMap(plan, hooks);
      Expect(observed.size() == plan.threads().size(), "all planned helper hooks ran");
      if (tree) overrides.tree->position_map.incremental->bottom_helpers = std::numeric_limits<unsigned>::max();
      else overrides.incremental->bottom_helpers = std::numeric_limits<unsigned>::max();
      Reject([&] { o::resolve_options({4096, 4, tree ? 512u : 8u}, {8}, {}, overrides); },
             "helper counts cannot wrap the core budget");
    }
  }
}

void TestValueWorkers() {
  for (auto scheme : {o::Scheme::kHierarchicalIncremental,o::Scheme::kHierarchicalSynchronous}) {
    o::OptionOverrides overrides; overrides.scheme = scheme;
    if (scheme == o::Scheme::kHierarchicalIncremental) {
      overrides.incremental.emplace(); overrides.incremental->value_workers = 3;
      overrides.incremental->owner_threads = 0; overrides.incremental->value_tail = 3;
      overrides.incremental->value_kernel = o::ValueKernel::kPermute;
    } else { overrides.synchronous.emplace(); overrides.synchronous->value_workers = 3; }
    const auto plan = o::resolve_options({512,8,48},{4},{},overrides);
    unsigned workers = 0;
    for (const auto& thread : plan.threads()) workers += thread.role == o::ThreadRole::kValue;
    Expect(workers == 3 && plan.threads().size() == 4,"value workers count against cores");
    o::ConstructionHooks hooks;
    std::atomic<unsigned> initialized{0};
    hooks.thread_init = [&](const o::PlannedThread& t) { if (t.role == o::ThreadRole::kValue) ++initialized; };
    CheckMap(plan,hooks);
    Expect(initialized == 3,"value init hooks run on configured workers");
    Reject([&] { o::resolve_options({512,8,48},{3},{},overrides); },"value workers exceed core budget");
  }
  o::OptionOverrides nested; nested.scheme=o::Scheme::kTree; nested.tree.emplace();
  nested.tree->payload_max_threads=1;
  nested.tree->position_map.mode=o::Scheme::kHierarchicalIncremental;
  nested.tree->position_map.incremental.emplace();
  nested.tree->position_map.incremental->owner_threads=0;
  nested.tree->position_map.incremental->value_workers=2;
  const auto plan=o::resolve_options({512,8,256},{4},{},nested);
  unsigned values=0; for(const auto& t:plan.threads()) values+=t.role==o::ThreadRole::kPositionValue;
  Expect(values==2,"nested value workers reserve position cores");
  CheckMap(plan);
  nested.tree->position_map.incremental->value_workers=std::numeric_limits<unsigned>::max();
  Reject([&] { o::resolve_options({512,8,256},{4},{},nested); },"nested value count cannot wrap core accounting");
  {
    // A value worker names a dense run's bucket in 12 bits, so a plan whose
    // dense prefix is longer than 4096 buckets is refused when it resolves.
    o::OptionOverrides big; big.scheme = o::Scheme::kHierarchicalIncremental; big.incremental.emplace();
    big.incremental->owner_threads = 0; big.incremental->value_workers = 2;
    big.incremental->online_stash_entries = 64 * 1024; big.incremental->prefix_flushes = 8;
    Reject([&] { o::resolve_options({size_t{1} << 22,8,16},{4},{},big); },
           "value workers with a dense prefix over 4096 buckets");
    big.incremental->prefix_flushes = 4;
    Expect(o::resolve_options({size_t{1} << 22,8,16},{4},{},big).choices().size() > 0,
           "value workers with a 4096-bucket dense prefix resolve");
  }

}

void TestLegacyFinish() {
  o::HybridOptions options;
  options.tree.payload_max_threads = 2;
  options.tree.position_map.deamortized_owner_threads = 0;
  o::Map<uint64_t, std::array<uint8_t,256>> map(128, options);
  std::array<uint8_t,256> value{}; value.fill(19);
  map.insert_or_assign(3, value);
  map.finish_pending_work();
  std::array<uint8_t,256> out{};
  Expect(map.find(3, &out) && out == value, "typed legacy hybrid supports complete finish");
}
}  // namespace

// Resolver auto and default Map<> both take their scheme and geometry
// from DefaultRule; only the payload-worker count they pass differs.
void TestDefaultRule() {
  Expect(o::kHybridTreeValueThreshold == 96, "the default crossover moved");
  for (size_t v : {8, 64, 95, 96, 127, 128, 191, 192, 256, 512, 1024, 4096}) {
    Expect(o::DefaultRule(v).tree == (v >= o::kHybridTreeValueThreshold),
           "default Map<>'s rule is the 96-byte crossover");
    for (unsigned cores : {2u, 4u, 16u}) {
      const auto plan = o::resolve_options({4096, 8, v}, {cores}, {}, {});
      Expect((plan.scheme() == o::Scheme::kTree) == o::DefaultRule(v).tree,
             "auto follows DefaultRule");
    }
  }
  const o::Options options;
  Expect(options.deamortized_branching_factor == o::kDefaultGeometry.branching_factor &&
         options.deamortized_dense_prefixes == o::kDefaultGeometry.dense_prefixes &&
         options.deamortized_online_stash_entries == o::kDefaultGeometry.online_stash_entries &&
         options.deamortized_half_fanout_prefix == o::kDefaultGeometry.half_fanout_prefix,
         "Options default to the rule's geometry");
  const auto plan = o::resolve_options({4096, 8, 16}, {4}, {}, {});
  Expect(Choice(plan, "hierarchy.branching_factor").value == std::to_string(o::kDefaultGeometry.branching_factor) &&
         Choice(plan, "hierarchy.online_stash_entries").value ==
             std::to_string(o::kDefaultGeometry.online_stash_entries),
         "auto falls back to the rule's geometry");
}

// The tree's fold and stash width: 0 is the default rule's, explicit or not,
// and reports the derived value; fewer stash registers than the rule's for
// the depth and fold are refused; and the map builds the tree the plan solved, also
// just past the capacities where the rule's fold-5 tree is one level deeper
// than an explicit fold 5 with four stash registers would be.
void TestTreeGeometry() {
  const auto unset = o::resolve_options({size_t{1} << 21, 32, 1024}, {4}, {}, Pin(o::Scheme::kTree));
  auto zero = Pin(o::Scheme::kTree); zero.tree.emplace();
  zero.tree->fold = 0; zero.tree->stash_registers = 0;
  const auto zeros = o::resolve_options({size_t{1} << 21, 32, 1024}, {4}, {}, zero);
  Expect(Choice(zeros, "tree.fold").value == "4" && Choice(zeros, "tree.stash_registers").value == "3" &&
         Choice(zeros, "tree.path_slots").value == "64",
         "explicit fold and stash_registers 0 resolve to the rule's");
  Expect(zeros.configuration_key() == unset.configuration_key(),
         "explicit 0 has the unset plan's configuration key");
  auto low = Pin(o::Scheme::kTree); low.tree.emplace();
  low.tree->fold = 5; low.tree->stash_registers = 3;
  Reject([&] { o::resolve_options({size_t{1} << 20, 8, 1024}, {4}, {}, low); },
         "fold 5 with three stash registers");
  low.tree->stash_registers.reset();
  Expect(Choice(o::resolve_options({size_t{1} << 20, 8, 1024}, {4}, {}, low), "tree.stash_registers").value == "4",
         "an explicit fold 5 takes four stash registers");
  // From 25 leaf bits (2^27 entries) the rule takes four at fold 1 too, and
  // three are refused there; 24 leaf bits (2^26) still take three.
  const auto below = o::resolve_options({size_t{1} << 26, 8, 1024}, {4}, {}, Pin(o::Scheme::kTree));
  Expect(Choice(below, "tree.leaf_bits").value == "24" && Choice(below, "tree.fold").value == "1" &&
         Choice(below, "tree.stash_registers").value == "3",
         "2^26 entries take three stash registers at fold 1");
  const auto wide = o::resolve_options({size_t{1} << 27, 8, 1024}, {4}, {}, Pin(o::Scheme::kTree));
  Expect(Choice(wide, "tree.leaf_bits").value == "25" && Choice(wide, "tree.fold").value == "1" &&
         Choice(wide, "tree.stash_registers").value == "4",
         "2^27 entries take four stash registers at fold 1");
  auto narrow = Pin(o::Scheme::kTree); narrow.tree.emplace();
  narrow.tree->stash_registers = 3;
  Reject([&] { o::resolve_options({size_t{1} << 27, 8, 1024}, {4}, {}, narrow); },
         "25 leaf bits with three stash registers");
  for (const auto c : {std::pair<size_t, unsigned>{2097247, 0}, {131078, 4}}) {
    auto p = Pin(o::Scheme::kTree); p.tree.emplace(); p.tree->leaf_scale = c.second;
    const auto plan = o::resolve_options({c.first, 8, 16}, {1}, {}, p);
    const auto g = microram::tree::TreeGeometry::ForCapacity(c.first, 0, 16, c.second);
    Expect(g.leaf_bits == 20 && g.fold == 5 && g.shape.stash_registers == 4 &&
           Choice(plan, "tree.leaf_bits").value == "20" && Choice(plan, "tree.fold").value == "5" &&
           Choice(plan, "tree.stash_registers").value == "4" && Choice(plan, "tree.path_slots").value == "64",
           "the plan solves the rule's tree");
    // Construction throws if the tree built differs from the plan's.
    auto map = o::make_map(plan);
    Expect(map.capacity() == c.first, "the planned tree constructs");
  }
}

// Map<> at a core budget builds what auto plans at that budget -- engine,
// payload workers and rebuild division.  Budgets stay small (at most four
// cores), since engines clamp to the host's physical cores.
void TestCoreBudget() {
  for (size_t v : {8, 255, 256, 1023, 1024}) {
    for (unsigned cores : {1u, 2u, 3u, 4u}) {
      const auto plan = o::resolve_options({4096, 8, v}, {cores}, {}, {});
      o::HybridByteMap<> map(4096, 8, v, o::CoreBudget{cores});
      Expect(map.uses_tree() == (plan.scheme() == o::Scheme::kTree), "budgeted Map<> picks auto's engine");
      if (map.uses_tree()) {
        Expect(map.tree()->payload_planes() == plan.payload_workers(), "budgeted Map<> runs auto's payload workers");
      } else {
        auto configured = o::make_map(plan);
        configured.with_backend([&](auto& concrete) {
          using M = std::decay_t<decltype(concrete)>;
          if constexpr (std::is_same_v<M, o::ByteMap<true>>) {
            const auto& mine = map.hierarchical()->engine();
            const auto& theirs = concrete.engine();
            Expect(mine.threaded() == theirs.threaded() && mine.owner_groups() == theirs.owner_groups() &&
                       mine.top_helper_threads() == theirs.top_helper_threads(),
                   "budgeted Map<> divides the rebuild as auto does");
          } else {
            Expect(false, "auto planned an engine Map<true> cannot hold");
          }
        });
      }
    }
  }
  // Typed and synchronous forms; a budget of zero is refused.
  o::Map<uint64_t, std::array<uint8_t, 1024>> typed(4096, o::CoreBudget{4});
  Expect(typed.byte_map().uses_tree(), "a 1 KiB Map<> at four cores is the tree");
  o::HybridByteMap<false> synchronous(4096, 8, 16, o::CoreBudget{2});
  Expect(!synchronous.uses_tree(), "a 16-byte synchronous Map<> is the hierarchy");
  Reject([&] { o::HybridByteMap<> zero(4096, 8, 16, o::CoreBudget{0}); }, "a budget of zero cores");
}

// The budget's one spin-before-park reaches every spin the overrides leave
// unset (e.g. a long spin for latency-sensitive callers that prefer burning a
// core to a wake-up delay), keeps explicit ones, and skips the tree's payload
// spin where there are no payload workers.
void TestSpinBudget() {
  o::ResourceBudget budget{16};
  budget.harness_cores = 1;
  Expect(Choice(o::resolve_options({1u << 20, 4, 8}, budget), "hierarchy.owner_spin_ns").value == "1000000",
         "no budget spin keeps the default owner spin");
  budget.spin_before_park_ns = 1000000000;
  const auto hierarchy = o::resolve_options({1u << 20, 4, 8}, budget);
  for (const char* field : {"hierarchy.owner_spin_ns", "hierarchy.batch_spin_ns", "hierarchy.value_spin_ns"}) {
    Expect(Choice(hierarchy, field).value == "1000000000", "budget spin reaches every hierarchy spin");
    Expect(Choice(hierarchy, field).source == o::ChoiceSource::kDerived, "budget spin recorded as derived");
  }
  auto pinned = Pin(o::Scheme::kHierarchicalIncremental);
  pinned.incremental.emplace(); pinned.incremental->owner_spin_ns = 5000;
  const auto kept = o::resolve_options({1u << 20, 4, 8}, budget, {}, pinned);
  Expect(Choice(kept, "hierarchy.owner_spin_ns").value == "5000" &&
         Choice(kept, "hierarchy.owner_spin_ns").source == o::ChoiceSource::kExplicit,
         "an explicit spin wins over the budget's");
  Expect(Choice(kept, "hierarchy.batch_spin_ns").value == "1000000000", "the unset spins still take the budget's");
  const auto synchronous = o::resolve_options({1u << 20, 4, 8}, budget, {},
                                              Pin(o::Scheme::kHierarchicalSynchronous));
  Expect(Choice(synchronous, "hierarchy.batch_spin_ns").value == "1000000000", "synchronous batch spin");
  const auto tree = o::resolve_options({1u << 20, 4, 1024}, budget);
  Expect(tree.scheme() == o::Scheme::kTree, "wide values resolve to the tree");
  Expect(Choice(tree, "tree.payload_spin_us").value == "1000000", "payload spin in microseconds");
  Expect(Choice(tree, "position_map.owner_spin_ns").value == "1000000000", "the position map's owners spin too");
  const auto narrow = o::resolve_options({1u << 20, 4, 8}, budget, {}, Pin(o::Scheme::kTree));
  Expect(Choice(narrow, "tree.payload_spin_us").source != o::ChoiceSource::kDerived,
         "no payload workers: the payload spin is left alone, not refused");
}

int main() {
  TestLegacyThreadAccounting();
  TestDefaultRule();
  TestTreeGeometry();
  TestCoreBudget();
  TestResolution(); TestInvalidInputs(); TestNestedBudget(); TestPlanningBoundaries();
  TestRealEngines(); TestLegacyFinish(); TestIneffectiveKnobs(); TestOverflowCandidate();
  TestRebuildBudget(); TestRebuildCostModel(); TestDomainCaps();
  TestBottomHelperPlans(); TestValueWorkers(); TestSpinBudget();
  if (failures) return 1;
  std::puts("configuration correctness tests passed (no performance measurements)");
}
