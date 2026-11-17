#pragma once

// OPT-IN RESOURCE PLANNING (guide: CONFIGURATION.md beside this header).
//
// `resolve_options(spec, budget, workload, overrides)` turns a public map
// specification, an explicit core/memory budget and optional per-field
// overrides into a `ResolvedPlan`: the chosen scheme (incremental or
// synchronous hierarchy, or tree), every resolved option with its provenance
// (explicit, fallback default, or derived), the planned threads and their
// roles, the modeled buffer bytes, and the certification report.
// `make_map(plan)` builds a `ConfiguredByteMap` from a plan and checks that
// the constructed map agrees with it.  The ordinary constructors
// (byte_map.hpp, tree_oram.hpp) are unaffected and keep their own defaults.
//
// Every input here is public; resolution never sees keys or values.
// Resolution creates no maps, worker threads or random seeds and does no CPU
// discovery: topology facts (cache domains, monitor-wait support, CPU ids)
// are declared by the caller.  Memory reports describe modeled buffers, not
// total heap or process memory.  Invalid or contradictory inputs throw
// std::invalid_argument naming the field.
#include <cpu_byteslice_oram/tree_oram.hpp>
#include "src/core/monitor_wait.hpp"

#include <algorithm>
#include <cstdint>
#include <functional>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>
#include <vector>

namespace cpu_byteslice_oram {

// The engine a plan builds: kAuto lets the default rule (default_rule.hpp)
// choose; the others pin ByteMap<true>, ByteMap<false> or TreeByteMap.
enum class Scheme { kAuto, kHierarchicalIncremental, kHierarchicalSynchronous, kTree };
// Whether the caller will use scalar calls or access_batch (a hint).
enum class ApiMode { kScalar, kBatch };
// Where a resolved value came from: an explicit override, the library's
// fallback default, or derived from other choices.
enum class ChoiceSource { kExplicit, kFallback, kDerived };
// What each planned thread does; the kPosition* roles are a tree's position
// map's.  Numeric values are stable because they are recorded in resolved
// plans, so roles are only appended; kRebuild and kPositionRebuild are
// reserved values that no plan produces.
enum class ThreadRole { kCaller, kOwner, kOnlineHelper, kRebuild,
                        kPayload, kPositionOwner, kPositionOnlineHelper, kPositionRebuild,
                        kTopHelper, kPositionTopHelper,
                        // 10 is reserved: the benchmark worker's JSON output
                        // (analysis/oram_bench/schema.py) uses it for the
                        // thread-pool slots of baseline backends.
                        kBottomHelper = 11, kPositionBottomHelper, kValue, kPositionValue };

// The map being planned: capacity in entries, key and value widths in bytes,
// and the access horizon (Options::max_accesses).
struct MapSpec {
  size_t requested_capacity = 0;
  size_t key_bytes = 0;
  size_t value_bytes = 0;
  uint64_t max_accesses = uint64_t{1} << 32;
};

// The resources a plan may spend.  Exceeding them explicitly is refused;
// automatic counts use what remains.
struct ResourceBudget {
  // Includes the caller and reserved harness cores. No hardware-auto sentinel.
  unsigned cores = 1;
  unsigned harness_cores = 0;
  // Optional CPU slots, one per declared physical core; the caller supplies
  // topology evidence. Explicit placement requires verified construction hooks.
  std::vector<unsigned> cpu_ids;
  // A limit on the modeled buffers (ResolvedPlan::modeled_buffer_bytes), not
  // on the process: those buffers are nearly all of each engine's heap at
  // practical capacities (benchmarks/oram/cpu_oram_allocation_audit.cpp
  // measures the remainder), but thread stacks, the allocator's rounding and
  // everything outside the library are not in them.
  std::optional<size_t> modeled_buffer_limit_bytes;
  // Declared cache domains (L3s) the cores split into evenly: a public input,
  // not discovered, so a plan does not depend on the host that resolves it.
  // With an explicit near/far boundary the rebuild budget is capped per side:
  // near threads share the caller's domain, which near/far placement also
  // gives the harness, and far threads get the other domains.
  unsigned cache_domains = 1;
  // The idle-wait instruction the target offers (as the benchmark doctor,
  // analysis/oram_bench/doctor.py, reports it), declared like cache_domains so a plan never depends on the CPU
  // that resolves it. A plan asking for monitor-wait needs one; the caller
  // checks the declaration against the CPU before it trusts the plan.
  microram::core::MonitorWaitKind monitor_wait = microram::core::MonitorWaitKind::kNone;
  // One spin-before-park for every library thread that waits (rebuild owners
  // and helpers, the requester's own wait, batch helpers, value workers, tree
  // payload workers), wherever the overrides leave that spin unset. Zero keeps
  // each field's default. A latency setting only: it never changes a result.
  uint64_t spin_before_park_ns = 0;
};

// The caller's expected API use.  Validated and recorded; the default rule
// does not depend on it.
struct WorkloadHint {
  ApiMode api_mode = ApiMode::kScalar;
  size_t expected_batch_size = 1;
};

// Tables keep the typed overrides, resolved values, provenance, and the
// matching `Options` / `TreeOptions` field (each row's last column) together.
// Columns: type, override name, fallback default, Options field.  A
// disengaged optional is auto; 0/false stay explicit.
// THE ARENA FIELDS configure both hierarchy schemes: the geometry, the batch
// path and the requester's wait limit.  THE REBUILD FIELDS -- threads,
// slices, placement and the cost model that divides them -- only the
// incremental one, since the synchronous scheme runs every merge on the
// requester (LevelArenaEngine::Options::synchronous).
#define CPU_ORAM_ARENA_FIELDS(X) \
  X(unsigned, value_workers, 0, deamortized_value_workers) \
  X(unsigned, value_tail, 2, deamortized_value_tail) \
  X(ValueKernel, value_kernel, ValueKernel::kAuto, deamortized_value_kernel) \
  X(uint64_t, value_spin_ns, 200000, deamortized_value_spin_nanos) \
  X(bool, value_pause, true, deamortized_value_pause) \
  X(bool, value_monitor_wait, false, deamortized_value_monitor_wait) \
  X(bool, value_demote, false, deamortized_value_demote) \
  X(unsigned, branching_factor, kDefaultGeometry.branching_factor, deamortized_branching_factor) \
  X(size_t, online_stash_entries, kDefaultGeometry.online_stash_entries, deamortized_online_stash_entries) \
  X(unsigned, prefix_flushes, 0, deamortized_prefix_flushes) \
  X(unsigned, top_digit, 0, deamortized_top_digit) \
  X(unsigned, dense_prefixes, kDefaultGeometry.dense_prefixes, deamortized_dense_prefixes) \
  X(bool, half_fanout_prefix, kDefaultGeometry.half_fanout_prefix, deamortized_half_fanout_prefix) \
  X(size_t, tier_buckets, 0, deamortized_tier_buckets) \
  X(BankFirst, bank_first, BankFirst::kNoClone, deamortized_bank_first) \
  X(unsigned, batch_lanes, 16, deamortized_batch_lanes) \
  X(BatchExecutionShape, batch_execution, BatchExecutionShape::kChunkedCascade, deamortized_batch_execution) \
  X(unsigned, batch_participants, 1, deamortized_batch_participants) \
  X(bool, batch_bucket_scan, false, deamortized_batch_bucket_scan) \
  X(bool, batch_profile, false, deamortized_batch_profile) \
  X(BatchResultLayout, batch_result_layout, BatchResultLayout::kSlicedPlaceAtLane, deamortized_batch_result_layout) \
  X(uint64_t, batch_spin_ns, uint64_t{la::kLevelArenaOwnerSpinMicros} * 1000, deamortized_batch_spin_nanos) \
  X(unsigned, wait_limit_ms, 120000, deamortized_wait_limit_millis)

// The rebuild_cost_* defaults are the rebuild cost model's calibration
// constants (LevelArenaRebuildCost); `python -m analysis.oram_bench
// fit-rebuild` re-derives them for a target.  They steer thread division and
// slicing only, never what is stored or which memory an access touches.
#define CPU_ORAM_REBUILD_FIELDS(X) \
  X(unsigned, owner_threads, 0, deamortized_owner_threads) \
  X(unsigned, top_helpers, 0, deamortized_top_helpers) \
  X(unsigned, bottom_helpers, 0, deamortized_bottom_helpers) \
  X(size_t, rebuild_lanes, 1, deamortized_rebuild_lanes) \
  X(size_t, lane_min_buckets, size_t{1} << 15, deamortized_lane_min_buckets) \
  X(uint64_t, slice_target_rate, 0, deamortized_slice_target_rate) \
  X(size_t, slice_touches, 0, deamortized_slice_touches) \
  X(bool, time_rebuild_stages, false, deamortized_time_rebuild_stages) \
  X(unsigned, near_max_level, 0, deamortized_near_max_level) \
  X(uint64_t, owner_spin_ns, uint64_t{la::kLevelArenaOwnerSpinMicros} * 1000, deamortized_owner_spin_nanos) \
  X(unsigned, park_retry_us, 1000, deamortized_park_retry_micros) \
  X(uint64_t, rebuild_cost_line_picos, 845, deamortized_rebuild_cost.line_picos) \
  X(uint64_t, rebuild_cost_residual_line_picos, 397, deamortized_rebuild_cost.residual_line_picos) \
  X(uint64_t, rebuild_cost_offer_line_picos, 1696, deamortized_rebuild_cost.offer_line_picos) \
  X(uint64_t, rebuild_cost_job_nanos, 2659, deamortized_rebuild_cost.job_nanos) \
  X(uint64_t, rebuild_cost_middle_burst_ppm, 300000, deamortized_rebuild_cost.middle_burst_ppm) \
  X(uint64_t, rebuild_cost_helper_speedup_ppm, 550000, deamortized_rebuild_cost.helper_speedup_ppm) \
  X(unsigned, rebuild_cost_max_top_threads, 8, deamortized_rebuild_cost.max_top_threads) \
  X(uint64_t, rebuild_cost_thread_gain_floor_ppm, 10000, deamortized_rebuild_cost.thread_gain_floor_ppm) \
  X(uint64_t, rebuild_cost_probe_bucket_picos, 20000, deamortized_rebuild_cost.probe_bucket_picos) \
  X(uint64_t, rebuild_cost_probe_line_picos, 450, deamortized_rebuild_cost.probe_line_picos) \
  X(uint64_t, rebuild_cost_slice_line_picos, 1500, deamortized_rebuild_cost.slice_line_picos)

#define CPU_ORAM_INCREMENTAL_FIELDS(X) CPU_ORAM_ARENA_FIELDS(X) CPU_ORAM_REBUILD_FIELDS(X)
#define CPU_ORAM_SYNCHRONOUS_FIELDS(X) CPU_ORAM_ARENA_FIELDS(X)

#define CPU_ORAM_TREE_FIELDS(X) \
  X(unsigned, fold, 0, fold) \
  X(unsigned, leaf_scale, 0, leaf_scale) \
  X(unsigned, max_load_ppm, 0, max_load) \
  X(unsigned, max_folded_slots, 0, max_folded_slots) \
  X(unsigned, stash_registers, 0, stash_registers) \
  X(unsigned, prefetch_ahead, 4, prefetch_ahead) \
  X(bool, uid_from_key, true, uid_from_key) \
  X(unsigned, payload_max_threads, 0, payload_max_threads) \
  X(size_t, payload_threshold, 32, payload_threshold) \
  X(unsigned, payload_spin_us, 200, payload_spin_micros) \
  X(bool, payload_monitor_wait, false, payload_monitor_wait)

#define CPU_ORAM_OPTIONAL(type, name, default_value, legacy) std::optional<type> name;
#define CPU_ORAM_VALUE(type, name, default_value, legacy) type name = default_value;
// A tree's position map keeps two rebuild threads unless told otherwise.
inline constexpr unsigned kTreePositionRebuildThreads = 2;
// With several cache domains, tree payload workers stay in the caller's
// domain below this value width and spread over every domain from it on:
// below it the cross-domain hand-off of each job costs more than a second
// memory link gains.  A calibration constant chosen by measurement on a
// two-domain host; it affects placement only, never results.
inline constexpr size_t kTreePayloadSpreadBytes = 2048;
inline constexpr uint64_t kInlineWorkFactorPpm =
    static_cast<uint64_t>(la::kLevelArenaInlineWorkFactor * 1000000);
// The rebuild's thread fields that do not map one to one onto Options:
// `rebuild_threads` is a budget the resolver divides itself (owners, top
// helpers, lanes and the level division are then explicit), `level_groups`
// is a list, and the inline share is a ratio in ppm like every other ratio.
struct IncrementalOverrides {
  CPU_ORAM_INCREMENTAL_FIELDS(CPU_ORAM_OPTIONAL)
  std::optional<unsigned> rebuild_threads;
  std::optional<std::vector<la::LevelGroupPlan>> level_groups;
  std::optional<uint64_t> inline_work_factor_ppm;
};
struct SynchronousOverrides { CPU_ORAM_SYNCHRONOUS_FIELDS(CPU_ORAM_OPTIONAL) };
struct PositionMapOverrides {
  std::optional<Scheme> mode;
  std::optional<IncrementalOverrides> incremental;
  std::optional<SynchronousOverrides> synchronous;
};
struct TreeOverrides {
  CPU_ORAM_TREE_FIELDS(CPU_ORAM_OPTIONAL)
  // Placement only: mark payload workers `near`, so a caller that
  // places by cache domain puts them in the caller's. The map ignores it.
  std::optional<bool> payload_near;
  PositionMapOverrides position_map;
};
struct OptionOverrides {
  Scheme scheme = Scheme::kAuto;
  std::optional<IncrementalOverrides> incremental;
  std::optional<SynchronousOverrides> synchronous;
  std::optional<TreeOverrides> tree;
};

struct IncrementalSettings {
  CPU_ORAM_INCREMENTAL_FIELDS(CPU_ORAM_VALUE)
  unsigned rebuild_threads = 0;  // the budget, when one was divided
  std::vector<la::LevelGroupPlan> level_groups;  // highest first; empty inline
  uint64_t inline_work_factor_ppm = kInlineWorkFactorPpm;
};
struct SynchronousSettings { CPU_ORAM_SYNCHRONOUS_FIELDS(CPU_ORAM_VALUE) };
struct TreeSettings { CPU_ORAM_TREE_FIELDS(CPU_ORAM_VALUE) };
#undef CPU_ORAM_OPTIONAL
#undef CPU_ORAM_VALUE

// One resolved field: its name, value as text, provenance and the reason.
struct ResolvedChoice {
  std::string field;
  std::string value;
  ChoiceSource source;
  std::string reason;
};
// One thread a plan starts (or the caller): its role, index within that
// role, and the CPU slot it is placed on when `ResourceBudget::cpu_ids` is
// given.
struct PlannedThread {
  ThreadRole role;
  unsigned index;
  std::optional<unsigned> cpu;
  // A rebuild thread's side of an explicit near/far boundary: true when every
  // level it drives is at or below it (it wants the caller's cache domain).
  // True for the payload workers placed in the caller's domain
  // (`PlanData::payload_near_workers`). Disengaged without a boundary and for
  // every other role.
  std::optional<bool> near = std::nullopt;
};
// How much a component's memory figure can be trusted.
enum class MemoryCoverage {
  // The engine records every buffer of this component as it allocates it,
  // and construction checks that record against this plan's figure.
  kTallied,
  // Computed from the geometry the constructor sizes from, without a
  // construction-time check.
  kModeled,
  // Less than what is allocated, by an unknown amount.
  kLowerBound,
};
// One modeled buffer component and its requested bytes.
struct PlannedMemory {
  std::string component;
  size_t requested_bytes;
  MemoryCoverage coverage = MemoryCoverage::kTallied;
  // A component may be complete while the aggregate library report is partial.
};
inline const char* MemoryCoverageName(MemoryCoverage c) {
  switch (c) {
    case MemoryCoverage::kTallied: return "tallied";
    case MemoryCoverage::kModeled: return "modeled";
    case MemoryCoverage::kLowerBound: return "lower_bound";
  }
  return "?";
}
// What the planned map supports: direct initialization (hierarchy only),
// batched position-map work (tree), and the batch execution path's name.
struct PlanCapabilities {
  bool direct_initialization = false;
  bool batch_position_map = false;
  std::string batch_execution_path;
};

namespace configuration_detail {
inline void Require(bool yes, const std::string& message) {
  if (!yes) throw std::invalid_argument("configuration: " + message);
}
template <class T> inline std::string Value(T value) {
  return std::to_string(static_cast<uint64_t>(value));
}
template <> inline std::string Value(bool value) { return value ? "true" : "false"; }
inline std::string Value(const std::string& value) { return value; }
// A level division, highest group first, as "first-last,first-last,...".
inline std::string GroupsText(const std::vector<la::LevelGroupPlan>& groups) {
  std::string text;
  for (const auto& g : groups)
    text += (text.empty() ? "" : ",") + std::to_string(g.first) + "-" + std::to_string(g.last);
  return text;
}
inline void Choice(std::vector<ResolvedChoice>& choices, const std::string& field,
                   const std::string& value, ChoiceSource source, const std::string& reason) {
  choices.push_back({field, value, source, reason});
}
template <class T>
inline void Pick(T& value, const std::optional<T>& override_value, const std::string& field,
                 std::vector<ResolvedChoice>& choices) {
  if (override_value) value = *override_value;
  Choice(choices, field, Value(value), override_value ? ChoiceSource::kExplicit : ChoiceSource::kFallback,
         override_value ? "explicit override" : "uncalibrated_fallback_v2");
}
template <class T>
inline void Derived(std::vector<ResolvedChoice>& choices, const std::string& field,
                    T value, const std::string& reason) {
  for (auto& choice : choices) {
    if (choice.field != field) continue;
    choice.value = Value(value);
    if (choice.source != ChoiceSource::kExplicit) choice.source = ChoiceSource::kDerived;
    choice.reason += "; " + reason;
    return;
  }
  Choice(choices, field, Value(value), ChoiceSource::kDerived, reason);
}
// The budget's spin_before_park_ns, in `unit_ns` units, for a spin the
// overrides leave unset.
template <class T>
inline void BudgetSpin(T& value, const std::optional<T>& override_value, uint64_t spin_ns, uint64_t unit_ns,
                       const std::string& field, std::vector<ResolvedChoice>& choices) {
  if (override_value || spin_ns == 0) return;
  const uint64_t units = std::max<uint64_t>(1, spin_ns / unit_ns);
  Require(units <= std::numeric_limits<T>::max(), field + ": spin_before_park_ns exceeds the field");
  value = static_cast<T>(units);
  Derived(choices, field, value, "the budget's spin_before_park_ns");
}
inline size_t Add(size_t a, size_t b) {
  if (b > std::numeric_limits<size_t>::max() - a) throw std::length_error("configuration byte overflow");
  return a + b;
}
// THE CERTIFICATION REPORT as two choices, `<prefix>certification` (the
// status) and `<prefix>failure_bound_log2` (the conditional bound, or
// "none"), both carrying the report's reason.  A report, not a choice: the
// planner flags an uncovered configuration and builds it anyway.
inline void CertificationChoices(std::vector<ResolvedChoice>& choices, const std::string& prefix,
                                 const la::LevelArenaCertification& c) {
  Choice(choices, prefix + "certification", la::LevelArenaCertificationStatusName(c.status),
         ChoiceSource::kDerived, c.reason);
  Choice(choices, prefix + "failure_bound_log2",
         c.failure_bound_log2_millis ? la::certification_detail::Millis(*c.failure_bound_log2_millis)
                                     : std::string("none"),
         ChoiceSource::kDerived,
         c.failure_bound_log2_millis
             ? "conditional lifetime capacity-failure bound, log2, rounded up; target " +
                   std::to_string(c.target_log2)
             : "no certified record applies; " + prefix + "certification says why");
}
// The report is derived from the configuration and the generated table, so
// it is not part of the configuration's identity: regenerating the table
// must not change a configuration key.
inline bool IsCertificationReport(const std::string& field) {
  auto ends = [&](const std::string& tail) {
    return field.size() >= tail.size() && field.compare(field.size() - tail.size(), tail.size(), tail) == 0;
  };
  return ends("certification") || ends("failure_bound_log2");
}
inline bool IsHierarchy(Scheme s) {
  return s == Scheme::kHierarchicalIncremental || s == Scheme::kHierarchicalSynchronous;
}

struct HierarchyPlan {
  Scheme scheme = Scheme::kHierarchicalIncremental;
  IncrementalSettings incremental;
  SynchronousSettings synchronous;
  la::LevelArenaCapacityChoice arena;
  size_t capacity = 0;
  size_t modeled_bytes = 0;
  // modeled_bytes with each buffer rounded as the allocator is asked for it
  // (AllocateAligned64: 2 MiB for a huge-page buffer, 64 B otherwise).
  size_t reserved_bytes = 0;
  unsigned extra_threads = 0;
  // Accesses between two carries into level l (index l - 1): the unit a
  // measurement window's maintenance coverage is counted in.
  std::vector<uint64_t> carry_periods;
  // What the failure-probability analysis says about this hierarchy
  // (la::CertifyLevelArenaGeometry).  Both schemes run the same jobs.
  la::LevelArenaCertification certification;
};
struct PlanData {
  MapSpec spec;
  ResourceBudget budget;
  WorkloadHint workload;
  Scheme scheme = Scheme::kAuto;
  HierarchyPlan hierarchy;  // top-level hierarchy or the tree's position map
  TreeSettings tree;
  microram::tree::TreeGeometry tree_geometry;
  unsigned payload_workers = 0;
  // Payload workers 0..payload_near_workers-1 want the caller's cache domain;
  // the rest are background (another domain first).
  unsigned payload_near_workers = 0;
  size_t capacity = 0;
  size_t modeled_bytes = 0;
  size_t reserved_bytes = 0;
  PlanCapabilities capabilities;
  std::vector<ResolvedChoice> choices;
  std::vector<PlannedThread> threads;
  std::vector<PlannedMemory> memory;
  std::vector<std::string> rejected_candidates;
  std::string configuration_key;
  // The whole map's certification: the hierarchy's for a hierarchical map,
  // not covered for a tree (whose own bound is not in the analysis; its
  // position map's is `hierarchy.certification`).
  la::LevelArenaCertification certification;
};

// The public Options a resolved incremental hierarchy constructs with; the
// geometry planner reads the same Options, so plan and construction agree.
// The rebuild's division is always explicit here: a budget has already been
// divided by PlanHierarchy, so the library's own budget path stays unused.
inline Options IncrementalOptions(const IncrementalSettings& s, uint64_t horizon) {
  Options options;  // Random engine seed is generated only at construction.
  options.max_accesses = horizon;
#define CPU_ORAM_COPY_I(type, name, default_value, legacy) options.legacy = s.name;
  CPU_ORAM_INCREMENTAL_FIELDS(CPU_ORAM_COPY_I)
#undef CPU_ORAM_COPY_I
  options.deamortized_level_groups = s.level_groups;
  options.deamortized_inline_work_factor = s.inline_work_factor_ppm / 1e6;
  return options;
}
// The same for a synchronous hierarchy: the arena fields alone.
inline Options SynchronousOptions(const SynchronousSettings& s, uint64_t horizon) {
  Options options;  // Random engine seed is generated only at construction.
  options.max_accesses = horizon;
#define CPU_ORAM_COPY_S(type, name, default_value, legacy) options.legacy = s.name;
  CPU_ORAM_SYNCHRONOUS_FIELDS(CPU_ORAM_COPY_S)
#undef CPU_ORAM_COPY_S
  return options;
}

// The arena fields' checks, on either scheme's overrides and the Options
// its settings construct with: zero is the auto sentinel of two Options
// fields, so an explicit zero override is refused here, and every range is
// the one each construction path checks (detail::ValidateArenaOptions),
// reported under this resolver's prefix.  For the incremental scheme that
// includes its rebuild fields.
template <class Overrides>
inline void RequireArenaFields(const Overrides& o, const Options& options, bool synchronous) {
  Require(!o.prefix_flushes || *o.prefix_flushes != 0, "explicit prefix_flushes must be 2,4,8; omit it for auto");
  Require(!o.top_digit || *o.top_digit != 0,
          "explicit top_digit must be 1, 2, 4 or 8, at most branching_factor "
          "(only a binary top has a certified preparation); omit it for auto");
  try {
    detail::ValidateArenaOptions(options, synchronous);
  } catch (const std::invalid_argument& e) {
    Require(false, e.what());
  }
}

// The batch participants an arena scheme's overrides ask for, checked, and
// the tiles they need (which the settings' batch_execution is moved to).
template <class Settings, class Overrides>
inline unsigned PickArenaParticipants(Settings& s, const Overrides& o, unsigned core_slots) {
  const unsigned participants = o.batch_participants.value_or(1);
  Require(participants >= 1 && participants <= kMaxOnlineParticipants && participants <= core_slots,
          "batch participants exceed supported range or core budget");
  if (participants > 1 || o.batch_bucket_scan.value_or(false))
    s.batch_execution = BatchExecutionShape::kParallelTiles;
  const unsigned values = o.value_workers.value_or(0);
  Require(values < core_slots && participants <= core_slots - values,
          "value workers and batch participants exceed core budget");
  return participants;
}
template <class Settings, class Overrides>
inline void NoteArenaTiles(const Settings& s, const Overrides& o, unsigned participants,
                           const std::string& prefix, PlanData& result) {
  if ((participants > 1 || s.batch_bucket_scan) && !o.batch_execution)
    Derived(result.choices, prefix + "batch_execution", static_cast<unsigned>(s.batch_execution),
            "batch helpers or bucket scans require parallel tiles");
}

// What the chosen geometry decided, for either scheme: the ladder's searched
// axes and tier widths as choices, the certification report, the capacity,
// the bill and its roles, and the carry periods.
inline void RecordArena(HierarchyPlan& h, const MapSpec& spec, size_t tier_override,
                        const std::string& prefix, PlanData& result) {
  const auto& g = h.arena.geometry;
  const la::LevelArenaGeometry geometry(g);
  // Keep the original request internally, so construction through Options
  // repeats the same deterministic search; expose the chosen geometry (no
  // sentinel) in the public choices and plan.
  Derived(result.choices, prefix + "prefix_flushes", g.prefix_flushes, "capacity ladder");
  Derived(result.choices, prefix + "top_digit", g.top_digit, "capacity ladder");
  Derived(result.choices, prefix + "levels", g.levels, "capacity ladder");
  if (tier_override == 0)
    Derived(result.choices, prefix + "tier_buckets", g.tier_buckets,
            g.level_tier_buckets.empty() ? "lifetime occupancy sizing across all levels"
                                         : "lifetime occupancy sizing, the widest level's");
  for (size_t i = 0; i < g.level_tier_buckets.size(); ++i)
    Derived(result.choices, prefix + "tier." + std::to_string(i + 1),
            g.level_tier_buckets[i], "lifetime occupancy sizing of the tables this level produces");
  for (size_t i = 0; i < g.level_fanouts.size(); ++i)
    Derived(result.choices, prefix + "fanout." + std::to_string(i + 1),
            g.level_fanouts[i], "capacity ladder");
  h.certification = la::CertifyLevelArenaGeometry(g, spec.max_accesses);
  CertificationChoices(result.choices, prefix, h.certification);
  h.capacity = h.arena.capacity;
  const auto pc = la::LevelArenaPublisherConfig(geometry,
      h.scheme == Scheme::kHierarchicalIncremental ? h.incremental.owner_threads : 0,
      h.scheme == Scheme::kHierarchicalSynchronous);
  const unsigned values = h.scheme == Scheme::kHierarchicalIncremental
      ? h.incremental.value_workers : h.synchronous.value_workers;
  Require(values == 0 || geometry.DensePrefixBuckets() <= la::ValueProgress::kMaxRun,
          "value_workers need prefix_flushes * online_stash_entries / 64 <= 4096 dense prefix buckets");
  h.arena.bill.Add(la::ValueWorkerPool::BufferBytes(values,
      la::LevelArenaStoredLayout(spec.key_bytes, spec.value_bytes, geometry),
      la::LevelArenaPublisher::MaxTablesFor(pc), pc.arena_slots));
  h.modeled_bytes = h.arena.bill.requested();
  h.reserved_bytes = h.arena.bill.reserved();
  for (unsigned l = 1; l <= g.levels; ++l)
    h.carry_periods.push_back(la::CheckedMul(geometry.PrefixProduct(l), geometry.PrefixPositions(),
                                             "carry period"));
  for (size_t i = 0; i < kLevelArenaByteRoles; ++i)
    result.memory.push_back({prefix + LevelArenaByteRoleName(static_cast<LevelArenaByteRole>(i)),
                            h.arena.bill.At(static_cast<LevelArenaByteRole>(i))});
}
// An explicit knob whose only effect needs a resource the plan does not have
// is rejected rather than silently ignored (CONFIGURATION.md, "Selection and
// overrides").
template <class T>
inline void RequireEffective(const std::optional<T>& knob, bool effective, const std::string& field,
                             const char* needs) {
  Require(!knob || effective, "explicit " + field + " has no effect without " + needs);
}

// The library cores on each side of a near/far boundary, from the declared
// cache domains: the caller's domain less the harness, and every other
// domain. Zero near cores is one domain, where nothing is capped.
struct DomainSplit {
  unsigned near_cores = 0;  // includes the caller and its batch helpers
  unsigned far_cores = 0;
};
inline DomainSplit SplitDomains(const ResourceBudget& budget) {
  if (budget.cache_domains <= 1) return {};
  const unsigned per_domain = budget.cores / budget.cache_domains;
  return {per_domain - budget.harness_cores, budget.cores - per_domain};
}
// The heuristic's inputs that are not configuration: two budgets, two caps or
// two cost models that divide the levels the same way (and give the same
// slice rate, which is a choice of its own) are the same configuration.  The
// slice line cost is not one of them: the engine sizes its pieces with it,
// and nothing derived from it is in the plan.
inline bool IsRebuildBudgetInput(const std::string& field, const std::string& prefix) {
  return field == prefix + "rebuild_threads" || field == prefix + "near_rebuild_threads_cap" ||
         field == prefix + "far_rebuild_threads_cap" ||
         (field.rfind(prefix + "rebuild_cost_", 0) == 0 && field != prefix + "rebuild_cost_slice_line_picos");
}

// A plan that asks for monitor-wait needs the capability declared in the
// budget; the declared kind is recorded as a derived choice.
inline void RequireMonitorWait(bool requested, const ResourceBudget& budget, const std::string& field,
                               PlanData& result) {
  if (!requested) return;
  Require(budget.monitor_wait != microram::core::MonitorWaitKind::kNone,
          field + " needs a declared monitor-wait capability (umwait or mwaitx)");
  Derived(result.choices, field + "_kind", std::string(microram::core::MonitorWaitKindName(budget.monitor_wait)),
          "declared target capability");
}

// Plans one hierarchy (the map itself, or a tree's position map) within
// `core_slots` cores, recording every choice under `prefix`.
// `whole_budget` is false for a tree's position map, which keeps
// kTreePositionRebuildThreads rebuild threads; the top-level hierarchy gets
// every core its caller and batch helpers leave. `domains` caps a budget's
// sides under an explicit near/far boundary (the top-level hierarchy only).
inline HierarchyPlan PlanHierarchy(const MapSpec& spec, Scheme scheme, unsigned core_slots,
                                  const IncrementalOverrides& io, const SynchronousOverrides& so,
                                  const std::string& prefix, PlanData& result, bool whole_budget = true,
                                  DomainSplit domains = {}) {
  Require(core_slots >= 1, "no core for hierarchy caller");
  RequireMonitorWait(scheme == Scheme::kHierarchicalIncremental ? io.value_monitor_wait.value_or(false)
                                                                : so.value_monitor_wait.value_or(false),
                     result.budget, prefix + "value_monitor_wait", result);
  HierarchyPlan h;
  h.scheme = scheme;
  if (scheme == Scheme::kHierarchicalIncremental) {
    auto& s = h.incremental;
    const unsigned participants = PickArenaParticipants(s, io, core_slots);
    const unsigned available = core_slots - participants - io.value_workers.value_or(0);
    // HOW MANY REBUILD THREADS is one question with one answer: a thread
    // budget that the library's load heuristic divides into owner groups, top
    // helpers and lanes (HeuristicRebuildParams), or an explicit owner count
    // whose division, helpers and lanes the caller may then pin.
    Require(!io.rebuild_threads || !io.owner_threads,
            "explicit rebuild_threads and owner_threads conflict; a thread budget chooses the owners");
    const bool budgeted = !io.owner_threads;
    Require(!budgeted || (!io.level_groups && !io.top_helpers && !io.bottom_helpers &&
                          !io.rebuild_lanes && !io.lane_min_buckets),
            "explicit level_groups, top_helpers, bottom_helpers, rebuild_lanes or lane_min_buckets "
            "need explicit owner_threads; a rebuild thread budget chooses them");
#define CPU_ORAM_PICK_I(type, name, default_value, legacy) Pick(s.name, io.name, prefix + #name, result.choices);
    CPU_ORAM_INCREMENTAL_FIELDS(CPU_ORAM_PICK_I)
#undef CPU_ORAM_PICK_I
    for (auto [value, override_value, name] : {std::tuple{&s.owner_spin_ns, &io.owner_spin_ns, "owner_spin_ns"},
                                               std::tuple{&s.batch_spin_ns, &io.batch_spin_ns, "batch_spin_ns"},
                                               std::tuple{&s.value_spin_ns, &io.value_spin_ns, "value_spin_ns"}})
      BudgetSpin(*value, *override_value, result.budget.spin_before_park_ns, 1, prefix + name, result.choices);
    Pick(s.inline_work_factor_ppm, io.inline_work_factor_ppm, prefix + "inline_work_factor_ppm", result.choices);
    // The rebuild cost model, checked before anything divides by it.
    const la::LevelArenaRebuildCost cost = IncrementalOptions(s, spec.max_accesses).deamortized_rebuild_cost;
    cost.Validate();
    if (io.level_groups) s.level_groups = *io.level_groups;
    if (budgeted) {
      s.rebuild_threads = io.rebuild_threads.value_or(whole_budget ? available
                                                                  : std::min(kTreePositionRebuildThreads, available));
      Choice(result.choices, prefix + "rebuild_threads", Value(s.rebuild_threads),
             io.rebuild_threads ? ChoiceSource::kExplicit : ChoiceSource::kFallback,
             io.rebuild_threads ? "explicit override" : whole_budget ?
             "uncalibrated_fallback_v2: every core the caller and batch helpers leave" :
             "uncalibrated_fallback_v2: a tree's position map keeps two rebuild threads");
      Require(s.rebuild_threads <= available, "rebuild threads and batch helpers exceed core budget");
    }
    NoteArenaTiles(s, io, participants, prefix, result);
    RequireArenaFields(io, IncrementalOptions(s, spec.max_accesses), /*synchronous=*/false);
    Require(s.near_max_level != kNearMaxLevelAuto, "host-auto near boundary is not a resolved public input");
    Require(s.owner_threads <= available, "owners and batch helpers exceed core budget");
    Require(uint64_t{s.owner_threads} + s.top_helpers + s.bottom_helpers <= available,
            "owners, top and bottom helpers and batch helpers exceed core budget");
    Require(!io.level_groups || s.level_groups.size() == s.owner_threads,
            "explicit level_groups must hold owner_threads groups");
    // A BUDGET IS DIVIDED ON A GEOMETRY, and the division's group count and
    // lanes are terms of the bill that chooses the geometry, so the library
    // plans both together (PlanArenaGeometry's budget path).  Its answer is
    // then pinned, and the explicit plan below must land on the same geometry.
    std::optional<la::LevelArenaCapacityChoice> budget_choice;
    if (budgeted && s.rebuild_threads > 0) {
      Options options = IncrementalOptions(s, spec.max_accesses);
      options.deamortized_rebuild_threads = s.rebuild_threads;
      if (s.near_max_level != 0 && domains.near_cores != 0) {
        // The caller and its batch helpers are near too; near/far placement
        // would otherwise spill the excess of either side onto the other.
        Require(domains.near_cores > participants + s.value_workers,
                "the caller's cache domain holds no core for a near rebuild thread");
        options.deamortized_near_rebuild_threads = domains.near_cores - participants - s.value_workers;
        options.deamortized_far_rebuild_threads = domains.far_cores;
        const char* why = "declared cache domains under an explicit near/far boundary";
        Derived(result.choices, prefix + "near_rebuild_threads_cap", options.deamortized_near_rebuild_threads, why);
        Derived(result.choices, prefix + "far_rebuild_threads_cap", options.deamortized_far_rebuild_threads, why);
      }
      budget_choice = detail::PlanArenaGeometry(spec.requested_capacity, spec.key_bytes, spec.value_bytes, options);
      const la::LevelArenaRebuildParams params = detail::BudgetRebuildParams(*budget_choice, options);
      s.owner_threads = static_cast<unsigned>(params.groups.size());
      s.level_groups = params.groups;
      s.top_helpers = params.top_helpers;
      s.rebuild_lanes = params.lanes.lanes;
      s.lane_min_buckets = params.lanes.min_buckets;
      const char* why = "rebuild thread budget divided by the load heuristic (HeuristicRebuildParams)";
      Derived(result.choices, prefix + "owner_threads", s.owner_threads, why);
      Derived(result.choices, prefix + "top_helpers", s.top_helpers, why);
      Derived(result.choices, prefix + "rebuild_lanes", s.rebuild_lanes, why);
      Derived(result.choices, prefix + "lane_min_buckets", s.lane_min_buckets, why);
    } else if (budgeted) {
      Derived(result.choices, prefix + "owner_threads", 0u, "a zero rebuild thread budget runs the rebuild inline");
    }
    // Capacity selection and the requested-byte report do not depend on the
    // process huge-page policy, which the benchmark never changes mid-process.
    h.arena = detail::PlanArenaGeometry(spec.requested_capacity, spec.key_bytes, spec.value_bytes,
                                        IncrementalOptions(s, spec.max_accesses));
    const auto& g = h.arena.geometry;
    if (budget_choice && (g.levels != budget_choice->geometry.levels ||
                          g.level_fanouts != budget_choice->geometry.level_fanouts ||
                          g.prefix_flushes != budget_choice->geometry.prefix_flushes ||
                          g.top_digit != budget_choice->geometry.top_digit ||
                          g.tier_buckets != budget_choice->geometry.tier_buckets ||
                          g.level_tier_buckets != budget_choice->geometry.level_tier_buckets ||
                          h.arena.bill.requested() != budget_choice->bill.requested()))
      throw std::logic_error("configuration: the rebuild budget's division did not converge on one geometry");
    Require(s.near_max_level <= g.levels, "explicit near boundary exceeds selected geometry");
    const la::LevelArenaGeometry geometry(g);
    // The engine divides an explicit owner count by the same load model; the
    // plan names that division so that placement and exact replay see it.
    if (s.owner_threads > 0 && s.level_groups.empty()) {
      const unsigned top_threads = s.rebuild_lanes > 1 ? 1 + s.top_helpers : 1;
      s.level_groups = la::PlanLevelGroups(geometry, h.arena.layout, s.owner_threads,
                                           std::min(s.near_max_level, g.levels), top_threads, cost,
                                           la::LevelResidualInputs{spec.max_accesses});
    }
    if (io.level_groups)
      Choice(result.choices, prefix + "level_groups", GroupsText(s.level_groups), ChoiceSource::kExplicit,
             "explicit override");
    else if (!s.level_groups.empty())
      Derived(result.choices, prefix + "level_groups", GroupsText(s.level_groups),
              "load heuristic division of the chosen geometry");
    // The cost model chooses a division and helpers the plan did not pin,
    // and a slice rate it did not name; with both pinned it chooses nothing.
    const bool divides = s.owner_threads > 0 && !io.level_groups;
    const bool rates = s.owner_threads > 0 && !io.slice_target_rate;
    RequireEffective(io.rebuild_cost_line_picos, divides, prefix + "rebuild_cost_line_picos",
                     "owner threads whose division is not explicit");
    RequireEffective(io.rebuild_cost_residual_line_picos, divides, prefix + "rebuild_cost_residual_line_picos",
                     "owner threads whose division is not explicit");
    RequireEffective(io.rebuild_cost_offer_line_picos, divides, prefix + "rebuild_cost_offer_line_picos",
                     "owner threads whose division is not explicit");
    RequireEffective(io.rebuild_cost_job_nanos, divides, prefix + "rebuild_cost_job_nanos",
                     "owner threads whose division is not explicit");
    RequireEffective(io.rebuild_cost_middle_burst_ppm, divides, prefix + "rebuild_cost_middle_burst_ppm",
                     "owner threads whose division is not explicit");
    RequireEffective(io.rebuild_cost_helper_speedup_ppm, divides, prefix + "rebuild_cost_helper_speedup_ppm",
                     "owner threads whose division is not explicit");
    RequireEffective(io.rebuild_cost_max_top_threads, divides && budgeted,
                     prefix + "rebuild_cost_max_top_threads", "a rebuild thread budget");
    RequireEffective(io.rebuild_cost_thread_gain_floor_ppm, divides && budgeted,
                     prefix + "rebuild_cost_thread_gain_floor_ppm", "a rebuild thread budget");
    RequireEffective(io.rebuild_cost_probe_bucket_picos, rates, prefix + "rebuild_cost_probe_bucket_picos",
                     "owner threads whose slice_target_rate is not explicit");
    RequireEffective(io.rebuild_cost_probe_line_picos, rates, prefix + "rebuild_cost_probe_line_picos",
                     "owner threads whose slice_target_rate is not explicit");
    RequireEffective(io.rebuild_cost_slice_line_picos, s.owner_threads > 0 && !io.slice_touches,
                     prefix + "rebuild_cost_slice_line_picos", "owner threads whose slice_touches is not explicit");
    RequireEffective(io.near_max_level, s.owner_threads > 0, prefix + "near_max_level", "owner threads");
    RequireEffective(io.owner_spin_ns, s.owner_threads > 0, prefix + "owner_spin_ns", "owner threads");
    RequireEffective(io.slice_target_rate, s.owner_threads > 0, prefix + "slice_target_rate", "owner threads");
    RequireEffective(io.slice_touches, s.owner_threads > 0, prefix + "slice_touches", "owner threads");
    RequireEffective(io.inline_work_factor_ppm, s.owner_threads == 0, prefix + "inline_work_factor_ppm",
                     "the inline executor (zero owner threads)");
    RequireEffective(io.lane_min_buckets, s.rebuild_lanes > 1, prefix + "lane_min_buckets",
                     "more than one rebuild lane");
    if (s.top_helpers > 0) {
      // Helpers share the lanes of the top's group; with none they never start.
      Require(s.owner_threads > 0, "top_helpers need owner threads");
      const la::LevelLaneConfig lanes{s.rebuild_lanes, s.lane_min_buckets};
      const auto& top = s.level_groups.front();
      bool laned = false;
      for (unsigned l = top.first; l <= top.last; ++l) laned = laned || la::LevelLaneCount(geometry, l, lanes) > 1;
      Require(laned, "top_helpers have no effect without a laned table in the top level's group "
                     "(rebuild_lanes > 1 and a table of at least lane_min_buckets)");
      // The library cuts helpers to the cores the others leave; a plan may
      // not count on more than its declared budget holds.
      Require(uint64_t{s.owner_threads} + s.top_helpers <= available,
              "owners, top helpers and batch helpers exceed core budget");
    }
    if (s.bottom_helpers > 0) {
      // Level 1's group's helpers: its own group, with laned tables.
      Require(s.owner_threads > 1, "bottom_helpers need level 1 in an owner group of its own");
      const la::LevelLaneConfig lanes{s.rebuild_lanes, s.lane_min_buckets};
      const auto& bottom = s.level_groups.back();
      bool laned = false;
      for (unsigned l = bottom.first; l <= bottom.last; ++l) laned = laned || la::LevelLaneCount(geometry, l, lanes) > 1;
      Require(laned, "bottom_helpers have no effect without a laned table in level 1's group "
                     "(rebuild_lanes > 1 and a table of at least lane_min_buckets)");
      Require(uint64_t{s.owner_threads} + s.top_helpers + s.bottom_helpers <= available,
              "owners, top and bottom helpers and batch helpers exceed core budget");
    }
    if (s.owner_threads > 0 && !io.slice_target_rate)
      Derived(result.choices, prefix + "slice_target_rate",
              static_cast<uint64_t>(std::llround(la::SaturatedOnlineRate(geometry, h.arena.layout, cost))),
              "saturated sequential requester rate of the chosen geometry");
    RecordArena(h, spec, s.tier_buckets, prefix, result);
    // The heuristic may spend fewer threads than its budget.
    Derived(result.choices, prefix + "rebuild_threads_used",
            s.owner_threads + s.top_helpers + s.bottom_helpers,
            "owner groups plus top and bottom helpers");
    h.extra_threads = s.owner_threads + s.top_helpers + s.bottom_helpers + participants - 1;
  } else {
    // THE SYNCHRONOUS SCHEME is the same engine's synchronous storage mode:
    // the same ladder, priced for that mode, the same jobs and so the same
    // certification, and no rebuild thread at all.
    auto& s = h.synchronous;
    const unsigned participants = PickArenaParticipants(s, so, core_slots);
#define CPU_ORAM_PICK_S(type, name, default_value, legacy) Pick(s.name, so.name, prefix + #name, result.choices);
    CPU_ORAM_SYNCHRONOUS_FIELDS(CPU_ORAM_PICK_S)
#undef CPU_ORAM_PICK_S
    for (auto [value, override_value, name] : {std::tuple{&s.batch_spin_ns, &so.batch_spin_ns, "batch_spin_ns"},
                                               std::tuple{&s.value_spin_ns, &so.value_spin_ns, "value_spin_ns"}})
      BudgetSpin(*value, *override_value, result.budget.spin_before_park_ns, 1, prefix + name, result.choices);
    NoteArenaTiles(s, so, participants, prefix, result);
    RequireArenaFields(so, SynchronousOptions(s, spec.max_accesses), /*synchronous=*/true);
    h.arena = detail::PlanArenaGeometry(spec.requested_capacity, spec.key_bytes, spec.value_bytes,
                                        SynchronousOptions(s, spec.max_accesses), /*synchronous=*/true);
    RecordArena(h, spec, s.tier_buckets, prefix, result);
    h.extra_threads = participants - 1;
  }
  Derived(result.choices, prefix + "actual_capacity", h.capacity, "geometry");
  return h;
}

inline microram::tree::TreeKnobs TreeKnobs(const TreeSettings& s) {
  microram::tree::TreeKnobs k;
  k.fold = s.fold;
  k.leaf_scale = s.leaf_scale;
  k.shape.max_load = s.max_load_ppm / 1000000.0;
  k.shape.max_folded_slots = s.max_folded_slots;
  k.shape.stash_registers = s.stash_registers;
  k.prefetch_ahead = s.prefetch_ahead;
  k.payload_max_threads = s.payload_max_threads;
  k.payload_threshold = s.payload_threshold;
  k.payload_spin_micros = s.payload_spin_us;
  k.payload_monitor_wait = s.payload_monitor_wait;
  return k;
}

inline void AddThreads(PlanData& d) {
  auto add = [&](ThreadRole role, unsigned count) {
    for (unsigned i = 0; i < count; ++i) {
      std::optional<unsigned> cpu;
      if (!d.budget.cpu_ids.empty()) cpu = d.budget.cpu_ids.at(d.threads.size());
      d.threads.push_back({role, i, cpu});
    }
  };
  add(ThreadRole::kCaller, 1);
  const bool tree = d.scheme == Scheme::kTree;
  const auto& h = d.hierarchy;
  if (h.scheme == Scheme::kHierarchicalIncremental) {
    // Owner i drives group i, highest first; the top group's helpers follow its
    // owner, so a policy filling slots in role order keeps them together.
    const auto& s = h.incremental;
    const auto owner = tree ? ThreadRole::kPositionOwner : ThreadRole::kOwner;
    auto rebuild = [&](ThreadRole role, unsigned index, unsigned group) {
      std::optional<unsigned> cpu;
      if (!d.budget.cpu_ids.empty()) cpu = d.budget.cpu_ids.at(d.threads.size());
      std::optional<bool> near;
      if (s.near_max_level != 0) near = la::GroupIsNear(s.level_groups.at(group), s.near_max_level);
      d.threads.push_back({role, index, cpu, near});
    };
    for (unsigned g = 0; g < s.owner_threads; ++g) {
      rebuild(owner, g, g);
      if (g == 0)
        for (unsigned i = 0; i < s.top_helpers; ++i)
          rebuild(tree ? ThreadRole::kPositionTopHelper : ThreadRole::kTopHelper, i, 0);
      if (g + 1 == s.owner_threads)
        for (unsigned i = 0; i < s.bottom_helpers; ++i)
          rebuild(tree ? ThreadRole::kPositionBottomHelper : ThreadRole::kBottomHelper, i, g);
    }
    add(tree ? ThreadRole::kPositionOnlineHelper : ThreadRole::kOnlineHelper,
        s.batch_participants - 1);
  } else {
    add(tree ? ThreadRole::kPositionOnlineHelper : ThreadRole::kOnlineHelper,
        h.synchronous.batch_participants - 1);
  }
  add(tree ? ThreadRole::kPositionValue : ThreadRole::kValue,
      h.scheme == Scheme::kHierarchicalIncremental ? h.incremental.value_workers : h.synchronous.value_workers);
  for (unsigned i = 0; i < d.payload_workers; ++i) {
    std::optional<unsigned> cpu;
    if (!d.budget.cpu_ids.empty()) cpu = d.budget.cpu_ids.at(d.threads.size());
    std::optional<bool> near;
    if (i < d.payload_near_workers) near = true;
    d.threads.push_back({ThreadRole::kPayload, i, cpu, near});
  }
}

inline PlanData Candidate(const MapSpec& spec, const ResourceBudget& budget,
                          const WorkloadHint& workload, const OptionOverrides& o, Scheme scheme) {
  const bool auto_selection = o.scheme == Scheme::kAuto;
  PlanData d;
  d.spec = spec; d.budget = budget; d.workload = workload; d.scheme = scheme;
  const unsigned cores = budget.cores - budget.harness_cores;
  if (scheme != Scheme::kTree) {
    d.hierarchy = PlanHierarchy(spec, scheme, cores, o.incremental.value_or(IncrementalOverrides{}),
                               o.synchronous.value_or(SynchronousOverrides{}), "hierarchy.", d,
                               /*whole_budget=*/true, SplitDomains(budget));
    d.capacity = d.hierarchy.capacity;
    d.modeled_bytes = d.hierarchy.modeled_bytes;
    d.reserved_bytes = d.hierarchy.reserved_bytes;
    d.capabilities.direct_initialization = true;
    const BatchExecutionShape shape = scheme == Scheme::kHierarchicalSynchronous
                                          ? d.hierarchy.synchronous.batch_execution
                                          : d.hierarchy.incremental.batch_execution;
    d.capabilities.batch_execution_path =
        shape == BatchExecutionShape::kParallelTiles ? "parallel_tiles" : "chunked_cascade";
  } else {
    const auto to = o.tree.value_or(TreeOverrides{});
    Require(spec.max_accesses <= (uint64_t{1} << 32),
            "tree access horizons above 2^32 require a validated security policy");
    const auto& po = to.position_map;
    const Scheme position = po.mode.value_or(Scheme::kHierarchicalIncremental);
    Require(IsHierarchy(position), "tree position map must name a hierarchy mode");
    Require(position == Scheme::kHierarchicalIncremental || !po.incremental, "irrelevant incremental position overrides");
    Require(position == Scheme::kHierarchicalSynchronous || !po.synchronous, "irrelevant synchronous position overrides");
    const auto io = po.incremental.value_or(IncrementalOverrides{});
    const auto so = po.synchronous.value_or(SynchronousOverrides{});
    // Explicit nested pools reserve their slots before any payload defaults.
    const bool incremental = position == Scheme::kHierarchicalIncremental;
    const uint64_t participants = uint64_t{incremental ? io.batch_participants.value_or(1)
                                              : so.batch_participants.value_or(1)} +
        (incremental ? io.value_workers.value_or(0) : so.value_workers.value_or(0));
    const uint64_t owners = !incremental ? 0
                            : io.owner_threads ? uint64_t{*io.owner_threads} + io.top_helpers.value_or(0) +
                                                     io.bottom_helpers.value_or(0)
                                               : io.rebuild_threads.value_or(0);
    Require(participants >= 1, "invalid nested thread count");
    const uint64_t reserved = uint64_t{participants - 1} + owners;
    Require(reserved < cores, "position-map workers leave no caller core");
    // ONE CACHE DOMAIN: no fixed cap.  The workers take every core the caller
    // and the position map's rebuild threads leave, and at least
    // min(8, free), so the position map's default reservation does not starve
    // the payload of a small budget.
    const unsigned free_cores = cores - 1 - static_cast<unsigned>(reserved);
    const unsigned rebuild = incremental && !io.owner_threads && !io.rebuild_threads ? kTreePositionRebuildThreads : 0;
    d.tree.payload_max_threads = std::max(std::min(8u, free_cores), free_cores > rebuild ? free_cores - rebuild : 0u);
    // SEVERAL CACHE DOMAINS: the caller waits for every payload worker's
    // hand-off on each access, and one worker in another domain costs the
    // whole cross-domain round trip at any width.  So the workers fill the
    // caller's domain first, and only a value wide enough to be bound by one
    // domain's memory link (kTreePayloadSpreadBytes) spreads over the others
    // too.  The position map's rebuild threads are background and take far
    // cores first.
    const DomainSplit domains = SplitDomains(budget);
    unsigned near_payload = 0, far_payload = 0;
    if (domains.near_cores != 0) {
      const uint64_t background = !incremental ? 0
          : io.owner_threads || io.rebuild_threads ? owners : kTreePositionRebuildThreads;
      near_payload = domains.near_cores > participants ? domains.near_cores - static_cast<unsigned>(participants) : 0;
      far_payload = domains.far_cores > background ? domains.far_cores - static_cast<unsigned>(background) : 0;
      d.tree.payload_max_threads = std::min(cores - 1 - static_cast<unsigned>(reserved),
          spec.value_bytes >= kTreePayloadSpreadBytes ? near_payload + far_payload : near_payload);
    }
#define CPU_ORAM_PICK_T(type, name, default_value, legacy) Pick(d.tree.name, to.name, "tree." #name, d.choices);
    CPU_ORAM_TREE_FIELDS(CPU_ORAM_PICK_T)
#undef CPU_ORAM_PICK_T
    auto& s = d.tree;
    // Auto stands in for the default hybrid Map<>, so it uses the hybrid's
    // longer payload spin (kHybridTreePayloadSpinMicros) too.
    if (auto_selection && !to.payload_spin_us) {
      s.payload_spin_us = kHybridTreePayloadSpinMicros;
      Derived(d.choices, "tree.payload_spin_us", s.payload_spin_us, "auto selection uses the hybrid map's spin");
    }
    // At most the stash lanes of the widest stash less one; the geometry
    // checks it against the stash actually chosen.
    Require(!to.max_folded_slots ||
                *to.max_folded_slots <= 64 * microram::tree::kMaxStashRegisters - 1,
            "invalid max_folded_slots");
    // 0, for fold and stash_registers, is the default rule's, as unset is.
    Require(!to.stash_registers || *to.stash_registers == 0 ||
                (*to.stash_registers >= microram::tree::kMinStashRegisters &&
                 *to.stash_registers <= microram::tree::kMaxStashRegisters),
            "invalid stash_registers");
    Require(!to.max_load_ppm || (*to.max_load_ppm > 0 && *to.max_load_ppm <= 1000000), "invalid max_load_ppm");
    Require(!to.uid_from_key || !*to.uid_from_key || spec.key_bytes <= kUidKeyBytes,
            "explicit key-derived UID is unsupported for keys wider than eight bytes");
    RequireMonitorWait(s.payload_monitor_wait, budget, "tree.payload_monitor_wait", d);
    if (s.uid_from_key && spec.key_bytes > kUidKeyBytes) {
      s.uid_from_key = false;
      Derived(d.choices, "tree.uid_from_key", false, "wide keys require counter UIDs");
    }
    auto knobs = TreeKnobs(s);
    Require(!to.max_load_ppm || knobs.shape.max_load <= 0.5,
            "explicit load exceeds the measured load of one half");
    d.tree_geometry = microram::tree::TreeGeometry::ForCapacity(
        std::max(spec.requested_capacity, kTreeMinimumCapacity), knobs.fold, spec.value_bytes,
        knobs.leaf_scale, knobs.shape);
    knobs.shape = d.tree_geometry.shape;
    microram::tree::ValidateReadPathConfiguration(d.tree_geometry, knobs);
    if (!to.fold || *to.fold == 0)
      Derived(d.choices, "tree.fold", d.tree_geometry.fold, "default rule for the tree's depth");
    if (!to.stash_registers || *to.stash_registers == 0)
      Derived(d.choices, "tree.stash_registers", d.tree_geometry.shape.stash_registers,
              "default rule for the tree's depth and fold");
    const auto slices = microram::tree::SliceLayout::For(d.tree_geometry.chunks(),
        microram::tree::PayloadThreadCount(spec.value_bytes, knobs));
    d.payload_workers = slices.payload_planes();
    RequireEffective(to.payload_spin_us, d.payload_workers > 0, "tree.payload_spin_us", "payload workers");
    if (d.payload_workers > 0)
      BudgetSpin(s.payload_spin_us, to.payload_spin_us, budget.spin_before_park_ns, 1000, "tree.payload_spin_us",
                 d.choices);
    RequireEffective(to.payload_near, d.payload_workers > 0, "tree.payload_near", "payload workers");
    if (to.payload_near) {
      d.payload_near_workers = *to.payload_near ? d.payload_workers : 0;
      Choice(d.choices, "tree.payload_near", Value(*to.payload_near), ChoiceSource::kExplicit, "explicit override");
    } else if (domains.near_cores != 0 && d.payload_workers > 0) {
      d.payload_near_workers = std::min(d.payload_workers, near_payload);
      Derived(d.choices, "tree.payload_near_workers", d.payload_near_workers,
              "caller's cache domain first; others only at value_bytes >= " +
              std::to_string(kTreePayloadSpreadBytes));
    }
    RequireEffective(to.payload_threshold, s.payload_max_threads > 0, "tree.payload_threshold",
                     "a nonzero payload worker cap");
    Require(d.payload_workers + reserved < cores, "tree payload and nested workers exceed core budget");
    d.capacity = d.tree_geometry.capacity();
    const size_t position_bytes = microram::tree::PositionEntry::StoredBytes(s.uid_from_key,
                                                                          d.tree_geometry.leaf_bits);
    const MapSpec ps{d.capacity, spec.key_bytes, position_bytes, spec.max_accesses};
    d.hierarchy = PlanHierarchy(ps, position, cores - d.payload_workers, io, so, "position_map.", d,
                                /*whole_budget=*/false);
    // Each plane allocates its buckets and its stash separately
    // (TreeStorage::Create), so each rounds on its own.
    size_t tree_bytes = 0, tree_reserved = 0;
    for (const auto& range : slices.ranges) {
      const auto slice = d.tree_geometry.ForSlice(range.begin, range.count);
      tree_bytes = Add(tree_bytes, slice.arena_bytes());
      tree_reserved = Add(tree_reserved, Add(microram::byteslice::Aligned64AllocationBytes(slice.bucket_bytes_total()),
                                             microram::byteslice::Aligned64AllocationBytes(slice.stash_bytes())));
    }
    d.memory.push_back({"tree.arenas", tree_bytes, MemoryCoverage::kModeled});
    d.modeled_bytes = Add(tree_bytes, d.hierarchy.modeled_bytes);
    d.reserved_bytes = Add(tree_reserved, d.hierarchy.reserved_bytes);
    d.capabilities.batch_position_map = true;
    d.capabilities.batch_execution_path = d.capabilities.batch_position_map ?
        "batched_position_map_then_ordered_tree" : "ordered_scalar";
    Derived(d.choices, "tree.max_load_ppm", static_cast<uint64_t>(d.tree_geometry.shape.target_load() * 1000000), "shape load");
    Derived(d.choices, "tree.path_slots", d.tree_geometry.path_slots(), "resolved path slots");
    Derived(d.choices, "tree.leaf_bits", d.tree_geometry.leaf_bits, "tree geometry");
    Derived(d.choices, "tree.payload_workers", d.payload_workers, "width, cap, and available payload chunks");
    Derived(d.choices, "tree.uid_from_key_effective", s.uid_from_key, "key width");
    Derived(d.choices, "position_map.mode", static_cast<unsigned>(position), "nested mode");
    Derived(d.choices, "position_map.value_bytes", position_bytes, "leaf bits and UID representation");
  }
  d.certification = scheme == Scheme::kTree
      ? la::LevelArenaNotCovered("the tree ORAM's own capacity bound is not in the level-arena "
                                 "certification; position_map.certification reports its position map")
      : d.hierarchy.certification;
  CertificationChoices(d.choices, "", d.certification);
  // Every engine's figure is a bill, so the budget holds for all of them.
  if (budget.modeled_buffer_limit_bytes) {
    Require(d.modeled_bytes <= *budget.modeled_buffer_limit_bytes, "modeled buffers exceed budget");
  }
  AddThreads(d);
  Require(d.threads.size() <= cores, "total thread roles exceed core budget");
  return d;
}
// Length-prefix every field so keys cannot collide through embedded delimiters.
inline void KeyField(std::string& key, const std::string& value) {
  key += std::to_string(value.size()) + ":" + value;
}
// Placement-independent: CPU slots are chosen per run and recorded separately,
// so a plan resolved without slots and the same plan placed share a key.
inline std::string ConfigurationKey(const PlanData& d) {
  std::string key = "oram_configuration_v1;";
  KeyField(key, Value(d.scheme)); KeyField(key, Value(d.capacity));
  KeyField(key, Value(d.modeled_bytes));
  // An incremental rebuild budget and its domain caps are only the
  // heuristic's inputs: two that resolve to the same division are the same
  // configuration.
  const std::string prefix = d.scheme == Scheme::kTree ? "position_map." : "hierarchy.";
  const bool incremental = d.hierarchy.scheme == Scheme::kHierarchicalIncremental;
  std::vector<std::pair<std::string,std::string>> choices;
  for (const auto& choice : d.choices)
    if ((!incremental || !IsRebuildBudgetInput(choice.field, prefix)) && !IsCertificationReport(choice.field))
      choices.emplace_back(choice.field, choice.value);
  std::sort(choices.begin(), choices.end());
  for (const auto& choice : choices) { KeyField(key, choice.first); KeyField(key, choice.second); }
  for (const auto& thread : d.threads) {
    KeyField(key, Value(thread.role)); KeyField(key, Value(thread.index));
  }
  return key;
}
}  // namespace configuration_detail

class ConfiguredByteMap;
class ResolvedPlan;
namespace configuration_detail { struct PlanEngineOptions; }
ResolvedPlan resolve_options(const MapSpec&, const ResourceBudget&, const WorkloadHint&,
                             const OptionOverrides&);

// THE RESULT OF resolve_options.  A read-only, copyable value object: exact
// replay takes this complete plan, not a bag of possibly edited options, and
// `make_map(plan)` constructs a fresh map from it (with a fresh random seed).
// There is no persisted exact-plan import.  Everything in it is a function of
// the public inputs.
class ResolvedPlan {
 public:
  const MapSpec& spec() const { return data_.spec; }
  const ResourceBudget& budget() const { return data_.budget; }
  const WorkloadHint& workload() const { return data_.workload; }
  Scheme scheme() const { return data_.scheme; }
  size_t actual_capacity() const { return data_.capacity; }
  size_t modeled_buffer_bytes() const { return data_.modeled_bytes; }
  // The same buffers as the allocator is asked for them: each rounded to its
  // alignment, 2 MiB for a huge-page buffer (MICRORAM_HUGE_PAGES).  Still no
  // engine objects, containers, thread stacks or allocator headers; the
  // allocation audit (benchmarks/oram/cpu_oram_allocation_audit.cpp) measures
  // what that leaves out.
  size_t modeled_reserved_bytes() const { return data_.reserved_bytes; }
  const std::vector<PlannedMemory>& memory_components() const { return data_.memory; }
  const std::vector<PlannedThread>& threads() const { return data_.threads; }
  const std::vector<ResolvedChoice>& choices() const { return data_.choices; }
  const std::vector<std::string>& rejected_candidates() const { return data_.rejected_candidates; }
  const PlanCapabilities& capabilities() const { return data_.capabilities; }
  // The name of the fallback-default policy that every kFallback choice and
  // the default rule (default_rule.hpp) belong to.
  const char* policy_id() const { return "uncalibrated_fallback_v2"; }
  const std::string& configuration_key() const { return data_.configuration_key; }
  unsigned payload_workers() const { return data_.payload_workers; }
  // Accesses between carries into each level 1..L of the hierarchy, lowest
  // first, for either scheme. For a tree they are its position map's,
  // counted in position-map accesses (TreeByteMap::position_map_access_count).
  // The last entry is the top's rebuild period, so a window's coverage of it
  // is accesses / that period.
  const std::vector<uint64_t>& carry_period_accesses() const { return data_.hierarchy.carry_periods; }
  // WHAT THE FAILURE-PROBABILITY ANALYSIS SAYS about this plan: certified
  // (conditional bound at most 2^-64 over the horizon), above the target,
  // or not covered, with the bound and the first unmet requirement.  Every
  // bound is conditional on the certification checker's undischarged
  // premises (the unconditional bound is 1).  The planner never refuses an
  // uncovered configuration; it reports it here and in the choices
  // (`certification`, `failure_bound_log2`, and the same under the
  // hierarchy's prefix).  certification() is the whole map's: the
  // hierarchy's for a hierarchical map, not covered for a tree.
  // hierarchy_certification() is the hierarchy's alone: the map's
  // own, or a tree's position map.
  const la::LevelArenaCertification& certification() const { return data_.certification; }
  const la::LevelArenaCertification& hierarchy_certification() const {
    return data_.hierarchy.certification;
  }
 private:
  explicit ResolvedPlan(configuration_detail::PlanData data) : data_(std::move(data)) {}
  configuration_detail::PlanData data_;
  friend ResolvedPlan resolve_options(const MapSpec&, const ResourceBudget&, const WorkloadHint&,
                                      const OptionOverrides&);
  friend class ConfiguredByteMap;
  friend struct configuration_detail::PlanEngineOptions;
};

// Plans a map from public inputs alone.  With Scheme::kAuto every scheme is
// tried, failed candidates are recorded in rejected_candidates(), and the
// default rule ranks the rest; a pinned scheme's failure throws.  Throws
// std::invalid_argument (with every candidate's reason under auto) when
// nothing fits, and std::length_error / std::overflow_error on arithmetic
// overflow.  Creates no map, thread or seed.
inline ResolvedPlan resolve_options(const MapSpec& spec, const ResourceBudget& budget,
                                    const WorkloadHint& workload = {}, const OptionOverrides& overrides = {}) {
  using namespace configuration_detail;
  detail::ValidateCommonArguments(spec.requested_capacity, spec.key_bytes, spec.value_bytes);
  Require(spec.max_accesses > 0, "max_accesses must be positive");
  Require(budget.cores > budget.harness_cores, "budget leaves no caller core");
  Require(budget.cache_domains >= 1 && budget.cores % budget.cache_domains == 0,
          "declared cache domains must split the cores evenly");
  Require(budget.cores / budget.cache_domains > budget.harness_cores,
          "the caller's cache domain leaves no core past the harness");
  Require(workload.api_mode == ApiMode::kScalar || workload.api_mode == ApiMode::kBatch, "invalid API mode");
  Require(workload.expected_batch_size > 0 && (workload.api_mode != ApiMode::kScalar ||
          workload.expected_batch_size == 1), "invalid caller batch size");
  Require(overrides.scheme == Scheme::kAuto || IsHierarchy(overrides.scheme) || overrides.scheme == Scheme::kTree,
          "unknown scheme");
  if (!budget.cpu_ids.empty()) {
    Require(budget.cpu_ids.size() == budget.cores, "CPU slots must match declared core count including harness");
    auto ids = budget.cpu_ids;
    std::sort(ids.begin(), ids.end());
    Require(std::adjacent_find(ids.begin(), ids.end()) == ids.end(), "duplicate CPU slots");
  }
  if (overrides.scheme != Scheme::kAuto) {
    Require(overrides.scheme == Scheme::kHierarchicalIncremental || !overrides.incremental, "irrelevant incremental options");
    Require(overrides.scheme == Scheme::kHierarchicalSynchronous || !overrides.synchronous, "irrelevant synchronous options");
    Require(overrides.scheme == Scheme::kTree || !overrides.tree, "irrelevant tree options");
  }
  std::vector<PlanData> eligible;
  std::vector<std::string> rejected;
  for (Scheme s : {Scheme::kHierarchicalIncremental, Scheme::kHierarchicalSynchronous, Scheme::kTree}) {
    if (overrides.scheme != Scheme::kAuto && overrides.scheme != s) continue;
    try {
      eligible.push_back(Candidate(spec, budget, workload, overrides, s));
    } catch (const std::invalid_argument& e) {
      if (overrides.scheme != Scheme::kAuto) throw;
      rejected.push_back(Value(s) + ": " + e.what());
    } catch (const std::length_error& e) {
      if (overrides.scheme != Scheme::kAuto) throw;
      rejected.push_back(Value(s) + ": " + e.what());
    } catch (const std::overflow_error& e) {  // checked geometry arithmetic
      if (overrides.scheme != Scheme::kAuto) throw;
      rejected.push_back(Value(s) + ": " + e.what());
    }
  }
  if (eligible.empty()) {
    std::string reasons = "no eligible configuration";
    for (const auto& reason : rejected) reasons += "; " + reason;
    Require(false, reasons);
  }
  // The library's default rule (default_rule.hpp), shared with default Map<>.
  // Synchronous trades latency for memory and is chosen only when
  // pinned or when nothing else fits.
  size_t best = 0;
  auto rank = [&](const PlanData& d) {
    if (d.scheme == Scheme::kHierarchicalSynchronous) return 2;
    if (d.scheme == Scheme::kTree) return DefaultRule(spec.value_bytes).tree ? 0 : 1;
    return 1;
  };
  for (size_t i = 1; i < eligible.size(); ++i)
    if (rank(eligible[i]) < rank(eligible[best])) best = i;
  auto selected = std::move(eligible[best]);
  // Computed before the scheme choice is recorded, so an auto row that selects
  // exactly a pinned row's configuration shares its key (the benchmark
  // harness then marks the two rows as the same configuration).
  selected.configuration_key = ConfigurationKey(selected);
  selected.rejected_candidates = std::move(rejected);
  Choice(selected.choices, "scheme", Value(selected.scheme),
         overrides.scheme == Scheme::kAuto ? ChoiceSource::kFallback : ChoiceSource::kExplicit,
         overrides.scheme == Scheme::kAuto ? "uncalibrated public-input fallback; no latency SLO guarantee"
                                           : "pinned scheme");
  Derived(selected.choices, "actual_capacity", selected.capacity, "selected geometry");
  Derived(selected.choices, "max_accesses", spec.max_accesses, "shared hierarchy/position-map horizon");
  return ResolvedPlan(std::move(selected));
}

// A hook runs ON the named thread. With explicit CPU slots it must pin and
// verify the assignment, throwing on failure. Without slots it is optional.
// Incremental owner threads start at the first access, not in make_map, so
// that initialize() can still bulk load; an owner hook's failure therefore
// surfaces from that first access. Other pools start during construction.
struct ConstructionHooks {
  std::function<void(const PlannedThread&)> thread_init;
};

namespace configuration_detail {
// The plain `Options` / `TreeOptions` a plan's settings translate to: what the
// ordinary constructors take, so a planned map is built by the same code.
inline Options LegacyOptions(const HierarchyPlan& h, uint64_t horizon) {
  if (h.scheme == Scheme::kHierarchicalIncremental) return IncrementalOptions(h.incremental, horizon);
  return SynchronousOptions(h.synchronous, horizon);
}
inline TreeOptions LegacyTreeOptions(const TreeSettings& s, Options position) {
  TreeOptions options;
#define CPU_ORAM_COPY_T(type, name, default_value, legacy) options.legacy = s.name;
  CPU_ORAM_TREE_FIELDS(CPU_ORAM_COPY_T)
#undef CPU_ORAM_COPY_T
  options.max_load = s.max_load_ppm / 1000000.0;
  options.position_map = std::move(position);
  return options;
}
}  // namespace configuration_detail

// A byte map built from a ResolvedPlan: one of ByteMap<true>,
// ByteMap<false>, TreeByteMap<true> or TreeByteMap<false>, behind the common
// byte-map interface (each operation has that engine's contract; see
// byte_map.hpp).  Construction runs `hooks.thread_init` for every planned
// thread, then checks that the constructed map's capacity, geometry, byte
// bill, thread division and (for a tree) payload planes and position map
// agree with the plan, throwing std::logic_error if they do not.
class ConfiguredByteMap {
 private:
  template <class F> decltype(auto) visit(F&& fn) {
    return std::visit([&](auto& pointer) -> decltype(auto) { return fn(*pointer); }, map_);
  }
  template <class F> decltype(auto) visit(F&& fn) const {
    return std::visit([&](const auto& pointer) -> decltype(auto) { return fn(std::as_const(*pointer)); }, map_);
  }
 public:
  explicit ConfiguredByteMap(const ResolvedPlan& plan, ConstructionHooks hooks = {}) : plan_(plan) {
    using namespace configuration_detail;
    const auto& d = plan_.data_;
    Require(d.budget.cpu_ids.empty() || bool(hooks.thread_init), "explicit placement needs a verified thread_init hook");
    auto callback = [threads = d.threads, hook = hooks.thread_init](ThreadRole role) {
      return [threads, hook, role](unsigned index) {
        if (!hook) return;
        for (const auto& thread : threads) if (thread.role == role && thread.index == index) {
          hook(thread); return;
        }
        throw std::logic_error("constructed worker absent from resolved plan");
      };
    };
    callback(ThreadRole::kCaller)(0);
    Options h = LegacyOptions(d.hierarchy, d.spec.max_accesses);
    const bool tree = d.scheme == Scheme::kTree;
    h.worker_thread_init = callback(tree ? ThreadRole::kPositionOwner : ThreadRole::kOwner);
    // Without its own hook a helper inherits the thread that starts the owners:
    // under explicit placement, the caller's single core.
    auto top_helper = callback(tree ? ThreadRole::kPositionTopHelper : ThreadRole::kTopHelper);
    auto bottom_helper = callback(tree ? ThreadRole::kPositionBottomHelper : ThreadRole::kBottomHelper);
    const unsigned top_helpers = d.hierarchy.incremental.top_helpers;
    h.deamortized_helper_thread_init = [top_helper, bottom_helper, top_helpers](unsigned index) {
      if (index < top_helpers) top_helper(index);
      else bottom_helper(index - top_helpers);
    };
    // Public batch init indices include caller 0, unlike planned helper indices.
    auto batch = callback(tree ? ThreadRole::kPositionOnlineHelper : ThreadRole::kOnlineHelper);
    h.deamortized_value_thread_init = callback(tree ? ThreadRole::kPositionValue : ThreadRole::kValue);
    h.deamortized_batch_thread_init = [batch](unsigned index) { batch(index - 1); };
    if (tree) {
      auto t = LegacyTreeOptions(d.tree, std::move(h));
      t.payload_worker_init = callback(ThreadRole::kPayload);
      if (d.hierarchy.scheme == Scheme::kHierarchicalIncremental)
        map_ = std::make_unique<TreeByteMap<true>>(d.spec.requested_capacity, d.spec.key_bytes, d.spec.value_bytes, t);
      else map_ = std::make_unique<TreeByteMap<false>>(d.spec.requested_capacity, d.spec.key_bytes, d.spec.value_bytes, t);
    } else if (d.scheme == Scheme::kHierarchicalIncremental) {
      map_ = std::make_unique<ByteMap<true>>(d.spec.requested_capacity, d.spec.key_bytes, d.spec.value_bytes, h);
    } else {
      map_ = std::make_unique<ByteMap<false>>(d.spec.requested_capacity, d.spec.key_bytes, d.spec.value_bytes, h);
    }
    if (capacity() != d.capacity) throw std::logic_error("constructed capacity differs from exact plan");
    // The rebuild's division and helpers are fixed at construction even
    // though the owner threads start at the first access; a tree's position
    // map has its own.
    auto check_division = [&](const ByteMap<true>& hierarchy) {
      const auto& s = d.hierarchy.incremental;
      const auto& engine = hierarchy.engine();
      bool same = engine.threaded() == (s.owner_threads > 0) &&
                  (!engine.threaded() || (engine.owner_groups() == s.level_groups.size() &&
                                          engine.top_helper_threads() == s.top_helpers &&
                                          engine.bottom_helper_threads() == s.bottom_helpers));
      for (size_t i = 0; same && engine.threaded() && i < s.level_groups.size(); ++i)
        same = engine.owner_group(i).first == s.level_groups[i].first &&
               engine.owner_group(i).last == s.level_groups[i].last;
      if (!same) throw std::logic_error("constructed rebuild division differs from exact plan");
    };
    // The geometry and participants a hierarchy was built with, against the
    // plan's, for either scheme.
    auto check_hierarchy = [&](const auto& hierarchy) {
      const auto& g = hierarchy.geometry_choice().geometry;
      const auto& p = d.hierarchy.arena.geometry;
      const unsigned participants = d.hierarchy.scheme == Scheme::kHierarchicalIncremental
                                        ? d.hierarchy.incremental.batch_participants
                                        : d.hierarchy.synchronous.batch_participants;
      if (g.levels != p.levels || g.level_fanouts != p.level_fanouts ||
          g.prefix_flushes != p.prefix_flushes || g.top_digit != p.top_digit ||
          g.tier_buckets != p.tier_buckets || g.level_tier_buckets != p.level_tier_buckets ||
          hierarchy.arena_bytes() != d.hierarchy.modeled_bytes ||
          hierarchy.batch_participant_capacity() != participants)
        throw std::logic_error("constructed hierarchy differs from exact plan");
    };
    std::visit([&](const auto& map) {
      using M = typename std::decay_t<decltype(map)>::element_type;
      if constexpr (std::is_same_v<M, ByteMap<true>> || std::is_same_v<M, ByteMap<false>>) {
        check_hierarchy(*map);
        if constexpr (std::is_same_v<M, ByteMap<true>>) check_division(*map);
      } else {
        if (map->payload_planes() != d.payload_workers || map->uid_from_key() != d.tree.uid_from_key ||
            map->path_levels() != d.tree_geometry.path_levels())
          throw std::logic_error("constructed tree differs from exact plan");
        const auto& position = map->position_byte_map();
        if (position.capacity() != d.hierarchy.capacity)
          throw std::logic_error("constructed position map differs from exact plan");
        check_hierarchy(position);
        if (map->arena_bytes() != d.modeled_bytes)
          throw std::logic_error("constructed tree buffers differ from exact plan");
        if constexpr (std::is_same_v<M, TreeByteMap<true>>) check_division(position);
      }
    }, map_);
  }
  ConfiguredByteMap(ConfiguredByteMap&&) noexcept = default;
  ConfiguredByteMap& operator=(ConfiguredByteMap&&) noexcept = default;
  ConfiguredByteMap(const ConfiguredByteMap&) = delete;
  ConfiguredByteMap& operator=(const ConfiguredByteMap&) = delete;

  // Dispatch once for a whole serialized workload. The callback must not retain
  // the backend reference beyond this configured map's lifetime.
  template <class F> decltype(auto) with_backend(F&& fn) {
    return visit(std::forward<F>(fn));
  }

  const ResolvedPlan& plan() const { return plan_; }
  size_t capacity() const { return visit([](const auto& m) { return m.capacity(); }); }
  size_t requested_capacity() const { return plan_.spec().requested_capacity; }
  size_t key_bytes() const { return plan_.spec().key_bytes; }
  size_t value_bytes() const { return plan_.spec().value_bytes; }
  bool find(const uint8_t* key, uint8_t* out) { return visit([&](auto& m) { return m.find(key, out); }); }
  bool contains(const uint8_t* key) { return visit([&](auto& m) { return m.contains(key); }); }
  void insert_or_assign(const uint8_t* key, const uint8_t* value) {
    visit([&](auto& m) { m.insert_or_assign(key, value); });
  }
  bool exchange(const uint8_t* key, const uint8_t* value, uint8_t* old, bool insert) {
    return visit([&](auto& m) { return m.exchange(key, value, old, insert); });
  }
  void write(const uint8_t* key, const uint8_t* value) {
    insert_or_assign(key, value);
  }
  template <class Update>
  bool access(const uint8_t* key, Update&& update) {
    return visit([&](auto& map) {
      return map.access(key, std::forward<Update>(update));
    });
  }
  template <class Update>
  bool Access(const uint8_t* key, Update&& update) {
    return access(key, std::forward<Update>(update));
  }
  bool erase(const uint8_t* key) { return visit([&](auto& m) { return m.erase(key); }); }
  bool erase(const uint8_t* key, uint8_t* old) { return visit([&](auto& m) { return m.erase(key, old); }); }
  void access_batch(size_t count, const BatchRequest* requests, uint8_t* found) {
    visit([&](auto& m) { m.access_batch(count, requests, found); });
  }
  bool supports_direct_initialization() const { return plan_.capabilities().direct_initialization; }
  template <class InputIterator>
  void initialize(InputIterator first, size_t count,
                  InitializationPolicy policy = InitializationPolicy::kDistinct) {
    configuration_detail::Require(supports_direct_initialization(), "tree initialization requires insertions");
    visit([&](auto& m) {
      using M = std::decay_t<decltype(m)>;
      if constexpr (std::is_same_v<M, ByteMap<true>> || std::is_same_v<M, ByteMap<false>>)
        m.initialize(first, count, policy);
    });
  }
  void finish_pending_work() {
    visit([](auto& m) { m.finish_pending_work(); });
  }
 private:
  ResolvedPlan plan_;
  std::variant<std::unique_ptr<ByteMap<true>>, std::unique_ptr<ByteMap<false>>,
               std::unique_ptr<TreeByteMap<true>>, std::unique_ptr<TreeByteMap<false>>> map_;
};

// Builds a fresh map from `plan` (see ConfiguredByteMap).
inline ConfiguredByteMap make_map(const ResolvedPlan& plan, ConstructionHooks hooks = {}) {
  return ConfiguredByteMap(plan, std::move(hooks));
}

namespace configuration_detail {
// The engine options a plan constructs (what ConfiguredByteMap builds from).
struct PlanEngineOptions {
  static Options Hierarchy(const ResolvedPlan& plan) {
    return LegacyOptions(plan.data_.hierarchy, plan.data_.spec.max_accesses);
  }
  static TreeOptions Tree(const ResolvedPlan& plan) {
    return LegacyTreeOptions(plan.data_.tree, Hierarchy(plan));
  }
};

// Default Map<> at a core budget is resolve_options(Scheme::kAuto) at
// that budget, restricted to the engines the hybrid can hold: the hierarchy of
// its own mode, or the tree over a position map of that mode.  Ranked as auto
// ranks them (DefaultRule at the tree's actual payload workers; the hierarchy
// unless the rule prefers the tree or the hierarchy does not fit), with the
// hybrid map's payload spin, which auto derives for a tree too.
inline HybridOptions BudgetedHybridOptions(size_t requested_capacity, size_t key_bytes,
                                           size_t value_bytes, unsigned cores, bool deamortize) {
  Require(cores >= 1, "a core budget includes the caller");
  const MapSpec spec{requested_capacity, key_bytes, value_bytes};
  const ResourceBudget budget{cores};
  const Scheme hierarchy = deamortize ? Scheme::kHierarchicalIncremental : Scheme::kHierarchicalSynchronous;
  OptionOverrides as_tree;
  as_tree.scheme = Scheme::kTree;
  as_tree.tree.emplace();
  as_tree.tree->position_map.mode = hierarchy;
  OptionOverrides as_hierarchy;
  as_hierarchy.scheme = hierarchy;
  auto attempt = [&](const OptionOverrides& o) -> std::optional<ResolvedPlan> {
    try {
      return resolve_options(spec, budget, {}, o);
    } catch (const std::invalid_argument&) {
    } catch (const std::length_error&) {
    } catch (const std::overflow_error&) {
    }
    return std::nullopt;
  };
  const auto tree = attempt(as_tree);
  const auto flat = attempt(as_hierarchy);
  Require(tree || flat, "no engine fits this core budget and shape");
  HybridOptions options;
  if (tree && (!flat || DefaultRule(value_bytes).tree)) {
    options.tree_value_threshold = 0;
    options.tree = PlanEngineOptions::Tree(*tree);
    options.tree.payload_spin_micros = kHybridTreePayloadSpinMicros;  // as auto derives it
  } else {
    options.tree_value_threshold = SIZE_MAX;
    options.hierarchical = PlanEngineOptions::Hierarchy(*flat);
  }
  return options;
}
}  // namespace configuration_detail

template <bool Deamortize>
HybridByteMap<Deamortize>::HybridByteMap(size_t requested_capacity, size_t key_bytes, size_t value_bytes,
                                         CoreBudget budget)
    : HybridByteMap(requested_capacity, key_bytes, value_bytes,
                    configuration_detail::BudgetedHybridOptions(requested_capacity, key_bytes, value_bytes,
                                                                budget.cores, Deamortize)) {}

#undef CPU_ORAM_INCREMENTAL_FIELDS
#undef CPU_ORAM_SYNCHRONOUS_FIELDS
#undef CPU_ORAM_ARENA_FIELDS
#undef CPU_ORAM_REBUILD_FIELDS
#undef CPU_ORAM_TREE_FIELDS

}  // namespace cpu_byteslice_oram
