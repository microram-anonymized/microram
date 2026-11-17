# Explicit resource planning

Include `<cpu_byteslice_oram/configuration.hpp>` for the opt-in resolver and
configured byte map. This is a header-only C++17 API without Python or JSON
dependencies. It is opt-in: `Map`, `HybridByteMap`, `ByteMap`, `TreeByteMap`,
and their explicit option constructors keep their own selection and defaults.
Every input to the resolver is public (sizes, budgets, declared topology,
overrides); it never sees keys or values.

```cpp
#include <cpu_byteslice_oram/configuration.hpp>

namespace oram = cpu_byteslice_oram;
oram::MapSpec spec{1024, 8, 48};
oram::ResourceBudget budget;
budget.cores = 4;          // caller, library helpers, and harness combined
budget.harness_cores = 1;  // leaves three library cores

oram::OptionOverrides overrides;
overrides.scheme = oram::Scheme::kHierarchicalIncremental;
overrides.incremental.emplace();
overrides.incremental->owner_threads = 0;  // explicit inline execution
overrides.incremental->batch_participants = 2; // caller + one helper

oram::WorkloadHint workload;
workload.api_mode = oram::ApiMode::kBatch;
workload.expected_batch_size = 64; // independent of internal lanes/participants

auto plan = oram::resolve_options(spec, budget, workload, overrides);
auto map = oram::make_map(plan);
// map.find / insert_or_assign / exchange / erase / access_batch
map.finish_pending_work();
```

`ResolvedPlan` is a copyable, read-only value with requested specification,
chosen scheme, actual capacity, geometry, capabilities, modeled memory
components, complete thread-role counts, and per-field provenance. Reusing the
same plan constructs a fresh map with the same public configuration. Factory
construction checks capacity against the plan, plus what each map exposes:
for either hierarchy scheme its geometry, modeled bytes and batch-participant
capacity, and for an incremental one the rebuild's level division and its
top-group helper count; tree payload planes, UID policy, path levels,
position-map capacity and the position map's hierarchy checked the same way.
Disagreement throws.
Random engine seeds are generated only during construction, and are not part of
configuration replay. Do not interpret replay as reproducing secret state or traces.

The resolver plans either hierarchy scheme with the same `Options`-based
geometry search the constructors run, and verifies the result. Public
`choices()` contains resolved geometry values, including the chosen top digit,
prefix count and fanout ladder, and for a tree its leaf bits, fold, stash
registers and path slots. There is no persisted
exact-plan import/export and no construction directly from a frozen geometry:
`resolve` pins every override, construction repeats the search and checks that
it agrees, and the worker compares each attempt's configuration key with the
frozen one. There is no parser accepting arbitrary mutable `ResolvedPlan`
fields.

### Certification report

`plan.certification()` says what the capacity-failure analysis
(`analysis/bound_certification`) establishes for the planned map. Its status
is one of:

- `certified`: the geometry matches a certified record, and its conditional
  bound on "some rebuild capacity test overflows within `max_accesses`" is at
  most 2^-64;
- `above_target`: a record matches, but its bound is above 2^-64;
- `not_covered`: no record applies.

With a record, `failure_bound_log2()` gives the bound, rounded up. `reason`
names the record, or the first requirement that failed: an untabled capacity,
B, s or q, a horizon above the certified one, stash or tier sizing that
differs from the record's, or an opt-in option the analysis does not model.

`hierarchy_certification()` is the hierarchy's own report: the map itself, or
a tree's position map. A tree map is `not_covered` at the top level, because
its own bound is not in this analysis. A synchronous map runs the same merge
jobs as an incremental one, so the same record certifies it. The same
report appears in `choices()` as `certification` and `failure_bound_log2`,
and under the `hierarchy.` or `position_map.` prefix. These fields are left out
of `configuration_key()`. `ByteMap::certification()` reports the same
thing for a map built through `Options`.

The planner never refuses an uncovered configuration; it only flags it.
At execution time the hierarchy enforces `max_accesses` as an online access
limit, including when used as a tree position map. See the
[access-budget and callback contract](../../README.md#callback-access).
Construction also rejects a horizon whose initialization offset, speculative
families or complete windows exceed the native integer fields, before table
allocation. This arithmetic limit applies to both hierarchy modes; the
[engine design](../../src/oram/levelarena/DESIGN.md#access-horizon-and-counter-limits)
explains its relation to dense table IDs.
Every bound is conditional on the checker's undischarged premises, so the
unconditional bound is 1. The table is generated. See
`src/oram/levelarena/DESIGN.md`, "Certification report", for how to
regenerate it.

## Selection and overrides

Schemes are auto, incremental hierarchy, synchronous hierarchy, and tree.
The two hierarchy schemes are the same engine: the synchronous one runs every
rebuild on the caller instead of on owner threads. Both take the same arena
fields (geometry, batch path, wait limit) with the same names and meanings;
only the incremental one takes the rebuild-thread, slice and cost-model fields.
Tree position-map mode can be explicitly incremental or synchronous; its default
is incremental. A synchronous position-map option block requires the explicit
synchronous mode. Every optional knob distinguishes absence from explicit
zero/false. For example, zero owners and zero payload cap are valid; explicit
zero prefix flushes or top digit are rejected, because zero is the auto
sentinel of the corresponding `Options` field; omit the override instead. A tree's explicit zero `fold` or `stash_registers` selects the
default rule, as leaving it unset does. Irrelevant blocks on pinned
schemes fail; auto records failed candidate constraints in
`rejected_candidates()` rather than applying them to another engine.

The hierarchy fields take the ranges of the `Options` fields they set; the
field comments in `byte_map.hpp` state them. For example, `online_stash_entries`
is 64 times a power of two, at most 262144, and `rebuild_lanes` is 1 to 64.
The resolver checks them with the same function the constructors use, so a
refusal is a `std::invalid_argument` that names the `Options` field. Keys are
at most 64 bytes under every scheme (`kMaxUserKeyBytes`), and a wider
`MapSpec::key_bytes` is refused before any candidate is planned.

The tree block takes `fold`, `stash_registers`, `max_folded_slots`,
`leaf_scale`, `max_load_ppm`, `prefetch_ahead`, `uid_from_key`,
`payload_max_threads`, `payload_threshold` (default 32 bytes per worker),
`payload_spin_us`, `payload_monitor_wait`, the placement-only `payload_near`,
and `position_map`. They mean what the `TreeOptions` fields of the same names
mean; the [tree design](../../src/oram/tree/DESIGN.md#geometry-and-the-default-rule)
gives the default rule. Explicit geometry values are validated as the
constructor validates them: `fold` 1 to 5 with a path of at most 32 buckets
(16 at fold 5);
`stash_registers` 3 or 4 and not below the rule's for the depth and fold,
so fold 5 and trees of 25 or more leaf bits need 4; `max_folded_slots` at most
`64 * stash_registers - 1`; `max_load_ppm` above zero and at most 500000, the
load the stash width was sized for. The plan records the resolved `tree.fold`,
`tree.stash_registers`, `tree.leaf_bits`, `tree.path_slots` and
`tree.payload_workers`.

An explicit knob whose only effect needs a resource the plan lacks is rejected
by name: `near_max_level`, `owner_spin_ns`, `slice_target_rate` or
`slice_touches` without owners, `inline_work_factor_ppm` with owners,
`lane_min_buckets` with one lane, `top_helpers` without a laned table in the top
level's group, `bottom_helpers` without a separate laned group for level one, `payload_spin_us`
without payload workers and `payload_threshold` with a zero payload cap.

The incremental rebuild's threads are one question with two spellings. A
`rebuild_threads` budget (owners plus top-group helpers) is divided by the
library's load heuristic (`HeuristicRebuildParams`, the same call the
`deamortized_rebuild_threads` option makes), and the plan then pins the answer:
`owner_threads`, `level_groups`, `top_helpers`, `rebuild_lanes` and
`lane_min_buckets` appear as derived choices and construction passes them
explicitly, so the geometry is planned once more with the pinned values and must
agree. An explicit `owner_threads` instead fixes the owner count; its division
is the engine's own (`PlanLevelGroups`, recorded as derived) unless
`level_groups` pins it, and helpers and lanes may then be pinned too. Setting
both spellings, or a helper/lane/division field next to a budget, is refused.
Explicit bottom helpers receive `kBottomHelper` roles (or
`kPositionBottomHelper` in a tree), with indices local to that pool and the
locality of level one's owner group. Construction maps the engine's combined
top-then-bottom helper indices to these roles. Both pools count toward the
core budget and the tree's reservation for its position map.
`rebuild_threads_used` records owners plus both helper pools; the heuristic
may spend fewer than its budget. With an explicit `near_max_level` and
`ResourceBudget::cache_domains` above one (declared equal L3 domains, not
discovered), the budget is capped per side: near threads at the caller's domain
less the harness, the caller and its batch helpers, far threads (the top's
helpers included) at the other domains. The caps are the derived
`near_rebuild_threads_cap` and `far_rebuild_threads_cap` choices (the
`deamortized_near_rebuild_threads`/`deamortized_far_rebuild_threads` options);
like the budget, they are heuristic inputs and not part of the configuration
key. A tree's two-thread position map is not capped.

The heuristic divides by a cost model (`LevelArenaRebuildCost`, the
`deamortized_rebuild_cost` option): by default, calibration constants fitted on
one development machine; for a target, the tuner's fit (`python -m analysis.oram_bench fit-rebuild`, which fits
it to the level-arena benchmark's `--fit-rows` on that machine). Its fields are
overrides in integer units: `rebuild_cost_line_picos`,
`rebuild_cost_residual_line_picos`, `rebuild_cost_offer_line_picos` and
`rebuild_cost_job_nanos` (a level's cost per access is routing lines x line +
residual-pass lines x residual line + offer lines x offer line + jobs x job,
counted under the engine's residual routing), `rebuild_cost_middle_burst_ppm`, `rebuild_cost_helper_speedup_ppm` and
`rebuild_cost_max_top_threads` (the top's helper curve and its cap, which is a
property of memory bandwidth and not of how many cores one L3 holds),
`rebuild_cost_thread_gain_floor_ppm`, `rebuild_cost_probe_bucket_picos` and
`rebuild_cost_probe_line_picos` (the requester's probe, which sets the default
`slice_target_rate`), and `rebuild_cost_slice_line_picos` (the line cost a
rebuild piece is budgeted at). Every field but the last is a heuristic input:
it moves the division, helpers and slice rate, which are choices of their own,
and stays out of the configuration key. The slice line cost sizes the engine's
pieces directly, so it is part of the key. Each is refused where it chooses
nothing: the division and helper fields next to an explicit `level_groups`, the
cap and floor without a budget, the probe fields next to an explicit
`slice_target_rate`, the slice field next to `slice_touches`, and all of them
without owner threads.

`carry_period_accesses()` lists the accesses between rebuilds reaching each
level, lowest first: carries into levels 1..L of either hierarchy scheme;
for a tree, its position map's, counted by
`TreeByteMap::position_map_access_count()`. The last entry is the top's period,
which is what cycle coverage counts.

There are no named tuning profiles. Tuned settings are explicit override blocks
(the benchmark runs a tuned configuration as one more compared configuration,
an *arm*, beside default auto; see
[benchmarks/campaigns](../../benchmarks/campaigns/README.md)); a library default changes only as a code change.

Auto reports the policy `uncalibrated_fallback_v2` (`ResolvedPlan::policy_id()`).
The policy name is a stable identifier recorded in plans. "Uncalibrated" means
the choice uses the library's fixed default rule and cost-model constants, not
a fit made on the target machine.
The hierarchy's rebuild budget is every core the caller and batch helpers
leave; a tree's nested position map keeps a two-thread budget
(`kTreePositionRebuildThreads`). It reserves explicitly
requested nested workers, resolves the remaining payload/owner budget, and
calls the library's default rule (`DefaultRule`, `default_rule.hpp`); default
`Map<>` calls the same rule with its fixed policy (one payload worker per
started 32 value bytes, no fixed cap), so the two cannot drift. Both take the
tree from 96 bytes whatever the budget; `default_rule.hpp` gives the
rationale. Constructed with `CoreBudget{n}`,
`Map<>` resolves the hierarchy of its own mode and the tree over a position map
of that mode at a budget of n cores, ranks them as auto does and builds the
winner from the plan's options with the hybrid's 2 ms payload spin, so it
matches auto at that budget (engine, rebuild division, payload workers);
it refuses a budget at which neither fits. The rule's geometry (B=8, two dense prefixes, a
64-entry online stash, the half-fanout prefix) is what `Options` and auto's
fallback both default to. Auto counts actual
payload planes after width/chunk limits, not just the requested cap. Synchronous
is a pinned baseline or last-resort candidate. When auto selects the tree it
uses the hybrid map's 2 ms payload spin (`kHybridTreePayloadSpinMicros`), so an
auto row behaves like the default `Map<>`; a pinned tree keeps the tree engine's
200 µs default. `WorkloadHint` carries only the API mode and caller batch size;
the fallback validates and records them, but no choice depends on them.

Resolution allocates only planning metadata, not map arenas or workers. It does
not generate random seeds or discover CPU topology. The resolver and existing
construction paths use the same arena capacity ladder and component byte
predictors. Capacity selection and the reported requested bytes do not depend
on the process huge-page policy; where a predictor rounds, it reads that policy
as construction does, and the benchmark never changes it between resolving and
constructing. The requested bytes are not an observed allocation
or a complete memory estimate.

Explicit tree loads above one half, tree horizons above 2^32, monitor-wait (tree payload
or arena value workers) without a declared `ResourceBudget::monitor_wait`
capability, and explicitly requested key-derived UIDs wider than eight bytes
fail. A declared capability is a public input like `cache_domains`; the
benchmark worker refuses a declaration its CPU does not match.
`ResourceBudget::spin_before_park_ns` (zero: each field's default) sets every
spin-before-park the overrides leave unset: owner, batch and value spins, a
tree position map's, and the tree payload spin where there are payload workers.
It is a latency choice only; results do not change. `Options` fields that the
resolver does not expose remain available through the ordinary constructors.
A default UID policy resolves to counter UIDs for wide keys. The resolver
offers no override that relaxes a security check.

## Resource and capability reporting

`cores` includes the single serialized caller; `harness_cores` are reserved and
never assigned to library roles. Incremental owners are extra threads; batch
participants include the caller. A synchronous hierarchy starts no thread but
its batch participants. Top-group helpers are extra threads, listed right after the owner of
the top level's group. Tree payload workers and position-map owner/helper/batch
threads share the same budget, with the caller counted once. With an
explicit `near_max_level`, each owner and helper records whether its levels are
all at or below the boundary (`PlannedThread::near`). `tree.payload_near`
(placement only) marks the payload workers near too, so near/far
placement puts them in the caller's cache domain instead of the remote one
first; the map itself ignores it. Explicit oversubscription fails;
automatic worker counts use the remaining budget. Plans include helper pools
even for scalar workloads because construction still allocates them.

Optional `cpu_ids` must name unique caller-supplied physical-core slots, with
one entry per declared core. The trailing harness slots remain unused by the
library. The resolver does not claim to prove physical topology, SMT exclusion,
or CPU availability. If CPU IDs are present, `make_map` requires a
`ConstructionHooks::thread_init` callback. It runs on the specified thread and
must install and verify its affinity, throwing on failure. The caller hook runs
before map construction; owner and top-helper hooks can run on the first online
access because direct fill defers owners. Helpers get their own hook
(`deamortized_helper_thread_init`): without it a helper inherits the thread that
starts the owners, which under explicit placement is the caller's single core. Hook failure propagates. Batch participants of either hierarchy scheme use
`deamortized_batch_thread_init`. Startup waits for every callback and joins
all helpers before propagating a failure. The ordinary constructors start threads without
hooks unless the corresponding `Options` field is set.

The benchmark's `VerifiedPlacement` helper validates explicit slots against a
preconstruction topology snapshot, installs singleton Linux thread masks, and
reads them back from the thread itself. Its injected-affinity fixtures cover the
inherited-mask trap without changing host affinity. Native worker `--cpu-ids`
also places the writer/telemetry thread on its reserved slot and records observed
masks. Automatic near/far assignment is the worker's `--placement near_far`
([WORKER.md](../../analysis/oram_bench/WORKER.md)); target topology/affinity
verification is still required.

Memory components (`memory_components()`) each carry a coverage label:

- Hierarchy (either scheme): the arena's byte-bill roles (arena, dense,
  scratch, participant buffers, plan pool and bookkeeping), `tallied`: the
  engine records every buffer and construction checks the record against the
  plan. In the synchronous scheme the arena role is its one region per level.
- Tree: the plane arenas, `modeled` (computed from the geometry the
  constructor sizes from), plus the position map's components.

The components sum to `modeled_buffer_bytes()`, which is requested bytes.
`modeled_reserved_bytes()` is the same buffers as the allocator is asked for
them: each rounded to its alignment, 2 MiB for a huge-page buffer, under the
resolving process's `MICRORAM_HUGE_PAGES` policy. The allocation audit tool
([`cpu_oram_allocation_audit.cpp`](../../benchmarks/oram/cpu_oram_allocation_audit.cpp))
compares the reserved bytes with each engine's live heap, using a counting
allocator; the engines are designed so that the modeled buffers are nearly all
of that heap, no engine allocates while accessing, and initialization has no
transient peak.
[`cpu_oram_allocation_test`](../../tests/oram/cpu_oram_allocation_test.cpp)
checks that the reserved bytes cover the live heap up to a small fixed
allowance, that accessing allocates nothing, and that destruction returns
every byte. What the reserved bytes leave out is small and fixed (engine
objects and small containers), plus what is not heap: thread stacks, the
binary, and a TEE guest's runtime memory. `modeled_buffer_limit_bytes` constrains the requested
bytes of every scheme. It still cannot establish that a trial fits RAM.

`supports_direct_initialization()` is true only for hierarchy. The configured
facade's `initialize()` refuses tree maps; workers must fill those with supported
insertion calls. Tree capabilities identify batched position-map
work, in either position-map mode, followed by ordered tree accesses.

`finish_pending_work()` is also available on all existing byte, hybrid, and
typed maps. For tree it drains both position-map rebuilds and payload eviction;
`drain_rebuilds()` and `drain_tree()` keep their narrower meanings.
The one-trial benchmark worker uses this barrier and records caller and
maintenance-inclusive rates. Its `with_backend(callback)` call dispatches once
for the trial; the callback receives the concrete map reference, whose lifetime
is bounded by the configured facade. This callback does not weaken
construction agreement checks.

## Local correctness validation

```bash
cmake -S . -B build
cmake --build build --target cpu_byteslice_configuration_test cpu_byteslice_configuration_test_checked -j2
ctest --test-dir build -R '^cpu_byteslice_configuration_test(_checked)?$' --output-on-failure
```

These are correctness tests, with no performance measurements. They exercise
capacity and worker thresholds, the three key/value record shapes the evaluation uses (4/8, 8/48 and 32/1024 bytes), both tree position-map
modes, repeated-key batch ordering, fill/finish capabilities, explicit zero/false,
invalid and ineffective combinations, memory-limit behavior, per-role startup hooks and fresh
construction from an existing plan. Performance tuning and checks inside a
protected runtime (TEE) are outside these tests.

Both hierarchy schemes accept `value_workers` (default 0), `value_tail`
(default 2), `value_kernel`, `value_spin_ns`, `value_pause`,
`value_monitor_wait`, and `value_demote`. Value workers count against the core
budget alongside caller, rebuild and batch roles; planned `kValue` and nested
`kPositionValue` roles use the construction hook. Their fixed buffers appear
in the requested/reserved memory report. The corresponding `Options` fields
are `deamortized_value_*`, including `deamortized_value_thread_init`. Scalar calls
join all reads; insertion bytes are engine-owned until unconditional next-job
forwarding or a drain at a public path/storage boundary. These controls also
apply to synchronous storage, which still rebuilds on the requester. Whether
value workers pay off, and where to place them, depends on the target; the
default is 0. Value workers need a dense prefix of at most 4096 buckets
(`prefix_flushes * online_stash_entries / 64`, with the resolved
`prefix_flushes`); the resolver and the `Options` constructors refuse a longer
one with `std::invalid_argument`.
