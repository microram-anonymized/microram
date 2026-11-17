# ORAM campaigns

The campaign tools plan, resolve, run, recover, reduce and plot ORAM
measurements. Python 3.9 or newer is required. Planning and validation use the
standard library and do not construct maps. Native execution additionally needs
a compiled worker and compatible hardware. Run these commands from the
repository root:

```bash
python -m analysis.oram_bench --help
python -m analysis.oram_bench plan --config benchmarks/campaigns/c4-tdx-smoke.json --dry-run
python -m analysis.oram_bench plan --config benchmarks/campaigns/c4-tdx.json --output /tmp/c4-tdx-plan
python -m analysis.oram_bench validate campaign benchmarks/campaigns/c4-tdx.json
python -m analysis.oram_bench schema campaign
python -m unittest discover -s tests/analysis -v
```

`--output` writes a normalized `plan.json`, including every logical trial and
its dependencies. Repeating the identical command is safe. A different plan
cannot overwrite that file, including when two planning processes race.
`--dry-run` and `--output` are mutually exclusive; omitting both also performs
a dry expansion. Invalid input exits with status 2 and a field-level diagnostic.
Output paths are local filesystems with hard links and directory fsync support.
This is plan publication, not the per-attempt commit/recovery protocol.

Plan rows say `deferred`, or `skipped` when a necessary constraint already
fails. `deferred` means the matrix row exists but has **not** passed the library
resolver, memory planning, access-horizon checks, or runtime verification. The
[`resolve` step](WORKER.md#the-resolve-step) then freezes the worker build,
resolves every row with the C++ resolver and writes `resolution.json`: runnable,
`same_as` another row, or skipped with a reason (including modelled memory over
the host headroom).
The [worker and local recovery guide](WORKER.md) documents the C++ worker,
full-event/checkpoint replay, native/fake doctor, native and synthetic
`run`/`status`/`resume`, verified campaign `reduce`, offline `plot` and the
per-request [`timeseries`](WORKER.md#time-series) commands.
Runs need a host that satisfies the campaign's topology and the worker's
compiled ISA and whose guest kernel shows the campaign's runtime: no TEE for
`native`, TDX or SEV-SNP for `tdx` and `snp`, which also need a per-boot
attestation capture ([protected runs](WORKER.md#protected-runs-in-a-confidential-vm-tdx-snp)). The [statistics](STATISTICS.md) and
[workload](WORKLOAD.md) primitives define the worker's measurements.
The [C++ resolver](../../include/cpu_byteslice_oram/CONFIGURATION.md) is the
only cross-field validator; the Python schema checks shape only (unknown
fields, types, explicit zero/false). Its memory report covers modeled buffers,
with coverage stated per component; it does not bound whole-process memory.
Keep library geometry and default policy in the C++ resolver.
The offline [`preflight` command](WORKER.md#preflight) checks saved doctor
evidence against the campaign's core/domain request and each row's memory
estimate, and optionally a worker's saved `resolved.json` against its
configuration key and helper locality. It writes nothing and launches no
workers; a native `run` applies the same checks live.

Library vocabulary used in these guides (hierarchy level, carry, top, owner
and helper threads, residual tier, dense prefix, tree payload worker) is
defined in the [design overview](../../DESIGN.md) and the
[arena design](../../src/oram/levelarena/DESIGN.md). In short: the
hierarchical map merges (carries) recent entries into a ladder of levels, the
largest being the top; owner threads run those level rebuilds in the
background, helpers parallelize a rebuild or a batch, and residual tiers hold
the entries a rebuild could not place in their main bucket. The tree map for
large values moves payload bytes with optional payload worker threads.

## Tuning after a code change

A knob value never needs a rebuild: every tunable is a runtime override, so
expose a compile-time constant as an override first. A code change is a new
campaign: edit, build, `plan` into a new directory, `resolve`
with the new worker, `run`, then compare with earlier campaigns. Results from
different builds are separate environment classes and are never pooled as
repetitions; a new build measures its own saturation rates.

To compare, `reduce` each campaign into its own directory and pass every
summary to one `plot`:

```bash
python -m analysis.oram_bench reduce --campaign /data/tune-a --reducer R --output /data/tune-a.reduced
python -m analysis.oram_bench reduce --campaign /data/tune-b --reducer R --output /data/tune-b.reduced
python -m analysis.oram_bench plot --summary /data/tune-a.reduced/summary.json \
  --summary /data/tune-b.reduced/summary.json --output /data/tune-a-vs-b
```

Each summary records its campaign name, plan ID and frozen worker hash, and
each repeat group the build that ran it. Every series is labeled
`campaign@build` (first eight hex digits of the worker hash) plus its
configuration, so one series never holds two builds. `plot` refuses inputs in
which two series would get one label (the same campaign name, build and
configuration twice); give repeat runs of one build distinct campaign `name`s.
`repetitions.csv` carries `campaign` and `build_identity` columns for the same
purpose.

## Editing a campaign

The [presets](../../benchmarks/campaigns/README.md) are ordinary JSON.
Candidates are explicit named option blocks, so adding three worker choices and
three geometry choices does not silently create nine tuning combinations.
Capacity, shape, API mode, caller batch size, and repetition do form a product.
Both the expanded trial count and the sum of per-trial time caps must fit the
campaign limits **before** rows are materialized. Each cap (`max_trial_ns`)
must cover `setup_allowance_ns` (construction, fill, settle and final
verification; default 120 s), the warmup plus
its own drain deadline when there is a warmup, the measurement, and the final
drain; it has no upper limit, since large-N baseline rows can need many
hours. The campaign
limit must cover the sum over admitted rows of each row's bound (its
trial-time estimate when its candidate has a model, else `max_trial_ns`) times
`(1 + limits.planned_retries)`; `planned_retries` (default 1) should match the
launch policy's `--retries`, and preemption retries are not budgeted.
`timing.settle_requests` unmeasured requests follow the warmup in every row.
A capacity sweep that should settle at least N requests per row sets
`timing.settle_per_entry_ppm` as well: each row then settles
`max(settle_requests, ceil(capacity * ppm / 10^6))`, written into that row's
spec and used by the access-horizon check (the paper's capacity sweeps
and Table 1 presets use `settle_requests` 2^21 with 10^6 ppm). Unset, it is left out of the plan, so
existing plan and trial identities are unchanged.
`plan["cost"]` reports the cap sum, the bound sum and the bound with retries. This bounds planning and the
declared trial budget; it is not a runtime estimate. The local
coordinator separately enforces the per-worker process deadline. That timeout
is an orchestration limit, not a library performance timestamp. A worker
killed at it is committed as `failed`/`time_cap` and never retried, since a
rerun would only spend another cap.

Matched paper latency curves use a **common geometric absolute offered-rate
grid**, shared by all arms (fixed arrivals). After tuned saturation
rates are frozen, select bounds spanning the slower and faster schemes and
emit the stage's `rates` block:

```bash
python -m analysis.oram_bench rate-grid --minimum 10000 --maximum 3000000 --factor 2
```

These illustrative bounds are not measured settings. The command rounds
geometric points upward to integer ops/s, includes the maximum endpoint (the
last interval may be shorter), sets the minimum floor and leaves saturation
fractions empty. Copy its JSON verbatim into every matched stage before
planning; align seeds, shape, workload and admitted windows as well. Existing
fraction presets are templates for saturation preparation, not a shared paper
grid. `plot` uses offered input rate with a log x-axis in both single-campaign
and cross-target latency panels. Achieved throughput stays in the reduction
exports; censored, paging or unstable rows retain their eligibility labels.
Process-RSS plots include harness/runtime bytes, while the separate library
allocation model and counted audits have their own scope.

A latency stage's `rates.minimum_ops_per_second` (default 100,000) is the
offered-rate floor: absolute rates below it fail validation, and a frozen
saturation fraction below it is never launched (`status` shows
`below_rate_floor`). Baseline curves and the rows matched to them set it
lower. A stage with `"diagnostic": true` (for example a low-rate screen) also
sets its own floor; its rows carry the `diagnostic_stage`
publication blocker, stay in `repetitions.csv` (column `diagnostic`) and are
left out of every `plot` figure.

`physical_cores=16, harness_cores=1` declares a 15-core library budget, including
its caller. It does not claim the current machine satisfies that budget. The
`c4-tdx-*` and `c4-native-*` presets declare their respective runtimes. A campaign
without an `execution` block (`runtime=unspecified`) cannot launch until a concrete execution environment
is configured. CPU slots and attestation must come from that environment.
The `(4,8)` shape means a 4-byte key and an 8-byte value.

Library overrides live under `incremental`, `synchronous`, or `tree`. Pinned
schemes reject irrelevant blocks; auto selection treats them as candidate
constraints. `tree.position_map` carries a separate mode and option blocks.
Zero owners and zero tree payload workers are explicit inline choices; false
remains an explicit boolean. Omitted or null override fields mean automatic.
Zero-as-auto sentinels, such as `prefix_flushes=0`, are rejected in this
interface; use null.

The caller's `batch_sizes`, engine `batch_lanes`, and `batch_participants` are
independent. Scalar rows always have caller batch size one and fixed-count
formation; they retain engine configuration because allocated helper pools
affect resources even if no batch is submitted. Occupancy is separately stated
in ppm; `live_entries=floor(requested_capacity*occupancy_ppm/1000000)`.
Actual rounded capacity remains null until resolution. Initial presets use full
occupancy, uniform independent requests, full value readout, and 95% reads/5%
updates to existing keys. `run` executes the declared policy natively or
synthetically.

Latency presets create saturation-source repetitions plus the offered-load
rows. Relative rates retain their fraction, source IDs, and a null integer rate;
no throughput estimate is invented on this host. The local coordinator freezes rates from
verified committed source trials using the declared median of drained rates,
then floors the fraction-scaled rate to integer ops/s. Absolute-rate controls
are already integers and have no dependency. A source retains the target batch
policy as provenance; saturated submission always has a full maximum-count
batch available, so a timeout adds no formation wait in that source.

Batch formation `arrive_together` (latency stages only) delivers each batch's
requests at one instant, one batch every `batch / rate` seconds (worker
`--arrival-group`), so no request waits for its batch to fill; response time
still runs from that arrival and includes queueing behind earlier batches.
`fixed_count` keeps single arrivals at the offered rate, so at low rates most of
a batched request's response time is the wait for the rest of its batch.

### Baselines

The [baseline schemes](../../benchmarks/baselines/README.md) are:

- `std_unordered_map`, in the main worker;
- `h2o2ram` and `h2o2ram_shipped`;
- `sonic_zingoram` and `sonic_zingoram_recursive`.

The last four run in their own workers (`benchmarks/baselines/`). A campaign
freezes one worker, so each baseline has its own campaign. A baseline must be
named explicitly; `auto` never resolves to one.

- **Overrides.** Their knobs live in the `h2o2ram` and `sonic` blocks.
- **Keys.** `Shape.key_layout: dense` makes key i the little-endian integer i.
  The index ORAMs need it at (4, 8), and the presets use it for every
  Standard ORAM row so that each baseline row has a matching row of ours (our
  map hashes keys with a keyed PRF, so the layout does not change its cost).
- **Row labels.** Every row carries `security` (`oblivious`,
  `oblivious_position_map_outside` or `not_oblivious`), `key_layout` and
  `stored_value_bytes`. A synthetic rehearsal labels its rows `not_oblivious`.
  Both SONIC schemes also carry `position_lookup: included` (each timed
  access includes its position lookup, recursive or outside the array; a
  data-tree-only row would be `excluded` and is not complete-access
  throughput); other schemes have none. The summary (schema v6, which includes
  the amplification inputs), the CSV and the plot series and families all carry
  the labels.
- **Planning skips.** Planning skips miss workloads for the index ORAMs, batch
  rows for the scalar-only baselines, and SONIC rows without dense keys
  (neither index ORAM can report a miss, and SONIC needs dense indices). A
  candidate's optional `trial_time` models (a per-arm time cap: an arm's N
  sweep ends at the largest N whose estimated trial fits) lengthen a row's window to
  its coverage window, and skip rows that would exceed `max_trial_ns` as
  `trial_time_cap`. A model's access and per-entry setup times scale with
  capacity as a power law from its `reference_capacity`, and `key_bytes`,
  `value_bytes` or `api_mode` restrict it to rows of those widths or that API.
  A candidate with models must cover every row it runs: the most specific
  match applies, and a row no model covers is a planning error. An
  offered-load row covers its window at the offered rate (a saturation
  fraction f takes access_ns / f per access), so low rates at large N are
  what the cap prunes first.
- **Time models from pilots.** `fit-trial-time --campaign PILOT ...` reads
  each completed pilot trial's drained rate and phase times and fits one
  model per scheme, width and API at the largest pilot capacity. Its
  exponent is the steeper of the access and setup slopes between the two
  largest capacities. `--margin-ppm` (default 25%) is added to every time,
  and `--apply PRESET` writes the models into a preset's candidates of those
  schemes, interpolating widths the pilot did not run.
- **Side files.** A worker's `--build-info` names the files it reads beside
  itself, such as H2O2RAM's planner cache. `resolve` copies and hashes them into
  `build/`, and `run` re-checks them before launching.
- **H2O2RAM's planner.** `prepare-h2o2ram` runs its host-timed planner once per
  distinct row, before `resolve`. Rows run by block size and then capacity, so
  each row's `planner_ns` is its marginal cost. Each child is capped at the
  host headroom (`RLIMIT_AS`) and, with `--timeout`, killed after that many
  seconds. The whole job stops at `--job-timeout` (default: none); rows it
  never reached are `not_attempted`. A failed or killed row stops only the larger rows of its block
  size, and `resolve` skips every unprepared row as a planner-cache miss. Each
  run appends its outcomes, with wall time and peak RSS, to
  `prepare_h2o2ram.json` in the campaign, and exits 2 if any row was not
  prepared.

## Identity and schema contract

Campaign formats use `schema_version: 1`; native worker resolutions use
`worker_schema_version: 2` with recorded resolver inputs. Unsupported versions
fail closed. Raw events are the C++ binary format, not a Python envelope. Use
`schema {campaign,overrides,worker-resolution,environment,manifest,attestation,attestation-verdict}` to export
the structural JSON schemas directly from the typed definitions. `validate`
also applies cross-field checks that JSON Schema alone does not express.
There are no permissive extension dictionaries, aliases, floating-point inputs,
unknown keys, duplicate JSON keys, negative numbers, or non-finite numbers.
Inputs distinguish booleans from integers. All integer fields are uint64;
timestamps/durations use nanoseconds unless a field explicitly ends in `_us`
or `_ms`. Sizes use bytes; fractions use integer millionths (`_ppm`).

- Omitted fields use their documented dataclass defaults and normalize to the
  same representation as those explicit defaults. Null overrides mean auto;
  null observations mean unavailable. Observed zero is a number with coverage.
- Canonical serialization is ASCII JSON, sorted object keys, no insignificant
  whitespace, `ensure_ascii=true`, and decimal integers. Array order is retained.
  IDs are a type/version prefix plus lowercase SHA-256 of those bytes.
- A logical trial hashes all its normalized execution, resource, instrumentation,
  timing, workload, override, capacity/width, API/batch, arrival/rate, seed, and
  repetition inputs. Source/build/dependency identities are included,
  including null when unknown. Stage and candidate labels distinguish arms.
  The campaign name, scheduling order, and planning cost caps are campaign-level
  metadata; they change the plan ID, not unchanged logical trial IDs.
- Workload and arrival seeds use the first eight SHA-256 bytes, big endian, of
  `[base_seed,repetition,purpose]`, or `[base_seed,repetition,purpose,seed_stream]`
  for a stage that names its own `seed_stream`. They are shared across schemes
  and scalar/batch modes. A stage's `seed_role` (`screening`, `finalist`,
  `held_out`) labels its purpose; the planner rejects a campaign whose
  `held_out` stage reuses a `screening` stage's seeds. Execution order
  hash-sorts IDs with `order_seed`, with all saturation sources ahead of
  dependent rows; no Python PRNG-version dependency.
- A physical environment is **not** folded into a logical trial. Attempts bind
  to immutable environment and resolved-plan records. The environment class
  (`environment-class-v5`) is the worker binary hash, library header hash,
  CPU model and family/model/stepping, topology, runtime, dependency closure
  (every shared object the loader resolves for the worker, hashed), kernel
  release, kernel command line (without its boot-disk parameters) and THP
  modes. Git state and Python
  tooling are recorded per attempt but excluded, so a coordinator or reducer
  fix does not strand a campaign. `read_plan` checks `plan.json` against its own
  `plan_id` and does not re-expand it with the current planner. `status`
  reports completions per environment class.
- Changing schema semantics requires a version bump and an explicit adapter;
  only explicitly supported formats are accepted.

The worker's `resolved.json` (`worker-resolution`) records actual
geometry/options as typed `choices` with provenance and reasons, no null or
`auto` values. It is an observation rather than an exact-plan import format.
`resolve` pins overrides, construction checks agreement, and `run` compares
each attempt's configuration key with the frozen one.

Raw events have no Python schema. The binary protocol and replay contract are
in [WORKER.md](WORKER.md). They cover phase boundaries, unaggregated count
windows, request outcomes and histogram intervals. A request has a unique ID
and optional batch ID; completed requests require ordered
arrival/dispatch/completion timestamps. Censored requests have no fabricated
completion. Request response/queue histograms and batch-call service histograms
carry different weightings. Histogram version 1 specifies 14,592 dense bins,
with portable lossless checkpoint encoding and a shared accumulator; see
[the format contract](STATISTICS.md). The C++ checkpoint reader checks bin
counts, occupied extrema, feasible bin sums and CRC integrity; its reducer
rejects duplicate, missing, or overlapping intervals.

Memory CSV observations are process and cgroup quantities, not a library
allocation total, and must not simply be summed with the resolver's modelled
bytes. Plan rows expose logical dataset bytes only, with null allocation peaks,
storage, and fill costs; `resolve` adds each row's modelled estimate, which bills the library's reserved
bytes (its buffers with allocator rounding) and falls back to requested
bytes for a resolution without them. An estimate can prove a row
infeasible; it cannot prove a row fits RAM. Raw-storage limits remain a
deferred gate until logging bandwidth and duration are known.

A complete manifest requires correctness, no event loss, artifacts with safe
relative paths and SHA-256 digests, and ordered measurement/drain boundaries.
Schema validation does not verify file contents, runtime attestation, locks, or
durability. Those are operational checks, not claims made by this planner. The
local POSIX commit/recovery implementation, its synthetic failure tests and
protected runs are described in [WORKER.md](WORKER.md). Output publication uses local POSIX filesystems.

## Paper analysis tools

Scripts in `analysis/`; none launches a campaign worker.
[REPRODUCE.md](../../REPRODUCE.md) says which of them produces each of the
paper's numbers:

- **`paper_numbers.py`** reads the reduced summaries of the
  [paper presets](../../benchmarks/campaigns/paper/README.md) (and a few raw
  worker files) and writes every Table 1 cell, the data of Figures 7 and 8 and
  every derived number of the text beside the paper's value.
- **`paper_micro.py`** runs the release's drivers with the paper's arguments
  for the micro-benchmark numbers (table rebuild against H2O2RAM, routing
  locality, VP2INTERSECT, tables per lookup, write throughput, eviction
  against EnigMap, memory latency, the whole-L3 check) and summarizes them
  ([benchmarks/oram](../../benchmarks/oram/README.md#paper-micro-benchmarks)).
- **`plot_stash_tail.py`** draws Figure 9 from an export of
  `run_stash_tail_long.py` and prints every stash number of Appendix A.3;
  `stash_rows/paper.json` lists the paper's trees and seeds.

**`crossover_export.py`.** `--summary SUMMARY.json [--resolution
RESOLUTION.json] --output DIR [--schemes A,B] [--per-batch]` writes
`crossovers.json` and `widths.csv`, per fixed requested capacity and API mode
(per batch size with `--per-batch`); it refuses a frontier whose actual
capacity changes with width. Per width it keeps each scheme's fastest row
(candidate and batch named) with drained req/s, allocated amplification
(`library_reserved_bytes`, else `library_modeled_bytes`, over
`logical_bytes`) and RSS amplification (`trial_peak_rss_bytes` over
`logical_bytes`). Throughput, allocated and RSS crossovers are separate
bracketing widths in bytes, every sign change listed, or "no crossing" with
the winner. Rows keep the resolved scheme, configuration key, `same_as`,
thread counts by role and the `hierarchy.`/`tree.`/`position_map.` choices;
blocked rows stay, labelled; "frozen" candidates are a separate arm; auto
rows are checked against the measured winner (auto is the uncalibrated
`DefaultRule`). `--resolution` is required when auto rows are present, since
only the resolution names auto's scheme.

**`bandwidth_join.py`.** `--rebuild FILE... --bandwidth FILE...
[--json] [--csv OUT]` joins arena rebuild rows (`--write-only --fit-rows
--stage-times` output, or `fit-rebuild --rows` JSONL) with a
`cpu_mem_bandwidth_benchmark --sweep` ceiling on threads = 1 + owners +
top helpers (inline = 1; the run row's `inline` field says which; prefix a
file whose rows lack that field with `inline:`). Per row: records/s, ns/access, speedup over the inline
row of the same shape, the streaming ceiling (GB/s = 10^9 B/s), prepare/
finish/fold/job ms, and MODELED traffic = 64 B x the levels' touch + residual
+ offer lines per access x records/s with its fraction of the ceiling. Modeled
traffic counts line touches (cache hits included, no hardware counters); the
ceiling is a streaming read of private buffers; the tool prints that neither
proves memory- or compute-bound. Rows without a ceiling at their thread count
keep nulls and a reason.

**`stall_bracket.py`.** `bracket --benchmark THROTTLED --rate-kops A
[--ks 1,2,4 | --k-max 64 --steps 4] -- CONFIG` runs
`cpu_byteslice_level_arena_benchmark_throttled`, one trial per point: per
owner slowdown K the independent rebuild rate R(K) (closed-loop `--write-only`
records/s of the same configuration) and the paced run's attributed stall
(`backpressure_delayed > 0`, never plain queue time), the ratio R/A, delayed
%, max/p99 stall us, and the bracket (smallest stable ratio, largest stalling
ratio) with status `bracketed`, `non_monotone`, `no_stall_anywhere` or
`stall_everywhere`; the unthrottled inline control runs once. Use helpers 0
and lanes 1 (helpers are not throttled) and `--write-only`. `model [--probe
FILE...]` prints the model's predictions for B=2/4/8 (1x/2.25x/4.5x rebuild
speed; mean 1.5/0.92/0.59 and worst 2/1/0.67 tables per access over log2 N),
labelled "predictions, not results", beside the probe-plan-shape benchmark's
measured mean/max tables per access over log2 N and the deviation sources.

**`compare_share.py`.** Comparison time inside a merge without
timing any call: `--counted` takes `cpu_byteslice_level_arena_benchmark_compare_counted`
output (`COMPARE_COUNT`: the window's 64 x 64 key-field comparisons by kind,
counted by compiled-in relaxed counters at the four rebuild-only primitives;
the merge is oblivious, so the counts are the same in any build and at any
thread count), `--merge` the plain build's `--fit-rows` output of the same
configuration (merge ms = the levels' `job_nanos`), `--kernel` the dedup
kernel benchmark (median ns per call over loops of 10^5+ calls, including its
`self` rows). It reports comparison ms priced at the native and the xor-min
rows, merge ms, the fraction, comparisons per access and the comparison-only
fallback/native ratio. Loop rows are L1-resident whole one-field kernels, so
operand misses inside a merge are left out and loads a merge shares are
charged per nest; the whole-merge native/fallback ratio needs merge times
from both builds.

The dedup kernel driver also accepts `half_unique` as its third positional
argument (`2000000 1 half_unique`): exactly 32 live slots per bucket and
distinct keys, with scalar oracle checks outside timing. Select and retain
the fixture when pricing `compare_share.py` counts; this key-field-only loop
omits values and tags. The overlap/zero-key control fixture is the default. Loop prices
include public loop/digest bookkeeping and no empty-loop subtraction is
applied, so counts times these prices remain estimates, not direct in-merge
comparison clocks or public request throughput.

The other scripts directly in `analysis/` each start with a docstring giving
their inputs and limits:

| Script | Purpose |
|---|---|
| `gen_stash_capacity_table.cpp`, `gen_residual_tier_bound.py` | Generate the rebuild's stash capacity table and residual tier coefficients in `src/oram/rebuild/` |
| `stash_capacity_certificate.py`, `modulo_occupancy_certificate.py` | `stash_capacity_certificate.py` certifies every stash-table entry with outward-rounded arithmetic; `modulo_occupancy_certificate.py` re-certifies those entries and the residual-tier selector's depths (exponents 67..200) under the radix map's modulo bias. Run both after regenerating (see [bound certification](../bound_certification/README.md)) |
| `residual_occupancy_certificate.py` | Outward-rounded interval arithmetic and balls-in-bins excess bounds shared by `gen_residual_tier_bound.py` and the two certificates |
| `level_arena_model.py` | Analytical storage/routing model of the level arena; `allocation_reconcile.py` compares it with counted allocations |
| `occupancy_tail.py` | Empirical occupancy distributions from the occupancy observer, beside the certified capacities |
| `run_stash_tail_long.py`, `stash_requirement.py`, `plot_stash_tail.py`, `plot_stash_vs_n.py` | Long stash-tail runs of the tree ORAM (`stash_rows/paper.json`: the paper's rows), the stash lanes they imply, Figure 9, and the stash size against N |
| `timing_summary.py` | Summaries and identity checks for the constant-time instruction test (`tests/timing/`) |
| `arena_harness_gate.py`, `preroute_rows.py` | Arena-benchmark analyses: the paced path's harness-overhead gate, and the pre-routing on/off comparison and merge-time split |

## Tuned presets and strict topology checks

There are no tuning profiles. A tuning campaign's winners are recorded as
explicit per-scheme override blocks in a versioned tuned preset, validated on
held-out rows, and run as an ordinary arm labeled apart from default auto.

`doctor` retains per-CPU package/core, sibling and unified-L3 evidence, checks
cross-CPU consistency, and names one allowed logical CPU per exposed physical
core. Optional `--require-physical-cores 16 --require-cache-domains N` (1 on
a single-L3 Xeon guest, 2 on a two-CCD Zen 5 guest) requires those exact exposed counts. A mismatch or missing required evidence writes the
environment record and returns status 2. This does not pin threads or establish
physical-host CCD placement or protected execution. Clock accuracy is
cross-checked (`worker --clock-check`, WORKER.md): `clock` reads `tsc_validated`
only when an invariant TSC is the clocksource and passes every check.

Environment records optionally include typed `topology` evidence and the
library header hash. Classes use `environment-class-v5`, including
the dependency closure.
