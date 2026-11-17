# ORAM benchmarks

This directory holds the benchmark drivers for the library: whole-map
measurements through the public API, diagnostics of the hierarchical
(level-arena) engine, microbenchmarks of the routing and deduplication
kernels, the tree ORAM's stash and eviction studies, and a few host
characterization tools. The design they measure is described in
[DESIGN.md](../../DESIGN.md), the
[level-arena design](../../src/oram/levelarena/DESIGN.md) and the
[tree design](../../src/oram/tree/DESIGN.md).

No measured results are recorded here; every driver prints its own rows
(human-readable tables and/or one JSON object per line).

## Building and running

Each `.cpp` file is a standalone target named after its file stem. A
top-level configure builds them by default (`CPU_BYTESLICE_ORAM_BUILD=all`):

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DCPU_BYTESLICE_ORAM_BUILD=all
cmake --build build -j
./build/benchmarks/cpu_byteslice_level_arena_benchmark --help
```

The binaries land in `build/benchmarks/`. A few targets are the same source
compiled with an instrumentation macro (see [Instrumented
variants](#instrumented-variants)); release builds
(`CPU_BYTESLICE_ORAM_RELEASE`) refuse those macros.

Campaign measurements (many trials, alternating arms, placement, telemetry)
are run through the Python harness, whose command-line interface is
documented in [analysis/oram_bench/README.md](../../analysis/oram_bench/README.md)
and whose single-trial worker protocol (the `cpu_oram_benchmark` binary) is
in [WORKER.md](../../analysis/oram_bench/WORKER.md). The reproduction guide
for the campaigns is [benchmarks/campaigns/README.md](../campaigns/README.md).

General practice for the standalone drivers:

- Pin the process (`taskset -c N`, or the driver's own `--cpu` / `--cpus`
  flag) and keep other load off the measured cores. Single-core kernel
  drivers should run on one pinned physical core.
- Time loops of many operations for at least a fraction of a second; the
  drivers repeat or chunk their timed regions so that no single operation
  is timed alone.
- Compare instrumented builds only with runs of the same build and
  placement: the counters and clock reads add overhead.
- On a cloud VM, check the usable L3 and the placement of each boot first
  (`cpu_cache_latency_benchmark`, `cpu_host_topology_probe`); both can vary
  between boots of the same instance type.

Terms used below: a *level* is one hashed table of the hierarchy; a
*carry* is the batch of records one level hands to the next when it fills;
a *rebuild* is the oblivious merge-and-route that builds a level from its
inputs; the *dense prefix* is the small, fully scanned region in front of
level 1 that collects the online stash's flushes; *owners* are the
background threads that run rebuild jobs (*helpers* assist the top level's
owner, *lanes* split one stage across threads); a *residual stash* or
*tier* holds the few records a bucket could not take. The level-arena
design document defines them in full.

## Public-map and hierarchy measurements

| Target | Measurement |
|---|---|
| `cpu_oram_benchmark` | The campaign worker: one resolved public-API trial (scalar or batch, saturated or paced), including telemetry; also the `std_unordered_map` throughput-ceiling baseline |
| `cpu_oram_allocation_audit` | Modeled memory of each resolved plan against counted heap allocations and process memory at construction, fill, access, and destruction |
| `cpu_byteslice_level_arena_benchmark` | The hierarchical engine under saturation or paced arrivals: rate, response times, byte bill by role, per-level rebuild phases, preparation hit rates, probe shape, and park reasons |
| `cpu_byteslice_oram_map_benchmark` | The public byte and typed adapters in synchronous and incremental modes |
| `cpu_byteslice_probe_plan_shape_benchmark` | The size composition of the public probe plan over an access cycle |
| `cpu_byteslice_occupancy_observer` | Diagnostic: occupancy of every residual structure against its capacity (never a performance row) |

### `cpu_oram_benchmark`

Run with no arguments or `--help` for the worker's interface; the full
protocol is in [WORKER.md](../../analysis/oram_bench/WORKER.md). It resolves
the requested scheme (`auto`, `hierarchical_incremental`,
`hierarchical_synchronous`, `tree`) with `resolve_options`, places the
caller, harness and engine threads, builds the map with `make_map` and runs
the shared trial loop. `--scheme std_unordered_map` runs the same loop over a
plain `std::unordered_map` (one thread, no security) as the throughput
ceiling.

Mixed workloads in the campaign worker, the arena benchmark and the
public-map benchmark use `exchange` for scalar writes: each write reads the
previous value and replaces it in one access. Batched writes request
`BatchOp::kReadThenWrite`. These writes are therefore probed, although the
library's default `write` / `insert_or_assign` is a blind (unprobed) write.
Initial fills and the arena benchmark's `--write-only` mode use blind writes.

### `cpu_oram_allocation_audit`

```text
cpu_oram_allocation_audit [--capacities LIST] [--shapes k:v,...]
                          [--schemes incremental,synchronous,tree]
                          [--cores N] [--accesses F] [--sites] [--steady-sites]
```

Replaces the global allocator with a counting one, resolves each row's plan
the way a campaign row does, builds, fills (direct initialization for a
hierarchy, insertions for a tree) and runs `F` times capacity mixed accesses.
It prints one `AUDIT_ROW` JSON object per row on stdout and a table on
stderr, attributes every allocation site to a library role, and checks that
destruction returns every byte. `analysis/allocation_reconcile.py` matches the
combined allocations to the layout model's per-level sizes. All rows run in
one process; the audit resets the peak RSS before each row
(`/proc/self/clear_refs`), so each row's `hwm` is its own peak, and prints
`"hwm":null` where the kernel refuses the reset. The audit runs every row and
exits 1 if any row failed (`"ok":false`) or left bytes live after destruction;
the reconciler reports failed rows and then exits 1 as well.

`--sites` names each site by running `addr2line` on the raw return
addresses, which works only in an executable with debug information and
without position-independent code. Configure a separate build for it:

```sh
cmake -S . -B build-audit -DCMAKE_BUILD_TYPE=Release -DCPU_BYTESLICE_ORAM_BUILD=all \
    -DCMAKE_CXX_FLAGS='-g -fno-pie' -DCMAKE_EXE_LINKER_FLAGS=-no-pie
cmake --build build-audit --target cpu_oram_allocation_audit
build-audit/benchmarks/cpu_oram_allocation_audit --capacities 134217728 --shapes 4:8 \
    --schemes incremental --cores 16 --sites > audit.txt
python3 analysis/allocation_reconcile.py audit.txt --csv audit.csv
```

In the default (position-independent) build every block is `unattributed`:
the reconciliation says so in a note, keeps the arena whole and omits the
counted-main rows. Two quantities compare the library with the main-table
model 64·M·W (M main buckets of the resolved ladder, W stored bytes per
slot). `library_live_over_model_main` is the library's live requested
bytes over the model. It needs only the resolved plan, so it is reported
from either build, with or without `--sites`. `total_minus_main_pct_of_main`
is the bytes outside the counted main tables, as a percentage of them; it
needs site names. When every level block matches its model size, the second
equals the first minus 1, in percent. The access phase allocates nothing (the
`steady` phase reports `allocations` 0), so `--accesses 0.05` shortens the run
without changing the counts; the default is 2 capacities of accesses.

### `cpu_byteslice_level_arena_benchmark`

`--help` lists the full interface. The main flags are `--capacity`, `--key`,
`--value`, `--branching`, `--digit`, `--owners` or `--rebuild-threads`,
`--top-helpers`, `--rebuild-lanes`, `--accesses`, `--reps` and `--latency`.
Its default closed loop measures saturation; `--reps` repeats the
measurement on fresh engines and reports the median rate.

- `--rate KOPS` selects scalar fixed-rate arrivals, with optional
  `--settle N` unmeasured requests first. Response times in that mode
  include time spent queued after the scheduled arrival. The window starts
  its own arrival schedule after the settle, with an empty queue.
- Every request draws a key the warm-up inserted, so the benchmark counts
  the lookups that found their key and refuses a run in which any missed.
  Returned values are not compared.
- `--write-only` measures unprobed insertion and rebuild demand; use the
  campaign worker for reads and probed writes at an offered rate.
- `--batch N` issues the workload through `access_batch` with `--lanes`,
  `--participants` and `--parallel`; `--cpus` pins the threads explicitly.
- `--place` pins the request thread and batch participants to one L3 domain
  and the far owner groups to another (multi-L3 hosts only);
  `--near-max-level` sets the near/far boundary.
- `--value-workers N` threads start inside the map and inherit the request
  thread's affinity, so with `--cpus`, or `--place` on a multi-L3 host, the
  benchmark refuses to run unless `--value-cpus` places them.
- `--stage-times`, `--merge-rows`, `--probe-counts` and `--fit-rows` add
  per-stage times, per-merge rows (read by `analysis/preroute_rows.py`),
  probe tallies, and `FIT_ROW` JSON lines for the rebuild cost-model tuner
  (`analysis/oram_bench/tuner.py`).

Under `--rate` or `--latency` the benchmark also reports request-correlated
rebuild backpressure: the engine counts the requester's wait for a free
dense-prefix slot (`LevelArenaEngine::requester_backpressure()`, slow path
only, no clock or atomic on the fast path) and the benchmark reads it around
each request. A request with a nonzero delta was delayed by rebuild by
exactly that many ns. The report gives the delayed requests, all completed
requests, their ratio, the maximum (exact) and p99 (over delayed requests)
attributed stall, and the total; `--fit-rows` carries the same as
`backpressure_*` fields in the `run` row, with `completed_records_per_s` and
`flushes_per_s`. In `--batch` mode each request is charged its whole batch
call's delay, and the output says so.

`--attribution 0` drops those per-request reads. It is the control arm for
`analysis/arena_harness_gate.py`, which checks that the reads do not perturb
the response times; the `run` fit row carries `response_count` and
`response_p50/p99/p999/max_ns` for it.

The default arena planner can round a capacity request up to the next
capacity its geometry supports; use the actual capacity reported in the
output (`FIT_ROW`, `COMPARE_COUNT`) for settle and window lengths. The
command-line header echoes the request.

### `cpu_byteslice_oram_map_benchmark`

```text
cpu_byteslice_oram_map_benchmark [entries=4096] [operations=65536]
```

Fills each public adapter with `entries` distinct keys (direct initialization
where the adapter offers it, otherwise one insert per key; a column says
which) and times a deterministic hit-only workload with one update per seven
reads. Prints fill time, ns per operation, Mops/s and a checksum per row.

### `cpu_byteslice_probe_plan_shape_benchmark`

```text
cpu_byteslice_probe_plan_shape_benchmark [capacity] [branching] [top_digit] [sample_every] [flushes]
cpu_byteslice_probe_plan_shape_benchmark --capacity N --branching B --top-digit D
    --key-bytes K --value-bytes V [--accesses N] [--owners N] [--prefix-flushes N] ...
```

Fills a map and walks one full cycle of accesses, sampling `PlanSnapshot()`
every `sample_every` accesses, and prints how many tables of each size an
average access probes (a dense table is scanned in full, a hashed one probed
per bucket). After every scalar `find` it also reads `last_probe_tables()` /
`last_probe_buckets()` and ends with one JSON line of per-access mean/max
tables and buckets. Capacity is the requested map capacity; a zero top digit
or flush count lets the geometry planner choose it. `flushes` is the dense
prefix radix r0 (stash flushes per prefix), not a trial count. Only public
quantities are reported.

### `cpu_byteslice_occupancy_observer`

Built with `MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER`, whose hook sees
secret-dependent occupancies; its output is a diagnostic, never a
performance row. It fills a map, runs `--settle` unobserved accesses
(default: capacity), then `--accesses` observed ones (default
max(10^7, capacity)): 95 % reads and 5 % updates of existing keys back to
back, scalar or `--batch N`. The default mode, one caller with
`--owners 0 --top-helpers 0 --bottom-helpers 0 --lanes 1`, is labelled in the
JSON. For every structure (stage, radix, merge, retained-carry and
dense-builder stashes, DFS range leaves, final tiers; each level and index)
it records capacity, exposure count, maximum, an occupancy histogram and the
per-job maximum sequence. Capacities are the engine's own, so a natural
overflow ends the run and is recorded under `failure`.

```sh
python3 analysis/occupancy_tail.py out.json [--block-jobs M] \
    [--certificate analysis/bound_certification/code/configuration_space_2p20.json]
```

reports the maximum load, the histogram and P(occupancy >= k) with one-sided
Clopper-Pearson bounds over blocks of M consecutive jobs (exposures within one
job are correlated and are not used as separate samples), and compares the
capacities with the certified configuration of the same shape (use the
`configuration_space_2pK.json` file for the observed capacity 2^K). It fits
nothing: zero observed overflows do not establish a 2^-64 failure bound,
which comes from the [certification](../../analysis/bound_certification/README.md).
The online stash unit and the dense prefix hold public counts and are not
observed.

## Routing and deduplication kernels

### `cpu_byteslice_stash_rebuild_benchmark`

The routing network that rebuilds a level, in isolation from the engine.

- Positional mode, `[min_log2] [max_log2] [radix] [value_bytes]
  [stash_buckets]` (defaults 6 .. 20 in steps of 2, radix 3, 16, 1): routes
  tables of 64-slot buckets at load 0.5 through the grouped and
  cache-oblivious butterflies, a radix pass and the fold, and reports ns per
  merge-split byte line.
- Routing rows (any `--` flag selects flag mode; one JSON object per line):
  `--network flat|grouped6|cache_oblivious|butterfly512[,..]`, `--key-bytes
  4|8`, `--value-bytes`, `--live-entries`, `--seed`, `--reps`, `--threads`,
  `--max-bytes`, with a correctness and overflow check per row. `flat` is the
  standard stage-major butterfly, `grouped6` fuses six levels per tile, and
  `cache_oblivious` is the network the engine runs. `butterfly512` is the flat
  butterfly on 512-slot buckets (`--live-entries` / 256 buckets, no stash, a
  surplus fails the row, one thread); it has three fewer levels, so compare
  total `route_ms` at the same `--live-entries`, not per-stage figures. The
  512-slot kernel is checked against a slot-by-slot reference by
  `tests/oram/cpu_byteslice_slot512_kernel_test.cpp`.
- `--network grouped6_unfused,cache_oblivious_unfused` is the fusion ablation:
  the benchmark-only traversals in `cpu_byteslice_routing_comparator.hpp`
  keep the production traversal, leaf/split rules, tag pruning and stage
  stashes, and only the four-bucket quad call is unfused. Compare fused and
  unfused versions of the same traversal, alternating their order.
- `--instances P [--cpus LIST]` runs P independent routes at once, one pinned
  thread each (instance i on the i-th CPU of LIST, own table, seed
  `--seed + i`), the way the engine rebuilds several levels at the same time,
  so the routes share the memory bandwidth. `--reps` is then the exact round
  count; a round starts every instance's route at one barrier and waits for
  the slowest at another, once per network, with the networks' order
  alternating each round. Each instance restores its table with streaming
  stores, so every route starts from DRAM. One untimed, verified route per
  network precedes the rounds. Rows (`"mode":"instances"`) give the mean and
  median per-instance route time, the round wall time, per-round arrays and
  `anon_huge_bytes`; an `instances_ratio` row compares the networks paired by
  round. Pass one CPU per physical core in LIST: where SMT siblings are
  numbered adjacently, `1-8` spans five physical cores, including core 0's
  sibling, three of them twice; pass `2,4,...,16` there. The paper's
  eight-instance run is
  `analysis/paper_micro.py routing-locality`
  ([Paper micro-benchmarks](#paper-micro-benchmarks)).
- Pair rows, `--pairs N`: N isolated merge-splits on two 64-slot buckets
  (load 0.5, tag bit 0). `--arm current|compress_expand|bitonic|slot512|all`
  (default all) picks the kernel: `current` is `MergeSplitPairStash`;
  `compress_expand` is a direct VPCOMPRESSB/VPEXPANDB merge-split; `bitonic`
  is the full 28-stage bitonic network over the pair's 128 slots (swap masks
  planned from the keys inside the timer, every stage applied to every routed
  line); `slot512` is the same merge-split on a pair of 512-slot buckets
  (`cpu_byteslice_slot512_kernel.hpp`), which has no residual stash, so a
  surplus is an overflow (`"stash":"none"`) and `--load-per-bucket` counts
  records per 64 slots. Compare arms per input record
  (`ns_per_input_record`), not per merge-split. All arms share the generated
  records, the routing predicate, the overflow contract and one verification
  (every record exactly once across both buckets and the stash, value intact,
  correct side). Each arm runs on two pools sized in bytes of bucket data,
  `cache_resident` (2.5 MiB) and `dram_streaming` (40 MiB); compare these
  sizes with the host's LLC before calling a row DRAM-bound, and use
  `--pool-bytes B` for one `custom` pool of another size. The pool is
  restored from a pristine copy outside the timer and the timer accumulates
  over pool-sized chunks; a pool/count that cannot form chunks of at least
  two calls is reported as `skipped_timing_granularity` rather than timed.
  `--load-per-bucket R` (test only) raises the load so that records really
  shed into the stash.

See the usage comment at the top of the source for every flag.

### `cpu_byteslice_dedup_kernel_benchmark`

```text
cpu_byteslice_dedup_kernel_benchmark [pairs_per_rep=2000000] [reps=7] [legacy|half_unique]
```

Times the cross-bucket key-deduplication kernel (the all-pairs match mask of
two 64-slot buckets) per bucket pair, with every implementation the build
supports: native VP2INTERSECT, the portable AVX-512 fallback the library uses
without it, and a simpler compare-and-rotate baseline; `self` rows time the
within-bucket dedup. The `legacy` fixture is roughly 3/4 occupied with
overlapping keys and real zero keys; `half_unique` has exactly 32 real slots
per bucket and unique keys, matching the load and key uniqueness of a
rebuild's merge. Both key widths and the within-bucket rows are checked
against an independent scalar oracle outside the timer. Only key fields are
loaded, so this is not a payload-width cost. Pin it to one core.

### `cpu_byteslice_exact_dedup_benchmark`

```text
cpu_byteslice_exact_dedup_benchmark [iterations] [repetitions]
```

Times the complete stored-key cross, self, four-destination and class masks
at 4, 8 and 16 bytes, plus dense matching with 16 and 64 prepared queries,
on L1-resident buckets. Each row checks an independent scalar oracle before
timing. Pin it to one CPU; these kernel timings do not establish whole-engine
performance or which path the engine dispatches to.

### `cpu_byteslice_table_rebuild_benchmark`

```text
cpu_byteslice_table_rebuild_benchmark --mode init|chain|umap-init|umap-merge|sort-merge|direct-merge
    [--capacity N] [--key N] [--value N] [--digit D] [--reps N] [--window N]
    [--seed N] [--cpu LIST]
```

Times building one hashed table with residual recovery, for the comparison
with H2O2RAM's level build. `init` is `ByteMap<false>::initialize` of
`capacity()` distinct records on a fresh, prefaulted map per repetition.
`chain` runs a branching-2 synchronous map that is full and written with
repeating keys, and times each write that completes a dense prefix: the
cascade that builds level k's table from the prefix and levels 1..k-1. It
prints one row per cascade depth and per-(level, digit) job medians; a
digit-2 job below the top merges two tables of half its size. The
conventional (not oblivious) comparators build the same table sizes at
K4/V8 (4-byte keys, 8-byte values): `umap-init` / `umap-merge` (a default-constructed `std::unordered_map`
filled one record at a time, from an array or from two maps of half the
entries) and `sort-merge` / `direct-merge` (64-slot buckets at load 1/2
rebuilt from half-loaded tables, in place by `std::sort` and one placement
pass, or by hashing each record straight into its bucket in separate
storage, [cpu_bucket_table.hpp](cpu_bucket_table.hpp)). Their keys are
distinct and hashed inside the timer. `--cpu LIST` runs one instance per CPU
side by side, starting every timed region together, to measure rebuilds that
share memory bandwidth
([parallel_instances.hpp](../support/parallel_instances.hpp)).

The matching H2O2RAM driver, `h2o2ram_routing_bench`
([source](../baselines/h2o2ram_routing_bench.cpp), whose header comment is its
full reference), is built into `build-baselines/h2o2ram/bin/` by the H2O2RAM
baseline build ([Fetch and build](../baselines/README.md#fetch-and-build)). It
times H2O2RAM's released `OHashBucket::build` on the shape of
`cpu_byteslice_stash_rebuild_benchmark`'s rows (N/32 buckets of 64 slots, load
1/2) and pairs with this benchmark's `init` and `chain` modes:

```text
h2o2ram_routing_bench --key-bytes 4|8 --value-bytes B --live-entries N --threads T
    --reps R --seed S --bucket-slots 64|128 [--merge 0|1] [--planned 0|1] [--cpu LIST]
```

`--merge 1` builds the table from two half-size tables, as H2O2RAM's rebuild
does from its lower levels. `--planned 1` builds the table type H2O2RAM's
ORAM would choose for a level of N blocks and reads that choice from the
planner cache, which must be prepared first
([H2O2RAM's planner cache](../baselines/README.md#h2o2rams-planner-cache)).
`analysis/paper_micro.py table-rebuild` runs the paper's comparison of the two
drivers on one core and computes the speedups
([Paper micro-benchmarks](#paper-micro-benchmarks)).

## Tree measurements

### `cpu_tree_oram_benchmark`

```text
cpu_tree_oram_benchmark [min_log2_n] [max_log2_n] [value_list] [memory_limit_gib]
                        [reps] [key_bytes] [max_cycle_accesses] [mode]
```

Fills each map, drains it, and times a permuted read cycle. Defaults are
capacities 2^16 through 2^20, values 64/256/1024/4096 bytes, a 12-GiB
estimate limit (larger configurations are reported as skipped), three
repetitions, eight-byte keys, and a 131,072-request cap on the timed cycle.
The fill always covers the full capacity. `--help` prints the usage; a
malformed or out-of-range argument is refused with exit status 2. The mode
selects the rows:

| Mode | Rows |
|---|---|
| 0 | Default tree (`TreeOptions{}`, so width-selected payload workers) and the hierarchy holding complete values; in `cpu_tree_oram_benchmark_phase_timed` also the tree's position-map and tree phases per read |
| 2 | Synchronous tree and payload-worker counts 1, 2, 3, 4, 6, 8, 10 and 12 |
| 5 | Tree with 0 through 4 payload workers, serial hierarchy, and hierarchy batches with 1, 2, or 4 participants |

Mode 2 reports both the caller-visible access time and a cycle with the
payload write-back drained inside the timed region. Mode 5 reports one
access-time column; its serial hierarchy is the comparison for callers with
one request at a time, while the batched rows require independent concurrent
requests. Worker counts may be capped by the host's available physical cores
and the number of payload chunks. Every mode exits 1 if a timed read misses
its key; returned values are not compared.

### `cpu_tree_eviction_comparator_benchmark`

```text
cpu_tree_eviction_comparator_benchmark [--capacity N] [--value-bytes V[,V...]]
    [--key-bytes K] [--passes P] [--seed S] [--verify-passes Q]
    [--fold F] [--stash-registers A]
    [--arm read_path|read_path_transposed|enigmap|all]
```

Times one isolated eviction pass on one core: the plan plus the payload
movement on one working set of `64 A` stash lanes and the path's 64 lanes, by
16 metadata and V payload byte lines. The geometry is the default rule's for
`--capacity` (`TreeGeometry::ForCapacity`), or an explicit `--fold` /
`--stash-registers` within the library's limits; a two-register path is
refused. Arms: `read_path` is the library's planner (`PlanReadPath`) and its
per-line routing; `read_path_transposed` adds the transposition between the
stored bucket layout and byte lines, as one engine access pays it; `enigmap`
is EnigMap's oblivious Path ORAM eviction (`EvictPath`, three oblivious sorts
of whole entries) on the same entries, built only into
`cpu_tree_eviction_comparator_benchmark_enigmap` when CMake is given
`-DMICRORAM_ENIGMAP_DIR` pointing at the checkout from
[fetch_enigmap.sh](../baselines/fetch_enigmap.sh). The first
`--verify-passes` passes (default 1000) of every arm are checked against
`ReferenceReadPathEvict`: slot for slot for the read-path arms, and for
`enigmap` by validity (every entry once and intact, each path entry eligible
for its bucket) with the same found, leftover-count and overflow results.
Input generation is not timed. One JSON line per (arm, V). `--key-bytes` is
a label echoed as `key_bytes` in each line; no arm reads it. The EnigMap
target also needs the Boost headers (`libboost-dev` on Debian and Ubuntu),
because EnigMap's sources include `boost/stacktrace.hpp`. The paper's rounds
(three, with the arm order rotated) are `analysis/paper_micro.py eviction`
([Paper micro-benchmarks](#paper-micro-benchmarks)).

### `cpu_tree_bucket_shape_benchmark`

```text
cpu_tree_bucket_shape_benchmark [options] row [row ...]
    e.g. cpu_tree_bucket_shape_benchmark --ops 20000000 lam=18,fold=3,logn=20
```

Runs the stash simulator (`cpu_tree_stash_sim.hpp`: the engine's eviction
plan over metadata, a binary tree of four-slot buckets, the path in one or two
registers, `A` stash registers, an unbounded stash) on rows of leaf bits,
fold and entries (`a=` sets the stash registers, default the rule's for the
fold). It pools independent seeds, fits the tail of each access's leftover
count over its deep end, and reports the stash lanes needed at `--target`
(default 96) bits with jackknife errors across seeds. Seeds are hashed before
use (`--seed-mix`, the default), which is what makes them independent;
`--no-seed-mix` hands the simulator the raw seeds, whose streams are shifted
copies of one stream, and such a run of more than one seed prints no error
bar and no verdict. Flags include `--ops`, `--seeds`,
`--workload uniform|roundrobin|hotset|misses|churn`, and `--save` / `--merge`
for runs split across processes. A row holds at most 2^31 entries
(`logn=31`), because the simulator's block ids are 32-bit signed integers.
[analysis/run_stash_tail_long.py](../../analysis/run_stash_tail_long.py)
`init OUT --binary B --rows F` runs a JSON row set `F` as one resumable
process per seed (a row may fix its own `seeds` and `seed_base`;
[analysis/stash_rows/paper.json](../../analysis/stash_rows/paper.json) holds
the paper's rows),
[analysis/stash_requirement.py](../../analysis/stash_requirement.py) turns its
export into the requirement `k*`, and
[analysis/plot_stash_tail.py](../../analysis/plot_stash_tail.py) draws the
paper's stash-tail figure from the same export.

The simulator is held to the engine slot for slot and stash lane for stash
lane by
[cpu_tree_read_path_oram_test.cpp](../../tests/oram/cpu_tree_read_path_oram_test.cpp).
Passing that comparison or extrapolating a measured stash tail does not
establish a lifetime overflow bound. Use the exact geometry, load and stash
width when interpreting either measurement; the "Stash size" section of the
[tree design](../../src/oram/tree/DESIGN.md) states the limits.

## Host characterization

- `cpu_cache_latency_benchmark [--cpu N] [--max-mib M] [--per-octave K]
  [--ms T] [--seed S] [--stride B] [--watch-mib W [--watch-s S] [--watch-out
  FILE]]` measures load-to-use latency against working set (4 KiB upward, a
  random 64-byte line cycle, one pinned core) in a few seconds. It reports
  the L1, L2, L3 and DRAM latencies and the usable cache: the working set
  before latency first exceeds a quarter of DRAM's. Use it to check a boot's
  effective L3. `--stride 4096` separates TLB reach from cache size;
  `--watch-mib` monitors one working set over time for cache interference.
- `cpu_host_topology_probe [--tests c2c,core,llc,region,freq] ...`
  infers where a VM's vCPUs and memory sit on a multi-die host: core-to-core
  latency between every pair of physical cores, per-core DRAM latency, L3
  share, latency per guest-physical GiB (`region`, needs root) and effective
  clock (the default set); `llcpar` adds the L3 a set of cores gets
  together. It prints tables and one `PROBE_SUMMARY` JSON line; the source's
  header lists every option.
- `cpu_mem_bandwidth_benchmark --sweep 1,2,4,8` measures streaming-read
  bandwidth at several thread counts; `--compete N --seconds S` runs N
  streaming threads beside another process, so the bandwidth the competitor
  loses is what that process used. `--first-core` pins the threads.

## Paper micro-benchmarks

[analysis/paper_micro.py](../../analysis/paper_micro.py) runs the drivers
above with the flags the paper's micro-benchmark numbers used and reduces
their rows to those numbers. Run it from the repository root after a native
build in `build/` (`--build` selects another). Each subcommand writes the
drivers' raw output, `commands.log` and `summary.json` to `--out DIR`, and
prints each reproduced number beside the paper's value. The log names
binaries by base name and SHA-256 and records no host name. `--dry-run`
prints the commands, and `--summarize-only` reduces an existing DIR again.
The script uses only the Python standard library.

| Subcommand | Driver runs | Reduced to (field) |
|---|---|---|
| `table-rebuild` | `cpu_byteslice_table_rebuild_benchmark --mode init --reps 5` at 2^10..2^MAX entries and one `--mode chain` run at 2^(MAX+2); `h2o2ram_routing_bench --threads 1 --bucket-slots 64` and `128` at the same sizes; K4, V8 and V64, one CPU (`--max-log2`, default 24) | H2O2RAM's 64-slot `median_ms` over ours: the init rows without duplicates, the chain's `cascade` rows (not `top`) with duplicates; range over the sizes and the 2^20 times |
| `routing-locality` | `cpu_byteslice_stash_rebuild_benchmark --network flat,cache_oblivious --key-bytes 4 --value-bytes 8 --live-entries 1048576 --instances 8 --cpus LIST --reps 50 --seed 741`, run twice | `route_ratio_median` of the `instances_ratio` row; the lower of the two runs |
| `vp2intersect-merge` | in a native build and a `-DCPU_BYTESLICE_ORAM_ENABLE_VP2INTERSECT=OFF` build (`--native-build`, `--fallback-build`): `cpu_byteslice_level_arena_benchmark --capacity n --key 4 --value 8 --branching 8 --owners 0 --write-only --settle n --accesses 2n --stage-times --fit-rows --reps 3` at n = 2,048, 32,768 and 1,048,576, and `cpu_byteslice_dedup_kernel_benchmark 2000000 1 half_unique` | fallback over native median merge time (the FIT_ROW `level` rows' `job_nanos` summed per repetition, compare_share.py's `merge_ms`); `--with-share` adds the counted build and the comparisons' share |
| `tables-per-lookup` | arena benchmark at 2^27 (`--capacity`), K4/V8, B = 8, `--settle N --accesses N --fit-rows --reps 1 --read-only --probe-counts`: one request at a time with `--rebuild-threads 14`, and batches of 64 (`--batch 64 --lanes 8 --participants 8 --parallel`) with 7 | FIT_ROW `run` `lookup_mains_mean` (main hash tables per lookup) |
| `write-throughput` | arena benchmark at 2^27, K4/V8, B = 8, `--settle N --accesses N --fit-rows --reps 1 --rebuild-threads 14 --write-only --merge-rows --probe-counts` | FIT_ROW `run` `completed_records_per_s`; `--scalar-rate` adds its ratio to a measured single-request rate |
| `eviction` | `cpu_tree_eviction_comparator_benchmark_enigmap --capacity 2097152 --key-bytes 4 --fold 4 --stash-registers 3 --passes 20000 --verify-passes 1000 --value-bytes 8,...,4096 --arm A`; three rounds, the arms rotated so each runs once first, second and third | median `ns_per_pass` over the rounds at 1 KiB: `read_path_transposed` (ours) and `enigmap` |
| `memory-latency` | `cpu_host_topology_probe --tests region --region-gib G --region-lines-per-page 8 --region-core C` (faults guest memory in; `--touch-gib`), then `--tests core` | `PROBE_SUMMARY` `core_dram_ns_median` |
| `l3-check` | `cpu_cache_latency_benchmark --cpu C --max-mib 64` on one core of each L3 domain (`--rounds`, `--interval`); `--llcpar` adds `cpu_host_topology_probe --tests llcpar` on each domain's cores | WHOLE, exit 0, when every curve reads at most 16.0 ns at 16.0 MiB, 23.5 ns at 22.6 MiB and 25.5 ns at 26.9 MiB (and llcpar at most 17.5 ns at 32 MiB together); otherwise CAPPED, exit 1. The defaults are the limits for Oracle's Zen 5 SEV-SNP VM; `--limits` sets others |

CPU placement follows the measured runs. Core 0 and its SMT sibling are left
to the system. The script picks one CPU per remaining physical core from
sysfs `thread_siblings_list`, which gives the same cores whether siblings are
numbered k and k+N (CPUs 1..15 on a 32-vCPU C4 VM) or adjacently (CPUs 2, 4,
..., 30 on a 16-OCPU Oracle E6 VM). Single-core runs use the first of these
CPUs. The routing run uses the first eight. A one-request-at-a-time arena run
puts the caller on the first and 14 rebuild threads on the next 14. A batch
row puts its eight threads on the last eight of the first 15 CPUs and seven
rebuild threads on the seven before them; on the Oracle VM those are the two
CCDs. `l3-check` uses the second physical core of each L3 domain (CPUs 2 and
18 on the Oracle VM). `python3 analysis/paper_micro.py cpus` prints the
choices for the host, and every list has an override flag.

## Instrumented variants

| Target | Source and macro | Adds |
|---|---|---|
| `cpu_byteslice_level_arena_benchmark_throttled` | arena benchmark, `MICRORAM_BYTESLICE_LEVEL_ARENA_PAUSE` | `--rebuild-slowdown K` |
| `cpu_byteslice_level_arena_benchmark_compare_counted` | arena benchmark, `MICRORAM_BYTESLICE_COMPARE_COUNT` | a `COMPARE_COUNT` line: the window's merge comparisons by kind |
| `cpu_tree_oram_benchmark_phase_timed` | tree benchmark, `MICRORAM_TREE_PHASE_TIMER` | position-map and tree phase ns per read (mode 0) |
| `cpu_tree_eviction_comparator_benchmark_enigmap` | eviction comparator, `MICRORAM_ENIGMAP_ARM` | the `enigmap` arm |
| `cpu_byteslice_occupancy_observer` | its own source, `MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER` | secret-dependent occupancy (diagnostic) |

`--rebuild-slowdown K` (real >= 1): after every owner group poll the owner
spins `(K-1)` times the time since its previous poll (parked time excluded),
so each owner runs at 1/K speed. It throttles owner threads only; use helpers
0 and lanes 1. The control arm is inline or K = 1 in the same binary. A
slowdown factor is not a measured rate: measure the rebuild records/s at each
K independently with the closed-loop `--write-only` run of the same binary and
configuration (no `--rate`). The unthrottled binary rejects the flag.

The compare-counted build's timings carry the counters' cost; take merge
times from the plain build and price the counted comparisons with
`cpu_byteslice_dedup_kernel_benchmark`. The phase-timed tree build reads the
clock three times per access.

## Support headers

- `cpu_byteslice_benchmark_support.hpp`: timing (`Measure`), SplitMix64, and
  the generated-record iterator that feeds direct initialization.
- `cpu_byteslice_benchmark_topology.hpp`: Linux CPU-topology discovery and
  near/far placement validation.
- `cpu_byteslice_routing_comparator.hpp`: the unfused traversals of the
  fusion ablation.
- `cpu_byteslice_slot512_kernel.hpp`: the benchmark-only 512-slot
  merge-split.
- `cpu_bucket_table.hpp`: the conventional bucket table of the table-rebuild
  comparators.
- `cpu_tree_stash_sim.hpp`, `cpu_tree_stash_row.hpp`: the tree stash
  simulator and its row specification.
