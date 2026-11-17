# Local worker, raw replay, and recovery

The one-trial worker runs the phased C++ trial runner. The real worker
resolves a scheme once, dispatches to the concrete map once, then uses the same
prepared workload adapter for incremental, synchronous, tree (both position-map
modes), and auto. The portable fake worker uses that runner and adapter without
importing the ORAM ISA requirements.

Campaign `run` and `resume` launch native, `tdx` and `snp` campaigns and
`--synthetic` rehearsals. A native run needs `execution.runtime = native` with
`require_protected = false` and a host that shows no TEE; a `tdx` or `snp` run
needs a guest whose kernel shows that TEE and this boot's attestation capture
([protected runs](#protected-runs-in-a-confidential-vm-tdx-snp)). Every run
needs a host that exposes the campaign's cores and cache domains and every ISA
extension the frozen worker was compiled with, and memory headroom per attempt;
each attempt's `resolved.json` is then checked against `resolution.json`
([native runs](#native-runs-and-the-local-rehearsal)). `reduce` lists every
publication blocker per repetition; harness overhead is not one (below).

## Build and correctness checks

```bash
cmake -S analysis -B /tmp/oram-bench-portable -DCMAKE_BUILD_TYPE=Release
cmake --build /tmp/oram-bench-portable -j2
ctest --test-dir /tmp/oram-bench-portable --output-on-failure

cmake -S . -B build
cmake --build build --target cpu_oram_benchmark cpu_byteslice_trial_adapter_test cpu_byteslice_trial_adapter_test_checked \
  cpu_byteslice_open_loop_adapter_test cpu_byteslice_open_loop_adapter_test_checked -j2
ctest --test-dir build -R '^cpu_byteslice_(trial|open_loop)_adapter_test(_checked)?$' --output-on-failure
```

Portable tests cover exact timing boundaries with a delayed fake backend/clock,
partial timeout batches, bounded reject-newest overload, deadline crossings,
preparation crossing a deadline, request-cap versus horizon exhaustion, result
validation, raw replay, malformed/corrupt/truncated chunks, bounded writer loss,
writer failure, and actual SIGKILL recovery. Real-map correctness tests use a
synthetic clock, repeated keys, mixed reads/updates, and 4/8, 8/48, 16/16, and
32/1024 record shapes. The open-loop adapter test runs every engine,
scalar and timeout-batched, on the steady clock at 2 kops/s and requires every
offered request admitted and completed. They do not measure target performance.

## One-trial interface

```bash
/tmp/oram-bench-portable/oram_bench_fake_worker --help
build/benchmarks/cpu_oram_benchmark --scheme tree --cores 4 --capacity 256 \
  --key-bytes 32 --value-bytes 1024 --resolve-only 1

# Synthetic local fixture, with a new output directory:
/tmp/oram-bench-portable/oram_bench_fake_worker --scheme fake \
  --output /tmp/oram-fake-trial --capacity 128 --key-bytes 4 --value-bytes 8 \
  --api batch --batch-size 16 --arrival fixed --rate 10000 \
  --batch-timeout-ns 100000 --measurement-ns 10000000
```

Both executables accept two synthetic backends. `--scheme fake` is the
correctness fake: it stores every value (`live x value_bytes`) behind a hash
index. `--scheme noop` stores nothing: a read, or a batch write's old
value, is generated at the version the worker's oracle expects, so
verification succeeds by construction and the caller does exactly the work it
does for a real map. It measures caller-side overhead (generation,
verification, checksum, trial loop, logging) and runs at any capacity; its own
cost is an O(1) key decode and one value generation per returned value, plus a
scan of the current batch's earlier writes. Neither accepts placement or
overrides. `resolve --synthetic --synthetic-backend noop` rehearses a campaign
on it; the rehearsal's dataset-size guard applies only to the fake.

Options are strict named pairs. Duplicate/unknown fields fail. Real overrides
use the live namespaces, for example `--override.incremental.owner_threads 0`,
`--override.incremental.half_fanout_prefix false`, or
`--override.tree.position_map.mode hierarchical_synchronous`. Explicit zero
and false remain explicit. `--cores` includes one reserved harness/writer core;
this is a budget, not evidence of actual placement. `resolved.json` is a
versioned **worker observation**, not an exact-plan import/export format.
`invocation.json` preserves the CLI arguments;
the binary hash binds the defaults in a campaign attempt.

The worker fills supported hierarchy maps directly and fills tree maps through
insertion. Warmup and the optional count-limited settle both leave background
maintenance running, so measurement never starts from a drained pipeline; the
final drain after measurement is the trial's only drain.
`--settle-requests N` is the row's `timing.settle_requests` from the plan. A
campaign normally settles every row by the same count; with
`timing.settle_per_entry_ppm` the planner raises each row's count to
`ceil(capacity * ppm / 10^6)` when that is larger (the paper presets use
10^6 with a 2^21 floor, so every row of a capacity sweep settles at least
max(N, 2^21) requests) and writes it into that row's spec, so the worker sees
one plain count. The planner's access-horizon check uses the row's count. An
offered-load row issues its settle at its own offered rate, so a large settle
at a low rate takes long; it falls under `setup_allowance_ns`, not the
measurement window. Every phase advances the public workload request
ID, so update versions never restart midway
through a trial. The library access budget includes online fill and all issued
phases. Repetitions and retries construct fresh processes/maps with planned
seeds; interrupted ORAM state is never resumed.

Every returned hit is compared across the **entire value**. Mixed workloads
use an exact 8-byte version per live key, separate from the bounded request and
record buffers; read-only workloads need no version table. This oracle is
explicitly included in `adapter_bytes` and reported as `version_table_bytes`.
It is not a constant-space verifier.

`--verification full|off` (hashed as `instrumentation.verification`, default
`full`) switches the oracle. `off` allocates no version table,
compares no returned value (read or old), and skips the final sweep and its
drain; the planner refuses it in a campaign with a smoke stage. It keeps the
hit/miss (`found`) checks and the checksum over returned read values. Update
values need no table: their version is `request_id+1`. An `off` trial writes
`"verification":"off","correctness_verified":false` to `worker.json`; its
manifest carries `verification: off` and is complete without a correctness
claim, and summaries, `repetitions.csv` and plot labels mark it `unverified`.

Writes update existing keys only. A batch write's `found` is whether the
key was present before it ran, and its `value_out` receives the value before
the write, on every engine (hierarchy incremental and synchronous, tree in both
position-map modes; the fake matches). The worker requires `found` for every
batch write in either mode, and under `full` compares the old value with the
oracle's version before the write (`verified_old_values`). A scalar write is
`exchange(key, value, old, true)`: one ORAM access that also copies the
previous value, like a batch `kReadThenWrite`. The worker checks neither that
old value nor whether the key was present. A scalar write therefore inserts a
record the map has lost, with the new value, and later reads and the final
sweep do not see that loss; they check only what scalar writes stored.
Values are generated and compared one 8-byte word at a time, and the rolling
checksum folds four independent word lanes, so caller-side work per byte is
small. No correctness claim relies solely on that checksum. A final,
outside-timing verification reads every live key for small fixtures, or 64
deterministic sample keys for larger ones, plus the final written key. Its calls
are reserved in the library access budget and its maintenance is completed
separately. This also gives write-only workloads a non-vacuous value check; large
trials do not claim exhaustive verification of every final map entry.

## Timing and queue contract

- Preparation, output verification, checksums, counters, histogram updates,
  and event-buffer copies all contribute to wall throughput.
- Offered-load trials read the clock once per served call: the read that
  completes a call is also the next call's dispatch time while requests are
  waiting (idle, the read after the wait). The service bracket therefore runs
  from the previous completion read, so it also holds the harness's work
  between calls: the previous call's result processing (hit checks, the
  checksum over every returned value, value verification under `full`), the
  statistics update and this call's preparation. For a 64-request batch this
  is on the order of a microsecond or more per call. A call dispatched after
  an idle wait carries only its own preparation, so the share of calls that
  carry the rest, and with it the service time, rises with the offered load.
  Response is the completion read less the
  computed arrival, and is exact. The dispatch time passed the deadline check,
  so live runs and replay apply the same `dispatch < deadline` rule. Response
  and queue preserve intended arrivals. Campaign service is **batch-call weighted**;
  response/queue are request weighted.
- Saturation uses coarse count windows (`--window-requests`, default 1,024
  requests, hashed as `instrumentation.window_requests`), caller end, and
  maintenance end. The clock is read at each window boundary, and on every
  call once the batch has at least 16 requests, so the loop overshoots the
  horizon by at most one window (scalar) or one call (batch >= 16). It has no
  per-call service timestamps unless `--service-timing 1`. The final window
  closes at the first read past the horizon; actual boundaries are retained.
  A count-only settle ignores the horizon, and the worker fails if a settle
  issues fewer requests than requested. Saturated response/queue are empty, and a precise completion
  count at the nominal time horizon is unavailable rather than fabricated.
- Offered-load trials offer every arrival in `[0,T)`, computed from the request
  index; the waiting requests are the id range from the next one to serve to
  the last that has arrived, so nothing is queued, copied or rejected and
  `admitted = offered`. Load above capacity therefore builds an unbounded
  backlog, which the drain deadline censors as outstanding. `--queue-limit` is
  only the bound a raw-event log declares for its replay (waiting plus one
  batch, at most 2^24 requests; the worker and schema reject larger values; the schema default is 2^23),
  and a logging trial that exceeds it fails. Fixed-count batches flush the final partial batch
  at the horizon; timeout batches can flush earlier, measured from the oldest
  waiting arrival.
- At `T + drain_ns`, queued/uninvoked requests become outstanding. A synchronous
  call or maintenance barrier already in progress cannot be canceled safely;
  its actual completion is retained and the deadline flag is set. On an
  offered-load row that is overload, not a failure: the worker
  exits 0, the unserved requests are censored and `reduce` labels the row
  `overloaded`. A saturated row whose drain overruns the deadline still
  invalidates the attempt (exit 3), since it has no complete drained window.
  A caller rate and a rate including final maintenance are both kept.
  Reaching the offered safety cap before the horizon is also explicit invalidity.
- Batch size/count pairs are retained in `worker.json`. Rejected/outstanding
  requests receive no made-up latency. The worker does not classify queue
  stability; `reduce` labels each offered-load repetition `stable`,
  `overloaded` or `backlog_growth` (below), since absence of censoring alone is
  not a stable-tail claim. Minimum tail-count sufficiency is
  configurable and shared with the reducer.

Process memory observations are taken before backend construction, after
construction/fill/warmup/settle,
before measurement, periodically on the worker's telemetry thread (100 ms by
default), and after drain. Linux fields include RSS, PSS, whole-process high
water, swap, page faults, and cgroup-v2 current/peak/ancestor limits. PSS comes
from `/proc/self/smaps_rollup`, which walks the page tables (tens to hundreds of
milliseconds at many GiB on 4 KiB pages), so only phase-boundary samples read
it; periodic samples leave PSS blank and read `/proc/self/status`. Missing
fields are blank, not zero. `cgroup_limit_bytes` is the tightest `memory.max`
up to the hierarchy root, `unlimited` when no level sets one, and blank when
unknown. `cgroup_peak_bytes` is the cgroup's lifetime `memory.peak`: workers
share the coordinator's cgroup, so it includes earlier trials. Timestamps use
the OS monotonic epoch and are separate from measurement-relative timestamps. Memory is not added to the
library bill. The output directory, resolved inputs and flushed baseline exist
before backend construction, so constructor failures retain that evidence.
Resolve-only commands still create no artifacts.

Periodic CSV labels distinguish `measure` (including offered-cohort draining),
`final_drain` (the all-maintenance barrier), and `log_flush` (after the timed
interval). Notifications perform only an atomic label store on the caller;
sampling and I/O remain on the telemetry thread. A read spanning a phase
transition is labeled `phase_transition`, because the OS fields are not an
atomic snapshot. Short phases may have no periodic sample; the after-drain
boundary sample remains mandatory. Whole-process high-water values do not
identify which phase established the peak. The worker does not plan a
complete allocation/initialization peak, and sampling/logging overhead is
validated per target with harness validation records (below).

Offline `memory-summary` reads retained CSV without sampling the analysis host:

```bash
python -m analysis.oram_bench memory-summary --input path/to/worker/memory.csv --interval-ns 100000000
```

The exact CSV header identifies memory CSV v1; new workers also persist its
version and sampling interval in `worker.json`. The streaming reducer rejects
unknown columns/phases, invalid integers, decreasing timestamps/cumulative fault
counters and reversed lifecycle boundaries. Missing fields remain null and
interrupted files have explicitly incomplete coverage. Phase summaries contain
observed maxima and known-field counts; whole-process/cgroup high-water counters
are cumulative, not peaks attributable exclusively to the named phase. The
summary (v2) reports the per-trial peak as `trial_peak_rss_bytes` (the worker's
`VmHWM`), renames the cgroup peak `cgroup_lifetime_peak_bytes`, and gives
`cgroup_limit_status` (`limited`, `unlimited` or `unknown`) beside
`minimum_observed_cgroup_limit_bytes`. There is no per-trial cgroup peak,
since workers share the coordinator's cgroup.

Paging classification uses the conservative envelope from `before_measure`
through `after_drain`, including logger setup and flushing. Nonzero observed
process swap or increasing major faults yields `paging_observed` and
`in_ram_valid=false`. Major faults can include file-backed I/O, so this is a
conservative exclusion with an explicit reason, not proof of swap traffic.
Minor-fault deltas are diagnostic. Missing boundaries or swap/major-fault fields
yield `unknown` unless positive paging evidence is present. Otherwise the label
is `no_paging_observed`: sparse samples do not prove continuous residency, and
`in_ram_valid` remains null pending the other publication gates. Initialization
and final verification faults are kept separate from this envelope.

Campaign reduction includes only memory files covered by the verified raw
manifest. The derived campaign summary (v6) carries per-repetition memory evidence,
CSV memory/paging columns, `queue_stability` and `publication_blockers`;
`publication_validated` is true exactly when no blocker applies. The blockers
are `cycle_coverage_insufficient` or `_unknown`, `paging_observed` or
`paging_unknown`, `queue_overloaded` (rejected, timed-out or outstanding
requests) or `queue_backlog_growth` (fewer than 99% of the horizon's arrivals
completed inside it, which a stable load always meets and a load above
capacity cannot), and, for offered-load rows, `p99_insufficient_samples`.
Plots draw blocked repetitions hollow. Reduction preserves observations and does not
rewrite historical attempt outcomes. Raw manifests and timing summaries retain
their versions. The C++ reducer still supplies all latency/throughput statistics.

### Harness validation records

A record (`validation.py`) binds one worker hash, environment class, key and
value width, core count and placement, API mode, caller batch size and batch
policy, arrival process, offered-rate range (none for saturated rows) and
logging/verification mode to the target's measured evidence: the response
p50/p99/p99.9/maximum and mean service of the bound arm against a control
(a lighter logging mode, or an identical-arms null run), the closed-loop no-op
harness ns/request, and event counts. A record passes only if its evidence
does: p50, p99 and p99.9 each at most 5% slower than the control (`gate_ppm`
50,000, which a record may tighten but not loosen; a published mode that is
faster than its control passes), the maximum present (reported, not gated: one
sample cannot resolve 5%) and no lost events; the verdict is re-derived from
the evidence, never taken from the record's `status`.

Records are reported evidence and block no row: harness overhead is unstable
and unavoidable, and charging it as a blocker would only favor the prior
schemes, which are slower. The worker's `publication_validated:false` field in
`worker.json` is ignored by `reduce` (it is kept so the worker binary, and with
it the environment class, does not change).

`validation-record --control C/summary.json --instrumented I/summary.json
--output DIR (--noop N/summary.json | --harness-ns NS) [--comparison
logging_mode|identical_arms]` writes one record per instrumented group that has
a control group with the same environment class and spec (the logging mode
aside for `logging_mode`), one repetition each; the no-op summary supplies
ns/request by API mode and batch size.

## Raw format and replay

Full-event mode (the diagnostic mode) keeps every event in one
in-memory buffer sized for the whole trial by the coordinator (192 B per scalar
request, 128 + 64/b per fixed-count batched request, from the row's rate and
horizon) and allocated and pre-faulted before fill and warmup. The request
thread only appends; nothing is encoded, checksummed or written while requests
are served. After the final drain the worker encodes bounded little-endian
chunks with a table-driven CRC and publishes them, recording
`post_trial_write_ns`. A full buffer invalidates the attempt (exit 3) with its
loss count. Memory telemetry runs on its own thread, bound to the harness slot.
`clock_origin_steady_ns` in `worker.json` is the trial clock's zero as absolute
`steady_clock` time, which places `memory.csv` samples on the event time axis.

`maintenance_coverage` in `worker.json` counts the rebuilds reaching each
level during the measured phase: the counter it read (`counter`), its value
before and after, the plan's `carry_period_accesses` (lowest level first;
`resolved.json` records them too) and `carries_by_level`, each the number of
period boundaries the counter crossed. A hierarchy of either scheme counts
carries into levels 1..L; a tree counts its position map's carries in
position-map accesses (`position_map_accesses`, one per tree access or batch
member). Every counter advances once per completed request, which the
real-engine open-loop test checks. It is `null` for the synthetic backends. `reduce` labels each repetition
`cycle_coverage`: `sufficient` when the top level took at least
`timing.minimum_top_level_carries` carries (default 2, which puts one whole top
rebuild period in the window), `insufficient_cycle_coverage` below it, and
`unknown` without a counter; `repetitions.csv` carries the label and the top
level's count.

The file header is the eight bytes `ORBEV01\n`, followed by four little-endian
uint64 values: payload bytes, CRC-32/ISO-HDLC, first record sequence, and record
count. Payload is `count * 64` bytes, capped at 64 MiB per chunk. Every record
is eight uint64 words: kind followed by these fields; unused words must be zero.

| Kind | Fields after kind |
|---|---|
| 1 begin | saturated, horizon, deadline, offered cap, queue limit, batch maximum, window requests |
| 2 arrival | request ID, intended arrival |
| 3 batch | batch ID, member count, dispatch, completion |
| 4 member | batch ID, request ID, intended arrival |
| 5 outcome | outcome (0 rejected, 1 timed-out, 2 outstanding), request ID, intended arrival |
| 6 saturation window | begin, end, completed requests |
| 7 optional saturation service | duration, member count |
| 8 end | caller end, maintenance end, offered, admitted, completed, flags, minimum tail count |

End flags are bit 0 offered-cap truncation and bit 1 deadline overrun. Arrival
IDs are contiguous; each has exactly one terminal outcome. Batch members remain
FIFO ordered. Replay keeps only the bounded pending cohort, validates all IDs,
serialized call order, chunk sequence and end totals, and uses the same C++
accumulator and JSON formatter as the live worker. CRC detects chunk corruption;
committed manifests additionally use SHA-256. Replay has a 16M pending-request
safety bound. No key, value, pointer, secret seed, or private ORAM state is logged.

Histogram-checkpoint mode (the publication mode) allocates no event buffer for
offered-load trials. It writes one delta checkpoint per block of
`--checkpoint-interval-ns` of completion time (`checkpoints/000000.bin`, ...;
blocks hold completions in (begin, end], the last ends at the drain end), plus
raw count/time boundaries in `worker.json`; the reducer merges them. At most
4096 blocks fit the horizon plus drain deadline (each is about 350 KB).
Saturation retains coarse windows in either logging mode. Diagnostic sampled
traces are not implemented; neither mode silently substitutes sampled tails.

```bash
/tmp/oram-bench-portable/oram_bench_aggregate --events /tmp/oram-fake-trial/events/*.bin
/tmp/oram-bench-portable/oram_bench_aggregate --events --format raw-csv /tmp/oram-fake-trial/events/*.bin
```

`raw-csv` exports the sequence and all eight words losslessly; the table above
names their fields. `--format csv` emits trial totals/rates. Plain checkpoint
inputs use the standalone reducer interface ([STATISTICS.md](STATISTICS.md)). `--repeat COMPLETED
CALLER_NS DRAINED_NS` (repeatable) computes median/range of per-repeat rates and
pooled rate as total operations/total time. Percentiles stay per repetition and
are never averaged. Range is descriptive, not a confidence interval.

## Time series

`timeseries` turns one committed full-event attempt into a figure-ready series;
saturated and histogram-checkpoint attempts have no per-request events and are
refused. It re-hashes the attempt, streams the per-request records from
`oram_bench_aggregate --events --format raw-csv` (run in `worker/events/` on
bare chunk names, so thousands of chunks fit in ARG_MAX; it validates each
record before printing it and the cohort's completeness at the end) and
writes the outputs below, publishing `requests.csv` only after the replay
passed. One pass; memory holds the series rows, one open interval's responses,
the plot points, the open batch and the requests that ended while a lower id
was still pending (none in the worker's FIFO log), never the whole cohort. It
relies on completions arriving in interval order (the worker's single caller
loop) and refuses a log that goes back into a closed interval:

```bash
python -m analysis.oram_bench timeseries --reducer build/analysis/oram_bench_aggregate \
  --campaign /data/campaign --trial-id TRIAL --output /tmp/series   # or --attempt DIR
```

- `requests.csv`: request id, status, arrival/dispatch/completion (ns, trial
  clock), response/queue/service (us), batch id; rejected, timed-out and
  outstanding requests keep their arrival and no made-up latency. Service is the
  batch call's, shared by its members.
- `series.csv`: 1 s intervals (`--interval-ns`) over the measurement window
  [0, horizon), binned by **completion time since the measurement start**;
  completions, throughput (req/s; the last interval keeps its own, shorter
  width), exact nearest-rank p50/p99/max response (us) and whether the interval
  has 100 samples. Completions after the horizon (drain) are in `requests.csv`
  only.
- `markers.csv` (`start_s,end_s,role,level`) holds maintenance spans read from
  the attempt's `worker/markers.csv` (`role,level,start_ns,end_ns`, trial
  clock; spans that end after the measurement start, so a start may be
  negative), which the worker writes after the trial and the commit hashes
  like any artifact. `worker.json` `maintenance_markers` names the
  source or why there is none:
  - ours: `top_merge_log`, the engine's top-merge log (the tree: its position
    map's), roles `top_prepare` (job bound to carry-dependent start;
    preparation may run ahead) and `top_merge` (to publication), level = the
    top. The log keeps the last 256 merges; a full log is labelled
    `top_merge_log_last_256_merges`. The worker drains the engine first.
  - H2O2RAM: `bracketed_buffer_full_access_includes_lookup`, role
    `h2o2ram_rebuild`. It has no rebuild events, so the worker times the
    access that starts with a full buffer (its `operator[]` rebuilds first);
    the span includes that access's lookup. Level = the table built,
    min(ctz(k), top) for the k-th rebuild.
  - SONIC: unavailable (its eviction runs inside each access, unpatched).

  Without markers `series.json` carries `markers_unavailable` (the worker's
  reason when it gave one); `maintenance_coverage` counts access-derived
  carries and proves no completed rebuild.
- `series.json`: the binning/quantile rules, window, counts, the clock origin,
  `max_stall` (request id, response us, arrival/completion s; the largest
  completed response over the whole attempt, lowest id on a tie).
- `series.png`/`series.pdf`: throughput per interval above a log-scale
  per-request response scatter on one time axis, maximum stall annotated,
  markers shaded in one color per role. The plot strides to at most 200,000 requests plus the maximum;
  the stride comes from `worker.json` `trial_boundaries` (completed), checked against the events.

## Terminal recovery rehearsal

Use a retained local filesystem with POSIX `flock`, hard links, atomic rename,
and file/directory fsync. There is no object-store backend or conditional remote
commit. Synthetic fixtures do not attest a protected environment or run the
planned ORAM candidates. Large synthetic datasets are refused.

```bash
python -m analysis.oram_bench doctor --execution fake \
  --worker /tmp/oram-bench-portable/oram_bench_fake_worker --output /tmp/oram-host.json
python -m analysis.oram_bench plan --config benchmarks/campaigns/c4-tdx-smoke.json \
  --output /tmp/oram-rehearsal
python -m analysis.oram_bench resolve --campaign /tmp/oram-rehearsal --synthetic \
  --worker /tmp/oram-bench-portable/oram_bench_fake_worker
python -m analysis.oram_bench run --campaign /tmp/oram-rehearsal --synthetic \
  --reducer /tmp/oram-bench-portable/oram_bench_aggregate
python -m analysis.oram_bench status --campaign /tmp/oram-rehearsal
python -m analysis.oram_bench resume --campaign /tmp/oram-rehearsal --synthetic \
  --reducer /tmp/oram-bench-portable/oram_bench_aggregate
python -m analysis.oram_bench reduce --campaign /tmp/oram-rehearsal \
  --reducer /tmp/oram-bench-portable/oram_bench_aggregate --output /tmp/oram-summary
python -m analysis.oram_bench plot --summary /tmp/oram-summary/summary.json --output /tmp/oram-plots
```

`resolve` freezes the worker into `campaign/build/worker` (with `build.json`:
worker and library-header hashes) and writes the immutable `resolution.json`;
see [the resolve step](#the-resolve-step). `run` and `resume` launch only that
frozen copy, so they take no `--worker`, and refuse a campaign without a
resolution.

Plotting is an optional offline matplotlib dependency. It exports PNG/PDF
per-repetition capacity, latency against offered input rate on a log x-axis,
and value-width observations,
keeps configurations/environments distinct, and displays failure/skip counts.
These initial plots are unvalidated. `memory.png`/`memory.pdf` show sampled
process RSS across capacities and value widths, including harness/logging
memory. Markers show censoring/paging and unknown paging evidence; missing RSS
is counted rather than drawn as zero. `plot` takes `--summary` once per
campaign and labels each series by campaign and build (see the
[tuning loop](README.md#tuning-after-a-code-change)); it reads only the current
summary version, so re-run `reduce` for an older one.

- **Amplification.** `memory.png`'s third panel plots bytes over the logical
  data, live × (key + value), against capacity: the library's reserved bytes
  from the resolution (hollow) and the trial's peak RSS (filled). At small N
  the RSS figure is dominated by the harness and runtime, not the library's
  buffers. Summary v6
  carries each repetition's `live_entries`, `logical_bytes`,
  `library_modeled_bytes` and `library_reserved_bytes`, and so does
  `repetitions.csv`.
- **Legends.** A series is colored by its family: candidate, API, security
  label and shape, plus campaign and runtime when the figure holds more than
  one. One legend of families sits outside the axes, and `series.csv` maps
  every series label to its family and color. Each repeat group is still
  drawn as its own series.
- **Targets side by side.** With more than one summary, `targets.png` puts
  one campaign per column (for example a TDX guest, its native control and an
  SEV-SNP guest), with
  saturated throughput against capacity and p99 against offered input rate
  on a log x-axis,
  shared axes, and each family one color in every column.

Uncertainty across time blocks: `oram_bench_aggregate --blocks`
reports each checkpoint block's statistics and their spread
([STATISTICS.md](STATISTICS.md)); `reduce` keeps them as `time_blocks` and
`plot` draws saturated-throughput min/max lines. Event-log trials have none.
Latency spread is retained but not plotted.

Each attempt gets a fresh directory. Raw artifacts are fsynced and SHA-256
hashed, then an immutable manifest and final `COMMITTED.json` are published;
new directory entries are fsynced too. `worker/summary.json` is derived and is
excluded from raw commits. Reduction regenerates it from committed raw files,
writing only under its own output directory, never inside a committed attempt.
The first valid successful attempt in the same environment class is selected.
Scheduling and `status` trust `COMMITTED.json`, the manifest hash and each
artifact's presence and size; `reduce` and `verify --campaign C --deep`
re-hash every raw byte (at a cloud block volume's sequential read rate, one
pass over hundreds of GiB takes most of an hour). `commit` hashes an attempt's artifacts once. The inherited
`flock` is the only ownership mechanism; `state.json` pids/boot IDs and
`coordinator_status.json` are diagnostic.

A child inherits the coordinator's lock descriptor. If the coordinator dies,
its active worker continues to hold ownership until it exits, preventing a
second runner from sharing the attempt. Once ownership is recovered, stale
uncommitted attempts are retained and retried from fresh initialization.
The coordinator checks `--min-free-bytes` before each launch (default 5 GiB)
and persists a disk-watermark stop reason. This is a launch guard, not a raw
volume estimate or an upload-backlog controller. The first `run` writes the
launch policy (`--retries`, `--preemption-retries`, `--min-free-bytes`) to
`launch_policy.json`; later runs and a boot service that passes none of them use
it, and a differing value needs `--update-launch-policy`. Publication campaigns
are sized for a 50 GiB data disk with `--min-free-bytes 5368709120` (5 GiB);
increase capacity only when retained publication output needs more room.
Full-event diagnostics need separate output sizing and do not determine the
publication disk size.

Before each launch, the coordinator checks the row's memory estimate from
`resolution.json` against fresh evidence. The result is kept only as the
attempt's `memory_preflight.json`; there is no separate
`preflights/` store. It reads
guest `MemTotal`/`MemAvailable` and resolves cgroup-v2 membership through
`/proc/self/mountinfo`, including relocated/escaped mounts and exposed ancestor
limits. Each finite ancestor budget subtracts that ancestor's own current usage,
including sibling processes. The configured headroom (20% by default) reserves
space against each total limit, not just the remaining free bytes. Guest
availability and a configured host cap further constrain the snapshot budget.
Hidden ancestors, unsupported cgroups and unreadable fields are explicit gaps.
The hierarchy root has no `memory.max` or `memory.current`; it is recorded as
unlimited (`hierarchy_root`) and bounded by guest `MemAvailable`. A
cgroup-namespace root is not the hierarchy root (it has `cgroup.type`), so its
hidden ancestors remain a gap.

The estimate is the resolver's modelled library bytes (requested bytes, not a
complete allocation model) plus the update-version oracle (none for read-only
rows or `verification = off`), event ring and writer chunk; for the fake
backend, its value storage (the no-op backend has none). It excludes unaudited
index/allocator/stack/runtime storage, so its complete peak remains null. A bound exceeding an exposed budget
stops launches with `reason=memory_headroom`; no attempt is created and no retry
is consumed. `resume` reads fresh evidence and can proceed when pressure clears.
Admitted attempts retain `memory_preflight.json` in their hashed raw commit.
These checks reject known infeasible synthetic launches; incomplete evidence is
still labeled `insufficient_evidence`, never proof that an ORAM fits RAM. The
shared pure assessor accepts future complete additional-peak estimates but
is the same for native and synthetic runs. Budget observations are snapshots,
not reservations; the headroom (20% by default) must absorb what the modelled
bytes miss until allocation coverage is complete.

Worker-side infrastructure failures (worker timeouts and signals) use the
retry budget (default one retry). Preemptions, meaning a coordinator-initiated
stop or an attempt orphaned by a dead coordinator, have their own generous
budget (default 20), so spot preemptions do not abandon a trial. A trial that
exhausts either budget shows as `abandoned` in `status`.
Correctness/stash/resource/logging failures are retained, not retried in search
of a lucky result. SIGTERM stops further launches and terminates the active
process group; a stop that arrives before the launch is rechecked with the
signals blocked, so it never starts a worker. The reducer runs in its own
session: a stop during post-trial replay commits the attempt as an interrupted
preemption, not as an invalid trial, and the replay timeout scales with the
trace size. SIGKILL recovery needs no notification. Relative rates are frozen
from verified source attempts in the matching environment class using exact
rational medians and integer floor, with source commit hashes preserved. The
frozen record is authoritative: if its sources no longer verify, dependent
trials are deferred as `rate_source_invalid` rather than refrozen.

`doctor` captures exposed CPU/cache/affinity topology, RAM/cgroup limits, boot and
host identity, source/worker hashes, and monotonic clock metadata. It uses the
same cgroup mount mapping and reports memory evidence gaps. Its unknown
facts are explicit. It also asks the worker for its compiled-in extensions
(`--compiled-isa`: `-march=native` bakes in the build host's) and records them
as `compiled_isa`, the host flags among them plus the invariant-TSC and
user-mode-wait flags as `cpu_flags`, and the kernel's `clock_source`. A
compiled extension the host does not expose (a guest may filter CPUID) is
`isa:not_exposed:<flag>` evidence: `doctor` exits 2 and a run refuses
the host. `clock:no_invariant_tsc` and `clock:clocksource_not_tsc` are
recorded, not enforced.

`doctor` also records what the guest kernel shows about a TEE (`tee`): the
`tdx_guest` CPU flag, `/dev/tdx_guest`, `/dev/sev-guest`, the boot log's
"Memory Encryption Features active" line (read with `dmesg`, then this boot's
journal) and whether configfs-tsm's report directory exists. TDX is shown by
the flag plus the device; SNP by `/dev/sev-guest`. A boot line that names a TEE
must name the same one, and an absent or unreadable line is recorded
(`tee:kernel_line_absent`, `tee:kernel_log_unreadable`) but does not decide.
The `sev*` CPU flags are recorded only, since a plain VM on SNP-capable
hardware can show them, and configfs-tsm's directory exists on plain VMs too.
`--execution` takes `native`, `tdx`, `snp` or `fake`, and the label is checked,
never trusted: `runtime:tdx_not_shown` (or `snp`) when the host does not show
that TEE, and `runtime:native_on_tee_host:<tee>` when a native label meets any
TEE signal. Either makes `doctor` exit 2 and `run` block, so the plain control
can never carry the TDX label or the reverse. Detection is evidence, not
attestation.

`doctor` also records each allowed CPU's NUMA node (from
`/sys/devices/system/node`). Neither placement policy considers memory
locality, so a mask that spans more than one node is refused
(`topology_contract:multiple_numa_nodes`: `doctor` exits 2 and `run` blocks).
That covers a sub-NUMA-clustered Xeon, a two-socket host and a Zen part in
NPS2/NPS4. Bind the whole run to one node instead, for example `numactl
--cpunodebind=0 --membind=0 python -m analysis.oram_bench run ...`, and run
`doctor` the same way. Where the kernel exposes no nodes the evidence is
unknown and nothing is refused.

`doctor` records guest runtime-private memory as `guest_memory`, apart from
process/library memory (memory.py, worker telemetry): `guest_ram_bytes`
(`MemTotal`), `unaccepted_bytes` (`/proc/meminfo` `Unaccepted:`),
`shared_bounce_bytes` (the swiotlb pool; `source` is `debugfs`
(`io_tlb_nslabs` x 2 KiB, root only), `dmesg` ("software IO TLB: mapped ...
(64MB)", unprivileged `dmesg` only) or `cmdline_request` (`swiotlb=`, a
request, not the pool)), reserved huge pages, and
`private_bytes_estimate` = RAM - shared - unaccepted, only when all three are
known and labelled an estimate (`MemTotal` may already exclude the pool).
THP modes and TEE flags stay in `thp_*` and `tee`. Every field the kernel did
not give is null and named in `unavailable` as `<field>:<reason>` (`permission`,
`missing`, `empty`, `not_in_log`, `no_meminfo_line`, `no_swiotlb_parameter`,
`not_reported`); absence is never read as zero or as protection. A host with no
TEE signal and a native label is `private_memory: not_applicable` with
`not_applicable` entries. The pure `assess_guest_memory` (guest_memory.py) takes
the raw texts, so fixtures cover TDX, SNP, native and denied reads; real
private-memory evidence still needs each guest. It is not in `missing_evidence`
and not in the class.

`doctor` records the kernel command line, the THP `enabled` and
`defrag` modes, the CPU's family, model number, stepping and microcode, and
steal ticks since boot. The environment class (`environment-class-v5`) includes
the command line (without `BOOT_IMAGE=`, `root=` and `initrd=`, which name the
boot disk, not behaviour), both THP modes and family/model/stepping: one cloud
machine type can run on more than one CPU generation (for example Granite
Rapids, model 0xAD, and Emerald Rapids, 0xCF), and a TD may not expose the
brand string's detail. Microcode and steal time are evidence only. Attempts
recorded under a different class version are never pooled with the current
one. `doctor` records two more things.

- **The dependency closure.** `ldd` on the worker names every shared object
  the loader resolves on this host, and each is hashed. The class's
  dependency identity is computed from those names and hashes, so a library
  update is a new environment. An object the loader cannot find
  is `dependency:not_found:<name>`; a host without `ldd` records
  `dependency_closure_unavailable` and falls back to identifying the
  dependencies by the libc version and machine alone.
- **The TSC cross-check.** `worker --clock-check` measures, inside the
  runtime:
  - the TSC's rate against `CLOCK_MONOTONIC_RAW` over five 200 ms windows;
  - `CLOCK_MONOTONIC`'s slew against the raw clock (NTP's correction);
  - the cost of one `steady_clock::now()`;
  - each allowed CPU's TSC offset from the first CPU's, bounded by causality
    over 256 ping-pongs between two pinned threads (no OS clock can measure
    this, because the vDSO computes the raw clock from the local TSC);
  - whether the TSC ever reads lower after a migration;
  - the kernel's NTP state.

  Each failure is named: `clock:tsc_rate_unstable` (a spread above 10 ppm),
  `clock:monotonic_slewed` (above 500 ppm), `clock:slow_clock_read` (above
  100 ns, a read that is not served by the vDSO), `clock:tsc_skew_across_cpus`
  (an offset interval that excludes zero), `clock:tsc_backwards_on_migration`
  and `clock:skew_unmeasured_on_some_cpus`. The environment's `clock` reads
  `tsc_validated` only when the clocksource is `tsc`, the invariant-TSC flags
  are present and no check failed, and `monotonic` otherwise. The measured
  values are evidence, not class inputs. The thresholds sit far above what a
  healthy host shows and far below what a TSC rescale or a clocksource switch
  produces (NTP's own slew is at most 500 ppm). Like the other
  `clock:` entries these do not refuse a run; they say how far the latencies
  can be trusted.

The target unit
[oram-bench-campaign.service.in](../../benchmarks/campaigns/oram-bench-campaign.service.in)
runs `resume` without `--synthetic` after its retained volume is mounted. It
runs as a fixed non-root user from an explicit working directory, with absolute
Python and reducer paths (the worker is the campaign's frozen copy), declares
`RequiresMountsFor=` for the campaign path, and sets `KillMode=control-group`
so a service stop also stops its worker. It runs `attest` as
`ExecStartPre=-+` (tdx and snp campaigns) and passes the free-space guard
(`--min-free-bytes`) on every resume. The provider-specific protected
launch/replacement service must wait for runtime and storage compatibility
verification; process recovery does not recreate an evicted instance. Preparing each target VM, its retained data volume
and the unit is described in the
[reproduction guide](../../benchmarks/campaigns/README.md#preparing-a-vm):
Google Cloud C4 with TDX and Oracle Cloud E6 with SEV-SNP, each with a
retained data volume beside its boot disk.

## Native runs and the local rehearsal

A native campaign declares `"execution": {"runtime": "native",
"require_protected": false}`. `run` then refuses nothing a synthetic run would
accept, and adds a runtime gate (the host must show no TEE, or the run blocks
with `reason=runtime`) and three more:

- before anything launches, the host's exposed physical cores, L3 domains and
  compiled ISA against the campaign's resources (a mismatch writes
  `coordinator_status.json` as `blocked` with `reason=topology` and launches
  nothing, so a boot service does not restart-loop);
- per attempt, the memory preflight above;
- after a worker exits cleanly, `attempt_check.json`: its configuration key
  against `resolution.json`, its placement policy against the campaign, and
  online-helper locality under `near_far`. A mismatch commits the attempt
  `invalid` with failure kind `configuration`, which is terminal.

[`local-native-rehearsal.json`](../../benchmarks/campaigns/local-native-rehearsal.json)
fits a small workstation (8 physical cores, one L3, 16 GiB): 27 rows, all
three schemes (`auto`, `hierarchical_incremental`, `tree`) and three shapes at
N = 2^16, scalar and batch-64 saturation,
plus two fixed-rate rows at 50% and 90% of a frozen saturation rate. It runs
in minutes and checks the path, not performance:

```bash
python -m analysis.oram_bench plan --config benchmarks/campaigns/local-native-rehearsal.json \
  --output /tmp/native-rehearsal
python -m analysis.oram_bench resolve --campaign /tmp/native-rehearsal --worker build/benchmarks/cpu_oram_benchmark
python -m analysis.oram_bench doctor --worker /tmp/native-rehearsal/build/worker --output /tmp/host.json \
  --require-physical-cores 8 --require-cache-domains 1
python -m analysis.oram_bench preflight --campaign /tmp/native-rehearsal --environment /tmp/host.json
python -m analysis.oram_bench run --campaign /tmp/native-rehearsal --reducer build/analysis/oram_bench_aggregate
python -m analysis.oram_bench reduce --campaign /tmp/native-rehearsal \
  --reducer build/analysis/oram_bench_aggregate --output /tmp/native-rehearsal.reduced
python -m analysis.oram_bench plot --summary /tmp/native-rehearsal.reduced/summary.json --output /tmp/native-plots
```

On the plain C4 control the same sequence runs with a `c4-native-*` preset
(`--require-physical-cores 16 --require-cache-domains 1`); in the TDX guest it
runs with a `c4-tdx-*` preset plus the attestation step below.

## Protected runs in a confidential VM (tdx, snp)

In a cloud confidential VM the harness runs inside the guest, so the runtime
adapter is detection and evidence, not a launcher. A `tdx` or `snp` campaign
(`"execution": {"runtime": "tdx", "require_protected": true}`) runs like a
native one, with one step added per boot, before `run`, as root:

```bash
python -m analysis.oram_bench doctor --execution tdx --worker campaign/build/worker --output host.json \
  --require-physical-cores 16 --require-cache-domains 1
sudo python -m analysis.oram_bench attest --campaign campaign     # once per boot, as root
python -m analysis.oram_bench run --campaign campaign --reducer build/analysis/oram_bench_aggregate
```

`attest` refuses unless the host shows the campaign's runtime and the boot log
names it (the root read, where the log is readable). It computes the
environment class exactly as `run` does and fetches one report through
configfs-tsm (Linux 6.7 or later), whose 64 bytes of report data are the
SHA-512 of the binding: runtime, host identity, boot identity and
environment class. The binding is used instead of the whole environment record
because the record also holds the calling process's cgroup memory and the
tooling's git state, which differ between the root capture and the service
user's run. The report, any auxiliary blob (SNP certificates) and a capture
record go under `campaign/attestations/`, named by the binding's hash, and are
handed to the campaign directory's owner. A second `attest` in the same boot
reuses the capture. The capture record keeps the configfs-tsm provider and
generation, the root-time detection, and facts read from the report locally:
whether it carries the bound report data, the debug bit (TD attribute DEBUG,
SNP policy DEBUG), and for SNP the raw `PLATFORM_INFO` word with its
Ciphertext Hiding bit (bit 4), the evidence of whether the SNP host hides
ciphertext from the hypervisor. To run `attest` under the boot
service, add it as `ExecStartPre=-+...`: `+` runs that one command with full
privileges while the service keeps its unprivileged user, and `-` keeps a
failed capture from failing the unit, so `run` blocks on the missing capture
instead of the service restart-looping.

`run` blocks (`coordinator_status.json` `blocked`, `reason=runtime`) unless the
label matches the live detection and this boot's capture for the class exists
(`attestation:no_capture_this_boot`); a debuggable guest cannot serve a
campaign with `require_protected` (`attestation:debug_guest`). The attempt's
environment record references the capture by path and hash. `preflight`
checks the saved doctor evidence's label and `runtime:` contract, but not the
capture, which is bound to the live boot.

Verification is offline, with the provider's tools: go-tdx-guest or Intel
Trust Authority for a TDX quote, virtee `snpguest` against AMD's VCEK for an
SNP report. Record the result per capture:

```bash
python -m analysis.oram_bench verdict --campaign campaign --capture attestations/<binding>.json \
  --verifier "snpguest 0.9 verify attestation" --result verified --reference <id> --verifier-output verify.log
```

`reduce` marks a row `protected_verified` only when its attempt's capture
still hashes as recorded and it has at least one `verified` verdict and no
`failed` one; `verification_reference` names the verdict. A row of a campaign
with `require_protected` that is not verified carries the
`protection_unverified` publication blocker. The report fetch itself can run
only in a guest; the tests drive it through a fake configfs entry with the
kernel's generation semantics.

## Fitting the rebuild cost model

The rebuild heuristic divides the levels among owner groups by a cost model
whose default coefficients are calibration constants fitted on one machine. `fit-rebuild` fits it to the machine it runs
on and writes the `rebuild_cost_*` override block a preset carries:

```bash
python -m analysis.oram_bench fit-rebuild --benchmark build/benchmarks/cpu_byteslice_level_arena_benchmark \
  --grid target --rows fit-rows.jsonl --output rebuild-fit.json
```

`--grid target` runs the level-arena benchmark with `--fit-rows` over B = 4 and
8, 1M-32M entries and 16 B and 48 B values with three owners, cache-resident
probe runs, and write-only runs with top helpers for the helper curve: 0, 1, 3
and 7, cut to the physical cores the requester and the three owners leave, plus
that widest count (12 on a 16-core target). The helper runs pin every thread to
a core of its own with the benchmark's `--cpus`, one CPU per exposed physical
core, instead of `--place`: a far domain of eight cores cannot hold the top's
helpers, and a single-domain host places nothing, so they would share SMT
siblings. They therefore need the host's physical-core identity, and the
command refuses to start without it. It runs for tens of minutes on a
16-core target. `--grid quick` is a short grid that checks a small machine
against the default coefficients.
Rows are appended, so a second run adds repetitions; without `--benchmark` the
command only fits the rows it is given. Each row carries the model's features
as the library counts them, so nothing in Python re-derives a geometry.

What it fits, and how:

- **The line and job terms:** relative least squares, over rows whose groups
  run on one thread each.
- **The slice line cost:** the fitted line times the default model's margin
  (its slice line cost over its line cost). It is raised to the worst line cost among rows the
  line term dominates, when that is higher.
- **The probe terms:** scaled down until the model's cost is at most every
  measured one. The slice rate must stay at or above what the requester
  reaches.
- **The helper speedup:** from the top level's phase wall time across helper
  counts.
- **The top-thread cap:** the largest measured thread count whose doubling
  still paid more than the gain floor. The cap is never extrapolated.
- **Not fitted:** the middle-level burst and the gain floor stay at the
  library's defaults.

`rebuild-fit.json` holds the block, the whole model and every row's
measured-to-modelled ratio.

A candidate that pins `owner_threads` must take the block without the cap and
floor, which only a budget uses. Validate a fit on held-out capacities before
adopting it.

## Native thread placement

The native one-trial worker accepts `--cpu-ids CPU,CPU,...`, with exactly
`--cores` distinct slots. Slots are assigned in the resolved plan's `threads`
order; the last slot is reserved for the event writer and periodic telemetry.
The list implies `--placement explicit`; the default without a list is
`--placement unplaced`. Placement is rejected for the synthetic backend.
Resolve-only mode validates selected slots against exposed topology and prints
them without constructing maps, pinning, or measuring.

`--placement near_far` selects slots automatically from the original allowed
mask. The deterministic, uncalibrated `near_far_v2` policy uses one allowed
logical CPU per exposed physical core (the lowest allowed SMT sibling). The
lowest-numbered physical core (usually CPU 0, which takes most interrupts) is
the reserved harness slot. The caller takes the highest remaining core of the
first L3, in order of each L3's lowest core, that can also hold every online
helper (nested position-map online helpers included) and every rebuild thread
the plan marks `near` (below an explicit `near_max_level`). Those local slots
are reserved first. The other roles (far and unmarked owners, top-group
helpers, nested helpers and tree payload helpers)
take the lowest remote CPUs in plan order, spilling to local CPUs if
necessary; the plan lists the top group's helpers right after its owner, so
they land together. Unused library slots follow; the last slot remains the
writer/telemetry CPU. A single L3 is supported as an all-local assignment;
this option does not assert a two-domain topology contract.
Explicit CPU lists remain available for alternative owner/payload placements.

Automatic selection cross-checks physical-core identities, sibling membership,
L3 membership and L3 sizes. Missing/inconsistent evidence, insufficient physical
cores, or insufficient caller-local slots cause rejection. CPUs outside the
allowed mask never become slots, even if sysfs sibling/cache lists include them.
`--cpu-ids` cannot be combined with `near_far` or `unplaced`.
The worker first resolves public thread roles, then resolves again with the
selected slots and checks that scheme/capacity/roles agree. This is not
exact-plan replay, and there are no tuning profiles.
`resolved.json` records the versioned placement policy and every `cpu_slots`
entry, including inactive library capacity and the harness reservation.

Before construction, the worker reuses exposed topology discovery under its
original allowed mask. Every slot must identify a different exposed physical
core, including the reserved harness slot. The caller and all library helpers
install and read back their own singleton masks. The telemetry
thread runs its startup hook (pinning it to the harness slot) before the
measured phase can begin. A helper may widen
its inherited caller mask to its original allowed slot; kernel/cgroup rejection
or readback disagreement fails explicitly.

`placement.json` schema 1 records each successful role's `inherited` and
`applied` masks, CPU and role index, plus the original allowed topology. Unknown die/NUMA
IDs stay null. Role numbers match `ThreadRole` in
`configuration.hpp`; `-1` denotes writer/periodic telemetry. Complete coverage
requires all planned library roles plus the writer. Construction/runtime
failures preserve partial evidence when available. `resolved.json` remains
planning evidence (`placement_verified=false`); actual verification is in the
sidecar. These masks describe exposed guest topology, not physical-host CCD
attestation. A native `run` checks the host's topology before launching and
every attempt's placement after it; the offline `preflight` below applies the
same checks to saved evidence. No target affinity or performance claims follow
from local injected-mask correctness tests.

`--cache-domains N` (default 1; `resolve` passes the campaign's
`required_cache_domains`) declares how many equal L3 domains split `--cores`.
It is a resolver input, not discovery, so a plan does not depend on the host
that resolves it. With an explicit `near_max_level` and a rebuild thread
budget, the resolver caps the near side at the caller's domain less the
harness, the caller and its batch helpers (6 of 8 on two 8-core domains) and
the far side at the other domains (8), recorded as the derived
`near_rebuild_threads_cap`/`far_rebuild_threads_cap` choices and kept out of
the configuration key like the budget itself. Under `near_far` placement the
worker refuses a host whose exposed L3 count differs from the declaration.

`--monitor-wait none|umwait|mwaitx` (from the campaign's
`resources.monitor_wait`) declares the idle-wait instruction the
target offers. The resolver refuses `tree.payload_monitor_wait` or an arena
`value_monitor_wait` without one and records the declared kind as a derived
choice; the worker refuses a declaration the CPU does not match, since the
pool would otherwise fall back to a futex park. `run` refuses a host whose
doctor flags lack `waitpkg` (umwait) or `monitorx` (mwaitx).

`--spin-before-park-ns N` (from the campaign's `resources.spin_before_park_ns`;
the paper presets in `benchmarks/campaigns/paper/` use 1 s, so no library thread parks between
requests; the older presets leave it unset) is the resolver budget's
one spin-before-park (`ResourceBudget::spin_before_park_ns`). Every spin the
overrides leave unset takes it, recorded as a derived choice: owners, top and
bottom helpers and the requester's own wait (`owner_spin_ns`), batch helpers
(`batch_spin_ns`), value workers (`value_spin_ns`), a tree position map's
spins, and the tree's payload workers (`payload_spin_us`, in microseconds, only
where there are payload workers). An explicit override wins. Unset, neither the
spec nor the argv names it, so earlier trial ids are unchanged.

`tree.payload_near` (placement only) marks the tree's payload workers
near, so `near_far` placement puts them on the caller's L3 instead of the
remote one first.

`worker.json` records `trial_cpu_ns` over the trial call (measurement and
drain): `process` (CLOCK_PROCESS_CPUTIME_ID), `caller_thread` (the request
thread, which busy-waits between arrivals), `telemetry_thread` and `wall`.
`reduce` derives `trial_cpu.library_cpu_seconds` (process less the two
harness threads) and `library_cores_busy`; at low offered rates that is the
library's idle CPU, the quantity a monitor-wait comparison reads.
`repetitions.csv` carries `library_cpu_seconds`, `process_cpu_seconds` and
`trial_wall_seconds`.

## The resolve step

`plan` stays portable. `resolve` needs the built worker:

```bash
python -m analysis.oram_bench resolve --campaign campaign --worker build/benchmarks/cpu_oram_benchmark
```

It copies the worker into `campaign/build/worker` and records `build.json`
(worker SHA-256, library-header SHA-256). A later resolve of the same campaign
must present the same binary; a library or worker change needs a new campaign
directory, which `plan` plus `resolve` create in seconds. It then calls
`--resolve-only 1` once per unique resolver input (scheme, widths, capacity,
horizon, API/batch, cores and every explicit `--override.*`), without
placement: slots are chosen on the target at run time, and the configuration
key excludes CPU ids. The immutable, self-hashed `resolution.json` records per
row:

- `status`: `runnable`, `skipped` (with reasons), or `same_as` another trial;
- the configuration key, actual capacity and modelled bytes;
- `estimated_memory`: modelled library bytes, version table, event ring and
  writer chunk, and their sum;
- `worker_arguments`: the exact resolver arguments every attempt starts with.

A row is skipped when the resolver rejects it (`resolver_rejected: ...`), when
modelled library bytes exceed `library_memory_limit_bytes`, or when the estimate
exceeds `host_memory_limit_bytes` less the headroom. Rows that resolve to the
same configuration key with the same inputs, apart from stage, candidate label
and overrides, run once: the later ones are `same_as` the first, and a
saturation-derived rate names its sources by the trials that execute them.
`status` counts `same_as` rows, `reduce` reports the executed result under
every label, and rate freezing follows the links. Cross-field validity of
library options is the C++ resolver's job alone; the Python schema only checks
shape.

## Preflight

One offline command prints the campaign's topology and memory
assessments against saved doctor evidence, and optionally checks one worker's
saved `resolved.json`:

```bash
python -m analysis.oram_bench preflight --campaign campaign --environment saved-host.json \
  [--trial-id TRIAL_ID --resolved saved-resolved.json]
```

- Topology: the environment's exposed physical cores and L3 domains against the
  campaign's `physical_cores` and `required_cache_domains`, plus any doctor
  contract gaps. Slot validity (membership, SMT exclusion) is the C++ worker's
  `--cpu-ids` check and is not repeated here.
- Memory: each runnable row's `resolution.json` estimate against the
  environment's memory limit less headroom.
- Attempt: the worker's configuration key must equal the row's key in
  `resolution.json`, its placement policy must match the campaign, and under
  `near_far` every top-level or nested online helper must share the caller's
  exposed L3.

The command reads files only and writes nothing. Exit status is 0 only when
every assessment is `compatible`. A native `run` applies the topology check
before it launches anything and the attempt check to every attempt.

