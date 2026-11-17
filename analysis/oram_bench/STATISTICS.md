# Portable statistics and checkpoint reduction

The shared histogram, typed timing/outcome accumulator and bounded lossless
checkpoints serve both the live worker and portable replay. This document
describes the checkpoint contract; [WORKER.md](WORKER.md) adds the implemented
full-event protocol, campaign commit verification, raw CSV export and
per-repetition reduction. The worker records service once per public call.

Configure the portable tool independently, avoiding the root project's CPU
feature probe and architecture flags:

```bash
cmake -S analysis -B build/portable-analysis -DCMAKE_BUILD_TYPE=Release
cmake --build build/portable-analysis -j2
ctest --test-dir build/portable-analysis --output-on-failure
build/portable-analysis/oram_bench_aggregate --help
build/portable-analysis/oram_bench_aggregate --format json 0000.bin 0001.bin
build/portable-analysis/oram_bench_aggregate --format csv 0000.bin 0001.bin
build/portable-analysis/oram_bench_aggregate --blocks 0000.bin 0001.bin
```

`--blocks` (json, checkpoint input only; event chunks carry no block boundaries,
and it excludes `--events`, csv and `--trial-boundaries`) keeps the whole summary
byte-identical and appends `blocks`: per checkpoint `interval_id`, `begin_ns`,
`end_ns`, completions, `throughput_ops_per_second` (completions over the block's
own duration) and the same response/queue/service objects (mean, minimum, p50/p95/p99/p999,
maximum, tail-sufficiency flags), from the same `Histogram`. `block_spread` (scope
`across_time_blocks_not_independent_repetitions`) gives, for throughput and each
distribution's mean/p50/p95/p99/p999/maximum, the block count, mean of block values,
sample standard deviation (null for one block), minimum and maximum; empty blocks'
null quantiles are skipped, and p99/p999 add `sufficient_blocks`. This is spread
over time blocks, not a confidence interval; blocks span measurement plus drain,
so a trailing drain block widens it. The Python `reduce` stores it as each
checkpoint repetition's `time_blocks` (null for event-log trials), and `plot`
draws saturated-throughput min/max lines from it.

The test suite creates synthetic timestamps; it has no clocks, map allocation,
benchmark execution, or target-ISA dependency. The root benchmark build also
provides `oram_bench_aggregate`. No Python or JSON library is required by the
C++ accumulator or reducer. Python is used only for CLI integration tests.

## Shared accumulator

The headers are [benchmark_histogram.hpp](../../src/oram/support/benchmark_histogram.hpp),
[benchmark_statistics.hpp](../../src/oram/support/benchmark_statistics.hpp), and
[benchmark_checkpoint.hpp](../../src/oram/support/benchmark_checkpoint.hpp).

`StatsAccumulator::observe(CompletionEvent)` receives one serialized scalar or
batch API call, its dispatch/completion timestamps, and every member's intended
arrival. It observes response and queue once per request, and the full call
service time once per call. Partial batches work identically. No service time
is divided by batch size. Arrivals must precede dispatch, dispatch must precede
completion, and authoritative calls cannot overlap or run backwards.

`OutcomeEvent` records terminal rejected, timed-out, or outstanding requests.
Each logical request must have exactly one terminal event. Outstanding means
censored at the trial's drain deadline; it is not a provisional queue observation.
No latency is generated for these outcomes. Offered count is the sum of the
terminal outcomes. The worker/event-log validator must enforce request IDs and
complete cohort coverage; this statistics layer does not store per-request IDs.

`StatisticsMode::kFullEvents` accepts timing and outcome events.
`StatisticsMode::kCheckpoints` accepts delta checkpoints. Mixing authoritative
modes fails. `diagnostic_only` events never affect totals in either mode, so
sampled traces cannot double count checkpoint distributions or manufacture tails.
Statistics additions and merges check uint64 overflow and fail before mutation.

An interval producer calls `checkpoint(interval_id, begin_ns, end_ns)` on a
full-event accumulator at the end of each interval. It returns only what was
observed since the previous checkpoint (a delta) and opens the next interval;
`finish()` still returns whole-run totals. Every interval contains the entire
response, queue, and service histograms plus all terminal outcome counts.
Intervals partition the event log by completion/outcome time, not by intended
arrival. A batch may have arrived before its completion interval. Interval IDs
start at zero and increase by one; adjacent intervals must meet exactly. Empty
intervals remain present. Duplicate, reordered, overlapping, or gapped intervals
are rejected. Do not pass cumulative snapshots as deltas.

`finish()` validates counts and returns sufficient statistics. Tail sample
sufficiency defaults to at least 100 expected observations beyond a percentile:
p99 needs 10,000 requests, p99.9 needs 100,000. Service tails use batch-call
counts. These flags describe sample counts only. Censoring is reported separately,
and this layer does not classify queue stability (campaign `reduce` does; see
[WORKER.md](WORKER.md)), so these summaries alone do not establish stable tails.

## Histogram version 1

The fixed 14,592-bin layout is a log-linear histogram with 256 sub-bins per
power of two:

- Values `0..511` ns have exact individual bins.
- For larger values, `shift = bit_length(value) - 9` and
  `index = shift * 256 + (value >> shift)`.
- For index `i >= 512`, `shift = (i - 256) // 256`,
  `sub = (i - 256) % 256 + 256`, and the upper bound is
  `((sub + 1) * 2**shift) - 1`. The last bound is `UINT64_MAX`.
- Quantiles use integer nearest rank with millionth fractions. They report
  the selected bin's upper bound, clamped to the observed maximum. The relative
  overstatement bound is `1/256 = 0.390625%`.

Count, sum, extrema, and bins use exact uint64 integers. Each count and each
sum must fit `0..2**64-1`; overflow throws, rather than wrapping or approximating.
Merging adds sufficient statistics, never reconstructed samples. Restoring a
histogram validates bin counts, occupied extrema, and feasible sum bounds.
Empty distributions have null extrema/mean/quantiles in new JSON summaries and
empty numeric CSV fields. Histogram summaries include p95.

## Checkpoint file version 1

This is an intermediate, standalone **statistics checkpoint** format, not the
campaign's complete binary event-chunk protocol. All numeric fields below are
unsigned 64-bit little-endian integers; there is no padding. No native struct
layout, floating point, or `size_t` appears on disk.

| Part | Fields in order |
| --- | --- |
| Header (24 bytes) | Eight ASCII bytes `ORBST01\n`; payload byte length; CRC-32 of payload stored in the low 32 bits of a uint64 (high bits zero) |
| Payload prefix | Checkpoint version `1`; histogram version `1`; bin count `14592`; interval ID; begin ns; end ns |
| Counts | Completed requests; completed batches; rejected; timed out; outstanding |
| Response histogram | Count; sum ns; minimum ns; maximum ns; 14592 dense bin counts |
| Queue histogram | Same fields |
| Service histogram | Same fields |

Empty binary extrema are canonically zero; the zero count makes them null
semantically. Payload length is exactly `350392` bytes; the file is `350416`
bytes. The reader checks this fixed size before allocating its buffer, checks
CRC-32/ISO-HDLC (reflected polynomial `0xedb88320`, init/final xor `0xffffffff`),
validates all statistics, and rejects trailing bytes and unsupported versions.
The checksum fixture `123456789` produces `0xcbf43926`.

`WriteCheckpoint` performs synchronous encoding/I/O and is intended to run
outside the timed caller. The worker supplies a preallocated event queue and
background writer; the coordinator supplies atomic publication, fsync,
SHA-256 manifests and final commit markers. CRC protects against accidental corruption, not malicious edits.

## Reduction scope

The CLI reduces the checkpoints supplied on its command line in that order and
writes JSON or three CSV distribution rows. Inputs must all belong to the same
repetition; they carry no trial/environment IDs, so the caller (the campaign
reducer) is responsible for grouping them. It outputs only after
all supplied files validate. Exit status 2 means an input/output failure.

When invoked with bare checkpoint files, the summary explicitly says
`supplied_checkpoints_only`. That mode does not verify a campaign or infer
throughput from interval lengths. Full worker reduction also supplies the raw
trial boundaries and verifies the cohort totals; full-event replay validates
arrival/member/outcome identities and call order. The Python campaign reducer
verifies committed manifests before invoking these C++ paths.

Campaign `reduce` labels queue stability per repetition and reports spread
across time blocks (`--blocks` above); it computes no confidence intervals.
See [WORKER.md](WORKER.md) for the commands, raw formats, local acceptance
tests and publication gates.
