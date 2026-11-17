# Measurement support

This directory is benchmark infrastructure, not part of the oblivious map. See
[DESIGN.md](DESIGN.md) for timing semantics and histogram bounds.

What is timed, in brief: a trial either runs *saturated* (a closed loop that
issues the next public call as soon as the previous one returns and reports
completed requests per elapsed time, reading the clock at least once per window of
requests) or at a *fixed offered rate* (an open loop whose request arrival
times are computed in advance from the rate). In the open loop the worker
reads the clock when it dispatches a call and when the call returns; each
request's latency is completion minus its intended arrival, split into
queueing (dispatch minus arrival) and service (completion minus dispatch).
Throughput is reported both to the caller's end (last request returned) and
to the drain end (after background maintenance finishes). All timestamps are
nanoseconds from `std::chrono::steady_clock` (or a test clock with the same
interface), and all observations go into fixed-size streaming histograms.

These portable C++17 headers are the measurement core of the one-trial worker
(`benchmarks/support/worker.hpp`) and of the offline reducer
(`analysis/oram_bench_aggregate.cpp`). None of them includes the map, needs the
library's ISA, or times requests with a clock other than `steady_clock`
(the optional checkpoint thread also reads its own CPU time):

- `benchmark_arrival.hpp`: arrival profiles and `FixedArrivals`, the
  closed-form (constant-space) fixed-rate arrival schedule.
- `benchmark_workload.hpp`: the deterministic `counter_permutation_v1`
  record and request generator.
- `benchmark_trial.hpp`: `RunTrial`, the phased trial loop -- saturated count
  windows, or an offered load through a bounded queue with batching, timeouts
  and a drain deadline.
- `benchmark_invocation.hpp`: the service-timing bracket around one public call.
- `benchmark_histogram.hpp` and `benchmark_statistics.hpp`: the version-1
  histogram and the typed `StatsAccumulator`.
- `benchmark_checkpoint.hpp`, `benchmark_events.hpp`, `benchmark_summary.hpp`
  and `benchmark_repetitions.hpp`: checkpoint and raw-event formats, replay and
  JSON summaries.

[WORKER.md](../../../analysis/oram_bench/WORKER.md) documents the worker's
contract, and [STATISTICS.md](../../../analysis/oram_bench/STATISTICS.md) and
[WORKLOAD.md](../../../analysis/oram_bench/WORKLOAD.md) the statistics and the
generators. The validation targets are the portable `oram_bench_*_test.cpp`
files in [`tests/analysis`](../../../tests/analysis) and, against real maps,
[`cpu_byteslice_trial_adapter_test.cpp`](../../../tests/oram/cpu_byteslice_trial_adapter_test.cpp)
(closed loop) and
[`cpu_byteslice_open_loop_adapter_test.cpp`](../../../tests/oram/cpu_byteslice_open_loop_adapter_test.cpp)
(offered load).

This is measurement infrastructure, not an ORAM engine or rebuild kernel, so it
is kept outside `rebuild/`.  Production users of the public map API do not need
to include it.
