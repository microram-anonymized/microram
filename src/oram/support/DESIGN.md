# Measuring service, queueing, and batching separately

Background rebuilding can move work away from a request without eliminating
that work. A throughput loop cannot show whether requests queue while a worker
falls behind. The trial runner therefore separates an external arrival
schedule from the execution of operations, so latency includes delay caused by
earlier operations.

## Arrivals do not follow completion

[`benchmark_arrival.hpp`](benchmark_arrival.hpp) computes arrivals from public
parameters, not from engine progress: request `k` of a fixed-rate run arrives
at `floor(k * gap)`. In [`benchmark_trial.hpp`](benchmark_trial.hpp), a request
that arrives while the preceding operation is still running waits, and keeps
its original arrival time. The waiting requests are the index range between
the next one to serve and the last one that has arrived, so the loop stores
and copies nothing per request.

For request `i`, let `a_i`, `s_i`, and `e_i` be its intended arrival, actual
start, and completion times. The runner records:

```
queue_i   = s_i - a_i
service_i = e_i - s_i
latency_i = e_i - a_i = queue_i + service_i
```

The runner reads the clock once per call. When requests are already waiting,
`s_i` is the read that completed the previous call, so `service_i` also holds
the harness's work between the two calls (result checks of the previous call,
statistics, and this call's preparation).

Resetting an arrival time after a stall would discard the queueing term. The
open-loop contract preserves it. Saturation measurements use a separate closed
loop that issues the next operation immediately after completion and reports
completed operations per elapsed time. That loop measures throughput and may
record service intervals; it does not establish latency under an offered load.

## Charge the wait to fill a batch

A fixed-count batch begins only after its last request has arrived. For a batch
of `b` requests arriving regularly at rate `r` requests per second, the first
request waits `(b-1)/r` seconds for the batch to fill, even with an idle
engine. The mean fill delay is `(b-1)/(2r)`. These follow by averaging the
delays `0, 1/r, ..., (b-1)/r`. A batch timeout bounds that wait by dispatching
a partial batch.

All requests in a batch share its start `s` and completion `e`, but retain
their individual arrival times. End-to-end latency `e-a_i` and queueing `s-a_i`
are weighted by request. Service `e-s` is recorded once per public call and
weighted by call; dividing it by `b` would report a time no request
experienced.

## Bound measurement memory

Retaining every observation uses memory proportional to the request count and
can change the memory pressure of the engine being measured. Streaming
histograms make the headline statistics independent of run length. Each
histogram has `(64-9)*256 + 512 = 14,592` counters of eight bytes, or 116,736
bytes (114 KiB) of bucket storage, plus scalar statistics. This count follows
from `Histogram::kBucketCount`, rather than a platform memory measurement.

Values below 512 nanoseconds have exact buckets. Above that range, each octave
has 256 buckets. The maximum relative bucket width is `1/256`, or 0.390625%.
Quantiles use the bucket's upper bound, capped at the observed maximum, so
quantization does not understate the sampled quantile. Counts, sum, minimum,
and maximum are exact integers. The arrival iterator is constant-space; only
the diagnostic full-event buffer grows with run length, and the worker
allocates it before the trial begins.

The [README](README.md) gives the headers and validation targets.
Update this document in place under the
[maintenance rule](../../../DESIGN.md#documentation-maintenance).
