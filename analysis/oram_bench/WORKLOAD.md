# Portable workload and arrival primitives

[benchmark_workload.hpp](../../src/oram/support/benchmark_workload.hpp) supplies
deterministic record/request generation. [benchmark_arrival.hpp](../../src/oram/support/benchmark_arrival.hpp)
supplies the shared arrival enum and a constant-space schedule iterator. Both
are C++17 headers without engine, clock, Python or ISA dependencies. They are
the building blocks of the campaign one-trial worker ([WORKER.md](WORKER.md)).

## Workload contract

`WorkloadSpec` contains live entries, disjoint miss key count, key/value widths,
read/hit fractions in integer millionths, seed and the maximum buffer request
count. All widths are positive. Live plus miss count must fit uint64 and the
declared key width. `(4,8)`, `(8,48)` and `(32,1024)` are ordinary supported widths.
The generator allocates no dataset or request buffers. It rejects incompatible
miss/write policies exactly as the campaign schema does: misses require a
nonempty disjoint set, and mixed hit/miss workloads are read-only in v1.

`At(request_id)` returns the public key ID, read/update choice, expected hit and
update version. IDs `0..live_entries-1` are live and the subsequent IDs are misses.
Uniform key selection uses rejection sampling, avoiding modulo bias. Separate
counter streams select hit, write and key. Decisions depend only on public seed
and request ID. Batch size, record width, scheme and completion speed do not
change that sequence. Repeated keys are intentional and retain request order.

`Key` encodes an ID as a seeded odd affine permutation in the first
`min(key_bytes,8)` bytes, little endian. This is a bijection over the validated
key space, so a narrow key cannot alias a live key with a miss key. Wider keys
retain the injective eight-byte prefix and fill the suffix with deterministic
ID-dependent bytes. These synthetic public keys are not cryptographic secrets.
`KeyId(key)` inverts the prefix in O(1) (the no-op backend's lookup); it does
not check suffix bytes, and a prefix outside the workload decodes to an ID at
or beyond the live plus miss count.

`Value(key_id, version, output, width)` fills every value byte deterministically,
one mixed 64-bit word per 8 bytes (little endian; a partial last word is truncated).
Initialization uses version zero; each update uses `request_id+1`, so an
update's value needs no per-key state, with or without the worker's version
oracle. Request IDs
range from zero through `UINT64_MAX-1`; the last uint64 ID is rejected before
its version could wrap. Read requests carry zero in `value_version`, meaning no
update payload; it is **not** the expected current version of the stored value.

`MatchesValue` compares every byte, a word at a time, against an explicitly supplied expected
version, without allocating another record. It supports initialization/read-only
checks and small reference-map mixed-workload tests. The caller must retain or
otherwise determine the latest version. Large mixed-workload validation without
an O(N) reference map is the worker's job (its version oracle); this helper does not
claim to detect stale updates without knowing their expected versions.

The `counter_permutation_v1` algorithm uses uint64 wraparound throughout. Let
`mix(x)` apply xor-right-30, multiply `0xbf58476d1ce4e5b9`, xor-right-27,
multiply `0x94d049bb133111eb`, then xor-right-31. A stream starts at
`mix(seed XOR domain) + request_id * 0x9e3779b97f4a7c15`; each draw adds that
same stride and returns `mix(state)`. Domains 1/2/3 select hit/write/key.
For bound `b`, discard draws below `(2^64-b) mod b`, then take the remainder
modulo `b`. Hit tests `< hit_ppm`; write tests `>= read_ppm`.

The key prefix is `id * (mix(seed XOR 4) OR 1) + mix(seed XOR 5)`.
Suffix word `j` (starting at 1) is `mix(id XOR mix(seed XOR 6) XOR j)`.
Value word `j` (starting at 0) is
`mix(mix(seed XOR 7) XOR mix(id) XOR mix(version XOR 0xd1b54a32d192ed03) XOR j)`.
Words emit little endian, truncated only to the already validated record width.
Golden fixtures freeze this identity; changing its output requires a new schema
generator identity, not reinterpretation of an existing campaign.

**Counter keys.** With `workload.distribution: counter` (the worker's
`--key-pattern counter`, used by every [paper preset](../../benchmarks/campaigns/paper/README.md)),
request `k` touches live key `k * S mod N` instead of a random one, where the
stride `S` is the first integer at or above `floor(N * 0x9e3779b97f4a7c15 / 2^64)`
(about 0.618 N) that is coprime with `N`. Any `N` consecutive requests therefore
touch every live key once, and consecutive requests touch scattered keys. Reads
and updates are not drawn per request: the worker draws them as above (domain 2)
for request IDs 0 to 4,095 once, and request `k` takes the decision of request
`k mod 4096`. Two consequences follow.

- The write share of a run is the share in those 4,096 draws. It is fixed by
  the workload seed and is not exactly `1 - read_ppm`: at a nominal 5% its
  standard deviation over seeds is about 0.35 points, so repetitions with
  different seeds run slightly different mixes.
- When `N` is a multiple of 4,096 (every power-of-two capacity from 4,096 up),
  the visits to one key, `N` requests apart, all take the same decision: each
  key is either always read or always updated.

The pattern issues hits only (`hit_ppm` must be 1,000,000). It keeps the key
generator's draws off the request thread, and it gives a batch of up to `N`
requests distinct keys.

## Arrival contract

`ArrivalSchedule(ScheduleSpec, optional_horizon_ns)` exposes `Next()` returning
an optional uint64 nanosecond offset. It uses constant storage, including a
fixed-size `mt19937_64` state. Intended times never consult service completions
or a wall clock. An explicit horizon admits offsets in `[0,T)`; repeated calls
after exhaustion return null. `num_accesses` remains an independent safety cap.
A worker that hits the cap before the cohort is complete must record that limit,
not claim it observed the whole arrival horizon.

Fixed arrivals are the only offered-load profile. Request `k` arrives at
`floor(k * 1e6 / rate_kops)` ns, so the first arrival is at zero and no
arrival is generated or stored: the trial computes it from the request index.
The spec expresses rate in kops/s. Zero, negative, nonfinite and
unrepresentable rates fail. Unsafe timestamp conversions fail explicitly; an
arrival at or beyond the horizon is omitted. Saturation issues requests
directly, takes no arrival horizon and generates no arrivals.

Rates are floating-point kops/s. Workload bytes
are integer-defined across platforms; exact stochastic schedule replay is only
promised within a compatible build/math environment. A campaign-to-worker bridge
must preserve units/precision and bind build provenance before exact replay.

## Validation without measurements

```bash
cmake -S analysis -B build/portable-analysis -DCMAKE_BUILD_TYPE=Release
cmake --build build/portable-analysis -j2
ctest --test-dir build/portable-analysis --output-on-failure
```

`oram_bench_workload_test` uses generated integers and a small reference fixture;
it reads no clock and constructs no ORAM. It covers width/key-space boundaries,
disjoint misses, seed replay, scalar versus batch request identity, repeated-key
updates, full-value corruption, buffer/version limits, frozen schedule fixtures,
mean offered rates per profile, half-open horizons, huge count caps, invalid
rates/phases and timestamp overflow.
The worker integrates these primitives. Real-engine correctness tests with
synthetic timestamps, and portable lifecycle/recovery tests, are described in
[WORKER.md](WORKER.md). None of these tests measures performance.
