# cpu_byteslice_oram

A header-only C++17 library of fixed-capacity oblivious key–value maps for one
x86-64 machine with AVX-512. Memory-access patterns and control flow are
designed to hide which keys are requested and whether lookups succeed. The
library provides two constructions:

- a **byte-sliced hierarchical ORAM**: recent accesses live in a dense online
  stash, older records in geometrically growing hashed tables that are rebuilt
  obliviously, either incrementally on owner threads or synchronously by the
  caller;
- a **tree ORAM for large values** (Path ORAM with read-path eviction) that
  stores values in a tree and small location records in a hierarchical
  position map.

A hybrid map chooses between them from the public value width. Read the
[design overview](DESIGN.md) and its
[security boundary](DESIGN.md#security-boundary-and-limitations) before
relying on the library.

```cpp
#include <cpu_byteslice_oram/oram.hpp>
#include <cstdint>

cpu_byteslice_oram::Map<uint64_t, uint64_t> map(1'000'000);
map.write(42, 7);  // blind upsert; insert_or_assign is the same operation
uint64_t out = 0;
bool found = map.find(42, &out);  // one access, hit or miss
```

## Layout

| Directory | Contents |
|---|---|
| [include/cpu_byteslice_oram](include/cpu_byteslice_oram/README.md) | Public byte, typed, tree, hybrid and configuration APIs |
| [src](src/DESIGN.md) | Implementation headers; [src/DESIGN.md](src/DESIGN.md) is the source index, reading order and glossary |
| [src/core](src/core/README.md) | Register-only constant-time selection, worker waits and the release-build instrumentation guard |
| [src/crypto](src/crypto/README.md) | AES key schedules, key derivation, routing tags and stored-key normalization |
| [src/oram](src/oram/README.md) | How the ORAM components compose ([design](src/oram/DESIGN.md)) |
| [src/oram/table](src/oram/table/README.md) | Byte-sliced bucket layout, metadata, matching, probes and batch forwarding |
| [src/oram/rebuild](src/oram/rebuild/README.md) | Oblivious routing networks, deduplication and residual recovery |
| [src/oram/scheduler](src/oram/scheduler/README.md) | Rebuild phase plans, resumable cursors and lanes |
| [src/oram/levelarena](src/oram/levelarena/README.md) | The hierarchical engine: geometry, merges, publication, owner threads, synchronous mode |
| [src/oram/tree](src/oram/tree/README.md) | Tree ORAM: geometry, read-path eviction, payload workers and position maps |
| [src/oram/support](src/oram/support/README.md) | Portable measurement infrastructure used by the benchmarks (not part of the map) |
| [cmake](cmake/DetectCpuFeatures.cmake) | CPU-feature probe and the installed package configuration |
| [tests](tests/README.md) | Correctness tests (`tests/oram`, one CTest binary per `*.cpp`, grouped in the tests README) |
| [tests/timing](tests/timing/README.md) | Constant-time instruction measurement and the instruction census |
| `tests/release_guard` | Checks that `CPU_BYTESLICE_ORAM_RELEASE` refuses every instrumentation macro |
| `tests/analysis` | Unit and CLI tests for the benchmark harness and the analysis scripts (synthetic fixtures) |
| [benchmarks/oram](benchmarks/oram/README.md) | Benchmark drivers: public-map worker, engine diagnostics, kernel and tree studies, host characterization |
| `benchmarks/support` | Shared C++ worker harness: option parsing, workload oracle, event log, memory telemetry, backends |
| [benchmarks/baselines](benchmarks/baselines/README.md) | Workers for the compared systems (H2O2RAM, SONIC), pinned fetches and patches |
| [REPRODUCE.md](REPRODUCE.md) | **How to reproduce every measured number in the paper**, item by item |
| [benchmarks/campaigns](benchmarks/campaigns/README.md) | Experiment presets (the paper's exact campaigns in [paper/](benchmarks/campaigns/paper/README.md)) and how to prepare VMs and run campaigns |
| [analysis/oram_bench](analysis/oram_bench/README.md) | Campaign planning, execution, reduction and plotting; also indexes the other `analysis/` scripts |
| [analysis/bound_certification](analysis/bound_certification/README.md) | Capacity-failure certification: report, certifiers and generated tables |
| [analysis/deamortization](analysis/deamortization/README.md) | Rebuild-speed and tables-per-lookup model of deamortization |
| [lean](lean/README.md) | Lean 4 formalization of the capacity and obliviousness bounds |
| [examples](examples/CMakeLists.txt) | Installed-library consumers: `basic.cpp` and the [Ethereum MPT example](examples/ethereum_mpt/README.md) |

Each source directory has a `DESIGN.md` for mechanisms, their correctness and
security arguments, and a `README.md` for engineering entry points and the
tests that cover them. Applications should use the public headers and CMake
target; `src/` paths are implementation details.

Recurring terms (*level*, *carry*, *prefix*, *inbox*, *tier*, *residual*,
*owner*, *helper*, *nonce family*, ...) are defined in the
[ORAM overview](src/oram/DESIGN.md#components-and-reading-order), in the
[top-level design](DESIGN.md), and in the term lists that open the
[table](src/oram/table/DESIGN.md), [rebuild](src/oram/rebuild/DESIGN.md) and
[arena](src/oram/levelarena/DESIGN.md) designs.

## Requirements

GCC and x86-64 with AVX2, AVX-512 F/VL/BW/DQ/VBMI/VBMI2/CD, AES-NI, VAES,
BMI1, BMI2 and LZCNT are required. The register-only assembly primitives and
code-generation checks support GCC only. CMake checks the build host's CPU
features and compiles with `-march=native`; run the resulting binary on
compatible hardware. There is no non-AVX-512 fallback. A cross-compiling
configure without `CMAKE_CROSSCOMPILING_EMULATOR` skips the CPU check, and
`-march=native` still selects the build host's CPU.

The project configures with CMake 3.16 or later. The `ctest --test-dir`
commands in this repository need CMake 3.20; with an older CMake, run CTest
from the build directory instead: `(cd build && ctest --output-on-failure)`.

VP2INTERSECT is optional. When available, it accelerates shared key
intersections. `-DCPU_BYTESLICE_ORAM_ENABLE_VP2INTERSECT=OFF` selects the
emulation and exact-matching paths even on a capable host. With it,
`CPU_BYTESLICE_ORAM_WIDE_KEY_VP2INTERSECT` (default ON) also matches 16-byte
stored keys (user keys of 16 bytes or more, all AES outputs) approximately:
rebuild deduplication ANDs four 32-bit segment matches and dense batch lookup
ANDs two 64-bit halves, so different partners can supply different parts. If
stored keys are ideal and never exposed to or chosen by the caller, a compared
rebuild slot falsely matches with probability at most 2^-104; see
[stored-key matching](analysis/bound_certification/ERROR_ACCOUNTING.md#stored-key-matching).
Turn it OFF for exact wide-key matching. The AES tag kernels
also have an AES-NI path selected by `MICRORAM_BYTESLICE_USE_VAES=0`, but CMake's
baseline check still requires VAES.

Python 3 runs the benchmark harness, analysis scripts and certifiers; the
campaign harness needs only the standard library to plan and run; its `plot`
and `timeseries` figures, `analysis/paper_numbers.py` and
`analysis/plot_stash_tail.py` draw their figures with matplotlib when it is
installed, `analysis/plot_stash_vs_n.py` uses matplotlib and numpy, and the
Python statement checks in `lean/spec_tests/` use mpmath. The Lean formalization needs `elan`/`lake`; see its
[README](lean/README.md#build).

## Build

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DCPU_BYTESLICE_ORAM_BUILD=tests
cmake --build build -j2
ctest --test-dir build --output-on-failure
```

`CPU_BYTESLICE_ORAM_BUILD` selects `library`, `tests` or `all` (tests plus
benchmarks and the campaign tools in `analysis/`). The top-level default is
`all`; embedding with `add_subdirectory()` defaults to `library`. The
fine-grained `CPU_BYTESLICE_ORAM_BUILD_TESTS` and
`CPU_BYTESLICE_ORAM_BUILD_BENCHMARKS` options override the current preset;
changing the preset resets them.

Every `tests/oram/*.cpp` produces a release test and an assertion-enabled
`_checked` test. On a VP2INTERSECT host with segment matching enabled, three
`_exact_wide` twins also test the exact wide-key path. CTest also runs the
instrumentation-guard check and a constant-time smoke test. The instruction
census needs line tables and is opt-in: `-DCPU_BYTESLICE_ORAM_INSTRUCTION_CENSUS=ON`
builds the tests with `-g1` and adds it to CTest. Run the full timing
certification on an idle, compatible host as explained in
[tests/timing](tests/timing/README.md). Correctness tests alone do not
establish obliviousness.

The Python tests run with `python3 -m unittest discover -s tests/analysis -v`.

## Library API

Include `<cpu_byteslice_oram/oram.hpp>`. The public namespace is
`cpu_byteslice_oram`.

| Type | Backend |
|---|---|
| `Map<Key, T, Deamortize = true>` | Hybrid typed map |
| `HybridByteMap<Deamortize = true>` | Hybrid byte map |
| `HierarchicalMap<Key, T, Deamortize = true>` | Hierarchical typed map |
| `ByteMap<Deamortize = true>` | Hierarchical byte map |
| `TreeMap<Key, T, Deamortize = true>` | Tree typed map |
| `TreeByteMap<Deamortize = true>` | Tree byte map |

The hybrid chooses the tree when the value width is at least
`HybridOptions::tree_value_threshold`. Unset, the library's default rule
(`DefaultRule` in `default_rule.hpp`, shared with the resolver's `auto`)
decides, which puts the crossover at 96 bytes (`kHybridTreeValueThreshold`,
one flat constant for every thread budget). This is a fixed public policy,
not runtime tuning; it was chosen from value-width sweeps, and the crossover
for a deployed workload and thread budget should be measured.
`Map<K, T> map(capacity, CoreBudget{n})` instead gives the map n cores
(caller included) and configures it exactly as the resolver's `auto` does at
that budget. The tree runs one payload worker per started 32 bytes of value
with no fixed cap, bounded by the physical cores the caller and the position
map leave; with several cache domains the resolver keeps them on the caller's
domain and spreads them over all domains only from `kTreePayloadSpreadBytes`
(2048) bytes.

`ByteMap<true>` uses per-level arenas with incremental rebuilds and defaults
to two owner threads. Setting `deamortized_owner_threads = 0` runs bounded
shares of rebuilding on the caller. `ByteMap<false>` uses synchronous storage:
the request completing a prefix runs all triggered merges, with one main region
per level, which takes about half the incremental mode's main-table storage. In
tree maps, `Deamortize` selects the position map's hierarchical mode; payload
workers are controlled separately.

`ByteMap` accepts `Options`, `TreeByteMap` accepts `TreeOptions`, and hybrids
accept `HybridOptions`. An `Options` implicitly converts to `HybridOptions`,
configuring the hierarchy directly or the tree's position map.

### Byte interface

Key and value widths are fixed at construction. Buffers remain valid for the
duration of a call. A successful lookup copies the value; a miss fills the
output with zeros. The returned presence bit is secret.

```cpp
cpu_byteslice_oram::ByteMap<> map(10'000, 16, 32);
uint8_t key[16] = {1};
uint8_t value[32] = {7};
uint8_t out[32];
map.write(key, value);
bool found = map.find(key, out);
bool present = map.contains(key);

// Return the old value and replace it when present or insert is true.
bool existed = map.exchange(key, value, out, /*insert=*/true);
bool erased = map.erase(key, out);  // old value, or zeros if absent
```

Each `find`, `contains`, `write` (also named `insert_or_assign` and
`insert_without_probe`), `exchange` and `erase` advances the access schedule
once. Hierarchical writes are blind: they skip the lookup cascade, including
when replacing an existing key, and the rebuild's deduplication later discards
the older copy. A blind write is therefore distinguishable from a probing
operation; see [Security boundary](DESIGN.md#security-boundary-and-limitations).
`exchange` reads the previous value and replaces it in one
access. The tree still needs its position lookup and path access for a write,
but skips returning the old value. Reads and misses mutate internal state.
There are no iterators, references into storage or `operator[]`.
A moved-from map may only be destroyed or assigned to.

Capacity bounds the live key set. `capacity()` may exceed
`requested_capacity()` because the geometry rounds up. There is no automatic
resize or exact live-size counter. Exceeding capacity violates the construction's
load assumptions; failure may occur during a later rebuild.

Keys of one through fifteen bytes are stored exactly, at their own width. Keys
of 16 bytes or more become 128-bit stored keys under a separate secret AES
schedule. At a fixed width of sixteen bytes this conversion is injective;
longer keys have a cryptographic collision risk. See the
[crypto design](src/crypto/DESIGN.md). Keys are at most 64 bytes
(`kMaxUserKeyBytes`) in every map, the tree's position map included; a wider
key is refused with `std::invalid_argument` by the constructors and the
resolver.

### Bulk initialization

`ByteMap` and `HierarchicalMap` support one-shot `initialize(first, count)` on
an untouched map. It builds the largest table directly. `count` is public,
at most `capacity()`, and may be zero. Empty input leaves an untouched map
untouched. A drain (`drain_rebuilds()`, `finish_pending_work()`) before any
access or `initialize` call does nothing and leaves the map untouched too.
Only `InitializationPolicy::kDistinct` is supported: the caller must guarantee
distinct keys.

The byte iterator yields `InitializationEntry{key_pointer, value_pointer}`;
both buffers must remain valid until the iterator is incremented. The typed
iterator yields pair-like records convertible to `Key` and `T`. Only one input
record is buffered, so single-pass generators are supported.

```cpp
#include <utility>
#include <vector>

std::vector<std::pair<uint64_t, uint64_t>> records{{1, 10}, {2, 20}};
cpu_byteslice_oram::HierarchicalMap<uint64_t, uint64_t> loaded(4096);
loaded.initialize(records.begin(), records.size());
```

Initialization leaves `access_count()` at zero. Iterator exceptions restore the
logical state; spent normalization reservations remain charged, so a retry
requires sufficient remaining allowance. Rebuild failures must be handled according
to the engine's failure contract. Owner threads start after a nonempty load or
on first use, allowing bulk initialization with any owner count. The
[rebuild design](src/oram/rebuild/DESIGN.md#initialize-directly-into-the-final-table)
explains the direct build.

`Map`, `HybridByteMap` and tree maps do not expose this initializer;
`supports_initialize` describes the typed/byte adapter capability.

### Batched access

Requests execute in lane order for equal keys: later requests see earlier
writes and erases. Inputs, keys and request descriptors must not alias or
depend on another lane's output buffers, including `found_out`; when they do,
the result depends on the batch execution shape. A lane's own value input
and output may overlap, even partially.

For every operation, including writes, a non-null output receives the previous
value, or zeros if absent. A non-null `found_out` receives one byte per request
indicating presence before that operation. Operation codes, the exchange
`insert` flag, and whether each value output or the batch presence output is
requested are public. Output descriptors help determine the hierarchy's
probe pattern and chunk boundaries.

Use `BatchOp::kWrite` for an upsert without an old value or presence result.
The hierarchy executes these lanes as blind writes when both `value_out` and
the batch's `found_out` are null. Packed `insert_or_assign_batch` uses this
path too. `BatchOp::kReadThenWrite` always takes the probed replacement path;
`kExchange` additionally controls insertion on a miss. `kWrite` probes when an
old value or presence result is requested. Blind writes split the hierarchy's
probed batches into contiguous runs, so mixed batches may have less probe
parallelism.

Required pointers must be valid. Invalid-request handling is not transactional
across backends: a tree batch may apply a valid prefix before rejecting a later
null pointer, while the hierarchy validates all pointers before mutation.

```cpp
using namespace cpu_byteslice_oram;
BatchRequest requests[] = {
    {BatchOp::kWrite, false, key, value, nullptr},
    {BatchOp::kRead, false, key, nullptr, out},
};
uint8_t found_flags[2];
map.access_batch(2, requests, found_flags);
```

Packed byte conveniences are `find_batch(n, keys, values_out, found_out)`,
`insert_or_assign_batch(n, keys, values)` and `erase_batch(n, keys, found_out)`.
Keys and values are contiguous at their configured widths. Typed maps provide
these forms over arrays of `Key`, `T` and `bool` presence flags.

Both hierarchical modes use chunked probing by default, with
`deamortized_batch_lanes = 16` (range 1–64). Arbitrarily long batches run in
successive chunks. `kParallelTiles` enables a persistent participant pool;
`deamortized_batch_participants` includes the caller. `batch_lanes()` reports
width per participant and `max_combined_batch_lanes()` the maximum snapshot width.
Each internal probing job also ends at the next requester-unit boundary,
including jobs spanning several participants. This preserves frozen history
when a later lane repeats a key; it can reduce the effective chunk width.
Runtime setters may narrow the pool but cannot exceed its constructed capacity.
Tree batches combine position-map operations, then execute paths in request
order. Every request counts as one logical access. A tree map's
`set_batch_lanes` validates the same range and then ignores the value: the
tree's batch width is fixed. The
[table design](src/oram/table/DESIGN.md#share-extraction-and-dense-scans-across-lanes)
explains batch matching and forwarding.

The ordering contract is also part of the Lean reference model
([`Spec/ApiGrouped.lean`](lean/RebuildBound/Spec/ApiGrouped.lean)),
which shows that cutting a batch into chunks preserves each request's result
and the chronological record of effects.

### Bottom-level fanout

The hierarchical planner selects a geometry covering the requested capacity.
`Options::deamortized_branching_factor` is 2, 4 or 8 (default 8).
`deamortized_half_fanout_prefix` allows smaller fanouts at the bottom of an
8-way hierarchy. `deamortized_top_digit = 0` and
`deamortized_prefix_flushes = 0` let the planner choose; explicit top digits
are 1, 2, 4 or 8, at most the branching factor.

`deamortized_bank_first` defaults to `BankFirst::kNoClone`, starting partial
builds in the level's local bank. Residual tiers are sized per level from the
geometry and `max_accesses` horizon (default `2^32`); a positive
`deamortized_tier_buckets` pins a shared width and must meet the occupancy
requirement. See the [arena design](src/oram/levelarena/DESIGN.md).

The hierarchy also enforces `max_accesses` as an online access limit. A scalar
request or internal batch chunk that exceeds the remaining budget throws
`std::overflow_error` before probing or changing records. Earlier batch chunks
remain committed; a smaller retry can use the remainder. Initialization does
not consume this budget, and pending work can still drain after exhaustion.

`max_key_normalizations` separately limits AES conversions of keys of 16 bytes
or more. Unset, it allows `capacity() + max_accesses` conversions; an explicit
zero forbids them. Initialization and internal batch chunks reserve their full
input count before conversion. Failed attempts keep their reservations, so
retries may need a larger allowance set at construction. Exhaustion throws
`std::overflow_error` before the new conversion or request changes records.
This bounds normalization work, not the hierarchy's total cryptographic error;
see the [accounting derivation](src/oram/levelarena/DESIGN.md#normalization-budget).

`max_routing_evaluations` limits routing messages, counting repeated work,
SIMD padding, rebuilds and failed initialization. Its default is `UINT64_MAX`,
an arithmetic ceiling rather than a cryptographic target. A refused reservation
throws and permanently stops the instance; accepted work may be incomplete and
cannot be drained or retried. Set the limit for the deployment's query budget;
it does not guarantee completion of `max_accesses`. The engine exposes
`RoutingEvaluationCount()` and `MaxRoutingEvaluations()`; see the
[routing accounting](src/oram/levelarena/DESIGN.md#routing-budget).

### Dense prefix and backpressure

`deamortized_online_stash_entries` is the insertion unit: 64 times a power of
two, at most 262144 (`kMaxOnlineStashEntries`), default 64.
`deamortized_prefix_flushes` units form a dense prefix;
their product is the prefix's entry count. Accesses scan the active stash,
retained prefixes and published tables. `deamortized_dense_prefixes` (default 2)
bounds outstanding complete prefixes and therefore controls backpressure.

Use `plan_geometry()` to inspect the selected geometry before construction and
`geometry_choice()` afterward. `arena_bytes()` and `byte_bill()` report modeled
engine buffers; `main_arena_bytes()` reports level storage, including the residual payload
pool, retained arena holes and masks. These are not
whole-process memory measurements: objects, container overhead and thread stacks
are outside parts of the bill. The [configuration API](include/cpu_byteslice_oram/CONFIGURATION.md)
provides an explicit core budget, resolved settings, buffer limits, thread roles
and `ConfiguredByteMap`. Resolution uses public inputs and does not build a map.

### Capacity certification

`ByteMap<true>::certification()` and the resolver's
`ResolvedPlan::certification()` report, for the exact geometry and request
horizon, whether the configuration is covered by the generated capacity table and the
conditional failure bound it records (see the
[certification report](src/oram/levelarena/DESIGN.md#certification-report)).
The table is produced offline by
[analysis/bound_certification](analysis/bound_certification/README.md), which
derives the bounds, states every premise, and regenerates the table. Its
[Lean formalization](lean/README.md) proves, in an
ideal reference model, API correctness, an exact simulator for the probe view,
and capacity failure at most `h * 2^-64` over `h` windows of `2^32` accesses
for the standard geometries; correspondence with the native code and the
cryptographic replacements remain explicit premises, listed in
[LEAN_CLAIMS.md](analysis/bound_certification/LEAN_CLAIMS.md).

### Scalar value workers

Scalar hierarchical value workers are disabled by default (`value_workers=0`).
Opt-in workers split fixed user-value columns while the requester retains
metadata and a public tail; full operations and automatic insertion drains
are described in the [level-arena guide](src/oram/levelarena/README.md).
They need a dense prefix of at most 4096 buckets
(`deamortized_prefix_flushes * deamortized_online_stash_entries / 64`);
construction refuses a longer one with `std::invalid_argument`.

### Typed interface

`Key` and `T` must be trivially copyable. Keys are compared by object
representation, so a typed map refuses at compile time a `Key` type whose
equal values can differ in their bytes
(`std::has_unique_object_representations`): one with padding bytes, which an
ordinary copy need not preserve, or with floating-point members. Encode such
keys into a type without padding, such as a byte array. A typed `Key` is at
most 64 bytes.
`find(key, &out)` supports values without a default constructor and writes the
output on both hits and misses. Zero bytes on a miss need not represent a valid
application value; inspect the presence result before interpreting such types.

The optional-returning `find(key)` and throwing `at(key)` additionally require
default construction. These conveniences expose hit/miss in control flow. Use
the pointer form when the caller must keep that distinction hidden.
They return `T` by value, so they hold a `T` on the caller's stack.
`find(key, &out)` writes straight into `out`. `exchange`, callback `access`
and bulk initialization stage one temporary value: on the stack up to
`kTypedStackValueBytes` (4096 bytes), and above that in a buffer the map
allocates once, at construction. So a value of any width needs no more stack
than that, except through `find(key)` and `at(key)`. Byte maps
also expose `exchange` and erase-with-old-value; typed adapters expose the
map-like find, write, insert, exchange, erase, contains and packed batch operations.

### Callback access

All byte and typed maps, including `ConfiguredByteMap`, provide
`access(key, update)` and the equivalent `Access(key, update)`. The callback
runs exactly once, receives the current value (all-zero bytes on a miss), and
mutates it in place. The result is always inserted or replaced. The operation
returns whether the queried key was present before the callback.

```cpp
cpu_byteslice_oram::Map<uint64_t, uint64_t> map(4096);
map.write(42, 7);
map.access(42, [](uint64_t& value) { ++value; });
map.Access(42, [](uint64_t& value, bool found) {
  value = found ? value + 1 : 10;
});
map.access(42, [](uint64_t& key, uint64_t& value) {
  key = 43;
  value += 5;
});
```

Typed callbacks return `void` and accept `T&`, `T&, bool`, `Key&, T&`, or
`Key&, T&, bool`. Byte callbacks use mutable `uint8_t*` buffers of the map's
configured widths instead of references. For overloaded or generic callbacks,
dispatch prefers key/value/presence, then value/presence, then key/value, then
value. Typed callbacks require default-constructible `T`; key-changing forms
also require copy-constructible `Key`. The original query key is not modified.

A key-changing signature removes the queried key and upserts the destination,
overwriting an existing destination. It follows the same schedule even if the
callback leaves the key unchanged. On successful completion, value-only callbacks use one hierarchical
access or two tree accesses; key-changing callbacks use two hierarchical
accesses or three tree accesses. Hybrid maps use their selected backend's count.
These costs include misses. Callback scratch is allocated on first use and
reused; it is adapter storage outside the engine's `byte_bill`. The
`max_accesses` horizon counts the underlying accesses, as does `access_count`.
Callbacks check their complete access cost before invoking user code. Tree
batches check the whole batch before changing position-map entries.
Tree callback updates compose a read and a later write; `exchange`
remains the one-access choice when the replacement value is already known.

Callbacks must not call into the same map, retain the supplied references or
buffers, or change them after returning. If a callback throws, logical map
contents are preserved, though the access schedule advances. A throwing callback
uses only the initial access and can therefore shorten the schedule. A
secret-dependent exception can reveal its completion outcome; the map's
obliviousness guarantee does not hide callback control flow or make these
different schedules indistinguishable. Backend failures
during restoration or commit retain the backend's usual failure contract;
multi-access updates do not promise transactional rollback. For types whose
zero bytes are not a valid value, use the presence argument before interpreting
a missing value. Callback branches and memory accesses are application code:
the presence-dependent example above reveals hit/miss in its own control flow.

### Tree map for large values

`TreeByteMap` stores values in a tree and small location records in a
hierarchical position map. The tree is binary with four-slot buckets at a
load of one half, and each access makes one pass: it reads one random path
and the stash, takes the entry out, evicts along the same path and writes it
back. The stash is three or four AVX-512 registers of 64 lanes and also holds
the top `fold` levels of the tree. `fold` and `stash_registers` default to a
rule by tree depth that keeps the path within one 16-bucket register up to
about 2^22 entries; larger trees use two. Explicit values are checked against
the stash-size requirement the rule rests on. The
[tree design](src/oram/tree/DESIGN.md#geometry-and-the-default-rule) gives the
rule, its limits, and the other geometry options (`max_folded_slots`,
`leaf_scale`, `max_load`). `capacity()` is the requested capacity, at least
128; storage doubles at each power of two.

For keys up to eight bytes, `uid_from_key` uses the complete key as its
identifier. All bit patterns are legal. The position map stores only the needed
leaf bytes; wider keys use an allocated identifier alongside the leaf.

`payload_threshold` defaults to 32 bytes and `payload_max_threads` to no
fixed cap. The worker count is `value_bytes / payload_threshold` rounded up
(none below the threshold), bounded by `payload_max_threads`, by the physical
cores left after the caller and position-map workers, and by the payload
chunks. Zero selects the single-threaded engine. Payload workers move
disjoint byte columns using the caller's one eviction plan.

Workers spin for `payload_spin_micros`, then park. The tree default is 200 us;
the hybrid uses 2000 us. Sparse workloads can pay wake-up latency. The hybrid's
threshold does not automatically change when the worker policy changes.

A tree stash overflow is fatal to the map: `failed()` becomes true and later
operations are refused; a failure of its position map is fatal in the same
way. Discard the instance and recover from data held elsewhere. The
[tree design](src/oram/tree/DESIGN.md) explains the eviction, the stash-size
procedure behind the default rule, and the diagnostic
API.

### Using the library from another C++ project

```cmake
add_subdirectory(path/to/cpu_byteslice_oram cpu_byteslice_oram-build EXCLUDE_FROM_ALL)
add_executable(my_app main.cpp)
target_link_libraries(my_app PRIVATE cpu_byteslice_oram::cpu_byteslice_oram)
target_compile_definitions(my_app PRIVATE CPU_BYTESLICE_ORAM_RELEASE)
```

The target supplies include paths, C++17, thread dependencies and compilation
flags. The flags are `-O3 -march=native`, as for this project's release tests
and benchmarks. They apply to every source of the target that links the library,
and they come after the consumer's own flags, so they override the
optimization level of a Debug build or an explicit `-O0`. Put code that must
build with other flags in a target that does not link the library. Embedding
leaves the consumer's build type alone; only a top-level configure of this
project defaults to Release.

Alternatively, install with `cmake --install build --prefix PREFIX`,
then use `find_package(cpu_byteslice_oram CONFIG REQUIRED)` in the consumer and
set `CMAKE_PREFIX_PATH` to that prefix. A complete consumer is in
[examples](examples/CMakeLists.txt). The install puts the public headers in
`PREFIX/include/cpu_byteslice_oram/` and the implementation headers, which the
public ones include as `src/...`, in `PREFIX/include/src/`. That directory name
is generic, so install into a prefix of its own rather than a shared one such
as `/usr/local`. Embedding puts the repository root on the include path for
the same reason, so a header at `src/core/...` or `src/oram/...` under one of
the consumer's own include directories shadows the library's header of that
name.

`CPU_BYTESLICE_ORAM_RELEASE` rejects incompatible test instrumentation macros
through [release_guard.hpp](src/core/release_guard.hpp). It does not disable
all runtime diagnostics or enforce the application's secrecy policy. The
instrumentation macros change class layouts, so a program must define each of
them in all of its translation units or in none; a mixed program links without
a diagnostic and is undefined.

The headers define one macro with a generic name, `INLINE` (forced inlining
of the register-only primitives), and replace an `INLINE` macro the including
code already has for the rest of that translation unit.

## Benchmarks and reproduction

Benchmarks build with `-DCPU_BYTESLICE_ORAM_BUILD=all` into `build/benchmarks/`.
This repository records no measurement results. [REPRODUCE.md](REPRODUCE.md)
maps every measured number in the paper to the campaign, driver or script that
regenerates it and to the output field that holds it.

**Map benchmark.** A quick public-API throughput check:

```sh
./build/benchmarks/cpu_byteslice_oram_map_benchmark 4096 65536
```

The arguments are entries and measured operations. The other drivers (engine
diagnostics, routing and deduplication kernels, tree studies, host
characterization, and instrumented variants) are documented with their
arguments in [benchmarks/oram](benchmarks/oram/README.md).

**Benchmark worker.** `cpu_oram_benchmark` resolves a configuration, fills and
warms it, checks responses against an exact oracle, and measures one scalar or
batched trial. Use `--help` for options.

```sh
./build/benchmarks/cpu_oram_benchmark --scheme hierarchical_incremental \
  --cores 4 --capacity 2097152 --key-bytes 8 --value-bytes 8 \
  --arrival saturated --output benchmark_results/saturated_21
```

Offered-load trials use intended arrival times, so latency includes queueing
and batch-fill delay. Service is measured per API call; response and queue times
are measured per request. `--cores` includes a reserved harness core. Runtime
library overrides use `--override.NAMESPACE.FIELD VALUE`. The
[worker contract](analysis/oram_bench/WORKER.md) defines outputs and timing,
and the [measurement design](src/oram/support/DESIGN.md) explains the timing
semantics. Saturation throughput alone does not establish an offered-load
tail bound.

**Campaign harness.** [analysis/oram_bench](analysis/oram_bench/README.md)
plans campaigns from the JSON presets in `benchmarks/campaigns`, resolves every
row with the library's resolver, checks topology, memory and TEE evidence,
runs the trials crash-safely, and reduces and plots the results.

**Baselines.** [benchmarks/baselines](benchmarks/baselines/README.md) wraps
H2O2RAM and SONIC behind the same worker interface, fetches
each at a pinned version, documents every patch, and states the comparison
rules.

**Reproduction guide.** [benchmarks/campaigns/README.md](benchmarks/campaigns/README.md)
lists the preset families, hardware and TEE requirements (Intel TDX, AMD
SEV-SNP and native controls), VM preparation, attestation checks, and the
order in which to run, resume and reduce a full reproduction.

## Ethereum MPT example

The [Ethereum MPT example](examples/ethereum_mpt/README.md) uses the library as
the private storage layer of an Ethereum state-proof service: the trie is
public, but which accounts and storage slots a client asks about is private. It
builds canonical account/storage proofs, packs public snapshots into tiered
fixed-width pages, and serves fixed-round account/storage proof batches through
real ORAM batch calls with fixed-work parsing and hashing. The local demos
cover padded proofs, mock block updates, retained roots, publication between
complete batches, stable incremental page uploads, public compaction and an
optional TLS 1.3 frame envelope. Read and update benchmarks with JSONL sweeps
accompany it. Its [design](examples/ethereum_mpt/DESIGN.md) states the security
boundary and the record format.

## Threading contract

Serialize all calls and introspection on one instance. Different instances may
be used concurrently. Internal reader epochs protect publication and retirement;
they do not make the public API safe for concurrent callers. Batches are issued
by one requester and use their own participant pool.

Owner threads drive contiguous groups of hierarchical levels. Top and bottom
helpers share rebuild lanes with their respective groups. Batch participants
are separate from rebuild owners. `worker_thread_init` runs on owners,
`deamortized_helper_thread_init` on helpers (top indices first, then bottom),
and `deamortized_batch_thread_init` on batch participants other than caller 0.
Hooks run on the workers they configure and may set affinity. Owner/helper
startup errors surface when the deferred pool starts; batch and payload pools
start during construction. A thread that has not left its hook after
`deamortized_wait_limit_millis`, and at least 120 s, ends the process: it can
be neither joined nor released.

`deamortized_wait_limit_millis` is a deadlock detector. An access waits at
most that long for a dense prefix slot. A drain waits as long as the owner
threads keep moving, and gives up after that long with no visible progress.
Either throws `std::runtime_error`; a refused access has changed nothing, and
the map stays usable.

The public adapters cap helper and payload pools against host physical cores.
Explicit owner and batch participant counts remain as requested and can
oversubscribe the host. The configuration resolver instead checks all roles
against its declared core budget; construction verifies the resulting plan.

The hierarchy's `drain_rebuilds()` finishes accepted work without waiting for
future carries. It retains valid speculative preparation and does not empty
partial levels, but waits for a phase in flight, such as a speculative top
preparation, whose length grows with the capacity. Synchronous hierarchy calls
already finish triggered rebuilds. For a tree, `drain_rebuilds()` waits for the position map and `drain_tree()`
waits for the payload workers' pending write-back. `finish_pending_work()`
waits for both.
Worker wait counters can still change while idle workers wait; they are
diagnostics, not secret occupancy measurements. The
[arena design](src/oram/levelarena/DESIGN.md#threading-rules) lists the
internal threading rules.

## Erasure

Hierarchical misses and erases create tombstones so repeated accesses do not
reveal equality by repeating older real probes. Tombstones shadow older copies
until top compaction clears those copies and omits the tombstones from its
output. Their temporary physical slots do not increase the supported live-set
capacity. See the [freshness protocol](src/oram/levelarena/DESIGN.md#online-security-and-capacity).

## Security boundary and limitations

This is research code. Storage is not encrypted or authenticated at rest;
capacity failures are observable and there is no automatic retry. The hierarchy's
capacity report is conditional on the certification's premises, and a
tree's own stash bound is not covered by that report. The observer model, the
assumptions and the full list of limitations are in
[DESIGN.md](DESIGN.md#security-boundary-and-limitations).

## Further reading

Start with [DESIGN.md](DESIGN.md), the [source index](src/DESIGN.md), the
[public configuration guide](include/cpu_byteslice_oram/CONFIGURATION.md), and
the component documentation linked above.
