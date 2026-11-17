# Baseline workers

The published systems we compare against run as separately built workers that
use the repository's [single-trial protocol](../../analysis/oram_bench/WORKER.md):
the same trial loop, workload generator, correctness oracle, statistics, memory
telemetry and campaign orchestration as our own rows. The only new code on a
baseline's measured path is a thin adapter per baseline (plus, for SONIC, a
recursive position map built from its own ORAM).

| Worker | Schemes | Compiler | Source |
|---|---|---|---|
| `oram_baseline_h2o2ram` | `h2o2ram` (patched, `oblivious`) | GCC | `h2o2ram_worker.cpp` |
| `oram_baseline_h2o2ram_shipped` | `h2o2ram_shipped` (`not_oblivious`) | GCC | the same source, without `H2O2RAM_CONSTANT_TIME_CMOV` |
| `oram_baseline_sonic` | `sonic_zingoram`, `sonic_zingoram_recursive` | Clang | `sonic_worker.cpp`, `sonic_map.hpp` |

`std_unordered_map` lives in the main worker, `cpu_oram_benchmark`
([`benchmarks/oram/cpu_oram_benchmark.cpp`](../oram/cpu_oram_benchmark.cpp)).
Each worker also has an `_audit` build that links the counting global allocator
([`baseline_allocation_audit.hpp`](../support/baseline_allocation_audit.hpp))
and is never used for timing. The shared worker code is in
[`benchmarks/support/`](../support/): `baseline_worker.hpp` holds the core-slot
choice, the resolved envelope and the placement evidence for pools that place
themselves.

[`fetch_enigmap.sh`](fetch_enigmap.sh) fetches EnigMap at a pinned commit,
unpatched, for one arm of the tree-eviction microbenchmark
([`benchmarks/oram/README.md`](../oram/README.md)); it is kept apart from
`fetch.sh` so the workers' fetch record does not depend on it.
[`run_sonic_pmchain.sh`](run_sonic_pmchain.sh) builds SONIC's own demo and
runs its batched map once ([SONIC's batched map](#sonics-batched-map-pmchain)).

## The systems compared

- **H2O2RAM** (USENIX Security 2025): a hierarchical doubly oblivious RAM, the
  closest to ours in structure: a hierarchy of oblivious hash tables whose
  sizes double from level to level, under a linear-scan buffer, rebuilt by
  oblivious sorts and compaction. A *hash planner* picks each level's table
  type (linear scan, bucket hash, cuckoo hash or two-tier hash) by timing the
  candidates on the host. Rebuilds are synchronous and amortized: the access
  that finds the buffer full rebuilds first. One caller, no batch API.
- **SONIC** (USENIX Security 2026): its ORAM, ZingORAM, is a concurrent tree
  ORAM for TEEs derived from RingORAM. It runs twice: with the position map
  outside (a plain array, as SONIC's own harness and paper measure it), and
  with a recursive position map built from ZingORAM trees. SONIC's own
  oblivious map, PMChain, is not used as the store: it finds a batch's
  positions with a linear scan of the whole position map, so it serves only
  145 requests/s at 2^20 records and batches of 64
  ([SONIC's batched map](#sonics-batched-map-pmchain)).
- **`std::unordered_map`**: not oblivious. It is the ceiling, what a plain hash
  map does on the same machine, so the cost of obliviousness can be stated.

H2O2RAM and SONIC are *index ORAMs*: they address blocks by a number, like an
array, not by an arbitrary key. Every system runs inside the confidential VM
as an ordinary process, as ours does: the whole guest is the TEE. SONIC's
paper measured SGX enclaves, so here it pays no enclave transitions and no EPC
limit, which favors it. We do not reproduce the papers' own end-to-end
applications; each system is measured as a single-server store on our
workload.

## Comparison rules

Code and analysis scripts cite these rules by number.

1. **Authors' code, authors' parameters.** Each baseline runs its published
   code at the pinned version. [Patches](#patches) lists every change; each
   is a few lines, and none changes the access or rebuild algorithm. A
   baseline runs with its paper's parameters or its code's defaults, and may
   also be given tuned parameters through `--override.<baseline>.*`.
2. **Maintenance included.** Every configuration performs its own maintenance
   (rebuilds, evictions) inside the measured window. SONIC's online-only
   configuration, which defers all evictions to an offline phase, is not run.
3. **One core budget.** Every thread a baseline starts counts against the
   same library slots as our rows; the harness keeps its own reserved core. No
   SMT siblings.
4. **Same requests; each index ORAM gets an index.** Every backend receives
   the same key bytes. An index ORAM's adapter turns them into an index
   ([`h2o2ram_index.hpp`](h2o2ram_index.hpp)):
   - **4-byte keys, dense layout** (`--key-layout dense`: key i is the
     little-endian integer i < N). Both index ORAMs use the key's value. Our
     map hashes keys with a keyed PRF, so the layout does not change its cost.
   - **8-byte permuted keys, H2O2RAM only.** The key with bit 63 (H2O2RAM's
     dummy flag) cleared. This is injective on the generator's keys: an 8-byte
     key is an odd affine map of the key ID modulo 2^64, so two keys agree
     below bit 63 only if their IDs differ by a multiple of 2^63.
   - **Wider keys, H2O2RAM only.** A keyed AES-CMAC of the key truncated to 63
     bits, the cryptographic hash H2O2RAM's paper asks for. H2O2RAM does not
     build with a 16-byte index, and it stores no key, so two keys with one
     digest would share a block: before the trial the adapter counts the fill
     keys' digest collisions and fails a row that has one rather than measure
     an aliased map.
   - SONIC needs dense indices in `[0, N)`, so it runs only dense keys.
5. **Values.** H2O2RAM stores any value width, ZingORAM any multiple of
   8 bytes. Rows carry `stored_value_bytes`, and memory is billed at that size
   plus each block's own header.
6. **Hits only.** Neither index ORAM can report a miss (SONIC has no block at
   or above N; H2O2RAM returns an uninitialized value for a missing index), so
   miss workloads are skipped for them, with a persisted reason.
7. **Correctness by the same oracle.** Rows run with `--verification full` by
   default, which checks the adapters and the baselines. Every baseline can
   return a write's old value, so the batch contract holds unchanged.
8. **Security labels.** Every row carries one: `oblivious` (ours,
   `sonic_zingoram_recursive`, `h2o2ram`),
   `oblivious_position_map_outside` (`sonic_zingoram`), or `not_oblivious`
   (`std_unordered_map`; `h2o2ram_shipped`, whose lookups
   [branch on the secret](#h2o2rams-lookups-branch-on-the-secret)). Plots
   print the label beside each series, and only `oblivious` rows are drawn as
   like-for-like competitors.
9. **Failure targets as published.** Ours is capacity failure at most 2^-64
   over 2^32 requests ([DESIGN.md](../../DESIGN.md)); SONIC's stash overflow is
   2^-80 per tree, so (L + 1) · 2^-80 for the recursive scheme with L map
   trees; H2O2RAM's δ is 2^-64. Each runs at its own target; none is retuned.
10. **No automatic selection.** `--scheme auto` never resolves to a baseline.
11. **A time cap per arm.** A trial's time grows with N, so each baseline
    arm's N sweep stops at the largest N whose estimated trial time fits the
    campaign's per-trial cap. The estimates are `trial_time` models fitted
    from pilot campaigns (`oram_bench fit-trial-time`;
    [`analysis/oram_bench/README.md`](../../analysis/oram_bench/README.md));
    rows above the cap are skipped as `trial_time_cap`.

## Host packages

- g++ (C++20);
- Clang, CMake and Ninja;
- `libtbb-dev`, `libnlopt-dev` and `libssl-dev`;
- git, curl, patch and python3 for `fetch.sh`;
- `libboost-dev` for the EnigMap arm of the tree-eviction comparator (its
  sources include `boost/stacktrace.hpp`), which the main build compiles
  against `fetch_enigmap.sh`'s checkout.

GTest and google-benchmark, which H2O2RAM's CMake also wants, are not needed.
Every baseline is built `-march=native` (see Builds below). H2O2RAM and SONIC
also turn AVX-512 on explicitly, so the CPU must have it.

**The paper's toolchain.** Both measured guests ran Ubuntu 26.04 with g++
15.2.0 (our library, our workers and H2O2RAM), Clang 21.1.8 (SONIC, whose CMake
accepts only Clang), CMake 4.2.3 and `libtbb-dev` 2022.3.0-2. Each baseline
worker's `--build-info` prints the toolchain versions that `fetch.sh` recorded
on the build host (`fetch_record.toolchain`), and `resolve` stores that output
in the campaign's `build/build.json`, so a reproduction can compare its
toolchain with these.

## Fetch and build

```sh
benchmarks/baselines/fetch.sh     # third_party/baselines: pinned sources, hashes checked, patches applied
CXX=g++ cmake -S benchmarks/baselines -B build-baselines/h2o2ram -G Ninja -DBASELINE=h2o2ram
cmake --build build-baselines/h2o2ram
CC=clang CXX=clang++ cmake -S benchmarks/baselines -B build-baselines/sonic -G Ninja -DBASELINE=sonic \
    -DCMAKE_BUILD_TYPE=Release
cmake --build build-baselines/sonic
ctest --test-dir build-baselines/h2o2ram --output-on-failure
ctest --test-dir build-baselines/sonic --output-on-failure
```

**Pinning.** [`fetch.sh`](fetch.sh) always downloads fresh copies:

| Baseline | Source | Pin |
|---|---|---|
| H2O2RAM | `github.com/55199789/H2O2RAM` (MIT) | commit `906eb97…`, plus a SHA-256 over the sorted per-file hashes of the tree |
| SONIC | Zenodo record 20646913, the USENIX Security 2026 artifact tarball (CC-BY 4.0); there is no public repository | the tarball's MD5 and SHA-256, and the tree hash after extraction |

It fails on any hash mismatch or on a patch that does not apply, and replaces
the destination only after every check passes. Each worker embeds the
resulting `fetch_record.json` (sources, the patched trees' hashes, each patch
file's hash and the toolchain versions) through `fetch_record.hpp.in`, so its
binary hash covers them; `--build-info` prints the record.

**Builds.** Each baseline is compiled with its own release flags
([`CMakeLists.txt`](CMakeLists.txt) reproduces them): H2O2RAM with GCC,
`-O3 -march=native` and AVX-512 already on, TBB and OpenMP; SONIC with Clang
in Release (its CMake refuses GCC), with its optional `SONIC_ENABLE_AVX512`
turned on, which compiles 512-bit loops into its constant-time set, select and
swap primitives and aligns blocks to 64 bytes (the artifact's default is off).
If Clang selects an incomplete GCC
installation, supply `--gcc-install-dir` for an installed libstdc++ toolchain
through `CMAKE_CXX_FLAGS` and `CMAKE_C_FLAGS`.

Both H2O2RAM binaries use the frozen planner and the shared layout and
extraction fixes. The patched binary also enables constant-time moves and
fresh dummy lookups; the comparison binary keeps its `not_oblivious` label.

## Patches

Patch files live in [`patches/`](patches/). `fetch.sh` applies them, in the
order below, after the checksum check, and the fetch record lists each one
with its hash. The patch files carry no headers, only the diff hunks.

| ID | Builds | Change | Why |
|---|---|---|---|
| P-H1 | both | Planner prints go to stderr instead of stdout. | Harness: stdout is the worker's JSON channel. |
| P-H2 | both (under `H2O2RAM_FROZEN_PLANNER`) | A planner-cache miss throws instead of timing candidates; a preparing process clears the flag to write the cache. | Harness and fairness: no host-timing sweep runs inside a measured process, and the configuration is frozen when a campaign is resolved. |
| P-H3 | `h2o2ram` only (under `H2O2RAM_CONSTANT_TIME_CMOV`) | The generic `CMOV` template selects in constant time, as `T tmp = val2; obliSwap(val1, tmp, cond);` with H2O2RAM's own `obliSwap` (declared before the template so non-class types find it). The two-tier table's branch on whether the overflow bin had the key becomes one major-bin lookup whose key is chosen by `CMOV`. | Constant time: the shipped generic `CMOV` is `if (cond) val1 = val2;`, and every block selection in a lookup uses it ([below](#h2o2rams-lookups-branch-on-the-secret)). |
| P-H4 | both | The constructors merge a linear-scan table into the buffer only while no table has been kept, and the buffer is the smallest kept level. | Correctness: the host-timed planner's plan need not be monotone; a linear-scan level above a kept table left a kept level smaller than the buffer, and rebuilds (which copy level i to offset buffer × 2^i) dropped blocks. |
| P-H5 | `h2o2ram` only (under P-H3's flag) | Bucket and cuckoo lookups remap the dummy index -1 to a fresh dummy ID, as the two-tier table already does. | Obliviousness of the access pattern: every dummy lookup of an epoch probed index -1's one fixed place, so the pattern showed at which level a block was found. |
| P-H6 | both | `OTwoTierHash::extract`: cast the PRF output to `KeyType`, and restart the per-bin count at a new bin (`!=` instead of `==`). | Correctness: the call bound to `oblivious_select`'s `bool` overload (every overflow block went to bin 0 or 1), and the count never capped a bin, so every rebuild of a two-tier level could drop blocks. |
| P-H7 | both | `getExecutablePath` terminates the `readlink` result and scans from its last byte. | Correctness: `readlink` does not terminate the path; a stale `/` past its end made the planner cache's folder the executable's own path, and the cache files failed to open. |
| P-S1 | SONIC | `zingoram::state::prng()` returns a `thread_local`, self-seeded `buffered_prng` instead of the tree's one shared generator, and `rebuild_subtrees` calls `st.prng()` inside each eviction worker. | Correctness: concurrent accesses and the eviction team rebuild buckets on several threads at once, and the shared generator (a buffer plus an OpenSSL AES-CTR context) has no lock. ThreadSanitizer on [`tests/sonic_stress.cpp`](tests/sonic_stress.cpp) shows the race in `buffered_prng::random_bytes`; it corrupts the generator, and long runs die in `EVP_EncryptInit_ex`. |

So `h2o2ram_shipped` is the published code with the correctness fixes (P-H4,
P-H6, P-H7) and the harness patches (P-H1, P-H2): it still has the
secret-dependent branches and passes verification. `h2o2ram` adds the security
fixes (P-H3, P-H5). The pair measures what the branches buy. The tests check
the patches against the pinned code: `h2o2ram_layout_test` (P-H4, P-H5, P-H6),
`h2o2ram_index_test` (P-H2) and the branch census (P-H3).

## How each baseline is wrapped

Each adapter implements the backend interface that `ExecuteWorker`
([`benchmarks/support/worker.hpp`](../support/worker.hpp)) drives: `Fill`,
`Find`, `Write`, `Batch` and `Finish`, plus `AccessCount` and `Markers` where
maintenance coverage applies; [`fake_backend.hpp`](../support/fake_backend.hpp)
is the model.

**Threads and placement.** None of the baselines takes our thread-start hook:
TBB, OpenMP and SONIC start their own pools. So a worker restricts the
process's allowed CPUs to the library slots before any pool starts (threads
inherit the mask), starts the pools, and then puts the caller on its own slot.
`placement.json` comes from scanning `/proc/self/task/*/status` and `stat`
after construction and after warmup (`placement_policy` =
`baseline_self_placed`); a thread outside the library slots fails the trial.
libgomp reads its environment before `main`, so the OpenMP workers re-execute
themselves once with the wanted `OMP_*` variables set and every binding
variable cleared.

### H2O2RAM

- **Map.** `ORAM::ObliviousRAM<uint64_t, Value<V>>` with the index of rule 4.
  `Find` reads `oram[index]` and copies the value out; `Write` reads the old
  value through the returned reference and assigns the new one, the same
  oblivious access. Value widths are compile-time and dispatched at run time.
- **Fill.** Dense keys use the range constructor (direct initialization; key i
  is index i). Sparse keys are `insert`ed in key-ID order, as H2O2RAM's own map
  benchmark fills its map; with digest indices the collision check of rule 4
  runs first.
- **Threads.** TBB and OpenMP get every library slot.
  `--override.h2o2ram.omp_wait_policy active|passive` sets libgomp's idle
  policy, and `h2o2ram.linear_scan_threshold` (128, the authors' default, or
  256, their large-block setting) the buffer size.
- **Maintenance.** Level i below the top is rebuilt every buffer × 2^(i+1)
  appends and the top every capacity appends; the worker reports these
  periods so the reducer can check that the window covers whole rebuild
  cycles. H2O2RAM has no rebuild events, so the marker span of a rebuild is
  the whole access that starts it.
- **Rebuild spans.** Every trial writes these spans to
  `<attempt>/worker/markers.csv` (`role,level,start_ns,end_ns` on the trial
  clock, role `h2o2ram_rebuild`, level min(ctz(k), top) for the k-th rebuild,
  0 the smallest kept level), histogram-checkpoint rows included. The spans at
  the file's largest level are the top-level rebuilds, each inside one access
  while later requests queue: they are the source of the paper's "about 117 s
  on Intel and 90 s on AMD", read from the K4/V8 2^27 rows of the
  `*-baseline-h2o2ram-table` campaigns (each window holds two; the measured
  half-rate rows' maximum responses were 117.4 s and 88.9 s).
  `analysis/paper_numbers.py --campaign DIR` reports them per row.
- **Bucket placement alone.** [`h2o2ram_routing_bench.cpp`](h2o2ram_routing_bench.cpp)
  times H2O2RAM's `OHashBucket::build` by itself on the table shapes of our
  `cpu_byteslice_stash_rebuild_benchmark`; its arguments are described in
  [benchmarks/oram/README.md](../oram/README.md) next to that benchmark. Its
  single-thread 64-slot rows are the H2O2RAM side of the paper's table-rebuild
  comparison (`analysis/paper_micro.py table-rebuild`).

### H2O2RAM's planner cache

H2O2RAM picks each level's table type by timing candidates on the host. It
caches its choices in `hash_map.bin<block bytes>` beside the executable
(`build-baselines/h2o2ram/bin/`), which both builds share. The shipped build
uses the patched build's choices.

1. `oram_bench plan`, then
   `oram_bench prepare-h2o2ram --campaign DIR --worker build-baselines/h2o2ram/bin/oram_baseline_h2o2ram`,
   on the target. It runs the rows smallest first and records each row's
   planner time and peak RSS in `DIR/prepare_h2o2ram.json`. A row that fails
   (the child is capped at the campaign's memory headroom) or outlives
   `--timeout` stops only the larger rows of its block size.
2. `oram_bench resolve` with the campaign's own worker (next section). It
   copies the cache from beside that worker into the campaign's `build/`,
   hashes it into `build.json`, and refuses a later resolve with a different
   cache.

For a `*-baseline-h2o2ram-shipped*` campaign, step 1 still takes the patched
worker, `oram_baseline_h2o2ram` (it prepares every row under the `h2o2ram`
scheme), and step 2 takes `oram_baseline_h2o2ram_shipped`, which reads the same
cache from the shared `bin/`.

Inside a trial a cache miss is an error (P-H2), so no planner timing sweep runs
in a measured process.

#### Running H2O2RAM's configuration search on a large VM and reusing it

The configuration search needs far more memory than the map it configures.
Its peak RSS was 115 GiB for 4-byte keys and 8-byte values at 2^27 records,
166 GiB for 8-byte keys and 48-byte values at 2^25, and more than 186 GiB for
32-byte keys and 1 KiB values at 2^21, while the trials themselves need 20 to
36 GiB. `prepare-h2o2ram` caps each planner child's address space at the
campaign's `host_memory_limit_bytes` less `headroom_ppm` (default 20%), 94 to
100 GiB on the 128 GB guests, so a search that outgrows it fails with
`bad_alloc`. The paper therefore ran every H2O2RAM search for Table 1 and
Figures 7 and 8 on a 256 GB AMD SEV-SNP guest that is otherwise identical to
the AMD trial VM, and the Intel runs reuse its results:

1. **On the 256 GB AMD guest** (its `MemTotal` is 269,766,885,376 B), fetch,
   build and `ctest` both baseline builds as above. Every
   `oci-zen5-snp-baseline-h2o2ram*` preset in
   [`benchmarks/campaigns/paper/`](../campaigns/paper/) declares this guest:
   `resources.host_memory_limit_bytes` 269766885376 and `headroom_ppm` 50000
   (5%, so a planner child may use about 239 GiB). `plan` and
   `prepare-h2o2ram` every H2O2RAM campaign of a block size before resolving
   any of them (a campaign freezes the cache as it is when resolved, and the
   width campaigns share `hash_map.bin16` and `bin1032` with the Table 1
   shapes), then resolve and run the AMD H2O2RAM trials on this guest.
   The searches the paper ran, as `prepare_h2o2ram.json` reports them
   (`wall_ns`, `peak_rss_bytes`; each row times only the levels the cache
   lacks):

   | Block (`hash_map.bin<8 + V>`) | Rows | Planner time | Peak RSS |
   |---|---|---|---|
   | 16 B (K4/V8; also K8/V8) | 2^15..2^26, then 2^27 | 8.8 h, then 12.1 h | 115 GiB at 2^27 |
   | 56 B (K8/V48) | 2^25, from an empty cache | 7.1 h | 166 GiB |
   | 1032 B (K32/V1024) | 2^21 | 4.7 h until `bad_alloc` at 186 GiB under the default 20% headroom, then 1.2 h more at 5% (the cached levels were kept) | over 186 GiB |
   | 2056 B (K8/V2048, Figure 8) | 2^20 | 5.6 h | 206 GiB |

2. **Copy the caches.** After the Intel guest's own `ctest`, copy
   `hash_map.bin16`, `hash_map.bin56` and `hash_map.bin1032` from the AMD
   guest's `build-baselines/h2o2ram/bin/` into the Intel guest's, overwriting
   the files there. The order matters: on a fresh build the census test
   creates these files and appends Intel-timed entries for any 2^16-record
   row they lack, so only a copy made after it leaves files byte-identical to
   AMD's. The `hash_time.bin*` files are timing logs that nothing reads.
3. **On the Intel guest**, `plan` and `prepare-h2o2ram` the
   `c4-tdx-baseline-h2o2ram-table`, `-throughput` and `-shipped-throughput`
   campaigns: every level is cached, so each row's planner time is a few
   seconds (the paper's runs took 3.5 s at 16-byte and 10 s at 1032-byte
   blocks). `resolve` then freezes every `hash_map.bin*` beside the worker
   into `$C/build/` and records it in `$C/build/build.json` under
   `side_files` (`name`, `sha256`, `bytes`). Compare those hashes with the AMD
   campaigns' `build.json`; the three files must match:

   ```sh
   python3 -c 'import json,sys; [print(f["name"], f["sha256"]) for f in json.load(open(sys.argv[1]))["side_files"]]' $C/build/build.json
   ```

4. **Intel Figure 8 is planned on Intel.** The platforms' plans differ: at
   2^20 records, 11 to 23 of a plan's 34 sub-tables differ between the two
   machines at each value size. Since 8-byte keys with 8-byte values also use
   16-byte blocks, they would find AMD's `hash_map.bin16`. So
   `c4-tdx-baseline-h2o2ram-width` uses a separate build directory,
   `build-baselines/h2o2ram-intel` (configured and tested as above, with no
   copied caches), whose worker prepares and resolves it on the Intel guest.
   Its searches fit the 128 GB guest up to 512-byte values (172 s at 8 B,
   3,914 s and 41 GiB at 512 B); the 1 KiB search, predicted at about 103 GiB,
   does not, so the paper's Intel curve stops at 512 B.

### Which worker each campaign resolves with

`resolve` freezes the worker it is given, so a baseline campaign passes its
baseline's worker instead of `build/benchmarks/cpu_oram_benchmark`; every other
step is as in
[Running a campaign](../campaigns/README.md#running-a-campaign):

```sh
# *-baseline-h2o2ram*  (patched, `oblivious`)
python3 -m analysis.oram_bench prepare-h2o2ram --campaign $C --worker build-baselines/h2o2ram/bin/oram_baseline_h2o2ram
python3 -m analysis.oram_bench resolve --campaign $C --worker build-baselines/h2o2ram/bin/oram_baseline_h2o2ram
# *-baseline-h2o2ram-shipped*  (`not_oblivious`)
python3 -m analysis.oram_bench prepare-h2o2ram --campaign $C --worker build-baselines/h2o2ram/bin/oram_baseline_h2o2ram
python3 -m analysis.oram_bench resolve --campaign $C --worker build-baselines/h2o2ram/bin/oram_baseline_h2o2ram_shipped
# *-baseline-sonic*
python3 -m analysis.oram_bench resolve --campaign $C --worker build-baselines/sonic/bin/oram_baseline_sonic
```

`*-baseline-std-unordered-map*` resolves with the main worker,
`build/benchmarks/cpu_oram_benchmark`.

### SONIC ZingORAM, with and without a position map

ZingORAM's `access` takes each block's current and new leaf, so the caller
keeps the position map, and a *mutator* that the ORAM applies to the block in
place, so one access can read and modify a block. Concurrent accesses must
target distinct blocks: if one block is accessed twice in flight, the second
access looks for it on its new path before the first has put it in the stash,
and the block is lost. [`sonic_map.hpp`](sonic_map.hpp) builds the map:

- **`sonic_zingoram`**: the position map is a plain array in the adapter, as in
  SONIC's harness. Label `oblivious_position_map_outside`.
- **`sonic_zingoram_recursive`**: map level i (1 ≤ i ≤ L) is a ZingORAM tree
  whose block j holds the 4-byte leaf labels of blocks j·b … j·b+b−1 of level
  i−1 (level 0 is the data tree; b is the branching factor). L is the smallest
  level count with ⌈N / b^L⌉ ≤ C, and the *top map* of at most C labels is an
  array scanned in full with SONIC's constant-time selects. An access walks the
  top map, the map trees from level L down, and the data tree, replacing each
  label it reads with a fresh one from SONIC's CSPRNG; every access touches all
  L + 1 trees and the whole top array, whatever the key. This construction is
  ours, built from SONIC's code. Label `oblivious`.
- **Windows.** Requests run in windows of W lanes (W = 1 for scalar calls, T
  access threads for batches), one tree at a time, top first. Lanes whose keys
  share a block in a tree form a run: the run's first lane (its
  *representative*) accesses the block, and the others access a dummy address
  on a fresh random leaf, so W accesses always run, on distinct blocks. Every
  access runs the same mutator over all W lanes with masked writes, so the
  instruction trace does not depend on the duplicates. The data round follows
  the batch contract: a read returns the latest earlier write of its run (or
  the value before the window), a write returns the value before it.
- **Parameters.** The paper's configurations: Ser (T=1, Z=8, S=12, R=3, E=1)
  for scalar rows and Par8 (T=8, Z=16, S=16, R=3, E=2) for batch rows, where Z
  and S are the real and dummy slots per bucket, R the routing depth (2^R
  eviction subtrees) and E the eviction batch. Map trees default to the data
  tree's parameters, with b = 16 and C = 2^11 = 2,048 (`map_top_entries`), so
  the top array holds 256 to 2,048 labels when N is a power of two. Every
  SONIC number in the paper used C = 2,048, and the paper presets also set it
  explicitly. With C = 4,096 the top array reaches 4,096 labels at 2^16, 2^20
  and 2^24, where SONIC ran 1.25 to 1.9x below its trend; a smaller limit
  leaves the last map tree with 64 or 128 blocks at some N, which SONIC's
  8-thread batch mode refuses (`evictslots_per_path must be positive`). For a
  power-of-two N, C = 2,048 and 4,096 build different maps only when N is
  2^12 times a power of 16 (2^16, 2^20, 2^24, 2^28), so the Table 1 sizes
  (2^21, 2^25, 2^27) do not depend on it. `--override.sonic.*` replaces any
  of them (`bucket_real_size`, `bucket_dummy_size`, `eviction_rate`,
  `evict_batch`, `routing_depth`, `access_threads`, `eviction_threads`, and the
  `map_*` fields of the recursive scheme). The stash bound always follows from
  SONIC's own analysis for a 2^-80 overflow probability. A tree of at most A/2
  blocks has no ZingORAM height, so the worker refuses a row that gives one,
  such as a `map_top_entries` or `map_branching_factor` that leaves the last
  map tree that small.
- **Fill.** ZingORAM starts empty, and a block comes into existence on its
  first access, so the fill is N writes through the full path in key order (a
  public order).
- **Threads.** SONIC's pools take one physical core per thread from the
  calling thread's allowed set and refuse to oversubscribe; all trees share
  one eviction pool.
- **Phase times.** The engine times each window's two parts on the calling
  thread, the position map (top scan and map trees; for `sonic_zingoram`, the
  plain array) and the data tree, and every trial writes them to
  `<attempt>/worker/sonic_phases.json` (`fill` and `after_fill`, each with
  `windows`, `accesses`, `map_ns` and `data_ns`; `after_fill` covers warmup,
  settle, measurement, drain and the final verification). The paper's
  position-map share is `map_ns / (map_ns + data_ns)` and its "SONIC's
  position map not counted" throughput is `accesses × 10^9 / data_ns`, both
  from `after_fill` of the saturated batch-64 rows: the K4/V8 2^27 row for
  "still 14x faster on Intel", the 8-byte-key, 1 KiB-value 2^21 row for
  "about 4x faster" at 1 KiB. `analysis/paper_numbers.py --campaign DIR`
  reads the file.

### SONIC's batched map, PMChain

SONIC's own oblivious map, PMChain (`sonic_omap`'s `pmchain`), keeps each
key's (address, counter) pair in a position map of N entries. To serve a
batch it builds an oblivious two-tier hash table on the batch's requests and
then passes every one of the N position-map entries through it
(`execute_o2th_chains`): each batch is a linear scan of the whole position
map, so a batch's cost grows with N whatever its size. With 2^20 records and
batches of 64 that stage takes over 99.9% of each batch, and PMChain serves
145 requests/s on the AMD machine (48,694 requests/s with batches of 4,096).
We therefore run SONIC's ORAM, ZingORAM, with dense keys 0..N−1 and give it a
recursive position map built from the same ORAM's trees in place of the scan
(above).

[`run_sonic_pmchain.sh`](run_sonic_pmchain.sh) reproduces the 145 requests/s.
It builds SONIC's demo, `sonic_demo`, from `third_party/baselines/sonic/sonic`
(the patched tree that `fetch.sh` writes) in its own build directory with
Clang, in Release, with `SONIC_BUILD_APPLICATIONS` and `SONIC_ENABLE_AVX512`
on, and runs
`sonic_demo pmchain experiment -N 1048576 -m 64 -B 16 -Z 16 -S 16 -R 3 --evict-batch 2 -W 8 --evict-threads 8 --batches 256 --write-ratio 0.05`:
16-byte blocks, the data tree of our Par8 batch rows, 5% writes and 256
batches (one batch takes about 0.44 s at 2^20, so the run takes two
minutes). The paper's number is the summary's `throughput: ... online=`
value, which the script prints last:

```sh
benchmarks/baselines/run_sonic_pmchain.sh                 # N = 2^20, batch 64, 256 batches
benchmarks/baselines/run_sonic_pmchain.sh 65536 64 16     # a quick check
```

N, the batch size (a multiple of 64, PMChain's position-map bucket) and the
batch count are its arguments; `BUILD_DIR`, `SONIC_DIR`, `ACCESS_WORKERS`,
`EVICT_THREADS`, `TIMEOUT` and `SKIP_BUILD=1` are read from the environment.
At 2^20 the paper's run kept 8 cores busy and peaked at 0.29 GiB.

**Duplicate keys in a batch.** SONIC's paper describes deduplicating the
requests of a batch before they reach the ORAM, but the artifact does not
implement it: PMChain's `populate_requests` takes the batch as given, its own
experiment driver issues consecutive keys, and concurrent ZingORAM accesses
must target distinct blocks (above). The paper therefore assumes that the
requests of a batch are already distinct. The paper's campaigns satisfy this:
with the counter key pattern (`workload.distribution` `counter`, the worker's
`--key-pattern counter`), request k touches key k·S mod N for a stride S
coprime with N, so any N consecutive requests, and so every batch of 64,
touch distinct keys. Our adapter does not depend on it: lanes whose keys
share a block in any tree, the data tree or a map tree, become one
representative access and dummy accesses on fresh random leaves, with an
instruction trace independent of the duplicates (Windows, above);
[`tests/sonic_recursive_map_test.cpp`](tests/sonic_recursive_map_test.cpp)
checks windows whose lanes all share one key, or one map block, against a
reference map.

## Security notes on the baselines

These observations explain the patches and the row labels; the tests
reproduce each one against the pinned sources.

### H2O2RAM's lookups branch on the secret

`CMOV` in H2O2RAM's `oblivious_operations.hpp` has constant-time
specializations (inline-asm `cmovnz`) for integer types only; the generic
template is `if (cond) val1 = val2;`. Every lookup selects the matching
*block*, a struct, with it: the buffer scan and the per-level result in
`oram.hpp`, and the linear-scan, bucket and cuckoo tables. Compiled with the
authors' flags, the buffer scan compares each entry's ID and jumps, loading the
value only on a match, and after each level's lookup the code branches on
whether the block was already found. An adversary who sees the instruction
trace (branch-predictor or single-stepping attacks) therefore learns whether
and where the requested block sits in the buffer and at which level it was
found, that is, how recently it was last accessed; for blocks longer than a
cache line, even the cache-line access pattern shows it. The two-tier table's
lookup also branches on whether the overflow bin held the key. The shipped
code is consequently faster than an oblivious one, most of all at large values,
so the like-for-like rows use the patched build (P-H3, P-H5), and the shipped
build runs beside it as `not_oblivious`.

[`tests/h2o2ram_trace_census.cpp`](tests/h2o2ram_trace_census.cpp) and
[`tests/check_h2o2ram_census.py`](tests/check_h2o2ram_census.py) check this by
single-stepping one lookup per target block in forked children and comparing
the executable's instruction traces: the patched build must give one trace for
every target, and the shipped build's traces must depart at the generic
`CMOV`'s branch. Library code (glibc `memcpy`) is left out of the traces; its
loop counts follow the probed bucket's position, which the access pattern
already shows.

### H2O2RAM's map truncates keys to 63 bits

H2O2RAM's `ObliviousMap<K, V>` (its `omap.hpp`) indexes the ORAM by
`std::hash<K>{}(key)` with the top bit cleared and stores the index, not the
key, so two keys whose hashes agree in those 63 bits silently share one block.
With n random keys the collision probability is about 1 − exp(−n² / 2^64)
(about 2^-10 at 2^27 keys, 63% at 2^32); meeting H2O2RAM's own δ = 2^-64 at
2^32 keys needs a digest of at least 127 bits, or the full key stored and
compared. Because `std::hash` is unkeyed, colliding keys can also be found
offline with a generic search of about 2^32 hash calls;
[`tests/h2o2ram_omap_collision_test.cpp`](tests/h2o2ram_omap_collision_test.cpp)
shows one such pair aliasing in the pinned code. Our adapter does not use
`ObliviousMap`: it passes H2O2RAM a keyed 63-bit digest and refuses fill sets
with a collision (rule 4).
