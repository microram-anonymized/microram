# Reproducing the paper's numbers

This guide maps every measured number in the paper to the command that
reproduces it and the output field that holds it. The numbers come from three
kinds of runs:

| Kind | Paper items | Hardware | Section |
|---|---|---|---|
| Campaigns on the two TEE virtual machines (and their unprotected twins) | Table 1, Figures 7 and 8, the throughput, response-time, memory and TEE-overhead statements of Sections 1 and 4 | Intel TDX and AMD SEV-SNP guests with 16 physical cores | [Campaigns](#2-campaigns-table-1-figures-7-and-8) |
| Micro-benchmarks on one core or one machine | rebuild speed against H2O2RAM, routing locality, VP2INTERSECT, constant-time bounds, tables per lookup, write rate, memory latency, eviction against EnigMap, allocation against the model | the same two machine types | [Micro-benchmarks](#4-micro-benchmarks) |
| Machine-independent computations | Figure 9 and the stash numbers of Appendix A.3, the failure terms of Appendix A.4, the Lean theorems of Appendix A.2, Table 2 and the rebuild speeds of Section 2.5 | any x86-64 host with AVX-512 (Lean: any Linux host) | [Appendix A](#5-appendix-a-stash-tail-failure-terms-and-proofs) |

Paths are relative to the repository root. Everything a step writes goes to a
directory you name; nothing in the checkout changes.

## 1. Before you start

**Build.** The library, its tests, the benchmark drivers and the campaign
tools (GCC 15.2 was used for the paper; see [README.md](README.md#requirements)):

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DCPU_BYTESLICE_ORAM_BUILD=all
cmake --build build -j
ctest --test-dir build --output-on-failure
```

The baselines are fetched at pinned versions and built separately (H2O2RAM with
GCC, SONIC with Clang): [benchmarks/baselines/README.md](benchmarks/baselines/README.md#fetch-and-build).
The eviction comparison also needs EnigMap ([section 4.8](#48-eviction-against-enigmap)).

**Machines.** Intel: Google Cloud `c4-standard-32` as a TDX trust domain, and
the same machine type without TDX. AMD: Oracle `VM.Standard.E6.Flex` with 16
OCPUs and 128 GB as an SEV-SNP guest, and the same shape without SNP.
H2O2RAM's configuration search additionally needs a 256 GB SEV-SNP guest
([section 2.4](#24-baselines)). Preparing a guest (image and kernel pinning,
quieting, attestation, data volume) is described in the
[reproduction guide](benchmarks/campaigns/README.md#preparing-a-vm).

**Boot checks.** Cloud boots differ in placement and co-tenants, and the
paper's numbers were taken on good boots. On every boot, before measuring:

- **AMD SEV-SNP:** touch guest memory once (SNP's memory latency reads 274-292 ns
  before the touch and about 205 ns after it), then check that the guest has
  the whole L3. The host may cap a guest's L3 share, and `doctor` cannot see
  that, so run the check before and after every campaign or micro-benchmark
  and discard runs whose check reads CAPPED:

  ```sh
  sudo build/benchmarks/cpu_host_topology_probe --tests region --region-gib 110 --region-lines-per-page 8 --region-core 2
  python3 analysis/paper_micro.py l3-check --out checks/l3-before-<run>    # exit 0 WHOLE, 1 CAPPED, 2 error
  ```

- **Intel TDX:** the paper's runs used boots whose 15-thread streaming
  bandwidth was at least 150 GB/s and whose 32 MiB load latency was at most
  40 ns, with no other VM on the same host (routing locality used a relaxed
  130 GB/s gate, checked before and after):

  ```sh
  build/benchmarks/cpu_cache_latency_benchmark --cpu 1
  taskset -c 1-15 build/benchmarks/cpu_mem_bandwidth_benchmark --sweep 1,15 --seconds 5 --mib-per-thread 1024 --first-core 1
  ```

  The cheapest end-to-end gate is the `tee` campaign
  ([section 2.3](#23-tee-overhead)): the paper's Intel boots read at least
  1.15 M requests/s one at a time and 3.25 M in batches at 2^27.

**A local rehearsal first.** `make_presets.py --rehearsal` writes scaled,
native copies of every paper campaign (N at most 2^16, short windows,
verification on). They exercise the whole pipeline in minutes on any AVX-512
host, without a TEE. The numbers they produce are not the paper's.

```sh
python3 benchmarks/campaigns/paper/make_presets.py --rehearsal /tmp/reh --physical-cores 12
python3 -m analysis.oram_bench doctor --execution native --worker build/benchmarks/cpu_oram_benchmark \
    --require-physical-cores $(lscpu -p=CORE | grep -v '^#' | sort -u | wc -l) --output /tmp/reh/doctor.json
for n in c4-tdx-table1-scalar c4-tdx-table1-batch c4-tdx-tee c4-native-tee c4-tdx-width; do
  C=/tmp/reh/camp-$n
  python3 -m analysis.oram_bench plan --config /tmp/reh/rehearsal-$n.json --output $C
  python3 -m analysis.oram_bench resolve --campaign $C --worker build/benchmarks/cpu_oram_benchmark
  python3 -m analysis.oram_bench run --campaign $C --reducer build/analysis/oram_bench_aggregate
  python3 -m analysis.oram_bench reduce --campaign $C --reducer build/analysis/oram_bench_aggregate --output $C.reduced
done
python3 analysis/paper_numbers.py /tmp/reh/camp-*.reduced/summary.json --rehearsal --output /tmp/reh/paper-numbers
```

## 2. Campaigns: Table 1, Figures 7 and 8

### 2.1 The paper presets

[`benchmarks/campaigns/paper/`](benchmarks/campaigns/paper/README.md) holds one
campaign per machine and paper item, `<target>-<item>.json`, generated by
`make_presets.py` (`--check` confirms that the committed files match it).
Targets are `c4-tdx` (Intel TDX), `oci-zen5-snp` (AMD SEV-SNP), and, for the
TEE-overhead pair only, `c4-native` and `oci-e6-native`. Each preset carries the
configuration of the measured rows: one trial per row; counter keys (request
`k` touches key `k·S mod N` for a stride `S` coprime with `N`, see
[WORKLOAD.md](analysis/oram_bench/WORKLOAD.md)); a 1 s spin before a library
thread parks; a settle of at least `N` requests before the window
(`timing.settle_per_entry_ppm`; SONIC settles 2^21); windows of at least `N`
requests and two top-level merges; a 256 MiB event buffer (1 GiB on batch
response rows, which time every call; memory leaves it out, see
[2.5](#25-from-reduced-campaigns-to-the-papers-numbers)); and, for response times, requests or
whole batches of 64 arriving at fixed intervals at a fraction of the saturated
throughput measured first in the same campaign.

| Item | What it measures | Worker |
|---|---|---|
| `throughput-k4v8` | ours and `std::unordered_map`, 4-byte keys, 8-byte values, N = 2^16..2^30, one at a time and batches of 64 | `build/benchmarks/cpu_oram_benchmark` |
| `table1-scalar` | ours and `std::unordered_map` at 4 B/8 B 2^27, 8 B/48 B 2^25, 32 B/1 KiB 2^21: saturated, and at 0.5 (and 0.8 for ours at 4 B/8 B) of it | `cpu_oram_benchmark` |
| `table1-batch` | the same shapes with batches of 64 | `cpu_oram_benchmark` |
| `width`, `width-hierarchy-wide`, `width-std-unordered-map` | 2^20 records, 8-byte keys, values 8 B..4 KiB, one at a time | `cpu_oram_benchmark` |
| `tee` | 4 B/8 B 2^27: one at a time and batches of 64 | `cpu_oram_benchmark` |
| `baseline-h2o2ram-table`, `-throughput`, `-shipped-throughput`, `-width` (+ AMD `-width-large`) | H2O2RAM (patched; the published build for `-shipped-`) | `build-baselines/h2o2ram/bin/oram_baseline_h2o2ram` (`_shipped`) |
| `baseline-sonic-table-scalar`, `-table-batch`, `-throughput`, `-width` | SONIC's ZingORAM with a recursive position map, top limit C = 2,048; batches of 64 | `build-baselines/sonic/bin/oram_baseline_sonic` |

"Ours" is the library's default choice (`auto`): the hierarchical ORAM for 4 B
and 48 B values and the hybrid ORAM for 1 KiB values. Batches of 64 run on
eight request threads with eight lanes each (`parallel-8x8`). The resolver
then gives one request thread and 11 rebuild threads for single requests and
eight request threads and seven rebuild threads for batches at 4 B/8 B, 2^27;
the split varies with N and shape and is recorded in each campaign's
`resolution.json` (`hierarchy.owner_threads`, `top_helpers`,
`rebuild_threads_used`, `batch_participants`).

### 2.2 Running a campaign

One campaign at a time, each on an otherwise idle guest, with `C` a new
directory on the data disk (see
[A full campaign](benchmarks/campaigns/README.md#a-full-campaign) for the boot
service, interruptions and attestation):

```sh
P=c4-tdx-table1-scalar
C=/mnt/oram-bench/$P
python3 -m analysis.oram_bench plan --config benchmarks/campaigns/paper/$P.json --output $C
python3 -m analysis.oram_bench resolve --campaign $C --worker build/benchmarks/cpu_oram_benchmark
python3 -m analysis.oram_bench preflight --campaign $C --environment /mnt/oram-bench/doctor.json
sudo python3 -m analysis.oram_bench attest --campaign $C          # tdx/snp, once per boot
python3 -m analysis.oram_bench run --campaign $C --reducer build/analysis/oram_bench_aggregate
python3 -m analysis.oram_bench reduce --campaign $C --reducer build/analysis/oram_bench_aggregate --output $C.reduced
```

H2O2RAM campaigns run `prepare-h2o2ram --campaign $C --worker <h2o2ram worker>`
before `resolve`; SONIC and H2O2RAM campaigns resolve with their own workers.

Planned trial time per machine (the planner's bound, excluding the settle and
H2O2RAM's configuration search): `throughput-k4v8` 4.7 h (Intel) / 6.5 h
(AMD), `table1-scalar` 1.0 h, `table1-batch` 0.5 h, `width` 30-45 min,
`width-hierarchy-wide` 1 h, `width-std-unordered-map` 0.3 h, `tee` 0.1 h,
`baseline-h2o2ram-table` 6.7 h, `-throughput` 3.4 h, `-shipped-throughput`
1.5 h, `-width` 0.4 h, `baseline-sonic-table-scalar` 7.0 h, `-table-batch`
6.0 h, `-throughput` 12.3 h, `-width` 0.5 h. `throughput-k4v8` needs about
85 GiB at 2^30.

### 2.3 TEE overhead

Run the protected `tee` campaign, then copy its frozen worker
(`$C/build/worker`) to the unprotected VM of the same machine type and resolve
the twin campaign (`c4-native-tee`, `oci-e6-native-tee`) with that copy, on a
boot close in time. The overhead is `1 - S_protected / S_native` of the
saturated rows: one at a time (`auto`) and batches of 64 (`parallel-8x8`), on
both machines.

### 2.4 Baselines

- **H2O2RAM's configuration search** needs far more memory than its map: run
  `prepare-h2o2ram` for every `oci-zen5-snp-baseline-h2o2ram*` campaign on a
  256 GB SEV-SNP guest (the presets declare it), then copy the planner cache to
  the Intel guest, and plan the Intel width campaign on Intel:
  [Running H2O2RAM's configuration search on a large VM](benchmarks/baselines/README.md#running-h2o2rams-configuration-search-on-a-large-vm-and-reusing-it).
- **std::unordered_map and the baselines** vary between boots and VMs more
  than our map (up to 2.9x for the hash map on C4); the paper reports the
  fastest of several boots. Run those campaigns on two or more boots.
- **SONIC's own map (PMChain),** 145 requests/s with 2^20 records and batches of
  64 on AMD: `benchmarks/baselines/run_sonic_pmchain.sh`
  ([SONIC's batched map](benchmarks/baselines/README.md#sonics-batched-map-pmchain)).

### 2.5 From reduced campaigns to the paper's numbers

Copy every `$C.reduced/summary.json` to one machine (the campaign name is read
from the file), plus a few raw worker files for three statements (SONIC
without its position map, from the SONIC batch campaigns; H2O2RAM's top-level
rebuild, from the H2O2RAM table campaigns):

```sh
rsync -a --include='*/' --include='plan.json' --include='sonic_phases.json' --include='markers.csv' \
    --exclude='*' VM:$C/ raw/<campaign>/   # *-baseline-sonic-table-batch, *-baseline-sonic-throughput, *-baseline-h2o2ram-table
python3 analysis/paper_numbers.py reduced/*/summary.json \
    $(for d in raw/*; do echo --campaign $d; done) \
    --write-throughput c4-tdx=<writes/s> --write-throughput oci-zen5-snp=<writes/s> \
    --output paper-numbers
```

`paper_numbers.py` uses rows of the paper presets only (a summary of another
campaign is listed in its report and used only where no paper row exists,
flagged), selects them by candidate, shape, capacity, API, batch size and
arrival, never by campaign layout, flags any row whose settings differ from
the paper presets' (settle, key pattern, mix, verification, spin), and
writes:

| File | Contents |
|---|---|
| `table1.md`, `table1.csv` | every Table 1 cell, reproduced beside the paper's value, with the row it came from and any methodology flag |
| `fig7.csv` (+ `fig7.pdf`, `fig7.png` with matplotlib) | Figure 7: throughput against N, both machines, one at a time and batches of 64, all four systems |
| `fig8.csv` (+ figures) | Figure 8: throughput and memory over data against value size |
| `claims.md`, `claims.csv` | every derived number in the text (40: 14.3x, 0.81x, 2.9x / 6.5x, 71x / 114x, 1.18x, 67% / 2.3x, the TEE overheads, 7.1x / 4.5x, 57%, ...) with the paper's value, the reproduced value and the arithmetic |
| `rows.csv` | every row read and what it fed |

Definitions it applies:

- **Throughput** is the saturated row's drained requests per second.
- **Response time** is measured from each request's (or whole batch's)
  scheduled arrival; Avg and P99 are the fixed-rate row's mean and 99th
  percentile at 0.5 of the same campaign's saturated throughput (0.8 for the
  abstract's 1.6 / 3.4 µs).
- **Table 1 memory** excludes the benchmark's own event buffer. Among a cell's
  rows (single-request rows for ours, H2O2RAM and the hash map; batch rows for
  SONIC), it takes the one with the highest peak RSS and subtracts the event
  buffer that row holds. The worker pre-faults that buffer before the fill in
  saturated rows: 256 MiB, or 1 GiB on the batch response campaigns, which time
  every call. Half-rate rows hold none. `rows.csv` lists each row's
  `trial_peak_rss_gib`, `event_buffer_gib` and `memory_gib`. Ours' "6.5x the
  space of the keys and values" divides its cell by `N·(K+V)`. The paper
  prints the Intel cells; the AMD cells are reported beside them.
- **Figure 8(c), "less memory from 32 bytes" and "57% less at 1 KiB"** use the
  library's reserved bytes over the logical bytes for ours (fixed when a
  campaign is resolved), and peak RSS less the event buffer over logical bytes
  for the baselines.
- **Several qualifying rows** (boots, campaigns): rows that meet the
  methodology first, then the fastest.

## 3. Statements of Sections 1-4 by source

| Statement | Source |
|---|---|
| Table 1, all cells | `table1-scalar`, `table1-batch` (ours and the hash map), `baseline-h2o2ram-table`, `baseline-sonic-table-*`; `table1.csv` |
| Figure 7 | `throughput-k4v8`, `baseline-h2o2ram-throughput`, `baseline-sonic-throughput`; `fig7.csv` |
| Figure 8 | `width*`, `baseline-h2o2ram-width*`, `baseline-sonic-width`; `fig8.csv` |
| 14.3x / 81% / 0.81x, 4.6 million x, 71x, 2.3x, 7.2x (abstract, Section 1) | `claims.md` |
| 14.3-19.0x and 9.7-14.1x over H2O2RAM by N; 10x at 8 B/48 B | `claims.md` (`throughput-k4v8` and `baseline-h2o2ram-throughput`) |
| 1.18x, 28% / half, 2.9x / 6.5x, 71x / 114x, 14x without SONIC's map, 67% / 2.3x | `claims.md` |
| 4.7 M / 10.1 M writes/s; 4.0x / 12x | [section 4.5](#45-write-throughput) with `--write-throughput` |
| 1.6 / 3.4 µs at 80%; H2O2RAM's ~117 s / ~90 s top rebuild | `claims.md` (the latter from `markers.csv`) |
| 6.5x memory, 2.3x / 2.8x less; TEE overhead 10% / 39%, 5% / 4% | `claims.md` (`tee` campaigns) |
| Hybrid faster from 96 B; 7.1x / 4.5x; less memory from 32 B; 57%; 67x / 62x; 8.3x; 8.4x / 10.5x; 2.0x; 7.2x / 7.0x; about 4x | `claims.md` |
| H2O2RAM's released build at most 26% faster | `claims.md` (`baseline-h2o2ram-shipped-throughput`) |
| SONIC's PMChain, 145 requests/s | [section 2.4](#24-baselines) |
| Memory latency 205 / 150-180 / 128 ns | [section 4.6](#46-memory-latency) |
| Rebuilds 30-54x / 60-139x faster; 48.2 / 18.0 ms vs about 2.5 s | [section 4.1](#41-table-rebuild-against-h2o2ram) |
| Routing locality 3.2x | [section 4.2](#42-routing-locality) |
| VP2INTERSECT, about 1.7x | [section 4.3](#43-vp2intersect-merge) |
| Constant-time bounds 0.0030 / 0.012 cycles | [section 4.9](#49-constant-time-bounds) |
| EnigMap eviction 8.1 / 4.3 µs vs 442 / 274 µs | [section 4.8](#48-eviction-against-enigmap) |

## 4. Micro-benchmarks

`analysis/paper_micro.py SUBCOMMAND --out DIR` runs the release drivers with
the paper's arguments and prints each reproduced number beside the paper's
value; `--dry-run` prints the driver commands, `--summarize-only` reduces an
existing directory again, and `cpus` prints the CPU choices. CPUs default to
one per physical core, leaving core 0 to the system, as in the measured runs
(C4: CPU 1 for single-core runs; E6: CPU 2). The subcommands and their outputs
are described in
[benchmarks/oram/README.md](benchmarks/oram/README.md#paper-micro-benchmarks).

### 4.1 Table rebuild against H2O2RAM

```sh
python3 analysis/paper_micro.py table-rebuild --out out/table-rebuild    # needs build-baselines/h2o2ram
```

Sizes 2^10..2^24, 8- and 64-byte values, one core. The paper's ranges (30-54x
on Intel, 60-139x on AMD, 8-byte values) are the line "V8 speedup with
duplicates (H2O2RAM 64-slot / ours chain)"; the 2^20 times (48.2 / 18.0 ms
against about 2.5 s) are the "V8 2^20" lines. About 35 minutes; `--values 8
--slots 64` gives just the paper's cells in about 6.

### 4.2 Routing locality

```sh
python3 analysis/paper_micro.py routing-locality --out out/routing          # Intel
```

Eight cores, each routing its own table of 2^20 records with 8-byte values,
run twice; the paper's 3.2x is the lower of the two `route_ratio_median`
values ("lower of the runs"). About a minute; needs about 0.6 GB of huge pages.

### 4.3 VP2INTERSECT merge

Needs Zen 5 (AMD). Build a second tree with the emulation path:

```sh
cmake -S . -B build-fallback -DCMAKE_BUILD_TYPE=Release -DCPU_BYTESLICE_ORAM_BUILD=all -DCPU_BYTESLICE_ORAM_ENABLE_VP2INTERSECT=OFF
cmake --build build-fallback -j --target cpu_byteslice_level_arena_benchmark cpu_byteslice_level_arena_benchmark_compare_counted cpu_byteslice_dedup_kernel_benchmark
python3 analysis/paper_micro.py vp2intersect-merge --out out/vp2 --native-build build --fallback-build build-fallback
```

"complete merge, fallback / native" at n = 2,048, 32,768 and 1,048,576 (paper:
about 1.7x). On a CPU without VP2INTERSECT both builds use the emulation and
the tool says so.

### 4.4 Tables per lookup

```sh
python3 analysis/paper_micro.py tables-per-lookup --out out/tables
```

4 B/8 B, 2^27, B = 8, read-only: `lookup_mains_mean` of one request at a time
(paper: 6.3 Intel, 6.0 AMD; Section 4.2's "about six") and of batches of 64
(7.8, 7.1). About 8 minutes, 10 GB. The "8 MiB" of the four smallest levels
follows from the geometry the arena benchmark prints at 2^27 (fanouts
4,4,4,8,8,8, 1 KiB buckets): level 4 holds partial tables of up to 7,168
buckets and passes up carries of 8,192 buckets.

### 4.5 Write throughput

```sh
python3 analysis/paper_micro.py write-throughput --out out/write --scalar-rate <Table 1 single-request rate>
```

All writes at 4 B/8 B, 2^27, B = 8, with 14 rebuild threads pinned one per
core: "all-write rate" (paper 4.7 M Intel, 10.1 M AMD) and its ratio to the
single-request lookup rate (4.0x, 12x). Pass the rate to `paper_numbers.py
--write-throughput` too. About 2 minutes; run it on a gated boot.

### 4.6 Memory latency

```sh
python3 analysis/paper_micro.py memory-latency --out out/memlat --touch-gib 110 --sudo    # E6 (128 GB)
python3 analysis/paper_micro.py memory-latency --out out/memlat --touch-gib 96 --sudo     # C4
```

The median over physical cores of the idle DRAM load-to-use latency
(`core_dram_ns_median`): about 205 ns under SEV-SNP, 128 ns on the plain E6
VM, 150 to 180 ns under TDX. The paper's values span several boots.

### 4.7 Allocation against the model

Any AVX-512 host; the allocations are deterministic:

```sh
cmake -S . -B build-audit -DCMAKE_BUILD_TYPE=Release -DCPU_BYTESLICE_ORAM_BUILD=all -DCMAKE_CXX_FLAGS='-g -fno-pie' -DCMAKE_EXE_LINKER_FLAGS=-no-pie
cmake --build build-audit --target cpu_oram_allocation_audit
build-audit/benchmarks/cpu_oram_allocation_audit --capacities 134217728 --shapes 4:8 --schemes incremental --cores 16 --sites --accesses 0.05 > audit.txt
python3 analysis/allocation_reconcile.py audit.txt --csv audit.csv
```

"within 1% of what the model predicts" is `total_minus_main_pct_of_main`
(0.906%), equivalently `library_live_over_model_main` (1.009).

### 4.8 Eviction against EnigMap

```sh
benchmarks/baselines/fetch_enigmap.sh                    # pinned; needs libboost-dev to build
cmake -S . -B build-enigmap -DCMAKE_BUILD_TYPE=Release -DCPU_BYTESLICE_ORAM_BUILD=all -DMICRORAM_ENIGMAP_DIR=$PWD/third_party/enigmap
cmake --build build-enigmap --target cpu_tree_eviction_comparator_benchmark_enigmap
python3 analysis/paper_micro.py eviction --out out/evict --binary build-enigmap/benchmarks/cpu_tree_eviction_comparator_benchmark_enigmap
```

2^21 records, fold 4, three stash registers, 20,000 timed passes after 1,000
verified ones, three rounds with the arms in rotated order, on one core whose
SMT sibling is idle. Ours is the `read_path_transposed` arm (it includes the
transposition to and from the stored layout). At 1 KiB: 8.1 / 4.3 µs for ours,
442 / 274 µs for EnigMap (medians over rounds). About 5 minutes.

### 4.9 Constant-time bounds

On each TEE guest, follow [tests/timing/README.md](tests/timing/README.md#on-each-target)
on an idle core whose SMT sibling is idle (the measured runs used CPU 5 on C4
and CPU 4 on E6). The paper's bound (0.0030 cycles per instruction under TDX,
0.012 under SEV-SNP) is the `largest bound:` line of the `--certify` run;
`analysis/timing_summary.py` tabulates it as "max bound".

## 5. Appendix A: stash tail, failure terms and proofs

### 5.1 Figure 9 and the numbers of A.3

A deterministic CPU simulation of the tree ORAM's stash (no TEE; any machine).
[`analysis/stash_rows/paper.json`](analysis/stash_rows/paper.json) lists the
ten trees with their seeds (1,000 runs each, 3,000 for 2^27).

The paper's per-run histograms are shipped
(`analysis/stash_rows/paper_runs.tar.xz`), so Figure 9 and every A.3 number can
be recomputed in about a minute:

```sh
OUT=stash-paper        # a directory one level below the checkout's root, as the digest path below assumes
python3 analysis/run_stash_tail_long.py init $OUT --binary build/benchmarks/cpu_tree_bucket_shape_benchmark \
    --rows analysis/stash_rows/paper.json --ops 5e8
tar -xJf analysis/stash_rows/paper_runs.tar.xz -C $OUT
(cd $OUT/runs && sha256sum -c --quiet ../../analysis/stash_rows/paper_hist.sha256)
python3 analysis/run_stash_tail_long.py report $OUT
python3 analysis/run_stash_tail_long.py export $OUT $OUT/export
python3 analysis/plot_stash_tail.py $OUT/export --check-paper    # exit 0: every number present and agreeing
```

`stash_tail_summary.txt` lists each number beside the paper's: the slopes
(0.76, 0.69 bits per record), the stash sizes at 2^-95 (134, 158; and 121 /
158 / 199 for 2^21 with 0, 3 and 4 merged levels), the extrapolation to 192
slots (about 2^-118 per access, 2^-87 per 2^31 accesses), the 28 cells of
Figure 9(b), and the N sweep's worst case (below 2^-144). `tree_stash_tail.pdf`
is Figure 9. Merging m levels is fold m + 1
([tree design](src/oram/tree/DESIGN.md)).

To regenerate the histograms themselves, run the plan instead of unpacking the
archive: 12,000 single-seed runs of 5·10^8 accesses after N inserts and a
warm-up pass that reads every key once,
about 1,420 core-hours (about 60 h at 24 jobs on a 32-core Xeon; a 2^27 run
peaks at 2.6 GB):

```sh
python3 analysis/run_stash_tail_long.py start $OUT --jobs 24     # resumable; status, stop, start
```

The simulation is integer-only. To check bit-exactness against the paper's
runs in a few core-hours, run two seeds per tree and compare digests:

```sh
OUT2=stash-check
python3 analysis/run_stash_tail_long.py init $OUT2 --binary build/benchmarks/cpu_tree_bucket_shape_benchmark \
    --rows analysis/stash_rows/paper.json --ops 5e8 --max-seeds 2 --only N12-f1-rr,N15-f1-rr,N20-f3-rr
python3 analysis/run_stash_tail_long.py start $OUT2 --jobs 6
(cd $OUT2/runs && sha256sum -c --ignore-missing ../../analysis/stash_rows/paper_hist.sha256)
```

### 5.2 Failure terms of A.4 and the capacity bound of A.2

The hierarchical ORAM's overflow term and the long-key terms come from the
certification ledger and its Lean theorems (read-only, seconds):

```sh
python3 analysis/bound_certification/code/long_key_live_collision.py --check
python3 -c "import csv,math; r=list(csv.DictReader(open('analysis/bound_certification/code/long_key_live_collision_summary.csv'))); [print(c, round(math.log2(max(float(x[c]) for x in r)) - 64, 2)) for c in ('tight_overflow', 'linear_collision', 'matching', 'total')]"
python3 -c "import json,math; d=json.load(open('analysis/bound_certification/code/long_key_live_collision.json')); v=max(float(m['matching_s_min_per_access']['decimal']) for m in d['members']); print('compared records per access', round(v, 2), 'false matches per 2^31 accesses: 2^%.2f' % (math.log2(v) + 31 - 104))"
```

The maxima over all certified configurations are, in log2 per window of
`I + n = 2^31`: overflow -65.55 (the paper's "below 2^-65.5"), long-key
collisions -66.0, and false matches -66.69. The ledger charges false matches
over the full 2^32-access envelope: at most 39.76 compared records per access
(the paper's "fewer than 40"), each matching falsely with probability 2^-104.
Over the paper's 2^31 accesses that is 2^-67.69, the paper's "below 2^-67.6".
The paper's sum h·(2^-65.5 + 2^-87 + 2^-67.6 + 2^-66) is 0.686·h·2^-64, below
its 0.7·h·2^-64. The ledger's own total keeps the 2^32 false-match charge,
0.747·2^-64, and Lean proves it below 0.75·h·2^-64 over h windows
(`NativeMatchLiveWindowError`). The tree's 2^-87 comes from section 5.1. `--check` reports the certified mode `tightened_live_n`
(188/188 below the target); the `original_*` modes are the untightened
diagnostics.

The certification as a whole (Theorem 1's per-merge bounds, the generated
table the library reads) is checked read-only by
[analysis/bound_certification](analysis/bound_certification/README.md#regenerate-and-verify):

```sh
python3 analysis/bound_certification/code/regenerate.py --dry-run          # "0 producer step(s)" means current
python3 analysis/bound_certification/code/manifest.py --check
python3 analysis/bound_certification/code/export_certified_bounds.py --check
```

The Lean proofs of Appendix A.2 (Theorems 1, 3, 4 and 5 and Lemma 2) build
with `lake` as described in [lean/README.md](lean/README.md#build); the
claim-by-claim map is [LEAN_CLAIMS.md](analysis/bound_certification/LEAN_CLAIMS.md).
The replay of the implementation against the model is described in
[lean/oracle/README.md](lean/oracle/README.md).

### 5.3 Table 2

The storage-overhead column (4.5x, 2.92x, 2.41x for B = 2, 4, 8) is the
"large-L limit" of rows (B, D) = (2, 2), (4, 4), (8, 8) printed by
`python3 analysis/level_arena_model.py quick`; the allocation audit of
[section 4.7](#47-allocation-against-the-model) confirms 2.41 at 2^27.

The rebuild-speed and tables-per-lookup columns of MICRORAM's rows come from
the idealized schedule model in
[analysis/deamortization](analysis/deamortization/README.md) (standard library
only, about 20 s):

```sh
python3 analysis/deamortization/deamortization_analysis.py --summary-only
```

One row per B. `modeled_min_speed` is the rebuild speed (1, 2.5625, 5.2748 for
B = 2, 4, 8; paper 1x, 2.56x, 5.27x). `probe_overhead_at_min` times 0.5 log N
is the average number of tables per lookup (1.5, 0.77, 0.47 log N), and
`storage_over_amortized_binary` times the amortized baseline's 2x is the
storage column again. The worst-case column (2, 1, 0.67 log N) is at most two
published tables per level, 2 log_B N.

```sh
python3 analysis/deamortization/arena_coupling/layout_speeds.py
python3 analysis/deamortization/check_deamortization_closed_form.py
```

The first prints the same minimum speeds at increasing depths (about a
minute). Its `no-prerouting` speed at B = 8, 6.78 in the deepest row, is
Section 2.5's speed for merges that start only when their carry arrives. The
second checks the model's closed forms against exact recurrences and the event
simulator. The measured tables per lookup are in
[section 4.4](#44-tables-per-lookup).

The prior-work rows are checked by
[analysis/deamortization/prior_work](analysis/deamortization/prior_work/README.md)
(standard library only, about 4 s):

```sh
python3 analysis/deamortization/prior_work/check_prior_work.py
```

It checks scheduling and reserved record slots, not hash overflow or sort
cost.

- Ostrovsky and Shoup: a rebuild speed of 6x (5.99 stalls, 6 passes), and on
  average 5/6 of a table per level, so 0.83 log N (6.67 at L = 8), with a peak
  of L + 1.
- PD-ORAM: 1.5 log N tables on average and 2 log N at worst (21 and 28 at
  L = 14), and a deadline compression of 2.
- Storage: Ostrovsky and Shoup reserve 3 times the amortized baseline,
  Goodrich et al. 11/4 times and PD-ORAM about 2.5 times. That is at least 5x
  the hash table. For Goodrich et al. the script checks only the storage.

`prior_work/check_closed_form.py` checks the B-ary closed forms against a
second, independent event simulator.

## 6. Expect

- One trial per row, as in the paper. Throughput repeats within a few percent
  on one boot; boots differ by more (12-18% on C4), which is why the boot
  checks above matter. `paper_numbers.py` marks a cell `differs` when its
  rounding differs from the paper's; read its relative difference.
- The baselines and the hash map are reported as the fastest of several boots.
- SONIC runs batches of 64 everywhere. A few of the paper's SONIC batch
  points were measured with batches of 8: the 4 B / 8 B Table 1 cells and
  Figure 7(d), plus Figure 7(b) at 2^27. Batch 64 ran within 2% of batch 8 at
  2^18, 2^21 and 2^24 in interleaved local runs. `paper_numbers.py` notes
  those cells.
- The code is the released library; the paper's runs used earlier revisions
  of the same code with the same configurations.
