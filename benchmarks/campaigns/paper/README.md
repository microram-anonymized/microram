# Paper presets

One campaign per target and paper item, `<target>-<item>.json`, each named
after its file. `make_presets.py` writes all of them; edit the generator, not
the JSON:

```bash
python3 benchmarks/campaigns/paper/make_presets.py            # rewrite the presets
python3 benchmarks/campaigns/paper/make_presets.py --check    # compare with a fresh generation
python3 benchmarks/campaigns/paper/make_presets.py --rehearsal /tmp/paper-rehearsal --physical-cores 12
```

Targets: `c4-tdx` (Intel TDX, 16 cores on one L3), `oci-zen5-snp` (AMD
SEV-SNP, 16 cores on two L3 domains), and for the TEE-overhead pair only
`c4-native` and `oci-e6-native` (the same VM types without protection). An
`oci-zen5-snp` preset plans the same rows, seeds and windows as its `c4-tdx`
twin; only name, execution and resources differ. The one exception is the
std::unordered_map stages of `throughput-k4v8`, which keep each machine's own
window model: the hash map runs 2-2.6x faster on Intel at 2^30, so no single
window holds N requests on AMD and still fits the 2^32 request horizon on
Intel. A native twin differs from its protected twin only in name and
execution.

All presets run one trial per row with the settings the measured rows used:
counter keys (`workload.distribution: counter`, see
[WORKLOAD.md](../../../analysis/oram_bench/WORKLOAD.md)), a 1 s spin before a
library thread parks, verification off, a settle of at least N requests
(`timing.settle_per_entry_ppm`; SONIC settles 2^21), windows sized from the
measured rates, a 256 MiB event buffer (1 GiB with per-call service timing on
batch latency rows; `paper_numbers.py` subtracts it from memory), a checkpoint thread on fixed-rate rows, and whole batches
of 64 arriving together on batch latency rows. Response-time rows run at a
fraction of the saturated row measured first in the same campaign.

| Item | Rows | Worker | What it measures |
|---|---|---|---|
| `throughput-k4v8` | 60 | `cpu_oram_benchmark` | ours (`auto`, `parallel-8x8`) and `std_unordered_map`, K4/V8, N = 2^16..2^30, single and batch 64 |
| `table1-scalar` | 13 | `cpu_oram_benchmark` | ours and `std_unordered_map` at K4/V8 2^27, K8/V48 2^25, K32/V1024 2^21: saturated, 0.5 (and 0.8 for ours at K4/V8) |
| `table1-batch` | 12 | `cpu_oram_benchmark` | the same shapes, batches of 64 arriving together, saturated and 0.5 |
| `width` | 24 | `cpu_oram_benchmark` | `hierarchy-frozen` and `tree`, 2^20, K8, 8 B..1 KiB; `tree` at 2 and 4 KiB |
| `width-hierarchy-wide` | 2 | `cpu_oram_benchmark` | `hierarchy-frozen` at 2 and 4 KiB, 300 s windows |
| `width-std-unordered-map` | 10 | `cpu_oram_benchmark` | `std_unordered_map`, 2^20, K8, 8 B..4 KiB |
| `tee` | 2 | `cpu_oram_benchmark` | K4/V8 2^27: `auto`, `parallel-8x8` (batch 64) |
| `baseline-h2o2ram-table` | 6 | `oram_baseline_h2o2ram` | H2O2RAM at the three Table 1 shapes: saturated and 0.5 |
| `baseline-h2o2ram-throughput` | 12 | `oram_baseline_h2o2ram` | H2O2RAM, K4/V8, 2^16..2^27 |
| `baseline-h2o2ram-shipped-throughput` | 11 | `oram_baseline_h2o2ram_shipped` | published H2O2RAM, K4/V8, 2^16..2^26 |
| `baseline-h2o2ram-width` | 7 | `oram_baseline_h2o2ram` | H2O2RAM, 2^20, K8, 8..512 B |
| `baseline-h2o2ram-width-large` | 2 | `oram_baseline_h2o2ram` | AMD only: 1 and 2 KiB |
| `baseline-sonic-table-scalar` | 6 | `oram_baseline_sonic` | SONIC (recursive map, C = 2,048) at the three shapes: saturated and 0.5 |
| `baseline-sonic-table-batch` | 6 | `oram_baseline_sonic` | the same with batches of 64 arriving together |
| `baseline-sonic-throughput` | 24 | `oram_baseline_sonic` | SONIC, K4/V8, 2^16..2^27, single and batch 64 |
| `baseline-sonic-width` | 10 | `oram_baseline_sonic` | SONIC, 2^20, K8 dense, 8 B..4 KiB |

The H2O2RAM presets of `oci-zen5-snp` declare the 256 GB guest (its
configuration search needs it); their `c4-tdx` twins resolve with the planner
cache copied from that guest, except `baseline-h2o2ram-width`, which is planned
on the C4 guest in a build directory of its own.

`--rehearsal OUT` writes native copies of every preset for a check on one
development host: capacities scaled to at most 2^16, 1 s warmup, 2 s base
windows, verification on, 30 s drains, a small settle, the given core budget
and one L3 domain; candidates, seeds, models and batch policies are kept.
Rows that need 8 batch tiles need at least 10 cores.
