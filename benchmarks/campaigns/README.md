# Reproducing the experiments

This directory holds the campaign presets for the paper's experiments and
this guide to running them. A *campaign* is one JSON preset expanded into a
fixed matrix of single trials (scheme, shape, capacity, API mode, batch size,
offered rate, seed). The harness in [analysis/oram_bench](../../analysis/oram_bench/README.md)
plans the matrix, freezes the worker binary, runs every trial in its own
process, survives reboots and preemptions, and reduces the committed raw
output into per-repetition summaries and plots. The worker contract, output
files and timing rules are in [WORKER.md](../../analysis/oram_bench/WORKER.md).

**The paper's numbers.** The campaigns that reproduce the paper's tables and
figures, with the exact configuration of the measured rows (counter keys, a
1 s spin before parking, a settle of at least N requests, eight request
threads per batch of 64, whole batches arriving together), are in
[paper/](paper/README.md). [REPRODUCE.md](../../REPRODUCE.md) maps every
measured number in the paper to its campaign, driver or script. The
top-level presets below are wider sweeps with the library's default
settings: use them to explore, and the `paper/` presets to reproduce.

Terms used below:

- **ours**: the library's schemes, selected by the candidate's `scheme`
  override: `hierarchical_incremental` (the byte-sliced hierarchical ORAM),
  `tree` (the tree ORAM for large values) and `auto` (the library default,
  which picks one of the two by value width; see
  [default_rule.hpp](../../include/cpu_byteslice_oram/default_rule.hpp)).
- **shape**: key and value width. The three paper shapes are named in the
  presets: `standard-provisional-k4-v8` (the standard ORAM benchmark shape:
  4-byte dense keys, 8-byte values, written H or K4/V8 below; the name is a
  fixed identifier that the tests match on, and the shape is final), `signal-sized` (K8/V48) and `ethereum-mpt-sized`
  (K32/V1024, the size of an Ethereum Merkle-Patricia-trie node; see the MPT
  example under `examples/`).
- **scalar / batch**: one request per API call, or a caller batch of 16, 64
  or 256 requests that arrive together.
- **saturation** row: a closed loop that measures drained throughput.
  **Offered-load** (latency) row: open-loop arrivals at a fixed rate, with
  latency measured from each request's scheduled arrival time, so queueing is
  included.
- **candidate**: a named block of runtime overrides (for example
  `{"incremental": {"rebuild_threads": 4}}`). Every tunable is a runtime
  override, so no candidate needs a rebuild. The override fields are defined
  by the C++ resolver; see
  [CONFIGURATION.md](../../include/cpu_byteslice_oram/CONFIGURATION.md).
- **environment class**: the hash of the frozen worker, its dependency
  closure, kernel release, kernel command line, THP modes, topology and
  runtime (native, TDX or SNP). Rows from different classes are never pooled.

## Preset families

Each file name is `<target>[-<purpose>].json`. The target says where the
campaign runs and fixes its admission requirements (`resources`,
`execution`); the purpose says what it measures.

| Target prefix | Environment | Admission requirements |
|---|---|---|
| `c4-tdx` | Intel TDX guest on Google Cloud `c4-standard-32` (Xeon 6, Granite Rapids) | `runtime: tdx`, protected; 1 L3 domain; 125,580,361,728 bytes of guest memory |
| `c4-native` | the same machine type without TDX: the native control | identical to the `c4-tdx` twin except `name` and `execution` |
| `oci-zen5-snp` | AMD SEV-SNP guest on Oracle Cloud `VM.Standard.E6.Flex` (EPYC 9005, Zen 5), 16 OCPUs | `runtime: snp`, protected; 16 physical cores, one SMT sibling per core (`smt: false`); 2 L3 domains; `near_far` placement; the same memory floor |
| `oci-e6-native-control`, `oci-zen5-snp-native-control-pair` | the plain E6 VM and the SNP VM for the native-vs-SNP comparison | identical matrices, seeds and resources; only `name` and `execution` differ |
| `local` | a small AVX-512 workstation (at least 8 physical cores, one L3 domain, 16 GiB) | native; checks the pipeline, not performance |

Resource values are admission requirements, not statements about a
provider's hardware: run `doctor` on the actual target first (below). The
`required_cache_domains` value is an exact-count gate, so a guest that
exposes a different number of L3 domains is refused rather than silently
measured.

| Purpose suffix | What it measures |
|---|---|
| `-smoke` | Correctness at capacity 128 with verification on. Never a performance row. |
| (none) | Main capacity campaign: saturated throughput and memory against capacity 2^15..2^27 for the three shapes, scalar and batch. In `c4-tdx`/`c4-native`, `capacity-sweep-h` adds every power of two for the H shape, `capacity-sweep-h-fixed-lanes16-participants1` is the controlled batch ablation (one frozen geometry, `hierarchy-frozen`, batch 16/64/256), and the `*-std-unordered-map` stages are the non-oblivious serial floor (`std::unordered_map` in the same worker). |
| `-latency` | Response time against offered load. The `latency` stage uses fractions of each arm's own saturation rate plus a 100,000 req/s point; the `latency-headline-*` stages are H at 2^27, K8/V48 at 2^25 and K32/V1024 at 2^21, scalar and batch 64, with `std_unordered_map` partners. |
| `-value-width` | Throughput against value width 8..4096 B at fixed N = 2^20 (and 2^21 for the dense-key stage), for `auto`, `tree` and `hierarchy-frozen` (the hierarchy at one explicit geometry, so only the width changes); `key-width-control` varies the key width at three value widths. This locates the crossover that the hybrid map's tree threshold encodes. |
| `-pilot` | Short rows at a few capacities, used only to fit the per-candidate `trial_time` planning models (below). |
| `-tune-rebuild-screen` | C4 TDX only. Rebuild thread budget 2/4/8/all and explicit owners; `budget-all-refit` carries a rebuild cost model refitted with `fit-rebuild` (below). |
| `-pil1-checkpoints`, `-pil1-full-events` | The harness-overhead pair (below): the same saturated rows at 2^20 with two logging modes. |
| `-baseline-*` | External baselines (below). |
| `-rehearsal`, `local-baseline-*` | Local end-to-end rehearsals of the pipeline and of each baseline worker. |

Main, latency, value-width and baseline presets run with `verification: off`;
the verified smoke stage at each shape and the test suite are the
correctness evidence, so the measured rows do not pay for checking.

Each `c4-native-*` file is a copy of its `c4-tdx-*` twin (smoke, main,
latency, value-width and the `pil1` pair; the pilot, rebuild-screen and
baseline presets are TDX only), and each `oci-zen5-snp-*` file is a copy of its `c4-tdx-*` twin with
only `name`, `execution` and `resources` changed (the tests in
`tests/analysis/test_oram_bench.py` enforce both). The Oracle presets carry
the C4 `trial_time` models; refit them from the Oracle pilot before planning
rows for the record.

## Hardware and TEE requirements

- **CPU**: x86-64 with AVX-512 F/VL/BW/DQ/VBMI/VBMI2/CD, VAES, AES-NI, BMI2
  (see [Requirements](../../README.md#requirements)). VP2INTERSECT is used
  when present (Zen 5); Granite Rapids lacks it and uses the emulation path.
- **Intel TDX**: a TD on Granite Rapids. The guest kernel must expose
  configfs-tsm (Linux 6.7 or newer) for `attest`.
- **AMD SEV-SNP**: an SNP guest on Zen 5 with `/dev/sev-guest` and
  configfs-tsm. SNP on these hosts runs without ciphertext hiding
  (`PLATFORM_INFO` bit 4 clear), so a co-resident host-level observer of
  ciphertext changes is outside what the Zen 5 rows can claim; `attest`
  records the bit for every boot.
- **Native controls**: the same machine type, image, kernel, kernel command
  line and THP mode without the TEE. Run the control with the worker binary
  frozen in the protected campaign (copy `campaign/build/worker`), so the
  only difference is the TEE.
- **Memory**: at least the preset's `host_memory_limit_bytes` visible to the
  guest (about 117 GiB; provision 128 GB). The planner removes rows whose
  modeled memory exceeds the headroom.

## Preparing a VM

The steps are the same on every provider; the provider sections below give
only what differs.

1. **Pin the image and kernel.** Use one fixed image version (the paper's
   runs used Ubuntu 26.04 with the provider's kernel) and hold the kernel
   packages after the first boot (`apt-mark hold` on the running kernel's
   `linux-image-*`, `linux-modules-*`, `linux-headers-*` and the provider's
   kernel metapackages). Never install a kernel metapackage (for example
   `linux-tools-<provider>` for `perf`): it can pull a newer kernel that the
   next boot selects, which is a new environment class. Install
   `linux-tools-$(uname -r)` instead.
2. **Quiet the guest.** Disable unattended upgrades and the apt timers
   (`unattended-upgrades.service`, `apt-daily.timer`,
   `apt-daily-upgrade.timer`), `apport`, and snap refreshes
   (`snap refresh --hold`).
3. **Packages and build.** `build-essential cmake git python3 chrony
   numactl python3-matplotlib linux-tools-$(uname -r)`; for the baselines
   also the packages in [the baseline guide](../baselines/README.md). Build
   with GCC from the repository root:

   ```bash
   cmake -S . -B build -DCPU_BYTESLICE_ORAM_BUILD=all && cmake --build build -j"$(nproc)"
   ```

   The campaign worker is `build/benchmarks/cpu_oram_benchmark` and the
   reducer `build/analysis/oram_bench_aggregate`. A TD may hide CPU features
   that the plain VM shows (on C4: AVX10.1, HLE, RTM, HRESET), so
   `-march=native` differs between the two; build in the protected guest and
   copy that frozen worker to the native control.
4. **Isolate the measurement cores.** Reserve physical core 0 (both SMT
   siblings) for housekeeping and the harness, and make every other CPU
   tickless, through a file in `/etc/default/grub.d/` followed by
   `update-grub` and one reboot:

   ```bash
   # C4 (siblings are n and n+16):           nohz_full=1-31 rcu_nocbs=1-31 irqaffinity=0
   # Oracle E6 (siblings adjacent, 0 and 1): nohz_full=2-31 rcu_nocbs=2-31 irqaffinity=0-1
   echo 'GRUB_CMDLINE_LINUX_DEFAULT="$GRUB_CMDLINE_LINUX_DEFAULT nohz_full=1-31 rcu_nocbs=1-31 irqaffinity=0"' \
     | sudo tee /etc/default/grub.d/99-oram-bench-nohz.cfg
   sudo update-grub   # then restart the VM
   ```

   Check `cat /proc/cmdline` and `cat /sys/devices/system/cpu/nohz_full`
   after every boot. In a TD every periodic scheduler tick on the request
   thread's core costs a VM exit, which otherwise dominates the latency tail.
   The command line is part of the environment class, so the native control
   needs the same one. `doctor` reports the topology and sibling pairing to
   use.
5. **Huge pages.** The library backs every allocation of 2 MiB or more with
   a 2 MiB-aligned mapping advised `MADV_HUGEPAGE` (default on;
   `MICRORAM_HUGE_PAGES=0` disables it; see
   [cpu_byteslice_layout.hpp](../../src/oram/table/cpu_byteslice_layout.hpp)).
   Keep `/sys/kernel/mm/transparent_hugepage/enabled` at `madvise` (the
   Ubuntu default) or `always`; under `never` the advice does nothing.
   `doctor` records both THP modes in the environment class. In an SNP guest
   the host's backing for guest memory may start as 4 KiB pages; touch most
   of guest memory once after boot and let it settle before the first
   measured trial.
6. **Data disk.** Put campaign directories on a separate retained disk
   (50 GB is enough for publication output) mounted at `/mnt/oram-bench`
   through `/etc/fstab` by UUID with `nofail`. Format it only when it is
   blank (`blkid` finds nothing and its first MiB reads as zeros), with eager
   inode-table initialization (`mkfs.ext4 -m 0 -E
   lazy_itable_init=0,lazy_journal_init=0`) so background initialization
   does not write during the first trials. When replacing a disk, remove the
   old disk's `/etc/fstab` line first: under `nofail` a stale first line
   leaves the new disk unmounted without an error.
7. **Clock.** Run `chrony`. After a stop and start the guest clock is off by
   about a second and chrony slews `CLOCK_MONOTONIC` until it is corrected;
   the service unit waits (`chronyc waitsync`) so no trial is timed during
   the slew. `doctor` reports `clock: tsc_validated` on TDX; SNP guests hide
   the invariant-TSC flags and use `kvm-clock`, so `doctor` reports
   `monotonic` there, and the worker's own `--clock-check` must pass.
8. **Constant-time instruction check.** On an idle core whose sibling is
   idle, certify the timing of the instructions the library emits on this
   CPU and take the instruction census, as described in
   [tests/timing](../../tests/timing/README.md) (section "On each target").
   This is the first step on a new CPU model, before any campaign.
9. **Gate the host.**

   ```bash
   python3 -m analysis.oram_bench doctor --execution tdx --worker build/benchmarks/cpu_oram_benchmark \
     --output /mnt/oram-bench/doctor.json --require-physical-cores 16 --require-cache-domains 1
   ```

   Use `--execution snp --require-cache-domains 2` on Oracle and
   `--execution native` on a control. `doctor` exits non-zero unless the
   guest kernel shows the requested runtime (for SNP: `/dev/sev-guest` and the
   `Memory Encryption Features active: AMD SEV SEV-ES SEV-SNP` boot line), the
   core and L3 counts match, and the compiled ISA is exposed.
10. **Check each boot's cache and bandwidth.** Cloud boots differ in
    placement and co-tenants, and some SNP hosts limit the L3 a guest can
    use. Before measuring, run the seconds-long microbenchmarks on an idle
    guest, on a core of each L3 domain, and compare against a reference boot
    of the same machine type:

    ```bash
    build/benchmarks/cpu_cache_latency_benchmark --cpu 2 --max-mib 512
    build/benchmarks/cpu_mem_bandwidth_benchmark --sweep 1,15 --seconds 5 --mib-per-thread 1024 --first-core 1
    ```

    Record the result with the campaign and label rows from a degraded boot
    rather than pooling them silently. The paper's Intel boots read at least
    150 GB/s with 15 threads and at most 40 ns at 32 MiB on CPU 1. On the
    E6 SEV-SNP guest, touch guest memory first (`sudo
    build/benchmarks/cpu_host_topology_probe --tests region --region-gib 110
    --region-lines-per-page 8 --region-core 2`) and run
    `python3 analysis/paper_micro.py l3-check --out <dir>` before and after
    each campaign: it judges one core of each L3 domain against the whole-L3
    limits (exit 0 WHOLE, 1 CAPPED), since the host can cap a guest's L3 share
    without changing what `doctor` sees.

### Intel TDX on Google Cloud C4

```bash
gcloud --project=<your-project> compute instances create <instance> --zone=<zone> \
  --machine-type=c4-standard-32 --min-cpu-platform="Intel Granite Rapids" \
  --confidential-compute-type=TDX --maintenance-policy=TERMINATE \
  --create-disk=boot=yes,auto-delete=yes,image=projects/ubuntu-os-cloud/global/images/<pinned-ubuntu-image>,type=hyperdisk-balanced,size=50GB \
  --create-disk=name=<instance>-data,device-name=oram-data,type=hyperdisk-balanced,size=50GB,auto-delete=no \
  --metadata-from-file=startup-script=<script that mounts the data disk and does steps 1-2>
# optional, cheaper: --provisioning-model=SPOT --instance-termination-action=STOP --no-restart-on-failure
```

The native control is the same command without `--confidential-compute-type`.
A Spot VM is stopped with about 30 s of notice and is not restarted; start
it again with `gcloud compute instances start`. Host maintenance also stops a
TD (no live migration). Both are expected interruptions (below).

**Attestation verification.** Each boot's capture is verified offline with
Google's [go-tdx-guest](https://github.com/google/go-tdx-guest) against
Intel's collateral (`go install github.com/google/go-tdx-guest/tools/check@latest`,
with Ubuntu's `golang-go`):

```bash
B=attestation-binding-v1-<hash>      # printed by attest, or in the unit's journal
RD=$(python3 -c "import json; print(json.load(open('$C/attestations/$B.json'))['report_data'])")
L=$C/attestations/$B.check.log
~/go/bin/check -in $C/attestations/$B.report.bin -get_collateral true -check_crl true \
  -report_data $RD -td_attributes 0000001000000000 -verbosity 1 > $L 2>&1
python3 -m analysis.oram_bench verdict --campaign $C --capture attestations/$B.json \
  --verifier "go-tdx-guest <version> tools/check -get_collateral true -check_crl true -td_attributes 0000001000000000" \
  --result verified --reference "go-tdx-guest-check-<UTC time>-quote-sha256-<prefix>" --verifier-output $L
```

`-td_attributes 0000001000000000` is SEPT_VE_DISABLE alone, so the check
fails if the TD's DEBUG bit is set. Record `--result failed` if any step
fails.

### AMD SEV-SNP on Oracle Cloud E6

```bash
oci compute instance launch --compartment-id <compartment> --availability-domain <ad> \
  --display-name <instance> --shape VM.Standard.E6.Flex --shape-config '{"ocpus":16,"memoryInGBs":128}' \
  --platform-config '{"type":"AMD_VM","isMemoryEncryptionEnabled":true}' \
  --image-id <pinned-ubuntu-image> --boot-volume-size-in-gbs 100 --subnet-id <subnet> \
  --ssh-authorized-keys-file <key.pub> --wait-for-state RUNNING
```

Confidential computing is chosen at launch and excludes preemptible
capacity, so the VM is on-demand. The native control is the same launch
without `--platform-config`. An OCPU is one physical core with two SMT
threads, so the guest shows 32 vCPUs on two whole 8-core CCDs (two L3
domains). A 100 GB boot volume holds the checkout, builds and campaigns, so
no block volume is needed. Stop and start the instance with `oci compute
instance action` rather than rebooting from inside the guest, and run `sync`
before every stop: a soft stop can lose unflushed files.

`attest` must report provider `sev_guest`, layout `snp_report` and
`report_data_matches: true`; its `facts` record the policy DEBUG bit (a
debug guest blocks a protected run) and `PLATFORM_INFO`, whose bit 4 is
Ciphertext Hiding (expected clear).

**Attestation verification** uses virtee
[snpguest](https://github.com/virtee/snpguest) against AMD's VCEK from the
Key Distribution Service, then checks that the report's REPORT_DATA (offset
0x50, 64 bytes) equals the capture's `report_data`:

```bash
A=$C/attestations; R=$A/$B.report.bin; CERTS=~/snp-certs; L=$A/$B.snpguest.log; mkdir -p $CERTS
snpguest fetch ca pem $CERTS turin                 # ARK and ASK
snpguest fetch vcek pem $CERTS $R                  # the VCEK for this chip and TCB
{ snpguest verify certs $CERTS && snpguest verify attestation -p turin $CERTS $R; } > $L 2>&1
python3 -c "import json,sys; c=json.load(open('$A/$B.json')); r=open('$R','rb').read(); \
  sys.exit(0 if r[0x50:0x90].hex()==c['report_data'] else 1)" && echo REPORT_DATA_MATCH >> $L
python3 -m analysis.oram_bench verdict --campaign $C --capture attestations/$B.json \
  --verifier "snpguest <version> verify certs + verify attestation -p turin" \
  --result verified --reference "snpguest-<UTC time>-report-sha256-<prefix>" --verifier-output $L
```

## Running a campaign

### Quick check on one machine (minutes)

Without a confidential VM, `local-native-rehearsal.json` runs the whole
pipeline natively (plan, resolve, doctor, preflight, run, reduce, plot) on
one AVX-512 host: the three shapes at N = 2^16 with `auto`,
`hierarchical_incremental` and `tree`, scalar and batch-64 saturation, plus
two fixed-rate rows. It checks the path, not performance. The commands are in
[WORKER.md, "Native runs and the local rehearsal"](../../analysis/oram_bench/WORKER.md#native-runs-and-the-local-rehearsal).
The preset declares 8 physical cores (a minimum), one L3 domain (an exact
count) and 16 GiB. On a host with a different number of L3 domains, such as
a multi-CCD Zen workstation, plan a copy whose
`resources.required_cache_domains` equals the count `doctor` reports; on a
host with fewer cores also lower `physical_cores`, keeping it a multiple of
the L3 count. The `local-baseline-*.json` presets do the same for each
baseline worker.

### A full campaign

From the repository root, with `C` a new directory on the data disk:

```bash
C=/mnt/oram-bench/<campaign>
python3 -m analysis.oram_bench plan --config benchmarks/campaigns/<preset>.json --output $C
python3 -m analysis.oram_bench resolve --campaign $C --worker build/benchmarks/cpu_oram_benchmark
python3 -m analysis.oram_bench preflight --campaign $C --environment /mnt/oram-bench/doctor.json
sudo python3 -m analysis.oram_bench attest --campaign $C          # tdx/snp only, once per boot
python3 -m analysis.oram_bench run --campaign $C --reducer build/analysis/oram_bench_aggregate
```

- `plan` validates the preset and writes `plan.json` with every logical
  trial; rows are `deferred` until resolved or `skipped` with a reason. Its
  counts are authoritative: defaults, coverage models and admission checks
  decide the runnable matrix, not the preset alone.
- `resolve` copies the worker into `$C/build/worker`, resolves every row
  with the C++ resolver and writes `resolution.json` (runnable, `same_as`
  another row, or skipped with a reason, including modeled memory over the
  host headroom). `run` and `resume` launch only that frozen copy.
- `run` refuses a host whose runtime, core and L3 counts, or ISA differ from
  the campaign, and a protected campaign without a capture for this boot.
  The first `run` writes `launch_policy.json` (retries, preemption retries,
  and the free-space guard, default 5 GiB); later runs reuse it.
- Run one campaign at a time: each assumes the whole machine. Do not build
  or relink while a campaign runs.

**As a boot service.** To resume automatically after a preemption, host
maintenance or a reboot, install one unit per campaign from
[oram-bench-campaign.service.in](oram-bench-campaign.service.in) (delete its
`attest` line for a native campaign):

```bash
U=oram-bench-<campaign>.service
sed -e "s|@CAMPAIGN_ROOT@|$C|g" -e "s|@BENCH_USER@|$(id -un)|g" -e "s|@SOURCE_ROOT@|$PWD|g" \
    -e "s|@PYTHON@|/usr/bin/python3|g" -e "s|@REDUCER@|$PWD/build/analysis/oram_bench_aggregate|g" \
    -e "s|@MIN_FREE_BYTES@|5368709120|g" \
    benchmarks/campaigns/oram-bench-campaign.service.in | sudo tee /etc/systemd/system/$U > /dev/null
sudo systemctl daemon-reload && sudo systemctl enable --now $U
```

On every start the unit attests as root, waits for the clock, and runs
`resume`, which exits when nothing is left or the campaign is blocked.
Disable the unit when the campaign finishes. Progress: `python3 -m
analysis.oram_bench status --campaign $C`, `journalctl -u $U`, and
`$C/coordinator_status.json` (`running`, `idle`, or `blocked` with a
reason).

**Interruptions.** A trial cut off by a stop is left orphaned and counted as
a preemption (retried up to `preemption_retries`, default 20), not as a
failure. After each boot, verify the new attestation capture (provider
sections above) and check `chronyc tracking`. A VM can be replaced (new boot
disk, same retained data disk): rebuild the checkout, reinstall the unit,
rerun `doctor`, and compare the new `environment_class` with the stored
rows' before resuming. The class excludes the machine-id, so a replacement
with the same image, kernel, command line and frozen worker keeps the rows.

**Fallback build.** `-DCPU_BYTESLICE_ORAM_ENABLE_VP2INTERSECT=OFF` produces a
different worker, not a preset field. Build it in a second tree, plan the
same preset into a second directory and `resolve` it with that worker; its
rows form their own environment class. On Zen 5 this measures the native
instruction against the emulation on the same hardware.

## Experiment index

For the paper's own numbers, follow [REPRODUCE.md](../../REPRODUCE.md): it
uses the [paper presets](paper/README.md), `analysis/paper_numbers.py` for
the campaigns, `analysis/paper_micro.py` for the micro-benchmarks below, and
`analysis/plot_stash_tail.py` for the tree's stash tail. This index lists the
general instruments behind each experiment.

Each experiment, what runs it, and what turns its output into a table or
figure. `<target>` is one of the prefixes above; binaries are under
`build/benchmarks/` unless noted.

| Experiment | Run with | Reduced by |
|---|---|---|
| Throughput and memory against capacity, three shapes, scalar and batch, with the `std::unordered_map` floor | `<target>.json` (campaign worker `cpu_oram_benchmark`) | `reduce`, then `plot` ([Outputs and reduction](#outputs-and-reduction)) |
| Response time against offered load | `<target>-latency.json`; matched curves as in [Matched latency curves](#matched-latency-curves) | `reduce`, `plot` |
| Throughput and memory against value width; the hierarchy/tree crossover | `<target>-value-width.json` | `reduce`, `plot`, then [crossover_export.py](../../analysis/crossover_export.py) `--summary <reduced>/summary.json --resolution $C/resolution.json --output <dir>` |
| Rebuild throughput against owner threads and the memory-bandwidth ceiling | `cpu_byteslice_level_arena_benchmark --write-only --stage-times --fit-rows` at each owner count, and `cpu_mem_bandwidth_benchmark --sweep <thread counts>` (each arena run's 1 + owners + top helpers; [guide](../oram/README.md#cpu_byteslice_level_arena_benchmark), [host characterization](../oram/README.md#host-characterization)) | [bandwidth_join.py](../../analysis/bandwidth_join.py) `--rebuild ... --bandwidth ...` |
| Rebuild thread division behind the default (C4) | `c4-tdx-tune-rebuild-screen.json` | `reduce`, `plot` |
| External baselines (H2O2RAM patched and as published, SONIC) | `<target>-baseline-*.json` ([Baselines](#baselines)) | `reduce`, `plot` with our summary |
| TEE cost (native against TDX or SNP) | `c4-native*` against `c4-tdx*`; [Native-vs-SNP control](#native-vs-snp-control) | `reduce` each arm, `plot` both summaries |
| Harness overhead | the `*-pil1-*` pair ([Harness-overhead pair](#harness-overhead-pair--pil1-)) | `validation-record` |
| VP2INTERSECT against the portable fallback, whole engine | [Fallback build](#a-full-campaign) of any preset | `reduce`, `plot` both builds |
| Table rebuild against H2O2RAM's level build | `cpu_byteslice_table_rebuild_benchmark` and `h2o2ram_routing_bench` ([guide](../oram/README.md#cpu_byteslice_table_rebuild_benchmark)) | their JSON rows |
| Tree eviction pass against EnigMap's Path ORAM eviction | `cpu_tree_eviction_comparator_benchmark_enigmap`, built against [fetch_enigmap.sh](../baselines/fetch_enigmap.sh)'s checkout ([guide](../oram/README.md#cpu_tree_eviction_comparator_benchmark)) | its JSON lines |
| Key-deduplication kernel, VP2INTERSECT against the fallback, and its share of a merge | `cpu_byteslice_dedup_kernel_benchmark`, `cpu_byteslice_level_arena_benchmark_compare_counted` and the plain arena benchmark with `--fit-rows` ([guide](../oram/README.md#cpu_byteslice_dedup_kernel_benchmark)) | [compare_share.py](../../analysis/compare_share.py) `--counted --merge --kernel` |
| Pre-routing (starting a merge's preparation before its carry arrives) on and off | `cpu_byteslice_level_arena_benchmark --merge-rows --stage-times`, with and without `--no-preroute` ([guide](../oram/README.md#cpu_byteslice_level_arena_benchmark)) | [preroute_rows.py](../../analysis/preroute_rows.py) `shares` and `compare` |
| Rebuild/access ratio at which requests start to stall | `cpu_byteslice_level_arena_benchmark_throttled` ([instrumented variants](../oram/README.md#instrumented-variants)) | [stall_bracket.py](../../analysis/stall_bracket.py) `bracket` |
| Memory per level against the layout model | `cpu_oram_allocation_audit` ([guide](../oram/README.md#cpu_oram_allocation_audit)) | [allocation_reconcile.py](../../analysis/allocation_reconcile.py) |
| Constant-time instruction timing and census | `build/tests/avx512_constant_time_test --certify` and `instruction_census.py` ([tests/timing](../../tests/timing/README.md#on-each-target)) | [timing_summary.py](../../analysis/timing_summary.py) |
| Arena benchmark's paced-path harness check | the arena benchmark with `--rate` | [arena_harness_gate.py](../../analysis/arena_harness_gate.py) |

## Order of a full reproduction on one target

1. **Smoke**: `<target>-smoke.json` and each `<target>-baseline-*-smoke.json`.
2. **Pilot and timing models.** Run `<target>-pilot.json` and the
   `<target>-baseline-pilot-*.json` files, then refit the planning models:

   ```bash
   python3 -m analysis.oram_bench fit-trial-time --campaign <pilot dir> [--campaign ...] \
     --apply benchmarks/campaigns/<preset>.json [--apply ...]
   ```

   A candidate's `trial_time` model (access time, setup time per entry, and
   a capacity exponent) estimates each row's duration so the planner can
   size measurement windows for the configured access coverage and prune
   rows that cannot finish under the trial cap. The models in these files
   are fitted from pilots on C4; refit them on any other target. They are
   planning estimates, not results.
3. **Rebuild cost model (optional).** Fit the hierarchy's rebuild cost model
   to the machine (tens of minutes on a 16-core target):

   ```bash
   python3 -m analysis.oram_bench fit-rebuild --benchmark build/benchmarks/cpu_byteslice_level_arena_benchmark \
     --grid target --rows fit-rows.jsonl --output rebuild-fit.json
   ```

   `rebuild-fit.json` holds the `rebuild_cost_*` override block, which a
   candidate carries the way `budget-all-refit` in the rebuild screen does;
   see [WORKER.md, "Fitting the rebuild cost model"](../../analysis/oram_bench/WORKER.md#fitting-the-rebuild-cost-model).
4. **Tuning screen** (`c4-tdx-tune-rebuild-screen.json`, C4 only). Each screening stage
   uses the `screening` seed stream; validate a chosen setting on held-out
   seeds (the planner refuses screening seeds in a `held_out` stage). Freeze
   the chosen settings as explicit overrides in a separately named preset.
5. **Capacity, latency, value-width**, then the baselines and the native
   control pair. Never pool rows across targets or environment classes.

Trial and campaign limits (`max_trial_ns`, `limits.max_trials`,
`limits.max_campaign_trial_ns`) bound the expanded work including planned
retries; changing an axis may require raising them. Large campaigns can be
split by stage into several campaign directories.

**Scale.** `python3 -m analysis.oram_bench plan --config <preset> --dry-run`
prints the row counts, skip reasons and a `cost` block:
`trial_time_bound_sum_ns` sums each row's modeled duration (its cap when it
has no model), and `trial_time_bound_with_retries_sum_ns` adds the planned
retries. That bound never exceeds the preset's declared budget
(`limits.max_campaign_trial_ns`), which is a planning cap, not a run time.
On one target the caps are about 330 hours of trial time for the main
capacity preset, about 1,130 hours for the latency preset, about 170 hours
for the value-width preset, about 72 hours for the rebuild screen and up to
about 140 hours for each baseline preset; the smoke presets and the local
rehearsal fit in about an hour. To check a result without the whole matrix,
copy a preset and keep one shape, a few capacities or one stage. Rows are
independent trials, except that a latency stage given as fractions of
saturation needs its arms' saturation rows in the same campaign.

### Matched latency curves

For a figure that compares schemes, all arms share one **absolute** geometric
offered-rate grid, generated after each arm's saturation rate S is known:

```bash
python3 -m analysis.oram_bench rate-grid --minimum <LOW> --maximum <HIGH> --factor 2
```

Choose LOW near the slowest arm's S/8 and HIGH near 0.95 of the fastest S,
and copy the emitted `rates` block verbatim into every matched stage, with
the same seeds, windows and floor. The fraction-of-saturation presets are
templates for this step. The figure's x-axis is the offered rate on a log
scale; achieved rate is in the tables. A rate above a slower arm's capacity
overloads it: such rows keep their censoring, backlog and loss labels and are
never shown as stable latency.

### Baselines

- `*-baseline-h2o2ram*`: H2O2RAM with constant-time moves and fresh dummy
  lookups enabled (`oblivious`).
- `*-baseline-h2o2ram-shipped*`: H2O2RAM as published (`not_oblivious`),
  sharing seeds with the patched campaign.
- `*-baseline-sonic*`: SONIC's ZingORAM and its recursive position-map
  variant.
- `std_unordered_map` runs in the main worker as the non-oblivious floor.

Build the baseline workers and prepare H2O2RAM's planner cache on the target
with `prepare-h2o2ram` before `resolve`, as described in
[the baseline guide](../baselines/README.md). Baseline security labels,
memory admission, unsupported APIs and timing caps stay attached to each row.

### Harness-overhead pair (`*-pil1-*`)

`<target>-pil1-checkpoints.json` and `<target>-pil1-full-events.json` hold the
same saturated rows (the three shapes at 2^20; `auto`, `hierarchical_incremental`
and `tree`; scalar and batch 64; verification off) and differ only in
logging. The `pil1` suffix is only the pair's fixed file-name label. Plan each into its own
directory, run and `reduce` both, plan the checkpoints preset a third time
and resolve it with `--synthetic --synthetic-backend noop` (a worker that
stores nothing, which measures the harness alone), and then:

```bash
python3 -m analysis.oram_bench validation-record --control <checkpoints>/summary.json \
  --instrumented <full-events>/summary.json --noop <noop>/summary.json --output <dir>
```

An identical-arms null (`--comparison identical_arms`) plans the checkpoints
preset twice. The resulting records report harness cost per request and the
change of each latency quantile due to logging; they are reported evidence
and do not block rows (see WORKER.md, "Harness validation records"). The
arena benchmark's paced path is checked outside the campaign by
[arena_harness_gate.py](../../analysis/arena_harness_gate.py).

### Native-vs-SNP control

`oci-e6-native-control.json` (on the plain E6 VM) and
`oci-zen5-snp-native-control-pair.json` (on the SNP VM) run three saturation
rows with seed 9001: H at 2^27 (batch 64, `auto`), K8/V48 at 2^25 (batch
64, `auto`) and K4/V1024 at 2^21 (scalar, `tree`). Run the control with the
SNP campaign's frozen worker. For response times, after both arms'
saturation rows exist, plan a copy of each with a latency stage at one
integer `absolute_ops_per_second` equal to 0.7 times the slower arm's
drained throughput (at least 100,000 req/s). Report the throughput loss
`100*(1 - S_snp/S_native)` % and the latency ratios for p50/p99/p99.9/max
alongside the raw values; they are ranges over runs, not confidence
intervals. The C4 pair is `c4-tdx*` against `c4-native*`.

## Outputs and reduction

Everything a campaign produces stays in its directory `$C`:

| Path | Content |
|---|---|
| `plan.json` | the expanded, immutable matrix |
| `build/worker`, `build/build.json` | the frozen worker and its hashes (worker, library headers, baseline caches) |
| `resolution.json` | per-row resolution or skip reason |
| `launch_policy.json`, `coordinator_status.json` | retry and disk policy; live state |
| attempt directories | one per trial attempt: raw events or histogram checkpoints, `memory.csv`, the environment record, a manifest of SHA-256 hashes and `COMMITTED.json` |
| `attestations/` | per-boot TDX/SNP captures, verifier logs and verdicts |

Reduce and plot:

```bash
python3 -m analysis.oram_bench reduce --campaign $C --reducer build/analysis/oram_bench_aggregate --output $C.reduced
python3 -m analysis.oram_bench plot --summary $C.reduced/summary.json [--summary <other>/summary.json] --output $C.plots
```

`reduce` re-verifies every committed attempt and writes `summary.json`
(per-repetition statistics, coverage and labels) and `repetitions.csv`. A row
of a protected campaign is `protected_verified` only if its boot's capture
has a `verified` verdict and no `failed` one; otherwise it carries
`protection_unverified`. `plot` draws throughput against capacity, latency
against offered rate, value-width and memory figures, one series per
campaign, build and configuration. `memory.csv` timestamps are absolute
monotonic clock values; subtract phase boundaries for durations.

## Measurement rules

- **Throughput over whole cycles.** Average over at least N accesses (N =
  capacity, one whole top-rebuild cycle) after a settle cycle; a short window
  can contain no top rebuild and overstate throughput. Check
  `maintenance_coverage` and the reducer's `insufficient_cycle_coverage`
  label.
- **Saturation rows** with `service_timing` off collect throughput without
  latency quantiles; report absent quantiles as absent. With
  `service_timing` on, each call logs a 64-byte event into
  `instrumentation.buffer_bytes` (default 64 MiB); size it for the row's call
  count, or the trial is invalid.
- **Offered rates** for our schemes are at least 100,000 req/s; baselines
  lower the floor. Stalls are measured at a fixed offered rate with latency
  from the scheduled arrival, never in a closed loop.
- **Latency is noisier than throughput** across identical runs. Prefer p50,
  or several repetitions reported as min..max; A/B comparisons alternate arm
  order and start with an identical-arms null.
- **Never time a single operation** in a microbenchmark: loop at least 10^4
  calls and divide.
- **Thread placement.** Check actual worker CPU masks before trusting thread
  scaling: OpenMP `OMP_PROC_BIND=true` (used by some baselines) can narrow the
  caller's mask before a thread pool is created. The worker records masks
  and counts per attempt.
- **Hierarchy rows use values below the hybrid threshold**
  (`kHybridTreeValueThreshold` in
  [default_rule.hpp](../../include/cpu_byteslice_oram/default_rule.hpp));
  wide values are the tree ORAM's regime.
- **Environment class.** A kernel upgrade, a kernel command-line or THP
  change, a different image or a rebuilt worker is a new class, and its rows
  are measured again rather than pooled.
- **Memory comparison.** Report matched peak RSS (VmHWM), sampled RSS/PSS
  over the measurement window and bytes per logical byte for ours and the
  baselines. Process RSS includes the harness and logging; keep the library's
  modeled bytes separate.

**Storage.** Publication output (histogram checkpoints, count and time
windows, telemetry and summaries) fits a 50 GB data disk with the 5 GiB
free-space guard. Full-event logging keeps about 192 bytes per scalar request
and needs its own size estimate. Check `df` between stages; the coordinator
checks only the watermark and does not reserve the next trial's output.
