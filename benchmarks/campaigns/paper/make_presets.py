#!/usr/bin/env python3
"""Write the paper preset family: one campaign per (target, item) behind the paper's measured numbers.

    python3 benchmarks/campaigns/paper/make_presets.py              (re)write every <target>-<item>.json here
    python3 benchmarks/campaigns/paper/make_presets.py --check      regenerate in memory, compare with the files
    python3 benchmarks/campaigns/paper/make_presets.py --rehearsal OUT [--physical-cores 16]
                                                  [--host-memory-bytes N]   scaled native copies for a local check

Targets: c4-tdx (Intel TDX, a 16-core c4-standard-32 guest with one L3), c4-native (the same VM without
TDX), oci-zen5-snp (AMD SEV-SNP, a 16-OCPU E6 guest with two L3 domains), oci-e6-native (the same VM without
SNP). The native targets exist only for the TEE-overhead pair (`tee`).

Every campaign keeps the settings the measured rows ran with: one trial per row, counter keys
(workload.distribution counter), a 1 s spin before any library thread parks (resources.spin_before_park_ns),
verification off, at least N settle requests (2^21 for SONIC), windows that hold at least N requests at the
slower target's measured rate (0.25-1.1 N for SONIC, 2 N for H2O2RAM), a 256 MiB event buffer (1 GiB with
per-call service timing on batch latency rows), a checkpoint thread on fixed-rate rows, whole batches of 64
arriving together on batch latency rows, and parallel 8 x 8 batch tiles for the hierarchical ORAM's batches.

An oci-zen5-snp preset plans the same matrix (rows, seeds, windows) as its c4-tdx twin; only name, execution
and resources differ. Where the measured rows of the two machines used different window models, the twins
share one model, usually the longer (ours in throughput-k4v8 below 2^30). Every window holds at least N
requests at the measured rates, except SONIC's, sized 0.25-1.1 N as measured. One exception to sharing: the
std::unordered_map stages of throughput-k4v8 keep each machine's own model (UNORDERED_MAP_SWEEP_MODELS),
since no single 2^30 window fits both. The c4-native and oci-e6-native presets differ from their protected
twin only in name and execution.

Response-time rows are fixed-arrival rows at a fraction of the saturated row measured first in the same
campaign (rates.saturation_fractions_ppm); the coordinator freezes that rate before they run.

Standard library only; the output is deterministic (JSON, two-space indent, one trailing newline).
"""

import argparse
import copy
import json
import math
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent

SECOND = 10**9
HOUR = 3600 * SECOND
DAY = 24 * HOUR
SPIN = SECOND                       # resources.spin_before_park_ns: nothing parks between requests
MIB = 1 << 20
N16, N20, N21, N25, N27, N30 = 1 << 16, 1 << 20, 1 << 21, 1 << 25, 1 << 27, 1 << 30
SETTLE_FLOOR = N21                  # sweeps settle max(N, 2^21)

# ---------------------------------------------------------------------------------------------------------------
# Targets. The C4 guest exposes 16 physical cores on one L3; the E6 guest 16 on two L3 domains (CCDs).
# host_memory_limit_bytes is each VM's MemTotal (planning and admission cap only).
C4_RESOURCES = {"physical_cores": 16, "smt": False, "required_cache_domains": 1,
                "host_memory_limit_bytes": 125580361728, "placement": "near_far", "spin_before_park_ns": SPIN}
E6_RESOURCES = {"physical_cores": 16, "smt": False, "required_cache_domains": 2,
                "host_memory_limit_bytes": 134576222208, "placement": "near_far", "spin_before_park_ns": SPIN}
# H2O2RAM's configuration search (prepare-h2o2ram) needs the 256 GB E6 SNP guest at 5% headroom: about
# 115 GiB at K4/V8 2^27, 166 GiB at K8/V48 2^25 and more than 186 GiB at K32/V1024 2^21. Every H2O2RAM
# SNP preset declares it; its C4 twin resolves with the planner cache copied from that VM.
E6_256GB_RESOURCES = {**E6_RESOURCES, "host_memory_limit_bytes": 269766885376, "headroom_ppm": 50000}

TARGETS = {
    "c4-tdx": (C4_RESOURCES, {"runtime": "tdx", "require_protected": True}),
    "c4-native": (C4_RESOURCES, {"runtime": "native", "require_protected": False}),
    "oci-zen5-snp": (E6_RESOURCES, {"runtime": "snp", "require_protected": True}),
    "oci-e6-native": (E6_RESOURCES, {"runtime": "native", "require_protected": False}),
}
PROTECTED = ("c4-tdx", "oci-zen5-snp")
NATIVE_TWIN = {"c4-native": "c4-tdx", "oci-e6-native": "oci-zen5-snp"}

# ---------------------------------------------------------------------------------------------------------------
# Shapes. Table 1's three shapes; SONIC (an index ORAM) takes 8-byte dense keys where the others take
# K8 or K32 keys, as in the measured rows.
K4V8 = {"name": "standard-provisional-k4-v8", "key_bytes": 4, "value_bytes": 8, "key_layout": "dense"}
K8V48 = {"name": "signal-sized", "key_bytes": 8, "value_bytes": 48}
K32V1024 = {"name": "ethereum-mpt-sized", "key_bytes": 32, "value_bytes": 1024}
K8V48_DENSE = {"name": "k8-v48-dense", "key_bytes": 8, "value_bytes": 48, "key_layout": "dense"}
K8V1024_DENSE = {"name": "k8-v1024-dense", "key_bytes": 8, "value_bytes": 1024, "key_layout": "dense"}


def k8(value_bytes, dense=False):
    """A Figure 8 shape: 8-byte keys (permuted, or dense for SONIC)."""
    if dense:
        return {"name": f"k8-v{value_bytes}-dense", "key_bytes": 8, "value_bytes": value_bytes, "key_layout": "dense"}
    return {"name": f"k8-v{value_bytes}", "key_bytes": 8, "value_bytes": value_bytes}


# Seed streams (stage.seed_stream): opaque names shared by every system at a shape, so all of them see the
# same workload seeds at that shape.
STREAM = {"k4v8": "oci-large-k4v8", "k8v48": "oci-large-k8v48", "k32v1024": "oci-large-k32v1024",
          "tee": "fp-ours-k4v8-2p27", "width": "fp-width-k8-2p20"}

# ---------------------------------------------------------------------------------------------------------------
# Candidates (the reducer selects rows by these names).
PARALLEL_TILES = {"batch_execution": "parallel_tiles", "batch_participants": 8}
# The frozen-geometry hierarchy of Figure 8 ("Ours, hierarchical ORAM"): the release's existing block.
HIERARCHY_FROZEN = {
    "scheme": "hierarchical_incremental",
    "incremental": {"branching_factor": 8, "online_stash_entries": 64, "prefix_flushes": 8, "top_digit": 8,
                    "dense_prefixes": 2, "owner_threads": 2, "top_helpers": 0, "rebuild_lanes": 1,
                    "bank_first": "no_clone", "time_rebuild_stages": False, "near_max_level": 0, "batch_lanes": 16,
                    "batch_execution": "chunked_cascade", "batch_participants": 1, "batch_bucket_scan": False,
                    "batch_profile": False, "batch_result_layout": "sliced_place_at_lane", "batch_spin_ns": 1000000,
                    "owner_spin_ns": 1000000, "park_retry_us": 1000, "wait_limit_ms": 120000}}


def candidate(name, overrides, models=()):
    entry = {"name": name, "overrides": copy.deepcopy(overrides)}
    if models:
        entry["trial_time"] = [dict(m) for m in models]
    return entry


def auto(*models):
    return candidate("auto", {"scheme": "auto"}, models)


def parallel_8x8(*models, batch_spin=False):
    """Batches of 64 split over 8 request threads (tiles) of 8 lanes; the measured latency rows also pinned the
    batch helpers' spin to 1 s explicitly (the same value the resource spin gives it)."""
    incremental = {**PARALLEL_TILES, "batch_lanes": 8}
    if batch_spin:
        incremental["batch_spin_ns"] = SPIN
    return candidate("parallel-8x8", {"scheme": "hierarchical_incremental", "incremental": incremental}, models)


def hierarchy_frozen(*models):
    return candidate("hierarchy-frozen", HIERARCHY_FROZEN, models)


def tree(*models):
    return candidate("tree", {"scheme": "tree"}, models)


def unordered_map(*models):
    return candidate("std_unordered_map", {"scheme": "std_unordered_map"}, models)


def h2o2ram(*models, shipped=False):
    scheme = "h2o2ram_shipped" if shipped else "h2o2ram"
    return candidate(scheme, {"scheme": scheme}, models)


def sonic(*models):
    """SONIC's ZingORAM with the recursive oblivious position map, top table limit C = 2,048 (every measured
    SONIC row; the worker's default is 4,096, which is 1.25-1.9x slower at 2^16, 2^20 and 2^24)."""
    return candidate("sonic_zingoram_recursive",
                     {"scheme": "sonic_zingoram_recursive", "sonic": {"map_top_entries": 2048}}, models)


def model(shape, api, access_ns, setup_ns_per_entry, reference, exponent_ppm, coverage_ppm, widths=True):
    """A trial_time model: windows of coverage_ppm/10^6 accesses per entry at access_ns each (at least the
    30 s base window), scaled by (capacity/reference)^(exponent/10^6)."""
    entry = {}
    if widths:
        entry.update(key_bytes=shape["key_bytes"], value_bytes=shape["value_bytes"])
    entry.update(api_mode=api, access_ns=access_ns, setup_ns_per_entry=setup_ns_per_entry)
    if reference is not None:
        entry.update(reference_capacity=reference, capacity_exponent_ppm=exponent_ppm)
    entry["coverage_accesses_per_entry_ppm"] = coverage_ppm
    return entry


# ---------------------------------------------------------------------------------------------------------------
# Campaign pieces.
COUNTER = {"distribution": "counter"}


def instrumentation(*, buffer_bytes=256 * MIB, checkpoint_thread=False, checkpoint_interval_ns=None,
                    service_timing=False):
    block = {"logging": "histogram_checkpoints", "verification": "off"}
    if checkpoint_thread:
        block["checkpoint_thread"] = True
    block["buffer_bytes"] = buffer_bytes
    if checkpoint_interval_ns is not None:
        block["checkpoint_interval_ns"] = checkpoint_interval_ns
    if service_timing:
        block["service_timing"] = True
    return block


LATENCY_SCALAR = instrumentation(checkpoint_thread=True, checkpoint_interval_ns=SECOND)
LATENCY_BATCH = instrumentation(buffer_bytes=1 << 30, checkpoint_thread=True, checkpoint_interval_ns=SECOND,
                                service_timing=True)


def timing(*, settle, per_entry=False, setup_ns, max_trial_ns, measurement_ns=30 * SECOND,
           drain_ns=30 * SECOND):
    block = {"warmup_ns": 5 * SECOND, "settle_requests": settle}
    if per_entry:
        block["settle_per_entry_ppm"] = 1_000_000       # each row settles max(settle, N)
    block.update(measurement_ns=measurement_ns, setup_allowance_ns=setup_ns, drain_deadline_ns=drain_ns,
                 max_trial_ns=max_trial_ns)
    return block


def capacity_stage(name, shape, capacities, cand, api, *, stream, batch=None, kind="capacity", shapes=None):
    stage = {"name": name, "kind": kind, "shapes": copy.deepcopy(shapes or [shape]), "capacities": list(capacities),
             "candidates": [cand] if isinstance(cand, dict) else list(cand), "api_modes": [api]}
    if api == "batch":
        stage["batch_sizes"] = [batch or 64]
    stage.update(seed_role="screening", seed_stream=stream)
    return stage


def latency_stage(name, shape, n, cand, api, *, stream, fractions=(500000,), minimum=100000):
    """A saturated row, then fixed arrivals at each fraction of its drained rate; batch rows deliver each
    batch of 64 at one instant (arrive_together), so response runs from that arrival."""
    stage = {"name": name, "kind": "latency", "shapes": [copy.deepcopy(shape)], "capacities": [n],
             "candidates": [cand], "api_modes": [api]}
    if api == "batch":
        stage.update(batch_sizes=[64], batch_policy={"formation": "arrive_together"})
    stage.update(rates={"saturation_fractions_ppm": list(fractions), "minimum_ops_per_second": minimum},
                 seed_stream=stream)
    return stage


def row_count(stages):
    """Rows the planner expands (one repetition): shapes x capacities x candidates x API rows x rates."""
    total = 0
    for stage in stages:
        modes = (1 if "scalar" in stage["api_modes"] else 0) + (
            len(stage.get("batch_sizes", [64])) if "batch" in stage["api_modes"] else 0)
        count = len(stage["shapes"]) * len(stage["capacities"]) * len(stage["candidates"]) * modes
        if "rates" in stage:
            rates = stage["rates"]
            fractions = len(rates.get("saturation_fractions_ppm", []))
            count *= len(rates.get("absolute_ops_per_second", [])) + fractions + bool(fractions)
        total += count
    return total


def campaign(*, base_seed, stages, timing_block, instrumentation_block, trial_budget_ns=14 * DAY):
    return {"schema_version": 1, "name": None, "repetitions": 1, "base_seed": base_seed,
            "resources": None, "execution": None, "workload": dict(COUNTER),
            "instrumentation": dict(instrumentation_block), "timing": dict(timing_block),
            "stages": stages, "limits": {"max_trials": row_count(stages), "max_campaign_trial_ns": trial_budget_ns}}


def powers(low, high):
    return [1 << e for e in range(low, high + 1)]


# ---------------------------------------------------------------------------------------------------------------
# Items. Each returns the campaign body (name, resources and execution are filled per target).

# std::unordered_map window models of the two K4/V8 sweeps (access ns at 2^27, capacity exponent), per machine.
# Its rate differs by 2-2.6x between them at 2^30 (Intel 1.02 M / 4.13 M req/s, AMD 0.49 M / 1.59 M), so no
# one window holds N requests on AMD and still fits the 2^32 request horizon on Intel after a 2^30 settle:
# each target keeps its own sweep's model (the one documented exception to identical twin matrices).
UNORDERED_MAP_SWEEP_MODELS = {"c4": {"scalar": (800, 150000), "batch": (300, 150000)},
                              "oci": {"scalar": (1600, 350000), "batch": (600, 250000)}}


def throughput_k4v8(target):
    """Figure 7 (ours and std::unordered_map, K4/V8 dense, N = 2^16..2^30, one at a time and batches of 64)
    and Table 1's K4/V8 2^27 throughput cells. Closed loop; the 2^27 rows are the Intel headline gate.
    Ours: the AMD sweep's models on both targets (longer than the Intel sweep's at every N below 2^30 whose
    window exceeds 30 s). The hash map: each target's own sweep model (UNORDERED_MAP_SWEEP_MODELS). The 2^30
    batch row of ours has its own stage with 0.5 N coverage: settle 2^30 plus a 3 N window would exceed the
    2^32 request horizon; 0.5 N at the model rate still holds about 1.45 N at Intel's measured rate. 2 s checkpoints keep the 2^30 hash-map window under the worker's 4,096 blocks."""
    scalar = model(K4V8, "scalar", 1648, 36, N27, 94176, 1_000_000)
    batch = model(K4V8, "batch", 696, 103, N25, 96205, 1_000_000)
    batch_2p30 = model(K4V8, "batch", 696, 103, N25, 96205, 500_000)
    umap = UNORDERED_MAP_SWEEP_MODELS[target.split("-")[0]]
    stream = STREAM["k4v8"]
    stages = [
        capacity_stage("ours-scalar", K4V8, powers(16, 30), auto(scalar), "scalar", stream=stream),
        capacity_stage("ours-batch64", K4V8, powers(16, 29), parallel_8x8(batch), "batch", stream=stream),
        capacity_stage("ours-batch64-2p30", K4V8, [N30], parallel_8x8(batch_2p30), "batch", stream=stream),
        capacity_stage("floor", K4V8, powers(16, 30),
                       unordered_map(model(K4V8, "scalar", umap["scalar"][0], 500, N27, umap["scalar"][1],
                                           1_200_000)), "scalar", stream=stream),
        capacity_stage("floor-batch64", K4V8, powers(16, 30),
                       unordered_map(model(K4V8, "batch", umap["batch"][0], 500, N27, umap["batch"][1],
                                           1_200_000)), "batch", stream=stream),
    ]
    return campaign(base_seed=1001, stages=stages,
                    timing_block=timing(settle=SETTLE_FLOOR, per_entry=True, setup_ns=4 * HOUR,
                                        max_trial_ns=12 * HOUR),
                    instrumentation_block=instrumentation(checkpoint_interval_ns=2 * SECOND))


def table1_scalar():
    """Table 1, single requests: throughput (the saturated rows), response time at half of each system's own
    throughput (and at 0.8 for ours at K4/V8, the abstract's 80% figures) and memory (the saturated rows'
    peak RSS, which includes the 256 MiB event buffer). Ours (auto: the hierarchical ORAM at 8 and 48 B,
    the hybrid tree ORAM at 1 KiB) and std::unordered_map."""
    k4, k8, k32 = STREAM["k4v8"], STREAM["k8v48"], STREAM["k32v1024"]
    stages = [
        latency_stage("ours-k4v8", K4V8, N27, auto(model(K4V8, "scalar", 1648, 36, N27, 0, 1_000_000)), "scalar",
                      stream=k4, fractions=(500000, 800000)),
        latency_stage("ours-k8v48", K8V48, N25, auto(model(K8V48, "scalar", 3030, 300, N25, 0, 1_000_000)),
                      "scalar", stream=k8),
        latency_stage("ours-k32v1024", K32V1024, N21,
                      auto(model(K32V1024, "scalar", 5556, 10000, N21, 0, 1_000_000)), "scalar", stream=k32),
        latency_stage("umap-k4v8", K4V8, N27, unordered_map(model(K4V8, "scalar", 1600, 1000, N27, 0, 1_200_000)),
                      "scalar", stream=k4, minimum=1),
        latency_stage("umap-k8v48", K8V48, N25,
                      unordered_map(model(K8V48, "scalar", 1000, 500, N25, 0, 1_200_000)), "scalar", stream=k8,
                      minimum=1),
        latency_stage("umap-k32v1024", K32V1024, N21,
                      unordered_map(model(K32V1024, "scalar", 1500, 500, N21, 0, 1_200_000)), "scalar",
                      stream=k32, minimum=1),
    ]
    return campaign(base_seed=1001, stages=stages,
                    timing_block=timing(settle=SETTLE_FLOOR, per_entry=True, setup_ns=900 * SECOND,
                                        max_trial_ns=HOUR),
                    instrumentation_block=LATENCY_SCALAR, trial_budget_ns=2 * DAY)


def table1_batch():
    """Table 1, batches of 64: throughput (saturated rows) and the response time of whole batches arriving
    together at fixed intervals at half of each system's own batch throughput. Per-call service timing
    needs the 1 GiB event buffer, so these rows are a campaign of their own."""
    k4, k8, k32 = STREAM["k4v8"], STREAM["k8v48"], STREAM["k32v1024"]
    stages = [
        latency_stage("ours-k4v8", K4V8, N27,
                      parallel_8x8(model(K4V8, "batch", 322, 103, N27, 0, 1_000_000), batch_spin=True), "batch",
                      stream=k4),
        latency_stage("ours-k8v48", K8V48, N25,
                      parallel_8x8(model(K8V48, "batch", 1000, 300, N25, 0, 1_000_000), batch_spin=True), "batch",
                      stream=k8),
        latency_stage("ours-k32v1024", K32V1024, N21,
                      auto(model(K32V1024, "batch", 6250, 10000, N21, 0, 1_000_000)), "batch", stream=k32),
        latency_stage("umap-k4v8", K4V8, N27, unordered_map(model(K4V8, "batch", 457, 1000, N27, 0, 1_000_000)),
                      "batch", stream=k4, minimum=1),
        latency_stage("umap-k8v48", K8V48, N25,
                      unordered_map(model(K8V48, "batch", 400, 500, N25, 0, 1_200_000)), "batch", stream=k8,
                      minimum=1),
        latency_stage("umap-k32v1024", K32V1024, N21,
                      unordered_map(model(K32V1024, "batch", 700, 500, N21, 0, 1_200_000)), "batch", stream=k32,
                      minimum=1),
    ]
    return campaign(base_seed=1001, stages=stages,
                    timing_block=timing(settle=SETTLE_FLOOR, per_entry=True, setup_ns=900 * SECOND,
                                        max_trial_ns=HOUR),
                    instrumentation_block=LATENCY_BATCH, trial_budget_ns=2 * DAY)


OURS_WIDTHS = (8, 16, 32, 48, 64, 96, 128, 192, 256, 512, 1024)
WIDE = (2048, 4096)


def width_body(stages, measurement_ns=30 * SECOND):
    return campaign(base_seed=1001, stages=stages,
                    timing_block=timing(settle=N20, setup_ns=900 * SECOND, max_trial_ns=1800 * SECOND,
                                        measurement_ns=measurement_ns),
                    instrumentation_block=instrumentation(), trial_budget_ns=7 * DAY)


def width():
    """Figure 8 (a, b) and the memory panel (c): 2^20 records, 8-byte keys, one request at a time. The
    frozen-geometry hierarchy ('Ours, hierarchical ORAM') and the tree ('Ours, hybrid ORAM') at 8-1024 B
    (96 B brackets the crossover), the tree alone at 2 and 4 KiB. 30 s windows."""
    stream = STREAM["width"]
    stages = [
        capacity_stage("value-width", None, [N20], [hierarchy_frozen(), tree()], "scalar", stream=stream,
                       kind="value_width", shapes=[k8(v) for v in OURS_WIDTHS]),
        capacity_stage("tree-wide", None, [N20], [tree()], "scalar", stream=stream, kind="value_width",
                       shapes=[k8(v) for v in WIDE]),
    ]
    return width_body(stages)


def width_hierarchy_wide():
    """Figure 8: the frozen hierarchy at 2 and 4 KiB, with 300 s windows (at about 20-40 K req/s a 30 s
    window would hold well under N requests)."""
    stages = [capacity_stage("hierarchy-wide", None, [N20], [hierarchy_frozen()], "scalar", stream=STREAM["width"],
                             kind="value_width", shapes=[k8(v) for v in WIDE])]
    return width_body(stages, measurement_ns=300 * SECOND)


UMAP_WIDTHS = (8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096)


def width_std_unordered_map():
    """Figure 8's std::unordered_map curve: 2^20 records, 8-byte keys, 8 B to 4 KiB, one at a time; settle
    2^21, 30 s windows (many N at these rates). The paper quotes the fastest of several boots."""
    stages = [capacity_stage("value-width-std-unordered-map", None, [N20],
                             unordered_map(model(None, "scalar", 300, 500, None, 0, 1_200_000, widths=False)),
                             "scalar", stream=STREAM["width"], kind="value_width",
                             shapes=[k8(v) for v in UMAP_WIDTHS])]
    return campaign(base_seed=1001, stages=stages,
                    timing_block=timing(settle=N21, setup_ns=900 * SECOND, max_trial_ns=HOUR),
                    instrumentation_block=instrumentation(), trial_budget_ns=2 * DAY)


def tee():
    """The TEE-overhead pair at K4/V8 2^27: run on the protected VM and on the same VM type without
    protection, with the protected campaign's frozen worker. Single requests (auto) and batches of 64
    (8 x 8 tiles), as in Table 1. Both targets run both rows."""
    scalar = model(K4V8, "scalar", 1648, 36, N27, 94176, 1_000_000)
    batch = model(K4V8, "batch", 696, 103, N25, 96205, 1_000_000)
    stream = STREAM["tee"]
    stages = [
        capacity_stage("ours-scalar", K4V8, [N27], auto(scalar), "scalar", stream=stream),
        capacity_stage("ours-batch64", K4V8, [N27], parallel_8x8(batch), "batch", stream=stream),
    ]
    return campaign(base_seed=1001, stages=stages,
                    timing_block=timing(settle=N27, setup_ns=900 * SECOND, max_trial_ns=1800 * SECOND),
                    instrumentation_block=instrumentation(), trial_budget_ns=3 * HOUR)


def baseline_h2o2ram_table():
    """Table 1, H2O2RAM (patched, oblivious; single requests only): saturated throughput, the response at
    half of it, and peak memory, at the three Table 1 shapes. The K4/V8 half-rate window is about 2.5 h, so
    checkpoints are 4 s (worker limit: 4,096 blocks); the 120 s drain covers a top-level rebuild in flight."""
    stages = [
        latency_stage("h2o2ram-k4v8", K4V8, N27, h2o2ram(model(K4V8, "scalar", 16000, 1013, N27, 0, 2_100_000)),
                      "scalar", stream=STREAM["k4v8"], minimum=1),
        latency_stage("h2o2ram-k8v48", K8V48, N25, h2o2ram(model(K8V48, "scalar", 23810, 5153, N25, 0, 2_100_000)),
                      "scalar", stream=STREAM["k8v48"], minimum=1),
        latency_stage("h2o2ram-k32v1024", K32V1024, N21,
                      h2o2ram(model(K32V1024, "scalar", 250000, 38746, N21, 0, 2_100_000)), "scalar",
                      stream=STREAM["k32v1024"], minimum=1),
    ]
    return campaign(base_seed=7301, stages=stages,
                    timing_block=timing(settle=SETTLE_FLOOR, per_entry=True, setup_ns=4 * HOUR,
                                        max_trial_ns=24 * HOUR, drain_ns=120 * SECOND),
                    instrumentation_block=instrumentation(checkpoint_thread=True, checkpoint_interval_ns=4 * SECOND))


H2O2RAM_K4V8 = model(K4V8, "scalar", 10154, 1013, 1 << 22, 238125, 2_000_000)
H2O2RAM_SHIPPED_K4V8 = model(K4V8, "scalar", 9282, 1011, 1 << 22, 260651, 2_000_000)


def h2o2ram_throughput_body(cand, capacities):
    stages = [capacity_stage(cand["name"], K4V8, capacities, cand, "scalar", stream=STREAM["k4v8"])]
    return campaign(base_seed=7301, stages=stages,
                    timing_block=timing(settle=SETTLE_FLOOR, per_entry=True, setup_ns=4 * HOUR,
                                        max_trial_ns=24 * HOUR),
                    instrumentation_block=instrumentation(checkpoint_interval_ns=2 * SECOND))


def baseline_h2o2ram_throughput():
    """Figure 7's H2O2RAM curve (patched), K4/V8 dense, 2^16..2^27, closed loop, windows of 2 N (two top
    rebuilds). 2 s checkpoints keep the 2^27 window (about 1.7 h) under the worker's 4,096 blocks."""
    return h2o2ram_throughput_body(h2o2ram(H2O2RAM_K4V8), powers(16, 27))


def baseline_h2o2ram_shipped_throughput():
    """The published (shipped, not oblivious) H2O2RAM on the same rows and seeds, 2^16..2^26 (the measured
    range): the 'at most 26% faster than the patched build' comparison. Prepare with the patched worker,
    then resolve this campaign with the shipped worker beside the same planner cache."""
    return h2o2ram_throughput_body(h2o2ram(H2O2RAM_SHIPPED_K4V8, shipped=True), powers(16, 26))


# H2O2RAM per-width models at 2^20 (access and setup ns per entry), as fitted from pilot runs in
# ../c4-tdx-baseline-h2o2ram.json; the paper rows' windows held 2.1 N.
H2O2RAM_WIDTH_MODELS = {8: (7300, 729), 16: (8997, 1314), 32: (11707, 2764), 64: (19041, 5910),
                        128: (42039, 11705), 256: (96022, 23876), 512: (223346, 49469),
                        1024: (524408, 103332), 2048: (1237189, 216735)}


def h2o2ram_width_body(widths):
    shapes = [k8(v) for v in widths]
    models = [model(k8(v), "scalar", *H2O2RAM_WIDTH_MODELS[v], N20, 0, 2_100_000) for v in widths]
    stages = [capacity_stage("h2o2ram", None, [N20], h2o2ram(*models), "scalar", stream=STREAM["width"],
                             kind="value_width", shapes=shapes)]
    return campaign(base_seed=1001, stages=stages,
                    timing_block=timing(settle=N20, setup_ns=4 * HOUR, max_trial_ns=24 * HOUR),
                    instrumentation_block=instrumentation(checkpoint_interval_ns=2 * SECOND))


def baseline_h2o2ram_width():
    """Figure 8's H2O2RAM curve, 2^20 records, 8-byte keys, 8-512 B (Intel stops at 512 B: the next
    configuration search does not fit in the C4 guest's memory). On Intel, plan these widths on the C4
    guest itself, in a build directory of their own (its plans differ from the AMD ones at small widths)."""
    return h2o2ram_width_body((8, 16, 32, 64, 128, 256, 512))


def baseline_h2o2ram_width_large():
    """AMD only: H2O2RAM at 1 and 2 KiB (on the 256 GB guest; the measured 2 KiB row failed an H2O2RAM
    assertion in its bipartite matcher)."""
    return h2o2ram_width_body((1024, 2048))


def sonic_table_body(api):
    batch = api == "batch"
    rows = ((K4V8, N27, 25600, 250_000, "k4v8"), (K8V48_DENSE, N25, 25000, 500_000, "k8v48"),
            (K8V1024_DENSE, N21, 33000, 1_100_000, "k32v1024"))
    stages = [latency_stage(f"sonic-{key}", shape, n,
                            sonic(model(shape, api, batch_ns if batch else 50000, 50000, n, 0, coverage)), api,
                            stream=STREAM[key], minimum=1)
              for shape, n, batch_ns, coverage, key in rows]
    block = instrumentation(buffer_bytes=(1 << 30) if batch else 256 * MIB, checkpoint_thread=True,
                            checkpoint_interval_ns=4 * SECOND, service_timing=batch)
    return campaign(base_seed=7301, stages=stages,
                    timing_block=timing(settle=SETTLE_FLOOR, setup_ns=8 * HOUR, max_trial_ns=16 * HOUR),
                    instrumentation_block=block)


def baseline_sonic_table_scalar():
    """Table 1, SONIC single requests at the three Table 1 shapes (8-byte dense keys at 48 B and 1 KiB):
    saturated throughput and the response at half of it. Settle 2^21 (SONIC has no rebuild cycle); windows
    0.25 N (2^27), 0.5 N (2^25) and 1.1 N (2^21). Filling 2^27 records takes about an hour."""
    return sonic_table_body("scalar")


def baseline_sonic_table_batch():
    """Table 1, SONIC batches of 64 (SONIC splits a batch over its 8 access threads in windows of 8):
    saturated throughput, peak memory (with the 1 GiB service-timing buffer) and the response of whole
    batches arriving together at half of the batch throughput."""
    return sonic_table_body("batch")


def baseline_sonic_throughput():
    """Figure 7's SONIC curves, K4/V8 dense, 2^16..2^27, one at a time and batches of 64, closed loop.
    Settle 2^21, windows 0.5 N (at least 30 s)."""
    models = (model(K4V8, "scalar", 19400, 19400, N21, 300000, 500_000),
              model(K4V8, "batch", 10300, 19400, N21, 300000, 500_000))
    stream = STREAM["k4v8"]
    stages = [capacity_stage("sonic-scalar", K4V8, powers(16, 27), sonic(*models), "scalar", stream=stream),
              capacity_stage("sonic-batch64", K4V8, powers(16, 27), sonic(*models), "batch", stream=stream)]
    return campaign(base_seed=7301, stages=stages,
                    timing_block=timing(settle=SETTLE_FLOOR, setup_ns=8 * HOUR, max_trial_ns=16 * HOUR),
                    instrumentation_block=instrumentation(checkpoint_interval_ns=4 * SECOND))


# Figure 8 SONIC: the slower of the two machines' measured single-request rates at 2^20 (req/s); each width's
# model allows 1.5x that time per access, with windows of 1.1 N and one access per entry to fill.
SONIC_WIDTH_RATES = {8: 53513, 16: 53069, 32: 52151, 64: 51742, 128: 49137, 256: 43627, 512: 39692,
                     1024: 27195, 2048: 19167, 4096: 12249}


def baseline_sonic_width():
    """Figure 8's SONIC curve: 2^20 records, 8-byte dense keys, 8 B to 4 KiB, one at a time, C = 2,048."""
    widths = sorted(SONIC_WIDTH_RATES)
    models = []
    for v in widths:
        access = math.ceil(1.5e9 / SONIC_WIDTH_RATES[v])
        models.append(model(k8(v, dense=True), "scalar", access, access, None, 0, 1_100_000))
    stages = [capacity_stage("sonic-scalar", None, [N20], sonic(*models), "scalar", stream=STREAM["width"],
                             kind="value_width", shapes=[k8(v, dense=True) for v in widths])]
    return campaign(base_seed=1001, stages=stages,
                    timing_block=timing(settle=N21, setup_ns=8 * HOUR, max_trial_ns=16 * HOUR),
                    instrumentation_block=instrumentation(checkpoint_interval_ns=4 * SECOND))


# item -> (builder, targets). H2O2RAM presets take the 256 GB resources on the SNP target (presets()).
ITEMS = {
    "throughput-k4v8": (throughput_k4v8, PROTECTED),
    "table1-scalar": (table1_scalar, PROTECTED),
    "table1-batch": (table1_batch, PROTECTED),
    "width": (width, PROTECTED),
    "width-hierarchy-wide": (width_hierarchy_wide, PROTECTED),
    "width-std-unordered-map": (width_std_unordered_map, PROTECTED),
    "tee": (tee, tuple(TARGETS)),
    "baseline-h2o2ram-table": (baseline_h2o2ram_table, PROTECTED),
    "baseline-h2o2ram-throughput": (baseline_h2o2ram_throughput, PROTECTED),
    "baseline-h2o2ram-shipped-throughput": (baseline_h2o2ram_shipped_throughput, PROTECTED),
    "baseline-h2o2ram-width": (baseline_h2o2ram_width, PROTECTED),
    "baseline-h2o2ram-width-large": (baseline_h2o2ram_width_large, ("oci-zen5-snp",)),
    "baseline-sonic-table-scalar": (baseline_sonic_table_scalar, PROTECTED),
    "baseline-sonic-table-batch": (baseline_sonic_table_batch, PROTECTED),
    "baseline-sonic-throughput": (baseline_sonic_throughput, PROTECTED),
    "baseline-sonic-width": (baseline_sonic_width, PROTECTED),
}
# Items whose body depends on the target (beyond name, resources and execution); their builders take it.
PER_TARGET = ("throughput-k4v8",)


def presets():
    """{file stem: campaign} for every paper preset, in a fixed order."""
    out = {}
    for item, (build, targets) in ITEMS.items():
        for target in targets:
            body = build(target) if item in PER_TARGET else build()
            resources, execution = TARGETS[target]
            if item.startswith("baseline-h2o2ram") and target == "oci-zen5-snp":
                resources = E6_256GB_RESOURCES
            name = f"{target}-{item}"
            body.update(name=name, resources=dict(resources), execution=dict(execution))
            out[name] = body
    return dict(sorted(out.items()))


def render(data):
    return json.dumps(data, indent=2) + "\n"


# ---------------------------------------------------------------------------------------------------------------
# Rehearsal copies: the same matrices, scaled to run natively on a development host in minutes.
REHEARSAL_MIN, REHEARSAL_MAX = 1 << 12, 1 << 16


def rehearsal_capacity(capacity):
    """2^27 -> 2^16; 2^24..2^27 map to 2^13..2^16, larger capacities to 2^16 too; 2^23 and below -> 2^12."""
    return max(REHEARSAL_MIN, min(REHEARSAL_MAX, capacity >> 11))


def rehearsal(data, physical_cores, host_memory_bytes):
    """A native copy for an end-to-end local check: capacities at most 2^16, 1 s warmup and 2 s base
    windows, verification on, 30 s drains, a small settle (at least N where the preset settles max(N, 2^21)
    per row; a fixed settle is scaled down), the host's core budget and one L3 domain; seeds, candidates,
    models and batch policies are unchanged."""
    d = copy.deepcopy(data)
    d["name"] = f"rehearsal-{data['name']}"
    resources = {"physical_cores": physical_cores, "smt": False, "required_cache_domains": 1,
                 "host_memory_limit_bytes": host_memory_bytes, "placement": "near_far"}
    if "spin_before_park_ns" in data["resources"]:
        resources["spin_before_park_ns"] = data["resources"]["spin_before_park_ns"]
    d["resources"] = resources
    d["execution"] = {"runtime": "native", "require_protected": False}
    d["instrumentation"]["verification"] = "full"
    t = d["timing"]
    t.update(warmup_ns=SECOND, measurement_ns=2 * SECOND, drain_deadline_ns=30 * SECOND,
             setup_allowance_ns=120 * SECOND, max_trial_ns=600 * SECOND)
    if t.get("settle_requests"):
        t["settle_requests"] = min(t["settle_requests"], 4096)
    for stage in d["stages"]:
        stage["capacities"] = sorted({rehearsal_capacity(c) for c in stage["capacities"]})
        if "rates" in stage:
            stage["rates"]["minimum_ops_per_second"] = 1
        if physical_cores < 16:
            for cand in stage["candidates"]:
                if cand["overrides"]["scheme"].startswith("sonic"):
                    # SONIC's eviction pool (8) plus its 8 batch access threads need more slots than this
                    # budget; a scalar row has exactly one access thread (the caller).
                    cand["overrides"]["sonic"]["eviction_threads"] = 4
                    if stage["api_modes"] == ["batch"]:
                        cand["overrides"]["sonic"]["access_threads"] = 4
    d["limits"] = {"max_trials": row_count(d["stages"]),
                   "max_campaign_trial_ns": 2 * row_count(d["stages"]) * t["max_trial_ns"]}
    return d


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="compare the committed files with a fresh generation")
    mode.add_argument("--rehearsal", metavar="OUT", help="write scaled native copies of every preset into OUT")
    parser.add_argument("--physical-cores", type=int, default=16, help="rehearsal core budget (default 16)")
    parser.add_argument("--host-memory-bytes", type=int, default=16 << 30,
                        help="rehearsal host_memory_limit_bytes (default 16 GiB)")
    args = parser.parse_args(argv)
    generated = presets()
    if args.check:
        problems = []
        for name, data in generated.items():
            path = HERE / f"{name}.json"
            if not path.exists():
                problems.append(f"missing {path.name}")
            elif path.read_text() != render(data):
                problems.append(f"differs {path.name}")
        extra = sorted(p.name for p in HERE.glob("*.json") if p.stem not in generated)
        problems += [f"not generated {name}" for name in extra]
        for line in problems:
            print(line, file=sys.stderr)
        print(f"{len(generated)} presets, {len(problems)} problems")
        return 1 if problems else 0
    if args.rehearsal:
        out = Path(args.rehearsal)
        out.mkdir(parents=True, exist_ok=True)
        for name, data in generated.items():
            copy_ = rehearsal(data, args.physical_cores, args.host_memory_bytes)
            (out / f"{copy_['name']}.json").write_text(render(copy_))
        print(f"wrote {len(generated)} rehearsal presets to {out}")
        return 0
    for path in HERE.glob("*.json"):
        if path.stem not in generated:
            path.unlink()
    for name, data in generated.items():
        (HERE / f"{name}.json").write_text(render(data))
    print(f"wrote {len(generated)} presets to {HERE}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
