"""Bounded, deterministic expansion only: no subprocesses or measurement hooks."""

import hashlib
import itertools
import os
from pathlib import Path
import tempfile

from .codec import canonical, decode, identity, load_json, plain, require
from .schema import INDEX_ORAM_SCHEMES, Campaign, security_label

# Baselines without a batch API; the resolver refuses rather than emulating one.
SCALAR_ONLY_SCHEMES = ("h2o2ram", "h2o2ram_shipped")
SONIC_SCHEMES = ("sonic_zingoram", "sonic_zingoram_recursive")


def stored_value_bytes(scheme, value_bytes):
    """The value width a backend stores (memory is billed at it). ZingORAM blocks are multiples of 8 bytes."""
    return -(-value_bytes // 8) * 8 if scheme in SONIC_SCHEMES else value_bytes


def timed(spec, model, live):
    """The row's window and estimated trial time under its arm's model (the per-arm time cap).

    Returns (spec, estimated_ns): the spec's measurement window grows to hold
    the coverage window; None when the candidate has no model. An offered-load
    row issues its accesses at the offered rate, not the arm's saturation
    rate, so its window is that many accesses at the slower of the two; a
    saturation fraction f of a rate 1/access_ns takes access_ns / f each.
    """
    if model is None:
        return spec, None
    timing, capacity, rate = spec["timing"], spec["requested_capacity"], spec.get("rate")
    accesses = -(-model.coverage_accesses_per_entry_ppm * capacity // 1_000_000)
    coverage = model.scaled(accesses * model.access_ns, capacity)
    if rate is not None and rate["kind"] == "absolute":
        coverage = max(coverage, -(-accesses * 10**9 // rate["ops_per_second"]))
    elif rate is not None:
        coverage = -(-coverage * 1_000_000 // rate["fraction_ppm"])
    window = max(timing["measurement_ns"], coverage)
    warmup = timing["warmup_ns"] + (timing["drain_deadline_ns"] if timing["warmup_ns"] else 0)
    setup = model.setup_ns + model.scaled(model.setup_ns_per_entry * live, capacity)
    estimate = setup + warmup + window + timing["drain_deadline_ns"]
    if window != timing["measurement_ns"]:
        spec = {**spec, "timing": {**timing, "measurement_ns": window}}
    return spec, estimate


def row_settle_requests(timing, capacity):
    """A row's settle: the campaign's settle_requests, raised to settle_per_entry_ppm of its capacity when set."""
    ppm = timing.settle_per_entry_ppm
    if ppm is None:
        return timing.settle_requests
    return max(timing.settle_requests, -(-capacity * ppm // 1_000_000))


def baseline_skip_reasons(spec):
    """Rows a baseline cannot run, known before resolution: index ORAMs cannot report a
    miss and SONIC needs dense keys as its indices; scalar-only baselines have no batch API."""
    scheme, reasons = spec["overrides"]["scheme"], []
    if scheme in INDEX_ORAM_SCHEMES and spec["workload"]["hit_ppm"] != 1_000_000:
        reasons.append("index_oram_cannot_report_misses")
    if scheme in SCALAR_ONLY_SCHEMES and spec["api_mode"] != "scalar":
        reasons.append("unsupported_api_mode")
    if scheme in SONIC_SCHEMES and spec["shape"].get("key_layout", "permuted") != "dense":
        reasons.append("sonic_needs_dense_keys")
    return reasons


def _seed(base, repetition, purpose, stream=None):
    # A stage's own stream is appended; without one the derivation is unchanged.
    key = [base, repetition, purpose] + ([] if stream is None else [stream])
    return int.from_bytes(hashlib.sha256(canonical(key)).digest()[:8], "big")


def _stage_seeds(campaign, stage, repetition):
    return {"workload_seed": _seed(campaign.base_seed, repetition, "workload-v1", stage.seed_stream),
            "arrival_seed": _seed(campaign.base_seed, repetition, "arrival-v1", stage.seed_stream)}


def _check_held_out_seeds(campaign):
    """A held-out row must not replay a screening row's workload or arrivals."""
    def seeds(stage):
        return {item for repetition in range(campaign.repetitions)
                for item in _stage_seeds(campaign, stage, repetition).items()}
    screening = [(stage.name, seeds(stage)) for stage in campaign.stages if stage.seed_role == "screening"]
    for stage in campaign.stages:
        if stage.seed_role == "held_out":
            held_out = seeds(stage)
            for name, used in screening:
                require(not held_out & used, f"held_out stage {stage.name!r} shares seeds with screening "
                        f"stage {name!r}; give it its own seed_stream")


def _row_count(stage, repetitions):
    modes = (1 if "scalar" in stage.api_modes else 0) + (
        len(stage.batch_sizes) if "batch" in stage.api_modes else 0)
    count = len(stage.shapes) * len(stage.capacities) * len(stage.candidates) * modes * repetitions
    if stage.rates:
        count *= (len(stage.rates.absolute_ops_per_second) + len(stage.rates.saturation_fractions_ppm) +
                  bool(stage.rates.saturation_fractions_ppm))
    return count


def expand(campaign):
    # Also validates callers that construct dataclasses directly, including all defaults.
    campaign = decode(Campaign, plain(campaign))
    # Smoke is the correctness evidence, so it always verifies.
    require(campaign.instrumentation.verification == "full" or
            all(stage.kind != "smoke" for stage in campaign.stages),
            "verification off is not allowed in a campaign with a smoke stage")
    count = sum(_row_count(stage, campaign.repetitions) for stage in campaign.stages)
    require(count <= campaign.limits.max_trials,
            f"matrix has {count} trials, exceeds max_trials={campaign.limits.max_trials}")
    maximum_ns = count * campaign.timing.max_trial_ns
    _check_held_out_seeds(campaign)
    common = {name: plain(getattr(campaign, name)) for name in
              ("workload", "timing", "instrumentation", "resources", "execution")}
    # Present only when on, so rows without it hash as before it existed.
    if not common["instrumentation"]["checkpoint_thread"]:
        del common["instrumentation"]["checkpoint_thread"]
    if common["resources"]["spin_before_park_ns"] is None:
        del common["resources"]["spin_before_park_ns"]
    if common["timing"]["settle_per_entry_ppm"] is None:
        del common["timing"]["settle_per_entry_ppm"]
    rows = []

    def add(spec, dependencies=None, model=None):
        if spec["arrival"] == "saturated" and "checkpoint_thread" in spec["instrumentation"]:
            # Saturated trials keep no checkpoint blocks, so the option does nothing there.
            spec = {**spec, "instrumentation": {k: v for k, v in spec["instrumentation"].items()
                                                if k != "checkpoint_thread"}}
        capacity = spec["requested_capacity"]
        # The row's own settle (settle_per_entry_ppm); the worker reads it from the spec.
        settle = row_settle_requests(campaign.timing, capacity)
        if settle != spec["timing"]["settle_requests"]:
            spec = {**spec, "timing": {**spec["timing"], "settle_requests": settle}}
        live = capacity * campaign.workload.occupancy_ppm // 1_000_000
        spec, estimated_ns = timed(spec, model, live)
        trial_id = identity("trial-v1", spec)
        widths = spec["shape"]
        logical_bytes = live * (widths["key_bytes"] + widths["value_bytes"])
        reasons = []
        if live == 0:
            reasons.append("occupancy_rounds_to_zero")
        # Avoid allocating an integer with an unbounded key_bytes shift.
        key_count = live + campaign.workload.miss_key_count
        if (key_count - 1).bit_length() > widths["key_bytes"] * 8:
            reasons.append("insufficient_disjoint_key_space")
        # Direct hierarchy initialization need not issue N online calls. Only
        # charge the known insertion lower bound when tree is explicitly pinned.
        minimum_fill_calls = live if spec["overrides"]["scheme"] == "tree" else 0
        if minimum_fill_calls + settle >= campaign.timing.max_accesses:
            reasons.append("access_horizon_cannot_cover_required_fill_and_settle")
        if logical_bytes >= 2**64:
            reasons.append("logical_dataset_exceeds_uint64_byte_range")
        reasons += baseline_skip_reasons(spec)
        if estimated_ns is not None and estimated_ns > spec["timing"]["max_trial_ns"]:
            reasons.append("trial_time_cap")
        # Memory limits are checked by `resolve` against the resolver's modelled
        # bytes (resolution.json), not against logical record bytes here.
        pending = ["library_resolution", "allocation_peak_estimate", "runtime_and_topology_verification",
                   "access_horizon_and_cycle_coverage", "raw_storage_and_fill_cost_pilot"]
        if dependencies:
            pending.append("freeze_saturation_derived_rate")
        for name in ("source_identity", "build_identity", "dependency_identity"):
            if getattr(campaign.execution, name) is None:
                pending.append(name)
        scheme = spec["overrides"]["scheme"]
        rows.append({"trial_id": trial_id, "spec": spec, "dependencies": dependencies or [],
                     "planning_status": "skipped" if reasons else "deferred",
                     "skip_reasons": reasons, "deferred_reasons": [] if reasons else pending,
                     # The baseline comparison's row labels (README.md, Baselines).
                     "security": security_label(scheme), "key_layout": widths["key_layout"],
                     "stored_value_bytes": stored_value_bytes(scheme, widths["value_bytes"]),
                     "live_entries": live, "actual_capacity": None, "estimated_trial_ns": estimated_ns,
                     "logical_dataset_bytes": logical_bytes if logical_bytes < 2**64 else None,
                     "estimated_peak_bytes": None,
                     "estimated_raw_bytes": None, "estimated_fill_ns": None,
                     "resolved_plan_id": None})
        return trial_id

    for stage in campaign.stages:
        modes = []
        if "scalar" in stage.api_modes:
            modes.append(("scalar", 1))
        if "batch" in stage.api_modes:
            modes.extend(("batch", size) for size in stage.batch_sizes)
        for shape, capacity, candidate, (mode, batch_size) in itertools.product(
                stage.shapes, stage.capacities, stage.candidates, modes):
            base = {"schema_version": 1, **common, "stage": stage.name, "kind": stage.kind,
                    "shape": plain(shape), "requested_capacity": capacity,
                    "candidate": candidate.name, "overrides": plain(candidate.overrides),
                    "api_mode": mode, "caller_batch_size": batch_size,
                    "batch_policy": plain(stage.batch_policy) if mode == "batch" else
                    {"formation": "fixed_count", "timeout_ns": None}}
            if stage.diagnostic:  # absent otherwise, so existing trial ids are unchanged
                base["diagnostic"] = True
            # Independent of scheme, scalar/batch mode, and offered rate.
            specs = [{**base, "repetition": repetition, **_stage_seeds(campaign, stage, repetition)}
                     for repetition in range(campaign.repetitions)]
            model = candidate.trial_time_model(plain(shape), mode)
            if stage.rates is None:
                for spec in specs:
                    add({**spec, "arrival": "saturated", "rate": None}, model=model)
                continue
            sources = []
            if stage.rates.saturation_fractions_ppm:
                for spec in specs:
                    # Timeout formation has no meaning without arrivals. Keep the
                    # requested latency policy as provenance for the matched source.
                    sources.append(add({**spec, "purpose": "saturation_source",
                                        "arrival": "saturated", "rate": None}, model=model))
            rates = [{"kind": "absolute", "ops_per_second": rate} for rate in
                     stage.rates.absolute_ops_per_second]
            rates += [{"kind": "saturation_fraction", "fraction_ppm": fraction,
                       "ops_per_second": None, "source_trial_ids": sources,
                       "reduction": "median_drained_ops_per_second_floor_v1",
                       "minimum_ops_per_second": stage.rates.minimum_ops_per_second}
                      for fraction in stage.rates.saturation_fractions_ppm]
            for rate, spec in itertools.product(rates, specs):
                add({**spec, "arrival": "fixed", "rate": rate},
                    sources if rate["kind"] == "saturation_fraction" else [], model=model)

    require(len({r["trial_id"] for r in rows}) == len(rows), "duplicate logical trials")
    # Every trial may be retried after a worker failure. A row with a
    # trial-time model is bounded by its estimate (which the cap check already
    # admitted), a row without one by the cap, so a long cap does not bill
    # every fast row its full cap; skipped rows never launch.
    bounded_ns = sum(campaign.timing.max_trial_ns if row["estimated_trial_ns"] is None else
                     row["estimated_trial_ns"] for row in rows if row["planning_status"] != "skipped")
    retried_ns = bounded_ns * (1 + campaign.limits.planned_retries)
    require(retried_ns <= campaign.limits.max_campaign_trial_ns,
            "sum of trial time bounds with planned retries exceeds max_campaign_trial_ns; "
            "reduce matrix, trial caps or planned_retries")
    # Hash-sort is stable across Python versions and independent of input matrix order.
    # Sources precede consumers, and each class is deterministically shuffled.
    rows.sort(key=lambda row: (bool(row["dependencies"]),
              identity("order", [campaign.order_seed, row["trial_id"]])))
    record = plain(campaign)
    # Like the specs: an unset per-row settle is left out, so the plan identity predates the field.
    if record["timing"]["settle_per_entry_ppm"] is None:
        del record["timing"]["settle_per_entry_ppm"]
    plan = {"schema_version": 1, "planner_version": "oram_bench_plan_v1",
            "campaign": record, "trials": rows,
            "cost": {"trial_count": len(rows), "trial_time_cap_sum_ns": maximum_ns,
                     "trial_time_bound_sum_ns": bounded_ns,
                     "planned_retries": campaign.limits.planned_retries,
                     "trial_time_bound_with_retries_sum_ns": retried_ns,
                     "warmup_and_measurement_sum_ns": count *
                     (campaign.timing.warmup_ns + campaign.timing.measurement_ns),
                     "estimated_total_raw_bytes": None, "estimated_total_fill_ns": None,
                     "note": "Time caps include the declared setup allowance; they exclude coordinator "
                             "overhead and preemption retries. Allocation, fill and storage need pilots."}}
    return {"plan_id": identity("plan-v1", plan), **plan}


def write_plan(plan, output):
    """Idempotent immutable plan publication; never replace a different plan."""
    directory = Path(output)
    from .store import durable_mkdir
    durable_mkdir(directory)
    destination = directory / "plan.json"
    payload = canonical(plan) + b"\n"
    # Hard-link publication fails atomically if another planner won the race.
    fd, temporary = tempfile.mkstemp(prefix=".plan-", dir=directory)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        try:
            os.link(temporary, destination)
        except FileExistsError:
            require(canonical(load_json(destination)) == canonical(plan),
                    f"{destination} already contains a different immutable plan; choose a new output")
        dir_fd = os.open(directory, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
        try:
            os.fsync(dir_fd)
        finally:
            os.close(dir_fd)
    finally:
        os.unlink(temporary)
