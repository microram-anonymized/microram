"""Harness-overhead gate records.

A record carries the target's measured gate evidence for one binding (worker
hash, environment class, shape, core placement, batch policy, arrival process
and rate range, logging mode) and the verdict gate_failures derives from the
measured quantiles. Records are reported evidence: they block and clear no
row (harness overhead is unstable and unavoidable, and charging it as a
publication blocker would only favor the slower prior schemes).
"""

from dataclasses import dataclass, field
import json
from pathlib import Path
from typing import Literal, Optional

from .codec import decode, load_json, plain, require
from .schema import ApiMode, BatchPolicy

# The logging budget: one-sided, 5%;
# a published mode faster than its control passes. Maxima are reported, never
# gated: a single sample cannot resolve such a change.
GATE_PPM = 50_000
GATED_QUANTILES = ("p50", "p99", "p999")


@dataclass(frozen=True)
class RateRange:
    minimum_ops_per_second: int
    maximum_ops_per_second: int

    def validate(self):
        require(0 < self.minimum_ops_per_second <= self.maximum_ops_per_second, "empty rate range")


@dataclass(frozen=True)
class Binding:
    worker_sha256: str
    environment_class: str
    key_bytes: int
    value_bytes: int
    physical_cores: int
    placement: Literal["near_far", "unplaced"]
    api_mode: ApiMode
    caller_batch_size: int
    batch_policy: BatchPolicy
    arrival: Literal["saturated", "fixed"]
    # None exactly for saturated rows; an offered row's frozen rate must lie inside.
    rate: Optional[RateRange]
    logging: Literal["full_events", "histogram_checkpoints"]
    verification: Literal["full", "off"]
    # Harness options that change what the request thread does; records made
    # before they existed bind the defaults.
    distribution: Literal["uniform", "counter"] = "uniform"
    checkpoint_thread: bool = False

    def validate(self):
        require((self.arrival == "saturated") == (self.rate is None), "a rate range binds offered rows only")
        require((self.api_mode == "scalar") == (self.caller_batch_size == 1), "scalar binds batch size 1")


@dataclass(frozen=True)
class QuantileChange:
    quantile: Literal["p50", "p99", "p999", "max", "mean_service"]
    control_ns: int
    instrumented_ns: int
    samples: int


@dataclass(frozen=True)
class Evidence:
    # logging_mode: the bound logging mode against a lighter control mode;
    # identical_arms: two runs of the bound mode (the null test).
    comparison: Literal["logging_mode", "identical_arms"]
    control_logging: Literal["full_events", "histogram_checkpoints"]
    changes: list[QuantileChange]
    harness_ns_per_request: int  # closed-loop no-op; reported, not gated
    events: int
    lost_events: int
    clock_read_ns: Optional[int] = None
    slew_ppb: Optional[int] = None
    cross_core_skew_ns: Optional[int] = None
    paths: list[str] = field(default_factory=list)


@dataclass(frozen=True)
class HarnessValidation:
    schema_version: Literal[1]
    status: Literal["passed", "failed"]
    binding: Binding
    evidence: Optional[Evidence]
    gate_ppm: int = GATE_PPM
    note: Optional[str] = None

    def validate(self):
        require(0 < self.gate_ppm <= GATE_PPM, "a record cannot loosen the 5% gate")


def gate_failures(record):
    """Why the record's own evidence does not pass; empty when it does."""
    evidence = record.evidence
    if record.status != "passed":
        return ["record_status_" + record.status]
    if evidence is None:
        return ["evidence_missing"]
    failures = []
    if evidence.lost_events:
        failures.append("lost_events")
    changes = {change.quantile: change for change in evidence.changes}
    for quantile in GATED_QUANTILES + ("max",):
        change = changes.get(quantile)
        if change is None or not change.samples or not change.control_ns:
            failures.append(quantile + "_evidence_missing")
        elif quantile != "max" and (change.instrumented_ns - change.control_ns) * 1_000_000 > \
                record.gate_ppm * change.control_ns:
            failures.append(quantile + "_over_gate")
    return failures


def row_binding(row, environment_class, worker_sha256, offered_ops_per_second):
    """The fields of one reduced row a record binds."""
    spec = row["spec"]
    return {"worker_sha256": worker_sha256, "environment_class": environment_class,
            "key_bytes": spec["shape"]["key_bytes"], "value_bytes": spec["shape"]["value_bytes"],
            "physical_cores": spec["resources"]["physical_cores"], "placement": spec["resources"]["placement"],
            "api_mode": spec["api_mode"], "caller_batch_size": spec["caller_batch_size"],
            "batch_policy": spec["batch_policy"], "arrival": spec["arrival"], "rate": offered_ops_per_second,
            "logging": spec["instrumentation"]["logging"],
            "verification": spec["instrumentation"].get("verification", "full"),
            "distribution": spec["workload"].get("distribution", "uniform"),
            "checkpoint_thread": spec["instrumentation"].get("checkpoint_thread", False)}


def _without(spec, names):
    return {k: v for k, v in spec.items() if k not in names}


def _change(quantile, control, instrumented):
    # Means arrive as floats from the worker and replay; records hold whole ns.
    ns = lambda value: None if value is None else round(value)
    return {"quantile": quantile, "control_ns": ns(control[1]), "instrumented_ns": ns(instrumented[1]),
            "samples": min(control[0], instrumented[0])}


def build_records(control, instrumented, comparison="logging_mode", harness_ns_per_request=None):
    """One record per instrumented group that has a matched control group.

    Both inputs are `reduce` summaries. Groups match on environment class and
    the whole spec, the logging mode aside for a logging comparison. Each
    group must hold one repetition (the one-trial policy); the verdict comes
    from gate_failures, never from the caller.
    """
    require(harness_ns_per_request is not None, "a record needs the closed-loop no-op harness ns/request")
    harness = harness_ns_per_request if callable(harness_ns_per_request) else lambda spec: harness_ns_per_request
    ignored = ("instrumentation",) if comparison == "logging_mode" else ()
    controls = {}
    for group in control["groups"]:
        key = (group["environment_class"], json.dumps(_without(group["spec"], ignored), sort_keys=True))
        controls[key] = group
    records, unmatched = [], []
    for group in instrumented["groups"]:
        key = (group["environment_class"], json.dumps(_without(group["spec"], ignored), sort_keys=True))
        twin = controls.get(key)
        if twin is None or len(group["repetitions"]) != 1 or len(twin["repetitions"]) != 1:
            unmatched.append(group["group_id"])
            continue
        mine, theirs = group["repetitions"][0], twin["repetitions"][0]
        spec = group["spec"]
        rate = mine["offered_ops_per_second"]
        binding = {**row_binding({"spec": spec}, group["environment_class"],
                                 instrumented["campaign"]["worker_sha256"], None),
                   "rate": None if rate is None else {"minimum_ops_per_second": rate,
                                                      "maximum_ops_per_second": rate}}
        pick = lambda record, kind, stat: (record["summary"][kind]["count"], record["summary"][kind][stat])
        changes = [_change(q, pick(theirs, "response", q + "_ns"), pick(mine, "response", q + "_ns"))
                   for q in ("p50", "p99", "p999")]
        changes.append(_change("max", pick(theirs, "response", "maximum_ns"), pick(mine, "response", "maximum_ns")))
        changes.append(_change("mean_service", pick(theirs, "service", "mean_ns"), pick(mine, "service", "mean_ns")))
        # An unavailable quantile (too few samples) is left out, which the gate reads as missing.
        changes = [c for c in changes if c["control_ns"] is not None and c["instrumented_ns"] is not None]
        evidence = {"comparison": comparison, "control_logging": twin["spec"]["instrumentation"]["logging"],
                    "changes": changes, "harness_ns_per_request": harness(spec),
                    # Only complete attempts reach a summary, and those lost no events.
                    "events": mine["summary"]["completed"], "lost_events": 0,
                    "paths": [mine["attempt_id"], theirs["attempt_id"]]}
        draft = decode(HarnessValidation, {"schema_version": 1, "status": "passed", "binding": binding,
                                           "evidence": evidence})
        failures = gate_failures(draft)
        records.append(plain(decode(HarnessValidation, {**plain(draft), "status": "failed" if failures else "passed",
                                                        "note": "; ".join(failures) or None})))
    return records, unmatched


def noop_harness(summary):
    """ns/request of a saturated no-op campaign, by API mode and caller batch size."""
    rates = {}
    for group in summary["groups"]:
        spec = group["spec"]
        if spec["arrival"] == "saturated" and spec["overrides"]["scheme"] in ("noop", "auto"):
            for repetition in group["repetitions"]:
                rate = repetition["summary"]["drained_ops_per_second"]
                key = (spec["api_mode"], spec["caller_batch_size"])
                rates[key] = max(rates.get(key, 0), rate)

    def lookup(spec):
        key = (spec["api_mode"], spec["caller_batch_size"])
        require(key in rates, f"no saturated no-op row for api {key[0]}, batch {key[1]}")
        return round(1e9 / rates[key])
    return lookup


def write_records(control_path, instrumented_path, output, comparison, harness_ns_per_request=None, noop_path=None):
    from .store import atomic_json
    require((harness_ns_per_request is None) != (noop_path is None), "give --harness-ns or --noop, not both")
    harness = harness_ns_per_request if noop_path is None else noop_harness(load_json(noop_path))
    records, unmatched = build_records(load_json(control_path), load_json(instrumented_path), comparison, harness)
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    paths = []
    for record in records:
        name = f"validation-{len(paths):04d}-{record['status']}.json"
        atomic_json(output / name, record)
        paths.append(str(output / name))
    return {"records": paths, "passed": sum(r["status"] == "passed" for r in records),
            "failed": sum(r["status"] == "failed" for r in records), "unmatched_groups": unmatched}
