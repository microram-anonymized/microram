"""One offline preflight: topology and resolution, never a launch.

`run` applies the same topology check before a native launch and the attempt
check to every native attempt (`topology_check`, `attempt_check`).

The runtime section compares the campaign's runtime with the evidence's label
and the doctor's `runtime:` contract (what the guest kernel shows).
Topology counts are the doctor's `--require-physical-cores/--require-cache-domains`
contract, and slot validity is the C++ worker's `--cpu-ids` check. This module
keeps only what neither covers: the campaign's core/domain request against the
saved environment, each row's memory estimate against the environment's memory,
and, for a worker's saved resolved.json, its configuration key and the
nested-helper locality of its placement. Nothing is written; the per-attempt
memory_preflight.json is the only retained admission record.
"""
from pathlib import Path

from .codec import decode, load_json, plain
from .schema import Environment, WorkerResolution

ONLINE_HELPER_ROLES = (2, 6)  # kOnlineHelper, kPositionOnlineHelper


def _topology(resources, environment):
    rejected, missing = [], []
    if environment.runtime == "fake":
        rejected.append("synthetic_environment")
    if resources["smt"]:
        rejected.append("smt_experiment_not_supported")
    missing.extend(reason for reason in environment.missing_evidence
                   if reason.startswith(("topology:", "topology_contract:")))
    # A compiled-in extension the host does not expose faults the worker.
    if any(reason.startswith("isa:not_exposed:") for reason in environment.missing_evidence):
        rejected.append("compiled_isa_not_exposed")
    missing.extend(reason for reason in environment.missing_evidence
                   if reason in ("isa:compiled_set_unknown", "isa:host_flags_unknown"))
    if environment.physical_cores is None:
        missing.append("exposed_physical_core_count")
    elif environment.physical_cores < resources["physical_cores"]:
        rejected.append("insufficient_exposed_physical_cores")
    # A declared idle-wait instruction (umwait/mwaitx) must be one the host exposes.
    wait = {"umwait": "waitpkg", "mwaitx": "monitorx"}.get(resources.get("monitor_wait", "none"))
    if wait is not None:
        if environment.cpu_flags is None:
            missing.append("cpu_flags")
        elif wait not in environment.cpu_flags:
            rejected.append("monitor_wait_not_exposed")
    domains = resources["required_cache_domains"]
    if environment.cache_domains is None:
        missing.append("exposed_cache_domains")
    elif domains is not None and len(environment.cache_domains) != domains:
        rejected.append("exposed_cache_domain_count_mismatch")
    return {"status": "incompatible" if rejected else "insufficient_evidence" if missing else "compatible",
            "rejection_reasons": sorted(set(rejected)), "missing_evidence": sorted(set(missing))}


def _runtime(execution, environment):
    """The campaign's runtime against the saved evidence's label and TEE detection.

    A tdx or snp run also needs this boot's attestation capture, which only
    `run` can check (the capture is bound to the live boot and class).
    """
    rejected = []
    if environment.runtime != "fake":
        if environment.runtime != execution["runtime"]:
            rejected.append("runtime_differs_from_campaign")
        rejected.extend(reason.removeprefix("runtime:") for reason in environment.missing_evidence
                        if reason.startswith("runtime:"))
    return {"status": "incompatible" if rejected else "compatible", "rejection_reasons": sorted(set(rejected))}


def _memory(plan, resolved, environment):
    limit = environment.memory_limit_bytes
    exceeding, fitting = [], 0
    for row in plan["trials"]:
        entry = resolved[row["trial_id"]]
        if entry["status"] != "runnable":
            continue
        headroom = row["spec"]["resources"]["headroom_ppm"]
        usable = None if limit is None else limit * (1_000_000 - headroom) // 1_000_000
        if usable is not None and entry["estimated_memory_bytes"] > usable:
            exceeding.append({"trial_id": row["trial_id"], "estimated_bytes": entry["estimated_memory_bytes"],
                              "usable_bytes": usable})
        else:
            fitting += 1
    return {"status": "unknown" if limit is None else "exceeds_budget" if exceeding else "within_estimated_budget",
            "environment_memory_limit_bytes": limit, "runnable_within_estimate": fitting,
            "exceeding": exceeding,
            "note": "Estimates are modelled requested bytes plus known worker buffers, not a certified peak."}


def helper_locality(environment, resolved, placement):
    """Online helpers must share the caller's exposed L3 under near_far placement."""
    rejected, missing = [], []
    topology = environment.topology
    by_cpu = {entry.cpu: entry for entry in topology.cpus} if topology is not None else {}
    caller = by_cpu.get(resolved.threads[0].cpu) if resolved.threads else None
    for thread in resolved.threads:
        if thread.role not in ONLINE_HELPER_ROLES or placement != "near_far":
            continue
        entry = by_cpu.get(thread.cpu)
        if entry is None or caller is None or entry.l3_cpus is None or caller.l3_cpus is None:
            missing.append("online_helper_locality")
        elif entry.l3_cpus != caller.l3_cpus:
            rejected.append("online_helper_outside_caller_l3")
    return rejected, missing


def _attempt(row, entry, environment, resolved):
    rejected, missing = [], []
    if entry["status"] != "runnable":
        rejected.append("trial_not_runnable:" + entry["status"])
    elif resolved.configuration_key != entry["configuration_key"]:
        rejected.append("configuration_key_differs_from_resolution")
    resources = row["spec"]["resources"]
    if resources["placement"] == "unplaced":
        if resolved.placement_policy != "unplaced":
            rejected.append("requested_unplaced_policy_mismatch")
    elif resolved.placement_policy == "unplaced":
        rejected.append("requested_near_far_placement_missing")
    locality_rejected, locality_missing = helper_locality(environment, resolved, resources["placement"])
    rejected += locality_rejected
    missing += locality_missing
    return {"trial_id": row["trial_id"],
            "status": "incompatible" if rejected else "insufficient_evidence" if missing else "compatible",
            "rejection_reasons": sorted(set(rejected)), "missing_evidence": sorted(set(missing)),
            "cpu_slots": resolved.cpu_slots}


def topology_check(resources, environment):
    """The campaign's core/domain request against a native host's evidence (run gate)."""
    return plain(_topology(resources, decode(Environment, environment)))


def attempt_check(row, entry, environment, resolved):
    """One native attempt's resolved.json against resolution.json and its placement."""
    return plain(_attempt(row, entry, decode(Environment, environment), decode(WorkerResolution, resolved)))


def preflight(campaign, environment_path, trial_id=None, resolved_path=None):
    from .campaign import read_plan
    from .codec import require
    from .resolution import entries, read_resolution

    require((trial_id is None) == (resolved_path is None), "--trial-id and --resolved go together")
    campaign = Path(campaign)
    plan = read_plan(campaign)
    resolved_entries = entries(read_resolution(campaign, plan))
    environment = decode(Environment, load_json(environment_path))
    resources = plan["campaign"]["resources"]
    result = {"plan_id": plan["plan_id"], "environment_class": environment.environment_class,
              "runtime": _runtime(plan["campaign"]["execution"], environment),
              "topology": _topology(resources, environment),
              "memory": _memory(plan, resolved_entries, environment),
              "attempt": None}
    if trial_id is not None:
        row = next((row for row in plan["trials"] if row["trial_id"] == trial_id), None)
        require(row is not None, "trial ID absent from immutable campaign")
        resolved = decode(WorkerResolution, load_json(resolved_path))
        result["attempt"] = _attempt(row, resolved_entries[trial_id], environment, resolved)
    statuses = [result["runtime"]["status"], result["topology"]["status"], result["memory"]["status"]]
    if result["attempt"] is not None:
        statuses.append(result["attempt"]["status"])
    result["status"] = ("incompatible" if any(s in ("incompatible", "exceeds_budget") for s in statuses) else
                        "compatible" if all(s in ("compatible", "within_estimated_budget") for s in statuses) else
                        "insufficient_evidence")
    return plain(result)
