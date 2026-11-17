"""Baseline-specific campaign steps (benchmarks/baselines/README.md).

`prepare-h2o2ram` runs H2O2RAM's host-timed planner once per distinct row of a
planned campaign, on the target and before `resolve`, which then freezes the
cache it wrote (hash_map.bin<block bytes> beside the worker). H2O2RAM runs in
two builds: `h2o2ram`, with a constant-time patch for its secret-dependent
lookups, and `h2o2ram_shipped`, the published code. The shipped build takes
the patched build's planner choices, so every row is prepared with the patched
worker's scheme.

Rows run by block size, then capacity, so each call times only the levels the
cache lacks (its planner_ns is the row's marginal cost) and the largest rows
come last. A row that fails or times out does not stop the others; the larger
rows of its block size are not attempted, since they need the same levels.
`resolve` then skips every unprepared row as a planner-cache miss. Each run
appends its outcomes to prepare_h2o2ram.json in the campaign.
"""
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import tempfile
import threading
import time

from .codec import load_json, require
from .resolution import resolver_arguments
from .store import atomic_json

H2O2RAM_SCHEMES = ("h2o2ram", "h2o2ram_shipped")
RECORD = "prepare_h2o2ram.json"


def memory_limit(resources):
    """The address-space cap for a planner child: the host headroom resolve applies to trials."""
    host = resources.get("host_memory_limit_bytes")
    return None if host is None else host * (1_000_000 - resources["headroom_ppm"]) // 1_000_000


def _planner(command, timeout, limit):
    """Run one planner child. Its peak RSS comes from wait4, since a TD may lack /usr/bin/time."""
    def cap():
        if limit is not None:  # an allocation past it throws bad_alloc instead of waking the OOM killer
            resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
    expired = threading.Event()
    with tempfile.TemporaryFile("w+") as out, tempfile.TemporaryFile("w+") as err:
        begin = time.monotonic_ns()
        child = subprocess.Popen(command, stdout=out, stderr=err, preexec_fn=cap)
        timer = threading.Timer(timeout, lambda: (expired.set(), child.kill())) if timeout else None
        if timer:
            timer.start()
        try:
            _, status, usage = os.wait4(child.pid, 0)
            child.returncode = os.waitstatus_to_exitcode(status)  # reaped: a late kill() is now a no-op
        finally:
            if timer:
                timer.cancel()
        wall = time.monotonic_ns() - begin
        out.seek(0)
        err.seek(0)
        stdout, stderr = out.read().strip(), err.read().strip()
    result = {"wall_ns": wall, "peak_rss_bytes": usage.ru_maxrss * 1024}
    if expired.is_set() and child.returncode == -signal.SIGKILL:
        return {**result, "status": "timeout", "error": f"killed after {timeout} s"}
    if child.returncode != 0:
        last = stderr.splitlines()[-1] if stderr else f"exit {child.returncode}"
        return {**result, "status": "failed", "error": last}
    return {**result, "status": "prepared", **json.loads(stdout)}


def prepare_h2o2ram(campaign, worker, timeout=None, job_timeout=None):
    """`timeout` caps one row's planner; `job_timeout` the whole job (default: none for both)."""
    from .campaign import read_plan
    require(job_timeout is None or job_timeout > 0, "job_timeout must be positive")
    deadline = None if job_timeout is None else time.monotonic() + job_timeout
    worker = Path(worker).resolve(strict=True)
    plan = read_plan(campaign)
    rows = {}
    for row in plan["trials"]:
        if row["spec"]["overrides"]["scheme"] not in H2O2RAM_SCHEMES or row["planning_status"] == "skipped":
            continue
        arguments = resolver_arguments(row, False)
        arguments[arguments.index("--scheme") + 1] = "h2o2ram"
        spec = row["spec"]
        rows.setdefault(tuple(arguments), (spec["shape"]["value_bytes"], spec["requested_capacity"],
                                           memory_limit(spec["resources"])))
    outcomes, failed = [], {}
    for arguments, (value_bytes, capacity, limit) in sorted(rows.items(), key=lambda item: (item[1][:2], item[0])):
        entry = {"arguments": list(arguments), "value_bytes": value_bytes, "capacity": capacity,
                 "memory_limit_bytes": limit}
        if value_bytes in failed:
            outcomes.append({**entry, "status": "not_attempted",
                             "error": f"capacity {failed[value_bytes]} of this block size failed"})
            continue
        remaining = None if deadline is None else deadline - time.monotonic()
        if remaining is not None and remaining <= 0:
            outcomes.append({**entry, "status": "not_attempted", "error": "job wall-time cap reached"})
            continue
        caps = [t for t in (timeout, remaining) if t is not None]
        row_timeout = min(caps) if caps else None
        outcome = {**entry, **_planner([str(worker), *arguments, "--prepare-planner", "1"], row_timeout, limit)}
        if outcome["status"] != "prepared":
            failed[value_bytes] = capacity
        outcomes.append(outcome)
    counts = {}
    for outcome in outcomes:
        counts[outcome["status"]] = counts.get(outcome["status"], 0) + 1
    run = {"worker": str(worker), "timeout_s": timeout, "job_timeout_s": job_timeout, "counts": counts,
           "rows": outcomes}
    path = Path(campaign) / RECORD
    earlier = load_json(path)["runs"] if path.exists() else []
    atomic_json(path, {"schema_version": 1, "plan_id": plan["plan_id"], "runs": earlier + [run]})
    return {**run, "record": str(path),
            "note": "Now run `resolve` with this worker; it freezes the planner cache beside it, and skips "
                    "unprepared rows as planner-cache misses. A later run's planner_ns counts only the "
                    "levels the cache still lacked."}
