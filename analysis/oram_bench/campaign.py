"""Local process orchestration and verified per-attempt commits.

`run` launches only the worker frozen by `resolve` (campaign/build/worker) with
the arguments recorded in resolution.json. A synthetic rehearsal runs the fake
or no-op backend. A native, tdx or snp run needs a host whose guest kernel
shows that runtime (a native host must show no TEE), for tdx and snp this
boot's attestation capture (attestation.py), a host whose exposed topology
satisfies its resources, and memory headroom for each attempt; every attempt's
resolved configuration and placement are then checked against
resolution.json. No logical campaign input is silently relaxed to run a map.
"""
from collections import Counter
from fractions import Fraction
import os
from pathlib import Path
import signal
import shutil
import subprocess

from .admission import attempt_check, topology_check
from .attestation import launch_gate
from .codec import decode, identity, load_json, plain, require
from .doctor import inspect, file_hash
from .preflight import memory_evidence, attempt_preflight
from .resolution import (entries, executed_trial, read_resolution, trial_arguments, verify_side_files,
                         worker_scheme)
from .schema import Environment
from .store import atomic_json, commit, durable_mkdir, ownership, verify


def read_plan(campaign):
    """Verify the stored plan against its own identity.

    The plan is not re-expanded with the current planner, so a planner or
    schema change (for example a new optional field) does not strand it.
    """
    plan = load_json(Path(campaign) / "plan.json")
    body = {k: v for k, v in plan.items() if k != "plan_id"}
    require(plan.get("plan_id") == identity("plan-v1", body), "immutable plan identity/content mismatch")
    return plan


def resolution_entries(campaign, plan):
    """Resolution entries by trial, or None before `resolve` has run."""
    if not (Path(campaign) / "resolution.json").exists():
        return None
    return entries(read_resolution(campaign, plan))


def attempts(campaign, trial_id):
    root = Path(campaign) / "trials" / trial_id / "attempts"
    return sorted(p for p in root.glob("*") if p.is_dir())


def successful(campaign, trial_id, environment_class=None):
    for attempt in attempts(campaign, trial_id):
        try:
            manifest = verify(attempt)
            require(manifest["trial_id"] == trial_id, "manifest belongs to another trial")
            environment = load_json(Path(campaign) / "environments" / (manifest["environment_id"] + ".json"))
            require(identity("environment-v1", environment) == manifest["environment_id"], "environment hash mismatch")
            if manifest["status"] == "complete" and (environment_class is None or
                    environment["environment_class"] == environment_class):
                return attempt, manifest
        except (OSError, ValueError, KeyError):
            continue
    return None


def completed_classes(campaign, trial_id):
    """Environment classes holding a verified complete attempt of this trial."""
    classes = set()
    for attempt in attempts(campaign, trial_id):
        try:
            manifest = verify(attempt)
            environment = load_json(Path(campaign) / "environments" / (manifest["environment_id"] + ".json"))
            require(identity("environment-v1", environment) == manifest["environment_id"], "environment hash mismatch")
            if manifest["status"] == "complete":
                classes.add(environment["environment_class"])
        except (OSError, ValueError, KeyError):
            continue
    return classes


def status(campaign):
    plan = read_plan(campaign)
    resolved = resolution_entries(campaign, plan)
    stored = Path(campaign) / "launch_policy.json"
    policy = load_json(stored) if stored.exists() else DEFAULT_LAUNCH_POLICY
    rows, by_class = [], {}
    for row in plan["trials"]:
        trial_id = row["trial_id"]
        entry = resolved[trial_id] if resolved else None
        if entry is not None and entry["status"] == "same_as":
            rows.append({"trial_id": trial_id, "status": "same_as", "same_as": entry["same_as"],
                         "attempts": 0, "selected_attempt": None})
            continue
        success = successful(campaign, trial_id)
        history = attempts(campaign, trial_id)
        skipped = row["planning_status"] == "skipped" or (entry is not None and entry["status"] == "skipped")
        state = "complete" if success else "skipped" if skipped else "pending"
        if state == "pending" and row["spec"].get("rate") and any(
                _below_floor(row, load_json(path)["ops_per_second"])
                for path in (Path(campaign) / "rates" / trial_id).glob("*.json")):
            state = "below_rate_floor"
        if not success and history:
            try:
                state = verify(history[-1])["status"]
            except (OSError, ValueError, KeyError):
                state = "uncommitted"
            worker_failures, preemptions, terminal = attempt_budget(campaign, trial_id)
            if not terminal and (worker_failures > policy["retries"] or
                                 preemptions > policy["preemption_retries"]):
                state = "abandoned"  # distinct from an interrupted trial that will retry
        for environment_class in completed_classes(campaign, trial_id):
            by_class[environment_class] = by_class.get(environment_class, 0) + 1
        rows.append({"trial_id": trial_id, "status": state, "attempts": len(history),
                     "selected_attempt": success[1]["attempt_id"] if success else None})
    coordinator = Path(campaign) / "coordinator_status.json"
    # A class change is visible: completions are reported per environment class.
    return {"plan_id": plan["plan_id"], "resolved": resolved is not None,
            "counts": dict(Counter(r["status"] for r in rows)),
            "complete_by_environment_class": dict(sorted(by_class.items())), "trials": rows,
            "coordinator": load_json(coordinator) if coordinator.exists() else None}


def verify_campaign(campaign, deep=False):
    """Verify every committed attempt; `deep` re-hashes all raw bytes."""
    plan = read_plan(campaign)
    verified, failed, uncommitted = 0, [], 0
    for row in plan["trials"]:
        for attempt in attempts(campaign, row["trial_id"]):
            if not (attempt / "COMMITTED.json").exists():
                uncommitted += 1
                continue
            try:
                verify(attempt, deep=deep)
                verified += 1
            except (OSError, ValueError, KeyError) as error:
                failed.append({"attempt": attempt.relative_to(campaign).as_posix(), "reason": str(error)})
    return {"deep": deep, "verified": verified, "uncommitted": uncommitted, "failed": failed}


def _rate(campaign, row, environment_class, resolved=None):
    """The offered rate: absolute, or frozen once from committed saturation sources.

    The frozen record is authoritative. If its sources no longer verify,
    the row is deferred as `rate_source_invalid` rather than re-deriving a
    different rate (which would contradict the immutable record on every resume).
    """
    rate = row["spec"]["rate"]
    if rate is None:
        return None, None
    if rate["kind"] == "absolute":
        return rate["ops_per_second"], None
    destination = Path(campaign) / "rates" / row["trial_id"] / (environment_class + ".json")
    if destination.exists():
        record = load_json(destination)
        for source in record["sources"]:
            attempt = next((a for a in attempts(campaign, source["trial_id"])
                            if a.name.endswith(source["attempt_id"])), None)
            try:
                require(attempt is not None and verify(attempt)["status"] == "complete" and
                        file_hash(attempt / "COMMITTED.json") == source["commit_sha256"], "source changed")
            except (OSError, ValueError, KeyError):
                return None, "rate_source_invalid"
        return record["ops_per_second"], _below_floor(row, record["ops_per_second"])
    sources, values = [], []
    for trial_id in rate["source_trial_ids"]:
        if resolved is not None:
            trial_id = executed_trial(resolved, trial_id)
        selected = successful(campaign, trial_id, environment_class)
        if selected is None:
            return None, "waiting for committed saturation sources in this environment class"
        attempt, manifest = selected
        boundaries = load_json(attempt / "worker/worker.json")["trial_boundaries"]
        require(boundaries[4] > 0, "saturation source has no drained duration")
        values.append(Fraction(boundaries[1] * 1_000_000_000, boundaries[4]))
        sources.append({"trial_id": trial_id, "attempt_id": manifest["attempt_id"],
                        "commit_sha256": file_hash(attempt / "COMMITTED.json")})
    values.sort()
    middle = len(values) // 2
    median = values[middle] if len(values) % 2 else (values[middle-1] + values[middle]) / 2
    frozen = int(median * rate["fraction_ppm"] / 1_000_000)
    require(frozen > 0, "derived offered rate rounds to zero")
    record = {"schema_version": 1, "trial_id": row["trial_id"], "environment_class": environment_class,
              "ops_per_second": frozen, "sources": sources, "reduction": rate["reduction"]}
    atomic_json(destination, record, immutable=True)
    return frozen, _below_floor(row, frozen)


def _below_floor(row, ops_per_second):
    """A frozen fraction under the stage's rate floor is recorded, never launched."""
    floor = row["spec"]["rate"].get("minimum_ops_per_second")  # absent in plans made before the floor
    return "below_rate_floor" if floor is not None and ops_per_second < floor else None


class ReplayInterrupted(Exception):
    """The coordinator was asked to stop while the replay was running."""


def reducer_inputs(paths):
    """(cwd, names) for the C++ reducer: its input files as names in their one shared directory.

    Absolute paths overflow ARG_MAX (2 MiB) at a few thousand files, which a large full-event row
    (thousands of event chunks) reaches. Relative names are ~25 bytes each.
    """
    parents = {path.parent for path in paths}
    require(len(parents) <= 1, "reducer inputs must share one directory")
    return (parents.pop() if parents else None), [path.name for path in paths]


def _replay_timeout(chunks):
    # Scales with trace size (about 20 MB/s is a conservative replay rate).
    return 120 + sum(path.stat().st_size for path in chunks) / 20e6


def worker_verification(metadata):
    """The worker's verification mode (full or off); a worker.json without the field verified fully."""
    return metadata.get("verification", "full")


def _verify_replay(reducer, output, require_live=True, chunks=None, stop=None, verification=None):
    """Replay committed raw data with the C++ reducer. Writes nothing.

    `chunks` is the verified manifest's list after commit; before commit the
    fresh output directory is listed. The reducer runs in its own session, so
    a coordinator stop signal cannot kill it and mislabel a good trial.
    A `verification = off` worker must not claim verified correctness.
    """
    metadata = load_json(output / "worker.json")
    mode = worker_verification(metadata)
    require(verification is None or mode == verification, "worker verification mode differs from the row")
    require(metadata["correctness_verified"] == (mode == "full") and metadata["lost_events"] == 0 and
            not metadata["writer_error"], "worker correctness/logging check failed")
    if chunks is None:
        chunks = sorted((output / "events").glob("*.bin"))
    checkpoints = sorted((output / "checkpoints").glob("*.bin")) if (output / "checkpoints").is_dir() else []
    if not checkpoints and (output / "checkpoint.bin").exists():
        checkpoints = [output / "checkpoint.bin"]
    cwd, names = reducer_inputs(chunks if chunks else checkpoints)
    reducer = Path(reducer).resolve()
    command = [str(reducer), "--events", *names] if chunks else [str(reducer),
        "--minimum-tail-count", str(metadata["minimum_tail_count"]), "--trial-boundaries",
        *map(str, metadata["trial_boundaries"]), *names]
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                               start_new_session=True, cwd=cwd)
    try:
        stdout, stderr = process.communicate(timeout=_replay_timeout(chunks))
    except subprocess.TimeoutExpired:
        process.kill()
        process.communicate()
        raise
    if stop is not None and stop[0]:
        raise ReplayInterrupted("coordinator stop during replay")
    require(process.returncode >= 0, f"reducer killed by signal {-process.returncode}")
    require(process.returncode == 0, "raw replay failed: " + stderr)
    import json
    replay = json.loads(stdout)
    # An offered-load row may reach the drain deadline with a backlog: that is censored overload
    # (labeled overloaded), not a failure. Only a saturated row's drain must end inside it.
    require(not replay["request_cap_reached"] and not (replay["deadline_exceeded"] and replay["saturated"]),
            "worker exceeded offered or drain budget")
    if require_live:
        require(replay == load_json(output / "summary.json"), "raw replay differs from live summary")
    return replay, metadata


DEFAULT_LAUNCH_POLICY = {"schema_version": 1, "retries": 1, "preemption_retries": 20,
                         "min_free_bytes": 5 * 1024**3}


def launch_policy(campaign, requested=None, update=False):
    """The campaign's persisted launch policy.

    The first run writes launch_policy.json. Later runs, including a boot
    service that passes no options, use it; a differing command-line value is
    refused unless `update` is set.
    """
    requested = {k: v for k, v in (requested or {}).items() if v is not None}
    path = Path(campaign) / "launch_policy.json"
    if path.exists():
        policy = load_json(path)
        changed = {k: v for k, v in requested.items() if policy.get(k) != v}
        if changed:
            require(update, "launch policy differs from launch_policy.json: " + ", ".join(sorted(changed)) +
                    "; pass --update-launch-policy to change it")
            policy = {**policy, **changed}
            atomic_json(path, policy)
        return policy
    policy = {**DEFAULT_LAUNCH_POLICY, **requested}
    require(policy["retries"] >= 0 and policy["preemption_retries"] >= 0 and policy["min_free_bytes"] >= 0,
            "invalid launch policy")
    atomic_json(path, policy)
    return policy


def attempt_budget(campaign, trial_id, environment_class=None, mark_orphans=False):
    """Classify earlier attempts.

    Preemptions (coordinator-initiated stops and attempts orphaned by a dead
    coordinator) are bounded separately from worker-side failures (timeouts,
    signals, resource failures), so spot preemptions do not use up retries.
    """
    worker_failures = preemptions = 0
    terminal = False
    for old in attempts(campaign, trial_id):
        require(not old.is_symlink(), "attempt directory cannot be a symlink")
        try:
            record = verify(old)
            old_environment = load_json(Path(campaign) / "environments" / (record["environment_id"] + ".json"))
            require(identity("environment-v1", old_environment) == record["environment_id"], "environment hash mismatch")
            if environment_class is not None and old_environment["environment_class"] != environment_class:
                continue
            if record["status"] == "complete":
                continue
            if record["failure_kind"] == "preemption":
                preemptions += 1
            elif record["failure_kind"] == "infrastructure":
                worker_failures += 1
            else:
                terminal = True
        except (OSError, ValueError, KeyError):
            preemptions += 1
            if mark_orphans:
                atomic_json(old / "state.json", {"status": "interrupted",
                    "reason": "uncommitted attempt after ownership recovery"})
    return worker_failures, preemptions, terminal


def run_campaign(campaign, reducer, *, synthetic=False, limit=None, retries=None, preemption_retries=None,
                 min_free_bytes=None, update_launch_policy=False):
    require(limit is None or limit > 0, "invalid launch limit")
    campaign, reducer = Path(campaign).resolve(), Path(reducer).resolve(strict=True)
    plan = read_plan(campaign)
    resolution = read_resolution(campaign, plan)
    resolved = entries(resolution)
    require(resolution["build"]["synthetic"] == synthetic,
            "the frozen build's synthetic/native mode differs from this run (resolve with --synthetic "
            "for a rehearsal, without it for a native campaign)")
    execution = plan["campaign"]["execution"]
    require(synthetic or execution["runtime"] in ("native", "tdx", "snp"),
            "a campaign run needs execution.runtime native (with require_protected = false), tdx or snp; "
            "an unspecified runtime never launches")
    # Launch only the frozen copy, never a rebuilt binary.
    worker = (campaign / "build" / "worker").resolve(strict=True)
    require("sha256-" + file_hash(worker) == resolution["build"]["worker_sha256"], "frozen worker binary changed")
    # The frozen worker reads them beside itself (H2O2RAM's planner cache).
    verify_side_files(campaign / "build", resolution["build"])
    environment = inspect(worker, "fake" if synthetic else execution["runtime"],
                          library_header=resolution["build"]["library_header_sha256"])
    # The label must match the guest kernel, and a tdx or snp run needs this
    # boot's capture, which the environment record then references by hash.
    gate = None if synthetic else launch_gate(campaign, execution, environment)
    if gate is not None and gate["attestation"] is not None:
        environment = plain(decode(Environment, {**environment, "attestation": gate["attestation"]}))
    environment_id = identity("environment-v1", environment)
    # A host must expose the campaign's cores and cache domains before anything
    # launches; a mismatch blocks rather than raises, so a boot service does
    # not restart-loop on it.
    topology = None if synthetic else topology_check(plan["campaign"]["resources"], environment)
    launched = 0
    rate_invalid, below_floor = [], []
    stop, active = [False], [None]
    def terminate(signum, frame):
        stop[0] = True
        if active[0] is not None:
            try:
                os.killpg(active[0].pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
    previous = {sig: signal.signal(sig, terminate) for sig in (signal.SIGTERM, signal.SIGINT)}
    try:
        with ownership(campaign) as lease:
            policy = launch_policy(campaign, {"retries": retries, "preemption_retries": preemption_retries,
                                              "min_free_bytes": min_free_bytes}, update_launch_policy)
            for reason, assessment in (("runtime", gate), ("topology", topology)):
                if assessment is not None and assessment["status"] != "compatible":
                    atomic_json(campaign / "coordinator_status.json", {"status": "blocked", "reason": reason,
                        "synthetic": synthetic, "assessment": assessment})
                    return {"synthetic": synthetic, "launched": 0, "stopped": False, **status(campaign)}
            atomic_json(campaign / "coordinator_status.json", {"status": "running", "synthetic": synthetic})
            atomic_json(campaign / "environments" / (environment_id + ".json"), environment, immutable=True)
            for row in plan["trials"]:
                if stop[0] or (limit is not None and launched >= limit):
                    break
                entry = resolved[row["trial_id"]]
                if entry["status"] != "runnable" or successful(campaign, row["trial_id"], environment["environment_class"]):
                    continue
                free_bytes = shutil.disk_usage(campaign).free
                if free_bytes < policy["min_free_bytes"]:
                    atomic_json(campaign / "coordinator_status.json", {"status": "blocked",
                        "reason": "disk_watermark", "free_bytes": free_bytes,
                        "minimum_free_bytes": policy["min_free_bytes"]})
                    stop[0] = True
                    break
                # The no-op backend stores no dataset; preflight bills the rest.
                require(not synthetic or worker_scheme(entry) == "noop" or
                        (row["live_entries"] <= 1_048_576 and row["logical_dataset_bytes"] <= 256 * 1024**2),
                        "synthetic rehearsal exceeds bounded fake-backend dataset limit")
                history = attempts(campaign, row["trial_id"])
                worker_failures, preemptions, terminal = attempt_budget(
                    campaign, row["trial_id"], environment["environment_class"], mark_orphans=True)
                if terminal or worker_failures > policy["retries"] or preemptions > policy["preemption_retries"]:
                    continue
                rate, deferred = _rate(campaign, row, environment["environment_class"], resolved)
                if deferred == "rate_source_invalid":
                    rate_invalid.append(row["trial_id"])
                elif deferred == "below_rate_floor":
                    below_floor.append(row["trial_id"])
                if deferred:
                    continue
                # Capture before allocating worker storage. This estimate guard
                # can reject a launch; it never certifies fit. The record is kept
                # only as the attempt's memory_preflight.json.
                preflight = attempt_preflight(row, entry, memory_evidence(), rate)
                if preflight["assessment"]["status"] == "exceeds_budget":
                    atomic_json(campaign / "coordinator_status.json", {"status": "blocked",
                        "reason": "memory_headroom", "trial_id": row["trial_id"],
                        "assessment": preflight["assessment"]})
                    stop[0] = True
                    break
                ordinal = len(history) + 1
                attempt_id = identity("attempt-v1", [row["trial_id"], environment_id, ordinal])
                attempt = campaign / "trials" / row["trial_id"] / "attempts" / (f"{ordinal:06d}-" + attempt_id)
                durable_mkdir(attempt, exclusive=True)
                atomic_json(attempt / "state.json", {"status": "running", "synthetic": synthetic,
                    "environment_id": environment_id})
                # Git state is recorded per attempt but is not part of the environment class.
                atomic_json(attempt / "requested.json", {"trial": row, "resolution": entry, "frozen_rate": rate,
                    "synthetic": synthetic, "source_identity": environment.get("source_identity")}, immutable=True)
                atomic_json(attempt / "memory_preflight.json", preflight, immutable=True)
                args = [str(worker), *trial_arguments(row, entry, attempt / "worker", rate)]
                verification = row["spec"]["instrumentation"].get("verification", "full")
                timed_out = False
                code = None
                with open(attempt / "stdout.log", "wb") as stdout, open(attempt / "stderr.log", "wb") as stderr:
                    # A stop that arrived during preflight or hashing must
                    # not launch; block the signals so the handler sees the child.
                    blocked = signal.pthread_sigmask(signal.SIG_BLOCK, {signal.SIGTERM, signal.SIGINT})
                    try:
                        if not stop[0]:
                            active[0] = subprocess.Popen(args, stdout=stdout, stderr=stderr,
                                start_new_session=True, pass_fds=(lease,))
                            launched += 1
                    finally:
                        signal.pthread_sigmask(signal.SIG_SETMASK, blocked)
                    if active[0] is not None:
                        atomic_json(attempt / "state.json", {"status": "running", "synthetic": synthetic,
                            "worker_pid": active[0].pid, "boot_identity": environment["boot_identity"],
                            "environment_id": environment_id})
                        try:
                            code = active[0].wait(timeout=row["spec"]["timing"]["max_trial_ns"] / 1e9)
                        except subprocess.TimeoutExpired:
                            timed_out = True
                            os.killpg(active[0].pid, signal.SIGKILL)
                            code = active[0].wait()
                        finally:
                            active[0] = None
                outcome, failure, reason = "complete", None, None
                summary, metadata = {}, {}
                if code is None:
                    outcome, failure, reason = "interrupted", "preemption", "stop before launch"
                elif code != 0 or stop[0]:
                    for filename, target in (("summary.json", summary), ("worker.json", metadata)):
                        try:
                            target.update(load_json(attempt / "worker" / filename))
                        except (OSError, ValueError):
                            pass
                    outcome = "interrupted" if code < 0 or stop[0] else "failed"
                    # Coordinator-initiated stops are preemptions; worker-side
                    # timeouts and signals count against the retry budget.
                    failure = "preemption" if stop[0] else "infrastructure" if outcome == "interrupted" else "resource"
                    reason = "worker timeout" if timed_out else f"worker exit {code}"
                    if timed_out and not stop[0]:
                        outcome, failure = "failed", "time_cap"
                        reason = f"worker exceeded max_trial_ns ({row['spec']['timing']['max_trial_ns']} ns)"
                    if code == 3 and not stop[0]:
                        outcome = "invalid"
                        failure = "logging" if metadata.get("lost_events") or metadata.get("writer_error") else "resource"
                    if "correctness:" in (attempt / "stderr.log").read_text(errors="replace"):
                        failure, outcome = "correctness", "failed"
                else:
                    try:
                        summary, metadata = _verify_replay(reducer, attempt / "worker", stop=stop,
                                                           verification=verification)
                    except ReplayInterrupted as error:
                        outcome, failure, reason = "interrupted", "preemption", str(error)
                    except subprocess.TimeoutExpired as error:
                        outcome, failure, reason = "interrupted", "infrastructure", "replay timeout: " + str(error)
                    except (ValueError, OSError, KeyError) as error:
                        if stop[0]:
                            outcome, failure, reason = "interrupted", "preemption", "stop during replay: " + str(error)
                        else:
                            outcome, failure, reason = "invalid", "logging", str(error)
                resolved_path = attempt / "worker/resolved.json"
                if outcome == "complete" and not synthetic:
                    # The worker re-resolved from the recorded arguments and
                    # placed its threads; both must match what resolve froze.
                    check = attempt_check(row, entry, environment, load_json(resolved_path))
                    atomic_json(attempt / "attempt_check.json", check, immutable=True)
                    if check["status"] == "incompatible":
                        outcome, failure = "invalid", "configuration"
                        reason = "attempt check: " + ", ".join(check["rejection_reasons"])
                commit(attempt, {"schema_version": 1, "trial_id": row["trial_id"], "attempt_id": attempt_id,
                    "environment_id": environment_id,
                    "resolved_plan_id": "sha256-" + file_hash(resolved_path) if resolved_path.exists() else "unresolved",
                    "status": outcome, "failure_kind": failure, "reason": reason,
                    "events": metadata.get("written_events", 0), "lost_events": metadata.get("lost_events", 0),
                    "correctness_verified": metadata.get("correctness_verified", False),
                    "verification": verification,
                    "measurement_begin_ns": 0 if summary else None,
                    "measurement_end_ns": summary.get("caller_end_ns"),
                    "drain_end_ns": summary.get("drain_end_ns")})
                atomic_json(attempt / "state.json", {"status": outcome, "synthetic": synthetic,
                    "environment_id": environment_id})
            if load_json(campaign / "coordinator_status.json")["status"] != "blocked":
                atomic_json(campaign / "coordinator_status.json", {"status": "stopped" if stop[0] else "idle",
                    "synthetic": synthetic, "rate_source_invalid": rate_invalid,
                    "below_rate_floor": below_floor})
    finally:
        for sig, handler in previous.items():
            signal.signal(sig, handler)
    return {"synthetic": synthetic, "launched": launched, "stopped": stop[0], **status(campaign)}
