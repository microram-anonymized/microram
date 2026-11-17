"""The resolve step: freeze the worker, resolve every row.

`plan` stays portable. `resolve` needs the built worker: it copies the binary
into the campaign's `build/` directory, calls `--resolve-only 1` once per unique
resolver input, and writes an immutable `resolution.json`. `run` and `resume`
then launch only the frozen copy with the arguments recorded here, so a
worker's request matches its resolution by construction.

Cross-field validity of library options is the C++ resolver's job alone; this
module never re-derives geometry, memory models or eligibility.
"""
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import subprocess

from .codec import canonical, identity, load_json, require
from .doctor import file_hash
from .store import atomic_json, durable_mkdir

ROOT = Path(__file__).resolve().parents[2]
RESOLUTION_SCHEMA_VERSION = 1


def library_header_identity(root=ROOT):
    """Hash of every header the header-only library and worker are built from."""
    digest = hashlib.sha256()
    for directory in ("include", "src"):
        for path in sorted((root / directory).rglob("*.hpp")):
            digest.update(path.relative_to(root).as_posix().encode() + b"\0" +
                          file_hash(path).encode() + b"\n")
    return "sha256-" + digest.hexdigest()


def override_fields(overrides):
    """Flatten explicit values only; zero/false survive, null stays automatic."""
    result = {}
    def walk(value, prefix):
        for name, item in value.items():
            path = prefix + name
            if isinstance(item, dict):
                walk(item, path + ".")
            elif item is not None:
                result[path] = item
    walk({key: value for key, value in overrides.items() if key not in ("schema_version", "scheme")}, "")
    return result


def _argument(value):
    return ("true" if value else "false") if type(value) is bool else str(value)


SYNTHETIC_BACKENDS = ("fake", "noop")  # correctness fake; constant-space no-op


def resolver_arguments(row, synthetic, backend="fake"):
    """Every worker argument the library resolver reads, in a stable order.

    Placement is deliberately absent: slots are chosen on the target at run
    time, and the configuration key is placement-independent. A synthetic
    row runs `backend` in place of the library.
    """
    spec = row["spec"]
    values = {"scheme": backend if synthetic else spec["overrides"]["scheme"],
              "capacity": spec["requested_capacity"], "key-bytes": spec["shape"]["key_bytes"],
              "value-bytes": spec["shape"]["value_bytes"], "max-accesses": spec["timing"]["max_accesses"],
              "api": spec["api_mode"], "batch-size": spec["caller_batch_size"],
              "cores": spec["resources"]["physical_cores"],
              # Declared domains cap a near/far boundary's rebuild budget per side.
              "cache-domains": spec["resources"]["required_cache_domains"] or 1}
    # Only dense rows name it, so permuted rows keep their earlier arguments.
    if spec["shape"].get("key_layout", "permuted") == "dense":
        values["key-layout"] = "dense"
    # Likewise only a declared idle-wait capability names it.
    if spec["resources"].get("monitor_wait", "none") != "none":
        values["monitor-wait"] = spec["resources"]["monitor_wait"]
    if spec["resources"].get("spin_before_park_ns"):
        values["spin-before-park-ns"] = spec["resources"]["spin_before_park_ns"]
    if not synthetic:
        values.update({"override." + name: value for name, value in
                       sorted(override_fields(spec["overrides"]).items())})
    return [part for key, value in values.items() for part in ("--" + key, _argument(value))]


RECORD_BYTES = 64
EVENT_SLACK_RECORDS = 1024


def event_buffer_bytes(row, rate):
    """The worker's whole-trial event buffer for this row.

    Saturated trials keep coarse windows in a configured buffer. Histogram-
    checkpoint offered-load trials allocate none. A full-event offered-load
    trial needs an arrival and a member (or outcome) record per request, plus
    one batch record per call: 192 B per scalar request and 128 + 64/b per
    fixed-count batched request. None until a saturation-derived rate is frozen.
    """
    spec = row["spec"]
    logging = spec["instrumentation"]
    if spec["arrival"] == "saturated":
        return logging["buffer_bytes"]
    if logging["logging"] != "full_events":
        return 0
    if rate is None:
        return None
    expected = rate * spec["timing"]["measurement_ns"] / 1e9
    # Fixed arrivals: the count is the mean, rounded up, plus slack.
    requests = min(math.ceil(expected) + 16, spec["timing"]["max_accesses"] + 1)
    batch = spec["caller_batch_size"]
    fixed_count = spec["batch_policy"]["formation"] != "max_count_or_timeout"
    calls = requests if batch == 1 or not fixed_count else math.ceil(requests / batch) + 1
    return (2 * requests + calls + EVENT_SLACK_RECORDS) * RECORD_BYTES


def trial_arguments(row, entry, output, rate):
    """The full worker argv for one attempt: resolved arguments plus trial inputs."""
    spec = row["spec"]
    workload, timing, logging = (spec[k] for k in ("workload", "timing", "instrumentation"))
    values = {"output": str(output), "live-entries": row["live_entries"],
              "batch-timeout-ns": spec["batch_policy"]["timeout_ns"] or 0,
              "queue-limit": timing["queue_limit"], "measurement-ns": timing["measurement_ns"],
              "warmup-ns": timing["warmup_ns"], "settle-requests": timing["settle_requests"],
              "drain-ns": timing["drain_deadline_ns"], "max-requests": timing["max_accesses"],
              "arrival": spec["arrival"], "read-ppm": workload["read_ppm"], "hit-ppm": workload["hit_ppm"],
              "miss-keys": workload["miss_key_count"], "buffer-requests": workload["buffer_requests"],
              "workload-seed": spec["workload_seed"], "arrival-seed": spec["arrival_seed"],
              "logging": logging["logging"], "minimum-tail-count": logging["minimum_tail_count"],
              "checkpoint-interval-ns": logging["checkpoint_interval_ns"],
              "memory-interval-ns": logging["memory_interval_ns"], "window-requests": logging["window_requests"],
              "service-timing": int(logging["service_timing"])}
    if "verification" in logging:  # absent from plans that do not set it
        values["verification"] = logging["verification"]
    # Harness options, passed only when on so other rows keep their argv.
    if workload["distribution"] == "counter":
        values["key-pattern"] = "counter"
    if logging.get("checkpoint_thread"):
        values["checkpoint-thread"] = 1
    if spec["arrival"] == "fixed" and spec["batch_policy"]["formation"] == "arrive_together":
        values["arrival-group"] = spec["caller_batch_size"]
    buffer = event_buffer_bytes(row, rate)
    require(buffer is not None, "event buffer needs the frozen offered rate")
    if buffer:
        values["event-buffer-bytes"] = buffer
        values["chunk-bytes"] = min(logging["chunk_bytes"], buffer)
    if not entry["synthetic"]:
        values["placement"] = spec["resources"]["placement"]
    if rate is not None:
        values["rate"] = rate
    return list(entry["worker_arguments"]) + [
        part for key, value in values.items() for part in ("--" + key, str(value))]


def worker_scheme(entry):
    """The --scheme a resolved row's worker runs (a library scheme, fake or noop)."""
    arguments = entry["worker_arguments"]
    return arguments[arguments.index("--scheme") + 1]


def known_rate(row):
    rate = row["spec"]["rate"]
    return None if rate is None or rate["kind"] != "absolute" else rate["ops_per_second"]


def library_bytes(configuration):
    """The library's modelled bytes, allocator rounding included where known."""
    reserved = configuration.get("modeled_reserved_bytes")
    return configuration["modeled_buffer_bytes"] if reserved is None else reserved


def estimated_memory(row, configuration, synthetic, rate=None):
    """Bytes the worker process allocates, from the resolver's model where one exists.

    The library's figure is its reserved bytes: every modelled buffer rounded
    as the allocator is asked for it (2 MiB for a huge-page buffer). The
    counting-allocator audit (benchmarks/oram/cpu_oram_allocation_audit.cpp,
    reconciled by analysis/allocation_reconcile.py) checks this against each
    engine's counted live heap. What it leaves out -- engine objects,
    containers, allocator headers and thread stacks -- is the headroom's to
    absorb. A resolution without reserved bytes (a baseline, or an envelope
    that does not report them) falls back to requested bytes. The
    event buffer of a saturation-derived row is null until its rate is
    frozen; the attempt preflight then prices it.
    """
    spec, live = row["spec"], row["live_entries"]
    buffer = event_buffer_bytes(row, rate if rate is not None else known_rate(row))
    # Read-only rows and verification off allocate no version table.
    unversioned = (spec["workload"]["read_ppm"] == 1_000_000 or
                   spec["instrumentation"].get("verification", "full") == "off")
    components = {
        "library_modeled": library_bytes(configuration),
        "verification_versions": 0 if unversioned else live * 8,
        "event_buffer": buffer,
    }
    if synthetic and configuration["scheme"] == "fake":  # the no-op backend stores nothing
        components["fake_values"] = live * spec["shape"]["value_bytes"]
    return components


def _skip_reasons(row, total, library_bytes):
    resources = row["spec"]["resources"]
    reasons = []
    limit = resources["library_memory_limit_bytes"]
    if limit is not None and library_bytes > limit:
        reasons.append("modeled_library_bytes_exceed_library_memory_limit")
    host = resources["host_memory_limit_bytes"]
    if host is not None and total > host * (1_000_000 - resources["headroom_ppm"]) // 1_000_000:
        reasons.append("estimated_memory_exceeds_host_headroom")
    return reasons


def duplicate_key(row, configuration_key, executed):
    """Rows that run the same configuration on the same inputs share this key.

    Stage, candidate label and overrides are labels here: the configuration key
    already captures what the overrides resolved to. A saturation-derived rate
    names its sources by the trials that execute them, so two arms whose
    sources are duplicates also derive the same rate.
    """
    spec = {k: v for k, v in row["spec"].items() if k not in ("stage", "kind", "candidate", "overrides", "purpose")}
    rate = spec.get("rate")
    if rate is not None and rate["kind"] == "saturation_fraction":
        spec["rate"] = {**rate, "source_trial_ids": [executed.get(t, t) for t in rate["source_trial_ids"]]}
    return identity("duplicate-v1", [configuration_key, spec])


def build_info(worker):
    """The worker's `--build-info` record, or None for a worker that has none.

    A baseline worker names the side files it reads beside its executable
    (H2O2RAM's planner cache) and embeds its fetch record.
    """
    try:
        result = subprocess.run([str(worker), "--build-info"], capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.SubprocessError):
        return None
    if result.returncode != 0:
        return None
    info = json.loads(result.stdout)
    require(info.get("build_info_schema_version") == 1, "unsupported worker build-info schema")
    for name in info.get("side_files", []):
        require(type(name) is str and name == Path(name).name and name not in ("", ".", "..", "worker",
                "build.json") and not name.startswith("."), f"unsafe worker side file {name!r}")
    return info


def _copy(source, destination):
    temporary = destination.with_name("." + destination.name + ".tmp")
    shutil.copy2(source, temporary)
    with open(temporary, "rb") as stream:
        os.fsync(stream.fileno())
    os.replace(temporary, destination)


def side_file_records(directory, names):
    return [{"name": name, "sha256": "sha256-" + file_hash(Path(directory) / name),
             "bytes": (Path(directory) / name).stat().st_size} for name in sorted(names)]


def verify_side_files(build, record):
    """The frozen side files must still be the ones build.json recorded."""
    for item in record.get("side_files", []):
        path = Path(build) / item["name"]
        require(path.is_file() and "sha256-" + file_hash(path) == item["sha256"],
                f"frozen side file {item['name']} changed")


def freeze_build(campaign, worker, synthetic):
    """Copy the worker, and the side files it declares, into campaign/build once.

    Later resolves must match: a changed worker or side file (for example a new
    H2O2RAM planner cache) needs a new campaign directory.
    """
    build = Path(campaign) / "build"
    record_path = build / "build.json"
    worker_sha256 = "sha256-" + file_hash(worker)
    info = None if synthetic else build_info(worker)
    side_files = side_file_records(Path(worker).parent, info.get("side_files", [])) if info else []
    if record_path.exists():
        record = load_json(record_path)
        require(record["worker_sha256"] == worker_sha256,
                "this campaign already froze a different worker build; a library or worker change "
                "needs a new campaign directory (plan, then resolve)")
        require(record["synthetic"] == synthetic, "frozen build differs in synthetic/native mode")
        require("sha256-" + file_hash(build / "worker") == worker_sha256, "frozen worker binary changed")
        require(record.get("side_files", []) == side_files,
                "the worker's side files differ from the frozen ones; a new planner cache needs a new "
                "campaign directory (plan, then resolve)")
        verify_side_files(build, record)
        return record
    durable_mkdir(build)
    for item in side_files:
        _copy(Path(worker).parent / item["name"], build / item["name"])
    _copy(worker, build / "worker")
    require("sha256-" + file_hash(build / "worker") == worker_sha256, "frozen worker copy differs")
    record = {"schema_version": 1, "worker_sha256": worker_sha256,
              "library_header_sha256": library_header_identity(), "synthetic": synthetic,
              "source_path": str(Path(worker).resolve())}
    if info is not None:
        record.update({"side_files": side_files, "build_info": info})
    verify_side_files(build, record)
    atomic_json(record_path, record, immutable=True)
    return record


def _resolve_native(worker, arguments):
    result = subprocess.run([str(worker), *arguments, "--resolve-only", "1"],
                            capture_output=True, text=True, timeout=120)
    if result.returncode != 0:
        return None, result.stderr.strip().splitlines()[-1] if result.stderr.strip() else f"exit {result.returncode}"
    resolved = json.loads(result.stdout)
    return {"configuration_key": resolved["configuration_key"], "scheme": resolved["scheme"],
            "actual_capacity": resolved["actual_capacity"],
            "modeled_buffer_bytes": resolved["modeled_buffer_bytes"],
            "modeled_reserved_bytes": resolved.get("modeled_reserved_bytes"),
            "library_threads": resolved["library_threads"], "resolved": resolved}, None


def _resolve_synthetic(row, arguments, backend):
    # Synthetic backends have no library model; fake storage is billed separately.
    return {"configuration_key": identity("synthetic-configuration-v1", arguments), "scheme": backend,
            "actual_capacity": row["spec"]["requested_capacity"], "modeled_buffer_bytes": 0,
            "library_threads": 1, "resolved": None}, None


def resolve_campaign(campaign, worker, *, synthetic=False, synthetic_backend="fake"):
    from .campaign import read_plan
    require(synthetic_backend in SYNTHETIC_BACKENDS and (synthetic or synthetic_backend == "fake"),
            "a synthetic backend needs a synthetic resolution")
    campaign, worker = Path(campaign).resolve(), Path(worker).resolve(strict=True)
    plan = read_plan(campaign)
    build = freeze_build(campaign, worker, synthetic)
    frozen = campaign / "build" / "worker"
    configurations, rows, representatives, executed = {}, [], {}, {}
    for row in plan["trials"]:
        entry = {"trial_id": row["trial_id"], "synthetic": synthetic, "status": "runnable",
                 "skip_reasons": list(row["skip_reasons"]), "same_as": None,
                 # A rehearsal runs a synthetic backend, whatever the row's scheme.
                 "security": "not_oblivious" if synthetic else row.get("security", "oblivious")}
        if row["planning_status"] == "skipped":
            entry["status"] = "skipped"
            rows.append(entry)
            continue
        arguments = resolver_arguments(row, synthetic, synthetic_backend)
        configuration_id = identity("resolver-arguments-v1", arguments)
        if configuration_id not in configurations:
            resolved, error = (_resolve_synthetic(row, arguments, synthetic_backend) if synthetic else
                               _resolve_native(frozen, arguments))
            configurations[configuration_id] = {"arguments": arguments, "error": error, **(resolved or {})}
        configuration = configurations[configuration_id]
        entry["configuration_id"] = configuration_id
        entry["worker_arguments"] = arguments
        if configuration["error"] is not None:
            entry["status"] = "skipped"
            entry["skip_reasons"].append("resolver_rejected: " + configuration["error"])
            rows.append(entry)
            continue
        components = estimated_memory(row, configuration, synthetic)
        total = sum(v for v in components.values() if v is not None)
        entry.update({"configuration_key": configuration["configuration_key"],
                      "actual_capacity": configuration["actual_capacity"],
                      "modeled_buffer_bytes": configuration["modeled_buffer_bytes"],
                      "modeled_reserved_bytes": configuration.get("modeled_reserved_bytes"),
                      "estimated_memory": components, "estimated_memory_bytes": total})
        reasons = _skip_reasons(row, total, library_bytes(configuration))
        if reasons:
            entry["status"] = "skipped"
            entry["skip_reasons"] += reasons
        else:
            # Plan order puts saturation sources before their consumers.
            key = duplicate_key(row, configuration["configuration_key"], executed)
            if key in representatives:
                entry["status"], entry["same_as"] = "same_as", representatives[key]
            else:
                representatives[key] = row["trial_id"]
            executed[row["trial_id"]] = entry["same_as"] or row["trial_id"]
        rows.append(entry)
    resolution = {"schema_version": RESOLUTION_SCHEMA_VERSION, "plan_id": plan["plan_id"], "build": build,
                  "configurations": {k: {key: value for key, value in v.items()}
                                     for k, v in sorted(configurations.items())},
                  "trials": rows}
    resolution = {"resolution_id": identity("resolution-v1", resolution), **resolution}
    path = campaign / "resolution.json"
    if path.exists():
        require(canonical(load_json(path)) == canonical(resolution),
                "resolution.json already differs from this resolution; start a new campaign directory")
    atomic_json(path, resolution, immutable=True)
    return summarize(resolution, plan)


# A planning constant for the retained data volume's sequential write rate
# (a cloud block volume's included baseline throughput).
DISK_BYTES_PER_SECOND = 140 * 1024**2


def summarize(resolution, plan=None):
    counts, reasons = {}, {}
    stages = {}
    rows = {row["trial_id"]: row for row in plan["trials"]} if plan else {}
    for entry in resolution["trials"]:
        row = rows.get(entry["trial_id"])
        if row is None or entry["status"] != "runnable":
            continue
        stage = stages.setdefault(row["spec"]["stage"], {"full_event_bytes": 0, "pending_rate_rows": 0})
        buffer = entry["estimated_memory"]["event_buffer"]
        if row["spec"]["arrival"] != "saturated" and row["spec"]["instrumentation"]["logging"] == "full_events":
            if buffer is None:
                stage["pending_rate_rows"] += 1
            else:
                stage["full_event_bytes"] += buffer
    for stage in stages.values():
        # Retained raw bytes and the post-trial write time at that disk rate.
        stage["post_trial_write_seconds"] = round(stage["full_event_bytes"] / DISK_BYTES_PER_SECOND, 1)
    for entry in resolution["trials"]:
        counts[entry["status"]] = counts.get(entry["status"], 0) + 1
        for reason in entry["skip_reasons"] if entry["status"] == "skipped" else []:
            reasons[reason] = reasons.get(reason, 0) + 1
    duplicates = [{"trial_id": e["trial_id"], "same_as": e["same_as"]}
                  for e in resolution["trials"] if e["status"] == "same_as"]
    peak = max((e["estimated_memory_bytes"] for e in resolution["trials"]
                if e["status"] == "runnable"), default=None)
    return {"resolution_id": resolution["resolution_id"], "worker_sha256": resolution["build"]["worker_sha256"],
            "configurations": len(resolution["configurations"]), "status_counts": counts,
            "skip_reasons": reasons, "same_as": duplicates, "largest_runnable_estimate_bytes": peak,
            "full_event_storage_by_stage": stages}


def read_resolution(campaign, plan):
    path = Path(campaign) / "resolution.json"
    require(path.exists(), "campaign has no resolution.json; run `resolve` with the worker first")
    resolution = load_json(path)
    body = {k: v for k, v in resolution.items() if k != "resolution_id"}
    require(resolution["resolution_id"] == identity("resolution-v1", body), "resolution.json identity mismatch")
    require(resolution["plan_id"] == plan["plan_id"], "resolution.json belongs to another plan")
    require(resolution["schema_version"] == RESOLUTION_SCHEMA_VERSION, "unsupported resolution schema")
    return resolution


def entries(resolution):
    return {entry["trial_id"]: entry for entry in resolution["trials"]}


def executed_trial(resolution_entries, trial_id):
    """The trial whose attempts stand for this row (itself unless same_as)."""
    entry = resolution_entries[trial_id]
    return entry["same_as"] or trial_id
