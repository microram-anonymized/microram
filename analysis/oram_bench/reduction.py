"""Verify committed artifacts and orchestrate the common C++ reducer."""
import csv
import json
from pathlib import Path
import subprocess

from .attestation import protection
from .campaign import _verify_replay, read_plan, reducer_inputs, successful, status, worker_verification
from .resolution import entries, executed_trial, read_resolution
from .schema import position_lookup_label
from .codec import identity, load_json, require
from .doctor import file_hash
from .memory import reduce_memory
from .store import atomic_json, verify

# A version-6 summary names the campaign, its frozen build and each group's
# build; carries each repetition's queue_stability and publication_blockers
# (publication_validated means "no blocker"); labels each row and group with
# its security label, key layout and stored value width (the baseline
# comparison labels); and gives each repetition's live entries, logical bytes
# and the library's modeled and reserved bytes (the amplification plot's
# inputs). Summaries are derived data: re-run `reduce` rather than adapting
# one of another version.
SUMMARY_SCHEMA_VERSION = 6


def load_campaign_summary(path):
    """Load a derived summary, without claiming to verify its raw artifacts.

    Run `reduce` to reverify a campaign's commits and regenerate this file.
    The complete document retains status inventory and per-repetition evidence.
    """
    document = load_json(path)
    version = document.get("campaign_summary_schema_version")
    require(type(version) is int and version == SUMMARY_SCHEMA_VERSION,
            "unsupported campaign summary; re-run reduce")
    require(isinstance(document.get("groups"), list), "campaign summary requires groups")
    require(isinstance(document.get("trial_status"), dict), "campaign summary requires trial_status")
    campaign = document.get("campaign")
    require(isinstance(campaign, dict) and type(campaign.get("name")) is str and
            campaign.get("plan_id") == document.get("plan_id") and "worker_sha256" in campaign,
            "campaign summary requires its campaign name, plan and build")
    seen_groups, seen_trials = set(), set()
    for group in document["groups"]:
        require("build_identity" in group, "repeat group requires its build")
        require(group["group_id"] not in seen_groups, "duplicate repeat group")
        seen_groups.add(group["group_id"])
        for row in group["repetitions"]:
            key = (row["environment_class"], row["trial_id"])
            require(key not in seen_trials, "duplicate trial repetition")
            seen_trials.add(key)
            require(row["environment_class"] == group["environment_class"] and
                    row["runtime"] == group["runtime"] and row["build_identity"] == group["build_identity"],
                    "repetition environment or build differs from group")
            spec = {k: v for k, v in row["spec"].items()
                    if k not in ("repetition", "workload_seed", "arrival_seed")}
            require(spec == group["spec"], "repetition configuration differs from group")
    return document


def committed_memory(attempt, manifest, metadata):
    """Only reduce observations covered by the already verified raw manifest."""
    captured = any(item["path"] == "worker/memory.csv" for item in manifest["artifacts"])
    version = metadata.get("memory_csv_schema_version")
    require(version is None or type(version) is int and version == 1, "unsupported worker memory CSV version")
    require(captured or version is None, "worker memory observations are absent from raw commit")
    if not captured:
        return None  # Old partial artifacts never acquire new coverage claims.
    return reduce_memory(attempt / "worker/memory.csv", interval_ns=metadata.get("memory_interval_ns"))


def observation_marker(repetition):
    memory = repetition.get("memory")
    if not repetition["summary"]["uncensored"] or (memory and memory["paging_status"] == "paging_observed"):
        return "x"
    if not memory or memory["paging_status"] == "unknown":
        return "+"
    return "o"


def marker_style(marker, color, blocked):
    """Hollow when a publication blocker applies. Unfilled markers (x, +) draw
    in their face color, so they stay as they are."""
    if blocked and marker not in ("x", "+"):
        return {"edgecolors": color, "facecolors": "none", "s": 22}
    return {"color": color, "s": 22}


def correctness_label(verification):
    """Rows run with verification off are labeled unverified."""
    return "verified" if verification == "full" else "unverified"


def cycle_coverage(metadata, minimum):
    """Design 4.2: whether the window held enough top-level carries.

    Unknown where the backend exposes no public counter (synthetic) or the
    worker predates coverage.
    """
    coverage = metadata.get("maintenance_coverage")
    if not coverage or not coverage["carries_by_level"]:
        return "unknown"
    return "sufficient" if coverage["carries_by_level"][-1] >= minimum else "insufficient_cycle_coverage"


# A stable offered load completes almost every arrival of [0, T) inside the
# horizon: only the last response time's worth is still waiting at T. A queue
# that grows (rho > 1) leaves about 1 - 1/rho of them waiting.
STABLE_HORIZON_COMPLETION_PPM = 990_000


def queue_stability(spec, summary):
    """Design 4.3: a stable tail needs no censoring and no backlog growth over the horizon."""
    if spec["arrival"] == "saturated":
        return "not_applicable"
    if not summary["uncensored"]:
        return "overloaded"
    offered = summary["offered"]
    if offered and summary["completed_during_horizon"] * 1_000_000 < offered * STABLE_HORIZON_COMPLETION_PPM:
        return "backlog_growth"
    return "stable"


def publication_blockers(spec, summary, memory, coverage, stability, protected_verified=False):
    """Why one repetition cannot be published as a steady-state result; empty when nothing blocks it.

    Blocked rows stay in every output, labeled.
    A campaign that requires protection needs a verified attestation verdict.
    Harness overhead blocks nothing (it is unstable and unavoidable, and
    charging it only favors the slower prior schemes); the harness gate
    records (validation.py) are reported evidence, and the worker's own
    `publication_validated` flag is ignored.
    """
    blockers = []
    if spec.get("diagnostic"):
        blockers.append("diagnostic_stage")
    if spec.get("execution", {}).get("require_protected") and not protected_verified:
        blockers.append("protection_unverified")
    if coverage != "sufficient":
        blockers.append("cycle_coverage_" + ("unknown" if coverage == "unknown" else "insufficient"))
    paging = memory["paging_status"] if memory else "unknown"
    if paging != "no_paging_observed":
        blockers.append("paging_observed" if paging == "paging_observed" else "paging_unknown")
    if stability in ("overloaded", "backlog_growth"):
        blockers.append("queue_" + stability)
    if spec["arrival"] != "saturated" and not summary["response"]["p99_sufficient_samples"]:
        blockers.append("p99_insufficient_samples")
    return blockers


def row_labels(row, entry):
    """The security label and stored value width (baseline row labels) for one plan row.

    Plans made before the baselines carry none: their rows are library rows
    with permuted keys. A synthetic rehearsal's resolution labels every row
    not_oblivious, whatever its scheme.
    """
    security = (entry or {}).get("security") or row.get("security", "oblivious")
    return {"security": security, "position_lookup": position_lookup_label(row["spec"].get("overrides", {}).get("scheme")),
            "key_layout": row.get("key_layout", "permuted"),
            "stored_value_bytes": row.get("stored_value_bytes", row["spec"]["shape"]["value_bytes"])}


def trial_cpu(metadata):
    """CPU-seconds over the worker's trial call (measurement and drain).

    `library` is the process less the caller (request), telemetry and checkpoint
    threads: the library's own threads, which at low offered rates is their idle
    CPU (spinning or waiting). None for workers that predate the field.
    """
    cpu = metadata.get("trial_cpu_ns")
    if not cpu:
        return None
    checkpoint = cpu.get("checkpoint_thread", 0)  # absent before the checkpoint thread
    library = max(0, cpu["process"] - cpu["caller_thread"] - cpu["telemetry_thread"] - checkpoint)
    return {"process_cpu_seconds": cpu["process"] / 1e9, "caller_cpu_seconds": cpu["caller_thread"] / 1e9,
            "telemetry_cpu_seconds": cpu["telemetry_thread"] / 1e9,
            "checkpoint_cpu_seconds": checkpoint / 1e9, "library_cpu_seconds": library / 1e9,
            "wall_seconds": cpu["wall"] / 1e9,
            "library_cores_busy": library / cpu["wall"] if cpu["wall"] else None}


def memory_model(row, entry):
    """The row's logical data and the library's modelled bytes, for amplification.

    Logical bytes are live entries times (key + value): what an ideal
    unprotected table would hold. The library's figures come from the
    resolution (requested and, where the resolver reports it, reserved: its
    buffers with the allocator's rounding); a synthetic row has none.
    """
    shape = row["spec"]["shape"]
    live = row.get("live_entries")
    entry = entry or {}
    modeled = entry.get("modeled_buffer_bytes") or None
    return {"live_entries": live,
            "logical_bytes": live * (shape["key_bytes"] + shape["value_bytes"]) if live else None,
            "library_modeled_bytes": modeled,
            "library_reserved_bytes": entry.get("modeled_reserved_bytes") if modeled else None}


def _time_blocks(reducer, attempt, manifest, metadata):
    """Checkpoint trials only: the C++ reducer's per-block statistics and across-block spread.

    Blocks cover measurement plus drain and are not independent repetitions;
    event-log trials have no block boundaries and report None.
    """
    paths = sorted(attempt / a["path"] for a in manifest["artifacts"]
                   if a["path"].startswith("worker/checkpoint") and a["path"].endswith(".bin"))
    if not paths:
        return None
    cwd, names = reducer_inputs(paths)
    result = subprocess.run([str(Path(reducer).resolve()), "--blocks", "--minimum-tail-count",
                             str(metadata["minimum_tail_count"]), *names], capture_output=True, text=True,
                            timeout=120, cwd=cwd)
    require(result.returncode == 0, "C++ block reduction failed: " + result.stderr)
    document = json.loads(result.stdout)
    return {"blocks": document["blocks"], "block_spread": document["block_spread"]}


def reduce_campaign(campaign, reducer, output):
    campaign, reducer, output = Path(campaign).resolve(), Path(reducer).resolve(strict=True), Path(output)
    plan = read_plan(campaign)
    resolution = read_resolution(campaign, plan) if (campaign / "resolution.json").exists() else None
    resolved = entries(resolution) if resolution is not None else None
    build = resolution["build"] if resolution is not None else {}
    environments = {}
    for path in (campaign / "environments").glob("*.json"):
        environment = load_json(path)
        require(path.stem == identity("environment-v1", environment), "environment identity differs")
        environments[environment["environment_class"]] = environment
    rows, groups = [], {}
    for row in plan["trials"]:
        for environment_class, environment in sorted(environments.items()):
            # A same_as row reports its representative's attempt under its own label.
            executed = executed_trial(resolved, row["trial_id"]) if resolved else row["trial_id"]
            selected = successful(campaign, executed, environment_class)
            if selected is None:
                continue
            attempt, manifest = selected
            # Reduction re-hashes every raw byte and replays exactly the
            # manifest's chunks. Derived summaries are written only under
            # the output directory, never inside a committed attempt.
            manifest = verify(attempt, deep=True)
            chunks = [attempt / a["path"] for a in manifest["artifacts"]
                      if a["path"].startswith("worker/events/") and a["path"].endswith(".bin")]
            summary, metadata = _verify_replay(reducer, attempt / "worker", require_live=False, chunks=sorted(chunks))
            memory = committed_memory(attempt, manifest, metadata)
            time_blocks = _time_blocks(reducer, attempt, manifest, metadata) if not chunks else None
            # Only repetitions and their independent seeds leave this key.
            # Workload/batch/rate/logging/runtime/build settings all remain.
            spec = {k: v for k, v in row["spec"].items() if k not in
                    ("repetition", "workload_seed", "arrival_seed")}
            group_id = identity("repeat-group-v1", [environment_class, spec])
            coverage = cycle_coverage(metadata, row["spec"].get("timing", {}).get("minimum_top_level_carries", 2))
            stability = queue_stability(row["spec"], summary)
            # Each attempt's own environment names its boot's attestation capture.
            protected, verification = protection(campaign, load_json(
                campaign / "environments" / (manifest["environment_id"] + ".json")))
            offered = load_json(attempt / "requested.json")["frozen_rate"]
            blockers = publication_blockers(row["spec"], summary, memory, coverage, stability, protected)
            labels = row_labels(row, resolved[row["trial_id"]] if resolved else None)
            record = {"trial_id": row["trial_id"], "executed_trial_id": executed, **labels,
                      **memory_model(row, resolved[row["trial_id"]] if resolved else None),
                      "attempt_id": manifest["attempt_id"],
                      "environment_class": environment_class, "runtime": environment["runtime"],
                      "protected_verified": protected, "verification_reference": verification,
                      "build_identity": environment["build_identity"],
                      "spec": row["spec"], "summary": summary,
                      "memory": memory, "correctness": correctness_label(worker_verification(metadata)),
                      "cycle_coverage": coverage, "time_blocks": time_blocks,
                      "top_level_carries": (metadata.get("maintenance_coverage") or
                                            {"carries_by_level": [None]})["carries_by_level"][-1],
                      "queue_stability": stability, "publication_blockers": blockers,
                      "publication_validated": not blockers,
                      "batch_sizes": metadata["batch_sizes"], "trial_cpu": trial_cpu(metadata),
                      "offered_ops_per_second": offered}
            rows.append(record)
            # The class includes the worker hash, so a group never spans builds.
            group = groups.setdefault(group_id, {"group_id": group_id,
                "environment_class": environment_class, "runtime": environment["runtime"],
                "build_identity": environment["build_identity"], "spec": spec, **labels, "repetitions": []})
            group["repetitions"].append(record)
    for group in groups.values():
        args = [str(reducer)]
        for row in group["repetitions"]:
            summary = row["summary"]
            args += ["--repeat", str(summary["completed"]), str(summary["caller_end_ns"]), str(summary["drain_end_ns"])]
        result = subprocess.run(args, capture_output=True, text=True, timeout=120)
        require(result.returncode == 0, "C++ repetition reduction failed: " + result.stderr)
        group["throughput"] = json.loads(result.stdout)
    # `plot` labels every series by campaign and build and never
    # pools across them. The build is the one `resolve` froze (null before it).
    identity_record = {"name": plan["campaign"]["name"], "plan_id": plan["plan_id"],
                       "worker_sha256": build.get("worker_sha256"),
                       "library_header_sha256": build.get("library_header_sha256")}
    result = {"campaign_summary_schema_version": SUMMARY_SCHEMA_VERSION, "plan_id": plan["plan_id"],
              "campaign": identity_record,
              "reducer_sha256": file_hash(reducer), "trial_status": status(campaign),
              "groups": [groups[k] for k in sorted(groups)]}
    atomic_json(output / "summary.json", result)
    # CSV is derived convenience data. Authoritative distributions stay in the
    # per-repetition JSON; censored distributions remain labeled as such.
    output.mkdir(parents=True, exist_ok=True)
    with open(output / "repetitions.csv", "w", newline="") as stream:
        columns = ["campaign", "build_identity", "trial_id", "attempt_id", "environment_class", "runtime",
                   "protected_verified", "candidate", "scheme", "security", "position_lookup", "capacity", "key_bytes", "key_layout",
                   "value_bytes", "stored_value_bytes", "api", "arrival", "completed", "rejected",
                   "outstanding", "drained_ops_per_second", "correctness", "cycle_coverage", "top_level_carries",
                   "queue_stability", "publication_blockers", "response_p99_ns", "response_p999_ns",
                   "p99_sufficient_samples", "p999_sufficient_samples", "publication_validated",
                   "paging_status", "sampled_envelope_rss_bytes", "sampled_envelope_pss_bytes",
                   "trial_peak_rss_bytes", "measurement_major_faults", "live_entries", "logical_bytes",
                   "library_modeled_bytes", "library_reserved_bytes", "diagnostic",
                   "library_cpu_seconds", "process_cpu_seconds", "trial_wall_seconds"]
        writer = csv.DictWriter(stream, fieldnames=columns)
        writer.writeheader()
        for row in rows:
            spec, summary = row["spec"], row["summary"]
            memory = row["memory"]
            envelope = memory["measurement_envelope"] if memory else {}
            peaks = envelope.get("sampled_max_bytes", {})
            writer.writerow({"campaign": identity_record["name"],
                **{k: row[k] for k in ("build_identity", "trial_id", "attempt_id", "environment_class",
                                       "runtime", "protected_verified", "publication_validated", "correctness", "cycle_coverage",
                                       "top_level_carries", "queue_stability", "security", "position_lookup",
                                       "key_layout",
                                       "stored_value_bytes")},
                "candidate": spec.get("candidate"), "scheme": spec.get("overrides", {}).get("scheme"),
                "publication_blockers": ";".join(row["publication_blockers"]),
                "capacity": spec["requested_capacity"], "key_bytes": spec["shape"]["key_bytes"],
                "value_bytes": spec["shape"]["value_bytes"], "api": spec["api_mode"], "arrival": spec["arrival"],
                **{k: summary[k] for k in ("completed", "rejected", "outstanding", "drained_ops_per_second")},
                "response_p99_ns": summary["response"]["p99_ns"], "response_p999_ns": summary["response"]["p999_ns"],
                "p99_sufficient_samples": summary["response"]["p99_sufficient_samples"],
                "p999_sufficient_samples": summary["response"]["p999_sufficient_samples"],
                "paging_status": memory["paging_status"] if memory else "unknown",
                "sampled_envelope_rss_bytes": peaks.get("rss_bytes"),
                "sampled_envelope_pss_bytes": peaks.get("pss_bytes"),
                "trial_peak_rss_bytes": memory["trial_peak_rss_bytes"] if memory else None,
                "measurement_major_faults": envelope.get("fault_deltas", {}).get("major_faults"),
                **{k: row[k] for k in ("live_entries", "logical_bytes", "library_modeled_bytes",
                                       "library_reserved_bytes")},
                "diagnostic": bool(spec.get("diagnostic")),
                "library_cpu_seconds": (row["trial_cpu"] or {}).get("library_cpu_seconds"),
                "process_cpu_seconds": (row["trial_cpu"] or {}).get("process_cpu_seconds"),
                "trial_wall_seconds": (row["trial_cpu"] or {}).get("wall_seconds")})
    return {"output": str(output), "campaign": identity_record["name"],
            "worker_sha256": identity_record["worker_sha256"], "groups": len(groups), "repetitions": len(rows)}


def series_family(group, with_campaign=True):
    """What a series is colored by: every configuration axis a panel does not plot.

    Groups of one family differ only in what the panels put on their axes
    (capacity, rate, value width) or in fields the family's legend does not
    need; each group is still drawn as its own series.
    """
    spec = group["spec"]
    shape = spec.get("shape", {})
    parts = [spec["candidate"], spec["api_mode"], group["security"]]
    if group.get("position_lookup"):  # SONIC rows include their position lookup
        parts.append(f"position lookup {group['position_lookup']}")
    if "key_bytes" in shape and "value_bytes" in shape:
        parts.append(f"k{shape['key_bytes']}:v{shape['value_bytes']}")
    if spec.get("instrumentation", {}).get("verification") == "off":
        parts.append("unverified")
    if with_campaign:
        parts = [group["campaign_label"], group["runtime"], *parts]
    return " / ".join(parts)


def series(summaries):
    """(label, color, summary, group) per repeat group across campaign summaries.

    A label names the campaign and the build that produced the group. Two groups that would share a label, which includes the same summary
    given twice, are refused rather than drawn as one series. The color is the
    group's FAMILY's (series_family), so a figure with hundreds of series needs
    a legend of families, not of series; series.csv maps each label to it.
    """
    result, seen, families = [], {}, {}
    for summary in summaries:
        for group in summary["groups"]:
            build = group["build_identity"] or "sha256-unknown"
            group["campaign_label"] = f"{summary['campaign']['name']}@{build.removeprefix('sha256-')[:8]}"
    # The campaign and runtime name a family only when the figure holds more
    # than one; with one they are the title's.
    several = len({(group["campaign_label"], group["runtime"])
                   for summary in summaries for group in summary["groups"]}) > 1
    for index, summary in enumerate(summaries):
        for group in summary["groups"]:
            spec = group["spec"]
            # Every series names its security label.
            label = (f"{group['campaign_label']} / {group['runtime']} / {spec['candidate']} / "
                     f"{spec['api_mode']} / {group['security']} / {group['group_id'][-8:]}")
            if group.get("position_lookup"):
                label += f" / position lookup {group['position_lookup']}"
            if spec.get("instrumentation", {}).get("verification") == "off":
                label += " / unverified"
            require(label not in seen, f"summaries {seen.get(label)} and {index} both contain series {label!r}; "
                    "series from one campaign name, build and configuration are not merged: plot them "
                    "separately or give the campaigns distinct names")
            seen[label] = index
            group["family"] = family = series_family(group, with_campaign=several)
            color = families.setdefault(family, _family_color(len(families)))
            result.append((label, color, summary, group))
    return result


def _family_color(index):
    """tab20's colors, then tab20b's: 40 before a color repeats."""
    import matplotlib
    palette = matplotlib.colormaps["tab20"].colors + matplotlib.colormaps["tab20b"].colors
    return palette[index % len(palette)]


def _family_legend(fig, groups):
    """One legend for the whole figure, of families, outside the axes."""
    from matplotlib.lines import Line2D
    families = {}
    for _, color, _, group in groups:
        families.setdefault(group["family"], color)
    if not families:
        return None
    handles = [Line2D([], [], marker="o", linestyle="", color=color) for color in families.values()]
    return fig.legend(handles, list(families), loc="center left", bbox_to_anchor=(1.0, 0.5), fontsize=6,
                      title="series family", title_fontsize=7)


def _write_series_table(groups, path):
    with open(path, "w", newline="") as stream:
        writer = csv.writer(stream)
        writer.writerow(["label", "family", "color", "group_id", "campaign", "runtime", "candidate", "api",
                         "security", "key_bytes", "value_bytes", "capacity", "arrival", "repetitions"])
        for label, color, _, group in groups:
            spec = group["spec"]
            shape = spec.get("shape", {})
            writer.writerow([label, group["family"], "#%02x%02x%02x" % tuple(int(255 * c) for c in color[:3]),
                             group["group_id"], group["campaign_label"], group["runtime"], spec["candidate"],
                             spec["api_mode"], group["security"], shape.get("key_bytes"),
                             shape.get("value_bytes"), spec.get("requested_capacity"), spec.get("arrival"),
                             len(group["repetitions"])])


def _plot_targets(plt, summaries, groups, output):
    """Cross-target figure: one column per campaign (a campaign runs on one
    target, e.g. a TDX guest, its native control, an SEV-SNP guest), sharing both axes, with each
    family one color in every column so the columns compare directly."""
    columns = sorted({group["campaign_label"] for _, _, _, group in groups})
    families = {}
    for _, _, _, group in groups:
        families.setdefault(series_family(group, with_campaign=False), _family_color(len(families)))
    fig, axes = plt.subplots(2, len(columns), figsize=(5 * len(columns), 8), sharex="row", sharey="row",
                             squeeze=False)
    for column, campaign in enumerate(columns):
        runtimes = set()
        for label, _, _, group in groups:
            if group["campaign_label"] != campaign:
                continue
            runtimes.add(group["runtime"])
            spec, color = group["spec"], families[series_family(group, with_campaign=False)]
            for repetition in group["repetitions"]:
                values = repetition["summary"]
                marker = observation_marker(repetition)
                style = marker_style(marker, color, bool(repetition["publication_blockers"]))
                if spec["arrival"] == "saturated":
                    axes[0][column].scatter(spec["requested_capacity"], values["drained_ops_per_second"],
                                            marker=marker, **style)
                elif values["response"]["p99_ns"] is not None:
                    axes[1][column].scatter(repetition["offered_ops_per_second"], values["response"]["p99_ns"] / 1e3,
                                            marker=marker, **style)
        axes[0][column].set_title(f"{campaign} ({', '.join(sorted(runtimes))})", fontsize=9)
        axes[0][column].set_xlabel("Requested capacity")
        axes[1][column].set_xlabel("Offered input rate (ops/s)")
        axes[1][column].set_xscale("log")
        for axis in (axes[0][column], axes[1][column]):
            axis.grid(alpha=.2)
    axes[0][0].set_xscale("log", base=2)
    axes[0][0].set_ylabel("Drained throughput (ops/s)")
    axes[1][0].set_ylabel("Response p99 (us)")
    from matplotlib.lines import Line2D
    handles = [Line2D([], [], marker="o", linestyle="", color=color) for color in families.values()]
    fig.legend(handles, list(families), loc="center left", bbox_to_anchor=(1.0, 0.5), fontsize=6,
                        title="series family", title_fontsize=7)
    fig.suptitle("One column per campaign; x = censored/paging, + = unknown paging, hollow = a publication "
                 "blocker applies. Series are never pooled across columns.", fontsize=10)
    fig.tight_layout()
    for suffix in ("png", "pdf"):
        fig.savefig(output / ("targets." + suffix), dpi=150, bbox_inches="tight")
    plt.close(fig)


def plot_summary(summary_paths, output):
    """Plot one or more reduced campaign summaries (each `reduce` output's summary.json)."""
    # Optional plotting dependency only; never imported by plan/run/recovery.
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
    except ImportError as error:
        raise ValueError("plot requires matplotlib in the offline analysis environment") from error
    if isinstance(summary_paths, (str, Path)):
        summary_paths = [summary_paths]
    require(bool(summary_paths), "plot needs at least one summary")
    summaries = [load_campaign_summary(path) for path in summary_paths]
    # Diagnostic stages never enter a figure; repetitions.csv keeps them.
    for summary in summaries:
        summary["groups"] = [g for g in summary["groups"] if not g["spec"].get("diagnostic")]
    groups = series(summaries)
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    # Each point remains one repetition. Do not connect different environments,
    # instruments or schemes into a curve, and do not average tail percentiles.
    fig, axes = plt.subplots(1, 3, figsize=(15, 4))
    for label, color, _, group in groups:
        spec = group["spec"]
        for repetition in group["repetitions"]:
            values = repetition["summary"]
            marker = observation_marker(repetition)
            blocked = bool(repetition["publication_blockers"])
            if spec["arrival"] == "saturated":
                spread = ((repetition.get("time_blocks") or {}).get("block_spread") or {}).get(
                    "throughput_ops_per_second")
                if spread and spread["blocks"] > 1:  # across-time-block min/max, not a confidence interval
                    for axis, x in ((axes[0], spec["requested_capacity"]), (axes[2], spec["shape"]["value_bytes"])):
                        axis.vlines(x, spread["minimum"], spread["maximum"], color=color, alpha=.4, lw=1)
                axes[0].scatter(spec["requested_capacity"], values["drained_ops_per_second"], marker=marker,
                                label=label, **marker_style(marker, color, blocked))
                axes[2].scatter(spec["shape"]["value_bytes"], values["drained_ops_per_second"], marker=marker,
                                label=label, **marker_style(marker, color, blocked))
            elif values["response"]["p99_ns"] is not None:
                offered = repetition["offered_ops_per_second"]
                if offered:
                    axes[1].scatter(offered, values["response"]["p99_ns"] / 1e3,
                                    marker=marker, label=label, **marker_style(marker, color, blocked))
    for axis, xlabel, ylabel in zip(axes,
            ("Requested capacity", "Offered input rate (ops/s)", "Value bytes"),
            ("Drained throughput (ops/s)", "Response p99 (us)", "Drained throughput (ops/s)")):
        axis.set_xlabel(xlabel); axis.set_ylabel(ylabel); axis.grid(alpha=.2)
    axes[1].set_xscale("log")
    _family_legend(fig, groups)
    counts = "; ".join(f"{s['campaign']['name']}: {s['trial_status']['counts']}" for s in summaries)
    fig.suptitle("x = censored/paging, + = unknown paging, hollow = a publication blocker applies; "
                 "line = min/max over time blocks (not a CI). Status: " + counts, fontsize=10)
    fig.tight_layout()
    for suffix in ("png", "pdf"):
        fig.savefig(output / ("campaign." + suffix), dpi=150, bbox_inches="tight")
    plt.close(fig)
    _write_series_table(groups, output / "series.csv")
    # Memory: the sampled RSS, and AMPLIFICATION -- bytes over the logical
    # data, live x (key + value) -- for the library's model (hollow) and the
    # trial's peak RSS (filled), both against capacity.
    memory_fig, memory_axes = plt.subplots(1, 3, figsize=(15, 4))
    missing = 0
    for label, color, _, group in groups:
        spec = group["spec"]
        for repetition in group["repetitions"]:
            memory = repetition.get("memory")
            envelope = memory["measurement_envelope"] if memory else {}
            rss = envelope.get("sampled_max_bytes", {}).get("rss_bytes")
            marker = observation_marker(repetition)
            if rss is None:
                missing += 1
            else:
                for axis, x in zip(memory_axes, (spec["requested_capacity"], spec["shape"]["value_bytes"])):
                    axis.scatter(x, rss / 2**20, marker=marker, label=label, color=color, s=22)
            logical = repetition.get("logical_bytes")
            if not logical:
                continue
            library = repetition.get("library_reserved_bytes") or repetition.get("library_modeled_bytes")
            if library:
                memory_axes[2].scatter(spec["requested_capacity"], library / logical, marker="o",
                                       edgecolors=color, facecolors="none", s=22)
            peak = memory.get("trial_peak_rss_bytes") if memory else None
            if peak:
                memory_axes[2].scatter(spec["requested_capacity"], peak / logical, marker=marker,
                                       color=color, s=22)
    for axis, xlabel, ylabel in zip(memory_axes, ("Requested capacity", "Value bytes", "Requested capacity"),
            ("Sampled process RSS maximum (MiB)", "Sampled process RSS maximum (MiB)",
             "Bytes / (live x (key + value))")):
        axis.set_xlabel(xlabel)
        axis.set_ylabel(ylabel)
        axis.grid(alpha=.2)
    memory_axes[2].set_xscale("log", base=2)
    memory_axes[2].set_yscale("log")
    memory_axes[2].set_title("hollow: library model (reserved bytes); filled: trial peak RSS", fontsize=8)
    _family_legend(memory_fig, groups)
    memory_fig.suptitle("RSS: before measure through after drain; includes harness/logging.\n"
        f"x = censored/paging, + = unknown paging; missing RSS: {missing}. Unvalidated.", fontsize=10)
    memory_fig.tight_layout()
    for suffix in ("png", "pdf"):
        memory_fig.savefig(output / ("memory." + suffix), dpi=150, bbox_inches="tight")
    plt.close(memory_fig)
    if len(summaries) > 1:
        _plot_targets(plt, summaries, groups, output)
    return {"output": str(output), "series": [label for label, _, _, _ in groups], "publication_validated": False}
