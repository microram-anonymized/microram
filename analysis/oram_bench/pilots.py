"""Pilot trials into trial_time models: the per-arm time cap of the baseline comparison.

A pilot is an ordinary campaign run at a few capacities per arm. For each
completed trial this reads the worker's phase times (memory.csv) and drained
rate, then fits, per scheme, widths and API, a model at the largest pilot
capacity. Its capacity exponent is the steeper of the access and setup slopes
between the two largest capacities, so a model extrapolates upward
conservatively. A width piloted at one capacity only (the value-width shapes)
borrows the steepest exponent its scheme showed at the same API. The
margin covers what one pilot cannot: run-to-run spread, a coverage window
that must not end one access short, and a slower target.

`apply_trial_time` writes the fitted models into campaign presets. A width
a stage runs but the pilot did not gets a model interpolated log-log in block
bytes, at the stage's largest capacity, between the nearest piloted widths
(extrapolated from the end pair outside them): it is an estimate for the time
cap, so pilot the widths that land near it.
"""
import csv
import json
import math
from pathlib import Path

from .campaign import read_plan, successful
from .codec import load_json, require
from .resolution import read_resolution, entries

# Arms whose windows must cover rebuilds. H2O2RAM: two top rebuilds, about
# 2 x capacity accesses. For the level arena, and the tree's position map, a
# window holds at least N = capacity accesses: one full cycle of the largest
# level (the top takes a carry every capacity / D of them), so every level's
# rebuild cost is inside the measured window.
COVERAGE_PPM = {"h2o2ram": 2_000_000, "h2o2ram_shipped": 2_000_000,
                "hierarchical_incremental": 1_000_000, "hierarchical_synchronous": 1_000_000,
                "tree": 1_000_000, "auto": 1_000_000}


def _phases(path):
    with open(path, newline="") as stream:
        rows = list(csv.DictReader(stream))
    times = {row["phase"]: int(row["monotonic_ns"]) for row in rows}
    peak = max(int(row["high_water_rss_bytes"] or 0) for row in rows)
    return times, peak


def pilot_rows(campaign):
    """One record per verified complete trial of a campaign."""
    campaign = Path(campaign)
    plan = read_plan(campaign)
    resolved = entries(read_resolution(campaign, plan))
    records = []
    for row in plan["trials"]:
        found = successful(campaign, row["trial_id"])
        if found is None:
            continue
        attempt, manifest = found
        worker = attempt / "worker"
        summary = load_json(worker / "summary.json")
        times, peak = _phases(worker / "memory.csv")
        spec, entry = row["spec"], resolved[row["trial_id"]]
        ops = summary["drained_ops_per_second"]
        # Construction, fill and the final verification: everything but the measured window.
        setup = (times["after_fill"] - times["before_construction"]) + (times["after_verify"] - times["after_drain"])
        records.append({
            "campaign": plan["campaign"]["name"], "trial_id": row["trial_id"], "candidate": spec["candidate"],
            "scheme": spec["overrides"]["scheme"], "key_bytes": spec["shape"]["key_bytes"],
            "value_bytes": spec["shape"]["value_bytes"], "capacity": spec["requested_capacity"],
            "live_entries": row["live_entries"], "api_mode": spec["api_mode"],
            "caller_batch_size": spec["caller_batch_size"], "verified": manifest.get("correctness_verified"),
            "drained_ops_per_second": ops, "access_ns": 1e9 / ops if ops else None,
            "construction_ns": times["after_construction"] - times["before_construction"],
            "fill_ns": times["after_fill"] - times["after_construction"],
            "verify_ns": times["after_verify"] - times["after_drain"], "setup_ns": setup,
            "peak_rss_bytes": peak, "modeled_library_bytes": entry.get("modeled_buffer_bytes"),
            "modeled_reserved_bytes": entry.get("modeled_reserved_bytes"),
            "estimated_memory_bytes": entry.get("estimated_memory_bytes"),
            "peak_over_estimate": peak / entry["estimated_memory_bytes"] if entry.get("estimated_memory_bytes") else None})
    return records


def _slope(low, high, field):
    """d log(field / entry or access) / d log(capacity) between two pilot rows."""
    if low[field] is None or high[field] is None or low[field] <= 0 or high[field] <= 0:
        return 0.0
    per = (lambda r: r[field] / r["live_entries"]) if field == "setup_ns" else (lambda r: r[field])
    return max(0.0, math.log(per(high) / per(low)) / math.log(high["capacity"] / low["capacity"]))


def fit_trial_time(records, margin_ppm=250_000):
    """{scheme: [TrialTimeModel as JSON]}, one model per (widths, API) the pilot ran."""
    require(margin_ppm >= 0, "margin must be non-negative")
    groups = {}
    for record in records:
        if record["access_ns"] is None:
            continue
        key = (record["scheme"], record["key_bytes"], record["value_bytes"], record["api_mode"])
        groups.setdefault(key, []).append(record)
    scale = 1 + margin_ppm / 1_000_000
    exponents = {}
    for key, rows in groups.items():
        rows.sort(key=lambda r: r["capacity"])
        if len(rows) > 1 and rows[-2]["capacity"] < rows[-1]["capacity"]:
            exponents[key] = max(_slope(rows[-2], rows[-1], "access_ns"), _slope(rows[-2], rows[-1], "setup_ns"))
    models = {}
    for (scheme, key_bytes, value_bytes, api_mode), rows in sorted(groups.items()):
        reference = rows[-1]
        exponent = exponents.get((scheme, key_bytes, value_bytes, api_mode))
        if exponent is None:
            exponent = max((e for (c, _, _, a), e in exponents.items() if (c, a) == (scheme, api_mode)),
                           default=0.0)
        model = {"key_bytes": key_bytes, "value_bytes": value_bytes, "api_mode": api_mode,
                 "access_ns": math.ceil(reference["access_ns"] * scale),
                 "setup_ns_per_entry": math.ceil(reference["setup_ns"] / reference["live_entries"] * scale),
                 "reference_capacity": reference["capacity"],
                 "capacity_exponent_ppm": round(exponent * 1_000_000)}
        coverage = COVERAGE_PPM.get(scheme, 0)
        if coverage:
            model["coverage_accesses_per_entry_ppm"] = coverage
        models.setdefault(scheme, []).append(model)
    return models


def block_bytes(scheme, value_bytes):
    """What a baseline moves per entry: H2O2RAM's Block, ZingORAM's padded block object."""
    if scheme.startswith("h2o2ram"):
        return value_bytes + 8
    if scheme.startswith("sonic"):
        return -(-value_bytes // 8) * 8 + 24
    return value_bytes


def _at(model, capacity):
    ratio = (capacity / model["reference_capacity"]) ** (model["capacity_exponent_ppm"] / 1_000_000)
    return model["access_ns"] * ratio, model["setup_ns_per_entry"] * ratio


def interpolated_model(scheme, fitted, key_bytes, value_bytes, api_mode, capacity):
    """A model for an unpiloted width, from the piloted widths of the same API."""
    same = [m for m in fitted if m["api_mode"] == api_mode]
    require(bool(same), f"{scheme}: the pilot ran no {api_mode} rows")
    points = sorted((block_bytes(scheme, m["value_bytes"]), *_at(m, capacity), m) for m in same)
    target = block_bytes(scheme, value_bytes)
    below = [p for p in points if p[0] <= target]
    above = [p for p in points if p[0] >= target]
    if not below:
        pair = points[:2]
    elif not above:
        pair = points[-2:]
    else:
        pair = [below[-1], above[0]]
    low, high = pair[0], pair[-1]

    def estimate(index):
        if low[0] == high[0]:
            return low[index]
        t = math.log(target / low[0]) / math.log(high[0] / low[0])
        return math.exp((1 - t) * math.log(low[index]) + t * math.log(high[index]))
    nearest = min(points, key=lambda p: abs(math.log(p[0] / target)))[3]
    model = {"key_bytes": key_bytes, "value_bytes": value_bytes, "api_mode": api_mode,
             "access_ns": math.ceil(estimate(1)), "setup_ns_per_entry": math.ceil(estimate(2)),
             "reference_capacity": capacity, "capacity_exponent_ppm": nearest["capacity_exponent_ppm"]}
    if "coverage_accesses_per_entry_ppm" in nearest:
        model["coverage_accesses_per_entry_ppm"] = nearest["coverage_accesses_per_entry_ppm"]
    return model


def apply_trial_time(preset, fitted):
    """Replace the trial_time of every candidate whose scheme the pilot fitted; returns the preset."""
    for stage in preset["stages"]:
        modes = [m for m in ("scalar", "batch") if m in stage.get("api_modes", ["scalar", "batch"])]
        for candidate in stage["candidates"]:
            scheme = candidate["overrides"]["scheme"]
            if scheme not in fitted:
                continue
            models = []
            for shape in stage["shapes"]:
                for mode in modes:
                    exact = [m for m in fitted[scheme] if (m["key_bytes"], m["value_bytes"], m["api_mode"]) ==
                             (shape["key_bytes"], shape["value_bytes"], mode)]
                    model = exact[0] if exact else interpolated_model(
                        scheme, fitted[scheme], shape["key_bytes"], shape["value_bytes"], mode,
                        max(stage["capacities"]))
                    if model not in models:
                        models.append(model)
            candidate["trial_time"] = models
    return preset


def fit_campaigns(campaigns, margin_ppm=250_000, apply=()):
    records = [record for campaign in campaigns for record in pilot_rows(campaign)]
    fitted = fit_trial_time(records, margin_ppm)
    for path in apply:
        preset = apply_trial_time(json.loads(Path(path).read_text()), fitted)
        Path(path).write_text(json.dumps(preset, indent=2) + "\n")
    return {"margin_ppm": margin_ppm, "rows": records, "trial_time": fitted, "applied": [str(p) for p in apply],
            "note": "Each scheme's models go into its candidates' trial_time (--apply does it). A width the "
                    "pilot did not run is interpolated; a scheme it did not run keeps its models."}
