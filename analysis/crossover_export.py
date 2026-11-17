#!/usr/bin/env python3
"""Fixed-N scheme crossovers and the auto check, from a reduced campaign.

Input: a `reduce` summary.json and, for the resolved scheme, configuration key,
same_as, worker counts and choices, the campaign's resolution.json (read from
the campaign directory by `reduce`; pass it with --resolution).  Output, in
--output: crossovers.json and widths.csv.

Frontiers.  Rows are grouped by (key_bytes, requested_capacity, api_mode): a
crossover is never computed across rows whose N differs (the input is split by
capacity, and a frontier whose resolved actual_capacity changes with width is
refused).  With --per-batch the caller batch size also splits a frontier;
otherwise each scheme's fastest setting at a width is chosen over every
candidate and batch size, and the winning candidate and batch are named.

Arms.  A group whose candidate name contains "frozen" is the geometry-frozen
arm: reported apart, never a frontier candidate.  A group whose
overrides.scheme is "auto" is the auto arm: its scheme is the RESOLVED scheme
(resolution.json), and it is checked, not compared.  Every other group is a
frontier candidate of its resolved scheme.  The two compared schemes are the
two distinct frontier schemes in the data (or --schemes A,B); rows of any
other scheme are listed, not compared.  Rows with publication_blockers stay
(labelled, with their blockers); a cell that rests on one says so.

Per width and scheme (the fastest row, by median drained_ops_per_second over
repetitions): throughput; allocated amplification = library_reserved_bytes
(else library_modeled_bytes, named per row) / logical_bytes; RSS amplification
= max trial_peak_rss_bytes / logical_bytes.  Memory is read off the fastest
row, not minimised over candidates.

Crossover (throughput, allocated, rss separately).  At each width where both
schemes have the metric, the winner is the higher throughput or the lower
amplification; exact ties are skipped.  Whenever the winner changes between
consecutive compared widths, a bracket [last width the previous winner wins,
first width the new winner wins] in value bytes is listed (every sign change).
No change gives "no_crossing" and the scheme that wins at every compared
width.  The allocated metric compares only widths where both rows use the same
byte basis.

Auto check: per width, the scheme auto resolved to against the scheme that
measured faster at that width: agree/disagree.  Auto is an uncalibrated policy
(DefaultRule in include/cpu_byteslice_oram/default_rule.hpp); the check judges
it against measurements, not against a cost-model threshold.

Reads (reduction.py `reduce_campaign`): group.spec.{shape.key_bytes,
shape.value_bytes, requested_capacity, candidate, overrides.scheme, api_mode,
caller_batch_size}, group.security, group.repetitions[].{trial_id,
summary.drained_ops_per_second, memory.trial_peak_rss_bytes, logical_bytes,
library_modeled_bytes, library_reserved_bytes, publication_blockers}.
resolution.json: trials[].{trial_id, configuration_id, configuration_key,
same_as, actual_capacity, modeled_reserved_bytes}, configurations[id].{scheme,
library_threads, resolved.{choices, threads}}.
"""
import argparse
import csv
import json
import os
import statistics
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from oram_bench.codec import ValidationError, require  # noqa: E402

AUTO_NOTE = ("auto is an uncalibrated policy (DefaultRule in "
             "include/cpu_byteslice_oram/default_rule.hpp); this check compares it with measurements")
CHOICE_PREFIXES = ("hierarchy.", "tree.", "position_map.")
METRICS = ("throughput", "allocated", "rss")


def _median(values):
    values = [v for v in values if v is not None]
    return statistics.median(values) if values else None


def _ratio(num, den):
    return num / den if num is not None and den else None


def load_resolution(resolution):
    if resolution is None:
        return None, None
    return {t["trial_id"]: t for t in resolution["trials"]}, resolution.get("configurations", {})


def row_of(group, trials, configurations):
    """One export row from a summary group (and its resolution entry)."""
    spec = group["spec"]
    reps = group["repetitions"]
    require(reps, "group %s has no repetitions" % group.get("group_id"))
    requested = spec.get("overrides", {}).get("scheme", "auto")
    entry = config = resolved = None
    if trials is not None:
        entry = trials.get(reps[0]["trial_id"])
        require(entry is not None, "trial %s is not in the resolution" % reps[0]["trial_id"])
        config = configurations.get(entry.get("configuration_id"), {})
        resolved = config.get("resolved") or {}
    scheme = (config or {}).get("scheme") or (None if requested == "auto" else requested)
    require(scheme is not None, "overrides.scheme is auto in group %s: --resolution is needed to know "
            "what it resolved to" % group.get("group_id"))
    candidate = spec["candidate"]
    arm = "frozen" if "frozen" in candidate else "auto" if requested == "auto" else "frontier"
    logical = _median([r.get("logical_bytes") for r in reps])
    basis = None
    allocated = None
    for name in ("library_reserved_bytes", "library_modeled_bytes"):
        allocated = _median([r.get(name) for r in reps])
        if allocated:
            basis = name
            break
    peaks = [(r.get("memory") or {}).get("trial_peak_rss_bytes") for r in reps]
    peak = max([p for p in peaks if p is not None], default=None)
    blockers = sorted({b for r in reps for b in r.get("publication_blockers", [])})
    threads = (resolved or {}).get("threads") or []
    roles = {}
    for thread in threads:
        roles[str(thread["role"])] = roles.get(str(thread["role"]), 0) + 1
    choices = {c["field"]: {"value": c["value"], "source": c.get("source")}
               for c in (resolved or {}).get("choices", []) if c["field"].startswith(CHOICE_PREFIXES)}
    return {
        "group_id": group.get("group_id"), "trial_id": reps[0]["trial_id"], "arm": arm,
        "candidate": candidate, "requested_scheme": requested, "scheme": scheme,
        "security": group.get("security"), "key_bytes": spec["shape"]["key_bytes"],
        "value_bytes": spec["shape"]["value_bytes"], "requested_capacity": spec["requested_capacity"],
        "actual_capacity": (entry or {}).get("actual_capacity"), "api_mode": spec["api_mode"],
        "caller_batch_size": spec.get("caller_batch_size"), "repetitions": len(reps),
        "drained_ops_per_second": _median([r["summary"]["drained_ops_per_second"] for r in reps]),
        "logical_bytes": logical, "allocated_bytes": allocated, "allocated_basis": basis,
        "allocated_amplification": _ratio(allocated, logical), "peak_rss_bytes": peak,
        "rss_amplification": _ratio(peak, logical),
        "publication_blockers": blockers, "blocked": bool(blockers),
        "resolved_scheme": scheme if config is not None else None,
        "configuration_key": (entry or {}).get("configuration_key"),
        "same_as": (entry or {}).get("same_as"),
        "library_threads": (config or {}).get("library_threads"), "worker_role_counts": roles or None,
        "choices": choices}


def _winner(metric, a, b):
    """'a' or 'b' (or None on a tie / missing) and the two compared values."""
    if metric == "throughput":
        x, y = a["drained_ops_per_second"], b["drained_ops_per_second"]
        better_a = x > y if None not in (x, y) else None
    else:
        key = "allocated_amplification" if metric == "allocated" else "rss_amplification"
        x, y = a[key], b[key]
        if None in (x, y) or (metric == "allocated" and a["allocated_basis"] != b["allocated_basis"]):
            return None, x, y
        better_a = x < y
    if x is None or y is None or x == y:
        return None, x, y
    return ("a" if better_a else "b"), x, y


def crossover(metric, cells, names):
    """Brackets of one metric over width-sorted cells {width: {'a': row, 'b': row}}."""
    sequence, skipped = [], []
    for width in sorted(cells):
        who, x, y = _winner(metric, cells[width]["a"], cells[width]["b"]) if "a" in cells[width] and "b" in cells[width] \
            else (None, None, None)
        if who is None:
            skipped.append(width)
        else:
            sequence.append((width, who, x, y))
    brackets = []
    for (w0, who0, *_), (w1, who1, *_) in zip(sequence, sequence[1:]):
        if who0 != who1:
            brackets.append({"bracket_bytes": [w0, w1], "last_winner_before": names[who0],
                             "first_winner_after": names[who1],
                             "uses_blocked_rows": any(cells[w][s]["blocked"] for w in (w0, w1) for s in "ab")})
    result = {"metric": metric, "widths_compared": [s[0] for s in sequence],
              "widths_not_compared": skipped}
    if not sequence:
        result.update(status="not_comparable", brackets=[], direction=None)
    elif brackets:
        result.update(status="crossing", brackets=brackets, direction=None)
    else:
        result.update(status="no_crossing", brackets=[], direction="%s wins at every compared width"
                      % names[sequence[0][1]])
    return result


def frontier_report(rows, names, key_bytes, capacity, api_mode, batch):
    require(len({r["requested_capacity"] for r in rows}) == 1, "a frontier never mixes capacities")
    actual = {r["actual_capacity"] for r in rows if r["actual_capacity"] is not None}
    for scheme in {r["scheme"] for r in rows}:
        per_scheme = {r["actual_capacity"] for r in rows if r["scheme"] == scheme and r["actual_capacity"] is not None}
        require(len(per_scheme) <= 1, "actual capacity of %s changes with width within a frontier (%s): "
                "N must be fixed" % (scheme, sorted(per_scheme)))
    best = {}
    for row in rows:
        if row["arm"] != "frontier" or row["scheme"] not in names.values():
            continue
        side = "a" if row["scheme"] == names["a"] else "b"
        cell = best.setdefault(row["value_bytes"], {})
        old = cell.get(side)
        if old is None or (row["drained_ops_per_second"] or -1) > (old["drained_ops_per_second"] or -1):
            cell[side] = row
    cells = {w: c for w, c in best.items()}
    widths = []
    for width in sorted(cells):
        entry = {"value_bytes": width}
        for side in "ab":
            row = cells[width].get(side)
            entry[names[side]] = None if row is None else {
                k: row[k] for k in ("candidate", "caller_batch_size", "drained_ops_per_second", "allocated_amplification",
                                    "allocated_basis", "rss_amplification", "publication_blockers", "blocked", "trial_id")}
        widths.append(entry)
    autos = {}
    for row in rows:
        if row["arm"] == "auto":
            old = autos.get(row["value_bytes"])
            if old is None or (row["drained_ops_per_second"] or -1) > (old["drained_ops_per_second"] or -1):
                autos[row["value_bytes"]] = row
    check = []
    for width in sorted(autos):
        auto, cell = autos[width], cells.get(width, {})
        faster = None
        if "a" in cell and "b" in cell:
            who = _winner("throughput", cell["a"], cell["b"])[0]
            faster = names[who] if who else None
        flag = "unknown" if faster is None else "agree" if auto["scheme"] == faster else "disagree"
        check.append({"value_bytes": width, "auto_resolved_scheme": auto["scheme"], "measured_faster_scheme": faster,
                      "flag": flag, "auto_drained_ops_per_second": auto["drained_ops_per_second"],
                      "auto_candidate": auto["candidate"], "auto_blocked": auto["blocked"],
                      "auto_publication_blockers": auto["publication_blockers"]})
    complete = {w: c for w, c in cells.items() if "a" in c and "b" in c}
    return {"key_bytes": key_bytes, "requested_capacity": capacity, "api_mode": api_mode, "caller_batch_size": batch,
            "actual_capacity": sorted(actual) or None, "schemes": [names["a"], names["b"]],
            "widths": widths, "crossovers": {m: crossover(m, complete, names) for m in METRICS},
            "auto_check": {"note": AUTO_NOTE, "widths": check},
            "frozen_arm": [r for r in rows if r["arm"] == "frozen"]}


def build(summary, resolution=None, schemes=None, per_batch=False):
    trials, configurations = load_resolution(resolution)
    rows = [row_of(g, trials, configurations) for g in summary["groups"]]
    frontier = sorted({r["scheme"] for r in rows if r["arm"] == "frontier"})
    if schemes is None:
        require(len(frontier) == 2, "need exactly two frontier schemes, found %s: pass --schemes A,B" % frontier)
        schemes = frontier
    require(len(schemes) == 2 and schemes[0] != schemes[1], "--schemes takes two different schemes")
    names = {"a": schemes[0], "b": schemes[1]}
    for row in rows:
        row["compared"] = row["arm"] != "frontier" or row["scheme"] in schemes
    split = {}
    for row in rows:
        key = (row["key_bytes"], row["requested_capacity"], row["api_mode"],
               row["caller_batch_size"] if per_batch else None)
        split.setdefault(key, []).append(row)
    frontiers = [frontier_report(split[k], names, *k) for k in sorted(split, key=str)]
    wins = set()
    for report in frontiers:
        for width in report["widths"]:
            wins.update(v["trial_id"] for v in width.values() if isinstance(v, dict) and "trial_id" in v)
    for row in rows:
        row["frontier_winner"] = row["trial_id"] in wins
    return {"schemes": schemes, "per_batch": per_batch,
            "ignored_frontier_schemes": sorted(set(frontier) - set(schemes)),
            "allocated_basis_note": "allocated amplification = library_reserved_bytes (else library_modeled_bytes, "
                                    "named per row) / logical_bytes; RSS = trial_peak_rss_bytes / logical_bytes",
            "campaign": summary.get("campaign"), "frontiers": frontiers}, rows


CSV_COLUMNS = ["arm", "frontier_winner", "key_bytes", "requested_capacity", "actual_capacity", "api_mode",
               "caller_batch_size", "value_bytes", "scheme", "requested_scheme", "candidate",
               "drained_ops_per_second", "allocated_amplification", "allocated_basis", "rss_amplification",
               "logical_bytes", "allocated_bytes", "peak_rss_bytes", "blocked", "publication_blockers",
               "security", "configuration_key", "same_as", "library_threads", "worker_role_counts", "choices",
               "trial_id", "compared"]


def write(output, document, rows):
    os.makedirs(output, exist_ok=True)
    with open(os.path.join(output, "crossovers.json"), "w") as stream:
        json.dump({"crossovers_schema_version": 1, **document, "rows": rows}, stream, indent=1, sort_keys=True)
        stream.write("\n")
    with open(os.path.join(output, "widths.csv"), "w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=CSV_COLUMNS)
        writer.writeheader()
        for row in sorted(rows, key=lambda r: (r["key_bytes"], r["requested_capacity"], r["api_mode"],
                                               r["value_bytes"], r["arm"], r["scheme"], r["candidate"])):
            out = {k: row.get(k) for k in CSV_COLUMNS}
            out["publication_blockers"] = ";".join(row["publication_blockers"])
            out["worker_role_counts"] = json.dumps(row["worker_role_counts"], sort_keys=True)
            out["choices"] = json.dumps(row["choices"], sort_keys=True)
            writer.writerow(out)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--summary", required=True, help="a `reduce` summary.json")
    ap.add_argument("--resolution", help="the campaign's resolution.json (resolved scheme, key, workers, choices)")
    ap.add_argument("--schemes", help="the two schemes to compare, A,B (default: the two frontier schemes)")
    ap.add_argument("--per-batch", action="store_true", help="a separate frontier per caller batch size")
    ap.add_argument("--output", required=True, help="directory for crossovers.json and widths.csv")
    args = ap.parse_args(argv)
    try:
        with open(args.summary) as stream:
            summary = json.load(stream)
        resolution = None
        if args.resolution:
            with open(args.resolution) as stream:
                resolution = json.load(stream)
        document, rows = build(summary, resolution, args.schemes.split(",") if args.schemes else None,
                               args.per_batch)
    except ValidationError as error:
        sys.exit("crossover_export: " + str(error))
    write(args.output, document, rows)


if __name__ == "__main__":
    main()
