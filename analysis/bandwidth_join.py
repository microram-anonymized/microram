#!/usr/bin/env python3
"""Join rebuild rows with a streaming-bandwidth sweep.

Question answered: how much memory traffic does the level-arena rebuild
generate at each worker count, next to what a plain streaming read reaches on
the same number of cores?  The join is a table; it does not decide whether the
rebuild is memory- or compute-bound.

Inputs
  --rebuild FILE...   (a) the arena benchmark's stdout run with
        `--write-only --fit-rows --stage-times` (lines `FIT_ROW {json}`), or
      (b) the tuner's `fit-rebuild --rows` JSON-lines files (bare JSON objects).
      Either form may be mixed.  A "run" row is followed by its per-level
      rows; levels are attached to the run row that precedes them.  `-` is stdin.
      The benchmark's run rows carry "inline" (`owners` is owner_groups,
      which is 1 for the inline executor too).  For rows without that
      field, PREFIX THE FILE WITH `inline:` (e.g. inline:run0.txt) when it
      was run with `--owners 0`.  Inline runs count as 1 thread and
      are the speedup baseline.
  --bandwidth FILE... `cpu_mem_bandwidth_benchmark --sweep` stdout (table lines
      `threads | GB/s | per thread`; GB/s there is 1e9 bytes/s of streaming
      reads, one private buffer per thread), or JSON lines
      {"threads": N, "gbs": X}.  Several points at one thread count: the
      largest is the ceiling.

Join rule (printed as match_rule): threads = 1 (the caller) + owners +
top_helpers (inline: 1), from the rebuild row, matched to the bandwidth point with the same
thread count.  `owners` is the engine's owner-group count (0 = inline
executor, so 1 thread).  Lane threads and the harness thread are NOT counted
(rows do not record them separately); pin the benchmark so this holds.

Per joined row
  records_per_s       completed_records_per_s of the run row
  ns_per_access       1e9 / records_per_s
  speedup             records_per_s over the mean of the inline
                      rows with the same capacity/key/value/branching/mode
  ceiling_gbs         measured streaming-read GB/s at that thread count
  modeled_gbs         bytes_per_record * records_per_s / 1e9, MODELED
  fraction_of_ceiling modeled_gbs / ceiling_gbs
  bytes_per_record    64 * sum over levels of (touch_lines_per_access +
                      residual_lines_per_access + offer_lines_per_access):
                      the cost model's per-access line counts
                      (LevelRebuildFeatures in
                      src/oram/levelarena/cpu_byteslice_level_arena_rebuild_params.hpp,
                      printed by FitRows() in the arena benchmark), one 64 B
                      line per touch
  prepare_ms/finish_ms/fold_ms/job_ms
                      sums over levels of the rows' *_nanos fields (whole run);
                      ordered_ms/divisible_ms are carried if a row has them.

Limits (also printed with every run)
  * modeled_gbs comes from a count of line touches, not hardware counters.  A
    touch is 64 B once: reads and writes are not doubled, cache hits are not
    removed, non-temporal stores and write-allocate traffic are not modeled.
  * The ceiling is a streaming READ sweep of private buffers; the rebuild's
    mix of reads, writes and strides can have a lower or higher achievable
    rate, so a fraction near or above 1 does not mean saturation and a low one
    does not mean compute-bound.  This tool cannot show either.
  * Rows without a bandwidth point at their thread count keep null bandwidth
    fields and a reason.  Rows without level rows have no traffic.
"""

import argparse
import csv
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

LINE_BYTES = 64
NOTE = ("note: modeled traffic is a count of 64 B line touches times records/s, "
        "not a hardware measurement; the streaming-read ceiling alone cannot "
        "show whether the rebuild is memory- or compute-bound.")
MATCH_RULE = "threads = 1 + owners + top_helpers == bandwidth sweep threads"
SHAPE_KEYS = ("capacity", "key_bytes", "value_bytes", "branching",
              "write_only", "read_only", "batch")
LINE_FIELDS = ("touch_lines_per_access", "residual_lines_per_access",
               "offer_lines_per_access")
MS_FIELDS = (("prepare_ms", "prepare_wall_nanos"), ("finish_ms", "finish_wall_nanos"),
             ("fold_ms", "fold_nanos"), ("job_ms", "job_nanos"),
             ("ordered_ms", "ordered_nanos"), ("divisible_ms", "divisible_nanos"))
_TABLE = re.compile(r"^\s*(\d+)\s*\|\s*([0-9.]+)\s*\|")


def read_text(path):
    return sys.stdin.read() if path == "-" else Path(path).read_text()


def parse_rebuild(text, inline=False):
    """Run rows (dicts) each with a "levels" list, from either input form."""
    runs = []
    for line in text.splitlines():
        line = line.strip()
        if line.startswith("FIT_ROW "):
            line = line[len("FIT_ROW "):]
        elif not line.startswith("{"):
            continue
        row = json.loads(line)
        kind = row.get("fit_row")
        if kind == "run":
            runs.append(dict(row, levels=[], inline=inline or bool(row.get("inline"))))
        elif kind == "level" and runs:
            runs[-1]["levels"].append(row)
    return runs


def parse_bandwidth(text):
    """{threads: [GB/s, ...]} from sweep table lines or JSON lines."""
    points = defaultdict(list)
    for line in text.splitlines():
        match = _TABLE.match(line)
        if match:
            points[int(match.group(1))].append(float(match.group(2)))
        elif line.strip().startswith("{"):
            row = json.loads(line)
            points[int(row["threads"])].append(float(row["gbs"]))
    return points


def shape(run):
    return tuple(run.get(key) for key in SHAPE_KEYS)


def threads_of(run):
    if run.get("inline"):
        return 1
    return 1 + int(run["owners"]) + int(run.get("top_helpers", 0))


def bytes_per_record(run):
    if not run["levels"]:
        return None
    return LINE_BYTES * sum(level.get(f, 0.0) for level in run["levels"] for f in LINE_FIELDS)


def join(runs, bandwidth):
    inline = defaultdict(list)
    for run in runs:
        if run.get("inline"):
            inline[shape(run)].append(run["completed_records_per_s"])
    rows = []
    for run in runs:
        rate = run["completed_records_per_s"]
        threads = threads_of(run)
        base = inline.get(shape(run))
        per_record = bytes_per_record(run)
        row = {key: run.get(key) for key in SHAPE_KEYS}
        row.update(inline=bool(run.get("inline")), owners=run["owners"], top_helpers=run.get("top_helpers", 0),
                   lanes=run.get("lanes"), threads=threads, match_rule=MATCH_RULE,
                   records_per_s=rate, ns_per_access=1e9 / rate if rate > 0 else None,
                   speedup=rate / (sum(base) / len(base)) if base else None,
                   bytes_per_record=per_record,
                   modeled_gbs=per_record * rate / 1e9 if per_record is not None else None,
                   traffic_basis="modeled (64 B line touches x records/s; no hardware counters)")
        for name, field in MS_FIELDS:
            values = [level[field] for level in run["levels"] if field in level]
            row[name] = sum(values) / 1e6 if values else None
        ceiling = max(bandwidth[threads]) if bandwidth.get(threads) else None
        row["ceiling_gbs"] = ceiling
        row["fraction_of_ceiling"] = (row["modeled_gbs"] / ceiling
                                      if ceiling and row["modeled_gbs"] is not None else None)
        reasons = []
        if ceiling is None:
            reasons.append("no bandwidth point at %d threads" % threads)
        if per_record is None:
            reasons.append("no level rows, so no modeled traffic")
        if base is None:
            reasons.append("no inline row of this shape, so no speedup")
        row["null_reason"] = "; ".join(reasons) or None
        rows.append(row)
    return rows


COLUMNS = ["capacity", "value_bytes", "inline", "owners", "top_helpers", "threads",
           "records_per_s", "ns_per_access", "speedup", "ceiling_gbs",
           "modeled_gbs", "fraction_of_ceiling", "bytes_per_record",
           "prepare_ms", "finish_ms", "fold_ms", "job_ms",
           "ordered_ms", "divisible_ms", "null_reason"]


def fmt(value):
    if value is None:
        return "-"
    return "%.4g" % value if isinstance(value, float) else str(value)


def render(rows):
    shown = [c for c in COLUMNS if any(r.get(c) is not None for r in rows) or c == "null_reason"]
    table = [shown] + [[fmt(r.get(c)) for c in shown] for r in rows]
    widths = [max(len(line[i]) for line in table) for i in range(len(shown))]
    lines = ["  ".join(cell.ljust(w) for cell, w in zip(line, widths)).rstrip() for line in table]
    return "\n".join(lines + ["match rule: " + MATCH_RULE, NOTE])


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--rebuild", nargs="+", required=True, metavar="FILE")
    parser.add_argument("--bandwidth", nargs="+", required=True, metavar="FILE")
    parser.add_argument("--json", action="store_true", help="print JSON instead of a table")
    parser.add_argument("--csv", metavar="OUT", help="also write the rows as CSV")
    args = parser.parse_args(argv)
    runs = []
    for spec in args.rebuild:
        inline = spec.startswith("inline:")
        runs.extend(parse_rebuild(read_text(spec[len("inline:"):] if inline else spec), inline))
    bandwidth = defaultdict(list)
    for path in args.bandwidth:
        for threads, values in parse_bandwidth(read_text(path)).items():
            bandwidth[threads].extend(values)
    if not runs:
        sys.exit("no rebuild run rows found")
    rows = join(runs, bandwidth)
    if args.csv:
        fields = list(rows[0])
        with open(args.csv, "w", newline="") as stream:
            writer = csv.DictWriter(stream, fieldnames=fields)
            writer.writeheader()
            writer.writerows(rows)
    if args.json:
        print(json.dumps({"rows": rows, "note": NOTE, "match_rule": MATCH_RULE}, indent=2))
    else:
        print(render(rows))


if __name__ == "__main__":
    main()
