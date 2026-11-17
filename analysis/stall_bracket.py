#!/usr/bin/env python3
"""The stable/stalling bracket of the rebuild/access ratio, and the model's predictions.

Two modes, JSON on stdout (a text table on stderr with --table).  Nothing here builds or edits
anything; it only runs the benchmark binaries it is given.

  bracket  Drives `cpu_byteslice_level_arena_benchmark_throttled` (--rebuild-slowdown K) for one fixed
           configuration and one fixed offered rate A.  For each K it measures
             (i)  the independent rebuild rate R(K): the closed-loop run of the SAME binary and
                  configuration at that K (no --rate), its `completed_records_per_s`;
             (ii) the paced run at --rate-kops with the same K: delayed fraction (%), and the maximum
                  and p99 attributed stall (us).
           RATIO = R(K) / A, both in records (= accesses) per second, unitless.  A STALL is attributed
           backpressure only: `backpressure_delayed > 0` (the requester waited for a dense prefix slot);
           queue time that is not attributed (a late arrival, a slow request) is not a stall.
           BRACKET: `smallest_stable_ratio` is the smallest ratio with zero attributed stall,
           `largest_stalling_ratio` the largest ratio with one; the crossing lies between them when
           the points are monotone (every stalling ratio below every stable one), else the status is
           `non_monotone` and both edges are still reported.  Other statuses: `no_stall_anywhere`,
           `stall_everywhere`, `no_points`.  K is a list (--ks 1,2,4,8) or an automatic search
           (default): double K from 1 until a stall (or --k-max), then bisect K geometrically between
           the last stable and the first stalling K for --steps steps (stopping early at a K ratio
           under 1.05).  K = 1 passes no flag.  The inline control arm (`--owners 0`, unthrottled, same
           binary) is run once, paced and closed loop.  One trial per point; nothing is alternated.
           The configuration goes after `--`, with --owners >= 1, --top-helpers 0 and
           --rebuild-lanes 1 (helpers are not throttled), and --write-only for the rebuild rate to mean
           anything; --fit-rows and --reps 1 are added here.
  model    Pure analysis.  Prints the requested PREDICTIONS (B = 2/4/8: rebuild speed 1x/2.25x/4.5x,
           mean tables per access 1.5/0.92/0.59 x log2 N, worst 2/1/0.67 x log2 N), labelled
           "predictions, not results", and, from `cpu_byteslice_probe_plan_shape_benchmark` JSON lines
           (--probe FILE..., '-' is stdin), the measured mean/max tables per access, each divided by
           log2 N, beside the prediction for that B, plus the fixed list of deviation sources.

    stall_bracket.py bracket --benchmark BENCH_THROTTLED --rate-kops 2000 [--ks 1,2,4,8] -- \\
        --capacity 65536 --value 8 --owners 1 --top-helpers 0 --rebuild-lanes 1 --write-only \\
        --accesses 200000 --settle 20000
    stall_bracket.py model --probe shape.json

Limits: the slowdown spins owners only, so the achieved R(K) is read, never assumed from K; a single
paced trial is noisy near the crossing (the report keeps every point); a small host is a smoke check.
"""
import argparse
import json
import math
import subprocess
import sys

PREDICTIONS_LABEL = "predictions, not results"
# B: (rebuild speed x, mean tables / log2 N, worst tables / log2 N), the requested model.
PREDICTIONS = {2: (1.0, 1.5, 2.0), 4: (2.25, 0.92, 1.0), 8: (4.5, 0.59, 0.67)}
DEVIATIONS = ("finite levels / top digit", "half-fanout / prefix geometry", "dense scans",
              "residual tiers", "queryable carries", "EDF pieces")


def strip_flag(args, flag):
    """args without `flag` and its value."""
    out, skip = [], False
    for a in args:
        if skip:
            skip = False
        elif a == flag:
            skip = True
        else:
            out.append(a)
    return out


def run_row(benchmark, args):
    result = subprocess.run([benchmark, *args, "--fit-rows", "--reps", "1"], capture_output=True, text=True,
                            check=True)
    rows = [json.loads(line.split(" ", 1)[1]) for line in result.stdout.splitlines() if line.startswith("FIT_ROW ")]
    runs = [r for r in rows if r.get("fit_row") == "run"]
    if len(runs) != 1:
        raise SystemExit(f"expected one FIT_ROW run line, got {len(runs)}")
    return runs[0]


def slowdown_args(k):
    return [] if k == 1 else ["--rebuild-slowdown", f"{k:g}"]


def point_from_rows(k, closed, paced, rate_kops):
    """One bracket point from the closed-loop row (R) and the paced row (A, stall)."""
    rate = closed["completed_records_per_s"]
    offered = rate_kops * 1000.0
    requests = paced["backpressure_requests"]
    delayed = paced["backpressure_delayed"]
    if not paced.get("backpressure_measured", True):
        raise SystemExit("the paced row carries no backpressure reads")
    return {"k": k, "rebuild_rate_per_s": rate, "offered_per_s": offered, "ratio": rate / offered,
            "stall": delayed > 0, "delayed": delayed, "requests": requests,
            "delayed_pct": 100.0 * delayed / requests if requests else 0.0,
            "max_stall_us": paced["backpressure_max_ns"] / 1e3, "p99_stall_us": paced["backpressure_p99_ns"] / 1e3,
            "total_stall_us": paced["backpressure_total_ns"] / 1e3,
            "response_p99_us": paced["response_p99_ns"] / 1e3, "response_max_us": paced["response_max_ns"] / 1e3,
            "achieved_per_s": paced["completed_records_per_s"]}


def bracket_of(points):
    """The stable/stalling bracket of points (dicts with `ratio`, `stall`)."""
    stable = [p["ratio"] for p in points if not p["stall"]]
    stalling = [p["ratio"] for p in points if p["stall"]]
    out = {"smallest_stable_ratio": min(stable) if stable else None,
           "largest_stalling_ratio": max(stalling) if stalling else None}
    if not points:
        status = "no_points"
    elif not stalling:
        status = "no_stall_anywhere"
    elif not stable:
        status = "stall_everywhere"
    elif max(stalling) < min(stable):
        status = "bracketed"
    else:
        status = "non_monotone"
    out["status"] = status
    out["crossing_interval"] = [out["largest_stalling_ratio"], out["smallest_stable_ratio"]] \
        if status == "bracketed" else None
    return out


def search(measure, k_max=64.0, steps=4, min_k_ratio=1.05):
    """Doubling from K=1 until a stall, then geometric bisection on K; returns points in measurement order."""
    points = []

    def probe(k):
        p = measure(k)
        points.append(p)
        return p
    k = 1.0
    last_stable = None
    while True:
        if probe(k)["stall"]:
            first_stall = k
            break
        last_stable = k
        if k >= k_max:
            return points
        k = min(k * 2, k_max)
    if last_stable is None:
        return points
    lo, hi = last_stable, first_stall
    for _ in range(steps):
        if hi / lo < min_k_ratio:
            break
        mid = round(math.sqrt(lo * hi), 3)
        if mid <= lo or mid >= hi:
            break
        if probe(mid)["stall"]:
            hi = mid
        else:
            lo = mid
    return points


def table_text(points):
    lines = ["K       R(K)/s        ratio R/A  stall  delayed%   max_us     p99_us"]
    for p in sorted(points, key=lambda p: p["ratio"]):
        lines.append(f"{p['k']:<7g} {p['rebuild_rate_per_s']:<13.0f} {p['ratio']:<10.3f} "
                     f"{'STALL' if p['stall'] else 'ok':<6} {p['delayed_pct']:<9.4f} {p['max_stall_us']:<10.1f} "
                     f"{p['p99_stall_us']:.1f}")
    return "\n".join(lines)


def bracket_mode(options, config):
    base = strip_flag(strip_flag(config, "--rate"), "--rebuild-slowdown")
    if "--write-only" not in base:
        print("warning: no --write-only; R(K) is not the rebuild capacity", file=sys.stderr)

    def measure(k):
        extra = slowdown_args(k)
        closed = run_row(options.benchmark, [*base, *extra])
        paced = run_row(options.benchmark, [*base, *extra, "--rate", str(options.rate_kops), "--attribution", "1"])
        return point_from_rows(k, closed, paced, options.rate_kops)
    if options.ks:
        points = [measure(float(k)) for k in options.ks.split(",")]
    else:
        points = search(measure, options.k_max, options.steps)
    inline = ["--owners", "0", *strip_flag(strip_flag(strip_flag(base, "--owners"), "--top-helpers"),
                                           "--rebuild-lanes")]
    control_closed = run_row(options.benchmark, inline)
    control_paced = run_row(options.benchmark, [*inline, "--rate", str(options.rate_kops), "--attribution", "1"])
    control = point_from_rows(None, control_closed, control_paced, options.rate_kops)
    report = {"mode": "bracket", "benchmark": options.benchmark, "config": config, "offered_kops": options.rate_kops,
              "definitions": {"ratio": "R(K)/A: closed-loop write-only records/s at K over the offered accesses/s",
                              "stall": "backpressure_delayed > 0 (attributed prefix-slot wait), not queue time",
                              "bracket": "smallest ratio with no stall, largest ratio with a stall"},
              "points": sorted(points, key=lambda p: p["k"]), "bracket": bracket_of(points),
              "inline_control": control, "trials_per_point": 1}
    if options.table:
        print(table_text(points), file=sys.stderr)
        print(f"inline control: ratio {control['ratio']:.3f} stall={control['stall']} "
              f"delayed {control['delayed_pct']:.4f}%", file=sys.stderr)
        print(json.dumps(report["bracket"]), file=sys.stderr)
    return report


def read_probe_lines(paths):
    rows = []
    for path in paths:
        if path == "-":
            text = sys.stdin.read()
        else:
            with open(path) as handle:
                text = handle.read()
        for line in text.splitlines():
            line = line.strip()
            if line.startswith("{") and '"tables"' in line:
                rows.append(json.loads(line))
    return rows


def model_rows(probe_rows):
    out = []
    for r in probe_rows:
        b = r["B"]
        log2n = math.log2(r["actual_capacity"])
        mean, worst = r["tables"]["mean"], r["tables"]["max"]
        row = {"B": b, "capacity": r["actual_capacity"], "log2_N": log2n, "D": r.get("D"), "r0": r.get("r0"),
               "L": r.get("L"), "measured_mean_tables": mean, "measured_max_tables": worst,
               "measured_mean_over_log2N": mean / log2n, "measured_max_over_log2N": worst / log2n}
        if b in PREDICTIONS:
            _, pm, pw = PREDICTIONS[b]
            row.update({"predicted_mean_over_log2N": pm, "predicted_worst_over_log2N": pw,
                        "predicted_mean_tables": pm * log2n, "predicted_worst_tables": pw * log2n,
                        "mean_measured_minus_predicted_over_log2N": mean / log2n - pm,
                        "worst_measured_minus_predicted_over_log2N": worst / log2n - pw})
        out.append(row)
    return out


def model_mode(options):
    predictions = [{"B": b, "rebuild_speed_x": s, "mean_tables_over_log2N": m, "worst_tables_over_log2N": w}
                   for b, (s, m, w) in sorted(PREDICTIONS.items())]
    rows = model_rows(read_probe_lines(options.probe or []))
    report = {"mode": "model", "label": PREDICTIONS_LABEL, "predictions": predictions,
              "measured_vs_prediction": rows, "deviation_sources": list(DEVIATIONS)}
    if options.table:
        print(PREDICTIONS_LABEL, file=sys.stderr)
        print("B  speed  mean/log2N  worst/log2N", file=sys.stderr)
        for p in predictions:
            print(f"{p['B']}  {p['rebuild_speed_x']:<5} {p['mean_tables_over_log2N']:<11} "
                  f"{p['worst_tables_over_log2N']}", file=sys.stderr)
        for r in rows:
            print(f"measured B={r['B']} N=2^{r['log2_N']:.0f}: mean {r['measured_mean_tables']:.3f} "
                  f"({r['measured_mean_over_log2N']:.3f} x log2N), max {r['measured_max_tables']} "
                  f"({r['measured_max_over_log2N']:.3f} x log2N)", file=sys.stderr)
        print("deviation sources: " + "; ".join(DEVIATIONS), file=sys.stderr)
    return report


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="mode", required=True)
    b = sub.add_parser("bracket")
    b.add_argument("--benchmark", required=True, help="the _throttled arena benchmark")
    b.add_argument("--rate-kops", type=float, required=True, help="offered rate A, k accesses/s")
    b.add_argument("--ks", help="comma list of slowdowns; omitted = doubling then bisection")
    b.add_argument("--k-max", type=float, default=64.0)
    b.add_argument("--steps", type=int, default=4, help="bisection steps")
    b.add_argument("--table", action="store_true")
    b.add_argument("args", nargs=argparse.REMAINDER)
    m = sub.add_parser("model")
    m.add_argument("--probe", nargs="*", help="probe-plan-shape output files ('-' = stdin)")
    m.add_argument("--table", action="store_true")
    options = parser.parse_args(argv)
    if options.mode == "bracket":
        config = options.args[1:] if options.args[:1] == ["--"] else options.args
        report = bracket_mode(options, config)
    else:
        report = model_mode(options)
    json.dump(report, sys.stdout, indent=1)
    print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
