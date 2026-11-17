#!/usr/bin/env python3
"""Deamortization microbenchmark: merge-time split and the pre-routing A/B.

Two modes; tables on stdout, JSON with --json.  Nothing here runs a benchmark.

  shares FILE...   (A) Where each non-top merge's work falls.  Reads the arena
        benchmark's stdout run with `--merge-rows --stage-times` (MERGE_ROW
        lines; one run per file, `--reps 1`).  Only merges published inside
        the measured window count, and adoptions (a carry taken in place, no
        work) are counted apart.  Per (run, level, k), k = the partial's size
        in carry units = digit - 1:
          share       post / (prepare + post), median and p99 over merges.
                      prepare = piece time routing the older partial;
                      post = install + finish piece time + the publication
                      transaction, i.e. the carry-dependent work.  Piece time
                      is summed over every thread that ran a piece.
          model       1 / (k + 1): the model's share after arrival.
          touch       the same share in estimated bucket touches
                      (PieceTouches), no timing noise; publication has none.
          ahead       fraction of merges whose preparation had finished when
                      the merge began (prepared_ahead).
          prep@arr    fraction (k >= 1) whose preparation had NOT finished
                      when the carry became available (prepare_end >
                      carry_ready, or it had not started).
          delay       publish - carry_ready, in carry intervals of that
                      level, median / p99 / max.  The interval is MEASURED:
                      the mean spacing of carry_ready stamps over the
                      window's carries (nominal = carry positions / rate is
                      printed per level beside it).
          post split  sweep / residual / route / publish shares of post time
                      (sums over the group's merges).
        One aggregate row per level weighted by the model's cost (k + 1):
          sum (k+1) share / sum (k+1)  beside  model = n / sum (k+1),
        and the plain work fraction sum post / sum (prepare + post).
        --check-b 8 prints, for that B, every (level, k) whose median share
        exceeds 1/(k+1) and every level with prep@arr above --regular (0.1).

  compare --manifest FILE   (B) Pre-routing on vs --no-preroute.  The
        manifest is JSON lines, one per benchmark run, written by whatever
        script drove the arms:
          {"kind": "sat"|"inline"|"A"|"fixed", "arm": "on"|"off"|"null",
           "pair": N, "file": PATH, ...}
        Each file is a benchmark stdout (FIT_ROW run row, and MERGE_ROW lines
        when run with --merge-rows).  Rows are grouped by (kind, B, capacity,
        executor, mix, offered rate); within a group each arm's pair-matched
        throughput ratio to "on" is printed with the number of pairs it is
        above 1 in.  Columns:
          rate        completed_records_per_s
          bp          backpressure: requester waits and park time (closed
                      loop), delayed requests (paced)
          idle        owner idle share: sum over owner groups of idle time /
                      (window seconds x groups)
          tables      lookup tables mean / max, buckets mean (--probe-counts)
          c2p         carry-to-publication per level, mean / max, in carry
                      intervals (MERGE_ROW stamps)
          resp        response p99 / max (paced runs)

    preroute_rows.py shares run-*.txt --check-b 8
    preroute_rows.py compare --manifest OUT/manifest.jsonl

Limits: piece time is CPU time across threads, not wall time; with helpers or
lanes the share is of work, not of elapsed time.  A ring keeps the last N
records per level (--merge-rows=N), so a large level-1 count covers only the
window's end.  One trial per arm per pair: read a ratio inside the null arm's
spread as nothing.
"""
import argparse
import json
import math
import statistics
import sys
from collections import defaultdict


def read_lines(path):
    with open(path) as handle:
        return handle.read().splitlines()


def tagged(lines, tag):
    prefix = tag + " "
    return [json.loads(line[len(prefix):]) for line in lines if line.startswith(prefix)]


def quantile(values, q):
    if not values:
        return None
    ordered = sorted(values)
    position = q * (len(ordered) - 1)
    lo = math.floor(position)
    hi = math.ceil(position)
    return ordered[lo] + (ordered[hi] - ordered[lo]) * (position - lo)


def ratio(num, den):
    return num / den if den else None


def run_key(window):
    executor = "inline" if window["inline"] else f"owners{window['owners']}"
    mix = "write-only" if window["write_only"] else "read-only" if window["read_only"] else "mixed"
    return (window["branching"], window["capacity"], executor, mix,
            "on" if window["preroute"] else "off", window.get("offered_kops", 0))


def carry_intervals(merges, window):
    """Per level: measured mean spacing of carry_ready stamps (ns) and the nominal one."""
    rate = window["accesses"] / window["seconds"] if window["seconds"] else 0.0
    out = {}
    by_level = defaultdict(list)
    for m in merges:
        if m["in_window"] and m["carry_ready_ns"]:
            by_level[m["level"]].append((m["ordinal"], m["carry_ready_ns"]))
    for level in range(1, window["levels"] + 1):
        nominal = window["carry_positions"][level - 1] / rate * 1e9 if rate else None
        points = sorted(by_level.get(level, []))
        measured = None
        if len(points) >= 2 and points[-1][0] > points[0][0]:
            measured = (points[-1][1] - points[0][1]) / (points[-1][0] - points[0][0])
        out[level] = {"measured_ns": measured, "nominal_ns": nominal}
    return out


def load_runs(paths):
    runs = []
    for path in paths:
        lines = read_lines(path)
        rows = tagged(lines, "MERGE_ROW")
        windows = [r for r in rows if r["merge_row"] == "window"]
        if len(windows) != 1:
            raise SystemExit(f"{path}: expected one MERGE_ROW window line (run with --merge-rows --reps 1), "
                             f"got {len(windows)}")
        window = windows[0]
        merges = [r for r in rows if r["merge_row"] == "merge"]
        owners = [r for r in rows if r["merge_row"] == "owner"]
        fit = [r for r in tagged(lines, "FIT_ROW") if r.get("fit_row") == "run"]
        runs.append({"path": path, "window": window, "merges": merges, "owners": owners,
                     "run": fit[0] if fit else None,
                     "intervals": carry_intervals(merges, window)})
    return runs


# ---------------------------------------------------------------------------
# (A) shares
# ---------------------------------------------------------------------------

def merge_facts(m, interval):
    prep = m["prepare_active_ns"]
    post = m["post_arrival_active_ns"]
    prep_t = m["prepare_touches"]
    post_t = m["post_touches"]
    unready = m["prepare_end_ns"] == 0 or m["prepare_end_ns"] > m["carry_ready_ns"]
    return {
        "share": ratio(post, prep + post),
        "touch_share": ratio(post_t, prep_t + post_t),
        "prep": prep, "post": post,
        "sweep": m["post_sweep_ns"], "residual": m["post_residual_ns"],
        "route": m["post_route_ns"] + m["post_fold_ns"], "publish": m["publish_active_ns"],
        "ahead": m["prepared_ahead"],
        "prep_at_arrival": m["k"] >= 1 and unready,
        "delay": ratio(m["publish_ns"] - m["carry_ready_ns"], interval) if m["carry_ready_ns"] else None,
    }


def shares(runs):
    groups = defaultdict(list)       # (run key, level, k) -> facts
    adoptions = defaultdict(int)     # (run key, level) -> count
    intervals = defaultdict(list)    # (run key, level) -> (measured, nominal)
    untimed = set()
    for run in runs:
        key = run_key(run["window"])
        if not run["window"].get("stage_times", True):
            untimed.add(key)
        for level, iv in run["intervals"].items():
            intervals[(key, level)].append(iv)
        for m in run["merges"]:
            if m["top"] or not m["in_window"]:
                continue
            if m["adoption"]:
                adoptions[(key, m["level"])] += 1
                continue
            iv = run["intervals"][m["level"]]
            interval = iv["measured_ns"] or iv["nominal_ns"]
            groups[(key, m["level"], m["k"])].append(merge_facts(m, interval))
    rows = []
    for (key, level, k), facts in sorted(groups.items()):
        share = [f["share"] for f in facts if f["share"] is not None]
        touch = [f["touch_share"] for f in facts if f["touch_share"] is not None]
        delay = [f["delay"] for f in facts if f["delay"] is not None]
        post = sum(f["post"] for f in facts)
        rows.append({
            "B": key[0], "capacity": key[1], "executor": key[2], "mix": key[3], "preroute": key[4],
            "level": level, "k": k, "n": len(facts),
            "share_median": quantile(share, 0.5), "share_p99": quantile(share, 0.99),
            "model": 1.0 / (k + 1),
            "touch_share_median": quantile(touch, 0.5),
            "ahead": sum(f["ahead"] for f in facts) / len(facts),
            "prep_at_arrival": (sum(f["prep_at_arrival"] for f in facts) / len(facts)) if k >= 1 else None,
            "delay_median": quantile(delay, 0.5), "delay_p99": quantile(delay, 0.99),
            "delay_max": max(delay) if delay else None,
            "post_split": {name: ratio(sum(f[name] for f in facts), post)
                           for name in ("sweep", "residual", "route", "publish")},
            "timed": key not in untimed,
        })
    levels = []
    by_level = defaultdict(list)
    for (key, level, k), facts in groups.items():
        by_level[(key, level)].extend((k, f) for f in facts)
    for (key, level), items in sorted(by_level.items()):
        weights = [(k + 1, f) for k, f in items if f["share"] is not None]
        wsum = sum(w for w, _ in weights)
        prep = sum(f["prep"] for _, f in items)
        post = sum(f["post"] for _, f in items)
        ivs = intervals[(key, level)]
        measured = [iv["measured_ns"] for iv in ivs if iv["measured_ns"]]
        nominal = [iv["nominal_ns"] for iv in ivs if iv["nominal_ns"]]
        levels.append({
            "B": key[0], "capacity": key[1], "executor": key[2], "mix": key[3], "preroute": key[4],
            "level": level, "merges": len(items), "adoptions": adoptions.get((key, level), 0),
            "weighted_share": ratio(sum(w * f["share"] for w, f in weights), wsum),
            "weighted_model": ratio(len(weights), wsum),
            "work_fraction_after_arrival": ratio(post, prep + post),
            "interval_measured_ms": statistics.mean(measured) / 1e6 if measured else None,
            "interval_nominal_ms": statistics.mean(nominal) / 1e6 if nominal else None,
        })
    return {"merges": rows, "levels": levels}


def fmt(value, spec=".3f"):
    if value is None:
        return "-"
    if isinstance(value, bool):
        return "yes" if value else "no"
    return format(value, spec)


def render_shares(report, check_b, regular):
    out = []
    current = None
    for r in report["merges"]:
        head = (r["B"], r["capacity"], r["executor"], r["mix"], r["preroute"])
        if head != current:
            current = head
            out.append(f"\nB={r['B']} N=2^{int(math.log2(r['capacity']))} {r['executor']} {r['mix']} "
                       f"preroute={r['preroute']}" + ("" if r["timed"] else "  (NO --stage-times: work is zero)"))
            out.append("  lvl  k     n  share med   p99  model  touch  ahead prep@arr  delay med   p99   max"
                       "   sweep resid route  publ")
        split = r["post_split"]
        out.append(f"  {r['level']:>3} {r['k']:>2} {r['n']:>5}  {fmt(r['share_median']):>9} {fmt(r['share_p99']):>5} "
                   f"{fmt(r['model']):>6} {fmt(r['touch_share_median']):>6} {fmt(r['ahead'], '.2f'):>6} "
                   f"{fmt(r['prep_at_arrival'], '.2f'):>8} {fmt(r['delay_median'], '.2f'):>10} "
                   f"{fmt(r['delay_p99'], '.2f'):>5} {fmt(r['delay_max'], '.2f'):>5}   "
                   f"{fmt(split['sweep'], '.2f'):>5} {fmt(split['residual'], '.2f'):>5} "
                   f"{fmt(split['route'], '.2f'):>5} {fmt(split['publish'], '.2f'):>5}")
    out.append("\nper level, weighted by the model's cost (k + 1)")
    out.append("  B  N     executor   mix         pre lvl merges adopt  w.share w.model  work-after  interval ms meas/nominal")
    for r in report["levels"]:
        out.append(f"  {r['B']}  2^{int(math.log2(r['capacity'])):<3} {r['executor']:<10} {r['mix']:<11} "
                   f"{r['preroute']:<3} {r['level']:>3} {r['merges']:>6} {r['adoptions']:>5}  "
                   f"{fmt(r['weighted_share']):>7} {fmt(r['weighted_model']):>7}  {fmt(r['work_fraction_after_arrival']):>10}  "
                   f"{fmt(r['interval_measured_ms'], '.4g')}/{fmt(r['interval_nominal_ms'], '.4g')}")
    if check_b is not None:
        out.append(f"\ncheck at B={check_b}: median share after arrival <= 1/(k+1)?")
        bad = [r for r in report["merges"] if r["B"] == check_b and r["share_median"] is not None
               and r["share_median"] > r["model"]]
        for r in bad:
            out.append(f"  EXCEEDS  N=2^{int(math.log2(r['capacity']))} {r['executor']} {r['mix']} pre={r['preroute']} "
                       f"level {r['level']} k={r['k']}: {r['share_median']:.3f} > {r['model']:.3f} "
                       f"(touch share {fmt(r['touch_share_median'])})")
        if not bad:
            out.append("  holds for every (level, k)")
        late = [r for r in report["merges"] if r["B"] == check_b and r["prep_at_arrival"] is not None
                and r["prep_at_arrival"] > regular]
        out.append(f"preparation still running at the carry's arrival in more than {regular:.0%} of merges:")
        for r in late:
            out.append(f"  N=2^{int(math.log2(r['capacity']))} {r['executor']} {r['mix']} pre={r['preroute']} "
                       f"level {r['level']} k={r['k']}: {r['prep_at_arrival']:.0%} of {r['n']}")
        if not late:
            out.append("  none")
    return "\n".join(out)


# ---------------------------------------------------------------------------
# (B) compare
# ---------------------------------------------------------------------------

def carry_to_publication(run):
    """Per non-top level, mean and max (publish - carry_ready) in measured carry intervals."""
    out = {}
    by_level = defaultdict(list)
    for m in run["merges"]:
        if not m["in_window"] or m["adoption"] or not m["carry_ready_ns"]:
            continue
        iv = run["intervals"][m["level"]]
        interval = iv["measured_ns"] or iv["nominal_ns"]
        if interval:
            by_level[m["level"]].append((m["publish_ns"] - m["carry_ready_ns"]) / interval)
    for level, values in sorted(by_level.items()):
        out[level] = {"mean": statistics.mean(values), "max": max(values), "n": len(values)}
    return out


def run_summary(path):
    lines = read_lines(path)
    fit = [r for r in tagged(lines, "FIT_ROW") if r.get("fit_row") == "run"]
    if len(fit) != 1:
        raise SystemExit(f"{path}: expected one FIT_ROW run line (--fit-rows --reps 1), got {len(fit)}")
    run = fit[0]
    out = {
        "rate": run["completed_records_per_s"],
        "requester_waits": run["requester_waits"],
        "requester_park_ms": run["requester_park_nanos"] / 1e6,
        "bp_delayed": run["backpressure_delayed"] if run["backpressure_measured"] else None,
        "bp_max_us": run["backpressure_max_ns"] / 1e3 if run["backpressure_measured"] else None,
        "resp_p99_us": run["response_p99_ns"] / 1e3 if run["response_count"] else None,
        "resp_max_us": run["response_max_ns"] / 1e3 if run["response_count"] else None,
        "tables_mean": run.get("lookup_tables_mean") if run.get("lookups_counted") else None,
        "tables_max": run.get("lookup_tables_max") if run.get("lookups_counted") else None,
        "buckets_mean": run.get("lookup_buckets_mean") if run.get("lookups_counted") else None,
        "owner_idle_share": None, "c2p": {},
    }
    groups = run["owners"] if not run["inline"] else 0
    if groups and run["seconds"]:
        out["owner_idle_share"] = run.get("owner_idle_nanos", 0) / (run["seconds"] * 1e9 * groups)
    merge_rows = tagged(lines, "MERGE_ROW")
    windows = [r for r in merge_rows if r["merge_row"] == "window"]
    if windows:
        parsed = {"merges": [r for r in merge_rows if r["merge_row"] == "merge" and not r["top"]],
                  "intervals": carry_intervals([r for r in merge_rows if r["merge_row"] == "merge"], windows[0])}
        out["c2p"] = carry_to_publication(parsed)
        out["owner_idle"] = {r["group"]: r["idle_share"] for r in merge_rows if r["merge_row"] == "owner"}
    key = (run["branching"], run["capacity"], "inline" if run["inline"] else f"owners{run['owners']}",
           "write-only" if run["write_only"] else "read-only" if run["read_only"] else "mixed",
           run.get("offered_kops", 0))
    return key, out


def compare(manifest):
    entries = [json.loads(line) for line in read_lines(manifest) if line.strip()]
    groups = defaultdict(lambda: defaultdict(dict))   # (kind, key) -> arm -> pair -> summary
    for e in entries:
        key, summary = run_summary(e["file"])
        groups[(e["kind"], key)][e["arm"]][e.get("pair", 0)] = summary
    report = []
    for (kind, key), arms in sorted(groups.items(), key=lambda kv: (kv[0][0], str(kv[0][1]))):
        row = {"kind": kind, "B": key[0], "capacity": key[1], "executor": key[2], "mix": key[3],
               "offered_kops": key[4], "arms": {}}
        base = arms.get("on", {})
        for arm, pairs in sorted(arms.items()):
            arm_out = {"pairs": pairs}
            ratios = [pairs[p]["rate"] / base[p]["rate"] for p in pairs
                      if p in base and pairs[p].get("rate") and base[p].get("rate")]
            if arm != "on" and ratios:
                arm_out["ratio_to_on_median"] = statistics.median(ratios)
                arm_out["pairs_above_1"] = sum(r > 1 for r in ratios)
                arm_out["pairs"] = pairs
                arm_out["n_pairs"] = len(ratios)
            row["arms"][arm] = arm_out
        report.append(row)
    return report


def render_compare(report):
    out = []
    for row in report:
        out.append(f"\n{row['kind']}  B={row['B']} N=2^{int(math.log2(row['capacity']))} {row['executor']} "
                   f"{row['mix']} offered={row['offered_kops']} kops")
        for arm, a in row["arms"].items():
            for pair, s in sorted(a["pairs"].items()):
                c2p = " ".join(f"L{lvl}:{v['mean']:.2f}/{v['max']:.2f}" for lvl, v in s["c2p"].items())
                out.append(f"  {arm:<4} pair {pair}: rate {s['rate'] / 1e3:9.1f} k/s  bp waits {s['requester_waits']} "
                           f"park {s['requester_park_ms']:.1f} ms delayed {fmt(s['bp_delayed'], 'd') if s['bp_delayed'] is not None else '-'}"
                           f"  idle {fmt(s['owner_idle_share'], '.2f')}  tables {fmt(s['tables_mean'], '.2f')}/"
                           f"{fmt(s['tables_max'], 'd') if s['tables_max'] is not None else '-'} buckets {fmt(s['buckets_mean'], '.1f')}"
                           f"  resp p99/max {fmt(s['resp_p99_us'], '.1f')}/{fmt(s['resp_max_us'], '.0f')} us")
                if c2p:
                    out.append(f"         carry->publication (intervals, mean/max): {c2p}")
            if "ratio_to_on_median" in a:
                out.append(f"  {arm} / on: median {a['ratio_to_on_median']:.3f} over {a['n_pairs']} pair(s), "
                           f"above 1 in {a['pairs_above_1']}")
    return "\n".join(out)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="mode", required=True)
    s = sub.add_parser("shares")
    s.add_argument("files", nargs="+")
    s.add_argument("--check-b", type=int, help="list (level, k) exceeding the model at this B")
    s.add_argument("--regular", type=float, default=0.1,
                   help="prep@arr fraction above which preparation is 'regularly' late (default 0.1)")
    s.add_argument("--json", action="store_true")
    c = sub.add_parser("compare")
    c.add_argument("--manifest", required=True)
    c.add_argument("--json", action="store_true")
    options = parser.parse_args(argv)
    if options.mode == "shares":
        report = shares(load_runs(options.files))
        print(json.dumps(report, indent=1) if options.json else render_shares(report, options.check_b, options.regular))
    else:
        report = compare(options.manifest)
        print(json.dumps(report, indent=1) if options.json else render_compare(report))
    return 0


if __name__ == "__main__":
    sys.exit(main())
