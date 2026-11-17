#!/usr/bin/env python3
"""The stash lanes a stash-tail row needs, from `run_stash_tail_long.py
export` output (fits.csv and tail.csv of one directory).  The read-path tree
sizes its stash registers with it: A registers hold 64 A - 1 lanes, and A is
the smallest with k* <= 64 A - 1 (src/oram/tree/DESIGN.md).

A row's requirement k* is the larger of
  * the fitted lane count at 2^-B plus two jackknife standard errors, and
  * the deepest fitted point carried to 2^-B at the shallower of the fit's
    slope and its deep half's: the guard against a tail that flattens.
Rows whose tail was too short to fit are listed with their maximum only.

Usage: stash_requirement.py EXPORT_DIR [--bits 96] [--series op-max]
"""

import argparse
import csv
import math
import os


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("export_dir")
    ap.add_argument("--bits", type=int, default=96, choices=(64, 80, 96))
    ap.add_argument("--series", default="op-max")
    a = ap.parse_args()

    with open(os.path.join(a.export_dir, "fits.csv")) as f:
        fits = [r for r in csv.DictReader(f)
                if r["phase"] == "steady" and r["series"] == a.series]
    points = {}
    rows = {}
    with open(os.path.join(a.export_dir, "tail.csv")) as f:
        for r in csv.DictReader(f):
            if r["phase"] != "steady" or r["series"] != a.series:
                continue
            points[(r["row"], int(r["k"]))] = float(r["neg_log2_p_ge_k"])
            rows.setdefault(r["row"], r)
            rows[r["row"]] = max(rows[r["row"]], r, key=lambda x: int(x["k"]))

    fitted = {}
    for r in fits:
        k_fit = float(r[f"lanes_at_2^-{a.bits}"])
        se = float(r[f"lanes_at_2^-{a.bits}_se"] or "nan")
        k1 = int(r["window_k1"])
        y1 = points[(r["row"], k1)]
        slope = min(float(r["slope_bits_per_lane"]), float(r["slope_deep_half"]))
        k_flat = k1 + (a.bits - y1) / slope
        k_se = k_fit + 2 * se
        fitted[r["row"]] = (r, k_fit, se, k_flat, max(k_se, k_flat))

    print(f"{'row':22s} {'log2N':>7s} {'fold':>4s} {'workload':10s} "
          f"{'seeds':>5s} {'max':>4s} {'slope':>6s} {'deep':>6s} "
          f"{'k@2^-' + str(a.bits):>9s} {'+2se':>6s} {'flat':>6s} {'k*':>6s}  A")
    for label, last in rows.items():
        head = (f"{label:22s} {last['log2_n']:>7s} {last['fold']:>4s} "
                f"{last['workload']:10s} {last['seeds']:>5s}")
        if label not in fitted:
            print(f"{head} {last['k']:>4s}   (tail too short to fit)")
            continue
        r, k_fit, se, k_flat, k_star = fitted[label]
        print(f"{head} {r['max']:>4s} {float(r['slope_bits_per_lane']):6.2f} "
              f"{float(r['slope_deep_half']):6.2f} {k_fit:9.1f} {k_fit + 2 * se:6.1f} "
              f"{k_flat:6.1f} {k_star:6.1f}  {math.ceil((k_star + 1) / 64)}")


if __name__ == "__main__":
    main()
