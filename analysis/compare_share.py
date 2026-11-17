#!/usr/bin/env python3
"""The comparisons' share of a merge, without timing any single call.

Three inputs, all from the same configuration:

  --counted FILE  cpu_byteslice_level_arena_benchmark_compare_counted output:
                  COMPARE_COUNT lines, the window's merge comparisons by kind
                  (one 64 x 64 nest of one key field: pair_q8 / pair_d4 across
                  two buckets, self_q8 / self_d4 within one).  The merge is
                  oblivious, so the counts are a public function of the
                  schedule: the same in any build and at any thread count.
  --merge FILE    the PLAIN cpu_byteslice_level_arena_benchmark output of the
                  same configuration with --fit-rows: per-level job_nanos,
                  summed into the merge time (the counted build's own times
                  carry its counters).
  --kernel FILE   cpu_byteslice_dedup_kernel_benchmark output: the median ns of
                  each kind over a long loop (pairs_per_rep calls per timing).

comparison ms = sum over kinds of count x loop ns per call; pair kinds are
priced at the native (VP2INTERSECT) and the xor-min rows (the fallback on
CPUs without VP2INTERSECT), self kinds
at the build's own `self` rows.  Reported: comparison ms (native, fallback),
merge ms, fraction %, comparisons per access, and the comparison-time
native/fallback ratio.

LIMITS, printed with the result: a loop row is the whole one-field kernel
(key loads, transposes, nest, zero-key repair) on L1-resident buckets, so it
leaves out cache misses on the operands inside a merge and charges each nest
its own loads where a merge may share them; the whole-merge native/fallback
ratio needs merge times from both builds, not this ratio.

    compare_share.py --counted C.txt --merge M.txt --kernel K.txt [--json]
"""
import argparse
import json
import re
import statistics
import sys

KINDS = ("pair_q8", "pair_d4", "self_q8", "self_d4")
LIMITS = ("loop rows are L1-resident whole one-field kernels: operand cache misses inside the merge are "
          "not included and loads a merge shares between nests are charged per nest; comparison-only "
          "native/fallback ratio, not the whole merge's")


def read_counted(path):
    with open(path) as stream:
        return [json.loads(line.split(" ", 1)[1]) for line in stream if line.startswith("COMPARE_COUNT ")]


def read_merge(path):
    """One merge record per FIT_ROW run row: the job_nanos of the level rows after it."""
    runs = []
    with open(path) as stream:
        for line in stream:
            if not line.startswith("FIT_ROW "):
                continue
            row = json.loads(line.split(" ", 1)[1])
            if row.get("fit_row") == "run":
                runs.append({"run": row, "job_nanos": 0.0, "levels": 0})
            elif row.get("fit_row") == "level" and runs:
                runs[-1]["job_nanos"] += float(row.get("job_nanos") or 0)
                runs[-1]["levels"] += 1
    return runs


def read_kernel(path):
    """Median ns per call by (key bytes, kernel name)."""
    rows = {}
    pattern = re.compile(r"^\s+(\d+) B\s+(\S+)\s+([\d.]+)\s+([\d.]+)\s+([\d.]+)\s*$")
    with open(path) as stream:
        for line in stream:
            match = pattern.match(line)
            if match:
                rows[(int(match[1]), match[2])] = float(match[4])
    return rows


def share(counted, merge, kernel):
    def price(arm):
        pair = arm
        costs = {"pair_q8": kernel.get((8, pair)), "pair_d4": kernel.get((4, pair)),
                 "self_q8": kernel.get((8, "self")), "self_d4": kernel.get((4, "self"))}
        missing = [k for k in KINDS if counted[k] and costs[k] is None]
        if missing:
            return None, f"no {arm} loop row for {', '.join(missing)}"
        return sum(counted[k] * (costs[k] or 0) for k in KINDS) / 1e6, None
    native_ms, native_why = price("native")
    fallback_ms, fallback_why = price("xor-min")
    merge_ms = merge["job_nanos"] / 1e6 if merge else None
    built = "native" if counted.get("vp2intersect") else "xor-min"
    own_ms = native_ms if built == "native" else fallback_ms
    comparisons = sum(counted[k] for k in KINDS)
    return {"capacity": counted["capacity"], "key_bytes": counted["key_bytes"],
            "value_bytes": counted["value_bytes"], "accesses": counted["accesses"],
            **{k: counted[k] for k in KINDS},
            "comparisons_per_access": comparisons / counted["accesses"] if counted["accesses"] else None,
            "comparison_ms_native": native_ms, "comparison_ms_fallback": fallback_ms,
            "unpriced": [why for why in (native_why, fallback_why) if why],
            "merge_ms": merge_ms, "merge_levels": merge["levels"] if merge else None,
            "counted_build_intersect": built,
            "fraction_percent": 100 * own_ms / merge_ms if own_ms is not None and merge_ms else None,
            "fallback_over_native_comparison": (fallback_ms / native_ms
                                                if native_ms and fallback_ms is not None else None)}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--counted", required=True)
    parser.add_argument("--merge", required=True)
    parser.add_argument("--kernel", required=True)
    parser.add_argument("--json", action="store_true")
    options = parser.parse_args(argv)
    counted, merges, kernel = read_counted(options.counted), read_merge(options.merge), read_kernel(options.kernel)
    if not counted:
        raise SystemExit("no COMPARE_COUNT line: run the _compare_counted build")
    if not kernel:
        raise SystemExit("no kernel rows: pass cpu_byteslice_dedup_kernel_benchmark output")
    # Repetitions pair up in order; the counts are equal in every repetition.
    rows = []
    for i, c in enumerate(counted):
        merge = merges[i] if i < len(merges) else None
        if merge and (merge["run"]["capacity"], merge["run"]["key_bytes"], merge["run"]["value_bytes"]) != (
                c["capacity"], c["key_bytes"], c["value_bytes"]):
            raise SystemExit("counted and plain runs differ in capacity or widths")
        rows.append(share(c, merge, kernel))
    merge_values = [r["merge_ms"] for r in rows if r["merge_ms"] is not None]
    report = {"rows": rows, "limits": LIMITS,
              "merge_ms_median": statistics.median(merge_values) if merge_values else None}
    if options.json:
        json.dump(report, sys.stdout, indent=1)
        print()
        return 0
    for r in rows:
        fraction = "-" if r["fraction_percent"] is None else f"{r['fraction_percent']:.1f}%"
        print(f"N={r['capacity']} K{r['key_bytes']}/V{r['value_bytes']}: {sum(r[k] for k in KINDS)} comparisons "
              f"({r['comparisons_per_access']:.3f}/access; " +
              ", ".join(f"{k} {r[k]}" for k in KINDS if r[k]) + ")")
        native = "-" if r["comparison_ms_native"] is None else f"{r['comparison_ms_native']:.3f}"
        fallback = "-" if r["comparison_ms_fallback"] is None else f"{r['comparison_ms_fallback']:.3f}"
        merge = "-" if r["merge_ms"] is None else f"{r['merge_ms']:.3f}"
        print(f"  comparison ms native {native}, fallback {fallback}; merge ms {merge} "
              f"({r['counted_build_intersect']} build): {fraction}")
        for why in r["unpriced"]:
            print(f"  unpriced: {why}")
    print("limits: " + LIMITS)
    return 0


if __name__ == "__main__":
    sys.exit(main())
