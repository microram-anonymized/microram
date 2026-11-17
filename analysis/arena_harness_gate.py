#!/usr/bin/env python3
"""Harness-overhead gate for the arena benchmark's paced path.

The campaign worker's gate records (oram_bench/validation.py) do not cover
`cpu_byteslice_level_arena_benchmark --rate`, whose per-request instrumentation
is the backpressure attribution reads (`--attribution`). This
runs that benchmark in pairs: `--attribution 1` (instrumented) against
`--attribution 0` (control), the arm order alternating per pair (a fixed order
fabricates a few percent), and gates the median per-pair ratio of the response
p50/p99/p99.9 like `validation.py`: it fails only when the instrumented arm is more than 5% slower than the
control (a faster instrumented arm passes); the maximum is reported, not gated.
`--null` runs identical arms (both instrumented) to show the instrument's own
spread first. Pass the benchmark's shape after `--`, with `--rate`; this script
adds `--fit-rows --reps 1 --attribution`.

    arena_harness_gate.py --benchmark BENCH --pairs 5 [--null] -- \\
        --capacity 1048576 --value 8 --write-only --rate 2000 --settle 100000
"""
import argparse
import json
import statistics
import subprocess
import sys

GATE_PPM = 50_000
QUANTILES = ("p50", "p99", "p999")


def run(benchmark, args, attribution):
    result = subprocess.run([benchmark, *args, "--fit-rows", "--reps", "1", "--attribution", str(attribution)],
                            capture_output=True, text=True, check=True)
    rows = [json.loads(line.split(" ", 1)[1]) for line in result.stdout.splitlines()
            if line.startswith("FIT_ROW ")]
    [row] = [r for r in rows if r.get("fit_row") == "run"]
    if not row["offered_kops"]:
        raise SystemExit("the gate is for paced rows: pass --rate")
    if row["backpressure_measured"] != bool(attribution):
        raise SystemExit("the benchmark ignored --attribution")
    return row


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--benchmark", required=True)
    parser.add_argument("--pairs", type=int, default=5)
    parser.add_argument("--null", action="store_true", help="identical instrumented arms (the instrument's spread)")
    parser.add_argument("args", nargs=argparse.REMAINDER)
    options = parser.parse_args(argv)
    args = options.args[1:] if options.args[:1] == ["--"] else options.args
    control_arm = 1 if options.null else 0
    pairs = []
    for index in range(options.pairs):
        order = (1, control_arm) if index % 2 == 0 else (control_arm, 1)
        rows = [run(options.benchmark, args, arm) for arm in order]
        instrumented, control = (rows[0], rows[1]) if index % 2 == 0 else (rows[1], rows[0])
        pairs.append({"order": "instrumented_first" if index % 2 == 0 else "control_first",
                      **{q: instrumented[f"response_{q}_ns"] / control[f"response_{q}_ns"] for q in QUANTILES},
                      "max_ns": [control["response_max_ns"], instrumented["response_max_ns"]],
                      "samples": min(control["response_count"], instrumented["response_count"])})
    median = {q: statistics.median(p[q] for p in pairs) for q in QUANTILES}
    failures = [f"{q}_over_gate" for q in QUANTILES if (median[q] - 1) * 1e6 > GATE_PPM]
    report = {"comparison": "identical_arms" if options.null else "attribution_off_control",
              "benchmark_args": args, "gate_ppm": GATE_PPM, "pairs": pairs,
              "median_ratio": median, "status": "failed" if failures else "passed", "failures": failures,
              "note": "median per-pair instrumented/control ratio; the maximum is reported, not gated"}
    json.dump(report, sys.stdout, indent=1)
    print()
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
