"""Branch census of H2O2RAM's lookup in both builds (README.md, "H2O2RAM's lookups branch on the secret").

    check_h2o2ram_census.py CENSUS_PATCHED CENSUS_SHIPPED WORKER_PATCHED

For each shape's block (8, 48 and 1024-byte values), the census traces one
lookup per target block, with targets in the buffer, lower levels and the top.
The patched build must give one instruction trace for every target: no branch
and no load depends on where, or whether, the block matched. The shipped build
must not, and the addresses whose counts differ are mapped to source lines, so
that the finding (the shipped lookups branch on the secret) reproduces from the
fetched source.

The planner cache beside the executables must cover each block size at 2^16
(the worker's --prepare-planner 1 writes it; this script prepares what is missing).
"""
import collections
import json
from pathlib import Path
import subprocess
import sys

SHAPES = ((4, 8, "dense"), (8, 48, "permuted"), (32, 1024, "permuted"))
ENVIRONMENT = {"OMP_NUM_THREADS": "7", "PATH": "/usr/bin:/bin"}


def prepare(worker, key, value, layout):
    args = [worker, "--scheme", "h2o2ram", "--capacity", "65536", "--key-bytes", str(key),
            "--value-bytes", str(value), "--key-layout", layout, "--cores", "8"]
    if subprocess.run(args + ["--resolve-only", "1"], capture_output=True).returncode == 0:
        return
    subprocess.run(args + ["--prepare-planner", "1"], check=True, capture_output=True, timeout=3600)


def census(binary, value):
    options = ["--two-tier"] if value == "two_tier" else ["--value-bytes", str(value), "--targets", "16"]
    result = subprocess.run([binary, *options], capture_output=True, text=True, timeout=3600, env=ENVIRONMENT)
    assert result.returncode == 0, result.stderr
    return json.loads(result.stdout)


def source_lines(binary, report):
    """Source lines of the branches where traces depart from the first target's.

    The census reports executable addresses only, so each maps through the load bias.
    """
    bias = int(report["executable_bias"], 16)
    inside = [int(t["departure"]["branch"], 16) - bias for t in report["traces"] if t["departure"]]
    if not inside:
        return collections.Counter()
    # One line per address, "path:line" or "path:line (discriminator n)": the
    # innermost inlined function's line, where the instruction came from.
    output = subprocess.run(["addr2line", "-e", binary, *[hex(a) for a in inside]], capture_output=True,
                            text=True, check=True).stdout.splitlines()
    lines = collections.Counter()
    for line in output:
        location = line.split(" (")[0]
        if ":" in location and not location.startswith("??"):
            path, number = location.rsplit(":", 1)
            lines[Path(path).name + ":" + number] += 1
    return lines


def main(patched, shipped, worker):
    failures = []
    # Each shape's block, then one two-tier table (16-byte blocks, planned with
    # the first shape): keys in its overflow pile against keys in its major bins.
    for key, value, layout in SHAPES + ((None, "two_tier", None),):
        if key is not None:
            prepare(worker, key, value, layout)
        reports = {"patched": census(patched, value), "shipped": census(shipped, value)}
        for build, report in reports.items():
            hashes = collections.Counter(t["hash"] for t in report["traces"])
            counts = sorted({t["instructions"] for t in report["traces"]})
            lines = source_lines(patched if build == "patched" else shipped, report)
            name = "two-tier table" if value == "two_tier" else f"{value:5d} B values"
            print(f"{name}, {build:7s}: {len(report['traces'])} targets, {len(hashes)} distinct "
                  f"traces, {counts[0]}..{counts[-1]} instructions")
            for line, count in lines.most_common(8):
                print(f"        departs at the branch at {line} ({count} targets)")
            if build == "patched" and len(hashes) != 1:
                failures.append(f"{value} B: the patched lookup's trace depends on the target")
            if build == "shipped":
                # The first departure: the generic CMOV's branch, which in a two-tier
                # table's overflow-bin scan comes before its own branch on the overflow hit.
                expected = ("oblivious_operations.hpp:", "ohash_tiers.hpp:")
                if len(hashes) == 1:
                    failures.append(f"{value}: the shipped lookup no longer branches on the match")
                elif not any(line.startswith(expected) for line in lines):
                    failures.append(f"{value}: the shipped build's divergence is not in the lookup's branches")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    print("census: the patched lookup is one trace at every shape and in a two-tier table; "
          "the shipped one branches in CMOV and in the two-tier lookup")
    return 0


if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:4]))
