#!/usr/bin/env python3
"""The paper's micro-benchmark numbers: run the released drivers with the
paper's flags and reduce their rows to the quoted numbers.

Each subcommand runs one measurement, writes the drivers' raw output, a
commands log and summary.json to --out DIR, and prints each reproduced number
beside the paper's value.  --summarize-only re-reads DIR without running
anything; --dry-run prints the commands.

  table-rebuild       one table rebuild, ours against H2O2RAM's build
                      (cpu_byteslice_table_rebuild_benchmark init/chain and
                      h2o2ram_routing_bench), one pinned core
  routing-locality    eight routes at once, one pass per stage against the
                      cache-oblivious route (cpu_byteslice_stash_rebuild_benchmark
                      --instances 8), run twice
  vp2intersect-merge  complete merges in a native and a
                      -DCPU_BYTESLICE_ORAM_ENABLE_VP2INTERSECT=OFF build
                      (cpu_byteslice_level_arena_benchmark --owners 0 --write-only)
  tables-per-lookup   main hash tables per lookup at 2^27, B = 8, one request at
                      a time and batches of 64 (arena benchmark --probe-counts)
  write-throughput    all-write rate at 2^27, B = 8, 14 rebuild threads
                      (arena benchmark --write-only)
  eviction            one eviction pass against EnigMap's, 2^21 entries, fold 4,
                      A = 3, three rounds with the arm order rotated
                      (cpu_tree_eviction_comparator_benchmark[_enigmap])
  memory-latency      idle DRAM load-to-use latency per core after touching
                      guest memory (cpu_host_topology_probe region, then core)
  l3-check            whole-L3 judge for a boot (cpu_cache_latency_benchmark on
                      one core per L3 domain): exit 0 WHOLE, 1 CAPPED, 2 error
  cpus                the CPU choices this host's topology gives

CPU choices come from sysfs: one CPU per physical core, core 0's excluded
(the harness's), whether SMT siblings are numbered adjacently (CPU 2k, 2k+1)
or k and k+N.  Every list can be overridden.  Logs name binaries by their
base name and SHA-256, never a host or a home directory.

Run from the repository root, for example
  python3 analysis/paper_micro.py table-rebuild --out out/table-rebuild
"""
import argparse
import hashlib
import json
import os
import re
import shlex
import statistics
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import compare_share  # noqa: E402

SYSFS_CPU = "/sys/devices/system/cpu"
N27 = 1 << 27

# The paper's values, quoted beside each reproduced number.
PAPER = {
    "table_rebuild_with_dups_v8": "Intel 30-54x, AMD 60-139x",
    "table_rebuild_2p20_ours_ms": "Intel 48.2 ms, AMD 18.0 ms",
    "table_rebuild_2p20_h2o2ram_ms": "about 2.5 s on both (Intel 2,461 ms, AMD 2,492 ms)",
    "routing_ratio": "3.2x on Intel TDX (the lower of two runs, measured 3.47x and 3.22x)",
    "vp2intersect_ratio": "about 1.7x on AMD (measured 1.76x at 2,048, 1.77x at 32,768, 1.65x at 1,048,576)",
    "tables_scalar": "Intel 6.3, AMD 6.0",
    "tables_batch": "Intel 7.8, AMD 7.1",
    "write_rate": "Intel 4.7 M writes/s, AMD 10.1 M writes/s",
    "write_over_single": "Intel 4.0x, AMD 12x",
    "evict_ours_us": "Intel 8.1 us, AMD 4.3 us",
    "evict_enigmap_us": "Intel 442 us, AMD 274 us",
    "dram_ns": "TDX 150-180 ns, SEV-SNP about 205 ns, E6 without SNP 128 ns",
}
# Table 1's single-request rates at K4/V8 2^27, the write ratio's denominators.
TABLE1_SINGLE = {"Intel": 1165738.0, "AMD": 844715.0}
L3_LIMITS = "16.0:16.0,22.6:23.5,26.9:25.5"
L3_LLCPAR_LIMIT = 17.5


# ---------------------------------------------------------------- topology

def parse_cpulist(text):
    """'0-3,8,10-11' -> [0, 1, 2, 3, 8, 10, 11] (the sysfs and taskset list format)."""
    cpus = []
    for part in text.strip().split(","):
        part = part.strip()
        if not part:
            continue
        if "-" in part:
            lo, hi = part.split("-", 1)
            cpus.extend(range(int(lo), int(hi) + 1))
        else:
            cpus.append(int(part))
    return cpus


def cpulist(cpus):
    return ",".join(str(c) for c in cpus)


def _read(path):
    with open(path) as handle:
        return handle.read().strip()


def read_topology(root=SYSFS_CPU):
    """{cpu: {"siblings": frozenset, "l3": frozenset or None}} for the online CPUs."""
    topo = {}
    for entry in sorted(os.listdir(root)):
        match = re.fullmatch(r"cpu(\d+)", entry)
        if not match:
            continue
        cpu = int(match.group(1))
        base = os.path.join(root, entry)
        try:
            if _read(os.path.join(base, "online")) == "0":
                continue
        except OSError:
            pass
        try:
            siblings = frozenset(parse_cpulist(_read(os.path.join(base, "topology",
                                                                   "thread_siblings_list"))))
        except OSError:
            continue
        l3 = None
        cache = os.path.join(base, "cache")
        if os.path.isdir(cache):
            for index in sorted(os.listdir(cache)):
                try:
                    if _read(os.path.join(cache, index, "level")) == "3":
                        l3 = frozenset(parse_cpulist(_read(os.path.join(cache, index,
                                                                         "shared_cpu_list"))))
                except OSError:
                    continue
        topo[cpu] = {"siblings": siblings | {cpu}, "l3": l3}
    return topo


def physical_cores(topo):
    """The first (lowest online) CPU of every SMT sibling group, ascending."""
    return sorted({min(t["siblings"] & topo.keys()) for t in topo.values()})


def paper_cpus(topo):
    """One CPU per physical core, core 0's excluded: C4 (siblings k, k+16)
    gives 1..15, Oracle E6 (siblings 2k, 2k+1) gives 2, 4, ..., 30."""
    core0 = topo[0]["siblings"] if 0 in topo else {0}
    return [c for c in physical_cores(topo) if c not in core0]


def l3_domains(topo):
    """The physical cores (first CPUs) of each L3 domain, domains by lowest CPU."""
    groups = {}
    everything = frozenset(topo)
    for c in physical_cores(topo):
        groups.setdefault(topo[c]["l3"] or everything, []).append(c)
    return sorted((sorted(v) for v in groups.values()), key=lambda d: d[0])


def l3_check_cpus(topo):
    """The second physical core of each L3 domain: CPU 2 and 18 on Oracle E6,
    CPU 1 on C4 (the first is skipped so that domain 0 avoids core 0)."""
    return [d[1] if len(d) > 1 else d[0] for d in l3_domains(topo)]


def layout(cpus, rebuild_threads=14, batch_threads=8, batch_rebuild=7):
    """The records' placement from one-per-core CPUs (core 0 excluded): the
    caller on the first, rebuild threads on the next `rebuild_threads`; for a
    batch row of `batch_threads` threads, the last `batch_threads` of the first
    batch_threads + batch_rebuild CPUs, rebuild threads on the ones before."""
    first = cpus[:batch_threads + batch_rebuild]
    return {"caller": cpus[:1], "rebuild": cpus[1:1 + rebuild_threads],
            "batch": first[-batch_threads:], "batch_rebuild": first[:-batch_threads][:batch_rebuild]}


# ---------------------------------------------------------------- running

class Runner:
    """Runs one step at a time, appending its stdout to DIR/STEM+suffix and its
    stderr to DIR/STEM.err, and logs `STEM exit=.. seconds=.. :: command` to
    DIR/commands.log with binaries by base name (their SHA-256 logged once)."""

    def __init__(self, out, quiet=False):
        self.out = Path(out)
        self.quiet = quiet
        self.failed = []
        self.hashed = set()
        self.out.mkdir(parents=True, exist_ok=True)

    @staticmethod
    def display(argv):
        # Absolute paths (which may name a home directory) and existing files
        # are shown by base name, whether or not the file exists.
        return " ".join(shlex.quote(os.path.basename(a) if os.path.isabs(a) or (os.sep in a and os.path.isfile(a))
                                    else a)
                        for a in argv)

    def log(self, line):
        with open(self.out / "commands.log", "a") as handle:
            handle.write(line + "\n")

    def run(self, stem, argv, suffix=".txt"):
        shown = self.display(argv)
        for a in argv:
            if os.sep in a and os.path.isfile(a) and a not in self.hashed:
                self.hashed.add(a)
                digest = hashlib.sha256(Path(a).read_bytes()).hexdigest()
                self.log("binary %s sha256 %s" % (os.path.basename(a), digest))
        start = time.monotonic()
        with open(self.out / (stem + suffix), "ab") as out, open(self.out / (stem + ".err"), "ab") as err:
            try:
                code = subprocess.call(argv, stdout=out, stderr=err)
            except OSError as error:
                err.write(("cannot run %s: %s\n" % (argv[0], error)).encode())
                code = 127
        seconds = time.monotonic() - start
        stamp = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        self.log("%s %s exit=%d seconds=%.2f :: %s" % (stamp, stem, code, seconds, shown))
        if not self.quiet:
            print("  %s exit=%d %.1f s" % (stem, code, seconds), file=sys.stderr, flush=True)
        if code:
            self.failed.append(stem)
        return code


def json_rows(path):
    """The JSON objects of a file, one per line; other lines skipped."""
    rows = []
    if not Path(path).exists():
        return rows
    for line in Path(path).read_text(errors="replace").splitlines():
        line = line.strip()
        if line.startswith("{"):
            try:
                rows.append(json.loads(line))
            except ValueError:
                pass
    return rows


def prefixed_rows(path, prefix):
    rows = []
    if not Path(path).exists():
        return rows
    for line in Path(path).read_text(errors="replace").splitlines():
        if line.startswith(prefix + " "):
            try:
                rows.append(json.loads(line[len(prefix) + 1:]))
            except ValueError:
                pass
    return rows


def fit_run_row(path):
    """The FIT_ROW run row of an arena benchmark output (the last, with --reps 1)."""
    runs = [r for r in prefixed_rows(path, "FIT_ROW") if r.get("fit_row") == "run"]
    return runs[-1] if runs else None


def probe_summary(path):
    rows = prefixed_rows(path, "PROBE_SUMMARY")
    return rows[-1] if rows else None


def item(name, value, unit, field, paper, note=""):
    return {"name": name, "reproduced": value, "unit": unit, "field": field, "paper": paper, "note": note}


def fmt(value, unit=""):
    if value is None:
        return "-"
    if isinstance(value, str):
        return value
    if unit == "x":
        return "%.2fx" % value
    if abs(value) >= 1000:
        return "{:,.0f}".format(value) + (" " + unit if unit else "")
    return "%.4g" % value + (" " + unit if unit else "")


def report(summary):
    lines = ["[%s] %s" % (summary["claim"], summary.get("setup", ""))]
    for it in summary["items"]:
        lines.append("  - %s: %s    (paper: %s)" % (it["name"], fmt(it["reproduced"], it["unit"]), it["paper"]))
        if it.get("note"):
            lines.append("      (%s)" % it["note"])
    for line in summary.get("table", []):
        lines.append("  " + line)
    for problem in summary.get("problems", []):
        lines.append("  PROBLEM: " + problem)
    return "\n".join(lines)


# ---------------------------------------------------------------- table rebuild

def plan_table_rebuild(a):
    steps = []
    for v in a.values:
        for e in range(a.min_log2, a.max_log2 + 1):
            steps.append(("ours-init-v%d" % v, [a.ours, "--mode", "init", "--capacity", str(1 << e), "--key", "4",
                                                "--value", str(v), "--reps", "5", "--cpu", str(a.cpu)]))
        steps.append(("ours-chain-v%d" % v, [a.ours, "--mode", "chain", "--capacity", str(1 << (a.max_log2 + 2)),
                                             "--key", "4", "--value", str(v), "--cpu", str(a.cpu)]))
        if a.h2o2ram:
            for slots in a.slots:
                for e in range(a.min_log2, a.max_log2 + 1):
                    steps.append(("h2o2ram-v%d-s%d" % (v, slots),
                                  ["taskset", "-c", str(a.cpu), a.h2o2ram, "--key-bytes", "4", "--value-bytes",
                                   str(v), "--live-entries", str(1 << e), "--threads", "1", "--bucket-slots",
                                   str(slots)]))
    return [(stem, argv, ".jsonl") for stem, argv in steps]


def summarize_table_rebuild(out):
    out = Path(out)
    widths = sorted({int(p.stem.split("-v")[1]) for p in out.glob("ours-init-v*.jsonl")})
    items, table, problems, details = [], [], [], {}
    for v in widths:
        init = {r["table_entries"]: r for r in json_rows(out / ("ours-init-v%d.jsonl" % v))
                if r.get("mode") == "init" and "median_ms" in r}
        chain = {r["table_entries"]: r for r in json_rows(out / ("ours-chain-v%d.jsonl" % v))
                 if r.get("row") == "cascade" and not r.get("top")}
        h2 = {s: {r["live"]: r for r in json_rows(out / ("h2o2ram-v%d-s%d.jsonl" % (v, s))) if "median_ms" in r}
              for s in (64, 128)}
        sizes = sorted(init)
        rows = []
        for n in sizes:
            a, b, i, c = h2[64].get(n), h2[128].get(n), init.get(n), chain.get(n)
            row = {"entries": n, "h2o2ram_64_ms": a and a["median_ms"], "h2o2ram_128_ms": b and b["median_ms"],
                   "ours_init_ms": i and i["median_ms"], "ours_chain_ms": c and c["median_ms"],
                   "h2o2ram_lost": [r and r.get("lost_to_overflow") for r in (a, b)]}
            row["speedup_no_dups"] = a["median_ms"] / i["median_ms"] if a and i else None
            row["speedup_with_dups"] = a["median_ms"] / c["median_ms"] if a and c else None
            rows.append(row)
            if any(x for x in row["h2o2ram_lost"]):
                problems.append("V%d 2^%d: H2O2RAM lost records to overflow %s" % (v, n.bit_length() - 1,
                                                                                  row["h2o2ram_lost"]))
            if c is None:
                problems.append("V%d: no chain cascade row builds %d entries" % (v, n))
        details["V%d" % v] = rows
        with_dups = [r["speedup_with_dups"] for r in rows if r["speedup_with_dups"]]
        no_dups = [r["speedup_no_dups"] for r in rows if r["speedup_no_dups"]]
        span = "2^%d..2^%d" % (sizes[0].bit_length() - 1, sizes[-1].bit_length() - 1) if sizes else "-"

        def rng(xs):
            return "%.0fx .. %.0fx" % (min(xs), max(xs)) if xs else None
        paper = v == 8
        items.append(item("V%d speedup with duplicates (H2O2RAM 64-slot / ours chain), %s" % (v, span),
                          rng(with_dups), "", "speedup with dups column, min .. max",
                          PAPER["table_rebuild_with_dups_v8"] if paper else "V8 only"))
        items.append(item("V%d speedup without duplicates (H2O2RAM 64-slot / ours init)" % v, rng(no_dups), "",
                          "speedup no dups column", "not in the paper"))
        at = next((r for r in rows if r["entries"] == 1 << 20), None)
        if at:
            items.append(item("V%d 2^20: ours with duplicates (chain cascade)" % v, at["ours_chain_ms"], "ms",
                              "ours-chain row=cascade median_ms",
                              PAPER["table_rebuild_2p20_ours_ms"] if paper else "V8 only"))
            items.append(item("V%d 2^20: H2O2RAM 64-slot build" % v, at["h2o2ram_64_ms"], "ms",
                              "h2o2ram-s64 median_ms",
                              PAPER["table_rebuild_2p20_h2o2ram_ms"] if paper else "V8 only"))
        table.append("K4 / V%d, one core: entries | H2O2RAM 64 ms | H2O2RAM 128 ms | ours init ms | "
                     "ours chain ms | speedup no dups | with dups" % v)
        for r in rows:
            table.append("  %10s | %10s | %10s | %10s | %10s | %8s | %8s" % (
                "{:,}".format(r["entries"]), fmt(r["h2o2ram_64_ms"]), fmt(r["h2o2ram_128_ms"]),
                fmt(r["ours_init_ms"]), fmt(r["ours_chain_ms"]),
                "%.0fx" % r["speedup_no_dups"] if r["speedup_no_dups"] else "-",
                "%.0fx" % r["speedup_with_dups"] if r["speedup_with_dups"] else "-"))
        if not h2[64]:
            problems.append("V%d: no H2O2RAM 64-slot rows (pass --h2o2ram-bench)" % v)
    if not widths:
        problems.append("no ours-init-v*.jsonl rows in %s" % out)
    return {"claim": "table-rebuild", "setup": "one table rebuild on one pinned core, K4",
            "items": items, "table": table, "problems": problems, "details": details}


# ---------------------------------------------------------------- routing locality

def plan_routing_locality(a):
    return [("routes-%d" % (i + 1),
             [a.binary, "--network", "flat,cache_oblivious", "--key-bytes", "4", "--value-bytes", "8",
              "--live-entries", str(a.live_entries), "--instances", str(len(a.cpus)), "--cpus", cpulist(a.cpus),
              "--reps", str(a.reps), "--seed", "741"], ".jsonl")
            for i in range(a.repeats)]


def summarize_routing_locality(out):
    out = Path(out)
    runs, problems = [], []
    for path in sorted(out.glob("routes-*.jsonl"), key=lambda p: int(p.stem.split("-")[1])):
        rows = json_rows(path)
        ratio = next((r for r in rows if r.get("mode") == "instances_ratio"), None)
        nets = {r["network"]: r for r in rows if r.get("mode") == "instances"}
        bad = [n for n, r in nets.items() if r.get("status") != "ok"]
        if bad:
            problems.append("%s: status not ok for %s" % (path.name, ", ".join(bad)))
        if ratio is None:
            problems.append("%s: no instances_ratio row" % path.name)
            continue
        runs.append({"run": path.stem, "route_ratio_median": ratio["route_ratio_median"],
                     "route_ratio_min": ratio["route_ratio_min"], "route_ratio_max": ratio["route_ratio_max"],
                     "flat_ms": nets.get("flat", {}).get("route_ms_median"),
                     "cache_oblivious_ms": nets.get("cache_oblivious", {}).get("route_ms_median"),
                     "instances": ratio.get("instances"), "cpus": ratio.get("cpus"),
                     "live_entries": ratio.get("live_entries", nets.get("flat", {}).get("live_entries"))})
    items = [item("%s: flat / cache-oblivious route time (median over rounds)" % r["run"],
                  r["route_ratio_median"], "x", "instances_ratio route_ratio_median",
                  PAPER["routing_ratio"],
                  "flat %s ms, cache-oblivious %s ms, %s instances on CPUs %s" % (
                      fmt(r["flat_ms"]), fmt(r["cache_oblivious_ms"]), r["instances"], r["cpus"]))
             for r in runs]
    if runs:
        items.append(item("lower of the runs (the paper quotes the lower)",
                          min(r["route_ratio_median"] for r in runs), "x", "min route_ratio_median",
                          PAPER["routing_ratio"]))
    else:
        problems.append("no routes-*.jsonl rows in %s" % out)
    sizes = sorted({r["live_entries"] for r in runs if r.get("live_entries")})
    setup = ("%s records per table, 8-byte values, one table per core"
             % (", ".join("2^%d" % (n.bit_length() - 1) if n & (n - 1) == 0 else str(n) for n in sizes) or "?"))
    return {"claim": "routing-locality", "setup": setup,
            "items": items, "problems": problems, "details": runs}


# ---------------------------------------------------------------- VP2INTERSECT merge

def plan_vp2intersect_merge(a):
    steps = []
    for arm, build in (("native", a.native_build), ("fallback", a.fallback_build)):
        bench = os.path.join(build, "benchmarks")
        steps.append(("%s-dedup-half" % arm, ["taskset", "-c", str(a.cpu),
                                              os.path.join(bench, "cpu_byteslice_dedup_kernel_benchmark"),
                                              str(a.kernel_pairs), "1", "half_unique"], ".txt"))
        for n in a.sizes:
            kinds = ("plain", "counted") if a.with_share else ("plain",)
            for kind in kinds:
                binary = os.path.join(bench, "cpu_byteslice_level_arena_benchmark")
                if kind == "counted":
                    binary += "_compare_counted"
                steps.append(("%s-merge-%d-%s" % (arm, n, kind),
                              ["taskset", "-c", str(a.cpu), binary, "--capacity", str(n), "--key", "4", "--value",
                               "8", "--branching", "8", "--owners", "0", "--write-only", "--settle", str(n),
                               "--accesses", str(2 * n), "--stage-times", "--fit-rows", "--reps", str(a.reps)],
                              ".txt"))
    return steps


def dedup_header(path):
    """(VP2INTERSECT compiled, {kernel row: median ns}) from a dedup kernel output."""
    if not Path(path).exists():
        return None, {}
    text = Path(path).read_text(errors="replace")
    match = re.search(r"VP2INTERSECT compiled: (\d)", text)
    return (bool(int(match.group(1))) if match else None), compare_share.read_kernel(str(path))


def summarize_vp2intersect_merge(out):
    out = Path(out)
    sizes = sorted({int(p.stem.split("-")[2]) for p in out.glob("native-merge-*-plain.txt")})
    items, problems, details = [], [], {"sizes": {}}
    compiled = {}
    for arm in ("native", "fallback"):
        flag, kernel = dedup_header(out / ("%s-dedup-half.txt" % arm))
        compiled[arm] = flag
        details[arm + "_vp2intersect_compiled"] = flag
        details[arm + "_self_4b_ns"] = kernel.get((4, "self"))
    if compiled.get("native") is False:
        problems.append("the native build has no VP2INTERSECT compiled in (this CPU lacks it): both arms run "
                        "the fallback and the ratio is not the paper's quantity")
    if compiled.get("fallback"):
        problems.append("the fallback build has VP2INTERSECT compiled in: configure it with "
                        "-DCPU_BYTESLICE_ORAM_ENABLE_VP2INTERSECT=OFF")
    ratios = []
    for n in sizes:
        med = {}
        for arm in ("native", "fallback"):
            path = out / ("%s-merge-%d-plain.txt" % (arm, n))
            merges = compare_share.read_merge(str(path)) if path.exists() else []
            values = [m["job_nanos"] / 1e6 for m in merges if m["levels"]]
            med[arm] = statistics.median(values) if values else None
            if not values:
                problems.append("%s: no FIT_ROW merge rows" % path.name)
        ratio = med["fallback"] / med["native"] if med["native"] and med["fallback"] else None
        if ratio:
            ratios.append(ratio)
        details["sizes"][n] = {"native_merge_ms": med["native"], "fallback_merge_ms": med["fallback"],
                               "fallback_over_native": ratio}
        items.append(item("N=%s: complete merge, fallback / native" % "{:,}".format(n), ratio, "x",
                          "median merge_ms (sum of FIT_ROW level job_nanos)", PAPER["vp2intersect_ratio"],
                          "native %s ms, fallback %s ms" % (fmt(med["native"]), fmt(med["fallback"]))))
        for arm in ("native", "fallback"):
            share = out / ("%s-merge-%d-counted.txt" % (arm, n))
            if share.exists():
                try:
                    counted = compare_share.read_counted(str(share))
                    merges = compare_share.read_merge(str(out / ("%s-merge-%d-plain.txt" % (arm, n))))
                    _, kernel = dedup_header(out / ("%s-dedup-half.txt" % arm))
                    if counted and kernel:
                        row = compare_share.share(counted[0], merges[0] if merges else None, kernel)
                        details["sizes"][n][arm + "_comparison_share_percent"] = row["fraction_percent"]
                except (ValueError, KeyError, IndexError) as error:
                    problems.append("%s: compare_share failed: %s" % (share.name, error))
    if ratios:
        items.append(item("range over the sizes", "%.2fx .. %.2fx" % (min(ratios), max(ratios)), "",
                          "fallback / native", PAPER["vp2intersect_ratio"]))
    else:
        problems.append("no native/fallback merge pairs in %s" % out)
    return {"claim": "vp2intersect-merge", "setup": "K4/V8, B = 8, inline merges (--owners 0), median of reps",
            "items": items, "problems": problems, "details": details}


# ---------------------------------------------------------------- tables per lookup

def plan_tables_per_lookup(a):
    n = str(a.capacity)
    common = ["--capacity", n, "--key", "4", "--value", "8", "--branching", "8", "--settle", n, "--accesses", n,
              "--fit-rows", "--reps", "1"]
    steps = []
    for mode in a.modes:
        for mix in a.mixes:
            flag = ["--read-only"] if mix == "read-only" else []
            if mode == "scalar":
                argv = (["taskset", "-c", cpulist(a.caller), a.arena] + common +
                        ["--rebuild-threads", str(len(a.rebuild)), "--rebuild-cpus", cpulist(a.rebuild)] +
                        flag + ["--probe-counts"])
            else:
                argv = (["taskset", "-c", cpulist(a.batch), a.arena] + common +
                        ["--rebuild-threads", str(len(a.batch_rebuild)), "--rebuild-cpus",
                         cpulist(a.batch_rebuild)] + flag +
                        ["--probe-counts", "--batch", "64", "--lanes", "8", "--participants", "8", "--parallel"])
            steps.append(("tables-%s-%s" % (mix, mode), argv, ".txt"))
    return steps


TABLE_FIELDS = ("capacity", "branching", "levels", "owners", "top_helpers", "batch", "accesses", "lookups_counted",
                "lookup_mains_mean", "lookup_mains_max", "lookup_tables_mean", "lookup_tables_max",
                "completed_records_per_s")


def summarize_tables_per_lookup(out):
    out = Path(out)
    items, problems, details = [], [], {}
    def order(path):
        mix, mode = path.stem[len("tables-"):].rsplit("-", 1)
        return (mix != "read-only", mode != "scalar", path.stem)
    for path in sorted(out.glob("tables-*.txt"), key=order):
        mix, mode = path.stem[len("tables-"):].rsplit("-", 1)
        row = fit_run_row(path)
        if row is None:
            problems.append("%s: no FIT_ROW run row" % path.name)
            continue
        details[path.stem] = {k: row.get(k) for k in TABLE_FIELDS}
        paper = (PAPER["tables_scalar"] if mode == "scalar" else PAPER["tables_batch"]) \
            if mix == "read-only" else "read-only rows only"
        items.append(item("%s %s: main tables per lookup (mean; max %s)" % (mix, mode, row.get("lookup_mains_max")),
                          row.get("lookup_mains_mean"), "", "FIT_ROW run lookup_mains_mean", paper,
                          "N=%s, %s levels, %s owners + %s top helpers, %s req/s" % (
                              "{:,}".format(row["capacity"]), row.get("levels"), row.get("owners"),
                              row.get("top_helpers"), fmt(row.get("completed_records_per_s")))))
    if not items:
        problems.append("no tables-*.txt rows in %s" % out)
    return {"claim": "tables-per-lookup", "setup": "K4/V8, B = 8, settle N then N accesses",
            "items": items, "problems": problems, "details": details}


# ---------------------------------------------------------------- write throughput

def plan_write_throughput(a):
    n = str(a.capacity)
    return [("write-only", ["taskset", "-c", cpulist(a.caller), a.arena, "--capacity", n, "--key", "4", "--value",
                            "8", "--branching", "8", "--settle", n, "--accesses", n, "--fit-rows", "--reps", "1",
                            "--rebuild-threads", str(len(a.rebuild)), "--rebuild-cpus", cpulist(a.rebuild),
                            "--write-only", "--merge-rows", "--probe-counts"], ".txt")]


def summarize_write_throughput(out, scalar_rate=None):
    out = Path(out)
    row = fit_run_row(out / "write-only.txt")
    if row is None:
        return {"claim": "write-throughput", "items": [], "problems": ["no FIT_ROW run row in write-only.txt"]}
    rate = row["completed_records_per_s"]
    problems = []
    if not row.get("write_only"):
        problems.append("FIT_ROW run is not write_only")
    if not row.get("preroute", True):
        problems.append("pre-routing was off")
    items = [item("all-write rate", rate / 1e6, "M writes/s", "FIT_ROW run completed_records_per_s",
                  PAPER["write_rate"], "N=%s, %s owners + %s top helpers = %s rebuild threads, %s accesses" % (
                      "{:,}".format(row["capacity"]), row.get("owners"), row.get("top_helpers"),
                      (row.get("owners") or 0) + (row.get("top_helpers") or 0), "{:,}".format(row["accesses"])))]
    if scalar_rate:
        items.append(item("over the measured single-request rate %s req/s" % fmt(scalar_rate), rate / scalar_rate,
                          "x", "rate / --scalar-rate", PAPER["write_over_single"]))
    for target, single in TABLE1_SINGLE.items():
        items.append(item("over the paper's %s Table 1 single cell (%s req/s)" % (target, fmt(single)),
                          rate / single, "x", "rate / Table 1 single", PAPER["write_over_single"]))
    return {"claim": "write-throughput", "setup": "K4/V8, B = 8, warm-up N/2, settle N, N blind writes timed",
            "items": items, "problems": problems,
            "details": {k: row.get(k) for k in TABLE_FIELDS + ("write_only", "preroute", "seconds")}}


# ---------------------------------------------------------------- eviction

def eviction_arms(binary):
    arms = ["read_path", "read_path_transposed"]
    return arms + ["enigmap"] if "enigmap" in os.path.basename(binary) else arms


def plan_eviction(a):
    arms = a.arms or eviction_arms(a.binary)
    steps = []
    for r in range(1, a.rounds + 1):
        for k in range(len(arms)):
            arm = arms[(k + r - 1) % len(arms)]
            steps.append(("evict-r%d-%s" % (r, arm),
                          ["taskset", "-c", str(a.cpu), a.binary, "--capacity", str(a.capacity), "--key-bytes", "4",
                           "--value-bytes", ",".join(str(v) for v in a.value_bytes), "--passes", str(a.passes),
                           "--verify-passes", str(a.verify_passes), "--fold", "4", "--stash-registers", "3",
                           "--arm", arm], ".jsonl"))
    return steps


def summarize_eviction(out):
    out = Path(out)
    times, problems, geometry = {}, [], {}
    for path in sorted(out.glob("evict-r*-*.jsonl")):
        match = re.fullmatch(r"evict-r(\d+)-(\w+)", path.stem)
        for row in json_rows(path):
            if row.get("status") != "ok":
                problems.append("round %s %s V=%s: status %s" % (match.group(1), row.get("arm"),
                                                                 row.get("value_bytes"), row.get("status")))
                continue
            times.setdefault((row["arm"], row["value_bytes"]), []).append(row["ns_per_pass"])
            geometry = {k: row.get(k) for k in ("capacity", "key_bytes", "fold", "stash_registers", "path_buckets",
                                                "lanes", "passes", "verified_passes")}
    widths = sorted({v for _, v in times})
    arms = [a for a in ("read_path", "read_path_transposed", "enigmap") if any(a == k[0] for k in times)]

    def med(arm, v):
        t = times.get((arm, v))
        return statistics.median(t) if t else None
    table = ["V (B) | " + " | ".join("%s median ns (rounds)" % a for a in arms) + " | EnigMap / ours"]
    for v in widths:
        cells = ["%s (%d)" % (fmt(med(a, v)), len(times.get((a, v), []))) for a in arms]
        ours, enig = med("read_path_transposed", v), med("enigmap", v)
        table.append("%5d | " % v + " | ".join(cells) + " | " + ("%.0fx" % (enig / ours) if ours and enig else "-"))
    items = []
    v = 1024 if 1024 in widths else (widths[-1] if widths else None)
    if v is not None:
        ours, enig = med("read_path_transposed", v), med("enigmap", v)
        rounds = sorted({len(times.get((a, v), [])) for a in arms})
        items.append(item("V=%d: ours (read_path_transposed), median over rounds" % v, ours and ours / 1e3, "us",
                          "ns_per_pass / 1000", PAPER["evict_ours_us"] if v == 1024 else "1 KiB only",
                          "rounds per arm %s" % rounds))
        items.append(item("V=%d: EnigMap, median over rounds" % v, enig and enig / 1e3, "us", "ns_per_pass / 1000",
                          PAPER["evict_enigmap_us"] if v == 1024 else "1 KiB only",
                          "" if enig else "no enigmap rows: build cpu_tree_eviction_comparator_benchmark_enigmap"))
    else:
        problems.append("no eviction rows in %s" % out)
    return {"claim": "eviction", "setup": "one eviction pass on one core, %s" % geometry,
            "items": items, "table": table, "problems": problems,
            "details": {"%s/%d" % k: t for k, t in sorted(times.items())}}


# ---------------------------------------------------------------- memory latency

def plan_memory_latency(a):
    steps = []
    sudo = ["sudo"] if a.sudo else []
    if a.touch_gib:
        steps.append(("touch", sudo + [a.probe, "--tests", "region", "--region-gib", str(a.touch_gib),
                                       "--region-lines-per-page", "8", "--region-core", str(a.region_core)], ".txt"))
    argv = [a.probe, "--tests", "core"]
    if a.chase_mib:
        argv += ["--chase-mib", str(a.chase_mib)]
    if a.hops:
        argv += ["--hops", str(a.hops)]
    steps.append(("core", argv, ".txt"))
    return steps


def summarize_memory_latency(out):
    out = Path(out)
    core = probe_summary(out / "core.txt")
    touch = probe_summary(out / "touch.txt")
    problems = []
    if core is None or "core_dram_ns_median" not in core:
        return {"claim": "memory-latency", "items": [], "problems": ["no PROBE_SUMMARY core fields in core.txt"]}
    if touch is None:
        problems.append("no touch step: guest memory was not touched first (SNP latency reads high before it)")
    items = [item("idle DRAM load-to-use latency, median over physical cores", core["core_dram_ns_median"], "ns",
                  "PROBE_SUMMARY core_dram_ns_median", PAPER["dram_ns"],
                  "min %s, max %s over %s cores" % (fmt(core.get("core_dram_ns_min")),
                                                    fmt(core.get("core_dram_ns_max")), core.get("cores")))]
    details = {"core": core, "touch": touch}
    return {"claim": "memory-latency", "setup": "cpu_host_topology_probe --tests core after the region touch",
            "items": items, "problems": problems, "details": details}


# ---------------------------------------------------------------- L3 check

def parse_limits(text):
    limits = {}
    for part in text.split(","):
        size, limit = part.split(":")
        limits["%.1f" % float(size)] = float(limit)
    return limits


def curve_points(text):
    """{'16.0': ns, ...} from cpu_cache_latency_benchmark output (MiB rows only)."""
    points = {}
    for line in text.splitlines():
        match = re.match(r"^\s*([\d.]+) MiB\s+([\d.]+)\s*$", line)
        if match:
            points[match.group(1)] = float(match.group(2))
    return points


def llcpar_median(text, together_mib=32):
    match = re.search(r"\(\s*%d MiB together\)\s+median ([\d.]+)" % together_mib, text)
    return float(match.group(1)) if match else None


def judge_l3(curves, llcpar=(), limits=None, llcpar_limit=L3_LLCPAR_LIMIT):
    """curves: [(label, text)] of cpu_cache_latency_benchmark outputs; llcpar:
    [(label, text)] of `cpu_host_topology_probe --tests llcpar` outputs.
    Returns (verdict, failures, points): WHOLE only if every curve has every
    limit's point at or below it and every llcpar median is within its limit."""
    limits = limits or parse_limits(L3_LIMITS)
    failures, points = [], {}
    for label, text in curves:
        pts = curve_points(text)
        points[label] = {size: pts.get(size) for size in limits}
        for size, limit in limits.items():
            if size not in pts:
                failures.append("%s: no %s MiB point (raise --max-mib)" % (label, size))
            elif pts[size] > limit:
                failures.append("%s: %s MiB %.2f ns > %.1f" % (label, size, pts[size], limit))
    for label, text in llcpar:
        median = llcpar_median(text)
        points[label] = {"32 MiB together": median}
        if median is None:
            failures.append("%s: no '32 MiB together' line" % label)
        elif median > llcpar_limit:
            failures.append("%s: 32 MiB together median %.1f ns > %.1f" % (label, median, llcpar_limit))
    verdict = "WHOLE" if curves and not failures else "CAPPED"
    return verdict, failures, points


def plan_l3_check(a):
    steps = []
    for r in range(1, a.rounds + 1):
        for cpu in a.cpus:
            steps.append(("l3-r%d-cpu%d" % (r, cpu), [a.cachelat, "--cpu", str(cpu), "--max-mib", str(a.max_mib)],
                          ".txt"))
        if a.llcpar:
            for i, cores in enumerate(a.llcpar_cores):
                steps.append(("llcpar-r%d-d%d" % (r, i), [a.probe, "--tests", "llcpar", "--llcpar-cores",
                                                         cpulist(cores), "--llcpar-mib", "1,2,3,4,6"], ".txt"))
    return steps


def summarize_l3_check(out, limits=L3_LIMITS, llcpar_limit=L3_LLCPAR_LIMIT):
    out = Path(out)
    curves = [(p.stem, p.read_text(errors="replace")) for p in sorted(out.glob("l3-r*-cpu*.txt"))]
    llcpar = [(p.stem, p.read_text(errors="replace")) for p in sorted(out.glob("llcpar-r*-d*.txt"))]
    verdict, failures, points = judge_l3(curves, llcpar, parse_limits(limits), llcpar_limit)
    items = [item("whole-L3 verdict over %d curves, %d llcpar runs" % (len(curves), len(llcpar)), verdict, "",
                  "every curve within --limits", "only WHOLE boots count for the AMD numbers")]
    table = ["%s: %s" % (label, " ".join("%s=%s" % (k, fmt(v)) for k, v in pts.items()))
             for label, pts in points.items()]
    return {"claim": "l3-check", "setup": "limits %s; llcpar <= %.1f ns" % (limits, llcpar_limit),
            "items": items, "table": table, "problems": failures, "verdict": verdict,
            "details": points}


# ---------------------------------------------------------------- command line

def build_parser():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0], epilog=__doc__.split("\n\n", 1)[1],
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--sysfs", default=SYSFS_CPU, help=argparse.SUPPRESS)
    sub = ap.add_subparsers(dest="command", required=True)

    def common(p, build=True):
        p.add_argument("--out", required=True, help="output directory (raw rows, commands.log, summary.json)")
        p.add_argument("--summarize-only", action="store_true", help="re-read --out without running anything")
        p.add_argument("--dry-run", action="store_true", help="print the commands and exit")
        if build:
            p.add_argument("--build", default="build", help="build directory (default build)")
        return p

    p = common(sub.add_parser("table-rebuild", help="ours against H2O2RAM's table build"))
    p.add_argument("--ours", help="cpu_byteslice_table_rebuild_benchmark (default BUILD/benchmarks/...)")
    p.add_argument("--h2o2ram-bench", dest="h2o2ram",
                   default="build-baselines/h2o2ram/bin/h2o2ram_routing_bench",
                   help="h2o2ram_routing_bench; '' runs ours only")
    p.add_argument("--cpu", type=int, help="the one CPU (default: first CPU of physical core 1)")
    p.add_argument("--min-log2", type=int, default=10)
    p.add_argument("--max-log2", type=int, default=24)
    p.add_argument("--values", type=int, nargs="+", default=[8, 64])
    p.add_argument("--slots", type=int, nargs="+", default=[64, 128], choices=(64, 128))

    p = common(sub.add_parser("routing-locality", help="eight routes at once: flat against cache-oblivious"))
    p.add_argument("--binary", help="cpu_byteslice_stash_rebuild_benchmark")
    p.add_argument("--cpus", help="one CPU per instance (default: the first 8 one-per-core CPUs)")
    p.add_argument("--instances", type=int, default=8)
    p.add_argument("--live-entries", type=int, default=1 << 20)
    p.add_argument("--reps", type=int, default=50)
    p.add_argument("--repeats", type=int, default=2, help="invocations (the paper quotes the lower of two)")

    p = common(sub.add_parser("vp2intersect-merge", help="native against fallback complete merges"), build=False)
    p.add_argument("--native-build", default="build")
    p.add_argument("--fallback-build", default="build-fallback")
    p.add_argument("--cpu", type=int)
    p.add_argument("--sizes", type=int, nargs="+", default=[2048, 32768, 1048576])
    p.add_argument("--reps", type=int, default=3)
    p.add_argument("--kernel-pairs", type=int, default=2000000)
    p.add_argument("--with-share", action="store_true",
                   help="also run the _compare_counted build for compare_share's comparison share")

    p = common(sub.add_parser("tables-per-lookup", help="main tables per lookup, scalar and batch 64"))
    p.add_argument("--arena", help="cpu_byteslice_level_arena_benchmark")
    p.add_argument("--capacity", type=int, default=N27)
    p.add_argument("--modes", nargs="+", default=["scalar", "batch64"], choices=("scalar", "batch64"))
    p.add_argument("--mixes", nargs="+", default=["read-only"], choices=("read-only", "mixed"))
    p.add_argument("--caller", help="scalar caller CPU")
    p.add_argument("--rebuild-cpus", help="scalar rebuild CPUs (default the next 14)")
    p.add_argument("--batch-cpus", help="the batch's 8 CPUs (caller and helpers)")
    p.add_argument("--batch-rebuild-cpus", help="the batch row's 7 rebuild CPUs")

    p = common(sub.add_parser("write-throughput", help="all-write rate at 2^27"))
    p.add_argument("--arena", help="cpu_byteslice_level_arena_benchmark")
    p.add_argument("--capacity", type=int, default=N27)
    p.add_argument("--caller", help="caller CPU")
    p.add_argument("--rebuild-cpus", help="rebuild CPUs (default the next 14)")
    p.add_argument("--scalar-rate", type=float, help="the campaign's single-request rate at 2^27 for the ratio")

    p = common(sub.add_parser("eviction", help="our eviction pass against EnigMap's"))
    p.add_argument("--binary", help="default BUILD/benchmarks/cpu_tree_eviction_comparator_benchmark_enigmap")
    p.add_argument("--cpu", type=int)
    p.add_argument("--rounds", type=int, default=3)
    p.add_argument("--arms", nargs="+", choices=("read_path", "read_path_transposed", "enigmap"))
    p.add_argument("--capacity", type=int, default=1 << 21)
    p.add_argument("--value-bytes", type=int, nargs="+", default=[8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096])
    p.add_argument("--passes", type=int, default=20000)
    p.add_argument("--verify-passes", type=int, default=1000)

    p = common(sub.add_parser("memory-latency", help="per-core idle DRAM latency after the memory touch"))
    p.add_argument("--probe", help="cpu_host_topology_probe")
    p.add_argument("--touch-gib", type=int, required=False, default=None,
                   help="GiB the region touch faults in first (110 on a 128 GB VM); 0 skips it")
    p.add_argument("--region-core", type=int)
    p.add_argument("--sudo", action="store_true", help="run the touch under sudo (guest-physical binning)")
    p.add_argument("--chase-mib", type=int, help="probe default 4096")
    p.add_argument("--hops", type=int, help="probe default 8388608")

    p = common(sub.add_parser("l3-check", help="whole-L3 judge; exit 0 WHOLE, 1 CAPPED, 2 usage error or failed step"))
    p.add_argument("--cachelat", help="cpu_cache_latency_benchmark")
    p.add_argument("--probe", help="cpu_host_topology_probe (for --llcpar)")
    p.add_argument("--cpus", help="one CPU per L3 domain (default: each domain's second physical core)")
    p.add_argument("--max-mib", type=int, default=64, help="64 between campaigns; 512 for a boot's full curve")
    p.add_argument("--rounds", type=int, default=1)
    p.add_argument("--interval", type=float, default=30.0, help="seconds between rounds")
    p.add_argument("--limits", default=L3_LIMITS, help="MiB:ns,... (default: the E6 SNP whole-L3 limits)")
    p.add_argument("--llcpar", action="store_true", help="also the domain's cores at once, 32 MiB together")
    p.add_argument("--llcpar-cores", help="CPU groups for --llcpar, ';' between groups (default: the first 8 "
                   "physical cores of each L3 domain)")
    p.add_argument("--llcpar-limit", type=float, default=L3_LLCPAR_LIMIT)

    sub.add_parser("cpus", help="print this host's CPU choices as JSON")
    return ap


SUMMARIZERS = {
    "table-rebuild": summarize_table_rebuild,
    "routing-locality": summarize_routing_locality,
    "vp2intersect-merge": summarize_vp2intersect_merge,
    "tables-per-lookup": summarize_tables_per_lookup,
    "eviction": summarize_eviction,
    "memory-latency": summarize_memory_latency,
}


def cpu_choices(topo):
    cpus = paper_cpus(topo)
    lay = layout(cpus)
    return {"physical_cores": physical_cores(topo), "one_per_core_without_core0": cpus,
            "l3_domains": l3_domains(topo), "l3_check_cpus": l3_check_cpus(topo),
            "single_core": cpus[:1], "routing_instances": cpus[:8], "scalar_caller": lay["caller"],
            "scalar_rebuild": lay["rebuild"], "batch_threads": lay["batch"], "batch_rebuild": lay["batch_rebuild"]}


def resolve(a, topo_loader):
    """Fill the defaults that depend on the build directory and the topology."""
    topo = None

    def cpus():
        nonlocal topo
        if topo is None:
            topo = topo_loader()
        return paper_cpus(topo)

    def bench(name):
        return os.path.join(a.build, "benchmarks", name)
    cmd = a.command
    if cmd == "table-rebuild":
        a.ours = a.ours or bench("cpu_byteslice_table_rebuild_benchmark")
        a.cpu = cpus()[0] if a.cpu is None else a.cpu
    elif cmd == "routing-locality":
        a.binary = a.binary or bench("cpu_byteslice_stash_rebuild_benchmark")
        a.cpus = (parse_cpulist(a.cpus) if a.cpus else cpus())[:a.instances]
        if len(a.cpus) < a.instances:
            raise SystemExit("routing-locality: %d instances need %d CPUs, have %s" % (a.instances, a.instances,
                                                                                      a.cpus))
    elif cmd == "vp2intersect-merge":
        a.cpu = cpus()[0] if a.cpu is None else a.cpu
    elif cmd in ("tables-per-lookup", "write-throughput"):
        a.arena = a.arena or bench("cpu_byteslice_level_arena_benchmark")

        def pick(given, key):
            return parse_cpulist(given) if given else layout(cpus())[key]
        a.caller = pick(a.caller, "caller")
        a.rebuild = pick(a.rebuild_cpus, "rebuild")
        if cmd == "tables-per-lookup":
            a.batch = pick(a.batch_cpus, "batch")
            a.batch_rebuild = pick(a.batch_rebuild_cpus, "batch_rebuild")
        if len(a.rebuild) < 14 and not a.rebuild_cpus:
            print("note: only %d rebuild CPUs on this host (the paper's runs used 14)" % len(a.rebuild),
                  file=sys.stderr)
        rows = [("scalar", a.caller, a.rebuild)]
        if cmd == "tables-per-lookup" and "batch64" in a.modes:
            if len(a.batch) != 8:
                raise SystemExit("tables-per-lookup: the batch row runs 8 participants and needs 8 batch CPUs, "
                                 "have %s" % cpulist(a.batch))
            rows.append(("batch", a.batch, a.batch_rebuild))
        for name, front, back in rows:
            if not front or not back:
                raise SystemExit("%s: the %s row needs request and rebuild CPUs (have %s and %s); "
                                 "pass them explicitly on a host with fewer than 16 cores"
                                 % (cmd, name, cpulist(front) or "none", cpulist(back) or "none"))
            if set(front) & set(back):
                raise SystemExit("%s: the %s row's request CPUs %s overlap its rebuild CPUs %s"
                                 % (cmd, name, cpulist(front), cpulist(back)))
    elif cmd == "eviction":
        a.binary = a.binary or bench("cpu_tree_eviction_comparator_benchmark_enigmap")
        a.cpu = cpus()[0] if a.cpu is None else a.cpu
    elif cmd == "memory-latency":
        a.probe = a.probe or bench("cpu_host_topology_probe")
        a.region_core = cpus()[0] if a.region_core is None else a.region_core
        if a.touch_gib is None and not (a.summarize_only or a.dry_run):
            raise SystemExit("memory-latency: pass --touch-gib G (about 85%% of guest memory, 110 on a 128 GB "
                             "VM; 0 skips the touch)")
    elif cmd == "l3-check":
        a.cachelat = a.cachelat or bench("cpu_cache_latency_benchmark")
        a.probe = a.probe or bench("cpu_host_topology_probe")
        if topo is None:
            topo = topo_loader()
        a.cpus = parse_cpulist(a.cpus) if a.cpus else l3_check_cpus(topo)
        a.llcpar_cores = ([parse_cpulist(g) for g in a.llcpar_cores.split(";") if g.strip()] if a.llcpar_cores
                          else [d[:8] for d in l3_domains(topo)])
    return a


PLANS = {
    "table-rebuild": plan_table_rebuild,
    "routing-locality": plan_routing_locality,
    "vp2intersect-merge": plan_vp2intersect_merge,
    "tables-per-lookup": plan_tables_per_lookup,
    "write-throughput": plan_write_throughput,
    "eviction": plan_eviction,
    "memory-latency": plan_memory_latency,
    "l3-check": plan_l3_check,
}


def summarize(a):
    if a.command == "write-throughput":
        return summarize_write_throughput(a.out, a.scalar_rate)
    if a.command == "l3-check":
        return summarize_l3_check(a.out, a.limits, a.llcpar_limit)
    return SUMMARIZERS[a.command](a.out)


def main(argv=None, topo_loader=None):
    a = build_parser().parse_args(argv)
    topo_loader = topo_loader or (lambda: read_topology(a.sysfs))
    if a.command == "cpus":
        for key, value in cpu_choices(topo_loader()).items():
            print("%-28s %s" % (key, json.dumps(value)))
        return 0
    if not a.summarize_only:
        try:
            resolve(a, topo_loader)
        except SystemExit as error:  # a usage error: exit 2, never the l3-check verdict's 1
            if isinstance(error.code, str):
                print(error.code, file=sys.stderr)
                return 2
            raise
        steps = PLANS[a.command](a)
        if a.dry_run:
            for stem, argv_, _ in steps:
                print("%s: %s" % (stem, Runner.display(argv_)))
            return 0
        if any(Path(a.out, stem + suffix).exists() for stem, _, suffix in steps):
            print("%s already holds rows of this run: use a fresh --out, or --summarize-only" % a.out,
                  file=sys.stderr)
            return 2
        runner = Runner(a.out)
        runner.log("paper_micro %s" % a.command)
        last_round = None
        for stem, argv_, suffix in steps:
            round_ = re.match(r"(?:l3|llcpar)-r(\d+)-", stem)
            if round_ and last_round not in (None, round_.group(1)):
                time.sleep(a.interval)
            last_round = round_.group(1) if round_ else None
            runner.run(stem, argv_, suffix)
    summary = summarize(a)
    if not a.summarize_only:
        summary["failed_steps"] = runner.failed
        if runner.failed:
            summary["problems"].append("steps exited non-zero: %s (see their .err files)" % ", ".join(runner.failed))
    Path(a.out).mkdir(parents=True, exist_ok=True)
    with open(Path(a.out) / "summary.json", "w") as handle:
        json.dump(summary, handle, indent=1, default=str)
    print(report(summary))
    if summary.get("failed_steps"):
        return 2
    if a.command == "l3-check":
        return 0 if summary["verdict"] == "WHOLE" else 1
    return 1 if not summary["items"] else 0


if __name__ == "__main__":
    sys.exit(main())
