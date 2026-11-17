#!/usr/bin/env python3
"""A long, resumable stash-tail run of tree ORAM geometry rows: how many
stash lanes each access leaves occupied, sampled deep enough to extrapolate
the per-access tail to 2^-96 (see `stash_requirement.py`).

The rows come from `--rows F`, a JSON list whose rows are `[label, spec,
workload]` triples or objects with those three keys: the spec is the
benchmark's geometry string and the workload is `uniform` or `roundrobin`,
for example

  [["N21-f1-rr",
    "z=4,b=2,lam=19,fold=1,logn=21,sched=readpath,plan=inplace,preg=2,label=N21-f1-rr",
    "roundrobin"]]

An object row may also carry `seeds` (its own seed count, overriding
`--seeds`), `seed_base` (its first seed), `active` (false to plan the row
without running it) and a free-text `note`; all are copied into plan.json.
Row r's seeds are `seed_base + i`, or SEED_STRIDE * (r + 1) + i without a
`seed_base`, so a row's seeds depend on its position unless it names its
base.  `init` refuses rows whose seed ranges overlap.
analysis/stash_rows/paper.json holds the paper's rows with their seeds.

Each UNIT is one seed of one row, run as its own
`cpu_tree_bucket_shape_benchmark --seeds 1 --seed-mix --save` process; a
unit's file appears (atomically) only when it is complete, so a stopped run
loses at most the units in flight and `run` picks up where it left off.
Units are ordered seed-major, so the rows stay balanced whenever the run
stops.

Usage (OUT is the run directory):
  run_stash_tail_long.py init OUT --binary B --rows F [--seeds S] [--ops N]
                              [--only L1,L2,...] [--max-seeds M]
  run_stash_tail_long.py run OUT [--jobs J]      # foreground; see `start`
  run_stash_tail_long.py start OUT [--jobs J]    # detached from the terminal
  run_stash_tail_long.py status OUT
  run_stash_tail_long.py report OUT              # pool what is done so far
  run_stash_tail_long.py export OUT DEST         # tail.csv + fits.csv for plots
  run_stash_tail_long.py stop OUT

`init` copies the binary into OUT, so rebuilding the tree does not change a
run in progress, and freezes the plan in OUT/plan.json.  `--seeds` can be
raised later by editing plan.json, and a row's own `"seeds"` there overrides
it for that row (to deepen one row alone); completed units are never rerun.
`--ops` takes an integer or an integral float such as 5e8.  For a short
check, `--only L1,L2` plans every row but marks the others `"active":
false` (their seeds stay as they would be), and `--max-seeds M` caps every
row's seed count, its own included.
"""

import argparse
import fcntl
import json
import os
import shutil
import signal
import subprocess
import sys
import time

# Row r's seeds are its seed_base + i, or SEED_STRIDE * (r + 1) + i without
# one.  With --seed-mix any distinct integers would do; disjoint ranges keep a
# file's seed readable as its row.
SEED_STRIDE = 1_000_000
ROW_KEYS = ("label", "spec", "workload", "seeds", "seed_base", "active", "note")


def die_with_parent():
    # A unit outlives a killed driver otherwise, and the next driver would
    # start it again beside the orphan.
    import ctypes
    PR_SET_PDEATHSIG = 1
    ctypes.CDLL("libc.so.6", use_errno=True).prctl(PR_SET_PDEATHSIG, signal.SIGTERM)


def load_plan(out):
    with open(os.path.join(out, "plan.json")) as f:
        return json.load(f)


def seed_range(plan, r, row):
    """Row r's seeds, as a half-open range [first, end)."""
    first = row.get("seed_base", SEED_STRIDE * (r + 1))
    return first, first + row.get("seeds", plan["seeds"])


def units(plan, inactive=False):
    # A row without a seed_base takes its seeds from its index in
    # plan["rows"], so a row is disabled with `"active": false` rather than
    # deleted; `inactive` still yields its units, for status and report.
    per_row = [seed_range(plan, r, row) for r, row in enumerate(plan["rows"])]
    for i in range(max(end - first for first, end in per_row)):
        for r, row in enumerate(plan["rows"]):
            first, end = per_row[r]
            if first + i >= end or not (inactive or row.get("active", True)):
                continue
            seed = first + i
            path = os.path.join(row["label"], f"seed-{seed}.hist")
            yield row, seed, path


def seed_overlap(plan):
    """None, or a message naming two rows whose seed ranges overlap."""
    spans = sorted(seed_range(plan, r, row) + (row["label"],)
                   for r, row in enumerate(plan["rows"]))
    end, owner = None, None
    for first, last, label in spans:
        if end is not None and first < end:
            return (f"rows {owner} and {label} share seeds from {first}; "
                    "give them disjoint seed_base values")
        if end is None or last > end:
            end, owner = last, label
    return None


def done(out, path):
    return os.path.exists(os.path.join(out, "runs", path))


def count_arg(text):
    """A positive integer, also written as an integral float (5e8)."""
    try:
        value = int(text)
    except ValueError:
        try:
            number = float(text)
        except ValueError:
            raise argparse.ArgumentTypeError(f"not a number: {text!r}")
        if not number.is_integer():
            raise argparse.ArgumentTypeError(f"not an integer: {text!r}")
        value = int(number)
    if value <= 0:
        raise argparse.ArgumentTypeError(f"must be positive: {text!r}")
    return value


def parse_rows(entries, source):
    """The rows file's entries as plan rows ({label, spec, workload, ...})."""
    if not isinstance(entries, list) or not entries:
        sys.exit(f"{source}: expected a non-empty JSON list of rows")
    rows = []
    for n, entry in enumerate(entries):
        where = f"{source}: row {n}"
        if isinstance(entry, list):
            if len(entry) != 3:
                sys.exit(f"{where}: a list row is [label, spec, workload]")
            entry = dict(zip(("label", "spec", "workload"), entry))
        elif not isinstance(entry, dict):
            sys.exit(f"{where}: a row is a [label, spec, workload] list or an object")
        unknown = sorted(set(entry) - set(ROW_KEYS))
        if unknown:
            sys.exit(f"{where}: unknown keys {unknown} (known: {', '.join(ROW_KEYS)})")
        for key in ("label", "spec", "workload"):
            if not isinstance(entry.get(key), str) or not entry[key]:
                sys.exit(f"{where}: `{key}` must be a non-empty string")
        for key, low in (("seeds", 1), ("seed_base", 0)):
            if key in entry and (isinstance(entry[key], bool)
                                 or not isinstance(entry[key], int) or entry[key] < low):
                sys.exit(f"{where}: `{key}` must be an integer >= {low}")
        if "active" in entry and not isinstance(entry["active"], bool):
            sys.exit(f"{where}: `active` must be true or false")
        rows.append({k: entry[k] for k in ROW_KEYS if k in entry})
    labels = [row["label"] for row in rows]
    if len(set(labels)) != len(labels):
        sys.exit(f"{source}: row labels must be unique")
    return rows


def cmd_init(a):
    if os.path.exists(os.path.join(a.out, "plan.json")):
        sys.exit(f"{a.out}/plan.json exists; edit it rather than re-init")
    with open(a.rows) as f:
        rows = parse_rows(json.load(f), a.rows)
    labels = [row["label"] for row in rows]
    if a.only is not None:
        only = [l.strip() for l in a.only.split(",") if l.strip()]
        unknown = [l for l in only if l not in labels]
        if unknown or not only:
            sys.exit(f"--only: no such rows {unknown} in {a.rows}" if unknown
                     else "--only: no row labels given")
        for row in rows:
            # A listed row runs even if the file retired it; the others are
            # planned (their index keeps the seeds of the rows after them).
            row.pop("active", None)
            if row["label"] not in only:
                row["active"] = False
        rows = [{k: row[k] for k in ROW_KEYS if k in row} for row in rows]
    seeds = a.seeds
    if a.max_seeds is not None:
        seeds = min(seeds, a.max_seeds)
        for row in rows:
            if "seeds" in row:
                row["seeds"] = min(row["seeds"], a.max_seeds)
    plan = {"binary": None, "ops": a.ops, "seeds": seeds, "rows": rows}
    clash = seed_overlap(plan)
    if clash:
        sys.exit(f"{a.rows}: {clash}")
    os.makedirs(os.path.join(a.out, "runs"), exist_ok=True)
    os.makedirs(os.path.join(a.out, "logs"), exist_ok=True)
    binary = os.path.join(a.out, "cpu_tree_bucket_shape_benchmark")
    shutil.copy2(a.binary, binary)
    plan["binary"] = binary
    for row in plan["rows"]:
        os.makedirs(os.path.join(a.out, "runs", row["label"]), exist_ok=True)
    with open(os.path.join(a.out, "plan.json"), "w") as f:
        json.dump(plan, f, indent=2)
    n_units = 0
    for r, row in enumerate(rows):
        first, end = seed_range(plan, r, row)
        active = row.get("active", True)
        n_units += (end - first) if active else 0
        print(f"  {row['label']:16s} {end - first:6d} seeds  {first}..{end - 1}"
              + ("" if active else "  (inactive)"))
    print(f"initialized {a.out}: {sum(r.get('active', True) for r in rows)} of "
          f"{len(rows)} rows active, {n_units:,} units x {a.ops:,} ops")


def cmd_run(a):
    out = a.out
    lock = open(os.path.join(out, "driver.lock"), "a+")
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        sys.exit("another driver holds driver.lock; not starting a second one")
    lock.truncate(0)
    lock.write(f"{os.getpid()}\n")
    lock.flush()
    signal.signal(signal.SIGHUP, signal.SIG_IGN)
    stopping = False

    def on_term(signum, frame):
        nonlocal stopping
        stopping = True

    signal.signal(signal.SIGTERM, on_term)
    signal.signal(signal.SIGINT, on_term)

    plan = load_plan(out)
    clash = seed_overlap(plan)
    if clash:
        sys.exit(f"{out}/plan.json: {clash}")
    todo = [u for u in units(plan) if not done(out, u[2])]
    log = open(os.path.join(out, "driver.log"), "a", buffering=1)

    def say(msg):
        log.write(time.strftime("%Y-%m-%d %H:%M:%S ") + msg + "\n")

    say(f"start pid {os.getpid()}: {len(todo)} units to do, {a.jobs} jobs")
    running = {}  # Popen -> (path, started)
    failures = 0
    while (todo or running):
        while not stopping and todo and len(running) < a.jobs:
            row, seed, path = todo.pop(0)
            final = os.path.join(out, "runs", path)
            logf = open(os.path.join(out, "logs", path.replace("/", "_") + ".txt"), "w")
            p = subprocess.Popen(
                [plan["binary"], "--ops", str(plan["ops"]), "--seeds", "1",
                 "--threads", "1", "--seed-base", str(seed), "--seed-mix",
                 "--workload", row["workload"], "--save", final, row["spec"]],
                stdout=logf, stderr=subprocess.STDOUT, preexec_fn=die_with_parent)
            logf.close()
            running[p] = (path, time.time())
        if stopping and running:
            for p in running:
                if p.poll() is None:
                    p.terminate()
        if not running:
            break
        time.sleep(2)
        for p in list(running):
            rc = p.poll()
            if rc is None:
                continue
            path, t0 = running.pop(p)
            if rc == 0 and done(out, path):
                say(f"done {path} in {time.time() - t0:.0f} s")
            elif not stopping:
                failures += 1
                say(f"FAILED {path} (exit {rc}); see logs/")
    left = sum(1 for u in units(plan) if not done(out, u[2]))
    say(f"exit: {left} units left, {failures} failures" +
        (" (stopped by signal)" if stopping else ""))
    sys.exit(1 if failures else 0)


def cmd_start(a):
    me = os.path.abspath(__file__)
    with open(os.path.join(a.out, "driver.out"), "a") as f:
        p = subprocess.Popen(
            [sys.executable, me, "run", a.out, "--jobs", str(a.jobs)],
            stdin=subprocess.DEVNULL, stdout=f, stderr=subprocess.STDOUT,
            start_new_session=True)
    time.sleep(1.5)
    if p.poll() is not None:
        sys.exit(f"driver exited at once (code {p.returncode}); see {a.out}/driver.out")
    print(f"driver pid {p.pid}, detached; `status` to watch, `stop` to stop")


def driver_pid(out):
    try:
        with open(os.path.join(out, "driver.lock")) as f:
            fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
            return None  # the lock was free: nobody is running
    except BlockingIOError:
        with open(os.path.join(out, "driver.lock")) as f:
            return int(f.read().split()[0])
    except FileNotFoundError:
        return None


def cmd_status(a):
    plan = load_plan(a.out)
    total = {r["label"]: 0 for r in plan["rows"]}
    have = dict(total)
    active = {r["label"]: r.get("active", True) for r in plan["rows"]}
    for row, seed, path in units(plan, inactive=True):
        total[row["label"]] += 1
        have[row["label"]] += done(a.out, path)
    for l in total:
        print(f"  {l:16s} {have[l]:4d} / {total[l]} seeds"
              + ("" if active[l] else "  (retired)"))
    n_done = sum(have[l] for l in have if active[l])
    n_all = sum(total[l] for l in total if active[l])
    pid = driver_pid(a.out)
    print(f"  {n_done} / {n_all} units; driver "
          + (f"RUNNING (pid {pid})" if pid else "NOT running"))
    # Throughput over the last 24 completed units.
    times = []
    try:
        with open(os.path.join(a.out, "driver.log")) as f:
            for line in f:
                if " done " in line:
                    times.append(time.mktime(time.strptime(line[:19], "%Y-%m-%d %H:%M:%S")))
    except FileNotFoundError:
        pass
    if pid and len(times) >= 8:
        recent = times[-24:]
        rate = (len(recent) - 1) / max(1.0, recent[-1] - recent[0])
        if rate > 0:
            print(f"  ~{rate * 3600:.0f} units/hour lately; "
                  f"ETA {(n_all - n_done) / rate / 3600:.1f} h")


def cmd_report(a):
    plan = load_plan(a.out)
    files = []
    for row, seed, path in units(plan, inactive=True):
        if done(a.out, path):
            files.append(path)
    if not files:
        sys.exit("no completed units yet")
    report = os.path.join(a.out, "report.txt")
    # Paths relative to runs/ keep the argument list short (the paper's plan
    # has 12,000 units), whatever OUT's own path length.
    binary = plan["binary"]
    if os.sep in binary:
        binary = os.path.abspath(binary)
    with open(report, "w") as f:
        subprocess.run([binary, "--merge", "--detail", "--series", "all"] + files,
                       stdout=f, check=True, cwd=os.path.join(a.out, "runs"))
    print(open(report).read())
    print(f"(written to {report})")


# EXPORT: the pooled tails and fits as CSV, for plotting from a checkout that
# does not have the (gitignored) run directory.  The fit is the benchmark's
# own (cpu_tree_bucket_shape_benchmark.cpp: ChooseWindow, FitTail, Jackknife)
# redone here, and `export` checks it against report.txt before writing.
PHASES = ("fill", "warm", "steady")
SERIES = ("access-pass", "evict-pass", "op-max", "after-op")
TAIL_START, TAIL_MIN = 10, 30  # the benchmark's --tail-start / --tail-min defaults


def read_seed_file(path):
    """{(phase, series): bins}, bins[k] = samples with leftover count exactly k."""
    hists = {}
    with open(path) as f:
        for line in f:
            parts = line.split()
            if not parts or parts[0] != "hist":
                continue
            p, q, samples = int(parts[1]), int(parts[2]), int(parts[3])
            bins = {}
            for kv in parts[5:]:
                k, c = kv.split(":")
                bins[int(k)] = int(c)
            assert sum(bins.values()) == samples, path
            hists[(PHASES[p], SERIES[q])] = bins
    return hists


def tail_of(bins, kmax):
    """t[k] = samples with x >= k, for k = 0..kmax + 1."""
    t = [0] * (kmax + 2)
    for k in range(kmax, -1, -1):
        t[k] = t[k + 1] + bins.get(k, 0)
    return t


def choose_window(bins, tail, samples):
    kmax = len(tail) - 2
    mode = max(range(kmax + 1), key=lambda k: (bins.get(k, 0), -k))
    threshold = samples * 2.0 ** -TAIL_START
    k0 = mode + 1
    while k0 <= kmax and tail[k0] > threshold:
        k0 += 1
    k0 = max(k0, mode + 2)
    k1 = k0
    for k in range(k0, kmax + 1):
        if tail[k] >= TAIL_MIN:
            k1 = k
    if k1 < k0 + 4:
        k0 = k1 = mode + 2
        for k in range(k0, kmax + 1):
            if tail[k] >= TAIL_MIN:
                k1 = k
    return (k0, k1) if k1 >= k0 + 3 else None


def ols(points):
    n = len(points)
    sx = sum(k for k, _ in points)
    sy = sum(y for _, y in points)
    sxx = sum(k * k for k, _ in points)
    sxy = sum(k * y for k, y in points)
    b = (n * sxy - sx * sy) / (n * sxx - sx * sx)
    return (sy - b * sx) / n, b


def fit_tail(tail, samples, window):
    """(intercept, slope, r2, slope_lo, slope_hi): log2 P[x >= k] = a - slope k."""
    import math
    k0, k1 = window
    pts = []
    for k in range(k0, k1 + 1):
        if k >= len(tail) or tail[k] == 0:
            break
        pts.append((k, math.log2(tail[k] / samples)))
    if len(pts) < 4:
        return None
    a, b = ols(pts)
    if b >= 0:
        return None
    mean = sum(y for _, y in pts) / len(pts)
    ss_tot = sum((y - mean) ** 2 for _, y in pts)
    ss_res = sum((y - (a + b * k)) ** 2 for k, y in pts)
    mid = k0 + len(pts) // 2
    lo = [p for p in pts if p[0] <= mid]
    hi = [p for p in pts if p[0] >= mid]
    half = lambda q: -ols(q)[1] if len(q) >= 3 else float("nan")
    return a, -b, 1 - ss_res / ss_tot if ss_tot > 0 else 1.0, half(lo), half(hi)


def k_at(fit, bits):
    return (bits + fit[0]) / fit[1]


def jack_se(values):
    m = len(values)
    mean = sum(values) / m
    return ((m - 1) / m * sum((v - mean) ** 2 for v in values)) ** 0.5


def parse_report_fits(path):
    """{(row label, workload, phase, series): (slope, slope se, k96, k96 se)}."""
    import re
    fits, key = {}, None
    head = re.compile(r"^=== (\S+) \|.*\|\s+(\w+)\s+\|\s+\d+ seeds")
    fitre = re.compile(r"^\s+(fill|warm|steady)\s+(\S+)\s+[\d,]+\s+mode.*fit k \d+\.\.\d+ "
                       r"to 2\^-\d+, ([\d.]+) \+- ([\d.]+)")
    lanes = re.compile(r"2\^-96\s+([\d.]+) \+- ([\d.]+)")
    for line in open(path):
        m = head.match(line)
        if m:
            row = (m.group(1), m.group(2))
            continue
        m = fitre.match(line)
        if m:
            key = row + (m.group(1), m.group(2))
            fits[key] = [float(m.group(3)), float(m.group(4))]
            continue
        m = lanes.search(line)
        if m and key:
            fits[key] += [float(m.group(1)), float(m.group(2))]
            key = None
    return fits


def cmd_export(a):
    import csv
    import math
    plan = load_plan(a.out)
    os.makedirs(a.dest, exist_ok=True)
    report = parse_report_fits(os.path.join(a.out, "report.txt"))
    tail_rows, fit_rows, checked = [], [], 0
    for row in plan["rows"]:
        spec = dict(kv.split("=") for kv in row["spec"].split(","))
        seeds = [read_seed_file(os.path.join(a.out, "runs", path))
                 for r, seed, path in units(plan, inactive=True)
                 if r is row and done(a.out, path)]
        # A row names its capacity as `logn` or as an explicit `n`, which
        # sweeps the load between the powers of two.
        n = int(spec["n"]) if "n" in spec else 1 << int(spec["logn"])
        common = {"row": row["label"], "workload": row["workload"],
                  "log2_n": n.bit_length() - 1 if n & (n - 1) == 0
                            else round(math.log2(n), 4),
                  "n": n,
                  "lambda": int(spec["lam"]), "fold": int(spec.get("fold", 1)),
                  "seeds": len(seeds)}
        for phase in PHASES:
            for series in SERIES:
                per_seed = [s[(phase, series)] for s in seeds]
                # The read path is the only schedule, so the evict-pass
                # series is always empty; it is kept for the --save format.
                if not any(per_seed):
                    continue
                kmax = max(max(b) for b in per_seed if b)
                tails = [tail_of(b, kmax) for b in per_seed]
                n_seed = [t[0] for t in tails]
                pooled_bins = {}
                for b in per_seed:
                    for k, c in b.items():
                        pooled_bins[k] = pooled_bins.get(k, 0) + c
                tail = [sum(t[k] for t in tails) for k in range(kmax + 2)]
                samples = tail[0]
                window = choose_window(pooled_bins, tail, samples)
                # Leave-one-seed-out tails, for every jackknife below.
                loo = [([tail[k] - t[k] for k in range(kmax + 2)], samples - n)
                       for t, n in zip(tails, n_seed)]
                for k in range(1, kmax + 1):
                    y = -math.log2(tail[k] / samples)
                    se = ""
                    if all(lt[k] > 0 for lt, _ in loo):
                        se = f"{jack_se([-math.log2(lt[k] / ln) for lt, ln in loo]):.4f}"
                    prev = -math.log2(tail[k - 1] / samples)
                    tail_rows.append({**common, "phase": phase, "series": series,
                                      "samples": samples, "k": k,
                                      "count_eq_k": pooled_bins.get(k, 0),
                                      "count_ge_k": tail[k],
                                      "neg_log2_p_ge_k": f"{y:.4f}",
                                      "neg_log2_p_se": se,
                                      "local_slope": f"{y - prev:.4f}",
                                      "in_fit_window": int(bool(window) and window[0] <= k <= window[1])})
                # Only the steady phase's fits are reported (and checked);
                # fill and warm keep their tail points.
                fit = fit_tail(tail, samples, window) if window and phase == "steady" else None
                if not fit:
                    continue
                loo_fits = [fit_tail(lt, ln, window) for lt, ln in loo]
                ok = all(loo_fits)
                se = lambda f: f"{jack_se([f(x) for x in loo_fits]):.4f}" if ok else ""
                out = {**common, "phase": phase, "series": series, "samples": samples,
                       "max": kmax, "window_k0": window[0], "window_k1": window[1],
                       "intercept_log2": f"{fit[0]:.6f}", "slope_bits_per_lane": f"{fit[1]:.6f}",
                       "slope_se": se(lambda x: x[1]), "slope_shallow_half": f"{fit[3]:.4f}",
                       "slope_deep_half": f"{fit[4]:.4f}", "r2": f"{fit[2]:.6f}"}
                for bits in (64, 80, 96):
                    out[f"lanes_at_2^-{bits}"] = f"{k_at(fit, bits):.3f}"
                    out[f"lanes_at_2^-{bits}_se"] = se(lambda x: k_at(x, bits))
                fit_rows.append(out)
                # The fit must be the one the report printed.
                key = (spec["label"], row["workload"], phase, series)
                if key in report:
                    want = report[key]
                    got = [fit[1], float(out["slope_se"] or "nan"),
                           k_at(fit, 96), float(out["lanes_at_2^-96_se"] or "nan")]
                    tol = [6e-4, 6e-4, 0.06, 0.06]
                    if not all(abs(g - w) <= t for g, w, t in zip(got, want, tol)):
                        sys.exit(f"export disagrees with report.txt at {key}: {got} vs {want}")
                    checked += 1
    for name, rows in (("tail.csv", tail_rows), ("fits.csv", fit_rows)):
        with open(os.path.join(a.dest, name), "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(rows[0]))
            w.writeheader()
            w.writerows(rows)
    shutil.copy2(os.path.join(a.out, "report.txt"), os.path.join(a.dest, "report.txt"))
    print(f"wrote {len(tail_rows)} tail points and {len(fit_rows)} fits to {a.dest} "
          f"({checked} fits checked against report.txt)")


def cmd_stop(a):
    pid = driver_pid(a.out)
    if not pid:
        sys.exit("no driver running")
    os.kill(pid, signal.SIGTERM)
    print(f"sent SIGTERM to driver {pid}; it stops its units and exits "
          "(in-flight units are lost and rerun on the next `start`)")


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("init")
    p.add_argument("out")
    p.add_argument("--binary", required=True)
    p.add_argument("--seeds", type=count_arg, default=256,
                   help="seeds per row without its own `seeds` (default 256)")
    p.add_argument("--ops", type=count_arg, default=1_000_000_000,
                   help="steady operations per seed, e.g. 500000000 or 5e8")
    p.add_argument("--rows", required=True,
                   help="JSON list of [label, spec, workload] or object rows")
    p.add_argument("--only", metavar="LABELS",
                   help="comma-separated labels to run; the other rows are planned inactive")
    p.add_argument("--max-seeds", type=count_arg, metavar="M",
                   help="cap every row's seeds at M, a row's own `seeds` included")
    for name in ("run", "start"):
        p = sub.add_parser(name)
        p.add_argument("out")
        p.add_argument("--jobs", type=int, default=24)
    for name in ("status", "report", "stop"):
        sub.add_parser(name).add_argument("out")
    p = sub.add_parser("export")
    p.add_argument("out")
    p.add_argument("dest")
    a = ap.parse_args()
    a.out = os.path.abspath(a.out)
    {"init": cmd_init, "run": cmd_run, "start": cmd_start, "status": cmd_status,
     "report": cmd_report, "export": cmd_export, "stop": cmd_stop}[a.cmd](a)


if __name__ == "__main__":
    main()
