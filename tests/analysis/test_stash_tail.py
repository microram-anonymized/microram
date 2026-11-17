"""Checks for the tree stash-tail tools on synthetic fixtures:
analysis/run_stash_tail_long.py (object rows, seed bases, overlap refusal,
--ops 5e8, --only, --max-seeds, export), analysis/stash_rows/paper.json,
analysis/plot_stash_tail.py (the Appendix A.3/A.4 numbers, Figure 9(b), missing
rows) and analysis/plot_stash_vs_n.py (rows read from the data)."""

from pathlib import Path
import contextlib
import csv
import importlib.util
import io
import json
import math
import os
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "analysis"))
import plot_stash_tail as P  # noqa: E402
import run_stash_tail_long as R  # noqa: E402

RUNNER = ROOT / "analysis" / "run_stash_tail_long.py"
PLOTTER = ROOT / "analysis" / "plot_stash_tail.py"
PAPER_ROWS = ROOT / "analysis" / "stash_rows" / "paper.json"
HAVE_MPL = importlib.util.find_spec("matplotlib") is not None
HAVE_NUMPY = importlib.util.find_spec("numpy") is not None
ENV = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")


def spec(label, lam, fold, logn):
    return (f"z=4,b=2,lam={lam},fold={fold},logn={logn},sched=readpath,plan=inplace,"
            f"preg=1,label={label}")


def read_csv(path):
    with open(path, newline="") as f:
        return list(csv.DictReader(f))


def run(*args, cwd=None):
    return subprocess.run([sys.executable, *map(str, args)], cwd=cwd, env=ENV,
                          capture_output=True, text=True)


def write_hist(path, label, spec_text, workload, seed, bins):
    """A `--save` file whose every phase and series holds `bins` ({k: count})."""
    samples = sum(bins.values())
    body = " ".join(f"{k}:{c}" for k, c in sorted(bins.items()))
    lines = ["cpu_tree_bucket_shape_benchmark seeds v1", f"spec {spec_text}",
             f"workload {workload}", "seed_mix 1",
             f"seed {seed} operations {samples} diverged 0", "note -"]
    for p in range(3):
        for q in range(4):
            lines.append(f"hist {p} {q} 0 0" if q == 1
                         else f"hist {p} {q} {samples} {max(bins)} {body}")
    lines.append("end")
    Path(path).write_text("\n".join(lines) + "\n")


def geometric_bins(samples, slope, kmax, shift=0):
    """Counts with P[x >= k] close to 2^(-slope (k - shift)), k = 0..kmax."""
    tail = [samples if k <= shift else int(samples * 2.0 ** (-slope * (k - shift)))
            for k in range(kmax + 2)]
    tail[kmax + 1] = 0
    return {k: tail[k] - tail[k + 1] for k in range(kmax + 1) if tail[k] > tail[k + 1]}


class RowsAndInitTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self.tmp.name)
        self.binary = self.dir / "fake_binary"
        self.binary.write_text("#!/bin/sh\nexit 0\n")
        self.binary.chmod(0o755)

    def tearDown(self):
        self.tmp.cleanup()

    def init(self, rows, *extra, name="out"):
        rows_file = self.dir / f"{name}.json"
        rows_file.write_text(json.dumps(rows))
        out = self.dir / name
        res = run(RUNNER, "init", out, "--binary", self.binary, "--rows", rows_file, *extra)
        plan = json.loads((out / "plan.json").read_text()) if res.returncode == 0 else None
        return res, plan

    def test_triples_keep_their_index_seeds(self):
        rows = [["a", spec("a", 10, 1, 12), "roundrobin"],
                ["b", spec("b", 13, 1, 15), "uniform"]]
        res, plan = self.init(rows, "--seeds", "3", "--ops", "1000")
        self.assertEqual(res.returncode, 0, res.stderr)
        self.assertEqual(plan["rows"], [{"label": "a", "spec": rows[0][1], "workload": "roundrobin"},
                                        {"label": "b", "spec": rows[1][1], "workload": "uniform"}])
        self.assertEqual(plan["ops"], 1000)
        seeds = [(row["label"], seed) for row, seed, _ in R.units(plan)]
        self.assertEqual(seeds, [("a", 1000000), ("b", 2000000), ("a", 1000001),
                                 ("b", 2000001), ("a", 1000002), ("b", 2000002)])

    def test_object_rows_seed_base_seeds_active(self):
        rows = [{"label": "a", "spec": spec("a", 10, 1, 12), "workload": "roundrobin",
                 "seed_base": 500, "note": "first"},
                {"label": "b", "spec": spec("b", 13, 1, 15), "workload": "roundrobin",
                 "seeds": 4, "seed_base": 7000},
                {"label": "c", "spec": spec("c", 16, 1, 18), "workload": "roundrobin",
                 "active": False},
                ["d", spec("d", 18, 3, 20), "roundrobin"]]
        res, plan = self.init(rows, "--seeds", "2", "--ops", "5e8")
        self.assertEqual(res.returncode, 0, res.stderr)
        self.assertEqual(plan["ops"], 500000000)
        self.assertIsInstance(plan["ops"], int)
        self.assertEqual(plan["rows"][0]["seed_base"], 500)
        self.assertEqual(plan["rows"][0]["note"], "first")
        self.assertEqual(plan["rows"][1]["seeds"], 4)
        self.assertFalse(plan["rows"][2]["active"])
        active = sorted(seed for _, seed, _ in R.units(plan))
        self.assertEqual(active, [500, 501, 7000, 7001, 7002, 7003, 4000000, 4000001])
        everything = {(row["label"], seed) for row, seed, _ in R.units(plan, inactive=True)}
        self.assertIn(("c", 3000000), everything)
        self.assertIn(("c", 3000001), everything)
        paths = {path for _, _, path in R.units(plan)}
        self.assertIn(os.path.join("b", "seed-7003.hist"), paths)
        self.assertTrue((self.dir / "out" / "runs" / "c").is_dir())
        self.assertIn("8 units", res.stdout)

    def test_overlapping_seed_ranges_are_refused(self):
        rows = [{"label": "a", "spec": spec("a", 10, 1, 12), "workload": "roundrobin",
                 "seed_base": 100},
                {"label": "b", "spec": spec("b", 13, 1, 15), "workload": "roundrobin",
                 "seed_base": 150}]
        res, _ = self.init(rows, "--seeds", "100", name="overlap")
        self.assertNotEqual(res.returncode, 0)
        self.assertIn("share seeds", res.stderr)
        self.assertFalse((self.dir / "overlap").exists())
        res, _ = self.init(rows, "--seeds", "50", name="disjoint")
        self.assertEqual(res.returncode, 0, res.stderr)
        # An explicit base can also collide with a later row's index default.
        rows = [{"label": "a", "spec": spec("a", 10, 1, 12), "workload": "roundrobin",
                 "seed_base": 2000000},
                ["b", spec("b", 13, 1, 15), "roundrobin"]]
        res, _ = self.init(rows, "--seeds", "10", name="clash")
        self.assertNotEqual(res.returncode, 0)
        self.assertIn("share seeds", res.stderr)
        # A row's own seed count counts too.
        rows = [{"label": "a", "spec": spec("a", 10, 1, 12), "workload": "roundrobin",
                 "seed_base": 0, "seeds": 11},
                {"label": "b", "spec": spec("b", 13, 1, 15), "workload": "roundrobin",
                 "seed_base": 10}]
        res, _ = self.init(rows, "--seeds", "1", name="ownseeds")
        self.assertNotEqual(res.returncode, 0)

    def test_run_refuses_an_edited_overlapping_plan(self):
        rows = [{"label": "a", "spec": spec("a", 10, 1, 12), "workload": "roundrobin",
                 "seed_base": 0},
                {"label": "b", "spec": spec("b", 13, 1, 15), "workload": "roundrobin",
                 "seed_base": 10}]
        res, plan = self.init(rows, "--seeds", "5")
        self.assertEqual(res.returncode, 0, res.stderr)
        plan["seeds"] = 20
        (self.dir / "out" / "plan.json").write_text(json.dumps(plan))
        res = run(RUNNER, "run", self.dir / "out", "--jobs", "1")
        self.assertNotEqual(res.returncode, 0)
        self.assertIn("share seeds", res.stderr)

    def test_ops_and_seeds_arguments(self):
        rows = [["a", spec("a", 10, 1, 12), "roundrobin"]]
        for i, (ops, want) in enumerate((("5e8", 500000000), ("500000000", 500000000),
                                         ("2E6", 2000000), ("1.5e3", 1500))):
            res, plan = self.init(rows, "--ops", ops, name=f"ops{i}")
            self.assertEqual(res.returncode, 0, res.stderr)
            self.assertEqual(plan["ops"], want)
        for bad in ("1.5", "0", "-5", "abc", "inf", "nan"):
            res, _ = self.init(rows, "--ops", bad, name="bad")
            self.assertNotEqual(res.returncode, 0, bad)
        res, _ = self.init(rows, "--seeds", "0", name="badseeds")
        self.assertNotEqual(res.returncode, 0)

    def test_only_and_max_seeds(self):
        rows = [{"label": "a", "spec": spec("a", 10, 1, 12), "workload": "roundrobin",
                 "seed_base": 10, "active": False},
                {"label": "b", "spec": spec("b", 13, 1, 15), "workload": "roundrobin",
                 "seed_base": 20},
                {"label": "c", "spec": spec("c", 16, 1, 18), "workload": "roundrobin",
                 "seed_base": 30000, "seeds": 3000}]
        res, plan = self.init(rows, "--seeds", "5", "--only", "a, c", "--max-seeds", "2")
        self.assertEqual(res.returncode, 0, res.stderr)
        self.assertNotIn("active", plan["rows"][0])
        self.assertFalse(plan["rows"][1]["active"])
        self.assertNotIn("active", plan["rows"][2])
        self.assertEqual(plan["seeds"], 2)
        self.assertEqual(plan["rows"][2]["seeds"], 2)
        self.assertEqual(sorted(s for _, s, _ in R.units(plan)), [10, 11, 30000, 30001])
        self.assertEqual(list(plan["rows"][1]), ["label", "spec", "workload", "seed_base", "active"])
        res, _ = self.init(rows, "--only", "a,zzz", name="unknown")
        self.assertNotEqual(res.returncode, 0)
        self.assertIn("zzz", res.stderr)

    def test_bad_rows_are_refused(self):
        good = {"label": "a", "spec": spec("a", 10, 1, 12), "workload": "roundrobin"}
        for bad in ([dict(good, seed_bse=3)], [dict(good, seeds=0)], [dict(good, seeds=True)],
                    [dict(good, seed_base=-1)], [dict(good, active="no")],
                    [{"label": "a", "spec": "x"}], [["a", "x"]], [good, dict(good)], [], {}):
            with self.assertRaises(SystemExit, msg=repr(bad)):
                R.parse_rows(bad, "rows.json")

    def test_init_does_not_overwrite_a_plan(self):
        rows = [["a", spec("a", 10, 1, 12), "roundrobin"]]
        res, _ = self.init(rows)
        self.assertEqual(res.returncode, 0, res.stderr)
        res, _ = self.init(rows)
        self.assertNotEqual(res.returncode, 0)
        self.assertIn("exists", res.stderr)


class PaperRowsTest(unittest.TestCase):
    def test_paper_rows(self):
        rows = R.parse_rows(json.loads(PAPER_ROWS.read_text()), str(PAPER_ROWS))
        bases = {r["label"]: r["seed_base"] for r in rows}
        self.assertEqual(bases, {"N21-f1-rr": 1000000, "N21-f4-rr": 4000000, "N21-f5-rr": 5000000,
                                 "N20-f3-rr": 9000000, "N20-f1-rr": 11000000,
                                 "N12-f1-rr": 12000000, "N15-f1-rr": 13000000,
                                 "N18-f1-rr": 14000000, "N24-f1-rr": 15000000,
                                 "N27-f1-rr": 16000000})
        plan = {"seeds": 256, "rows": rows}  # every row carries its own count: --seeds does not matter
        self.assertIsNone(R.seed_overlap(plan))
        self.assertEqual(sum(1 for _ in R.units(plan)), 12000)
        seeds = {r["label"]: r["seeds"] for r in rows}
        self.assertEqual(seeds["N27-f1-rr"], 3000)
        self.assertEqual(sum(seeds.values()), 12000)
        for r in rows:
            kv = dict(x.split("=") for x in r["spec"].split(","))
            self.assertEqual(kv["label"], r["label"])
            self.assertEqual(r["workload"], "roundrobin")
            self.assertEqual(r["label"], f"N{kv['logn']}-f{kv['fold']}-rr")
            self.assertEqual(int(kv["lam"]), int(kv["logn"]) - 2)  # load one half
            self.assertEqual((kv["z"], kv["b"], kv["sched"], kv["plan"]),
                             ("4", "2", "readpath", "inplace"))
            self.assertEqual(kv["preg"], "1" if kv["fold"] != "1" or int(kv["lam"]) < 17 else "2")

    def test_digests_name_the_first_seeds(self):
        rows = json.loads(PAPER_ROWS.read_text())
        lines = (PAPER_ROWS.parent / "paper_hist.sha256").read_text().splitlines()
        want = [f"{r['label']}/seed-{r['seed_base'] + i}.hist" for r in rows for i in range(24)]
        self.assertEqual([l.split()[1] for l in lines], want)
        self.assertTrue(all(len(l.split()[0]) == 64 for l in lines))

    @unittest.skipUnless((PAPER_ROWS.parent / "paper_runs.tar.xz").exists(), "no paper_runs archive")
    def test_paper_runs_archive(self):
        import hashlib
        import tarfile
        rows = json.loads(PAPER_ROWS.read_text())
        digests = dict(reversed(l.split()) for l in
                       (PAPER_ROWS.parent / "paper_hist.sha256").read_text().splitlines())
        names, checked = set(), 0
        with tarfile.open(PAPER_ROWS.parent / "paper_runs.tar.xz") as tar:
            for m in tar:
                self.assertEqual((m.uid, m.gid, m.uname, m.gname, m.mtime), (0, 0, "", "", 0))
                if not m.isfile():
                    continue
                names.add(m.name)
                key = m.name[len("runs/"):]
                if key in digests:
                    data = tar.extractfile(m).read()
                    self.assertEqual(hashlib.sha256(data).hexdigest(), digests[key], key)
                    checked += 1
        want = {f"runs/{r['label']}/seed-{r['seed_base'] + i}.hist"
                for r in rows for i in range(r.get("seeds", 1000))}
        self.assertEqual(names, want)
        self.assertEqual(checked, len(digests))


# The fits of the paper's runs (fits.csv, steady op-max): label -> (log2 N,
# leaf bits, fold, seeds, window, intercept, slope).
PAPER_FITS = {
    "N20-f1-rr": (20, 18, 1, 1000, (10, 37), -2.883486, 0.800230),
    "N21-f1-rr": (21, 19, 1, 1000, (10, 40), -3.695154, 0.753202),
    "N20-f3-rr": (20, 18, 3, 1000, (22, 52), 6.683064, 0.760367),
    "N21-f4-rr": (21, 19, 4, 1000, (36, 69), 14.580368, 0.693386),
    "N21-f5-rr": (21, 19, 5, 1000, (59, 97), 26.310917, 0.608870),
    "N12-f1-rr": (12, 10, 1, 1000, (9, 37), -3.049764, 0.846327),
    "N15-f1-rr": (15, 13, 1, 1000, (9, 35), -2.446319, 0.852391),
    "N18-f1-rr": (18, 16, 1, 1000, (9, 38), -3.168862, 0.791525),
    "N24-f1-rr": (24, 22, 1, 1000, (10, 41), -3.816888, 0.737806),
    "N27-f1-rr": (27, 25, 1, 3000, (10, 52), -6.772831, 0.588827),
}
SWEEP = ("N12-f1-rr", "N15-f1-rr", "N18-f1-rr", "N20-f1-rr", "N21-f1-rr", "N24-f1-rr", "N27-f1-rr")
SAMPLES = 1 << 40


def tail_points(label, kmax=80):
    """{k: count >= k} whose measured stash sizes at lambda 15..30 are the
    paper's Figure 9(b) values for a sweep row, and a plain line otherwise."""
    fit = PAPER_FITS[label]
    if label not in SWEEP:
        return {k: max(1, math.ceil(SAMPLES * 2.0 ** -(fit[6] * k))) for k in range(1, kmax)}
    col = SWEEP.index(label)
    marks = sorted((P.PAPER_FIG9B[lam][col], lam) for lam in P.LAMBDAS)

    def y(k):  # -log2 P[x >= k]: reaches lambda exactly at its paper stash size
        below = [lam for v, lam in marks if v <= k]
        if not below:
            return 15.0 * k / marks[0][0] - 0.01
        return below[-1] + 0.001 * k
    return {k: math.ceil(SAMPLES * 2.0 ** -y(k)) for k in range(1, 45)}


def write_export(dest, labels):
    os.makedirs(dest, exist_ok=True)
    tail_fields = ["row", "workload", "log2_n", "n", "lambda", "fold", "seeds", "phase", "series",
                   "samples", "k", "count_eq_k", "count_ge_k", "neg_log2_p_ge_k", "neg_log2_p_se",
                   "local_slope", "in_fit_window"]
    fit_fields = ["row", "workload", "log2_n", "n", "lambda", "fold", "seeds", "phase", "series",
                  "samples", "max", "window_k0", "window_k1", "intercept_log2",
                  "slope_bits_per_lane", "slope_se", "slope_shallow_half", "slope_deep_half", "r2"]
    with open(os.path.join(dest, "tail.csv"), "w", newline="") as ft, \
            open(os.path.join(dest, "fits.csv"), "w", newline="") as ff:
        wt = csv.DictWriter(ft, fieldnames=tail_fields)
        wf = csv.DictWriter(ff, fieldnames=fit_fields)
        wt.writeheader()
        wf.writeheader()
        for label in labels:
            n, lam, fold, seeds, (k0, k1), a, b = PAPER_FITS[label]
            common = {"row": label, "workload": "roundrobin", "log2_n": n, "n": 1 << n,
                      "lambda": lam, "fold": fold, "seeds": seeds}
            pts = tail_points(label)
            for phase in ("warm", "steady"):  # warm rows must be ignored
                for series in ("access-pass", "op-max"):
                    for k, c in sorted(pts.items()):
                        wt.writerow({**common, "phase": phase, "series": series,
                                     "samples": SAMPLES, "k": k, "count_eq_k": 0,
                                     "count_ge_k": c if series == "op-max" else 1,
                                     "neg_log2_p_ge_k": f"{-math.log2(c / SAMPLES):.4f}",
                                     "neg_log2_p_se": "", "local_slope": "", "in_fit_window": 0})
            for series, shift in (("op-max", 0.0), ("after-op", 50.0)):
                wf.writerow({**common, "phase": "steady", "series": series, "samples": SAMPLES,
                             "max": max(pts), "window_k0": k0, "window_k1": k1,
                             "intercept_log2": f"{a + shift:.6f}",
                             "slope_bits_per_lane": f"{b:.6f}", "slope_se": "0.01",
                             "slope_shallow_half": "0", "slope_deep_half": "0", "r2": "0.999"})


class StashTailSummaryTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    def summary(self, labels, *argv):
        export = self.dir / "export"
        write_export(export, labels)
        out = io.StringIO()
        code = 0
        with contextlib.redirect_stdout(out):
            try:
                P.main([str(export), "--no-figure", *argv])
            except SystemExit as e:
                code = e.code
        s = json.loads((export / "stash_tail_summary.json").read_text())
        return s, code, (export / "stash_tail_summary.txt").read_text()

    def claim(self, s, cid):
        return next(c for c in s["claims"] if c["id"] == cid)

    def test_formulas(self):
        fits = {"intercept_log2": "14.580368", "slope_bits_per_lane": "0.693386"}
        self.assertAlmostEqual(P.k_at(fits, 95), (95 + 14.580368) / 0.693386)
        self.assertAlmostEqual(P.line_at(fits, 192), 14.580368 - 0.693386 * 192)
        self.assertEqual(P.registers_for(127.0), 2)
        self.assertEqual(P.registers_for(127.5), 3)
        self.assertEqual(P.registers_for(158.04), 3)
        self.assertEqual(P.registers_for(199.24), 4)
        self.assertEqual([P.default_registers(f, l) for f, l in
                          ((1, 10), (4, 19), (5, 19), (3, 18), (1, 22), (1, 23), (1, 25))],
                         [3, 3, 4, 3, 3, 4, 4])
        self.assertEqual([P.default_fold(l) for l in (10, 16, 17, 18, 19, 20, 21, 25)],
                         [1, 1, 2, 3, 4, 5, 1, 1])

    def test_stash_needed(self):
        row = {"samples": 1024, "points": {1: (512, 1.0), 2: (64, 4.0), 3: (2, 9.0), 4: (1, 10.0)}}
        self.assertEqual(P.stash_needed(row, 1), 1)
        self.assertEqual(P.stash_needed(row, 3), 2)
        self.assertEqual(P.stash_needed(row, 4), 2)
        self.assertEqual(P.stash_needed(row, 9), 3)
        self.assertEqual(P.stash_needed(row, 10), 4)
        self.assertIsNone(P.stash_needed(row, 11))  # 1024 samples cannot resolve 2^-11

    def test_every_paper_number(self):
        s, code, text = self.summary(list(PAPER_FITS), "--check-paper")
        self.assertEqual(code, 0, text)
        self.assertTrue(s["agrees_with_paper"], text)
        self.assertEqual(s["missing"], [])
        rows = s["rows"]
        self.assertAlmostEqual(rows["N20-f3-rr"]["k_at_target"], 133.73, places=2)
        self.assertAlmostEqual(rows["N21-f4-rr"]["k_at_target"], 158.04, places=2)
        self.assertAlmostEqual(rows["N21-f1-rr"]["k_at_target"], 121.22, places=2)
        self.assertAlmostEqual(rows["N21-f5-rr"]["k_at_target"], 199.24, places=2)
        self.assertAlmostEqual(rows["N21-f4-rr"]["log2_p_at_64A"], -118.55, places=2)
        self.assertAlmostEqual(rows["N21-f4-rr"]["log2_p_at_64A_minus_1"], -117.86, places=2)
        self.assertAlmostEqual(rows["N21-f4-rr"]["log2_p_at_64A_per_2^31_accesses"], -87.55, places=2)
        self.assertAlmostEqual(rows["N20-f3-rr"]["log2_p_at_64A"], -139.31, places=2)
        self.assertEqual(rows["N27-f1-rr"]["default_registers"], 4)
        self.assertAlmostEqual(rows["N27-f1-rr"]["log2_p_at_64A"], -6.772831 - 0.588827 * 256, places=6)
        self.assertEqual(s["n_sweep_worst"]["log2_p_at_64A_minus_1"]["row"], "N24-f1-rr")
        self.assertAlmostEqual(s["n_sweep_worst"]["log2_p_at_64A_minus_1"]["value"], -144.74, places=2)
        self.assertAlmostEqual(s["n_sweep_worst"]["log2_p_at_64A"]["value"], -145.48, places=2)
        self.assertEqual(s["merging_at_2^21"]["0"]["registers"], 2)
        self.assertEqual(s["merging_at_2^21"]["3"]["registers"], 3)
        self.assertEqual(s["merging_at_2^21"]["4"]["registers"], 4)
        self.assertEqual(s["other_trees_worst"]["library default fold"]["row"], "N20-f3-rr")
        f9 = s["figure_9b"]
        self.assertEqual(f9["log2_n"], [12, 15, 18, 20, 21, 24, 27])
        for lam in P.LAMBDAS:
            self.assertEqual(f9["stash"][str(lam)], list(P.PAPER_FIG9B[lam]))
        self.assertEqual(f9["seeds"][-1], 3000)
        self.assertIn("All paper numbers present and agreeing.", text)
        self.assertIn("0.76 bits per record", text)

    def test_missing_rows_are_tolerated(self):
        labels = [l for l in PAPER_FITS if l not in ("N21-f5-rr", "N27-f1-rr", "N20-f1-rr")]
        s, code, text = self.summary(labels)
        self.assertEqual(code, 0)
        self.assertFalse(s["agrees_with_paper"])
        self.assertEqual(self.claim(s, "A.3 k at 2^-95 2^21 merged 4")["status"], "missing")
        self.assertEqual(self.claim(s, "A.3 slope 2^21, merge 3 levels")["status"], "agrees")
        self.assertEqual(self.claim(s, "A.3 N sweep worst at 64A-1")["status"], "incomplete")
        self.assertEqual(self.claim(s, "Fig 9(b) 2^-30 2^27")["status"], "missing")
        self.assertEqual(self.claim(s, "Fig 9(b) 2^-30 2^24")["status"], "agrees")
        self.assertEqual(s["figure_9b"]["log2_n"], [12, 15, 18, 21, 24])
        self.assertIn("missing", text)
        _, code, _ = self.summary(labels, "--check-paper")
        self.assertEqual(code, 1)

    def test_unfitted_and_unreached(self):
        export = self.dir / "export"
        write_export(export, ["N21-f4-rr", "N12-f1-rr"])
        # Drop N12's fit and cut its tail before 2^-30.
        rows = [r for r in read_csv(export / "fits.csv") if r["row"] != "N12-f1-rr"]
        with open(export / "fits.csv", "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(rows[0]))
            w.writeheader()
            w.writerows(rows)
        tail = [r for r in read_csv(export / "tail.csv")
                if r["row"] != "N12-f1-rr" or int(r["k"]) < 30]
        with open(export / "tail.csv", "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(tail[0]))
            w.writeheader()
            w.writerows(tail)
        rows, fits = P.load(export)
        s = P.summarize(rows, fits)
        self.assertEqual(s["unfitted_rows"], ["N12-f1-rr"])
        self.assertFalse(s["rows"]["N12-f1-rr"]["fitted"])
        self.assertEqual(s["figure_9b"]["stash"]["25"], [26])
        self.assertEqual(s["figure_9b"]["stash"]["30"], [None])
        self.assertIn("tail too short to fit", P.render_text(s, "x"))

    def test_target_and_lambdas(self):
        s, code, _ = self.summary(list(PAPER_FITS), "--target-bits", "96", "--lambdas", "15,22",
                                  "--check-paper")
        self.assertAlmostEqual(s["rows"]["N21-f4-rr"]["k_at_target"], (96 + 14.580368) / 0.693386)
        self.assertEqual(self.claim(s, "A.3 k at 2^-96 2^21, merge 3 levels")["status"], "not compared")
        self.assertEqual(s["figure_9b"]["lambdas"], [15, 22])
        self.assertEqual(s["figure_9b"]["paper"], {"15": [15, 15, 15, 15, 15, 16, 16]})
        self.assertEqual(code, 0)  # every number that has a paper value still agrees
        with contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit):
                P.main([str(self.dir / "export"), "--lambdas", "x"])

    def test_rows_found_by_geometry_not_label(self):
        export = self.dir / "export"
        write_export(export, list(PAPER_FITS))
        for name in ("tail.csv", "fits.csv"):
            text = (export / name).read_text().replace("N21-f4-rr", "big-tree")
            (export / name).write_text(text)
        rows, fits = P.load(export)
        s = P.summarize(rows, fits)
        self.assertTrue(s["agrees_with_paper"])
        self.assertEqual(self.claim(s, "A.3 slope 2^21, merge 3 levels")["row"], "big-tree")

    @unittest.skipUnless(HAVE_MPL, "matplotlib not installed")
    def test_figure(self):
        export = self.dir / "export"
        write_export(export, ["N20-f3-rr", "N21-f4-rr", "N12-f1-rr", "N15-f1-rr"])
        res = subprocess.run([sys.executable, str(PLOTTER), str(export), "--out",
                              str(self.dir / "fig")], capture_output=True, text=True,
                             env=dict(ENV, MPLCONFIGDIR=str(self.dir / "mpl")))
        self.assertEqual(res.returncode, 0, res.stderr)
        for name in ("tree_stash_tail.pdf", "tree_stash_tail.png", "stash_tail_summary.txt",
                     "stash_tail_summary.json"):
            self.assertGreater((self.dir / "fig" / name).stat().st_size, 0, name)
        self.assertFalse((export / "stash_tail_summary.json").exists())


class ExportWithSeedBaseTest(unittest.TestCase):
    """init -> synthetic .hist files under seed_base seeds -> export -> summary."""

    def test_export_reads_seed_base_units(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            binary = tmp / "fake_binary"
            binary.write_text("#!/bin/sh\nexit 0\n")
            rows = [{"label": "N21-f4-rr", "spec": spec("N21-f4-rr", 19, 4, 21),
                     "workload": "roundrobin", "seed_base": 4000000},
                    {"label": "N12-f1-rr", "spec": spec("N12-f1-rr", 10, 1, 12),
                     "workload": "roundrobin", "seed_base": 12000000, "seeds": 3},
                    {"label": "N15-f1-rr", "spec": spec("N15-f1-rr", 13, 1, 15),
                     "workload": "roundrobin", "seed_base": 13000000}]
            (tmp / "rows.json").write_text(json.dumps(rows))
            out = tmp / "out"
            res = run(RUNNER, "init", out, "--binary", binary, "--rows", tmp / "rows.json",
                      "--seeds", "2", "--ops", "1e6")
            self.assertEqual(res.returncode, 0, res.stderr)
            plan = json.loads((out / "plan.json").read_text())
            for row, seed, path in R.units(plan):
                slope = 0.7 if row["label"] == "N21-f4-rr" else 0.85
                shift = 30 if row["label"] == "N21-f4-rr" else 0
                write_hist(out / "runs" / path, row["label"], row["spec"], row["workload"],
                           seed, geometric_bins(1 << 22, slope, 60, shift + seed % 2))
            # A stray file outside the plan's seeds must not be read.
            write_hist(out / "runs" / "N15-f1-rr" / "seed-5.hist", "N15-f1-rr",
                       rows[2]["spec"], "roundrobin", 5, {0: 10, 90: 10})
            (out / "report.txt").write_text("")
            res = run(RUNNER, "export", out, tmp / "export")
            self.assertEqual(res.returncode, 0, res.stderr)
            fits = {r["row"]: r for r in read_csv(tmp / "export" / "fits.csv")
                    if r["phase"] == "steady" and r["series"] == "op-max"}
            self.assertEqual(fits["N12-f1-rr"]["seeds"], "3")
            self.assertEqual(fits["N15-f1-rr"]["seeds"], "2")
            self.assertLess(int(fits["N15-f1-rr"]["max"]), 90)
            self.assertAlmostEqual(float(fits["N12-f1-rr"]["slope_bits_per_lane"]), 0.85, delta=0.02)
            r, f = P.load(tmp / "export")
            s = P.summarize(r, f)
            k = s["rows"]["N21-f4-rr"]["k_at_target"]
            want = (95 + float(fits["N21-f4-rr"]["intercept_log2"])) / float(
                fits["N21-f4-rr"]["slope_bits_per_lane"])
            self.assertAlmostEqual(k, want, places=9)
            self.assertEqual(s["figure_9b"]["log2_n"], [12, 15])


@unittest.skipUnless(HAVE_MPL and HAVE_NUMPY, "matplotlib and numpy not installed")
class StashVsNTest(unittest.TestCase):
    def test_rows_from_headers_and_missing_rows(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            runs = tmp / "run" / "runs"
            for label, lam, fold, logn, workload, seeds in (
                    ("small", 10, 1, 12, "roundrobin", 3), ("folded", 18, 3, 20, "roundrobin", 2),
                    ("uni", 13, 1, 15, "uniform", 2), ("empty", 16, 1, 18, "roundrobin", 0),
                    ("big", 19, 1, 21, "roundrobin", 2)):
                (runs / label).mkdir(parents=True)
                for i in range(seeds):
                    write_hist(runs / label / f"seed-{i}.hist", label, spec(label, lam, fold, logn),
                               workload, i, geometric_bins(1 << 16, 0.8, 30, i))
            dest = tmp / "dest"
            res = subprocess.run([sys.executable, str(ROOT / "analysis" / "plot_stash_vs_n.py"),
                                  str(dest), "--runs", str(tmp / "run"), "--lambdas", "5,10,20"],
                                 capture_output=True, text=True,
                                 env=dict(ENV, MPLCONFIGDIR=str(tmp / "mpl")))
            self.assertEqual(res.returncode, 0, res.stderr)
            rows = read_csv(dest / "stash_vs_n.csv")
            self.assertEqual(sorted({(r["row"], r["log2_n"]) for r in rows}),
                             [("big", "21"), ("small", "12")])
            # 2^16 samples per seed cannot resolve 2^-20.
            self.assertEqual(sorted({r["lambda"] for r in rows}), ["10", "5"])
            self.assertTrue((dest / "stash_vs_n.png").exists())
            self.assertIn("skipping the extrapolated plot", res.stdout)


if __name__ == "__main__":
    unittest.main()
