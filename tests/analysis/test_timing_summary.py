"""Synthetic fixture for analysis/timing_summary.py: one agreeing pair and one
pair whose microcode differs."""
import copy
import csv
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "analysis"))
import timing_summary  # noqa: E402


def cls(name, t=0.5, bound=0.001, verdict="certified", kept=99990):
    return {"name": name, "mean_ticks": 100.0, "diff_cycles_per_op": 0.0, "se_cycles_per_op": 0.0001, "t": t,
            "bound_cycles_per_op": bound, "diff_cycles_per_sample": 0.0, "rounds_kept": kept,
            "outliers": 10, "tail_p": 0.5, "verdict": verdict}


def variant(name, status="certified"):
    ref = cls("random", 0, 0, "reference", 0)
    return {"name": name, "key": name.split(".")[0], "role": "ctrl", "form": "lat", "status": status,
            "rounds": 100000, "seconds": 1.0, "ops_per_sample": 128, "ref_cycles_per_op": 5.0,
            "classes": [ref, cls("identity", t=-1.5, bound=0.002), cls("zero", t=0.7, bound=0.003),
                        cls("random#null", t=0.1)]}


def document(microcode="0xaa", seed=1):
    return {"platform": {"vendor": "GenuineIntel", "brand": "Test CPU", "family": 6, "model": 1, "stepping": 1,
                         "microcode": microcode, "kernel": "Linux x", "hypervisor": "KVM", "guest_flags": "none",
                         "cpu": 3},
            "config": {"mode": "certify", "iters": 8, "min_rounds": 100000, "max_rounds": 2000000,
                       "tolerance_cycles_per_op": 0.05, "alpha": 0.001, "seed": seed, "comparisons": 20, "z": 4.0},
            "clock": {"tsc_ghz": 2.0, "tsc_quantum": 1, "ticks_per_cycle_start": 1.0,
                      "ticks_per_cycle_end": 1.0, "sample_overhead_ticks": 10},
            "verdict": "PASS", "skipped": ["vp2intersectq.data.lat (no avx512vp2intersect)"],
            "variants": [variant("vpermb.ctrl.lat"), variant("vpcompressb.mask.lat")]}


class TimingSummaryTest(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.addCleanup(self.dir.cleanup)
        self.root = Path(self.dir.name)

    def write(self, name, doc):
        path = self.root / name
        path.write_text(json.dumps(doc))
        return str(path)

    def test_agreeing_pair(self):
        cert = self.write("c.json", document(seed=1))
        null = self.write("n.json", document(seed=2))
        out_csv, out_md = self.root / "o.csv", self.root / "o.md"
        rc = timing_summary.main(["--target", f"T:cert={cert},null={null},build=abc", "--csv", str(out_csv),
                                  "--markdown", str(out_md)])
        self.assertEqual(rc, 0)
        rows = list(csv.DictReader(open(out_csv)))
        self.assertEqual(len(rows), 3)  # two variants and one unsupported
        by = {r["variant"]: r for r in rows}
        r = by["vpermb.ctrl.lat"]
        self.assertEqual(r["verdict"], "certified")
        self.assertAlmostEqual(float(r["statistic_t_max_abs"]), 1.5)  # null class excluded
        self.assertAlmostEqual(float(r["bound_cycles_per_instruction"]), 0.003)
        self.assertEqual(r["threshold_z"], "4.0")
        self.assertEqual(r["build"], "abc")
        self.assertEqual(r["environment"], "unavailable")
        u = by["vp2intersectq.data.lat"]
        self.assertEqual(u["verdict"], "unsupported")
        self.assertIn("avx512vp2intersect", u["support"])
        md = out_md.read_text()
        self.assertIn("unsupported", md)
        self.assertIn("environment identity (not in the JSON)", md)

    def test_microcode_mismatch_is_an_error(self):
        cert = self.write("c.json", document(microcode="0xaa", seed=1))
        null = self.write("n.json", document(microcode="0xbb", seed=2))
        rc = timing_summary.main(["--target", f"T:cert={cert},null={null}", "--markdown", str(self.root / "o.md")])
        self.assertEqual(rc, 1)
        t = timing_summary.summarize_target("T", {"cert": cert, "null": null})
        self.assertTrue(any("platform.microcode" in e for e in t["errors"]))

    def test_missing_microcode_listed_not_filled(self):
        cert = self.write("c.json", document(microcode="", seed=1))
        t = timing_summary.summarize_target("T", {"cert": cert})
        self.assertEqual(t["identity"]["microcode"], "unavailable")
        self.assertTrue(any("microcode" in m for m in t["missing"]))


if __name__ == "__main__":
    unittest.main()
