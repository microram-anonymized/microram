"""The rebuild/access stall bracket and model script (analysis/stall_bracket.py) against a
fake benchmark: no measurement."""
import io
import json
from pathlib import Path
import stat
import sys
import tempfile
import unittest
from contextlib import redirect_stdout

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from analysis import stall_bracket as sb  # noqa: E402

# Rebuild rate 4e6/K records/s (inline: 2e6); the paced run stalls when R < 1.5 * A.
FAKE = """#!/usr/bin/env python3
import json, sys
a = sys.argv[1:]
k = float(a[a.index("--rebuild-slowdown") + 1]) if "--rebuild-slowdown" in a else 1.0
inline = a[a.index("--owners") + 1] == "0"
r = 2e6 if inline else 4e6 / k
rate = float(a[a.index("--rate") + 1]) * 1000 if "--rate" in a else 0
row = {"fit_row": "run", "completed_records_per_s": r if not rate else rate, "backpressure_measured": True,
       "backpressure_requests": 1000 if rate else 0,
       "backpressure_delayed": 10 if rate and r < 1.5 * rate and not inline else 0,
       "backpressure_max_ns": 5000, "backpressure_p99_ns": 2000, "backpressure_total_ns": 9000,
       "response_p99_ns": 3000, "response_max_ns": 6000}
print("FIT_ROW " + json.dumps({"fit_row": "level"}))
print("FIT_ROW " + json.dumps(row))
"""


def pt(ratio, stall):
    return {"ratio": ratio, "stall": stall}


class BracketLogic(unittest.TestCase):
    def test_edges(self):
        b = sb.bracket_of([pt(4, False), pt(2, False), pt(1, True), pt(0.5, True)])
        self.assertEqual((b["status"], b["smallest_stable_ratio"], b["largest_stalling_ratio"]), ("bracketed", 2, 1))
        self.assertEqual(b["crossing_interval"], [1, 2])

    def test_degenerate(self):
        self.assertEqual(sb.bracket_of([])["status"], "no_points")
        b = sb.bracket_of([pt(3, False), pt(2, False)])
        self.assertEqual((b["status"], b["largest_stalling_ratio"]), ("no_stall_anywhere", None))
        b = sb.bracket_of([pt(3, True), pt(2, True)])
        self.assertEqual((b["status"], b["smallest_stable_ratio"]), ("stall_everywhere", None))

    def test_non_monotone(self):
        b = sb.bracket_of([pt(4, True), pt(2, False)])
        self.assertEqual((b["status"], b["crossing_interval"]), ("non_monotone", None))

    @staticmethod
    def synthetic(threshold):
        def measure(k):
            ratio = 8.0 / k
            return {"k": k, "ratio": ratio, "stall": ratio < threshold}
        return measure

    def test_search_bisects_and_stops(self):
        pts = sb.search(self.synthetic(1.5), k_max=64, steps=4)
        ks = [p["k"] for p in pts]
        self.assertEqual(ks[:4], [1.0, 2.0, 4.0, 8.0])  # doubling until K=8 stalls (ratio 1 < 1.5)
        self.assertEqual(len(ks), 4 + 4)                # then exactly `steps` bisections
        b = sb.bracket_of(pts)
        self.assertEqual(b["status"], "bracketed")
        self.assertLess(b["smallest_stable_ratio"] - b["largest_stalling_ratio"], 0.5)
        self.assertEqual(len(sb.search(self.synthetic(1.5), 64, 0)), 4)
        self.assertLess(len(sb.search(self.synthetic(1.5), 64, 50)), 4 + 50)  # tight K bracket stops early

    def test_search_edge_cases(self):
        self.assertEqual(len(sb.search(self.synthetic(0), k_max=8)), 4)      # no stall: 1,2,4,8
        self.assertEqual(len(sb.search(self.synthetic(100), k_max=8)), 1)    # stall at K=1


class FitRowParsing(unittest.TestCase):
    def run_cli(self, *args):
        with tempfile.TemporaryDirectory() as d:
            fake = Path(d) / "bench"
            fake.write_text(FAKE)
            fake.chmod(fake.stat().st_mode | stat.S_IEXEC)
            out = io.StringIO()
            with redirect_stdout(out):
                code = sb.main(["bracket", "--benchmark", str(fake), "--rate-kops", "2000", *args, "--",
                                "--capacity", "16384", "--owners", "1", "--write-only", "--rate", "7"])
            self.assertEqual(code, 0)
            return json.loads(out.getvalue())

    def test_explicit_ks(self):
        r = self.run_cli("--ks", "1,2,4")
        # A = 2e6; R = 4e6/K -> ratios 2, 1, 0.5; stall below 1.5
        self.assertEqual([p["ratio"] for p in r["points"]], [2.0, 1.0, 0.5])
        self.assertEqual([p["stall"] for p in r["points"]], [False, True, True])
        self.assertEqual(r["points"][1]["delayed_pct"], 1.0)
        self.assertEqual(r["points"][1]["max_stall_us"], 5.0)
        self.assertEqual(r["bracket"]["crossing_interval"], [1.0, 2.0])
        self.assertFalse(r["inline_control"]["stall"])
        self.assertEqual(r["inline_control"]["rebuild_rate_per_s"], 2e6)

    def test_auto_search(self):
        r = self.run_cli("--steps", "3")
        self.assertEqual(r["bracket"]["status"], "bracketed")
        self.assertEqual(r["points"][0]["k"], 1.0)

    def test_strip_flag(self):
        self.assertEqual(sb.strip_flag(["--a", "1", "--b", "2", "--c"], "--b"), ["--a", "1", "--c"])


class ModelTable(unittest.TestCase):
    LINE = json.dumps({"requested_capacity": 65536, "actual_capacity": 65536, "B": 4, "D": 4, "r0": 8, "L": 4,
                       "tables": {"mean": 9.6, "max": 12, "min": 6}})

    def test_arithmetic(self):
        [r] = sb.model_rows([json.loads(self.LINE)])
        self.assertAlmostEqual(r["measured_mean_over_log2N"], 0.6)
        self.assertAlmostEqual(r["measured_max_over_log2N"], 0.75)
        self.assertAlmostEqual(r["predicted_mean_tables"], 0.92 * 16)
        self.assertAlmostEqual(r["worst_measured_minus_predicted_over_log2N"], 0.75 - 1.0)

    def test_report_label_and_parse(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "shape.txt"
            p.write_text("probe plan shape: B = 4\n" + self.LINE + "\n")
            out = io.StringIO()
            with redirect_stdout(out):
                sb.main(["model", "--probe", str(p)])
        r = json.loads(out.getvalue())
        self.assertEqual(r["label"], "predictions, not results")
        self.assertEqual([x["B"] for x in r["predictions"]], [2, 4, 8])
        self.assertEqual(r["predictions"][2]["rebuild_speed_x"], 4.5)
        self.assertEqual(len(r["measured_vs_prediction"]), 1)
        self.assertEqual(len(r["deviation_sources"]), 6)


if __name__ == "__main__":
    unittest.main()
