"""The comparisons'-share-of-a-merge join (analysis/compare_share.py) on synthetic
benchmark outputs: no measurement."""
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from contextlib import redirect_stdout

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from analysis import compare_share  # noqa: E402

KERNEL = """cpu_byteslice_dedup_kernel_benchmark: ns per 64 x 64 bucket pair, 200000 pairs x 3 reps (VP2INTERSECT compiled: 1)
  key  kernel               min   median      max
  8 B  native              27.0     30.0     31.0
  4 B  native              10.0     10.0     11.0
  8 B  xor-min             80.0     90.0     95.0
  4 B  xor-min             60.0     60.0     61.0
  8 B  self                20.0     25.0     26.0
  4 B  self                 5.0      5.0      6.0
  masks: all kernels agree
"""
COUNT = {"compare_count": "run", "capacity": 4096, "key_bytes": 8, "value_bytes": 8, "accesses": 1000,
         "vp2intersect": True, "pair_q8": 2000, "pair_d4": 0, "self_q8": 40, "self_d4": 0}


def merge(job_nanos, capacity=4096):
    run = {"fit_row": "run", "capacity": capacity, "key_bytes": 8, "value_bytes": 8}
    return "\n".join(["FIT_ROW " + json.dumps(run)] +
                     ["FIT_ROW " + json.dumps({"fit_row": "level", "level": i + 1, "job_nanos": n})
                      for i, n in enumerate(job_nanos)]) + "\n"


class CompareShareTest(unittest.TestCase):
    def run_tool(self, counted, merged):
        with tempfile.TemporaryDirectory() as directory:
            paths = {}
            for name, text in (("counted", counted), ("merge", merged), ("kernel", KERNEL)):
                paths[name] = Path(directory) / name
                paths[name].write_text(text)
            out = io.StringIO()
            with redirect_stdout(out):
                compare_share.main(["--counted", str(paths["counted"]), "--merge", str(paths["merge"]),
                                    "--kernel", str(paths["kernel"]), "--json"])
            return json.loads(out.getvalue())

    def test_prices_counts_by_loop_cost(self):
        report = self.run_tool("COMPARE_COUNT " + json.dumps(COUNT) + "\n", merge([100_000, 200_000]))
        [row] = report["rows"]
        # native: 2000 x 30 + 40 x 25 = 61,000 ns; fallback: 2000 x 90 + 40 x 25 = 181,000 ns
        self.assertAlmostEqual(row["comparison_ms_native"], 0.061)
        self.assertAlmostEqual(row["comparison_ms_fallback"], 0.181)
        self.assertAlmostEqual(row["merge_ms"], 0.3)
        self.assertAlmostEqual(row["fraction_percent"], 100 * 0.061 / 0.3)
        self.assertAlmostEqual(row["comparisons_per_access"], 2.04)
        self.assertAlmostEqual(row["fallback_over_native_comparison"], 181 / 61)
        self.assertIn("L1-resident", report["limits"])

    def test_a_fallback_build_uses_its_own_rows_and_shapes_must_match(self):
        fallback = {**COUNT, "vp2intersect": False}
        [row] = self.run_tool("COMPARE_COUNT " + json.dumps(fallback) + "\n", merge([300_000]))["rows"]
        self.assertAlmostEqual(row["fraction_percent"], 100 * 0.181 / 0.3)
        with self.assertRaises(SystemExit):
            self.run_tool("COMPARE_COUNT " + json.dumps(COUNT) + "\n", merge([1], capacity=8192))


if __name__ == "__main__":
    unittest.main()
