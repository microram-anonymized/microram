"""Checks for analysis/bandwidth_join.py, which joins rebuild fit rows with a streaming-
bandwidth sweep per worker count, on synthetic rows: no measurement."""
import json
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "analysis"))
import bandwidth_join as bj  # noqa: E402


def run_row(owners, rate, helpers=0, capacity=1024):
    return {"fit_row": "run", "capacity": capacity, "key_bytes": 8, "value_bytes": 8,
            "branching": 4, "write_only": True, "read_only": False, "batch": 0,
            "owners": owners, "top_helpers": helpers, "lanes": 1,
            "completed_records_per_s": rate}


def level_row(touch, residual, offer, **extra):
    row = {"fit_row": "level", "touch_lines_per_access": touch,
           "residual_lines_per_access": residual, "offer_lines_per_access": offer}
    row.update(extra)
    return row


def rows_text(prefix=""):
    rows = [dict(run_row(1, 1e6), inline=True), level_row(1.0, 0.5, 0.25, fold_nanos=2e6, job_nanos=5e6),
            level_row(2.0, 0.0, 0.0, fold_nanos=1e6),
            run_row(1, 2e6), level_row(1.0, 0.5, 0.25),
            run_row(3, 3e6), level_row(1.0, 0.0, 0.0)]
    return "\n".join(prefix + json.dumps(r) for r in rows)


SWEEP = """cpu_mem_bandwidth_benchmark: streaming reads, 8 MiB per thread
threads |   GB/s | per thread
      1 |   10.0 |   10.0
      2 |   18.0 |    9.0
"""


class JoinTest(unittest.TestCase):
    def test_both_forms_parse_alike(self):
        a = bj.parse_rebuild(rows_text("FIT_ROW "))
        b = bj.parse_rebuild("noise\n" + rows_text())
        self.assertEqual(a, b)
        self.assertEqual([len(r["levels"]) for r in a], [2, 1, 1])

    def test_inline_flag_from_file_prefix(self):
        runs = bj.parse_rebuild(rows_text(), inline=True)
        self.assertTrue(all(r["inline"] for r in runs))

    def test_bandwidth_forms(self):
        table = bj.parse_bandwidth(SWEEP)
        self.assertEqual(table[2], [18.0])
        jl = bj.parse_bandwidth('{"threads": 4, "gbs": 30.5}\n{"threads": 4, "gbs": 31}')
        self.assertEqual(jl[4], [30.5, 31.0])

    def test_join(self):
        runs = bj.parse_rebuild(rows_text())
        rows = bj.join(runs, bj.parse_bandwidth(SWEEP))
        inline, one, three = rows
        self.assertEqual([r["threads"] for r in rows], [1, 2, 4])
        self.assertAlmostEqual(one["speedup"], 2.0)
        self.assertAlmostEqual(inline["speedup"], 1.0)
        # inline: 64 * (1.75 + 2.0) = 240 B/record at 1e6 records/s = 0.24 GB/s
        self.assertAlmostEqual(inline["bytes_per_record"], 240.0)
        self.assertAlmostEqual(inline["modeled_gbs"], 0.24)
        self.assertAlmostEqual(inline["fraction_of_ceiling"], 0.024)
        self.assertAlmostEqual(inline["ns_per_access"], 1000.0)
        self.assertAlmostEqual(inline["fold_ms"], 3.0)
        self.assertAlmostEqual(inline["job_ms"], 5.0)
        self.assertAlmostEqual(one["modeled_gbs"], 112.0 * 2e6 / 1e9)
        self.assertEqual(one["ceiling_gbs"], 18.0)
        self.assertIsNone(one["null_reason"])

    def test_missing_ceiling(self):
        runs = bj.parse_rebuild(rows_text())
        three = bj.join(runs, bj.parse_bandwidth(SWEEP))[2]
        self.assertIsNone(three["ceiling_gbs"])
        self.assertIsNone(three["fraction_of_ceiling"])
        self.assertIn("no bandwidth point at 4 threads", three["null_reason"])
        self.assertIsNotNone(three["modeled_gbs"])

    def test_no_inline_row_and_no_levels(self):
        rows = bj.join([dict(run_row(1, 1e6), levels=[])], {1: [5.0]})
        self.assertIsNone(rows[0]["speedup"])
        self.assertIsNone(rows[0]["modeled_gbs"])
        self.assertIn("no level rows", rows[0]["null_reason"])

    def test_render_has_note(self):
        rows = bj.join(bj.parse_rebuild(rows_text()), bj.parse_bandwidth(SWEEP))
        self.assertIn("cannot show whether the rebuild is memory- or compute-bound", bj.render(rows))


if __name__ == "__main__":
    unittest.main()
