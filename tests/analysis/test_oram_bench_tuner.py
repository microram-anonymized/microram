"""The rebuild cost tuner on synthetic fit rows: known constants in, the same constants out."""
import contextlib
import io
import json
import math
from pathlib import Path
import tempfile
import unittest

from analysis.oram_bench.codec import ValidationError
from analysis.oram_bench.tuner import (DEFAULTS, fit, fit_helpers, fit_probe_terms, fit_rebuild_terms,
                                       grid_commands, override_block, parse_rows)
from analysis.oram_bench.__main__ import main


def run_row(capacity, branching, value, buckets, bucket_lines, ns_per_access, parked=0, write_only=False):
    accesses = capacity
    return {"fit_row": "run", "capacity": capacity, "key_bytes": 8, "value_bytes": value, "branching": branching,
            "levels": 6, "bucket_bytes": 1728, "owners": 3, "top_helpers": 0, "lanes": 1,
            "write_only": write_only, "read_only": False, "batch": 0, "offered_kops": 0, "accesses": accesses,
            "seconds": ns_per_access * accesses / 1e9, "requester_waits": 0, "requester_park_nanos": parked,
            "credit_stops": 0, "probe_buckets": buckets, "probe_bucket_lines": bucket_lines,
            "last_probe_buckets": buckets, "model_rate": 1.0, "slice_target_rate": 1.0}


def level_row(capacity, level, levels, lines, jobs, ns, helpers=0, wall=None, lanes=False, value=16, residual=None,
              offers=None):
    row = {"fit_row": "level", "capacity": capacity, "key_bytes": 8, "value_bytes": value, "branching": 8,
           "levels": levels, "bucket_bytes": 1728, "owners": 3, "top_helpers": helpers, "lanes": 8 if lanes else 1,
           "write_only": False, "read_only": False, "batch": 0, "offered_kops": 0, "accesses": capacity,
           "level": level, "group": 0, "in_top_group": level == levels, "takes_lanes": lanes,
           "touch_lines_per_access": lines, "jobs_per_access": jobs, "jobs": 8, "job_nanos": ns * capacity,
           "measured_ns_per_access": ns, "model_ns_per_access": ns}
    if residual is not None:
        row["residual_lines_per_access"] = residual
    if offers is not None:
        row["offer_lines_per_access"] = offers
    if wall is not None:
        row.update(prepare_wall_nanos=wall[0] * 4, prepares=4, finish_wall_nanos=wall[1] * 4, finishes=4)
    return row


def rebuild_rows(line_ns, job_ns, noise=(), residual_ns=None, offer_ns=None):
    """Level rows over two shapes whose features vary independently.

    With `residual_ns` (`offer_ns`), every row also carries residual (offer)
    lines, priced at it.
    """
    rows = []
    features = [(20.0, 0.004, 30.0, 4.0), (40.0, 0.0005, 5.0, 30.0), (60.0, 0.0001, 12.0, 2.0),
                (160.0, 0.00002, 20.0, 10.0), (10.0, 0.01, 50.0, 60.0), (75.0, 0.0002, 3.0, 1.0),
                (30.0, 0.001, 90.0, 15.0), (50.0, 0.002, 8.0, 80.0)]
    for i, (lines, jobs, residual, offers) in enumerate(features):
        ns = lines * line_ns + jobs * job_ns
        ns += residual * residual_ns if residual_ns is not None else 0.0
        ns += offers * offer_ns if offer_ns is not None else 0.0
        ns *= noise[i] if i < len(noise) else 1.0
        rows.append(level_row(1 << 22, i % 6 + 1, 6, lines, jobs, ns,
                              residual=residual if residual_ns is not None else None,
                              offers=offers if offer_ns is not None else None))
    return rows


def terms(result):
    return (result.line_picos, result.residual_line_picos, result.offer_line_picos, result.job_nanos)


class RebuildFitTests(unittest.TestCase):
    def test_recovers_known_constants(self):
        result = fit_rebuild_terms(rebuild_rows(1.4, 9000.0, residual_ns=0.6, offer_ns=1.9))
        self.assertEqual(result.method, "least_squares")
        self.assertEqual(terms(result), (1400, 600, 1900, 9000))
        # No row costs more a line than the fit, so the host's margin sets the slice budget.
        self.assertEqual(result.slice_line_picos, round(1400 * DEFAULTS["slice_line_picos"] / DEFAULTS["line_picos"]))
        self.assertTrue(all(abs(r["ratio"] - 1) < 1e-9 for r in result.residuals))

    def test_coarser_groupings_when_a_column_is_missing(self):
        # Rows printed before the offer column: offers are priced with the residual sweeps.
        result = fit_rebuild_terms(rebuild_rows(1.4, 9000.0, residual_ns=0.6))
        self.assertEqual((terms(result), result.method), ((1400, 600, 600, 9000), "least_squares_residual_as_one"))
        # ... and before the residual columns: one line cost.
        result = fit_rebuild_terms(rebuild_rows(1.4, 9000.0))
        self.assertEqual((terms(result), result.method), ((1400, 1400, 1400, 9000), "least_squares_one_line"))

    def test_non_negative_when_a_term_explains_nothing(self):
        # Offer lines that cost nothing: the active set drops them rather than going negative.
        result = fit_rebuild_terms(rebuild_rows(1.2, 6000.0, residual_ns=0.5, offer_ns=0.0,
                                                noise=(1.0, 1.01, 0.99, 1.0, 1.0, 1.02, 0.98, 1.0)))
        self.assertEqual(result.method, "least_squares")
        self.assertGreaterEqual(result.offer_line_picos, 0)
        self.assertLess(result.offer_line_picos, 60)
        self.assertAlmostEqual(result.line_picos, 1200, delta=40)

    def test_slice_line_is_the_worst_line_cost(self):
        # One line-dominated row slower than the rest by more than the margin: the slice budget takes it.
        margin = DEFAULTS["slice_line_picos"] / DEFAULTS["line_picos"]
        slow = 1.2 * margin
        noisy = rebuild_rows(1.2, 6000.0, noise=(1, 1, 1, slow, 1, 1))
        result = fit_rebuild_terms(noisy)
        line, slice_line = result.line_picos, result.slice_line_picos
        self.assertGreater(slice_line, line * margin)
        self.assertAlmostEqual(slice_line / 1000, 1.2 * slow, delta=0.08)
        # A job-heavy row that is slow says nothing about lines.
        heavy = rebuild_rows(1.2, 6000.0, noise=(1, 1, 1, 1, 1.5, 1))
        result = fit_rebuild_terms(heavy)
        self.assertAlmostEqual(result.slice_line_picos, result.line_picos * margin, delta=2)

    def test_helper_rows_and_waiting_rows_are_excluded(self):
        rows = rebuild_rows(1.0, 5000.0)
        rows.append(level_row(1 << 22, 6, 6, 160.0, 0.00002, 1.0, helpers=3))  # the owner's share only
        self.assertEqual(terms(fit_rebuild_terms(rows)), (1000, 1000, 1000, 5000))

    def test_one_shape_scales_the_defaults(self):
        line, job = DEFAULTS["line_picos"] / 1000, DEFAULTS["job_nanos"]
        rows = [level_row(1 << 22, 1, 6, 10.0, 0.001, 2 * (10.0 * line + 0.001 * job)),
                level_row(1 << 22, 2, 6, 20.0, 0.002, 2 * (20.0 * line + 0.002 * job))]
        result = fit_rebuild_terms(rows)
        doubled = 2 * DEFAULTS["line_picos"]
        self.assertEqual((terms(result), result.method), ((doubled, doubled, doubled, 2 * job), "scaled_defaults"))

    def test_no_usable_rows(self):
        with self.assertRaises(ValidationError):
            fit_rebuild_terms([level_row(1 << 22, 6, 6, 160.0, 0.00002, 1.0, helpers=1)])


class ProbeFitTests(unittest.TestCase):
    def test_envelope_keeps_the_rate_at_or_above_every_measurement(self):
        rows = [run_row(1 << 18, 8, 16, 14, 378, 14 * (18.0 + 0.4 * 27)),
                run_row(1 << 18, 8, 256, 14, 14 * 64, 14 * (18.0 + 0.4 * 64)),
                run_row(1 << 25, 8, 16, 14, 378, 14 * (18.0 + 0.4 * 27) * 1.6),  # DRAM-bound: slower
                run_row(1 << 22, 4, 16, 18, 486, 18 * (18.0 + 0.4 * 27) * 1.1)]
        bucket, line, method, residuals = fit_probe_terms(rows)
        self.assertTrue(method.endswith("+envelope"))
        self.assertTrue(all(r["modelled_rate_over_measured"] >= 1 - 1e-9 for r in residuals))
        # ... and tight: the envelope touches the fastest row rather than undershooting all of them.
        self.assertAlmostEqual(min(r["modelled_rate_over_measured"] for r in residuals), 1.0, places=6)
        # Rows that parked on the rebuild or skipped the probe measure something else.
        waited = run_row(1 << 20, 8, 16, 14, 378, 1.0, parked=10**12)
        writes = run_row(1 << 20, 8, 16, 14, 378, 1.0, write_only=True)
        self.assertEqual(fit_probe_terms(rows + [waited, writes])[:2], (bucket, line))


class HelperFitTests(unittest.TestCase):
    def rows(self, speedups, capacity=1 << 25):
        rows = []
        for m, speedup in speedups.items():
            wall = 1e8 / speedup
            rows.append(level_row(capacity, 6, 6, 160.0, 0.00002, 100.0, helpers=m - 1,
                                  wall=(wall / 2, wall / 2), lanes=True))
        return rows

    def test_speedup_and_cap(self):
        curve = {1: 1.0, 2: 1.55, 4: 2.1, 8: 2.6, 16: 2.61}
        s, cap, report = fit_helpers(self.rows(curve))
        expected = sum((curve[m] - 1) * math.log2(m) for m in (2, 4, 8, 16)) / sum(
            math.log2(m) ** 2 for m in (2, 4, 8, 16))
        self.assertEqual(s, round(expected * 1e6))
        self.assertEqual(cap, 8)  # the 8 -> 16 doubling paid less than 1 %
        self.assertEqual(report[0]["speedup_by_threads"]["16"], 2.61)

    def test_cap_never_extrapolates(self):
        _, cap, _ = fit_helpers(self.rows({1: 1.0, 2: 1.6, 4: 2.2}))
        self.assertEqual(cap, 4)
        self.assertIsNone(fit_helpers(self.rows({2: 1.6, 4: 2.2})))  # no one-thread baseline


class EndToEndTests(unittest.TestCase):
    def test_fit_block_and_cli(self):
        rows = rebuild_rows(1.3, 7000.0, residual_ns=0.7, offer_ns=2.1) + [
            run_row(1 << 18, 8, 16, 14, 378, 14 * (19.0 + 0.5 * 27)),
            run_row(1 << 18, 8, 256, 14, 896, 14 * (19.0 + 0.5 * 64))]
        result = fit(rows)
        self.assertEqual(tuple(result.cost[name] for name in ("line_picos", "residual_line_picos", "offer_line_picos",
                                                              "job_nanos")), (1300, 700, 2100, 7000))
        self.assertEqual(result.cost["middle_burst_ppm"], DEFAULTS["middle_burst_ppm"])
        self.assertIn("helper_speedup_ppm", result.report["not_fitted"])
        block = override_block(result)["incremental"]
        self.assertEqual(sorted(block), sorted("rebuild_cost_" + name for name in result.fitted))
        text = "noise\n" + "".join("FIT_ROW " + json.dumps(row) + "\n" for row in rows) + "MEDIAN RATE\n"
        self.assertEqual(parse_rows(text), rows)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "rows.jsonl"
            path.write_text("".join(json.dumps(row) + "\n" for row in rows))
            output = Path(directory) / "fit.json"
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(main(["fit-rebuild", "--rows", str(path), "--output", str(output)]), 0)
            record = json.loads(output.read_text())
            self.assertEqual(record["override"]["incremental"]["rebuild_cost_line_picos"], 1300)
            self.assertEqual(record["rows"], len(rows))

    def test_grid_commands(self):
        slots = list(range(0, 32, 2))  # 16 physical cores, one sibling each
        commands = grid_commands("/bin/benchmark", "target", core_slots=slots)
        self.assertTrue(all("--fit-rows" in c for c in commands))
        helpers = [c for c in commands if "--top-helpers" in c]
        others = [c for c in commands if "--top-helpers" not in c]
        self.assertTrue(all("--place" in c and "--cpus" not in c for c in others))
        # Capped at the cores the requester and three owners leave, widest included.
        self.assertEqual(sorted({int(c[c.index("--top-helpers") + 1]) for c in helpers}), [0, 1, 3, 7, 12])
        for command in helpers:
            count = int(command[command.index("--top-helpers") + 1])
            threads = 1 + count
            self.assertGreaterEqual(int(command[command.index("--rebuild-lanes") + 1]), 2 * threads)
            # Pinned one thread per physical core, never near/far placed.
            self.assertNotIn("--place", command)
            cpus = [int(cpu) for cpu in command[command.index("--cpus") + 1].split(",")]
            self.assertEqual(cpus, slots[:1 + 3 + count])
        wide = grid_commands("/bin/benchmark", "target", core_slots=list(range(128)))
        wide_helpers = [c for c in wide if "--top-helpers" in c]
        self.assertEqual(max(int(c[c.index("--top-helpers") + 1]) for c in wide_helpers), 31)
        self.assertTrue(all(int(c[c.index("--rebuild-lanes") + 1]) <= 64 for c in wide_helpers))
        small = grid_commands("/bin/benchmark", "target", core_slots=list(range(8)))
        self.assertEqual(sorted({int(c[c.index("--top-helpers") + 1]) for c in small if "--top-helpers" in c}),
                         [0, 1, 3, 4])
        with self.assertRaises(ValidationError):
            grid_commands("/bin/benchmark", "target")  # no core identity for the helper rows
        with self.assertRaises(ValidationError):
            grid_commands("/bin/benchmark", "target", core_slots=[0, 1, 2])
        self.assertNotIn("--place", grid_commands("/bin/benchmark", "quick", place=False)[0])
        with self.assertRaises(ValidationError):
            grid_commands("/bin/benchmark", "nonexistent")


if __name__ == "__main__":
    unittest.main()
