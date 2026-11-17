"""Reducer checks for analysis/occupancy_tail.py (occupancy distributions and empirical
tails from the diagnostic occupancy-observer build) on a synthetic observer JSON."""

from pathlib import Path
import json
import math
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "analysis"))
import occupancy_tail as ot


def structure(kind, level, index, capacity, job_max, per_job=2):
    """Each job exposed the structure `per_job` times: its max and a zero."""
    hist = [0] * (capacity + 1)
    for m in job_max:
        hist[m] += 1
        hist[0] += per_job - 1
    return {"kind": kind, "level": level, "index": index, "capacity": capacity,
            "events": per_job * len(job_max), "max": max(job_max),
            "overflows": 0, "jobs": len(job_max), "hist": hist,
            "job_max": list(job_max)}


def document(structures):
    return {"schema": "occupancy_observer_v1",
            "meta": {"capacity": 1 << 20, "requested_capacity": 1 << 20,
                     "key_bytes": 4, "value_bytes": 8, "branching": 8,
                     "prefix_flushes": 8, "top_digit": 8, "levels": 4,
                     "level_fanouts": [4, 8, 8], "workload": "H",
                     "update_percent": 5, "mode": "synthetic",
                     "settle_accesses": 0, "observed_accesses": 1},
            "structures": structures}


class BinomialTest(unittest.TestCase):
    def test_zero_successes_closed_form(self):
        n = 1000
        self.assertAlmostEqual(ot.clopper_pearson_upper(0, n, 0.95),
                               1 - 0.05 ** (1 / n), places=12)

    def test_cdf_matches_exact_sum(self):
        n, p = 40, 0.13
        for k in (0, 1, 5, 12, 39):
            exact = sum(math.comb(n, i) * p ** i * (1 - p) ** (n - i)
                        for i in range(k + 1))
            self.assertAlmostEqual(ot.binom_cdf(k, n, p), exact, places=10)

    def test_upper_bound_inverts_the_cdf(self):
        for k, n in ((1, 20), (3, 100), (10, 50)):
            pu = ot.clopper_pearson_upper(k, n, 0.95)
            self.assertAlmostEqual(ot.binom_cdf(k, n, pu), 0.05, places=8)
            self.assertGreater(pu, k / n)

    def test_all_successes_is_one(self):
        self.assertEqual(ot.clopper_pearson_upper(7, 7, 0.95), 1.0)


class ReducerTest(unittest.TestCase):
    def test_blocks_drop_partial_tail_and_take_maxima(self):
        self.assertEqual(ot.blocks_of([1, 5, 2, 2, 9, 0, 3], 2), [5, 2, 9])
        self.assertEqual(ot.blocks_of([4], 2), [])

    def test_exceedance_counts(self):
        jobs = [0, 0, 3, 1, 0, 0, 5, 0]          # 8 jobs, blocks of 2
        doc = document([structure("stage_stash", 2, 3, 64, jobs)])
        report = ot.reduce_report(doc, block_jobs=2, confidence=0.95)
        s = report["structures"][0]
        self.assertEqual(s["max"], 5)
        self.assertAlmostEqual(s["max_load_pct"], 100 * 5 / 64)
        self.assertEqual(s["n_blocks"], 4)
        by_k = {r["k"]: r for r in s["exceedance"]}
        # block maxima are [0, 3, 0, 5]
        self.assertEqual(by_k[1]["blocks"], 2)
        self.assertEqual(by_k[3]["blocks"], 2)
        self.assertEqual(by_k[4]["blocks"], 1)
        self.assertEqual(by_k[5]["blocks"], 1)
        self.assertEqual(by_k[6]["blocks"], 0)
        self.assertAlmostEqual(by_k[6]["block_upper"], 1 - 0.05 ** 0.25)
        # exposures: 16 exposures, each job one max and one zero
        self.assertEqual(by_k[0]["exposures"], 16)
        self.assertEqual(by_k[1]["exposures"], 3)
        self.assertEqual(by_k[5]["exposures"], 1)
        self.assertEqual(by_k[6]["exposures"], 0)
        self.assertEqual(s["full_blocks"], 0)
        self.assertEqual(s["overflows"], 0)

    def test_block_bound_is_not_the_exposure_bound(self):
        # Many correlated exposures per job must not tighten the interval.
        jobs = [0] * 100
        s1 = structure("range_leaf", 1, 2, 128, jobs, per_job=1)
        s2 = structure("range_leaf", 1, 2, 128, jobs, per_job=5000)
        r1 = ot.reduce_report(document([s1]), 5)["structures"][0]
        r2 = ot.reduce_report(document([s2]), 5)["structures"][0]
        self.assertEqual(r1["exceedance"][-1]["block_upper"],
                         r2["exceedance"][-1]["block_upper"])

    def test_rejects_other_schema_and_bad_block(self):
        with self.assertRaises(ValueError):
            ot.reduce_report({"schema": "x"})
        with self.assertRaises(ValueError):
            ot.reduce_report(document([]), block_jobs=0)

    def test_text_report_and_json_roundtrip(self):
        doc = document([structure("final_tier", 1, 0, 64, [1, 2, 1, 0] * 4)])
        report = ot.reduce_report(doc, 4)
        text = ot.render_text(report)
        self.assertIn("final_tier", text)
        self.assertIn("zero overflows do not establish 2^-64", text)
        json.dumps(report)


class CertificateTest(unittest.TestCase):
    def cert(self, stash=(1, 1, 1, 1), tier=(1, 1, 1, 1)):
        return {"candidates": [
            {"name": "other", "levels": 5, "prefix_flushes": 8,
             "top_digit": 8, "stash_buckets": [9] * 5,
             "level_tier_buckets": [9] * 5},
            {"name": "L4_r8_D8", "levels": 4, "prefix_flushes": 8,
             "top_digit": 8, "level_fanouts": [4, 8, 8],
             "stash_buckets": list(stash), "level_tier_buckets": list(tier),
             "conditional_lifetime_log2_display": -71.9,
             "status": "unproved_applicability"}]}

    def report(self):
        doc = document([structure("stage_stash", 2, 0, 64, [1, 2]),
                        structure("final_tier", 4, 0, 128, [1, 2]),
                        structure("range_leaf", 1, 2, 128, [1, 2])])
        return ot.reduce_report(doc, 1)

    def test_equal_capacities(self):
        cmp = ot.compare_certificate(self.report(), self.cert(tier=(1, 1, 1, 2)))
        self.assertTrue(cmp["matched"])
        self.assertTrue(cmp["all_capacities_equal"])
        self.assertEqual(cmp["candidate"], "L4_r8_D8")

    def test_mismatch_is_flagged(self):
        cmp = ot.compare_certificate(self.report(), self.cert())
        self.assertFalse(cmp["all_capacities_equal"])

    def test_no_candidate(self):
        report = self.report()
        report["meta"]["levels"] = 9
        self.assertFalse(ot.compare_certificate(report, self.cert())["matched"])


if __name__ == "__main__":
    unittest.main()
