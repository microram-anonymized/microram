"""analysis/crossover_export.py (fixed-N scheme crossovers and the `auto` scheme check)
on synthetic reduce summaries."""
from pathlib import Path
import csv
import json
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "analysis"))
import crossover_export as cx
from oram_bench.codec import ValidationError

N = 1 << 20
H, T = "hierarchical_incremental", "tree"


def group(width, scheme, ops, *, candidate=None, capacity=N, api="scalar", batch=1, alloc=100, rss=200,
          blockers=(), live=1000, requested=None, tid=None):
    candidate = candidate or scheme
    tid = tid or "t-%s-%s-%d-%d-%s" % (candidate, api, width, capacity, batch)
    spec = {"shape": {"key_bytes": 8, "value_bytes": width}, "requested_capacity": capacity, "candidate": candidate,
            "overrides": {"scheme": requested or scheme}, "api_mode": api, "caller_batch_size": batch}
    rep = {"trial_id": tid, "summary": {"drained_ops_per_second": ops},
           "memory": {"trial_peak_rss_bytes": rss}, "logical_bytes": live * (8 + width),
           "library_reserved_bytes": alloc * live * (8 + width), "library_modeled_bytes": None,
           "publication_blockers": list(blockers)}
    return {"group_id": "g-" + tid, "spec": spec, "security": "oblivious", "repetitions": [rep]}


def resolution(groups, capacity_of=None, auto_scheme=None):
    trials, configs = [], {}
    for g in groups:
        rep = g["repetitions"][0]
        scheme = g["spec"]["overrides"]["scheme"]
        if scheme == "auto":
            scheme = (auto_scheme or {})[g["spec"]["shape"]["value_bytes"]]
        cid = "c-" + rep["trial_id"]
        configs[cid] = {"scheme": scheme, "library_threads": 3,
                        "resolved": {"choices": [{"field": "tree.z", "value": 4, "source": "derived", "reason": ""},
                                                 {"field": "hierarchy.fanout", "value": 8, "source": "fallback", "reason": ""},
                                                 {"field": "other.x", "value": 1, "source": "derived", "reason": ""}],
                                     "threads": [{"role": 0, "index": 0, "cpu": None},
                                                 {"role": 4, "index": 0, "cpu": None},
                                                 {"role": 4, "index": 1, "cpu": None}]}}
        actual = (capacity_of or (lambda g: g["spec"]["requested_capacity"]))(g)
        trials.append({"trial_id": rep["trial_id"], "configuration_id": cid, "configuration_key": "key-" + scheme,
                       "same_as": None, "actual_capacity": actual})
    return {"trials": trials, "configurations": configs}


def run(groups, res=True, **kw):
    summary = {"campaign": {"name": "synthetic"}, "groups": groups}
    return cx.build(summary, resolution(groups) if res is True else res, **kw)


def pair(widths, h_ops, t_ops, **kw):
    out = []
    for w, a, b in zip(widths, h_ops, t_ops):
        out += [group(w, H, a, **kw), group(w, T, b, **kw)]
    return out


W = [8, 64, 256, 1024]


def crossing(document, metric, index=0):
    return document["frontiers"][index]["crossovers"][metric]


class CrossoverTest(unittest.TestCase):
    def test_one_clean_crossing(self):
        document, _ = run(pair(W, [9, 8, 4, 2], [3, 4, 5, 6]))
        c = crossing(document, "throughput")
        self.assertEqual(c["status"], "crossing")
        self.assertEqual([b["bracket_bytes"] for b in c["brackets"]], [[64, 256]])
        self.assertEqual((c["brackets"][0]["last_winner_before"], c["brackets"][0]["first_winner_after"]), (H, T))

    def test_no_crossing(self):
        document, _ = run(pair(W, [9, 8, 7, 6], [1, 2, 3, 4]))
        c = crossing(document, "throughput")
        self.assertEqual(c["status"], "no_crossing")
        self.assertIn(H, c["direction"])
        self.assertEqual(c["brackets"], [])

    def test_two_crossings(self):
        document, _ = run(pair(W, [9, 1, 1, 9], [1, 5, 5, 1]))
        c = crossing(document, "throughput")
        self.assertEqual([b["bracket_bytes"] for b in c["brackets"]], [[8, 64], [256, 1024]])

    def test_fastest_setting_per_scheme_is_chosen_and_named(self):
        groups = pair([8], [5], [1]) + [group(8, H, 7, candidate="h-fast", batch=64)]
        document, _ = run(groups)
        cell = document["frontiers"][0]["widths"][0][H]
        self.assertEqual((cell["candidate"], cell["drained_ops_per_second"]), ("h-fast", 7))

    def test_allocation_and_rss_disagree(self):
        groups = []
        for w, (ha, hr, ta, tr) in zip(W[:3], [(1, 10, 5, 5), (1, 10, 5, 5), (9, 10, 5, 5)]):
            groups += [group(w, H, 5, alloc=ha, rss=hr * 1000 * (8 + w)),
                       group(w, T, 5, alloc=ta, rss=tr * 1000 * (8 + w))]
        document, _ = run(groups)
        self.assertEqual(crossing(document, "allocated")["brackets"][0]["bracket_bytes"], [64, 256])
        self.assertEqual(crossing(document, "rss")["status"], "no_crossing")
        self.assertIn(T, crossing(document, "rss")["direction"])
        self.assertEqual(crossing(document, "throughput")["widths_not_compared"], [8, 64, 256])  # ties

    def test_blocked_row_is_kept_and_labelled(self):
        groups = pair(W, [9, 8, 4, 2], [3, 4, 5, 6])
        groups[2] = group(64, H, 8, blockers=("coverage",))
        document, rows = run(groups)
        blocked = [r for r in rows if r["blocked"]]
        self.assertEqual(len(blocked), 1)
        self.assertEqual(blocked[0]["publication_blockers"], ["coverage"])
        self.assertTrue(crossing(document, "throughput")["brackets"][0]["uses_blocked_rows"])
        self.assertTrue(document["frontiers"][0]["widths"][1][H]["blocked"])

    def test_frozen_arm_is_separate(self):
        groups = pair(W, [9, 8, 4, 2], [3, 4, 5, 6]) + [group(8, H, 100, candidate="hierarchy-frozen")]
        document, rows = run(groups)
        frontier = document["frontiers"][0]
        self.assertEqual(len(frontier["frozen_arm"]), 1)
        self.assertEqual(frontier["widths"][0][H]["drained_ops_per_second"], 9)
        self.assertEqual([r["arm"] for r in rows].count("frozen"), 1)
        self.assertFalse([r for r in rows if r["arm"] == "frozen" and r["frontier_winner"]])

    def test_auto_agree_and_disagree(self):
        groups = pair(W[:2], [9, 2], [3, 4])  # hierarchy faster at 8, tree faster at 64
        groups += [group(8, H, 8, candidate="auto", requested="auto"), group(64, H, 3, candidate="auto", requested="auto")]
        document, rows = run(groups, res=resolution(groups, auto_scheme={8: H, 64: H}))
        flags = {c["value_bytes"]: c["flag"] for c in document["frontiers"][0]["auto_check"]["widths"]}
        self.assertEqual(flags, {8: "agree", 64: "disagree"})
        self.assertIn("uncalibrated", document["frontiers"][0]["auto_check"]["note"])
        auto_rows = [r for r in rows if r["arm"] == "auto"]
        self.assertEqual({r["scheme"] for r in auto_rows}, {H})
        self.assertEqual(auto_rows[0]["requested_scheme"], "auto")

    def test_auto_without_resolution_refused(self):
        groups = pair(W[:1], [9], [3]) + [group(8, H, 8, candidate="auto", requested="auto")]
        with self.assertRaises(ValidationError):
            run(groups, res=None)

    def test_capacities_are_separate_frontiers(self):
        groups = pair(W, [9, 8, 4, 2], [3, 4, 5, 6]) + pair(W, [9, 8, 7, 6], [1, 2, 3, 4], capacity=N * 2)
        document, _ = run(groups)
        self.assertEqual([f["requested_capacity"] for f in document["frontiers"]], [N, 2 * N])
        self.assertEqual(crossing(document, "throughput", 0)["status"], "crossing")
        self.assertEqual(crossing(document, "throughput", 1)["status"], "no_crossing")

    def test_refuses_to_mix_capacities(self):
        _, rows = run(pair(W[:2], [9, 8], [3, 4]) + pair(W[:2], [9, 8], [3, 4], capacity=2 * N))
        with self.assertRaises(ValidationError):
            cx.frontier_report(rows, {"a": H, "b": T}, 8, N, "scalar", None)

    def test_refuses_capacity_that_changes_with_width(self):
        groups = pair(W[:2], [9, 8], [3, 4])
        with self.assertRaises(ValidationError):
            run(groups, res=resolution(groups, capacity_of=lambda g: N + g["spec"]["shape"]["value_bytes"]))

    def test_three_schemes_need_explicit_choice(self):
        groups = pair(W[:2], [9, 8], [3, 4]) + [group(8, "hierarchical_synchronous", 1)]
        with self.assertRaises(ValidationError):
            run(groups)
        document, _ = run(groups, schemes=[H, T])
        self.assertEqual(document["ignored_frontier_schemes"], ["hierarchical_synchronous"])

    def test_resolution_fields_and_cli_outputs(self):
        groups = pair(W, [9, 8, 4, 2], [3, 4, 5, 6])
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            (tmp / "s.json").write_text(json.dumps({"campaign": {"name": "x"}, "groups": groups}))
            (tmp / "r.json").write_text(json.dumps(resolution(groups)))
            cx.main(["--summary", str(tmp / "s.json"), "--resolution", str(tmp / "r.json"), "--output", str(tmp / "o")])
            document = json.loads((tmp / "o" / "crossovers.json").read_text())
            row = document["rows"][0]
            self.assertEqual(row["configuration_key"], "key-" + row["scheme"])
            self.assertEqual(row["choices"], {"tree.z": {"value": 4, "source": "derived"},
                                              "hierarchy.fanout": {"value": 8, "source": "fallback"}})
            self.assertEqual(row["worker_role_counts"], {"0": 1, "4": 2})
            self.assertEqual(row["allocated_basis"], "library_reserved_bytes")
            with open(tmp / "o" / "widths.csv") as stream:
                rows = list(csv.DictReader(stream))
            self.assertEqual(len(rows), 8)
            self.assertIn("rss_amplification", rows[0])


if __name__ == "__main__":
    unittest.main()
