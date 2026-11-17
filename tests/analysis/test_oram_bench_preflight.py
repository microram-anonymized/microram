"""Injected filesystem/evidence fixtures; no host sampling or worker execution."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from analysis.oram_bench.codec import decode
from analysis.oram_bench.schema import Campaign
from analysis.oram_bench.planner import expand, write_plan
from analysis.oram_bench.campaign import run_campaign
from analysis.oram_bench.preflight import memory_evidence, assess_memory, attempt_preflight
from analysis.oram_bench.campaign import read_plan
from analysis.oram_bench.resolution import entries, read_resolution, resolve_campaign
from analysis.oram_bench.doctor import memory_limit


def files():
    return {"/proc/meminfo": "MemTotal: 1000 kB\nMemAvailable: 800 kB",
            "/proc/self/cgroup": "0::/parent/leaf",
            "/proc/self/mountinfo": "1 2 0:1 / /cg rw - cgroup2 cgroup rw",
            "/cg/parent/leaf/memory.max": "500000", "/cg/parent/leaf/memory.current": "10000",
            "/cg/parent/memory.max": "600000", "/cg/parent/memory.current": "350000",
            "/cg/memory.max": "max", "/cg/memory.current": "400000"}


def configuration():
    return {"schema_version": 1, "name": "preflight-fixture", "repetitions": 1,
        "stages": [{"name": "fixture", "kind": "smoke", "capacities": [128],
            "shapes": [{"name": "small", "key_bytes": 4, "value_bytes": 8}],
            "candidates": [{"name": "auto", "overrides": {"scheme": "auto"}}], "api_modes": ["scalar"]}],
        "timing": {"warmup_ns": 0, "measurement_ns": 1000000, "max_trial_ns": 5000000000,
                   "setup_allowance_ns": 1000000000,
                   "drain_deadline_ns": 1000000000}}


class PreflightTests(unittest.TestCase):
    def test_ancestor_usage_and_headroom(self):
        evidence = memory_evidence(files().get)
        self.assertEqual(evidence["missing_evidence"], [])
        self.assertEqual(memory_limit(evidence), 500000)
        result = assess_memory(evidence, lower_bound_bytes=100000)
        self.assertEqual(result["available_bytes_upper_bound"], 130000)  # .8 * parent limit - parent usage
        self.assertEqual(result["status"], "insufficient_evidence")
        self.assertIn("complete_additional_allocation_peak", result["missing_evidence"])
        self.assertEqual(assess_memory(evidence, lower_bound_bytes=130000, estimated_peak_bytes=130000)["status"],
                         "within_estimated_budget")
        denied = assess_memory(evidence, lower_bound_bytes=130001)
        self.assertEqual(denied["exceeded_scopes"], ["cgroup:/cg/parent"])
        self.assertEqual(denied["status"], "exceeds_budget")

    def test_guest_and_configured_limits_rounding(self):
        evidence = memory_evidence(files().get)
        result = assess_memory(evidence, lower_bound_bytes=1, host_limit_bytes=101)
        self.assertEqual(result["available_bytes_upper_bound"], 80)
        evidence["guest_available_bytes"] = 200000
        self.assertEqual(assess_memory(evidence, lower_bound_bytes=1)["available_bytes_upper_bound"], 0)
        result = assess_memory(evidence, lower_bound_bytes=100000, headroom_ppm=0)
        self.assertEqual(result["available_bytes_upper_bound"], 200000)
        for kwargs in ({"headroom_ppm": -1}, {"headroom_ppm": 1000000}, {"headroom_ppm": True},
                       {"estimated_peak_bytes": 0}, {"host_limit_bytes": 2**64}):
            with self.assertRaises(ValueError):
                assess_memory(evidence, lower_bound_bytes=1, **kwargs)

    def test_unknowns_never_certify_fit(self):
        for absent in ("/proc/meminfo", "/proc/self/cgroup", "/proc/self/mountinfo",
                       "/cg/parent/memory.current", "/cg/parent/memory.max"):
            data = files(); del data[absent]
            result = assess_memory(memory_evidence(data.get), lower_bound_bytes=1, estimated_peak_bytes=1)
            self.assertEqual(result["status"], "insufficient_evidence", absent)
        evidence = memory_evidence(lambda _: None)
        result = assess_memory(evidence, lower_bound_bytes=1)
        self.assertIsNone(result["available_bytes_upper_bound"])
        data = files(); del data["/cg/parent/leaf/memory.current"]
        result = assess_memory(memory_evidence(data.get), lower_bound_bytes=9999999)
        self.assertEqual(result["status"], "exceeds_budget")
        for invalid in ("-1", "junk", "1.0", str(2**64)):
            data = files(); data["/cg/parent/memory.max"] = invalid
            self.assertIn("cgroup_limit:/cg/parent", memory_evidence(data.get)["missing_evidence"])

    def test_hierarchy_root_is_unlimited_and_bounded_by_guest(self):
        # An ordinary host's cgroup-v2 root has no memory.max or memory.current.
        data = files()
        del data["/cg/memory.max"], data["/cg/memory.current"]
        data.update({"/cg/cgroup.controllers": "cpu memory", "/cg/parent/memory.max": "max",
                     "/cg/parent/leaf/memory.max": "max", "/cg/parent/cgroup.type": "domain",
                     "/cg/parent/leaf/cgroup.type": "domain"})
        evidence = memory_evidence(data.get)
        self.assertEqual(evidence["missing_evidence"], [])
        self.assertEqual([(a["path"], a["hierarchy_root"], a["limit_known"]) for a in evidence["ancestors"]],
                         [("/cg/parent/leaf", False, True), ("/cg/parent", False, True), ("/cg", True, True)])
        # Guest MemAvailable bounds the root: 800 KiB less the 20% headroom of 1000 KiB.
        result = assess_memory(evidence, lower_bound_bytes=614400, estimated_peak_bytes=614400)
        self.assertEqual(result["available_bytes_upper_bound"], 614400)
        self.assertEqual(result["status"], "within_estimated_budget")
        denied = assess_memory(evidence, lower_bound_bytes=614401, estimated_peak_bytes=614401)
        self.assertEqual(denied["exceeded_scopes"], ["guest_available"])
        # A cgroup-namespace root (cgroup.type present) hides its ancestors, and a
        # directory that is not a cgroup-v2 group proves nothing.
        for extra, reason in (({"/cg/cgroup.type": "domain"}, "cgroup_ancestors_above_mount"),
                              ({"/cg/cgroup.controllers": None}, "cgroup_limit:/cg")):
            changed = {**data, **extra}
            evidence = memory_evidence(lambda path: changed.get(path))
            self.assertIn(reason, evidence["missing_evidence"])
            self.assertFalse(evidence["ancestors"][-1]["hierarchy_root"])
            result = assess_memory(evidence, lower_bound_bytes=1, estimated_peak_bytes=1)
            self.assertEqual(result["status"], "insufficient_evidence")

    def test_mount_roots_escapes_and_namespace(self):
        data = files()
        data["/proc/self/mountinfo"] = "1 2 0:1 /parent /odd\\040mount rw - cgroup2 cgroup rw"
        data.update({"/odd mount/leaf/memory.max": "100", "/odd mount/leaf/memory.current": "0",
                     "/odd mount/memory.max": "max"})
        evidence = memory_evidence(data.get)
        self.assertEqual(evidence["ancestors"][0]["path"], "/odd mount/leaf")
        self.assertIn("cgroup_ancestors_above_mount", evidence["missing_evidence"])
        data["/proc/self/cgroup"] = "0::/"
        self.assertTrue(memory_evidence(data.get)["cgroup_mount"]["namespace_root_mapping"])
        data["/proc/self/cgroup"] = "0::/other"
        self.assertIn("cgroup_v2_mount_mapping", memory_evidence(data.get)["missing_evidence"])
        for path in ("/../escape", "relative"):
            data["/proc/self/cgroup"] = "0::" + path
            self.assertEqual(memory_evidence(data.get)["ancestors"], [])
        data = files()
        data["/proc/self/mountinfo"] += "\n3 2 0:1 /parent /subset rw - cgroup2 cgroup rw"
        self.assertEqual(memory_evidence(data.get)["cgroup_mount"]["mount_point"], "/cg")

    def test_synthetic_lower_bound_preserves_incomplete_coverage(self):
        with tempfile.TemporaryDirectory() as directory:
            for read_ppm, versions in ((950000, 128 * 8), (1000000, 0)):
                data = configuration(); data["workload"] = {"read_ppm": read_ppm}
                campaign = Path(directory) / str(read_ppm)
                write_plan(expand(decode(Campaign, data)), campaign)
                worker = Path(directory) / "worker"; worker.write_text("never executed")
                resolve_campaign(campaign, worker, synthetic=True)
                plan = read_plan(campaign)
                row = plan["trials"][0]
                entry = entries(read_resolution(campaign, plan))[row["trial_id"]]
                result = attempt_preflight(row, entry, memory_evidence(lambda _: None))
                self.assertEqual(result["components"]["fake_values"], 128 * 8)
                self.assertEqual(result["components"]["verification_versions"], versions)
                self.assertIsNone(result["assessment"]["estimated_peak_bytes"])
                self.assertEqual(result["assessment"]["status"], "insufficient_evidence")

    def test_blocked_launch_persists_evidence_without_attempt(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            campaign = root / "campaign"
            write_plan(expand(decode(Campaign, configuration())), campaign)
            worker, reducer = root / "worker", root / "reducer"
            worker.write_text("never executed"); reducer.write_text("never executed")
            resolve_campaign(campaign, worker, synthetic=True)
            env = {"environment_class": "fixture", "boot_identity": "fixture"}
            evidence = memory_evidence(files().get)
            with patch("analysis.oram_bench.campaign.inspect", return_value=env), \
                 patch("analysis.oram_bench.campaign.memory_evidence", return_value=evidence), \
                 patch("analysis.oram_bench.campaign.subprocess.Popen") as launch:
                result = run_campaign(campaign, reducer, synthetic=True, min_free_bytes=0)
                self.assertEqual(result["launched"], 0)
                self.assertEqual(result["coordinator"]["reason"], "memory_headroom")
                self.assertEqual(result["coordinator"]["assessment"]["status"], "exceeds_budget")
                self.assertEqual(list(campaign.glob("trials/*/attempts/*")), [])
                again = run_campaign(campaign, reducer, synthetic=True, min_free_bytes=0)
                self.assertEqual(again["coordinator"], result["coordinator"])
                launch.assert_not_called()
                # Relaxed resources create fresh evidence, with no worker needed
                # to verify that resume reaches the launch boundary.
                changed = copy.deepcopy(evidence)
                changed["guest_total_bytes"] = changed["guest_available_bytes"] = 2**40
                for ancestor in changed["ancestors"]:
                    ancestor.update(limit_bytes=None, current_bytes=0, limit_known=True)
                with patch("analysis.oram_bench.campaign.memory_evidence", return_value=changed):
                    launch.side_effect = RuntimeError("fixture reached launch")
                    with self.assertRaisesRegex(RuntimeError, "fixture reached launch"):
                        run_campaign(campaign, reducer, synthetic=True, min_free_bytes=0)
                attempt = next(campaign.glob("trials/*/attempts/*"))
                self.assertEqual(json.loads((attempt / "memory_preflight.json").read_text())["evidence"], changed)
                # The attempt's record is the only retained admission record.
                self.assertFalse((campaign / "preflights").exists())


if __name__ == "__main__":
    unittest.main()
