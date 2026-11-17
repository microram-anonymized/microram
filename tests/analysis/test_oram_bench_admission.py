"""Admission checks (analysis/oram_bench/admission.py) on saved evidence.

Admission is the single preflight before a trial runs: the host's topology,
memory and declared resources must satisfy the campaign's contract.  Tests use
saved evidence only: no topology discovery, pinning or runs.
"""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest

from analysis.oram_bench.admission import preflight
from analysis.oram_bench.codec import decode, plain
from analysis.oram_bench.planner import expand, write_plan
from analysis.oram_bench.schema import Campaign, Environment
from analysis.oram_bench.topology import capture_topology
from analysis.oram_bench.__main__ import main
from analysis.oram_bench.resolution import entries, read_resolution, resolve_campaign
from analysis.oram_bench.campaign import read_plan
from test_oram_bench_resolution import stub_worker


def configuration():
    return {"schema_version": 1, "name": "topology-fixture", "repetitions": 1,
            "resources": {"physical_cores": 4},
            "execution": {"runtime": "native", "require_protected": False},
            "stages": [{"name": "fixture", "kind": "smoke", "capacities": [128],
                        "shapes": [{"name": "small", "key_bytes": 4, "value_bytes": 8}],
                        "candidates": [{"name": "auto", "overrides": {"scheme": "auto"}}],
                        "api_modes": ["scalar"]}]}


def environment(allowed=None, missing=None):
    files = {}
    cpus = []
    for core, first in enumerate((3, 11, 19, 27, 35, 43)):
        group = "3,7,11,15,19,23" if core < 3 else "27,31,35,39,43,47"
        for cpu in (first, first + 4):
            cpus.append(cpu)
            root = f"/sys/devices/system/cpu/cpu{cpu}"
            for suffix, value in {"topology/physical_package_id": "0", "topology/core_id": str(core),
                                  "topology/thread_siblings_list": f"{first},{first+4}",
                                  "cache/index3/level": "3", "cache/index3/type": "Unified",
                                  "cache/index3/shared_cpu_list": group, "cache/index3/size": "32M"}.items():
                files[root + "/" + suffix] = value
    if missing:
        del files[missing]
    cpus = cpus if allowed is None else allowed
    topology = capture_topology(cpus, lambda path: files.get(str(path)), lambda root: [root / "cache/index3"])
    return plain(Environment(1, "fixture-host", "fixture-boot", "fixture-class", "native", False, None,
                             "synthetic CPU evidence", len(topology.physical_core_slots) if
                             topology.physical_core_slots is not None else None, sorted(cpus),
                             topology.cache_domains, None, "fixture-build", "fixture-source", "fixture-deps",
                             "monotonic", None, ["synthetic_fixture"], topology))


def resolution(roles=(0, 1, 2), slots=(3, 27, 11, 35), scheme="hierarchical_incremental"):
    indices = {}
    threads = []
    for role, cpu in zip(roles, slots):
        index = indices.get(role, 0)
        threads.append({"role": role, "index": index, "cpu": cpu})
        indices[role] = index + 1
    return {"worker_schema_version": 1, "scheme": scheme, "requested_capacity": 128, "actual_capacity": 128,
            "policy_identity": "uncalibrated_fallback_v2", "configuration_key": "fixture-config",
            "supports_direct_initialization": True, "modeled_buffer_bytes": 4096,
            "choices": [{"field": "fixture", "value": "1", "source": "derived", "reason": "fixture"}],
            "library_threads": len(threads), "reserved_harness_cores": 1, "placement_verified": False,
            "threads": threads, "placement_policy": "near_far_v2", "cpu_slots": list(slots)}


class PreflightTests(unittest.TestCase):
    """Environment fixture: six exposed cores in two L3 domains (3,11,19 | 27,35,43)."""

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = Path(self.directory.name)
        import os
        os.environ["STUB_WORKER_LOG"] = str(self.root / "calls.jsonl")
        self.campaign = self.root / "campaign"
        write_plan(expand(decode(Campaign, configuration())), self.campaign)
        resolve_campaign(self.campaign, stub_worker(self.root))
        plan = read_plan(self.campaign)
        self.row = plan["trials"][0]
        self.entry = entries(read_resolution(self.campaign, plan))[self.row["trial_id"]]

    def tearDown(self):
        self.directory.cleanup()

    def check(self, env=None, resolved=None, trial=True):
        env_path = self.root / "environment.json"
        env_path.write_text(json.dumps(env or environment()))
        resolved_path = None
        if trial:
            resolved_path = self.root / "resolved.json"
            value = resolution() if resolved is None else resolved
            value.setdefault("configuration_key", self.entry["configuration_key"])
            if value["configuration_key"] == "fixture-config":
                value["configuration_key"] = self.entry["configuration_key"]
            resolved_path.write_text(json.dumps(value))
        return preflight(self.campaign, env_path, self.row["trial_id"] if trial else None, resolved_path)

    def test_compatible_campaign_and_attempt(self):
        result = self.check()
        self.assertEqual(result["topology"]["status"], "compatible")
        self.assertEqual(result["attempt"]["status"], "compatible", result["attempt"])
        # Memory is unknown until the environment reports a limit.
        self.assertEqual(result["memory"]["status"], "unknown")
        self.assertEqual(result["status"], "insufficient_evidence")
        env = environment(); env["memory_limit_bytes"] = 2**40
        self.assertEqual(self.check(env=env)["status"], "compatible")

    def test_memory_estimates_against_environment(self):
        env = environment(); env["memory_limit_bytes"] = 1024**2
        result = self.check(env=env, trial=False)
        self.assertEqual(result["memory"]["status"], "exceeds_budget")
        self.assertEqual(len(result["memory"]["exceeding"]), 1)
        self.assertEqual(result["status"], "incompatible")

    def test_topology_counts_and_contract(self):
        small = environment(allowed=[3, 7, 11, 15])  # two cores, one domain
        result = self.check(env=small, trial=False)
        self.assertIn("insufficient_exposed_physical_cores", result["topology"]["rejection_reasons"])
        self.assertIn("exposed_cache_domain_count_mismatch", result["topology"]["rejection_reasons"])
        env = environment(); env["runtime"] = "fake"
        self.assertIn("synthetic_environment", self.check(env=env, trial=False)["topology"]["rejection_reasons"])
        env = environment(); env["missing_evidence"].append("topology_contract:cache_domains_2_observed_1")
        self.assertIn("topology_contract:cache_domains_2_observed_1",
                      self.check(env=env, trial=False)["topology"]["missing_evidence"])

    def test_declared_monitor_wait_must_be_exposed(self):
        # A declared monitor-wait instruction reaches the resolver, and run refuses a host without it.
        from analysis.oram_bench.admission import _topology
        from analysis.oram_bench.resolution import resolver_arguments
        resources = {**plain(decode(Campaign, configuration()).resources), "monitor_wait": "umwait"}
        for flags, outcome in ((None, ("missing_evidence", "cpu_flags")),
                               (["monitorx"], ("rejection_reasons", "monitor_wait_not_exposed")),
                               (["waitpkg"], None)):
            with self.subTest(flags=flags):
                result = _topology(resources, decode(Environment, {**environment(), "cpu_flags": flags}))
                if outcome:
                    self.assertIn(outcome[1], result[outcome[0]])
                else:
                    self.assertNotIn("monitor_wait_not_exposed", result["rejection_reasons"])
                    self.assertNotIn("cpu_flags", result["missing_evidence"])
        row = {**self.row, "spec": {**self.row["spec"], "resources": resources}}
        arguments = resolver_arguments(row, False)
        self.assertEqual(arguments[arguments.index("--monitor-wait") + 1], "umwait")
        self.assertNotIn("--monitor-wait", resolver_arguments(self.row, False))

    def test_attempt_configuration_key_and_helper_locality(self):
        other = resolution(); other["configuration_key"] = "another-configuration"
        self.assertIn("configuration_key_differs_from_resolution",
                      self.check(resolved=other)["attempt"]["rejection_reasons"])
        for roles, scheme in (((0, 1, 2), "hierarchical_incremental"), ((0, 5, 6), "tree")):
            crossed = resolution(roles=roles, slots=(3, 11, 27, 35), scheme=scheme)
            self.assertIn("online_helper_outside_caller_l3",
                          self.check(resolved=crossed)["attempt"]["rejection_reasons"])
        env = environment(); env["topology"] = None
        self.assertIn("online_helper_locality", self.check(env=env)["attempt"]["missing_evidence"])
        unplaced = resolution(); unplaced["placement_policy"] = "unplaced"
        unplaced["cpu_slots"] = []; unplaced["threads"] = [dict(t, cpu=None) for t in unplaced["threads"]]
        self.assertIn("requested_near_far_placement_missing",
                      self.check(resolved=unplaced)["attempt"]["rejection_reasons"])

    def test_cli_prints_both_assessments_and_writes_nothing(self):
        before = sorted(p.relative_to(self.campaign) for p in self.campaign.rglob("*"))
        env_path = self.root / "environment.json"
        env = environment(); env["memory_limit_bytes"] = 2**40
        env_path.write_text(json.dumps(env))
        resolved_path = self.root / "resolved.json"
        value = resolution(); value["configuration_key"] = self.entry["configuration_key"]
        resolved_path.write_text(json.dumps(value))
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            code = main(["preflight", "--campaign", str(self.campaign), "--environment", str(env_path),
                         "--trial-id", self.row["trial_id"], "--resolved", str(resolved_path)])
        self.assertEqual(code, 0, output.getvalue())
        result = json.loads(output.getvalue())
        self.assertEqual({result["topology"]["status"], result["attempt"]["status"]}, {"compatible"})
        self.assertEqual(sorted(p.relative_to(self.campaign) for p in self.campaign.rglob("*")), before)
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(main(["preflight", "--campaign", str(self.campaign), "--environment",
                                   str(env_path), "--trial-id", self.row["trial_id"]]), 2)


if __name__ == "__main__":
    unittest.main()
