"""The resolve step (analysis/oram_bench/resolution.py) against a stub worker.

Resolution asks the built worker (its C++ resolver) for each planned row's
concrete configuration and memory estimate, and freezes the result with the
worker's build identity into the campaign.  No ORAM is built and no clock is read.
"""
import json
import os
from pathlib import Path
import stat
import sys
import tempfile
import unittest
from unittest.mock import patch

from analysis.oram_bench.campaign import read_plan, status
from analysis.oram_bench.codec import ValidationError, decode
from analysis.oram_bench.planner import expand, write_plan
from analysis.oram_bench.resolution import (entries, executed_trial, library_bytes, read_resolution,
                                            resolve_campaign, trial_arguments)
from analysis.oram_bench.schema import Campaign
from analysis.oram_bench.tee import assess_tee

STUB = r'''#!PYTHON
"""Answers --resolve-only like the C++ worker: auto selects the pinned hierarchy."""
import json, os, sys
args = sys.argv[1:]
if args == ["--build-info"]:
    # A worker without side files exits nonzero, as workers before --build-info do.
    if "STUB_SIDE_FILES" not in os.environ:
        sys.exit(2)
    print(json.dumps({"build_info_schema_version": 1, "baseline": "stub",
                      "side_files": os.environ["STUB_SIDE_FILES"].split(",")}))
    sys.exit(0)
values = dict(zip(args[::2], args[1::2]))
with open(os.environ["STUB_WORKER_LOG"], "a") as log:
    log.write(json.dumps(args) + "\n")
if values.get("--prepare-planner") == "1":
    import resource, time
    capacity = int(values["--capacity"])
    if int(os.environ.get("STUB_PREPARE_FAIL_AT", 0) or 2**64) <= capacity:
        sys.stderr.write("terminate called after throwing an instance of 'std::bad_alloc'\n")
        sys.exit(134)
    time.sleep(float(os.environ.get("STUB_PREPARE_SLEEP", 0)))
    print(json.dumps({"prepared": "stub", "planner_ns": capacity, "planner_cache_sha256": "00",
                      "stub_rlimit_as": resource.getrlimit(resource.RLIMIT_AS)[0]}))
    sys.exit(0)
if values.get("--override.incremental.owner_threads") == "99":
    sys.stderr.write("configuration: owners and batch helpers exceed core budget\n")
    sys.exit(2)
scheme = values["--scheme"]
selected = "hierarchical_incremental" if scheme == "auto" else scheme
capacity = int(values["--capacity"])
overrides = sorted((k, v) for k, v in values.items() if k.startswith("--override."))
print(json.dumps({"worker_schema_version": 2, "scheme": selected, "requested_capacity": capacity,
    "actual_capacity": capacity, "policy_identity": "uncalibrated_fallback_v2",
    "configuration_key": json.dumps([selected, capacity, values["--value-bytes"], values["--cores"], overrides]),
    "supports_direct_initialization": True, "modeled_buffer_bytes": capacity * 100,
    "choices": [{"field": "scheme", "value": selected, "source": "fallback", "reason": "stub"}],
    "library_threads": 1, "reserved_harness_cores": 1, "placement_verified": False,
    "threads": [{"role": 0, "index": 0, "cpu": None}], "placement_policy": "unplaced", "cpu_slots": []}))
'''


def stub_worker(directory):
    path = Path(directory) / "stub-worker"
    path.write_text(STUB.replace("PYTHON", sys.executable, 1))
    path.chmod(path.stat().st_mode | stat.S_IXUSR)
    return path


def configuration(candidates=None, resources=None, repetitions=2):
    return {"schema_version": 1, "name": "resolve-fixture", "repetitions": repetitions,
            "resources": {"physical_cores": 4, **(resources or {})},
            "stages": [{"name": "fixture", "kind": "smoke", "capacities": [128],
                        "shapes": [{"name": "small", "key_bytes": 4, "value_bytes": 8}],
                        "candidates": candidates or [
                            {"name": "auto", "overrides": {"scheme": "auto"}},
                            {"name": "pinned", "overrides": {"scheme": "hierarchical_incremental"}}],
                        "api_modes": ["scalar"]}]}


class ResolveTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = Path(self.directory.name)
        self.worker = stub_worker(self.root)
        self.log = self.root / "calls.jsonl"
        os.environ["STUB_WORKER_LOG"] = str(self.log)

    def tearDown(self):
        self.directory.cleanup()

    def campaign(self, data=None, name="campaign"):
        path = self.root / name
        write_plan(expand(decode(Campaign, data or configuration())), path)
        return path

    def calls(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()] if self.log.exists() else []

    def test_auto_duplicate_of_pinned_is_same_as_and_resolved_once_per_configuration(self):
        campaign = self.campaign()
        summary = resolve_campaign(campaign, self.worker)
        # Two candidates x two repetitions, but only two distinct resolver inputs.
        self.assertEqual(len(self.calls()), 2)
        self.assertEqual(summary["status_counts"], {"runnable": 2, "same_as": 2})
        plan = read_plan(campaign)
        resolved = entries(read_resolution(campaign, plan))
        rows = {row["trial_id"]: row for row in plan["trials"]}
        for duplicate in summary["same_as"]:
            original = rows[duplicate["same_as"]]
            copy_row = rows[duplicate["trial_id"]]
            self.assertNotEqual(original["spec"]["candidate"], copy_row["spec"]["candidate"])
            self.assertEqual(original["spec"]["repetition"], copy_row["spec"]["repetition"])
            self.assertEqual(executed_trial(resolved, duplicate["trial_id"]), duplicate["same_as"])
            self.assertEqual(resolved[duplicate["same_as"]]["status"], "runnable")
        self.assertEqual(status(campaign)["counts"], {"pending": 2, "same_as": 2})

    def test_distinct_configurations_are_not_duplicates(self):
        candidates = [{"name": "auto", "overrides": {"scheme": "auto"}},
                      {"name": "tree", "overrides": {"scheme": "tree"}}]
        summary = resolve_campaign(self.campaign(configuration(candidates)), self.worker)
        self.assertEqual(summary["status_counts"], {"runnable": 4})

    def test_memory_limits_skip_with_reasons(self):
        # 128 entries x 100 modelled bytes = 12,800 library bytes in the stub.
        data = configuration(resources={"library_memory_limit_bytes": 12_799})
        summary = resolve_campaign(self.campaign(data), self.worker)
        self.assertEqual(summary["skip_reasons"], {"modeled_library_bytes_exceed_library_memory_limit": 4})
        data = configuration(resources={"host_memory_limit_bytes": 1024**2})  # below the 64 MiB event ring
        summary = resolve_campaign(self.campaign(data, "host"), self.worker)
        self.assertEqual(summary["skip_reasons"], {"estimated_memory_exceeds_host_headroom": 4})
        entry = entries(read_resolution(self.root / "host", read_plan(self.root / "host")))
        estimate = next(iter(entry.values()))["estimated_memory"]
        self.assertEqual(estimate["library_modeled"], 12_800)
        self.assertEqual(estimate["verification_versions"], 128 * 8)

    def test_library_bytes_prefer_reserved_bytes(self):
        # The allocator rounding is what the process really holds, so
        # admission bills it; an envelope without it (a baseline's)
        # falls back to the requested bytes.
        self.assertEqual(library_bytes({"modeled_buffer_bytes": 100, "modeled_reserved_bytes": 2 << 20}),
                         2 << 20)
        self.assertEqual(library_bytes({"modeled_buffer_bytes": 100, "modeled_reserved_bytes": None}), 100)
        self.assertEqual(library_bytes({"modeled_buffer_bytes": 100}), 100)

    def test_verification_off_bills_no_version_table_and_reaches_the_worker(self):
        data = configuration(repetitions=1)
        data["stages"][0]["kind"] = "capacity"
        for mode, versions in (("full", 128 * 8), ("off", 0)):
            data["instrumentation"] = {"verification": mode}
            campaign = self.campaign(data, mode)
            resolve_campaign(campaign, self.worker)
            plan = read_plan(campaign)
            row = next(r for r in plan["trials"] if r["spec"]["candidate"] == "pinned")
            entry = entries(read_resolution(campaign, plan))[row["trial_id"]]
            self.assertEqual(entry["estimated_memory"]["verification_versions"], versions)
            argv = trial_arguments(row, entry, self.root / "out", None)
            self.assertEqual(dict(zip(argv[::2], argv[1::2]))["--verification"], mode)
        # Verification is a trial input, never a resolver input.
        self.assertTrue(all("--verification" not in call for call in self.calls()))

    def test_harness_options_reach_the_worker_only_when_on(self):
        data = configuration(repetitions=1)
        data["stages"][0]["kind"] = "latency"
        data["stages"][0]["rates"] = {"absolute_ops_per_second": [100_000]}
        for on in (False, True):
            data["instrumentation"] = {"logging": "histogram_checkpoints", "checkpoint_thread": on}
            data["workload"] = {"distribution": "counter" if on else "uniform"}
            campaign = self.campaign(data, "on" if on else "off")
            resolve_campaign(campaign, self.worker)
            plan = read_plan(campaign)
            row = next(r for r in plan["trials"] if r["spec"]["candidate"] == "pinned")
            # Off, the field is absent from the spec, so the trial id does not move.
            self.assertEqual("checkpoint_thread" in row["spec"]["instrumentation"], on)
            entry = entries(read_resolution(campaign, plan))[row["trial_id"]]
            values = dict(zip(*[iter(trial_arguments(row, entry, self.root / "out", None))] * 2))
            self.assertEqual(values.get("--key-pattern"), "counter" if on else None)
            self.assertEqual(values.get("--checkpoint-thread"), "1" if on else None)
        # Saturated rows keep no checkpoint blocks, so they never carry the option.
        saturated = {**data, "stages": [{**data["stages"][0], "kind": "capacity", "rates": None}]}
        rows = expand(decode(Campaign, saturated))["trials"]
        self.assertTrue(rows and all("checkpoint_thread" not in r["spec"]["instrumentation"] for r in rows))
        # Counter keys are distinct and scattered, so every scheme and API mode can run them.
        mixed = {**data, "stages": [{**data["stages"][0], "api_modes": ["scalar", "batch"], "batch_sizes": [4],
                                     "candidates": [{"name": "map", "overrides": {"scheme": "std_unordered_map"}},
                                                    {"name": "pinned", "overrides": {"scheme": "hierarchical_incremental"}}]}]}
        rows = expand(decode(Campaign, mixed))["trials"]
        self.assertEqual({r["spec"]["api_mode"] for r in rows}, {"scalar", "batch"})
        reasons = {reason for r in rows for reason in r["skip_reasons"]}
        self.assertEqual(reasons, set())  # nothing about keys
        # One spin-before-park setting for every waiting library thread reaches the
        # resolver; unset, the spec does not name it, so trial ids without it are unchanged.
        self.assertTrue(all("spin_before_park_ns" not in r["spec"]["resources"]
                            for r in expand(decode(Campaign, data))["trials"]))
        spun = {**data, "resources": {**data.get("resources", {}), "spin_before_park_ns": 1_000_000_000}}
        campaign = self.campaign(spun, "spin")
        resolve_campaign(campaign, self.worker)
        plan = read_plan(campaign)
        row = next(r for r in plan["trials"] if r["spec"]["candidate"] == "pinned")
        self.assertEqual(row["spec"]["resources"]["spin_before_park_ns"], 1_000_000_000)
        entry = entries(read_resolution(campaign, plan))[row["trial_id"]]
        values = dict(zip(*[iter(trial_arguments(row, entry, self.root / "out", None))] * 2))
        self.assertEqual(values.get("--spin-before-park-ns"), "1000000000")
        with self.assertRaisesRegex(ValidationError, "spin_before_park_ns"):
            decode(Campaign, {**data, "resources": {**data.get("resources", {}), "spin_before_park_ns": 0}})
        with self.assertRaisesRegex(ValidationError, "checkpoint thread"):
            decode(Campaign, {**data, "instrumentation": {"checkpoint_thread": True}})
        with self.assertRaisesRegex(ValidationError, "counter key"):
            decode(Campaign, {**data, "workload": {"distribution": "counter", "read_ppm": 1_000_000,
                                                   "hit_ppm": 500_000, "miss_key_count": 4}})

    def test_noop_synthetic_backend_stores_no_values(self):
        campaign = self.campaign(configuration(repetitions=1))
        resolve_campaign(campaign, self.worker, synthetic=True, synthetic_backend="noop")
        plan = read_plan(campaign)
        for row in plan["trials"]:
            entry = entries(read_resolution(campaign, plan))[row["trial_id"]]
            values = dict(zip(entry["worker_arguments"][::2], entry["worker_arguments"][1::2]))
            self.assertEqual(values["--scheme"], "noop")
            self.assertNotIn("fake_values", entry["estimated_memory"])
            self.assertEqual(entry["estimated_memory"]["verification_versions"], 128 * 8)
        with self.assertRaisesRegex(ValidationError, "synthetic"):
            resolve_campaign(self.campaign(configuration(), "native"), self.worker, synthetic_backend="noop")

    def test_resolver_rejection_is_a_persisted_skip(self):
        candidates = [{"name": "bad", "overrides": {"scheme": "hierarchical_incremental",
                                                     "incremental": {"owner_threads": 99}}}]
        summary = resolve_campaign(self.campaign(configuration(candidates)), self.worker)
        self.assertEqual(summary["status_counts"], {"skipped": 2})
        [reason] = summary["skip_reasons"]
        self.assertTrue(reason.startswith("resolver_rejected: configuration: owners"), reason)

    def test_arguments_bind_the_worker_request_to_the_resolution(self):
        candidates = [{"name": "tuned", "overrides": {"scheme": "hierarchical_incremental", "incremental": {
            "owner_threads": 0, "half_fanout_prefix": False, "batch_execution": "parallel_tiles"}}}]
        campaign = self.campaign(configuration(candidates, repetitions=1))
        resolve_campaign(campaign, self.worker)
        [call] = self.calls()
        values = dict(zip(call[::2], call[1::2]))
        self.assertEqual(values["--override.incremental.owner_threads"], "0")
        self.assertEqual(values["--override.incremental.half_fanout_prefix"], "false")
        self.assertEqual(values["--override.incremental.batch_execution"], "parallel_tiles")
        self.assertEqual((values["--scheme"], values["--cores"]), ("hierarchical_incremental", "4"))
        self.assertNotIn("--placement", values)  # placement is chosen at run time
        plan = read_plan(campaign)
        row = plan["trials"][0]
        entry = entries(read_resolution(campaign, plan))[row["trial_id"]]
        argv = trial_arguments(row, entry, self.root / "out", None)
        self.assertEqual(argv[:len(entry["worker_arguments"])], entry["worker_arguments"])
        keys = argv[::2]
        self.assertEqual(len(keys), len(set(keys)), "duplicate worker option")
        self.assertEqual(dict(zip(argv[::2], argv[1::2]))["--placement"], "near_far")

    def test_resolution_and_build_are_immutable(self):
        campaign = self.campaign()
        first = resolve_campaign(campaign, self.worker)
        self.assertEqual(resolve_campaign(campaign, self.worker), first)  # idempotent
        self.assertEqual((campaign / "build/worker").read_bytes(), self.worker.read_bytes())
        other = self.root / "other-worker"
        other.write_bytes(self.worker.read_bytes() + b"\n# rebuilt\n")
        with self.assertRaisesRegex(ValidationError, "different worker build"):
            resolve_campaign(campaign, other)
        path = campaign / "resolution.json"
        tampered = json.loads(path.read_text())
        tampered["trials"][0]["status"] = "skipped"
        path.chmod(0o644)
        path.write_text(json.dumps(tampered))
        with self.assertRaisesRegex(ValidationError, "identity mismatch"):
            read_resolution(campaign, read_plan(campaign))

    def test_plan_is_checked_against_its_own_identity(self):
        campaign = self.campaign()
        plan = json.loads((campaign / "plan.json").read_text())
        plan["campaign"]["future_optional_field"] = None  # tolerated only if the hash matches
        (campaign / "plan.json").write_text(json.dumps(plan))
        with self.assertRaisesRegex(ValidationError, "identity"):
            read_plan(campaign)

    def test_run_refuses_without_resolution(self):
        from analysis.oram_bench.campaign import run_campaign
        campaign = self.campaign()
        with self.assertRaisesRegex(ValidationError, "no resolution.json"):
            run_campaign(campaign, self.worker, synthetic=True)

    def test_native_run_refuses_protected_campaigns(self):
        from analysis.oram_bench.campaign import run_campaign
        campaign = self.campaign()  # default execution: unspecified runtime, protection required
        resolve_campaign(campaign, self.worker)
        with self.assertRaisesRegex(ValidationError, "require_protected = false"):
            run_campaign(campaign, self.worker)
        with self.assertRaisesRegex(ValidationError, "synthetic/native mode differs"):
            run_campaign(campaign, self.worker, synthetic=True)

    def test_native_run_blocks_on_a_host_without_the_requested_topology(self):
        from analysis.oram_bench.campaign import run_campaign
        data = configuration(resources={"physical_cores": 1024, "required_cache_domains": 8})
        data["execution"] = {"runtime": "native", "require_protected": False}
        campaign = self.campaign(data)
        resolve_campaign(campaign, self.worker)
        self.assertIn(["--cache-domains", "8"], [c[i:i + 2] for c in self.calls() for i in range(len(c))])
        # A plain host's TEE evidence, so the runtime gate passes on any host, a TD included.
        plain_host = assess_tee([], False, False, True, None, False)
        with patch("analysis.oram_bench.doctor.detect_tee", return_value=plain_host):
            result = run_campaign(campaign, self.worker, min_free_bytes=0)
        self.assertEqual((result["launched"], result["synthetic"]), (0, False))
        blocked = json.loads((campaign / "coordinator_status.json").read_text())
        self.assertEqual((blocked["status"], blocked["reason"]), ("blocked", "topology"))
        self.assertNotEqual(blocked["assessment"]["status"], "compatible")
        self.assertFalse((campaign / "trials").exists())

    def test_attempt_check_compares_the_worker_resolution(self):
        from analysis.oram_bench.admission import attempt_check
        from analysis.oram_bench.doctor import inspect
        campaign = self.campaign(configuration(resources={"placement": "unplaced"}))
        resolve_campaign(campaign, self.worker)
        plan = read_plan(campaign)
        row = plan["trials"][0]
        entry = entries(read_resolution(campaign, plan))[row["trial_id"]]
        environment = inspect(self.worker, "native")
        resolved = {"worker_schema_version": 1, "scheme": "hierarchical_incremental", "requested_capacity": 128,
                    "actual_capacity": 128, "policy_identity": "uncalibrated_fallback_v2",
                    "configuration_key": entry["configuration_key"], "supports_direct_initialization": True,
                    "modeled_buffer_bytes": 12800, "library_threads": 1,
                    "choices": [{"field": "scheme", "value": "hierarchical_incremental", "source": "explicit",
                                 "reason": "fixture"}],
                    "reserved_harness_cores": 1, "placement_verified": False,
                    "threads": [{"role": 0, "index": 0, "cpu": None}], "placement_policy": "unplaced",
                    "cpu_slots": []}
        self.assertEqual(attempt_check(row, entry, environment, resolved)["status"], "compatible")
        resolved["configuration_key"] = "another"
        self.assertIn("configuration_key_differs_from_resolution",
                      attempt_check(row, entry, environment, resolved)["rejection_reasons"])


if __name__ == "__main__":
    unittest.main()
