"""Campaign coordinator recovery paths with injected processes: a stop before launch is
committed as a preemption, a stop during replay as an interruption that writes nothing,
and a frozen offered rate stays authoritative.  No workers run."""
import json
import os
from pathlib import Path
import signal
import stat
import sys
import tempfile
import unittest
from unittest.mock import patch

from analysis.oram_bench import campaign as coordinator
from analysis.oram_bench.codec import decode, identity
from analysis.oram_bench.planner import expand, write_plan
from analysis.oram_bench.resolution import entries, read_resolution, resolve_campaign
from analysis.oram_bench.schema import Campaign
from analysis.oram_bench.store import atomic_json, commit, durable_mkdir
from test_oram_bench_resolution import configuration, stub_worker


def script(path, body):
    path.write_text(f"#!{sys.executable}\n" + body)
    path.chmod(path.stat().st_mode | stat.S_IXUSR)
    return path


class RecoveryTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = Path(self.directory.name)
        os.environ["STUB_WORKER_LOG"] = str(self.root / "calls.jsonl")

    def tearDown(self):
        self.directory.cleanup()

    def test_stop_before_launch_commits_a_preemption_without_launching(self):
        campaign = self.root / "campaign"
        # No headroom reservation: the preflight of this stub trial must not
        # depend on how much of the host's memory is free.
        write_plan(expand(decode(Campaign, configuration(candidates=[
            {"name": "auto", "overrides": {"scheme": "auto"}}], repetitions=1,
            resources={"headroom_ppm": 0}))), campaign)
        worker = self.root / "worker"; worker.write_text("never executed")
        resolve_campaign(campaign, worker, synthetic=True)
        real = coordinator.attempt_preflight
        def preflight_then_stop(*args):
            os.kill(os.getpid(), signal.SIGTERM)  # arrives after the top-of-loop check
            return real(*args)
        environment = {"environment_class": "fixture", "boot_identity": "fixture"}
        with patch.object(coordinator, "inspect", return_value=environment), \
             patch.object(coordinator, "attempt_preflight", side_effect=preflight_then_stop), \
             patch.object(coordinator.subprocess, "Popen") as launch:
            result = coordinator.run_campaign(campaign, worker, synthetic=True, min_free_bytes=0)
        launch.assert_not_called()
        self.assertTrue(result["stopped"])
        self.assertEqual(result["launched"], 0)
        [attempt] = campaign.glob("trials/*/attempts/*")
        manifest = json.loads((attempt / "manifest.json").read_text())
        self.assertEqual((manifest["status"], manifest["failure_kind"]), ("interrupted", "preemption"))

    def test_stop_during_replay_is_an_interruption_and_replay_writes_nothing(self):
        output = self.root / "worker"
        output.mkdir()
        (output / "worker.json").write_text(json.dumps({"correctness_verified": True, "lost_events": 0,
            "writer_error": "", "minimum_tail_count": 1, "trial_boundaries": [1, 1, 1, 1, 1, 0]}))
        (output / "checkpoint.bin").write_bytes(b"")
        reducer = script(self.root / "reducer", "import json\nprint(json.dumps("
                         "{'request_cap_reached': False, 'deadline_exceeded': False, 'completed': 1}))\n")
        with self.assertRaises(coordinator.ReplayInterrupted):
            coordinator._verify_replay(reducer, output, require_live=False, stop=[True])
        replay, _ = coordinator._verify_replay(reducer, output, require_live=False, stop=[False])
        self.assertEqual(replay["completed"], 1)
        self.assertFalse((output / "summary.json").exists())

    def test_frozen_rate_is_authoritative_and_invalid_sources_defer(self):
        data = configuration(candidates=[{"name": "auto", "overrides": {"scheme": "auto"}}], repetitions=1)
        data["stages"][0].update(kind="latency", rates={"saturation_fractions_ppm": [500000],
                                                                    "minimum_ops_per_second": 1})
        campaign = self.root / "latency"
        write_plan(expand(decode(Campaign, data)), campaign)
        resolve_campaign(campaign, stub_worker(self.root))
        plan = coordinator.read_plan(campaign)
        resolved = entries(read_resolution(campaign, plan))
        source = next(r for r in plan["trials"] if not r["dependencies"])
        consumer = next(r for r in plan["trials"] if r["dependencies"])
        environment = {"environment_class": "fixture-class", "value": 1}
        environment_id = identity("environment-v1", environment)
        atomic_json(campaign / "environments" / (environment_id + ".json"), environment)
        attempt = campaign / "trials" / source["trial_id"] / "attempts" / "000001-attempt-fixture"
        durable_mkdir(attempt / "worker")
        atomic_json(attempt / "worker/worker.json", {"trial_boundaries": [1000, 1000, 0, 10**9, 2 * 10**9, 0]})
        commit(attempt, {"schema_version": 1, "trial_id": source["trial_id"], "attempt_id": "attempt-fixture",
            "environment_id": environment_id, "resolved_plan_id": "fixture", "status": "complete",
            "failure_kind": None, "reason": None, "events": 0, "lost_events": 0, "correctness_verified": True,
            "measurement_begin_ns": 0, "measurement_end_ns": 10**9, "drain_end_ns": 2 * 10**9})
        rate, deferred = coordinator._rate(campaign, consumer, "fixture-class", resolved)
        self.assertEqual((rate, deferred), (250, None))  # 500 ops/s drained, at half
        self.assertEqual(coordinator._rate(campaign, consumer, "fixture-class", resolved), (250, None))
        # A frozen rate under the stage's floor is kept but never launched.
        floored = {**consumer, "spec": {**consumer["spec"], "rate": {**consumer["spec"]["rate"],
                                                                     "minimum_ops_per_second": 251}}}
        self.assertEqual(coordinator._rate(campaign, floored, "fixture-class", resolved), (250, "below_rate_floor"))
        (attempt / "COMMITTED.json").unlink()
        self.assertEqual(coordinator._rate(campaign, consumer, "fixture-class", resolved),
                         (None, "rate_source_invalid"))


if __name__ == "__main__":
    unittest.main()
