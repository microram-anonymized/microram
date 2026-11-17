"""Harness gate records (analysis/oram_bench/validation.py).

A gate record carries measured harness-overhead evidence for one binding
(worker hash, environment, shape, core placement, logging mode, ...) and the
verdict derived from its quantiles.  Tests check that a record re-derives its
verdict from its inputs and that records are reported evidence only: they never
block or clear a row.
"""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from analysis.oram_bench.codec import ValidationError, decode
from analysis.oram_bench.planner import expand
from analysis.oram_bench.reduction import publication_blockers
from analysis.oram_bench.schema import Campaign
from analysis.oram_bench.validation import HarnessValidation, build_records, gate_failures

WORKER = "sha256-" + "a" * 64


def changes(**overrides):
    values = {"p50": (1000, 1010), "p99": (5000, 5090), "p999": (9000, 9100), "max": (40000, 90000),
              "mean_service": (800, 801), **overrides}
    return [{"quantile": q, "control_ns": c, "instrumented_ns": i, "samples": 10**6} for q, (c, i) in values.items()]


def record(**binding):
    data = {"schema_version": 1, "status": "passed",
            "binding": {"worker_sha256": WORKER, "environment_class": "class-a", "key_bytes": 4, "value_bytes": 8,
                        "physical_cores": 16, "placement": "near_far", "api_mode": "scalar",
                        "caller_batch_size": 1, "batch_policy": {"formation": "fixed_count", "timeout_ns": None},
                        "arrival": "fixed", "rate": {"minimum_ops_per_second": 100_000,
                                                     "maximum_ops_per_second": 2_000_000},
                        "logging": "full_events", "verification": "off", **binding},
            "evidence": {"comparison": "logging_mode", "control_logging": "histogram_checkpoints",
                         "changes": changes(), "harness_ns_per_request": 69, "events": 10**7, "lost_events": 0}}
    return data


def rows():
    campaign = {"schema_version": 1, "name": "fixture", "repetitions": 1,
                "instrumentation": {"logging": "full_events", "verification": "off"},
                "stages": [{"name": "latency", "kind": "latency", "capacities": [128], "api_modes": ["scalar"],
                            "shapes": [{"name": "k4-v8", "key_bytes": 4, "value_bytes": 8}],
                            "candidates": [{"name": "auto", "overrides": {"scheme": "auto"}}],
                            "rates": {"absolute_ops_per_second": [500_000, 600_000]}}]}
    return {("fixed" if row["spec"]["rate"]["ops_per_second"] == 500_000 else "other"): row
            for row in expand(decode(Campaign, campaign))["trials"]}


class ValidationTests(unittest.TestCase):
    def test_the_verdict_is_rederived_from_the_evidence(self):
        over = record()
        over["evidence"]["changes"] = changes(p999=(9000, 9600))  # 6.7% slower > 5%
        # Only a slower published mode fails: a faster one is not an overhead.
        faster = record()
        faster["evidence"]["changes"] = changes(p50=(9000, 6000), p99=(9000, 3000), p999=(9000, 9440))  # 4.9% slower passes
        self.assertEqual(gate_failures(decode(HarnessValidation, faster)), [])
        lost = record()
        lost["evidence"]["lost_events"] = 1
        missing = record()
        missing["evidence"]["changes"] = [c for c in changes() if c["quantile"] != "max"]
        absent = record()
        absent["evidence"] = None
        failed = record(); failed["status"] = "failed"
        expected = [["p999_over_gate"], ["lost_events"], ["max_evidence_missing"], ["evidence_missing"],
                    ["record_status_failed"]]
        for document, failures in zip((over, lost, missing, absent, failed), expected):
            with self.subTest(failures=failures):
                self.assertEqual(gate_failures(decode(HarnessValidation, document)), failures)
        # The maximum is reported, never gated: one sample cannot resolve 5%.
        self.assertEqual(gate_failures(decode(HarnessValidation, record())), [])

    def test_a_record_cannot_loosen_the_gate_or_bind_inconsistently(self):
        for document in ({**record(), "gate_ppm": 60_000}, record(rate=None), record(arrival="saturated"),
                         record(caller_batch_size=16)):
            with self.subTest(document=document), self.assertRaises(ValidationError):
                decode(HarnessValidation, document)

    def test_harness_overhead_blocks_no_row(self):
        # Without any gate record, a clean row has no publication blocker.
        spec = rows()["fixed"]["spec"]
        summary = {"response": {"p99_sufficient_samples": True}, "uncensored": True}
        memory = {"paging_status": "no_paging_observed"}
        self.assertEqual(publication_blockers(spec, summary, memory, "sufficient", "stable", True), [])


def summary(spec, logging, p999, offered=500_000, group="g"):
    spec = {**spec, "instrumentation": {**spec["instrumentation"], "logging": logging}}
    distribution = lambda scale: {"count": 10**6, "mean_ns": 800 * scale, "p50_ns": 1000 * scale,
                                  "p99_ns": 5000 * scale, "p999_ns": p999, "maximum_ns": 90000}
    record = {"summary": {"response": distribution(1), "service": distribution(1), "completed": 10**6},
              "offered_ops_per_second": offered, "attempt_id": "attempt-" + logging}
    return {"campaign": {"worker_sha256": WORKER},
            "groups": [{"group_id": group, "environment_class": "class-a", "spec": spec, "repetitions": [record]}]}


class RecordBuilderTests(unittest.TestCase):
    def test_a_matched_pair_becomes_a_gated_record(self):
        spec = rows()["fixed"]["spec"]
        control = summary(spec, "histogram_checkpoints", 9000)
        for p999, status in ((9100, "passed"), (9400, "passed"), (9500, "failed")):
            with self.subTest(p999=p999):
                [record], unmatched = build_records(control, summary(spec, "full_events", p999), harness_ns_per_request=69)
                self.assertEqual((record["status"], unmatched), (status, []))
                self.assertEqual(record["binding"]["rate"], {"minimum_ops_per_second": 500_000,
                                                             "maximum_ops_per_second": 500_000})
                self.assertEqual(gate_failures(decode(HarnessValidation, record)) == [], status == "passed")
        other = summary(rows()["other"]["spec"], "full_events", 9100, group="other")
        self.assertEqual(build_records(control, other, harness_ns_per_request=69), ([], ["other"]))
        with self.assertRaises(ValidationError):
            build_records(control, other)


class DelayedClockReplayTests(unittest.TestCase):
    """The gate through the real replay: synthetic event logs whose instrumented
    arm reads every completion `delay_ns` late (a delayed clock), replayed by
    oram_bench_aggregate, then gated. Identical arms and a 1% delay pass; a 30%
    delay fails at every quantile it moves past 5%."""

    REQUESTS = 120_000  # p99.9 needs 100 tail samples
    GAP = 100_000       # arrivals every 100 us; service stays below, so no queueing

    def replay(self, reducer, directory, name, delay_ns):
        import struct
        import subprocess
        import zlib
        n, gap = self.REQUESTS, self.GAP
        events = [(1, 0, n * gap, n * gap + 10**9, n, 1024, 1, 1024, 0)]
        for i in range(n):
            # 10 us typical service, every 97th request 15 us, every 1009th 30 us.
            service = 10_000 + (5_000 if i % 97 == 0 else 0) + (15_000 if i % 1009 == 0 else 0)
            arrival = i * gap
            last = arrival + service + delay_ns
            events += [(2, i, arrival, 0, 0, 0, 0, 0), (3, i, 1, arrival, last, 0, 0, 0), (4, i, i, arrival, 0, 0, 0, 0)]
        end = max(last, n * gap)
        events.append((8, end, end, n, n, n, 0, 100, 0))
        payload = b"".join(struct.pack("<8Q", *e[:8]) for e in events)
        path = Path(directory) / f"{name}.bin"
        path.write_bytes(b"ORBEV01\n" + struct.pack("<4Q", len(payload), zlib.crc32(payload), 0, len(events)) + payload)
        result = subprocess.run([str(reducer), "--events", str(path)], capture_output=True, text=True, timeout=300)
        self.assertEqual(result.returncode, 0, result.stderr)
        return json.loads(result.stdout)

    def test_a_delayed_clock_fails_the_gate_and_identical_arms_pass(self):
        from tests.analysis.test_oram_bench_timeseries import find_reducer
        reducer = find_reducer()
        if reducer is None:
            self.skipTest("oram_bench_aggregate is not built")
        spec = rows()["fixed"]["spec"]
        with tempfile.TemporaryDirectory() as directory:
            def campaign(logging, delay_ns):
                replayed = self.replay(reducer, directory, f"{logging}-{delay_ns}", delay_ns)
                return {"campaign": {"worker_sha256": WORKER},
                        "groups": [{"group_id": "g", "environment_class": "class-a",
                                    "spec": {**spec, "instrumentation": {**spec["instrumentation"],
                                                                         "logging": logging}},
                                    "repetitions": [{"summary": replayed, "offered_ops_per_second": 500_000,
                                                     "attempt_id": f"attempt-{delay_ns}"}]}]}
            control = campaign("histogram_checkpoints", 0)
            self.assertTrue(control["groups"][0]["repetitions"][0]["summary"]["response"]["p999_sufficient_samples"])
            for delay_ns, status, failures in ((0, "passed", None), (100, "passed", None),
                                               (3000, "failed", "p50_over_gate; p99_over_gate; p999_over_gate")):
                with self.subTest(delay_ns=delay_ns):
                    [record], unmatched = build_records(control, campaign("full_events", delay_ns),
                                                        harness_ns_per_request=69)
                    self.assertEqual((record["status"], record.get("note"), unmatched), (status, failures, []))
                    changes = {c["quantile"]: c for c in record["evidence"]["changes"]}
                    moved = {q: c["instrumented_ns"] - c["control_ns"] for q, c in changes.items()}
                    # The replay recovers the injected delay: exactly in the maximum and
                    # mean, within the histogram's bucket width (< 1/64) in the quantiles.
                    self.assertEqual((moved["max"], moved["mean_service"]), (delay_ns, delay_ns), moved)
                    for q in ("p50", "p99", "p999"):
                        self.assertLessEqual(abs(moved[q] - delay_ns), changes[q]["control_ns"] / 64, moved)


if __name__ == "__main__":
    unittest.main()
