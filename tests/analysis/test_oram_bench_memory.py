"""Offline memory fixtures only; no worker launch or host sampling."""
import csv
import io
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
from types import SimpleNamespace

from analysis.oram_bench.codec import identity
from analysis.oram_bench.memory import HEADER, reduce_memory_stream
from analysis.oram_bench.reduction import (SUMMARY_SCHEMA_VERSION, committed_memory, memory_model, observation_marker, plot_summary,
                                           reduce_campaign)


def observation(phase, ns, **values):
    result = dict.fromkeys(HEADER, "")
    result.update(phase=phase, monotonic_ns=ns, swap_bytes=0, minor_faults=10, major_faults=5)
    result.update(values)
    return [result[key] for key in HEADER]


def fixture(rows):
    stream = io.StringIO()
    writer = csv.writer(stream)
    writer.writerow(HEADER)
    writer.writerows(rows)
    stream.seek(0)
    return stream


def plot_fixture(campaign, build, memory=None):
    """A current summary with one saturated group from `campaign` at `build`."""
    spec = {"candidate": "fixture", "api_mode": "scalar", "arrival": "saturated",
            "requested_capacity": 256, "shape": {"value_bytes": 8}}
    build = "sha256-" + build * 64
    row = {"trial_id": "trial", "environment_class": "class-" + build, "runtime": "fake",
           "build_identity": build, "spec": {**spec, "repetition": 0, "workload_seed": 1, "arrival_seed": 2},
           "summary": {"uncensored": True, "drained_ops_per_second": 10}, "memory": memory,
           "queue_stability": "not_applicable", "publication_blockers": ["cycle_coverage_unknown"]}
    return {"campaign_summary_schema_version": SUMMARY_SCHEMA_VERSION, "plan_id": "plan",
            "campaign": {"name": campaign, "plan_id": "plan", "worker_sha256": build, "library_header_sha256": None},
            "trial_status": {"counts": {"complete": 1}},
            "groups": [{"runtime": "fake", "group_id": "group-" + build, "environment_class": "class-" + build,
                        "build_identity": build, "spec": spec, "security": "oblivious", "repetitions": [row]}]}


def complete_rows():
    return [observation("before_construction", 0, rss_bytes=100, major_faults=1),
            observation("after_construction", 10, rss_bytes=900),
            observation("after_fill", 20, rss_bytes=800),
            observation("before_measure", 30, rss_bytes=500),
            observation("measure", 40, rss_bytes=600, pss_bytes=400, minor_faults=12),
            observation("final_drain", 50, rss_bytes=700, minor_faults=12),
            observation("after_drain", 60, rss_bytes=550, minor_faults=13),
            observation("after_verify", 70, rss_bytes=1000, minor_faults=20, major_faults=8)]


class MemoryTests(unittest.TestCase):
    def test_scope_peaks_deltas_and_nulls(self):
        summary = reduce_memory_stream(fixture(complete_rows()), interval_ns=10)
        envelope = summary["measurement_envelope"]
        self.assertTrue(envelope["complete"])
        self.assertEqual(envelope["sampled_max_bytes"]["rss_bytes"], 700)
        self.assertEqual(envelope["fault_deltas"], {"minor_faults": 3, "major_faults": 0})
        self.assertEqual(envelope["maximum_observation_gap_ns"], 10)
        self.assertEqual(summary["paging_status"], "no_paging_observed")
        self.assertIsNone(summary["in_ram_valid"])
        self.assertIsNone(summary["library_allocation_bytes"])
        self.assertFalse(summary["initialization_peak_complete"])
        self.assertEqual(summary["phases"]["measure"]["sampled_max_bytes"]["swap_bytes"], 0)
        self.assertIsNone(summary["phases"]["final_drain"]["sampled_max_bytes"]["pss_bytes"])
        self.assertEqual(summary["phases"]["final_drain"]["known_samples"]["pss_bytes"], 0)

    def test_paging_and_missing_evidence(self):
        for field, value, reason in (("swap_bytes", 1024, "nonzero_process_swap"),
                                     ("major_faults", 6, "major_faults_in_measurement_envelope")):
            rows = [observation("before_measure", 0), observation("phase_transition", 5, **{field: value}),
                    observation("after_drain", 10, **{field: value})]
            summary = reduce_memory_stream(fixture(rows))
            self.assertEqual(summary["paging_status"], "paging_observed")
            self.assertEqual(summary["paging_reasons"], [reason])
            self.assertIs(summary["in_ram_valid"], False)
        for rows in ([], complete_rows()[:3], complete_rows()[:6],
                     [observation("before_measure", 0), observation("after_drain", 10, swap_bytes="")],
                     [observation("before_measure", 0, major_faults=""), observation("after_drain", 10)],
                     [observation("after_drain", 10)]):
            summary = reduce_memory_stream(fixture(rows))
            self.assertEqual(summary["paging_status"], "unknown")
            self.assertIsNone(summary["in_ram_valid"])
        # A known bad observation cannot be hidden by other unavailable fields.
        summary = reduce_memory_stream(fixture([observation("after_drain", 10, swap_bytes=1, major_faults="")]))
        self.assertEqual(summary["paging_status"], "paging_observed")

    def test_repeated_baseline_poll_and_no_legacy_label(self):
        rows = [observation("before_measure", 0), observation("before_measure", 1, minor_faults=11),
                observation("measure", 2, minor_faults=12), observation("after_drain", 3, minor_faults=13)]
        summary = reduce_memory_stream(fixture(rows))
        self.assertEqual(summary["measurement_envelope"]["begin_ns"], 0)
        self.assertEqual(summary["measurement_envelope"]["fault_deltas"]["minor_faults"], 3)
        self.assertIsNone(summary["sampling_interval_ns"])
        rows[2][0] = "measure_or_drain"  # an unknown phase label is rejected
        with self.assertRaisesRegex(ValueError, "unknown memory CSV phase"):
            reduce_memory_stream(fixture(rows))

    def test_cgroup_limit_marker_and_peak_scopes(self):
        def limits(*values):
            rows = [observation("before_measure", 0, cgroup_limit_bytes=values[0])]
            rows += [observation("measure", i + 1, cgroup_limit_bytes=v) for i, v in enumerate(values[1:])]
            summary = reduce_memory_stream(fixture(rows))
            return summary["cgroup_limit_status"], summary["minimum_observed_cgroup_limit_bytes"]
        # "unlimited" (every level reads max) is not "unknown" (blank).
        self.assertEqual(limits("unlimited", "unlimited"), ("unlimited", None))
        self.assertEqual(limits("", ""), ("unknown", None))
        self.assertEqual(limits("", "unlimited"), ("unlimited", None))
        self.assertEqual(limits("unlimited", 700, 500, "unlimited"), ("limited", 500))
        summary = reduce_memory_stream(fixture([observation("before_measure", 0, cgroup_limit_bytes="unlimited")]))
        self.assertEqual(summary["phases"]["before_measure"]["known_samples"]["cgroup_limit_bytes"], 1)
        for field, value in (("cgroup_limit_bytes", "max"), ("rss_bytes", "unlimited"),
                             ("cgroup_peak_bytes", "unlimited")):
            with self.subTest(field=field), self.assertRaises(ValueError):
                reduce_memory_stream(fixture([observation("before_measure", 0, **{field: value})]))
        # memory.peak is the coordinator cgroup's lifetime peak; VmHWM is the trial's.
        rows = complete_rows()
        rows[1] = observation("after_construction", 10, rss_bytes=900, high_water_rss_bytes=950,
                              cgroup_peak_bytes=9000)
        rows[4] = observation("measure", 40, rss_bytes=600, high_water_rss_bytes=950, cgroup_peak_bytes=9100)
        summary = reduce_memory_stream(fixture(rows))
        self.assertEqual(summary["trial_peak_rss_bytes"], 950)
        self.assertEqual(summary["measurement_envelope"]["sampled_max_bytes"]["cgroup_lifetime_peak_bytes"], 9100)
        self.assertNotIn("cgroup_peak_bytes", summary["measurement_envelope"]["sampled_max_bytes"])
        self.assertNotIn("cgroup_peak_bytes", summary["phases"]["measure"]["known_samples"])
        self.assertIn("earlier_trials", summary["cgroup_lifetime_peak_scope"])
        self.assertIsNone(reduce_memory_stream(fixture(complete_rows()))["trial_peak_rss_bytes"])

    def test_bad_records_fail_closed(self):
        invalid = [
            [observation("bogus", 0)],
            [observation("before_measure", 10), observation("after_drain", 9)],
            [observation("after_fill", 0), observation("after_construction", 1)],
            [observation("after_fill", 0), observation("after_fill", 1)],
            [observation("before_measure", 0), observation("after_drain", 1, major_faults=4)],
            [observation("before_measure", 0), observation("after_drain", 1, minor_faults=9)],
            [observation("measure", 0)],
            [observation("before_measure", 0), observation("after_drain", 1), observation("phase_transition", 2)],
            [observation("before_measure", 0)[:-1]],
        ]
        for rows in invalid:
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                reduce_memory_stream(fixture(rows))
        for number in ("-1", "+1", "1.0", " 1", "１２", str(2**64), "1e3"):
            with self.subTest(number=number), self.assertRaises(ValueError):
                reduce_memory_stream(fixture([observation("before_measure", 0, rss_bytes=number)]))
        for text in ("", ",".join(reversed(HEADER)) + "\n", ','.join(HEADER) + '\n"unterminated'):
            with self.assertRaises(ValueError):
                reduce_memory_stream(io.StringIO(text))
        for interval in (0, -1, True, 2**64):
            with self.assertRaises(ValueError):
                reduce_memory_stream(fixture([]), interval_ns=interval)

    def test_commit_coverage_and_cli(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "worker").mkdir()
            raw = root / "worker/memory.csv"
            raw.write_text(fixture(complete_rows()).getvalue())
            manifest = {"artifacts": [{"path": "worker/memory.csv"}]}
            self.assertEqual(committed_memory(root, manifest, {})["paging_status"], "no_paging_observed")
            self.assertIsNone(committed_memory(root, {"artifacts": []}, {}))
            with self.assertRaises(ValueError):
                committed_memory(root, {"artifacts": []}, {"memory_csv_schema_version": 1})
            for version in (2, True, "1"):
                with self.assertRaises(ValueError):
                    committed_memory(root, manifest, {"memory_csv_schema_version": version})
            command = [sys.executable, "-m", "analysis.oram_bench", "memory-summary", "--input", str(raw)]
            run = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(run.returncode, 0, run.stderr)
            self.assertEqual(json.loads(run.stdout)["paging_status"], "no_paging_observed")
            raw.write_text("bad header\n")
            self.assertEqual(subprocess.run(command, capture_output=True).returncode, 2)

    def test_plot_markers(self):
        row = {"summary": {"uncensored": True}}
        self.assertEqual(observation_marker(row), "+")
        row["memory"] = {"paging_status": "no_paging_observed"}
        self.assertEqual(observation_marker(row), "o")
        row["memory"]["paging_status"] = "paging_observed"
        self.assertEqual(observation_marker(row), "x")
        row["memory"]["paging_status"] = "unknown"
        self.assertEqual(observation_marker(row), "+")
        row["summary"]["uncensored"] = False
        self.assertEqual(observation_marker(row), "x")

    def test_campaign_reduction_preserves_memory_and_gates_publication(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            attempt = root / "attempt"
            (attempt / "worker").mkdir(parents=True)
            (attempt / "requested.json").write_text('{"frozen_rate":null}')
            reducer = root / "reducer"
            reducer.write_text("fixture executable identity; never executed")
            environment = {"environment_class": "fixture", "runtime": "fake", "build_identity": "sha256-" + "b" * 64}
            (root / "environments").mkdir()
            (root / "environments" / (identity("environment-v1", environment) + ".json")).write_text(json.dumps(environment))
            spec = {"requested_capacity": 256, "shape": {"key_bytes": 4, "value_bytes": 8},
                    "api_mode": "scalar", "arrival": "saturated", "repetition": 0,
                    "workload_seed": 1, "arrival_seed": 2}
            summary = {"completed": 10, "rejected": 0, "outstanding": 0, "caller_end_ns": 100,
                       "drain_end_ns": 120, "drained_ops_per_second": 10e9 / 120,
                       "response": {"p99_ns": None, "p999_ns": None, "p99_sufficient_samples": False,
                                    "p999_sufficient_samples": False}}
            metadata = {"batch_sizes": [[1, 10]],
                        "memory_csv_schema_version": 1, "memory_interval_ns": 10,
                        "maintenance_coverage": {"carries_by_level": [40, 3]}}
            manifest = {"attempt_id": "attempt", "environment_id": identity("environment-v1", environment),
                        "artifacts": [{"path": "worker/memory.csv"}]}
            for swap, paging, valid in ((0, "no_paging_observed", True), (1, "paging_observed", False),
                                       ("", "unknown", False)):
                (attempt / "worker/memory.csv").write_text(fixture([
                    observation("before_measure", 0, rss_bytes=100),
                    observation("after_drain", 10, rss_bytes=200, swap_bytes=swap, high_water_rss_bytes=300)]).getvalue())
                with patch("analysis.oram_bench.reduction.read_plan", return_value={"plan_id": "plan",
                           "campaign": {"name": "fixture-campaign"},
                           "trials": [{"trial_id": "trial", "spec": spec}]}), \
                     patch("analysis.oram_bench.reduction.successful", return_value=(attempt, manifest)), \
                     patch("analysis.oram_bench.reduction.verify", return_value=manifest), \
                     patch("analysis.oram_bench.reduction._verify_replay", return_value=(summary, metadata)), \
                     patch("analysis.oram_bench.reduction.status", return_value={"counts": {"complete": 1}}), \
                     patch("analysis.oram_bench.reduction.subprocess.run", return_value=SimpleNamespace(
                           returncode=0, stdout='{"repetitions":1}', stderr="")) as repeated:
                    result = reduce_campaign(root, reducer, root / "derived")
                self.assertEqual(result["repetitions"], 1)
                self.assertIn("--repeat", repeated.call_args.args[0])
                derived = json.loads((root / "derived/summary.json").read_text())
                record = derived["groups"][0]["repetitions"][0]
                self.assertIs(record["publication_validated"], valid)
                self.assertEqual(record["memory"]["paging_status"], paging)
                with (root / "derived/repetitions.csv").open() as stream:
                    csv_row = next(csv.DictReader(stream))
                self.assertEqual(csv_row["paging_status"], paging)
                self.assertEqual(csv_row["sampled_envelope_rss_bytes"], "200")
                self.assertEqual(csv_row["trial_peak_rss_bytes"], "300")
                # The summary names its campaign and every group its build.
                self.assertEqual((csv_row["campaign"], csv_row["build_identity"]),
                                 ("fixture-campaign", "sha256-" + "b" * 64))
                self.assertEqual(derived["campaign"], {"name": "fixture-campaign", "plan_id": "plan",
                                 "worker_sha256": None, "library_header_sha256": None})
                self.assertEqual(derived["groups"][0]["build_identity"], "sha256-" + "b" * 64)
                self.assertEqual(result["campaign"], "fixture-campaign")

    @unittest.skipUnless(importlib.util.find_spec("matplotlib"), "optional plotting dependency unavailable")
    def test_latency_plots_use_log_offered_rate_even_when_achieved_differs(self):
        figures = {}
        def capture(figure, path, **kwargs):
            if str(path).endswith('.png'):
                figures[Path(path).stem] = figure
        with tempfile.TemporaryDirectory() as directory:
            paths = []
            for campaign, build in [('slow', 'a'), ('fast', 'b')]:
                summary = plot_fixture(campaign, build)
                group = summary['groups'][0]
                group['spec']['arrival'] = 'fixed'
                row = group['repetitions'][0]
                row['spec']['arrival'] = 'fixed'
                row['offered_ops_per_second'] = 1000
                row['summary']['response'] = {'p99_ns': 5000}
                path = Path(directory) / (campaign + '.json')
                path.write_text(json.dumps(summary))
                paths.append(path)
            with patch('matplotlib.figure.Figure.savefig', autospec=True, side_effect=capture):
                plot_summary(paths, Path(directory) / 'plots')
            for axis in [figures['campaign'].axes[1], *figures['targets'].axes[2:4]]:
                self.assertEqual(axis.get_xscale(), 'log')
                self.assertEqual(axis.get_xlabel(), 'Offered input rate (ops/s)')
                self.assertTrue(axis.collections)
                for points in axis.collections:
                    self.assertEqual(list(points.get_offsets()[:, 0]), [1000])

    @unittest.skipUnless(importlib.util.find_spec("matplotlib"), "optional plotting dependency unavailable")
    def test_offline_plot_exports_and_missing_memory(self):
        with tempfile.TemporaryDirectory() as directory, patch.dict(os.environ, {"MPLCONFIGDIR": directory}):
            root = Path(directory)
            for memory in (reduce_memory_stream(fixture(complete_rows())), None):
                source = root / "summary.json"
                source.write_text(json.dumps(plot_fixture("fixture", "a", memory)))
                output = root / ("with-memory" if memory else "without-memory")
                self.assertFalse(plot_summary(source, output)["publication_validated"])
                for prefix in ("campaign", "memory"):
                    self.assertTrue((output / (prefix + ".png")).read_bytes().startswith(b"\x89PNG"))
                    self.assertTrue((output / (prefix + ".pdf")).read_bytes().startswith(b"%PDF"))
            # Only the current summary schema version is plotted.
            old = plot_fixture("fixture", "a")
            old["campaign_summary_schema_version"] = 2
            source.write_text(json.dumps(old))
            with self.assertRaisesRegex(ValueError, "re-run reduce"):
                plot_summary(source, root / "old")

    @unittest.skipUnless(importlib.util.find_spec("matplotlib"), "optional plotting dependency unavailable")
    def test_memory_model_is_logical_bytes_against_the_library_bill(self):
        row = {"live_entries": 1000, "spec": {"shape": {"key_bytes": 8, "value_bytes": 48}}}
        self.assertEqual(memory_model(row, {"modeled_buffer_bytes": 90_000, "modeled_reserved_bytes": 2 << 20}),
                         {"live_entries": 1000, "logical_bytes": 56_000, "library_modeled_bytes": 90_000,
                          "library_reserved_bytes": 2 << 20})
        # A synthetic row models nothing; a resolution without reserved bytes reports none.
        self.assertIsNone(memory_model(row, {"modeled_buffer_bytes": 0})["library_modeled_bytes"])
        self.assertIsNone(memory_model(row, {"modeled_buffer_bytes": 5})["library_reserved_bytes"])
        self.assertIsNone(memory_model(row, None)["library_modeled_bytes"])

    def test_plot_compares_campaigns_without_pooling_builds(self):
        with tempfile.TemporaryDirectory() as directory, patch.dict(os.environ, {"MPLCONFIGDIR": directory}):
            root = Path(directory)
            paths = []
            for name, build in (("tune", "a"), ("tune", "b"), ("tune-rerun", "a")):
                paths.append(root / f"{name}-{build}.json")
                paths[-1].write_text(json.dumps(plot_fixture(name, build)))
            # One configuration from three campaign/build pairs is three series.
            result = plot_summary(paths, root / "compare")
            self.assertEqual([label.split(" / ")[0] for label in result["series"]],
                             ["tune@" + "a" * 8, "tune@" + "b" * 8, "tune-rerun@" + "a" * 8])
            self.assertTrue((root / "compare/campaign.png").read_bytes().startswith(b"\x89PNG"))
            # Several campaigns also get one column each, and every
            # series is listed with its family; with several campaigns the
            # family names the campaign too.
            self.assertTrue((root / "compare/targets.png").read_bytes().startswith(b"\x89PNG"))
            with open(root / "compare/series.csv") as stream:
                table = list(csv.DictReader(stream))
            self.assertEqual([row["label"] for row in table], result["series"])
            self.assertTrue(all(row["family"].startswith(row["campaign"]) for row in table))
            single = plot_summary(paths[:1], root / "single")
            self.assertFalse((root / "single/targets.png").exists())
            with open(root / "single/series.csv") as stream:
                self.assertFalse(next(csv.DictReader(stream))["family"].startswith("tune@"))
            self.assertEqual(len(single["series"]), 1)
            # A series never merges two inputs: the same campaign and build twice is refused.
            with self.assertRaisesRegex(ValueError, "not merged"):
                plot_summary([paths[0], paths[0]], root / "twice")
            command = [sys.executable, "-m", "analysis.oram_bench", "plot", "--summary", str(paths[0]),
                       "--summary", str(paths[1]), "--output", str(root / "cli")]
            run = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(run.returncode, 0, run.stderr)
            self.assertEqual(len(json.loads(run.stdout)["series"]), 2)
            refused = subprocess.run(command[:-4] + ["--summary", str(paths[0]), "--output", str(root / "no")],
                                     capture_output=True, text=True)
            self.assertEqual(refused.returncode, 2)
            self.assertIn("not merged", refused.stderr)


if __name__ == "__main__":
    unittest.main()
