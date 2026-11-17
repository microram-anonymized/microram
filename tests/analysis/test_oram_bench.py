"""Planner, schema and codec tests for the benchmark harness (analysis/oram_bench).

Covers campaign decoding and validation, deterministic trial expansion and
hashing, the time and cost caps, and that every preset in benchmarks/campaigns/
expands to its expected rows.  Planning/contract tests only: no ORAM
construction or timing measurements.
"""

import json
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from analysis.oram_bench.codec import ValidationError, canonical, decode, identity, json_schema, load_json, plain
from analysis.oram_bench.planner import expand, write_plan
from analysis.oram_bench.rates import geometric_rate_grid
from analysis.oram_bench.schema import Campaign, Environment, Manifest, Overrides, SCHEMAS

ROOT = Path(__file__).resolve().parents[2]


def config():
    return {"schema_version": 1, "name": "fixture", "repetitions": 2,
            "stages": [{"name": "small", "kind": "smoke",
                        "shapes": [{"name": "k4-v8", "key_bytes": 4, "value_bytes": 8}],
                        "capacities": [128], "api_modes": ["scalar", "batch"], "batch_sizes": [16],
                        "candidates": [{"name": "incremental", "overrides": {
                            "scheme": "hierarchical_incremental", "incremental": {
                                "owner_threads": 0, "half_fanout_prefix": False}}}]}]}


def plan(data=None):
    return expand(decode(Campaign, config() if data is None else data))


class CodecTests(unittest.TestCase):
    def test_strict_scalars_and_fields(self):
        for field, value in [("repetitions", True), ("base_seed", -1), ("base_seed", 2**64),
                             ("base_seed", 1.0), ("repetition", 2), ("schema_version", 2)]:
            with self.subTest(field=field, value=value):
                data = config()
                data[field] = value
                with self.assertRaises(ValidationError):
                    decode(Campaign, data)
        data = config()
        data["stages"][0]["candidates"][0]["overrides"]["incremental"]["owners"] = 2
        with self.assertRaisesRegex(ValidationError, "unknown fields"):
            decode(Campaign, data)

    def test_duplicates_nonfinite_and_missing_required(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "fixture.json"
            for text in ['{"schema_version":1,"schema_version":2}', '{"seed":NaN}', '{"seed":Infinity}']:
                path.write_text(text)
                with self.assertRaises(ValidationError):
                    load_json(path)
        with self.assertRaisesRegex(ValidationError, "required field"):
            decode(Campaign, {"schema_version": 1})

    def test_explicit_zero_false_and_null(self):
        automatic = decode(Overrides, {"incremental": {}})
        explicit = decode(Overrides, {"incremental": {"owner_threads": 0, "half_fanout_prefix": False}})
        self.assertIsNone(automatic.incremental.owner_threads)
        self.assertEqual(explicit.incremental.owner_threads, 0)
        self.assertIs(explicit.incremental.half_fanout_prefix, False)
        self.assertNotEqual(identity("options", automatic), identity("options", explicit))
        self.assertEqual(canonical(automatic), canonical(decode(Overrides, {
            "incremental": {"owner_threads": None}})))
        self.assertEqual(explicit, decode(Overrides, plain(explicit)))

    def test_overrides_validate_shape_only(self):
        # Unknown fields, wrong types and out-of-set enum values are shape errors.
        bad = [
            {"incremental": {"bogus": 1}},
            {"incremental": {"branching_factor": 3}},
            {"incremental": {"owner_threads": "2"}},
            {"synchronous": {"owner_threads": 0}},
            {"tree": {"stash_registers": 2}},
            {"scheme": "fast"},
        ]
        for value in bad:
            with self.subTest(value=value), self.assertRaises(ValidationError):
                decode(Overrides, value)
        # Cross-field validity is the C++ resolver's job alone:
        # the planner must not become a second resolver.
        for value in ({"scheme": "tree", "incremental": {"owner_threads": 0}},
                      {"incremental": {"batch_execution": "chunked_cascade", "batch_participants": 4}},
                      {"scheme": "tree", "synchronous": {"prefix_flushes": 2}},
                      {"scheme": "auto", "incremental": {}, "tree": {}}):
            with self.subTest(value=value):
                decode(Overrides, value)

    def test_contract_schemas_are_serializable_and_closed(self):
        for name, cls in SCHEMAS.items():
            with self.subTest(schema=name):
                schema = json_schema(cls)
                self.assertEqual(json.loads(json.dumps(schema)), schema)
                for definition in schema["$defs"].values():
                    self.assertIs(definition["additionalProperties"], False)


class PlannerTests(unittest.TestCase):
    def test_common_geometric_rates_and_seeds_across_arms(self):
        grid = geometric_rate_grid(10_000, 3_000_000)
        self.assertEqual(grid.absolute_ops_per_second,
                         [10000, 20000, 40000, 80000, 160000, 320000, 640000, 1280000, 2560000, 3000000])
        data = config()
        stage = data['stages'][0]
        stage.update(kind='latency', rates=plain(grid))
        stage['candidates'].append({'name': 'floor', 'overrides': {'scheme': 'std_unordered_map'}})
        rows = plan(data)['trials']
        for candidate in ('incremental', 'floor'):
            arm = [r['spec'] for r in rows if r['spec']['candidate'] == candidate]
            self.assertEqual({s['rate']['ops_per_second'] for s in arm}, set(grid.absolute_ops_per_second))
            self.assertEqual({s['arrival'] for s in arm}, {'fixed'})
        for repetition in range(data['repetitions']):
            self.assertEqual(len({(r['spec']['workload_seed'], r['spec']['arrival_seed'])
                                  for r in rows if r['spec']['repetition'] == repetition}), 1)

    def test_geometric_rate_rounding_and_invalid_bounds(self):
        self.assertEqual(geometric_rate_grid(101, 400, '1.5').absolute_ops_per_second,
                         [101, 152, 228, 341, 400])
        self.assertEqual(geometric_rate_grid(7, 7).absolute_ops_per_second, [7])
        for minimum, maximum, factor in [(0, 10, '2'), (10, 9, '2'), (1, 9, '1'),
                                         (1, 9, 'NaN'), (1, 9, 'Infinity'), (1, 9, 'bad'),
                                         (10, 100, '1.00001')]:
            with self.subTest(minimum=minimum, maximum=maximum, factor=factor), self.assertRaises(ValidationError):
                geometric_rate_grid(minimum, maximum, factor)

    def test_determinism_and_normalization(self):
        first = plan()
        normalized = plan(plain(decode(Campaign, config())))
        self.assertEqual(canonical(first), canonical(normalized))
        self.assertEqual(len(first["trials"]), 4)
        self.assertEqual(len({t["trial_id"] for t in first["trials"]}), 4)
        self.assertTrue(all(t["planning_status"] == "deferred" for t in first["trials"]))
        self.assertTrue(all(t["actual_capacity"] is None for t in first["trials"]))
        without_id = {k: v for k, v in first.items() if k != "plan_id"}
        self.assertEqual(first["plan_id"], identity("plan-v1", without_id))

    def test_semantic_changes_have_new_ids(self):
        original = {r["trial_id"] for r in plan()["trials"]}
        mutations = [
            ("workload", "read_ppm", 500000), ("workload", "occupancy_ppm", 500000),
            ("timing", "max_accesses", 2**33), ("timing", "warmup_ns", 0),
            ("instrumentation", "logging", "histogram_checkpoints"),
            ("instrumentation", "service_timing", True),
            ("resources", "headroom_ppm", 100000), ("resources", "placement", "unplaced"),
            ("execution", "build_identity", "build-a"),
            ("execution", "source_identity", "revision-a"),
            ("execution", "dependency_identity", "toolchain-a"),
        ]
        for section, field, value in mutations:
            with self.subTest(section=section, field=field):
                data = config()
                data[section] = {field: value}
                self.assertFalse(original & {r["trial_id"] for r in plan(data)["trials"]})

    def test_verification_off_is_hashed_and_refused_in_smoke(self):
        # The smoke stage is the correctness evidence and always verifies.
        data = config()
        data["instrumentation"] = {"verification": "off"}
        with self.assertRaisesRegex(ValidationError, "smoke stage"):
            plan(data)
        data["stages"][0]["kind"] = "capacity"
        rows = plan(data)["trials"]
        self.assertTrue(all(r["spec"]["instrumentation"]["verification"] == "off" for r in rows))
        full = config()
        full["stages"][0]["kind"] = "capacity"
        self.assertFalse({r["trial_id"] for r in rows} & {r["trial_id"] for r in plan(full)["trials"]})

    def test_seeds_match_across_modes_and_repeat_independently(self):
        rows = plan()["trials"]
        by_rep = {}
        for row in rows:
            spec = row["spec"]
            by_rep.setdefault(spec["repetition"], set()).add(spec["workload_seed"])
            self.assertEqual(spec["caller_batch_size"], 1 if spec["api_mode"] == "scalar" else 16)
            self.assertEqual(spec["overrides"]["incremental"]["owner_threads"], 0)
        self.assertEqual([len(v) for v in by_rep.values()], [1, 1])
        self.assertNotEqual(by_rep[0], by_rep[1])

    def test_seed_streams_and_held_out_rows(self):
        # A stage without a stream keeps the original [base_seed, repetition, purpose] seeds.
        specs = [r["spec"] for r in plan()["trials"]]
        workload = {s["repetition"]: s["workload_seed"] for s in specs}
        arrival = {s["repetition"]: s["arrival_seed"] for s in specs}
        self.assertEqual((workload[0], arrival[1]), (2379887508926093655, 12172724043452833568))
        default = set(workload.values()) | set(arrival.values())
        data = config()
        screen = data["stages"][0]
        screen.update(seed_role="screening", seed_stream="screening")
        held = {**screen, "name": "held", "seed_role": "held_out", "seed_stream": "held-out"}
        final = {**screen, "name": "final", "seed_role": "finalist"}  # may replay screening seeds
        data["stages"] += [held, final]
        rows = plan(data)["trials"]
        by_stage = {}
        for row in rows:
            spec = row["spec"]
            by_stage.setdefault(spec["stage"], set()).update((spec["workload_seed"], spec["arrival_seed"]))
        self.assertFalse(by_stage["held"] & by_stage["small"])
        self.assertEqual(by_stage["final"], by_stage["small"])
        self.assertFalse(by_stage["small"] & default)
        # A held-out stage that replays a screening stream is rejected.
        for stream in ("screening", None):
            held["seed_stream"] = stream
            screen["seed_stream"] = stream
            with self.subTest(stream=stream), self.assertRaisesRegex(ValidationError, "held_out stage 'held'"):
                plan(data)
        held["seed_role"] = None
        self.assertEqual(len(plan(data)["trials"]), 12)

    def test_trial_cap_covers_setup_warmup_drain_and_retries(self):
        # The trial cap must cover setup allowance + warmup + its drain + measurement + drain.
        timing = {"setup_allowance_ns": 100, "warmup_ns": 10, "measurement_ns": 20,
                  "drain_deadline_ns": 5, "max_trial_ns": 140}
        data = config()
        data["timing"] = timing
        self.assertEqual(len(plan(data)["trials"]), 4)
        for field, value in (("max_trial_ns", 139), ("setup_allowance_ns", 101)):
            data["timing"] = {**timing, field: value}
            with self.subTest(field=field), self.assertRaisesRegex(ValidationError, "setup allowance"):
                plan(data)
        # Without a warmup phase there is no warmup drain.
        data["timing"] = {**timing, "warmup_ns": 0, "max_trial_ns": 125}
        plan(data)
        # The campaign cap covers every trial's cap once per planned attempt.
        data["timing"] = timing
        for retries, limit, ok in ((1, 4 * 140 * 2, True), (1, 4 * 140 * 2 - 1, False),
                                   (0, 4 * 140, True), (2, 4 * 140 * 3 - 1, False)):
            data["limits"] = {"planned_retries": retries, "max_campaign_trial_ns": limit}
            with self.subTest(retries=retries, limit=limit):
                if ok:
                    cost = plan(data)["cost"]
                    self.assertEqual(cost["trial_time_cap_sum_ns"], 4 * 140)
                    self.assertEqual(cost["trial_time_bound_with_retries_sum_ns"], 4 * 140 * (1 + retries))
                else:
                    with self.assertRaisesRegex(ValidationError, "planned retries"):
                        plan(data)

    def test_trial_cap_has_no_upper_limit(self):
        # There is no built-in upper limit on a trial's cap: large-N baseline rows can run for hours.
        data = config()
        data["timing"] = {"max_trial_ns": 48 * 3600 * 10**9}
        data["limits"] = {"max_campaign_trial_ns": 10**18}
        plan(data)

    def test_campaign_bound_counts_a_modelled_row_at_its_estimate(self):
        # A long trial cap must not bill every fast modelled row its full cap.
        data = config()
        data["timing"] = {"setup_allowance_ns": 100, "warmup_ns": 0, "measurement_ns": 20,
                          "drain_deadline_ns": 5, "max_trial_ns": 10**6}
        data["stages"][0]["candidates"][0]["trial_time"] = [{"setup_ns": 75}]
        data["limits"] = {"planned_retries": 0, "max_campaign_trial_ns": 4 * 100}
        cost = plan(data)["cost"]
        self.assertEqual(cost["trial_time_bound_sum_ns"], 4 * (75 + 20 + 5))
        self.assertEqual(cost["trial_time_cap_sum_ns"], 4 * 10**6)
        data["stages"][0]["candidates"][0]["trial_time"] = []
        with self.assertRaisesRegex(ValidationError, "planned retries"):
            plan(data)

    def test_matrix_order_does_not_change_trials(self):
        data = config()
        data["stages"][0]["capacities"] = [128, 256]
        first = plan(data)
        data["stages"][0]["capacities"].reverse()
        self.assertEqual(first["trials"], plan(data)["trials"])

    def test_limits_checked_before_large_expansion(self):
        data = config()
        data["repetitions"] = 1000
        data["stages"][0]["capacities"] = list(range(1, 1000))
        with self.assertRaisesRegex(ValidationError, "matrix has"):
            plan(data)
        data = config()
        data["limits"] = {"max_campaign_trial_ns": 1}
        with self.assertRaisesRegex(ValidationError, "time bounds"):
            plan(data)

    def test_key_space_and_memory_lower_bounds(self):
        data = config()
        data["stages"][0]["shapes"][0]["key_bytes"] = 1
        data["stages"][0]["capacities"] = [256]
        self.assertTrue(all(t["planning_status"] == "deferred" for t in plan(data)["trials"]))
        data["workload"] = {"read_ppm": 1000000, "hit_ppm": 500000, "miss_key_count": 1}
        self.assertTrue(all("insufficient_disjoint_key_space" in t["skip_reasons"]
                            for t in plan(data)["trials"]))
        data = config()
        data["resources"] = {"library_memory_limit_bytes": 100}
        for row in plan(data)["trials"]:
            # Memory limits are resolve's job, with the resolver's modelled bytes.
            self.assertEqual(row["logical_dataset_bytes"], 128 * 12)
            self.assertEqual(row["skip_reasons"], [])

    def test_latency_sources_and_absolute_rates(self):
        data = config()
        stage = data["stages"][0]
        stage["kind"] = "latency"
        stage["rates"] = {"absolute_ops_per_second": [1000], "saturation_fractions_ppm": [950000]}
        with self.assertRaisesRegex(ValidationError, "minimum_ops_per_second"):
            plan(data)  # the default floor is 100k req/s
        stage["rates"]["minimum_ops_per_second"] = 1000
        rows = plan(data)["trials"]
        self.assertEqual(len(rows), 12)  # two modes * two repetitions * (1 source + 2 rates)
        index = {r["trial_id"]: i for i, r in enumerate(rows)}
        for row in rows:
            spec = row["spec"]
            if spec["arrival"] == "saturated":
                self.assertIsNone(spec["rate"])
            elif spec["rate"]["kind"] == "saturation_fraction":
                self.assertIsNone(spec["rate"]["ops_per_second"])
                self.assertEqual(len(row["dependencies"]), 2)
                for source_id in row["dependencies"]:
                    self.assertLess(index[source_id], index[row["trial_id"]])
                    self.assertEqual(rows[index[source_id]]["spec"]["api_mode"], spec["api_mode"])
            else:
                self.assertEqual(spec["rate"]["ops_per_second"], 1000)
                self.assertFalse(row["dependencies"])

    def test_immutable_publication(self):
        with tempfile.TemporaryDirectory() as directory:
            first = plan()
            write_plan(first, directory)
            write_plan(first, directory)
            self.assertEqual(load_json(Path(directory) / "plan.json"), first)
            data = config()
            data["base_seed"] = 2
            with self.assertRaisesRegex(ValidationError, "different immutable plan"):
                write_plan(plan(data), directory)
            self.assertEqual(load_json(Path(directory) / "plan.json"), first)
            self.assertEqual([p.name for p in Path(directory).iterdir()], ["plan.json"])

    def test_competing_plan_publication_has_one_winner(self):
        first = plan()
        data = config()
        data["base_seed"] = 2
        second = plan(data)
        with tempfile.TemporaryDirectory() as directory:
            with ThreadPoolExecutor(max_workers=2) as pool:
                futures = [pool.submit(write_plan, value, directory) for value in (first, second)]
                errors = [future.exception() for future in futures]
            self.assertEqual(sum(error is None for error in errors), 1)
            self.assertTrue(all(error is None or isinstance(error, ValidationError) for error in errors))
            self.assertIn(load_json(Path(directory) / "plan.json"), (first, second))

    def test_horizon_does_not_assume_direct_fill_is_n_calls(self):
        data = config()
        data["timing"] = {"max_accesses": 128}
        self.assertTrue(all(row["planning_status"] == "deferred" for row in plan(data)["trials"]))
        data["stages"][0]["candidates"] = [{"name": "tree", "overrides": {"scheme": "tree"}}]
        self.assertTrue(all("access_horizon_cannot_cover_required_fill_and_settle" in row["skip_reasons"]
                            for row in plan(data)["trials"]))

    def test_logical_byte_overflow_is_a_skip(self):
        data = config()
        data["stages"][0]["shapes"][0]["value_bytes"] = 2**63
        for row in plan(data)["trials"]:
            self.assertIn("logical_dataset_exceeds_uint64_byte_range", row["skip_reasons"])
            self.assertIsNone(row["logical_dataset_bytes"])

    def test_all_presets_expand_without_measurements(self):
        # Expected row counts of every shipped preset in benchmarks/campaigns/.
        # The c4-* presets (Intel TDX and the same machine without TDX) carry
        # the std_unordered_map stages and a dense 4-byte-key value-width
        # copy; the c4-tdx-baseline-* presets run the baselines.
        expected = {}
        for runtime in ("tdx", "native"):
            # The latency presets start at 100k req/s, and paper rows start
            # with one trial each.
            expected.update({f"c4-{runtime}-smoke": 21, f"c4-{runtime}": 355, f"c4-{runtime}-latency": 450,
                             f"c4-{runtime}-value-width": 234})
        expected["c4-tdx-tune-rebuild-screen"] = 48
        expected.update({"c4-tdx-baseline-h2o2ram": 78, "c4-tdx-baseline-h2o2ram-smoke": 3,
                         "c4-tdx-baseline-h2o2ram-shipped": 64,
                         "c4-tdx-baseline-h2o2ram-shipped-smoke": 3, "c4-tdx-baseline-sonic": 104,
                         "c4-tdx-baseline-sonic-smoke": 4,
                         "c4-tdx-baseline-pilot-h2o2ram": 10, "c4-tdx-baseline-pilot-h2o2ram-shipped": 10,
                         "c4-tdx-baseline-pilot-sonic": 20,
                         "local-baseline-h2o2ram": 3, "local-baseline-h2o2ram-shipped": 3, "local-baseline-sonic": 4,
                         "local-baseline-std-unordered-map": 3})
        # The harness gate pairs (*-pil1-*): the same saturated rows under each logging mode.
        expected.update({f"{p}-pil1-{m}": 18 for p in ("c4-tdx", "c4-native", "oci-zen5-snp")
                         for m in ("checkpoints", "full-events")})
        for name, count in expected.items():
            with self.subTest(preset=name):
                data = load_json(ROOT / "benchmarks" / "campaigns" / f"{name}.json")
                result = plan(data)
                self.assertEqual(len(result["trials"]), count)
                skipped = [r for r in result["trials"] if r["planning_status"] != "deferred"]
                # The baseline presets carry trial_time models fitted from pilot runs, so
                # their own trial-time cap may prune rows; nothing else is skipped at planning.
                if name.startswith("c4-tdx-baseline-") and not name.endswith("-smoke") and "-pilot-" not in name:
                    self.assertTrue(skipped)
                    self.assertTrue(all(r["skip_reasons"] == ["trial_time_cap"] for r in skipped))
                elif name in ("c4-tdx", "c4-native", "c4-tdx-latency", "c4-native-latency"):
                    # Trial-time models lengthen windows to N accesses. The cap
                    # prunes only 1 KiB rows: at capacity, ones the memory model skips at
                    # resolve anyway; in the latency stage, the hierarchy's at 2^24.
                    # The headline latency stage adds the tree at 2^27 (12 rows: setup
                    # alone takes minutes against the 900 s latency cap).
                    self.assertEqual(len(skipped), 24 if "latency" in name else 8)
                    self.assertTrue(all(r["skip_reasons"] == ["trial_time_cap"]
                                        and r["spec"]["requested_capacity"] >= 2**24
                                        and (r["spec"]["shape"]["value_bytes"] == 1024 or
                                             (r["spec"]["stage"] == "latency-headline-h" and
                                              r["spec"]["overrides"]["scheme"] == "tree"))
                                        for r in skipped))
                else:
                    self.assertEqual(skipped, [])

    def test_oracle_presets_plan_the_c4_matrix(self):
        # Each oci-zen5-snp preset (AMD SEV-SNP) is a copy of its c4-tdx twin that
        # changes only the runtime, name and resources.
        for path in sorted((ROOT / "benchmarks" / "campaigns").glob("oci-zen5-snp-*.json")):
            twin = ROOT / "benchmarks" / "campaigns" / path.name.replace("oci-zen5-snp", "c4-tdx")
            if not twin.exists():
                continue
            with self.subTest(preset=path.stem):
                ours, theirs = plan(load_json(path)), plan(load_json(twin))
                # Source trial ids hash the execution, so only their count is compared.
                key = lambda row: {**{k: v for k, v in row["spec"].items() if k not in ("execution", "resources")},
                                   "rate": row["spec"]["rate"] and {**row["spec"]["rate"], "source_trial_ids":
                                           len(row["spec"]["rate"].get("source_trial_ids", []))}}
                self.assertEqual(sorted(map(json.dumps, map(key, ours["trials"]))),
                                 sorted(map(json.dumps, map(key, theirs["trials"]))))
                self.assertEqual(load_json(path)["execution"]["runtime"], "snp")

    def test_c4_standard_rows_have_dense_keys(self):
        # Rule 4: every backend gets dense keys on the Standard ORAM record.
        for path in (ROOT / "benchmarks" / "campaigns").glob("c4-*.json"):
            for stage in load_json(path)["stages"]:
                for shape in stage["shapes"]:
                    if shape["name"] == "standard-provisional-k4-v8":
                        self.assertEqual(shape.get("key_layout"), "dense", (path.name, stage["name"]))

    def test_c4_control_matches_its_tdx_preset(self):
        # The plain C4 control runs the same matrix and seeds; only the runtime differs.
        for suffix in ("-smoke", "", "-latency", "-value-width", "-pil1-checkpoints", "-pil1-full-events"):
            with self.subTest(preset=suffix):
                tdx = load_json(ROOT / "benchmarks" / "campaigns" / f"c4-tdx{suffix}.json")
                native = load_json(ROOT / "benchmarks" / "campaigns" / f"c4-native{suffix}.json")
                self.assertEqual(tdx["execution"], {"runtime": "tdx", "require_protected": True})
                self.assertEqual(native["execution"], {"runtime": "native", "require_protected": False})
                self.assertEqual({k: v for k, v in tdx.items() if k not in ("name", "execution")},
                                 {k: v for k, v in native.items() if k not in ("name", "execution")})
                self.assertEqual(tdx["resources"]["required_cache_domains"], 1)

    def test_cli_dry_run_and_failure(self):
        command = [sys.executable, "-m", "analysis.oram_bench", "plan", "--config",
                   "benchmarks/campaigns/c4-tdx-smoke.json"]
        success = subprocess.run(command + ["--dry-run"], cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(success.returncode, 0, success.stderr)
        self.assertEqual(json.loads(success.stdout)["status_counts"], {"deferred": 21})
        error = subprocess.run(command + ["--output", "unused", "--dry-run"], cwd=ROOT,
                               capture_output=True, text=True)
        self.assertEqual(error.returncode, 2)
        self.assertIn("mutually exclusive", error.stderr)


class EnvelopeContractTests(unittest.TestCase):
    def test_complete_manifest_needs_evidence(self):
        data = {"schema_version": 1, "trial_id": "t", "attempt_id": "a", "environment_id": "e",
                "resolved_plan_id": "r", "status": "complete", "failure_kind": None, "reason": None,
                "artifacts": [{"path": "events/0000.bin", "sha256": "0" * 64, "bytes": 10}],
                "events": 1, "lost_events": 0, "correctness_verified": True,
                "measurement_begin_ns": 0, "measurement_end_ns": 10, "drain_end_ns": 11}
        decode(Manifest, data)
        for field, value in [("correctness_verified", False), ("lost_events", 1), ("artifacts", []),
                             ("drain_end_ns", None), ("measurement_end_ns", 12)]:
            bad = {**data, field: value}
            with self.subTest(field=field), self.assertRaises(ValidationError):
                decode(Manifest, bad)
        # A complete verification-off trial is valid only when visibly unverified.
        decode(Manifest, {**data, "verification": "off", "correctness_verified": False})
        with self.assertRaises(ValidationError):
            decode(Manifest, {**data, "verification": "off"})
        with self.assertRaises(ValidationError):
            decode(Manifest, {**data, "verification": "sampled"})
        decode(Manifest, {**data, "status": "failed", "failure_kind": "correctness", "correctness_verified": False})
        data["artifacts"][0]["path"] = "../outside"
        with self.assertRaises(ValidationError):
            decode(Manifest, data)

    def test_native_cannot_claim_protected(self):
        data = {"schema_version": 1, "host_identity": "h", "boot_identity": None, "environment_class": "e",
                "runtime": "native", "protected_verified": True, "verification_reference": "claim",
                "cpu_model": None, "physical_cores": None, "allowed_cpus": [], "cache_domains": None,
                "memory_limit_bytes": None, "build_identity": "b", "source_identity": "s",
                "dependency_identity": "d", "clock": "monotonic", "clock_evidence": None,
                "missing_evidence": ["cpu"]}
        with self.assertRaises(ValidationError):
            decode(Environment, data)


class ReducerInputTests(unittest.TestCase):
    def test_relative_names_in_one_directory(self):
        from analysis.oram_bench.campaign import reducer_inputs
        chunks = [Path("/a/worker/events") / f"{i:020d}.bin" for i in range(8420)]
        cwd, names = reducer_inputs(chunks)
        self.assertEqual(cwd, Path("/a/worker/events"))
        self.assertEqual(names[1], f"{1:020d}.bin")
        self.assertLess(sum(len(n) + 1 for n in names), 2**21 // 4)  # far below ARG_MAX, unlike the absolute paths
        self.assertEqual(reducer_inputs([]), (None, []))
        with self.assertRaises(ValidationError):
            reducer_inputs([Path("/a/x.bin"), Path("/b/y.bin")])


class CycleCoverageTests(unittest.TestCase):
    def test_top_level_carries_gate_steady_state(self):
        from analysis.oram_bench.reduction import cycle_coverage
        covered = {"maintenance_coverage": {"carries_by_level": [900, 110, 3]}}
        self.assertEqual(cycle_coverage(covered, 2), "sufficient")
        self.assertEqual(cycle_coverage(covered, 4), "insufficient_cycle_coverage")
        # No public counter (synthetic): unknown, never zero.
        self.assertEqual(cycle_coverage({"maintenance_coverage": None}, 2), "unknown")
        self.assertEqual(cycle_coverage({}, 2), "unknown")


class PublicationGateTests(unittest.TestCase):
    def test_queue_stability_and_blockers(self):
        from analysis.oram_bench.reduction import publication_blockers, queue_stability
        open_loop, saturated = {"arrival": "fixed"}, {"arrival": "saturated"}
        def summary(offered, during, uncensored=True, tail=True):
            return {"offered": offered, "completed_during_horizon": during, "uncensored": uncensored,
                    "response": {"p99_sufficient_samples": tail}}
        self.assertEqual(queue_stability(saturated, {}), "not_applicable")
        self.assertEqual(queue_stability(open_loop, summary(1000, 999)), "stable")
        # rho = 1.1 leaves about 9 % of the horizon's arrivals waiting at T.
        self.assertEqual(queue_stability(open_loop, summary(1100, 1000)), "backlog_growth")
        self.assertEqual(queue_stability(open_loop, summary(1000, 999, uncensored=False)), "overloaded")
        memory = {"paging_status": "no_paging_observed"}
        self.assertEqual(publication_blockers(open_loop, summary(1000, 999), memory, "sufficient", "stable"), [])
        self.assertEqual(publication_blockers(saturated, {}, None, "insufficient_cycle_coverage", "not_applicable"),
                         ["cycle_coverage_insufficient", "paging_unknown"])
        self.assertEqual(publication_blockers(open_loop, summary(1100, 1000, tail=False), memory,
                                              "unknown", "backlog_growth"),
                         ["cycle_coverage_unknown", "queue_backlog_growth", "p99_insufficient_samples"])
        self.assertEqual(publication_blockers({**open_loop, "diagnostic": True}, summary(1000, 999), memory,
                                              "sufficient", "stable"), ["diagnostic_stage"])

    def test_trial_cpu(self):
        from analysis.oram_bench.reduction import trial_cpu
        self.assertIsNone(trial_cpu({}))
        cpu = trial_cpu({"trial_cpu_ns": {"process": 9_000_000_000, "caller_thread": 2_000_000_000,
                                          "telemetry_thread": 1_000_000_000, "wall": 3_000_000_000}})
        self.assertEqual(cpu["library_cpu_seconds"], 6.0)
        self.assertEqual(cpu["library_cores_busy"], 2.0)

    def test_diagnostic_stage_has_its_own_floor_and_keeps_other_ids(self):
        # A low-rate diagnostic stage goes below the 100k floor
        # only through its own minimum_ops_per_second.
        data = config()
        before = {r["trial_id"] for r in plan(data)["trials"]}
        low = {"name": "low", "kind": "latency", "diagnostic": True, "api_modes": ["scalar"],
               "shapes": data["stages"][0]["shapes"], "capacities": [128],
               "candidates": data["stages"][0]["candidates"],
               "rates": {"absolute_ops_per_second": [2000, 200, 20]}}
        data["stages"].append(low)
        with self.assertRaisesRegex(ValidationError, "minimum_ops_per_second"):
            plan(data)
        low["rates"]["minimum_ops_per_second"] = 20
        rows = plan(data)["trials"]
        self.assertTrue(before <= {r["trial_id"] for r in rows})
        self.assertEqual(sorted({r["spec"]["rate"]["ops_per_second"] for r in rows if r["spec"].get("diagnostic")}),
                         [20, 200, 2000])
        self.assertFalse(any("diagnostic" in r["spec"] for r in rows if r["spec"]["stage"] != "low"))


if __name__ == "__main__":
    unittest.main()
