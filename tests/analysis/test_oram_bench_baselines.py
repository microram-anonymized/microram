"""The baseline-backend contract against stub workers.

Baselines (H2O2RAM, SONIC, std::unordered_map; see benchmarks/baselines/) run
through the same campaign harness as the library: their preparation jobs,
build identities, security labels, per-row trial-time models and timeouts are
checked here with stub workers that run no baseline code.
"""
import json
import math
import os
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from test_oram_bench_resolution import configuration, stub_worker  # noqa: E402

from analysis.oram_bench.campaign import read_plan
from analysis.oram_bench.codec import ValidationError, decode, plain
from analysis.oram_bench.planner import expand, timed, write_plan
from analysis.oram_bench.reduction import row_labels, series
from analysis.oram_bench.resolution import (entries, read_resolution, resolve_campaign, resolver_arguments,
                                            verify_side_files)
from analysis.oram_bench.schema import Campaign, Overrides, TrialTimeModel, WorkerResolution, security_label


def envelope(scheme="h2o2ram", policy="baseline_self_placed", requested=None, roles=(0, 10, 10)):
    """A baseline worker's resolved.json: a caller and pool slots, no carries."""
    slots = list(range(len(roles) + 1))
    threads = [{"role": role, "index": sum(r == role for r in roles[:i]), "cpu": slots[i]}
               for i, role in enumerate(roles)]
    request = {"resolver_request_schema_version": 1, "scheme": requested or scheme, "requested_capacity": 65536,
               "key_bytes": 4, "value_bytes": 8, "key_layout": "dense", "max_accesses": 2**32,
               "api_mode": "scalar", "caller_batch_size": 1, "cores": len(slots), "harness_cores": 1,
               "overrides": [], "cache_domains": 1}
    return {"worker_schema_version": 2, "resolver_request": request, "scheme": scheme,
            "requested_capacity": 65536, "actual_capacity": 65536, "policy_identity": "baseline_v1",
            "configuration_key": "baseline-key", "supports_direct_initialization": True,
            "modeled_buffer_bytes": 1 << 20, "carry_period_accesses": [],
            "choices": [{"field": "scheme", "value": scheme, "source": "explicit", "reason": "fixture"}],
            "library_threads": len(threads), "reserved_harness_cores": 1, "placement_verified": False,
            "threads": threads, "placement_policy": policy, "cpu_slots": slots}


def baseline_campaign(candidates, shapes=None, api_modes=("scalar", "batch"), workload=None):
    data = {"schema_version": 1, "name": "baseline-fixture", "repetitions": 1,
            "resources": {"physical_cores": 4},
            "stages": [{"name": "fixture", "kind": "capacity", "capacities": [65536],
                        "shapes": shapes or [
                            {"name": "k4", "key_bytes": 4, "value_bytes": 12, "key_layout": "dense"},
                            {"name": "k8", "key_bytes": 8, "value_bytes": 48}],
                        "candidates": candidates, "api_modes": list(api_modes), "batch_sizes": [64]}]}
    if workload:
        data["workload"] = workload
    return decode(Campaign, data)


def rows_by(plan, *fields):
    return {tuple(row["spec"][f] if f in row["spec"] else row["spec"]["shape"][f] for f in fields): row
            for row in plan["trials"]}


class SchemaTests(unittest.TestCase):
    def test_baseline_schemes_and_their_blocks(self):
        for scheme in ("std_unordered_map", "h2o2ram", "h2o2ram_shipped", "sonic_zingoram",
                       "sonic_zingoram_recursive"):
            decode(Overrides, {"scheme": scheme})
        decode(Overrides, {"scheme": "h2o2ram", "h2o2ram": {"linear_scan_threshold": 256,
                                                            "omp_wait_policy": "passive"}})
        decode(Overrides, {"scheme": "sonic_zingoram_recursive", "sonic": {
            "bucket_real_size": 16, "map_branching_factor": 64, "map_top_entries": 4096}})
        for bad in ({"scheme": "h2o2ram", "incremental": {}},          # a library block on a baseline
                    {"scheme": "tree", "h2o2ram": {}},                    # a baseline block on the library
                    {"scheme": "h2o2ram", "sonic": {}},
                    {"scheme": "sonic_zingoram", "h2o2ram": {}},
                    {"scheme": "h2o2ram", "h2o2ram": {"linear_scan_threshold": 512}},
                    {"scheme": "sonic_zingoram", "sonic": {"stash_bound": 10}},
                    {"scheme": "sonic_zingoram_recursive", "sonic": {"map_branching_factor": 8}}):
            with self.subTest(bad=bad), self.assertRaises(ValidationError):
                decode(Overrides, bad)

    def test_security_labels(self):
        self.assertEqual({s: security_label(s) for s in (
            "auto", "tree", "hierarchical_incremental", "h2o2ram", "sonic_zingoram_recursive", "sonic_zingoram",
            "h2o2ram_shipped", "std_unordered_map", "fake", "noop")}, {
            "auto": "oblivious", "tree": "oblivious", "hierarchical_incremental": "oblivious",
            "h2o2ram": "oblivious", "sonic_zingoram_recursive": "oblivious",
            "sonic_zingoram": "oblivious_position_map_outside", "h2o2ram_shipped": "not_oblivious",
            "std_unordered_map": "not_oblivious", "fake": "not_oblivious", "noop": "not_oblivious"})

    def test_worker_resolution_accepts_baseline_envelopes(self):
        for scheme in ("h2o2ram", "h2o2ram_shipped", "sonic_zingoram", "sonic_zingoram_recursive"):
            resolved = decode(WorkerResolution, envelope(scheme))
            self.assertEqual((resolved.placement_policy, resolved.carry_period_accesses),
                             ("baseline_self_placed", []))
        decode(WorkerResolution, envelope("std_unordered_map", "near_far_v2", roles=(0,)))
        decode(WorkerResolution, envelope("h2o2ram", "unplaced") | {
            "cpu_slots": [], "threads": [{"role": 0, "index": 0, "cpu": None}], "library_threads": 1})
        bad = [envelope("h2o2ram", requested="auto"),                 # rule 10
               envelope("tree", roles=(0, 10)),                        # pool slots are a baseline's
               envelope("std_unordered_map", roles=(0, 10)),            # the hash map is one thread
               envelope("tree", roles=(0, 4)),                          # only baselines place themselves
               envelope("h2o2ram", roles=(0, 10, 10)) | {"cpu_slots": [3, 2, 1, 0]}]
        for document in bad:
            with self.subTest(document=document["scheme"]), self.assertRaises(ValidationError):
                decode(WorkerResolution, document)

    def test_bottom_helper_roles_do_not_alias_baseline_pool_slots(self):
        for scheme, role in (("hierarchical_incremental", 11), ("tree", 12)):
            document = envelope(scheme, "near_far_v2", roles=(0, role))
            self.assertEqual(decode(WorkerResolution, document).threads[1].role, role)
            with self.assertRaises(ValidationError):
                decode(WorkerResolution, envelope("h2o2ram", roles=(0, role)))
            with self.assertRaises(ValidationError):
                decode(WorkerResolution, envelope(scheme, "near_far_v2", roles=(0, 10)))


class PlannerTests(unittest.TestCase):
    def test_rows_carry_labels(self):
        candidates = [{"name": name, "overrides": {"scheme": name}} for name in
                      ("auto", "std_unordered_map", "h2o2ram", "h2o2ram_shipped", "sonic_zingoram",
                       "sonic_zingoram_recursive")]
        plan = expand(baseline_campaign(candidates, api_modes=("scalar",)))
        rows = rows_by(plan, "candidate", "name")
        for (candidate, shape), row in rows.items():
            self.assertEqual(row["security"], security_label(candidate))
            self.assertEqual(row["key_layout"], "dense" if shape == "k4" else "permuted")
        # Rule 5: ZingORAM blocks are multiples of 8 bytes; the others store the width.
        self.assertEqual(rows[("sonic_zingoram", "k4")]["stored_value_bytes"], 16)
        self.assertEqual(rows[("h2o2ram", "k4")]["stored_value_bytes"], 12)
        self.assertEqual(rows[("auto", "k8")]["stored_value_bytes"], 48)

    def test_skip_reasons(self):
        candidates = [{"name": name, "overrides": {"scheme": name}} for name in
                      ("tree", "std_unordered_map", "h2o2ram", "sonic_zingoram")]
        plan = expand(baseline_campaign(candidates))
        rows = rows_by(plan, "candidate", "name", "api_mode")
        self.assertEqual(rows[("h2o2ram", "k4", "batch")]["skip_reasons"], ["unsupported_api_mode"])
        self.assertEqual(rows[("sonic_zingoram", "k8", "scalar")]["skip_reasons"], ["sonic_needs_dense_keys"])
        for runnable in (("tree", "k4", "batch"), ("sonic_zingoram", "k4", "batch"), ("h2o2ram", "k8", "scalar"),
                         ("std_unordered_map", "k4", "scalar"), ("std_unordered_map", "k8", "batch")):
            self.assertEqual(rows[runnable]["planning_status"], "deferred", runnable)
        # Rule 6: an index ORAM cannot report a miss.
        misses = {"read_ppm": 1_000_000, "hit_ppm": 500_000, "miss_key_count": 1000}
        plan = expand(baseline_campaign(candidates, api_modes=("scalar",), workload=misses))
        rows = rows_by(plan, "candidate", "name")
        for scheme in ("h2o2ram", "sonic_zingoram"):
            self.assertIn("index_oram_cannot_report_misses", rows[(scheme, "k4")]["skip_reasons"])
        for scheme in ("tree", "std_unordered_map"):
            self.assertEqual(rows[(scheme, "k4")]["skip_reasons"], [])

    def test_dense_keys_reach_the_resolver_and_permuted_arguments_are_unchanged(self):
        plan = expand(baseline_campaign([{"name": "tree", "overrides": {"scheme": "tree"}}],
                                        api_modes=("scalar",)))
        rows = rows_by(plan, "name")
        dense = resolver_arguments(rows[("k4",)], False)
        self.assertEqual(dense[dense.index("--key-layout") + 1], "dense")
        self.assertNotIn("--key-layout", resolver_arguments(rows[("k8",)], False))
        # A shape without the field is permuted, as plans made before it were.
        old = decode(Campaign, {**plain(baseline_campaign([{"name": "tree", "overrides": {"scheme": "tree"}}])),
                                "name": "old"})
        self.assertEqual({s.key_layout for s in old.stages[0].shapes}, {"dense", "permuted"})


class SideFileTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = Path(self.directory.name)
        self.worker = stub_worker(self.root)
        os.environ["STUB_WORKER_LOG"] = str(self.root / "calls.jsonl")
        (self.root / "hash_map.bin16").write_text("65536 65536 64 two_tier 8\n")

    def tearDown(self):
        os.environ.pop("STUB_SIDE_FILES", None)
        self.directory.cleanup()

    def campaign(self, name):
        path = self.root / name
        write_plan(expand(decode(Campaign, configuration(repetitions=1))), path)
        return path

    def test_declared_side_files_are_frozen_and_checked(self):
        os.environ["STUB_SIDE_FILES"] = "hash_map.bin16"
        campaign = self.campaign("frozen")
        resolve_campaign(campaign, self.worker)
        build = json.loads((campaign / "build/build.json").read_text())
        [item] = build["side_files"]
        self.assertEqual(item["name"], "hash_map.bin16")
        self.assertEqual((campaign / "build/hash_map.bin16").read_bytes(),
                         (self.root / "hash_map.bin16").read_bytes())
        self.assertEqual(build["build_info"]["baseline"], "stub")
        resolve_campaign(campaign, self.worker)  # idempotent
        # A new planner cache beside the same worker needs a new campaign.
        (self.root / "hash_map.bin16").write_text("65536 65536 64 cuckoo\n")
        with self.assertRaisesRegex(ValidationError, "side files differ"):
            resolve_campaign(campaign, self.worker)
        # A frozen cache edited in place is refused before any launch.
        (campaign / "build/hash_map.bin16").write_text("tampered\n")
        with self.assertRaisesRegex(ValidationError, "frozen side file hash_map.bin16 changed"):
            verify_side_files(campaign / "build", build)

    def test_unsafe_or_missing_side_files_are_refused(self):
        for names, error in (("../escape", "unsafe"), ("worker", "unsafe"), ("absent.bin", "absent.bin")):
            os.environ["STUB_SIDE_FILES"] = names
            with self.subTest(names=names), self.assertRaisesRegex((ValidationError, OSError), error):
                resolve_campaign(self.campaign("bad-" + names.replace("/", "_").replace(".", "_")), self.worker)

    def test_workers_without_build_info_freeze_no_side_files(self):
        campaign = self.campaign("plain")
        resolve_campaign(campaign, self.worker)
        build = json.loads((campaign / "build/build.json").read_text())
        self.assertNotIn("side_files", build)
        verify_side_files(campaign / "build", build)


class TimeCapTests(unittest.TestCase):
    """Trial-time models: per-row windows and caps from an arm's time model."""
    def plan(self, capacities, model):
        data = {"schema_version": 1, "name": "time-cap", "repetitions": 1,
                "timing": {"warmup_ns": 0, "measurement_ns": 10**9, "drain_deadline_ns": 10**9,
                           "setup_allowance_ns": 10**9, "max_trial_ns": 100 * 10**9},
                "stages": [{"name": "capacity", "kind": "capacity", "capacities": capacities,
                            "shapes": [{"name": "k8", "key_bytes": 8, "value_bytes": 48}],
                            "candidates": [{"name": "h2o2ram", "overrides": {"scheme": "h2o2ram"},
                                            **({"trial_time": model if type(model) is list else [model]}
                                               if model else {})},
                                           {"name": "tree", "overrides": {"scheme": "tree"}}],
                            "api_modes": ["scalar"]}]}
        return rows_by(expand(decode(Campaign, data)), "candidate", "requested_capacity")

    def test_windows_grow_with_coverage_and_the_cap_prunes(self):
        model = {"setup_ns_per_entry": 50, "access_ns": 100, "coverage_accesses_per_entry_ppm": 2_000_000}
        rows = self.plan([2**16, 2**24, 2**29], model)
        small, large, pruned = (rows[("h2o2ram", n)] for n in (2**16, 2**24, 2**29))
        self.assertEqual(small["spec"]["timing"]["measurement_ns"], 10**9)  # coverage (13 ms) fits the window
        self.assertEqual(large["spec"]["timing"]["measurement_ns"], 2 * 2**24 * 100)  # two top rebuilds
        self.assertEqual(large["estimated_trial_ns"], 50 * 2**24 + 2 * 2**24 * 100 + 10**9)
        self.assertEqual((small["planning_status"], large["planning_status"]), ("deferred", "deferred"))
        self.assertEqual(pruned["skip_reasons"], ["trial_time_cap"])  # 26.8 s setup + 107 s window > 100 s
        # Arms without a model keep the campaign's window and have no estimate.
        tree = rows[("tree", 2**29)]
        self.assertEqual((tree["spec"]["timing"]["measurement_ns"], tree["estimated_trial_ns"]), (10**9, None))
        self.assertEqual(tree["skip_reasons"], [])

    def test_a_coverage_window_needs_an_access_time(self):
        with self.assertRaises(ValidationError):
            self.plan([2**16], {"coverage_accesses_per_entry_ppm": 2_000_000})

    def test_access_and_setup_scale_with_capacity(self):
        # Doubling capacity costs 1.25x per access: exponent log2(1.25) = 0.321928.
        model = {"setup_ns_per_entry": 1000, "access_ns": 4000, "coverage_accesses_per_entry_ppm": 2_000_000,
                 "reference_capacity": 2**20, "capacity_exponent_ppm": 321928}
        rows = self.plan([2**20, 2**22, 2**24], model)
        at, above = rows[("h2o2ram", 2**20)], rows[("h2o2ram", 2**22)]
        self.assertEqual(at["spec"]["timing"]["measurement_ns"], 2 * 2**20 * 4000)
        self.assertEqual(at["estimated_trial_ns"], 1000 * 2**20 + 2 * 2**20 * 4000 + 10**9)
        window = above["spec"]["timing"]["measurement_ns"]
        self.assertAlmostEqual(window / (2 * 2**22 * 4000), 1.5625, places=5)  # 1.25^2
        self.assertEqual(above["skip_reasons"], [])  # 6.6 s setup + 52 s window + 1 s drain
        self.assertEqual(rows[("h2o2ram", 2**24)]["skip_reasons"], ["trial_time_cap"])  # 41 s + 328 s + 1 s
        self.assertAlmostEqual((above["estimated_trial_ns"] - window - 10**9) / (1000 * 2**22), 1.5625, places=5)

    def test_a_model_per_width_and_a_fallback(self):
        models = [{"access_ns": 100, "coverage_accesses_per_entry_ppm": 1_000_000},
                  {"access_ns": 1000, "coverage_accesses_per_entry_ppm": 1_000_000, "value_bytes": 48}]
        data = {"schema_version": 1, "name": "per-width", "repetitions": 1,
                "timing": {"warmup_ns": 0, "measurement_ns": 1, "drain_deadline_ns": 1,
                           "setup_allowance_ns": 1, "max_trial_ns": 10**12},
                "stages": [{"name": "capacity", "kind": "capacity", "capacities": [2**20],
                            "shapes": [{"name": "k8", "key_bytes": 8, "value_bytes": 48},
                                       {"name": "k8v8", "key_bytes": 8, "value_bytes": 8}],
                            "candidates": [{"name": "h2o2ram", "overrides": {"scheme": "h2o2ram"},
                                            "trial_time": models}],
                            "api_modes": ["scalar"]}]}
        rows = rows_by(expand(decode(Campaign, data)), "value_bytes")
        self.assertEqual(rows[(48,)]["spec"]["timing"]["measurement_ns"], 2**20 * 1000)
        self.assertEqual(rows[(8,)]["spec"]["timing"]["measurement_ns"], 2**20 * 100)
        # Without the fallback, the 8-byte row has no model, which planning refuses.
        data["stages"][0]["candidates"][0]["trial_time"] = models[1:]
        with self.assertRaisesRegex(ValidationError, "no trial_time model covers"):
            expand(decode(Campaign, data))
        # Two models for one width are refused, and so is a tie between two selectors.
        data["stages"][0]["candidates"][0]["trial_time"] = [models[1], models[1]]
        with self.assertRaises(ValidationError):
            decode(Campaign, data)
        data["stages"][0]["candidates"][0]["trial_time"] = [{**models[0], "key_bytes": 8}, models[1]]
        with self.assertRaisesRegex(ValidationError, "tie"):
            expand(decode(Campaign, data))

    def test_offered_load_rows_cover_their_window_at_the_offered_rate(self):
        model = {"access_ns": 5000, "coverage_accesses_per_entry_ppm": 2_000_000}
        data = {"schema_version": 1, "name": "latency-cap", "repetitions": 1,
                "timing": {"warmup_ns": 0, "measurement_ns": 10**9, "drain_deadline_ns": 10**9,
                           "setup_allowance_ns": 10**9, "max_trial_ns": 600 * 10**9},
                "stages": [{"name": "latency", "kind": "latency", "capacities": [2**20],
                            "shapes": [{"name": "k8", "key_bytes": 8, "value_bytes": 48}],
                            "candidates": [{"name": "h2o2ram", "overrides": {"scheme": "h2o2ram"},
                                            "trial_time": [model]}],
                            "api_modes": ["scalar"],
                            "rates": {"absolute_ops_per_second": [1000, 10**6],
                                      "saturation_fractions_ppm": [100_000],
                                      "minimum_ops_per_second": 1000}}]}
        rows = {(r["spec"]["arrival"], json.dumps(r["spec"]["rate"], sort_keys=True)): r
                for r in expand(decode(Campaign, data))["trials"]}
        by_rate = {}
        for (arrival, rate), row in rows.items():
            rate = json.loads(rate)
            key = "saturated" if rate is None else rate.get("ops_per_second") or rate["fraction_ppm"]
            by_rate[key] = row
        saturated = 2 * 2**20 * 5000  # 10.5 s at the arm's own rate
        self.assertEqual(by_rate["saturated"]["spec"]["timing"]["measurement_ns"], saturated)
        # Faster than the arm can go: it still runs at its own rate.
        self.assertEqual(by_rate[10**6]["spec"]["timing"]["measurement_ns"], saturated)
        # 2^21 accesses at 1,000/s is 35 minutes, over the 10-minute cap.
        self.assertEqual(by_rate[1000]["estimated_trial_ns"], 2 * 2**20 * 10**6 + 10**9)  # window + drain
        self.assertEqual(by_rate[1000]["skip_reasons"], ["trial_time_cap"])
        # A tenth of saturation takes ten times the saturated window.
        self.assertEqual(by_rate[100_000]["spec"]["timing"]["measurement_ns"], 10 * saturated)
        self.assertEqual(by_rate[100_000]["skip_reasons"], [])

    def test_a_batch_model_beside_the_scalar_one(self):
        data = {"schema_version": 1, "name": "per-api", "repetitions": 1,
                "timing": {"warmup_ns": 0, "measurement_ns": 1, "drain_deadline_ns": 1,
                           "setup_allowance_ns": 1, "max_trial_ns": 10**12},
                "stages": [{"name": "capacity", "kind": "capacity", "capacities": [2**20],
                            "shapes": [{"name": "k4", "key_bytes": 4, "value_bytes": 8, "key_layout": "dense"}],
                            "candidates": [{"name": "zing", "overrides": {"scheme": "sonic_zingoram"},
                                            "trial_time": [{"setup_ns_per_entry": 5000},
                                                           {"setup_ns_per_entry": 1000, "api_mode": "batch"}]}],
                            "api_modes": ["scalar", "batch"], "batch_sizes": [64]}]}
        rows = rows_by(expand(decode(Campaign, data)), "api_mode")
        self.assertEqual(rows[("scalar",)]["estimated_trial_ns"], 5000 * 2**20 + 2)
        self.assertEqual(rows[("batch",)]["estimated_trial_ns"], 1000 * 2**20 + 2)

    def test_a_capacity_exponent_needs_its_reference(self):
        with self.assertRaises(ValidationError):
            self.plan([2**16], {"access_ns": 1, "capacity_exponent_ppm": 1})


class FitTrialTimeTests(unittest.TestCase):
    def record(self, capacity, access_ns, setup_ns, scheme="h2o2ram", api="scalar", value=48):
        return {"candidate": scheme, "scheme": scheme, "key_bytes": 8, "value_bytes": value, "api_mode": api,
                "capacity": capacity, "live_entries": capacity, "access_ns": access_ns, "setup_ns": setup_ns}

    def test_the_largest_pilot_is_the_reference_and_the_steeper_slope_extrapolates(self):
        from analysis.oram_bench.pilots import fit_trial_time
        records = [self.record(2**16, 4000, 2**16 * 100), self.record(2**18, 5000, 2**18 * 100),
                   self.record(2**20, 6250, 2**20 * 150)]
        [model] = fit_trial_time(records, margin_ppm=0)["h2o2ram"]
        self.assertEqual((model["reference_capacity"], model["access_ns"], model["setup_ns_per_entry"]),
                         (2**20, 6250, 150))
        # Access grew 1.25x over 4x (exponent 0.161); setup per entry 1.5x (0.292), the steeper.
        self.assertEqual(model["capacity_exponent_ppm"], round(math.log(1.5) / math.log(4) * 1e6))
        self.assertEqual(model["coverage_accesses_per_entry_ppm"], 2_000_000)
        # The fitted model plans: the row at the reference measures its two top rebuilds.
        timed_spec, _ = timed({"timing": {"measurement_ns": 1, "warmup_ns": 0, "drain_deadline_ns": 1},
                               "requested_capacity": 2**20}, decode(TrialTimeModel, model), 2**20)
        self.assertEqual(timed_spec["timing"]["measurement_ns"], 2 * 2**20 * 6250)

    def test_one_model_per_width_and_api_with_the_margin(self):
        from analysis.oram_bench.pilots import fit_trial_time
        records = [self.record(2**16, 1000, 2**16 * 10, scheme="sonic_zingoram"),
                   self.record(2**16, 400, 2**16 * 4, scheme="sonic_zingoram", api="batch"),
                   self.record(2**16, 2000, 2**16 * 10, scheme="sonic_zingoram", value=1024)]
        models = fit_trial_time(records, margin_ppm=250_000)["sonic_zingoram"]
        self.assertEqual(sorted((m["value_bytes"], m["api_mode"], m["access_ns"]) for m in models),
                         [(48, "batch", 500), (48, "scalar", 1250), (1024, "scalar", 2500)])
        self.assertTrue(all("coverage_accesses_per_entry_ppm" not in m and m["capacity_exponent_ppm"] == 0
                            for m in models))

    def test_a_width_piloted_once_borrows_its_candidates_steepest_exponent(self):
        from analysis.oram_bench.pilots import fit_trial_time
        records = [self.record(2**16, 4000, 2**16 * 100), self.record(2**18, 8000, 2**18 * 100),
                   self.record(2**18, 90000, 2**18 * 900, value=4096),
                   self.record(2**16, 900, 2**16 * 9, api="batch", value=4096)]
        models = {(m["value_bytes"], m["api_mode"]): m for m in fit_trial_time(records, margin_ppm=0)["h2o2ram"]}
        self.assertEqual(models[(48, "scalar")]["capacity_exponent_ppm"], 500_000)  # 2x over 4x
        self.assertEqual(models[(4096, "scalar")]["capacity_exponent_ppm"], 500_000)
        self.assertEqual(models[(4096, "batch")]["capacity_exponent_ppm"], 0)  # nothing to borrow at batch


class ApplyTrialTimeTests(unittest.TestCase):
    fitted = {"h2o2ram": [
        {"key_bytes": 8, "value_bytes": 8, "api_mode": "scalar", "access_ns": 1000, "setup_ns_per_entry": 100,
         "reference_capacity": 2**20, "capacity_exponent_ppm": 250_000, "coverage_accesses_per_entry_ppm": 2_000_000},
        {"key_bytes": 8, "value_bytes": 1016, "api_mode": "scalar", "access_ns": 100_000, "setup_ns_per_entry": 10_000,
         "reference_capacity": 2**18, "capacity_exponent_ppm": 500_000, "coverage_accesses_per_entry_ppm": 2_000_000}]}

    def preset(self):
        widths = (8, 120, 1016)
        return {"stages": [{"name": "vw", "kind": "value_width", "capacities": [2**20], "api_modes": ["scalar"],
                            "shapes": [{"name": f"v{v}", "key_bytes": 8, "value_bytes": v} for v in widths],
                            "candidates": [{"name": "h", "overrides": {"scheme": "h2o2ram"}},
                                           {"name": "ours", "overrides": {"scheme": "tree"}}]}]}

    def test_piloted_widths_copy_and_others_interpolate_in_block_bytes(self):
        from analysis.oram_bench.pilots import apply_trial_time
        stage = apply_trial_time(self.preset(), self.fitted)["stages"][0]
        models = {m["value_bytes"]: m for m in stage["candidates"][0]["trial_time"]}
        self.assertEqual(models[8], self.fitted["h2o2ram"][0])
        self.assertEqual(models[1016], self.fitted["h2o2ram"][1])
        # Blocks 16 and 1024 B bracket 128 B, half way in log; the 1 KiB model is 2x at 2^20.
        middle = models[120]
        self.assertEqual(middle["reference_capacity"], 2**20)
        self.assertAlmostEqual(middle["access_ns"], math.sqrt(1000 * 200_000), delta=1)
        self.assertEqual(middle["coverage_accesses_per_entry_ppm"], 2_000_000)
        # A scheme the pilot did not fit keeps what it had.
        self.assertNotIn("trial_time", stage["candidates"][1])

    def test_the_applied_preset_plans(self):
        from analysis.oram_bench.pilots import apply_trial_time
        preset = {"schema_version": 1, "name": "applied", "repetitions": 1,
                  "timing": {"warmup_ns": 0, "measurement_ns": 10**9, "drain_deadline_ns": 10**9,
                             "setup_allowance_ns": 10**9, "max_trial_ns": 300 * 10**9},
                  **apply_trial_time(self.preset(), self.fitted)}
        preset["stages"][0]["candidates"].pop()
        rows = rows_by(expand(decode(Campaign, preset)), "value_bytes")
        self.assertEqual(rows[(8,)]["spec"]["timing"]["measurement_ns"], 2 * 2**20 * 1000)
        # 200 us an access at 2^20: a 419 s window and 21 s of setup, over the 300 s cap.
        self.assertEqual(rows[(1016,)]["skip_reasons"], ["trial_time_cap"])


class PrepareTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = Path(self.directory.name)
        self.worker = stub_worker(self.root)
        self.log = self.root / "calls.jsonl"
        os.environ["STUB_WORKER_LOG"] = str(self.log)
        for name in ("STUB_PREPARE_FAIL_AT", "STUB_PREPARE_SLEEP"):
            os.environ.pop(name, None)

    def tearDown(self):
        for name in ("STUB_PREPARE_FAIL_AT", "STUB_PREPARE_SLEEP"):
            os.environ.pop(name, None)
        self.directory.cleanup()

    def prepare(self, capacities=(128,), values=(8,), candidates=("h2o2ram", "h2o2ram_shipped", "tree"),
                resources=None, timeout=None, name="campaign", job_timeout=None):
        from analysis.oram_bench.baselines import prepare_h2o2ram
        data = configuration([{"name": name, "overrides": {"scheme": name}} for name in candidates],
                             resources=resources, repetitions=2)
        data["stages"][0].update({"kind": "capacity", "capacities": list(capacities),
                                  "shapes": [{"name": f"v{v}", "key_bytes": 8, "value_bytes": v} for v in values]})
        campaign = self.root / name
        if not campaign.exists():
            write_plan(expand(decode(Campaign, data)), campaign)
        return campaign, prepare_h2o2ram(campaign, self.worker, timeout, job_timeout)

    def calls(self):
        return [dict(zip(c[::2], c[1::2])) for c in map(json.loads, self.log.read_text().splitlines())]

    def test_each_distinct_row_is_prepared_once_with_the_patched_scheme(self):
        _, result = self.prepare()
        # Two schemes x two repetitions, one set of planner inputs: one call.
        [call] = self.calls()
        self.assertEqual((call["--scheme"], call["--prepare-planner"]), ("h2o2ram", "1"))
        self.assertEqual(result["counts"], {"prepared": 1})
        [row] = result["rows"]
        self.assertEqual((row["planner_ns"], row["capacity"]), (128, 128))
        self.assertGreater(row["peak_rss_bytes"], 0)

    def test_rows_run_small_to_large_and_a_failure_stops_only_its_block_size(self):
        os.environ["STUB_PREPARE_FAIL_AT"] = "4096"
        _, result = self.prepare(capacities=(16384, 128, 4096, 1024), values=(48, 8))
        order = [(int(c["--value-bytes"]), int(c["--capacity"])) for c in self.calls()]
        # The plan order is shuffled; the calls are not, and nothing past a failure runs.
        self.assertEqual(order, [(8, 128), (8, 1024), (8, 4096), (48, 128), (48, 1024), (48, 4096)])
        status = {(r["value_bytes"], r["capacity"]): r["status"] for r in result["rows"]}
        self.assertEqual(status[(8, 4096)], "failed")
        self.assertEqual(status[(8, 16384)], "not_attempted")
        self.assertEqual(result["counts"], {"prepared": 4, "failed": 2, "not_attempted": 2})
        self.assertIn("bad_alloc", {r["error"] for r in result["rows"] if r["status"] == "failed"}.pop())

    def test_a_row_past_its_timeout_is_killed_and_recorded(self):
        os.environ["STUB_PREPARE_SLEEP"] = "30"
        _, result = self.prepare(timeout=0.5)
        [row] = result["rows"]
        self.assertEqual(row["status"], "timeout")
        self.assertLess(row["wall_ns"], 20 * 10**9)

    def test_the_job_stops_at_its_wall_time_cap(self):
        # An optional cap on the whole preparation job, not only each row (none by default).
        os.environ["STUB_PREPARE_SLEEP"] = "30"
        _, result = self.prepare(values=(8, 48), job_timeout=0.5)
        self.assertEqual([r["status"] for r in result["rows"]], ["timeout", "not_attempted"])
        self.assertEqual(result["rows"][1]["error"], "job wall-time cap reached")
        with self.assertRaisesRegex(ValidationError, "positive"):
            self.prepare(name="zero", job_timeout=0)

    def test_the_child_is_capped_at_the_host_headroom(self):
        _, result = self.prepare(resources={"host_memory_limit_bytes": 10 * 2**30})
        [row] = result["rows"]
        self.assertEqual(row["memory_limit_bytes"], 8 * 2**30)  # the default 20% headroom
        self.assertEqual(row["stub_rlimit_as"], 8 * 2**30)
        _, unlimited = self.prepare(name="no-limit")
        self.assertIsNone(unlimited["rows"][0]["memory_limit_bytes"])

    def test_each_run_appends_to_the_campaign_record(self):
        campaign, _ = self.prepare()
        self.prepare()
        record = json.loads((campaign / "prepare_h2o2ram.json").read_text())
        self.assertEqual([run["counts"] for run in record["runs"]], [{"prepared": 1}, {"prepared": 1}])
        self.assertEqual(record["plan_id"], read_plan(campaign)["plan_id"])


class ReductionLabelTests(unittest.TestCase):
    def test_labels_come_from_the_row_and_a_rehearsal_is_not_oblivious(self):
        plan = expand(baseline_campaign([{"name": "s", "overrides": {"scheme": "sonic_zingoram"}}],
                                        api_modes=("scalar",)))
        row = rows_by(plan, "name")[("k4",)]
        self.assertEqual(row_labels(row, {"security": "oblivious_position_map_outside"}),
                         {"security": "oblivious_position_map_outside", "position_lookup": "included",
                          "key_layout": "dense", "stored_value_bytes": 16})
        self.assertEqual(row_labels(row, {"security": "not_oblivious"})["security"], "not_oblivious")
        # A plan made before the labels: a library row with permuted keys.
        old = {"spec": {"shape": {"value_bytes": 8}}}
        self.assertEqual(row_labels(old, None), {"security": "oblivious", "position_lookup": None,
                                                 "key_layout": "permuted", "stored_value_bytes": 8})

    def test_series_print_the_security_label(self):
        group = {"spec": {"candidate": "h2o2ram_shipped", "api_mode": "scalar"}, "build_identity": "sha256-ab",
                 "runtime": "tdx", "group_id": "group-12345678", "security": "not_oblivious"}
        [(label, _, _, _)] = series([{"campaign": {"name": "c"}, "groups": [group]}])
        self.assertIn("/ not_oblivious /", label)
        # Both SONIC rows say their position lookup is inside the access.
        sonic = {**group, "spec": {"candidate": "sonic_zingoram", "api_mode": "scalar"},
                 "security": "oblivious_position_map_outside", "position_lookup": "included"}
        [(label, _, _, found)] = series([{"campaign": {"name": "c"}, "groups": [sonic]}])
        self.assertIn("/ oblivious_position_map_outside /", label)
        self.assertIn("position lookup included", label)
        self.assertIn("position lookup included", found["family"])

    def test_a_synthetic_resolution_labels_every_row_not_oblivious(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            worker = stub_worker(root)
            os.environ["STUB_WORKER_LOG"] = str(root / "calls.jsonl")
            campaign = root / "campaign"
            write_plan(expand(decode(Campaign, configuration(repetitions=1))), campaign)
            resolve_campaign(campaign, worker, synthetic=True)
            plan = read_plan(campaign)
            self.assertEqual({e["security"] for e in entries(read_resolution(campaign, plan)).values()},
                             {"not_oblivious"})
            self.assertEqual({row["security"] for row in plan["trials"]}, {"oblivious"})


if __name__ == "__main__":
    unittest.main()
