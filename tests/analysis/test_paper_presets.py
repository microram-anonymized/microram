"""The paper preset family (benchmarks/campaigns/paper/) and the planner's per-row settle option.

Planning only: every preset validates and expands to its expected rows with nothing skipped, its twins plan
the same matrix, and the settings the measured rows ran with hold row by row. The rehearsal copies plan too.
No ORAM construction or measurement.
"""

import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

from analysis.oram_bench.codec import ValidationError, decode, json_schema, load_json
from analysis.oram_bench.planner import expand
from analysis.oram_bench.resolution import trial_arguments
from analysis.oram_bench.schema import Campaign

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / "benchmarks" / "campaigns" / "paper"
GENERATOR = PAPER / "make_presets.py"

# Rows per item (one repetition); every target of an item plans the same count.
EXPECTED_ROWS = {
    "throughput-k4v8": 60,              # ours scalar 15 + batch 14 + batch 2^30 1, hash map scalar 15 + batch 15
    "table1-scalar": 13,                # ours K4/V8 sat + 0.5 + 0.8, K8/V48 and K32 sat + 0.5; hash map 3 x 2
    "table1-batch": 12,                 # ours and hash map at three shapes, sat + 0.5 each
    "width": 24,                        # 11 widths x (frozen hierarchy, tree) + tree at 2 and 4 KiB
    "width-hierarchy-wide": 2,
    "width-std-unordered-map": 10,
    "tee": 2,                           # scalar, 8 x 8 batch 64
    "baseline-h2o2ram-table": 6,
    "baseline-h2o2ram-throughput": 12,
    "baseline-h2o2ram-shipped-throughput": 11,
    "baseline-h2o2ram-width": 7,
    "baseline-h2o2ram-width-large": 2,
    "baseline-sonic-table-scalar": 6,
    "baseline-sonic-table-batch": 6,
    "baseline-sonic-throughput": 24,
    "baseline-sonic-width": 10,
}
TARGETS = ("c4-tdx", "c4-native", "oci-zen5-snp", "oci-e6-native")
ONLY_ON = {"tee": TARGETS, "baseline-h2o2ram-width-large": ("oci-zen5-snp",)}
CANDIDATES = {"auto", "parallel-8x8", "hierarchy-frozen", "tree", "std_unordered_map",
              "h2o2ram", "h2o2ram_shipped", "sonic_zingoram_recursive"}
# One worker binary resolves a campaign: the library's (with std::unordered_map), H2O2RAM's or SONIC's.
WORKERS = ({"auto", "hierarchical_incremental", "tree", "std_unordered_map"}, {"h2o2ram"}, {"h2o2ram_shipped"},
           {"sonic_zingoram_recursive"})
SONIC = "sonic_zingoram_recursive"
SPIN = 1_000_000_000
N21 = 1 << 21
MIB = 1 << 20


def plan(data):
    return expand(decode(Campaign, data))


def split(stem):
    for target in TARGETS:
        if stem.startswith(target + "-"):
            return target, stem[len(target) + 1:]
    raise AssertionError(f"{stem}: no known target prefix")


def preset_paths():
    return sorted(PAPER.glob("*.json"))


class PlanCache:
    plans = {}

    @classmethod
    def get(cls, path):
        if path not in cls.plans:
            cls.plans[path] = plan(load_json(path))
        return cls.plans[path]


# The one documented exception to identical twin matrices: these stages keep each machine's own window model
# (make_presets.UNORDERED_MAP_SWEEP_MODELS), so their trial_time models and windows differ.
TWIN_MODEL_EXCEPTIONS = {"throughput-k4v8": {"floor", "floor-batch64"}}


def twin_key(row, model_exceptions=()):
    """A row with its execution and resources dropped (source trial ids hash them, so only their count)."""
    spec = row["spec"]
    rate = spec["rate"]
    if spec["stage"] in model_exceptions:
        spec = {**spec, "timing": {k: v for k, v in spec["timing"].items() if k != "measurement_ns"}}
    return json.dumps({**{k: v for k, v in spec.items() if k not in ("execution", "resources")},
                       "rate": rate and {**rate, "source_trial_ids": len(rate.get("source_trial_ids", []))}},
                      sort_keys=True)


def without_models(data, stages):
    """The campaign with the trial_time models of the named stages dropped."""
    data = json.loads(json.dumps(data))
    for stage in data["stages"]:
        if stage["name"] in stages:
            for cand in stage["candidates"]:
                cand.pop("trial_time", None)
    return data


class GeneratorTests(unittest.TestCase):
    def test_committed_files_match_the_generator(self):
        result = subprocess.run([sys.executable, str(GENERATOR), "--check"], cwd=ROOT, capture_output=True,
                                text=True, env={"PYTHONDONTWRITEBYTECODE": "1"})
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_family_is_complete(self):
        expected = {f"{target}-{item}" for item in EXPECTED_ROWS
                    for target in ONLY_ON.get(item, ("c4-tdx", "oci-zen5-snp"))}
        self.assertEqual({path.stem for path in preset_paths()}, expected)


class PresetPlanTests(unittest.TestCase):
    def test_every_preset_plans_its_rows_without_skips(self):
        for path in preset_paths():
            with self.subTest(preset=path.stem):
                data = load_json(path)
                self.assertEqual(data["name"], path.stem)
                self.assertEqual(data["repetitions"], 1)
                rows = PlanCache.get(path)["trials"]
                self.assertEqual(len(rows), EXPECTED_ROWS[split(path.stem)[1]])
                self.assertEqual(data["limits"]["max_trials"], len(rows))
                self.assertEqual([r["skip_reasons"] for r in rows if r["planning_status"] != "deferred"], [])

    def test_cli_dry_run(self):
        command = [sys.executable, "-m", "analysis.oram_bench", "plan", "--dry-run", "--config",
                   str(PAPER / "c4-tdx-tee.json")]
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                                env={"PYTHONDONTWRITEBYTECODE": "1"})
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)["status_counts"], {"deferred": 2})


class TwinTests(unittest.TestCase):
    def test_native_twin_differs_only_in_name_and_execution(self):
        for native, protected, runtime in (("c4-native", "c4-tdx", "tdx"), ("oci-e6-native", "oci-zen5-snp", "snp")):
            with self.subTest(native=native):
                a = load_json(PAPER / f"{protected}-tee.json")
                b = load_json(PAPER / f"{native}-tee.json")
                self.assertEqual(a["execution"], {"runtime": runtime, "require_protected": True})
                self.assertEqual(b["execution"], {"runtime": "native", "require_protected": False})
                drop = lambda d: {k: v for k, v in d.items() if k not in ("name", "execution")}
                self.assertEqual(drop(a), drop(b))

    def test_oracle_twin_plans_the_c4_matrix(self):
        # An oci-zen5-snp preset changes only name, execution and resources: same rows, seeds and windows.
        for path in sorted(PAPER.glob("oci-zen5-snp-*.json")):
            twin = PAPER / path.name.replace("oci-zen5-snp-", "c4-tdx-", 1)
            if not twin.exists():
                continue
            with self.subTest(preset=path.stem):
                exceptions = TWIN_MODEL_EXCEPTIONS.get(split(path.stem)[1], set())
                ours, theirs = load_json(path), load_json(twin)
                drop = lambda d: {k: v for k, v in without_models(d, exceptions).items()
                                  if k not in ("name", "execution", "resources")}
                self.assertEqual(drop(ours), drop(theirs))
                key = lambda row: twin_key(row, exceptions)
                self.assertEqual(sorted(map(key, PlanCache.get(path)["trials"])),
                                 sorted(map(key, PlanCache.get(twin)["trials"])))
                self.assertEqual(ours["execution"], {"runtime": "snp", "require_protected": True})
                self.assertEqual(ours["resources"]["required_cache_domains"], 2)
                self.assertEqual(theirs["resources"]["required_cache_domains"], 1)


class InvariantTests(unittest.TestCase):
    """The measured rows' settings, row by row."""

    def rows(self):
        for path in preset_paths():
            for row in PlanCache.get(path)["trials"]:
                yield path.stem, load_json(path), row

    def test_campaign_settings(self):
        for path in preset_paths():
            data = load_json(path)
            with self.subTest(preset=path.stem):
                self.assertEqual(data["resources"]["spin_before_park_ns"], SPIN)
                self.assertEqual(data["workload"], {"distribution": "counter"})
                self.assertEqual(data["instrumentation"]["verification"], "off")
                self.assertEqual(data["instrumentation"]["logging"], "histogram_checkpoints")
                schemes = {c["overrides"]["scheme"] for st in data["stages"] for c in st["candidates"]}
                self.assertTrue(any(schemes <= worker for worker in WORKERS), schemes)
                for stage in data["stages"]:
                    stream = stage["seed_stream"]
                    self.assertIsNone(re.search(r"20\d\d|\d{4}-\d\d-\d\d", stream), stream)
                    for shape in stage["shapes"]:
                        if shape["name"] == "standard-provisional-k4-v8":
                            self.assertEqual(shape.get("key_layout"), "dense")

    def test_row_settings(self):
        for stem, data, row in self.rows():
            spec = row["spec"]
            scheme = spec["overrides"]["scheme"]
            label = (stem, spec["stage"], spec["requested_capacity"], spec["api_mode"], spec["arrival"])
            self.assertIn(spec["candidate"], CANDIDATES, label)
            self.assertEqual(spec["resources"]["spin_before_park_ns"], SPIN, label)
            self.assertEqual(spec["workload"]["distribution"], "counter", label)
            # At least N settle requests (SONIC: 2^21, as measured; it has no rebuild cycle).
            settle = spec["timing"]["settle_requests"]
            if scheme == SONIC:
                self.assertEqual(settle, N21, label)
            else:
                self.assertGreaterEqual(settle, spec["requested_capacity"], label)
            if spec["timing"].get("settle_per_entry_ppm"):
                self.assertEqual(settle, max(N21, spec["requested_capacity"]), label)
            # The worker refuses more than 4,096 checkpoint blocks over its window plus drain.
            interval = spec["instrumentation"]["checkpoint_interval_ns"]
            self.assertLessEqual((spec["timing"]["measurement_ns"] + spec["timing"]["drain_deadline_ns"]) // interval,
                                 4096, label)
            # Windows come from the measured rows' models, except Figure 8's fixed 30 s / 300 s windows.
            if not split(stem)[1].startswith("width"):
                self.assertIsNotNone(row["estimated_trial_ns"], label)
            if scheme == SONIC:
                self.assertEqual({k: v for k, v in spec["overrides"]["sonic"].items() if v is not None},
                                 {"map_top_entries": 2048}, label)
            if spec["api_mode"] == "batch":
                incremental = spec["overrides"].get("incremental") or {}
                if scheme == "hierarchical_incremental":
                    self.assertEqual(spec["candidate"], "parallel-8x8", label)
                    self.assertEqual((incremental["batch_execution"], incremental["batch_participants"],
                                      incremental["batch_lanes"]), ("parallel_tiles", 8, 8), label)
                if scheme == "auto":  # the tree ORAM at 1 KiB
                    self.assertEqual(spec["shape"]["value_bytes"], 1024, label)
                if spec["kind"] == "latency":
                    self.assertEqual(spec["batch_policy"]["formation"], "arrive_together", label)
            logging = spec["instrumentation"]
            if spec["kind"] == "latency":
                self.assertEqual(logging.get("service_timing"), spec["api_mode"] == "batch", label)
                if spec["arrival"] == "fixed":
                    self.assertTrue(logging.get("checkpoint_thread"), label)
                    self.assertEqual(spec["rate"]["kind"], "saturation_fraction", label)
            self.assertEqual(logging["buffer_bytes"], 1024 * MIB if logging.get("service_timing") else 256 * MIB, label)

    def test_batch_sizes_and_fractions(self):
        for stem, data, row in self.rows():
            spec = row["spec"]
            if spec["api_mode"] == "batch":
                self.assertEqual(spec["caller_batch_size"], 64)  # every batch row, SONIC's included
            if spec["arrival"] == "fixed":
                fraction = spec["rate"]["fraction_ppm"]
                expected = {500000, 800000} if (spec["candidate"] == "auto" and spec["api_mode"] == "scalar" and
                                                spec["shape"]["value_bytes"] == 8) else {500000}
                self.assertIn(fraction, expected, (stem, spec["stage"]))

    def test_h2o2ram_amd_presets_declare_the_256_gb_guest(self):
        for path in sorted(PAPER.glob("*-baseline-h2o2ram*.json")):
            resources = load_json(path)["resources"]
            with self.subTest(preset=path.stem):
                if path.stem.startswith("oci-zen5-snp-"):
                    self.assertEqual(resources["host_memory_limit_bytes"], 269766885376)
                    self.assertEqual(resources["headroom_ppm"], 50000)
                else:
                    self.assertNotIn("headroom_ppm", resources)

    def test_the_2p30_batch_row_fits_the_request_horizon(self):
        rows = PlanCache.get(PAPER / "c4-tdx-throughput-k4v8.json")["trials"]
        largest = [r["spec"] for r in rows if r["spec"]["requested_capacity"] == 1 << 30
                   and r["spec"]["candidate"] == "parallel-8x8"]
        self.assertEqual([s["stage"] for s in largest], ["ours-batch64-2p30"])
        data = load_json(PAPER / "c4-tdx-throughput-k4v8.json")
        stage = next(st for st in data["stages"] if st["name"] == "ours-batch64-2p30")
        self.assertEqual(stage["candidates"][0]["trial_time"][0]["coverage_accesses_per_entry_ppm"], 500000)

    def test_large_rows_fit_the_request_horizon_at_measured_rates(self):
        # Settle + warmup + window at the measured rate (plus 15% for a faster boot) stays below the 2^32
        # request horizon, and the window still holds N requests at the measured rate.
        measured = {  # req/s of the measured sweeps: (auto, parallel-8x8, hash map, hash map batch 64)
            "c4-tdx": {1 << 28: (1056817, 3328364, 1376826, 5010380), 1 << 29: (965831, 3112513, 1186842, 4900942),
                       1 << 30: (840452, 2993297, 1018627, 4131709)},
            "oci-zen5-snp": {1 << 28: (748986, 5125248, 576875, 1883599), 1 << 29: (672773, 4869045, 518567, 1701304),
                             1 << 30: (554974, 4430612, 488528, 1593642)}}
        column = {("auto", "scalar"): 0, ("parallel-8x8", "batch"): 1, ("std_unordered_map", "scalar"): 2,
                  ("std_unordered_map", "batch"): 3}
        for target, rates in measured.items():
            for row in PlanCache.get(PAPER / f"{target}-throughput-k4v8.json")["trials"]:
                spec = row["spec"]
                n = spec["requested_capacity"]
                if n not in rates:
                    continue
                rate = rates[n][column[(spec["candidate"], spec["api_mode"])]]
                timing = spec["timing"]
                window = timing["measurement_ns"] / 1e9 * rate
                total = timing["settle_requests"] + (timing["warmup_ns"] / 1e9 * rate + window) * 1.15
                label = (target, spec["stage"], n)
                self.assertLess(total, timing["max_accesses"], label)
                self.assertGreaterEqual(window, n, label)

    def test_intel_h2o2ram_width_stops_at_512_bytes(self):
        widths = lambda name: sorted(s["value_bytes"] for st in load_json(PAPER / name)["stages"] for s in st["shapes"])
        self.assertEqual(widths("c4-tdx-baseline-h2o2ram-width.json")[-1], 512)
        self.assertEqual(widths("oci-zen5-snp-baseline-h2o2ram-width-large.json"), [1024, 2048])


class RehearsalTests(unittest.TestCase):
    def test_rehearsal_copies_plan_natively_at_small_capacities(self):
        with tempfile.TemporaryDirectory() as directory:
            result = subprocess.run([sys.executable, str(GENERATOR), "--rehearsal", directory,
                                     "--physical-cores", "12"], cwd=ROOT, capture_output=True, text=True,
                                    env={"PYTHONDONTWRITEBYTECODE": "1"})
            self.assertEqual(result.returncode, 0, result.stderr)
            paths = sorted(Path(directory).glob("*.json"))
            self.assertEqual({p.stem for p in paths}, {f"rehearsal-{p.stem}" for p in preset_paths()})
            for path in paths:
                with self.subTest(preset=path.stem):
                    data = load_json(path)
                    self.assertEqual(data["name"], path.stem)
                    self.assertEqual(data["execution"], {"runtime": "native", "require_protected": False})
                    self.assertEqual(data["resources"]["physical_cores"], 12)
                    self.assertEqual(data["resources"]["required_cache_domains"], 1)
                    self.assertEqual(data["instrumentation"]["verification"], "full")
                    self.assertGreaterEqual(data["timing"]["drain_deadline_ns"], 30 * 10**9)
                    rows = plan(data)["trials"]
                    original = PlanCache.get(PAPER / f"{path.stem[len('rehearsal-'):]}.json")["trials"]
                    self.assertEqual({r["spec"]["candidate"] for r in rows},
                                     {r["spec"]["candidate"] for r in original})
                    self.assertTrue(all(r["planning_status"] == "deferred" for r in rows))
                    self.assertTrue(all(r["spec"]["requested_capacity"] <= 1 << 16 for r in rows))
                    self.assertTrue(all(r["spec"]["timing"]["settle_requests"] <= 1 << 16 for r in rows))
                    # Under 16 cores SONIC gets a smaller pool; a scalar row keeps its single access thread.
                    for row in rows:
                        sonic = row["spec"]["overrides"].get("sonic")
                        if sonic is not None:
                            self.assertEqual(sonic["eviction_threads"], 4)
                            self.assertEqual(sonic["access_threads"],
                                             4 if row["spec"]["api_mode"] == "batch" else None)


def fixture(**timing):
    return {"schema_version": 1, "name": "fixture", "repetitions": 1, "timing": timing,
            "stages": [{"name": "sweep", "kind": "capacity",
                        "shapes": [{"name": "k4-v8", "key_bytes": 4, "value_bytes": 8}],
                        "capacities": [128, 4096], "api_modes": ["scalar"],
                        "candidates": [{"name": "tree", "overrides": {"scheme": "tree"}}]}]}


class SettlePerEntryTests(unittest.TestCase):
    """timing.settle_per_entry_ppm: each row settles max(settle_requests, ceil(capacity * ppm / 10^6))."""

    def settles(self, data):
        return {r["spec"]["requested_capacity"]: r["spec"]["timing"]["settle_requests"] for r in plan(data)["trials"]}

    def test_rows_settle_their_own_count(self):
        self.assertEqual(self.settles(fixture(settle_requests=1000, settle_per_entry_ppm=1_000_000)),
                         {128: 1000, 4096: 4096})
        self.assertEqual(self.settles(fixture(settle_requests=0, settle_per_entry_ppm=333_333)),
                         {128: 43, 4096: 1366})  # rounded up
        self.assertEqual(self.settles(fixture(settle_requests=1000)), {128: 1000, 4096: 1000})

    def test_unset_is_absent_so_identities_are_unchanged(self):
        unset, explicit = plan(fixture(settle_requests=7)), plan(fixture(settle_requests=7, settle_per_entry_ppm=None))
        self.assertEqual(unset["plan_id"], explicit["plan_id"])
        self.assertNotIn("settle_per_entry_ppm", unset["campaign"]["timing"])
        self.assertTrue(all("settle_per_entry_ppm" not in r["spec"]["timing"] for r in unset["trials"]))
        on = plan(fixture(settle_requests=7, settle_per_entry_ppm=1_000_000))
        self.assertEqual(on["campaign"]["timing"]["settle_per_entry_ppm"], 1_000_000)
        self.assertTrue(all(r["spec"]["timing"]["settle_per_entry_ppm"] == 1_000_000 for r in on["trials"]))
        self.assertTrue({r["trial_id"] for r in unset["trials"]}.isdisjoint(r["trial_id"] for r in on["trials"]))
        # Every shipped top-level preset plans to the same identity with the field spelled out as null.
        for path in sorted((ROOT / "benchmarks" / "campaigns").glob("*.json")):
            with self.subTest(preset=path.stem):
                data = load_json(path)
                spelled = json.loads(json.dumps(data))
                spelled.setdefault("timing", {})["settle_per_entry_ppm"] = None
                self.assertEqual(plan(data)["plan_id"], plan(spelled)["plan_id"])

    def test_positive_only(self):
        with self.assertRaisesRegex(ValidationError, "settle_per_entry_ppm"):
            plan(fixture(settle_per_entry_ppm=0))

    def test_access_horizon_uses_the_row_settle(self):
        rows = plan(fixture(settle_requests=0, settle_per_entry_ppm=1_000_000, max_accesses=5000))["trials"]
        reasons = {r["spec"]["requested_capacity"]: r["skip_reasons"] for r in rows}
        # The pinned tree fills by insertion: 128 + 128 < 5000, but 4096 + 4096 is not.
        self.assertEqual(reasons[128], [])
        self.assertEqual(reasons[4096], ["access_horizon_cannot_cover_required_fill_and_settle"])

    def test_worker_argv_carries_the_row_settle(self):
        rows = plan(fixture(settle_requests=1000, settle_per_entry_ppm=1_000_000))["trials"]
        entry = {"worker_arguments": ["--scheme", "tree"], "synthetic": False}
        for row in rows:
            argv = trial_arguments(row, entry, "/nonexistent", None)
            self.assertEqual(argv[argv.index("--settle-requests") + 1],
                             str(max(1000, row["spec"]["requested_capacity"])))

    def test_json_schema_exports_the_field(self):
        timing = json_schema(Campaign)["$defs"]["Timing"]
        self.assertIn("settle_per_entry_ppm", timing["properties"])
        self.assertNotIn("settle_per_entry_ppm", timing["required"])


if __name__ == "__main__":
    unittest.main()
