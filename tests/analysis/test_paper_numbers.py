"""analysis/paper_numbers.py: synthetic summaries holding the measured values behind the paper reproduce its
Table 1 cells and derived numbers; selection (paper presets only, the presets' method, joint TEE pairs, stage
kinds), flags and missing inputs; agreement with the preset generator; and a smoke run over two small reduced
summaries from a scaled local run (scrubbed of build, environment and trial hashes)."""
import contextlib
import csv
import io
import json
from pathlib import Path
import re
import runpy
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "analysis"))
import paper_numbers as pn  # noqa: E402

FIXTURES = Path(__file__).resolve().parent / "fixtures" / "paper_numbers"
GENERATOR = ROOT / "benchmarks" / "campaigns" / "paper" / "make_presets.py"
GIB = 2**30
RUNTIME = {"c4-tdx": "tdx", "oci-zen5-snp": "snp", "c4-native": "native", "oci-e6-native": "native"}
SONIC, UMAP = "sonic_zingoram_recursive", "std_unordered_map"
P88 = "parallel-8x8"
N21, N27 = 1 << 21, 1 << 27
# GiB: the event buffers the worker pre-faults in saturated rows (half-rate rows hold none): 1 GiB in the
# batch-latency campaigns (service timing), 256 MiB in the others.
SERVICE_BUFFER, EVENT_BUFFER = 1.0, 0.25
SERVICE_TIMING_ITEMS = ("table1-batch", "baseline-sonic-table-batch")

# Unrounded values of the measurements behind Table 1 (ops/s; response mean and p99 in ns; memory in GiB),
# per column (k4v8, k8v48, k32v1024) as (Intel, AMD).
THROUGHPUT = {
    ("single", "ours"): [(1165738, 844715), (567651, 615509), (269179, 293055)],
    ("single", "h2o2ram"): [(81511, 87203), (57037, 59009), (4041, 4712)],
    ("single", "sonic"): [(22741, 19963), (35240, 27000), (32011, 27910)],
    ("single", "umap"): [(1441661, 714514), (1490000, 1340000), (1170000, 1050000)],
    ("batch", "ours"): [(3374988, 5531267), (1448268, 2125263), (333743, 364253)],
    ("batch", "sonic"): [(47721, 48360), (59626, 64000), (46618, 52036)],
    ("batch", "umap"): [(5075162, 2399532), (5460000, 4710000), (1980000, 1810000)],
}
RESPONSE = {
    ("single", "ours"): [((880, 1320), (1270, 2470)), ((1780, 2420), (1660, 2960)),
                         ((3637.7, 6127), (3321.3, 6239))],
    ("single", "h2o2ram"): [((4.02e9, 90.4e9), (2.19e9, 61.1e9)), ((1.52e9, 32.0e9), (1.27e9, 27.7e9)),
                            ((0.726e9, 20.2e9), (0.755e9, 19.9e9))],
    ("single", "sonic"): [((96.8e3, 604e3), (84.0e3, 573e3)), ((85e3, 535e3), (78e3, 526e3)),
                          ((130e3, 758e3), (110e3, 711e3))],
    ("single", "umap"): [((824, 1299), (1530, 3460)), ((980, 1290), (1070, 2420)), ((800, 1410), (1060, 2930))],
    ("batch", "ours"): [((16.1e3, 19.8e3), (10.67e3, 16.03e3)), ((34.46e3, 44.67e3), (33.35e3, 46.21e3)),
                        ((202.46e3, 217.60e3), (170.6e3, 184.8e3))],
    ("batch", "sonic"): [((1.28e6, 2.73e6), (1.28e6, 2.59e6)), ((1.1e6, 2.5e6), (1.0e6, 2.2e6)),
                         ((1.6e6, 3.8e6), (1.4e6, 3.3e6))],
    ("batch", "umap"): [((11.98e3, 13.73e3), (28.34e3, 34.05e3)), ((10.77e3, 12.35e3), (13.68e3, 18.43e3)),
                        ((23.42e3, 25.98e3), (30.16e3, 36.61e3))],
}
# The paper's memory cells (GiB): each cell's highest-peak row less the event buffer it holds. As recorded, Ours
# and the hash map peak in their saturated single-request rows (Ours 10.04 / 9.34 / 4.617 GiB of peak RSS),
# H2O2RAM in its half-rate rows and SONIC in its saturated batch rows (15.94 / 9.76 GiB at the wider shapes).
MEMORY = {"ours": (9.79, 9.09, 4.367), "h2o2ram": (22.1, 19.7, 36.16), "sonic": (27.69, 14.94, 8.76),
          "umap": (7.07, 2.76, 2.17)}
COLUMNS = [(4, 8, 1 << 27), (8, 48, 1 << 25), (32, 1024, 1 << 21)]
MACHINES = ("c4-tdx", "oci-zen5-snp")
# Figure 8 (K8, 2^20): throughput (hierarchy, hybrid) and library reserved / logical (hierarchy, hybrid).
FIG8 = {"c4-tdx": {16: (1821105, 988164), 32: (1303960, 732603), 64: (799500, 634859), 96: (578393, 602299),
                   1024: (47862, 341193)},
        "oci-zen5-snp": {16: (1960234, 1025616), 32: (1552900, 946668), 64: (992610, 875803),
                         96: (723154, 853110), 1024: (82710, 370644)}}
FIG8_MEMORY = {16: (5.55, 5.59), 32: (5.31, 4.20), 64: (5.1, 3.2), 96: (5.0, 2.8), 1024: (4.8906, 2.0904)}
# SONIC data tree alone (req/s) and position-map share; H2O2RAM top-level rebuild spans (s).
SONIC_DATA_TREE = {("c4-tdx", 4): (248981, 0.808), ("c4-tdx", 32): (77694, 0.41),
                   ("oci-zen5-snp", 4): (374460, 0.72), ("oci-zen5-snp", 32): (87393, 0.40)}
TOP_REBUILDS = {"c4-tdx": (117.2, 117.6), "oci-zen5-snp": (89.5, 90.3)}


def candidate_of(system, setting, value_bytes):
    if system == "ours":
        return "auto" if setting == "single" or value_bytes == 1024 else P88
    return {"h2o2ram": "h2o2ram", "sonic": SONIC, "umap": UMAP}[system]


def table_campaign(machine, system, setting):
    """The paper preset holding a Table 1 row."""
    api = "scalar" if setting == "single" else "batch"
    if system in ("ours", "umap"):
        return f"{machine}-table1-{api}"
    if system == "h2o2ram":
        return f"{machine}-baseline-h2o2ram-table"
    return f"{machine}-baseline-sonic-table-{api}"


def stage_kind(campaign):
    item = pn.target_and_item(campaign, {})[1]
    return "value_width" if "width" in item else "latency" if "table" in item else "capacity"


class Builder:
    """Synthetic reduced summaries: one group per repetition, the fields paper_numbers reads, with the paper
    presets' method settings (counter keys, verification off, 1 s spin, settle max(N, 2^21), 2^21 for SONIC)."""

    def __init__(self):
        self.campaigns, self.count, self.raw = {}, 0, []

    def row(self, campaign, candidate, key, value, capacity, *, api="scalar", batch=1, arrival="saturated",
            ops=None, rate=None, mean=None, p99=None, maximum=None, rss=None, reserved=None, completed=None,
            blockers=(), stability=None, scheme=None, formation=None, runtime=None, coverage=None, kind=None,
            boot=None, settle=None):
        self.count += 1
        trial, attempt = f"trial-v1-{self.count:04d}{'0' * 56}", f"attempt-{self.count:04d}"
        target, item = pn.target_and_item(campaign, {})
        buffer = (1 << 30) if item in SERVICE_TIMING_ITEMS else (256 << 20)
        runtime = runtime or RUNTIME.get(target, "native")
        scheme = scheme or ({"auto": "auto", P88: "hierarchical_incremental", "parallel-8x64":
                             "hierarchical_incremental", "hierarchy-frozen": "hierarchical_incremental",
                             "tree": "tree"}.get(candidate, candidate))
        system = pn.system_of(candidate, scheme)
        if settle is None:
            settle = N21 if system == "sonic" else max(capacity, N21)
        spec = {"stage": "s", "kind": kind or stage_kind(campaign), "candidate": candidate,
                "overrides": {"scheme": scheme}, "shape": {"key_bytes": key, "value_bytes": value},
                "requested_capacity": capacity, "api_mode": api, "caller_batch_size": batch,
                "batch_policy": {"formation": formation or ("arrive_together" if api == "batch" else "fixed_count")},
                "arrival": arrival, "rate": rate, "execution": {"runtime": runtime},
                "workload": {"distribution": "counter", "read_ppm": 950_000, "hit_ppm": 1_000_000,
                             "occupancy_ppm": 1_000_000, "miss_key_count": 0},
                "timing": {"settle_requests": settle},
                "instrumentation": {"verification": "off", "buffer_bytes": buffer,
                                    "logging": "histogram_checkpoints"},
                "resources": {"physical_cores": 16, "spin_before_park_ns": 10**9}}
        rep = {"trial_id": trial, "executed_trial_id": trial, "attempt_id": attempt, "environment_class": "env",
               "runtime": runtime, "spec": spec,
               "summary": {"drained_ops_per_second": ops, "completed": completed or 2 * capacity,
                           "response": {"mean_ns": mean, "p50_ns": mean, "p99_ns": p99, "p999_ns": p99,
                                        "maximum_ns": maximum or p99}},
               "memory": {"trial_peak_rss_bytes": None if rss is None else int(rss * GIB)},
               "library_reserved_bytes": None if reserved is None else int(reserved),
               "logical_bytes": capacity * (key + value), "live_entries": capacity,
               "publication_blockers": list(blockers) or (["cycle_coverage_unknown"] if system != "ours" else []),
               "queue_stability": stability or ("not_applicable" if arrival == "saturated" else "stable"),
               "cycle_coverage": coverage or ("sufficient" if system == "ours" else "unknown"),
               "offered_ops_per_second": (rate or {}).get("ops_per_second")}
        if boot is not None:
            rep["_boot"] = boot  # another summary (boot) of the same campaign
        self.campaigns.setdefault(campaign, []).append(rep)
        return trial, attempt

    def fixed(self, campaign, source, fraction, mean, p99, **kwargs):
        rate = {"kind": "saturation_fraction", "fraction_ppm": fraction, "source_trial_ids": [source]}
        return self.row(campaign, arrival="fixed", rate=rate, mean=mean, p99=p99, **kwargs)

    def write(self, directory):
        paths = []
        for name, reps in sorted(self.campaigns.items()):
            boots = {}
            for rep in reps:
                boots.setdefault(rep.get("_boot"), []).append({k: v for k, v in rep.items() if k != "_boot"})
            for boot, boot_reps in sorted(boots.items(), key=lambda kv: str(kv[0])):
                plan = "plan-" + name + ("" if boot is None else f"-{boot}")
                document = {"campaign_summary_schema_version": 6, "plan_id": plan,
                            "campaign": {"name": name, "plan_id": plan, "worker_sha256": None},
                            "trial_status": {}, "groups": [{"group_id": rep["trial_id"], "runtime": rep.get("runtime"),
                                                            "repetitions": [rep]} for rep in boot_reps]}
                path = Path(directory) / (f"{name}.json" if boot is None else f"{name}-{boot}.json")
                path.write_text(json.dumps(document))
                paths.append(path)
        return paths

    def worker_file(self, directory, campaign, trial, attempt, name, text):
        worker = Path(directory) / campaign / "trials" / trial / "attempts" / f"000001-{attempt}" / "worker"
        worker.mkdir(parents=True, exist_ok=True)
        (worker / name).write_text(text)
        return Path(directory) / campaign


def phases_json(data_tree, share):
    data_ns = 10**10
    return json.dumps({"schema": "sonic-phases-v1", "after_fill": {
        "windows": 1, "accesses": data_tree * 10, "data_ns": data_ns, "map_ns": int(data_ns * share / (1 - share))}})


def markers_csv(levels):
    return "role,level,start_ns,end_ns\n" + "".join(f"h2o2ram_rebuild,{level},0,{int(seconds * 1e9)}\n"
                                                   for level, seconds in levels)


def memory_of(system, setting, arrival, ci):
    """Peak RSS (GiB) of a Table 1 row, shaped like the records: a saturated row holds its event buffer, a
    half-rate row holds none but its map peaks slightly higher (so it may exceed the saturated row's memory
    without being the highest peak), and H2O2RAM peaks in its half-rate rows."""
    memory = MEMORY[system][ci]
    buffer = SERVICE_BUFFER if setting == "batch" else EVENT_BUFFER
    if system == "h2o2ram":
        return memory if arrival == "fixed" else memory - 0.5
    designated = setting == ("batch" if system == "sonic" else "single")
    if not designated:  # never read for memory
        memory += 0.3
    return memory + (buffer if arrival == "saturated" else 0.03)


def paper_rows(b, raw_dir):
    """Every row behind the paper's campaign numbers, on both TEE targets; returns the raw campaign dirs."""
    dirs = set()
    for mi, machine in enumerate(MACHINES):
        for ci, (key, value, n) in enumerate(COLUMNS):
            for (setting, system), per_column in THROUGHPUT.items():
                ops = per_column[ci][mi]
                api, batch = ("scalar", 1) if setting == "single" else ("batch", 64)
                skey = 8 if system == "sonic" and key == 32 else key
                campaign = table_campaign(machine, system, setting)
                candidate = candidate_of(system, setting, value)
                reserved = (MEMORY[system][ci] - 0.01) * GIB if system == "ours" else None
                completed = int(0.3 * n) if system == "sonic" and n == N27 else None  # SONIC: 0.25 N windows
                trial, attempt = b.row(campaign, candidate, skey, value, n, api=api, batch=batch, ops=ops,
                                       rss=memory_of(system, setting, "saturated", ci), reserved=reserved,
                                       completed=completed)
                mean, p99 = RESPONSE[(setting, system)][ci][mi]
                b.fixed(campaign, trial, 500_000, mean, p99, candidate=candidate, key=skey, value=value,
                        capacity=n, api=api, batch=batch, rss=memory_of(system, setting, "fixed", ci),
                        reserved=reserved)
                if system == "sonic" and setting == "batch" and key in (4, 32):
                    dirs.add(b.worker_file(raw_dir, campaign, trial, attempt, "sonic_phases.json",
                                           phases_json(*SONIC_DATA_TREE[(machine, key)])))
                if system == "h2o2ram" and key == 4:
                    levels = [(3, 0.5), (17, TOP_REBUILDS[machine][0]), (17, TOP_REBUILDS[machine][1])]
                    dirs.add(b.worker_file(raw_dir, campaign, trial, attempt, "markers.csv", markers_csv(levels)))
        tdx = machine == "c4-tdx"
        source = [t for t in b.campaigns[f"{machine}-table1-scalar"] if t["spec"]["candidate"] == "auto" and
                  t["spec"]["requested_capacity"] == 1 << 27 and t["spec"]["arrival"] == "saturated"][0]
        if tdx:  # the 0.8 S row of the abstract
            b.fixed(f"{machine}-table1-scalar", source["trial_id"], 800_000, 1550, 3380, candidate="auto", key=4,
                    value=8, capacity=1 << 27)
        # Figure 7: ours and H2O2RAM single requests by N (2^27 is the Table 1 row).
        for system, candidate in (("ours", "auto"), ("h2o2ram", "h2o2ram")):
            for log2, ops in pn.PAPER_FIG7[("intel" if tdx else "amd", "single", system)].items():
                if log2 != 27:
                    b.row(f"{machine}-throughput-k4v8" if system == "ours" else
                          f"{machine}-baseline-h2o2ram-throughput", candidate, 4, 8, 1 << log2, ops=ops)
        # H2O2RAM shipped against patched (AMD 2^17 is the maximum, 1.256).
        shipped = {16: 366998, 17: 359374} if not tdx else {16: 279837 * 1.15, 17: 257616 * 1.18}
        for log2, ops in shipped.items():
            b.row(f"{machine}-baseline-h2o2ram-shipped-throughput", "h2o2ram_shipped", 4, 8, 1 << log2, ops=ops)
        # Figure 8.
        for width, (h_ops, t_ops) in FIG8[machine].items():
            for candidate, ops, ratio in (("hierarchy-frozen", h_ops, FIG8_MEMORY[width][0]),
                                          ("tree", t_ops, FIG8_MEMORY[width][1])):
                n = 1 << 20
                b.row(f"{machine}-width", candidate, 8, width, n, ops=ops, rss=3.0,
                      reserved=ratio * n * (8 + width))
    # TEE pairs: Intel one cycle; AMD two cycles per side (the paper averages them). The AMD batch-64 values are
    # synthetic: no recorded plain-VM batch-64 row at 2^27 gives the paper's 4%.
    for single, batch, campaign in ((1043168, 3363663, "c4-tdx-tee"), (1162739, 3545062, "c4-native-tee")):
        b.row(campaign, "auto", 4, 8, 1 << 27, ops=single)
        b.row(campaign, P88, 4, 8, 1 << 27, api="batch", batch=64, ops=batch)
    for singles, batches, campaign in (((860869, 855851), (5531267, 5525000), "oci-zen5-snp-tee"),
                                       ((1394892, 1399691), (5761736, 5755000), "oci-e6-native-tee")):
        for single, batch in zip(singles, batches):
            b.row(campaign, "auto", 4, 8, 1 << 27, ops=single)
            b.row(campaign, P88, 4, 8, 1 << 27, api="batch", batch=64, ops=batch)
    return sorted(dirs)


def run(paths, output, **kwargs):
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        return pn.reduce_paper(paths, output, figures=False, **kwargs)


def read_csv(path):
    with open(path, newline="") as stream:
        return list(csv.DictReader(stream))


def cells_of(out):
    return {tuple(r[k] for k in ("section", "setting", "system", "column", "machine", "metric")): r
            for r in read_csv(out / "table1.csv")}


class Formatting(unittest.TestCase):
    def test_paper_rounding(self):
        cases = {1165738: "1.17 M", 844715: "845 K", 81511: "82 K", 4041: "4.0 K", 4712: "4.7 K",
                 19963: "20 K", 2399532: "2.40 M", 333743: "334 K", 10144000: "10.1 M", 145: "145",
                 99960: "100 K", 999700: "1.00 M"}
        for ops, text in cases.items():
            self.assertEqual(pn.format_rate(ops), text, ops)
        self.assertEqual(pn.format_time(880, "µs"), "0.88 µs")
        self.assertEqual(pn.format_time(800, "µs"), "0.80 µs")
        self.assertEqual(pn.format_time(202.46e3, "µs"), "202 µs")
        self.assertEqual(pn.format_time(4.02e9, "s"), "4.0 s")
        self.assertEqual(pn.format_time(0.755e9, "s"), "0.76 s")  # half up, not to even
        self.assertEqual(pn.format_time(1.28e6, "ms"), "1.3 ms")
        self.assertEqual(pn.format_gib(10.04 * GIB), "10.0 GiB")
        self.assertEqual(str(pn.round_places(27.5, 0)), "28")
        self.assertAlmostEqual(pn.parse_paper("0.88 µs"), 880)
        self.assertAlmostEqual(pn.parse_paper("1.17 M"), 1.17e6)

    def test_paper_table_has_every_cell(self):
        # 24 + 18 single/batch throughput, 48 + 36 response, 4 systems x 3 columns x 2 machines of memory.
        self.assertEqual(len(pn.PAPER_TABLE1), 24 + 18 + 48 + 36 + 24)
        self.assertEqual(pn.PAPER_TABLE1[("throughput", "single", "h2o2ram", "k32v1024", "amd", "ops")], "4.7 K")
        self.assertEqual(pn.PAPER_TABLE1[("response", "batch", "sonic", "k8v48", "intel", "p99")], "2.5 ms")
        self.assertEqual(pn.PAPER_TABLE1[("memory", "single", "sonic", "k4v8", "intel", "peak_rss")], "27.7 GiB")
        # The paper prints memory for the Intel rows only: the AMD cells are reported, not graded.
        self.assertIsNone(pn.PAPER_TABLE1[("memory", "single", "sonic", "k4v8", "amd", "peak_rss")])
        self.assertEqual(sum(1 for v in pn.PAPER_TABLE1.values() if v is None), 12)


class AgreesWithPresetGenerator(unittest.TestCase):
    """PAPER_ITEMS and the method settings mirror benchmarks/campaigns/paper/make_presets.py."""

    def test_items_mirror_make_presets(self):
        generator = runpy.run_path(str(GENERATOR))  # no bytecode written
        self.assertEqual({item: tuple(targets) for item, (_, targets) in generator["ITEMS"].items()},
                         pn.PAPER_ITEMS)
        for name in generator["presets"]():
            target, item = pn.target_and_item(name, {})
            self.assertTrue(pn.is_paper_preset(target, item), name)
            self.assertTrue(pn.is_paper_preset(*pn.target_and_item("rehearsal-" + name, {})), name)

    def test_every_preset_row_meets_the_method_and_covers_the_paper(self):
        """Every row the planner expands from the paper presets is a paper preset row without a flag (SONIC's
        2^21 settle is a note), and those rows feed every Table 1 cell and every figure reference point."""
        if str(ROOT) not in sys.path:
            sys.path.insert(1, str(ROOT))
        from analysis.oram_bench.codec import decode, load_json
        from analysis.oram_bench.planner import expand
        from analysis.oram_bench.schema import Campaign
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        paths = []
        for preset in sorted(GENERATOR.parent.glob("*.json")):
            plan = expand(decode(Campaign, load_json(preset)))
            groups = []
            for i, trial in enumerate(plan["trials"]):
                spec, n = trial["spec"], trial["spec"]["requested_capacity"]
                rep = {"trial_id": trial["trial_id"], "attempt_id": f"a{i}", "environment_class": "e",
                       "runtime": plan["campaign"]["execution"]["runtime"], "spec": spec,
                       "summary": {"drained_ops_per_second": 1000.0 + i, "completed": 2 * n,
                                   "response": {"mean_ns": 1000 + i, "p99_ns": 2000 + i, "maximum_ns": 3000}},
                       "memory": {"trial_peak_rss_bytes": GIB + i}, "library_reserved_bytes": GIB // 2,
                       "logical_bytes": n * (spec["shape"]["key_bytes"] + spec["shape"]["value_bytes"]),
                       "publication_blockers": [], "queue_stability": "stable", "cycle_coverage": "sufficient"}
                groups.append({"runtime": rep["runtime"], "repetitions": [rep]})
            path = Path(tmp.name) / preset.name
            path.write_text(json.dumps({"plan_id": plan["plan_id"], "campaign": {"name": plan["campaign"]["name"]},
                                        "groups": groups}))
            paths.append(path)
        out = Path(tmp.name) / "out"
        report = run(paths, out)
        self.assertEqual(report["campaigns_not_paper_presets"], [])
        rows = read_csv(out / "rows.csv")
        self.assertEqual({r["flags"] for r in rows}, {""})
        self.assertEqual({r["paper_preset"] for r in rows}, {"yes"})
        sonic_notes = {r["notes"] for r in rows if r["system"] == "sonic" and int(r["capacity"]) > N21}
        self.assertEqual(sonic_notes, {"settle_below_N(2097152)"})
        self.assertEqual(report["table1_reproduced"], report["table1_cells"])
        for name in ("fig7.csv", "fig8.csv"):
            unfed = [(r["machine"], r["system"], r.get("log2_capacity") or r.get("value_bytes"))
                     for r in read_csv(out / name) if r["paper"] and not r["ops_per_second"]]
            self.assertEqual(unfed, [], name)
        # Figure 8 reads the value_width stages only; Table 1 never does.
        for r in rows:
            uses = r["used_for"].split(";") if r["used_for"] else []
            if r["kind"] == "value_width":
                self.assertFalse([u for u in uses if u.startswith("table1:")], r["trial_id"])
            else:
                self.assertFalse([u for u in uses if u.startswith("fig8:")], r["trial_id"])


class PaperValues(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        tmp = Path(cls.tmp.name)
        builder = Builder()
        dirs = paper_rows(builder, tmp / "raw")
        cls.paths = builder.write(tmp)
        cls.report = run(cls.paths, tmp / "out", campaign_dirs=[str(d) for d in dirs],
                         writes={"c4-tdx": 4710600, "oci-zen5-snp": 10144000})
        cls.out = tmp / "out"
        cls.cells = cells_of(cls.out)
        cls.claims = {r["id"]: r for r in read_csv(cls.out / "claims.csv")}

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def test_every_table1_cell_matches(self):
        self.assertEqual(len(self.cells), len(pn.PAPER_TABLE1))
        differing = {k: (r["reproduced"], r["paper"]) for k, r in self.cells.items()
                     if r["status"] not in ("match", "reported")}
        self.assertEqual(differing, {})
        self.assertEqual(self.report["table1_matching"], len(pn.PAPER_TABLE1) - 12)
        self.assertEqual(self.report["table1_graded"], len(pn.PAPER_TABLE1) - 12)
        self.assertEqual(self.report["table1_reproduced"], len(pn.PAPER_TABLE1))
        cell = self.cells[("throughput", "single", "ours", "k4v8", "intel", "ops")]
        self.assertEqual((cell["reproduced"], cell["flags"]), ("1.17 M", ""))
        self.assertTrue(cell["trial_id"].startswith("trial-v1-"))
        self.assertEqual(self.report["campaigns_not_paper_presets"], [])

    def test_amd_memory_is_reported_not_graded(self):
        reported = {k: r for k, r in self.cells.items() if r["status"] == "reported"}
        self.assertEqual({k[4] for k in reported}, {"amd"})
        self.assertEqual({k[0] for k in reported}, {"memory"})
        self.assertEqual(len(reported), 12)
        amd = self.cells[("memory", "single", "ours", "k4v8", "amd", "peak_rss")]
        self.assertEqual((amd["paper"], amd["reproduced"], amd["relative_difference"]), ("", "9.8 GiB", ""))
        self.assertIn("9.8 GiB [not printed]", (self.out / "table1.md").read_text())

    def test_every_claim_reproduces(self):
        bad = {k: (r["status"], r["paper"], r["reproduced"], r["missing"]) for k, r in self.claims.items()
               if r["status"] not in ("matches", "holds", "reported") and not r["status"].startswith("within")}
        self.assertEqual(bad, {})
        self.assertEqual(self.report["claims"].get("missing input"), None)
        self.assertEqual({k: r["flags"] for k, r in self.claims.items() if r["flags"]}, {})

    def test_headline_ratios(self):
        expect = {"ours-vs-h2o2ram-k4v8": "14.3x", "ours-vs-umap-k4v8": "0.81x", "ours-vs-umap-k4v8-percent": "81%",
                  "batch-gain-ours": "2.9x; 6.5x", "ours-vs-umap-amd": "1.18x", "intel-to-amd-ours": "28%",
                  "intel-to-amd-umap": "50%", "ours-vs-sonic-batch-both": "71x; 114x",
                  "ours-vs-umap-batch-intel": "67%", "ours-vs-umap-batch-amd": "2.3x",
                  "tee-overhead-intel": "10%; 5%", "tee-overhead-amd": "39%; 4%", "write-vs-lookup": "4.0x; 12x",
                  "ours-vs-h2o2ram-by-n-intel": "14.3x; 19.0x", "ours-vs-h2o2ram-by-n-amd": "9.7x; 14.1x",
                  "ours-vs-h2o2ram-k8v48": "10x; 10x", "ours-vs-h2o2ram-k32": "67x; 62x",
                  "ours-vs-sonic-single-k32": "8.4x; 10.5x", "ours-vs-sonic-batch-k32": "7.2x; 7.0x",
                  "memory-vs-h2o2ram-k4v8": "2.3x", "memory-vs-sonic-k4v8": "2.8x", "memory-vs-h2o2ram-k32": "8.3x",
                  "memory-vs-sonic-k32": "2.0x", "memory-over-data-k4v8": "6.5x",
                  "response-vs-h2o2ram-million": "4.6 million x", "response-at-0.8": "1.6 µs; 3.4 µs",
                  "hybrid-vs-hierarchy-1k": "7.1x; 4.5x", "hybrid-memory-1k": "57%; 57%",
                  "hybrid-crossover": "96 B; 96 B", "hybrid-memory-crossover": "32 B; 32 B",
                  "ours-vs-sonic-data-tree-k4v8": "14x", "ours-vs-sonic-data-tree-k32": "4x; 4x",
                  "h2o2ram-shipped-vs-patched": "26%", "write-throughput": "4.7 M/s; 10.1 M/s"}
        for cid, text in expect.items():
            self.assertEqual(self.claims[cid]["reproduced"], text, cid)
            self.assertEqual(self.claims[cid]["paper"], text, cid)
        self.assertIn("1,165,738 req/s / 81,511 req/s", self.claims["ours-vs-h2o2ram-k4v8"]["formula"])
        self.assertEqual(len(self.claims["ours-vs-h2o2ram-k4v8"]["rows"].split(";")), 2)
        # 'falls by half' is an 'about' statement, graded with the 10% tolerance.
        self.assertEqual(self.claims["intel-to-amd-umap"]["status"], "within 10%")

    def test_raw_worker_files(self):
        rebuild = self.claims["h2o2ram-top-rebuild"]
        self.assertEqual(rebuild["status"], "within 10%")
        self.assertIn("2 top-level rebuild spans (level 17, 1 row), mean 117.4 s", rebuild["formula"])
        self.assertIn("position-map share 80.8%", self.claims["ours-vs-sonic-data-tree-k4v8"]["notes"])

    def test_checks_and_reports(self):
        for cid in ("batch-faster-on-amd", "umap-batch-gain", "response-vs-h2o2ram-both"):
            self.assertEqual(self.claims[cid]["status"], "holds", cid)
        self.assertNotIn("memory-minus-reserved", self.claims)  # the paper no longer states the buffer

    def test_memory_deducts_the_event_buffer(self):
        # SONIC: its batch rows; the highest peak is the saturated row, less its 1 GiB service-timing buffer
        # (at 8 B / 48 B the half-rate row's 14.97 GiB is higher than 14.94 but is not the highest peak).
        for column, text in (("k4v8", "27.7 GiB"), ("k8v48", "14.9 GiB"), ("k32v1024", "8.8 GiB")):
            cell = self.cells[("memory", "single", "sonic", column, "intel", "peak_rss")]
            self.assertEqual(cell["reproduced"], text, column)
            self.assertIn("less its 1024 MiB event buffer", cell["note"])
        # Ours and the hash map: saturated single-request rows less 256 MiB.
        for system, text in (("ours", "9.8 GiB"), ("umap", "7.1 GiB")):
            cell = self.cells[("memory", "single", system, "k4v8", "intel", "peak_rss")]
            self.assertEqual(cell["reproduced"], text, system)
            self.assertIn("less its 256 MiB event buffer", cell["note"])
        # H2O2RAM peaks in its half-rate row, which holds no event buffer.
        cell = self.cells[("memory", "single", "h2o2ram", "k4v8", "intel", "peak_rss")]
        self.assertEqual((cell["reproduced"], cell["note"]), ("22.1 GiB", ""))
        rows = {r["trial_id"]: r for r in read_csv(self.out / "rows.csv")}
        ours = rows[self.cells[("memory", "single", "ours", "k4v8", "intel", "peak_rss")]["trial_id"]]
        self.assertEqual((ours["event_buffer_gib"], ours["memory_gib"]), ("0.2500", "9.7900"))

    def test_sonic_batch_8_notes(self):
        for machine in ("intel", "amd"):
            note = self.cells[("throughput", "batch", "sonic", "k4v8", machine, "ops")]["note"]
            self.assertIn("the paper's value was a batch-8 row", note)
        fig7 = read_csv(self.out / "fig7.csv")
        noted = {(r["machine"], r["log2_capacity"]) for r in fig7
                 if r["system"] == "sonic" and r["panel"] == "batch64" and r["note"]}
        self.assertIn(("intel", "27"), noted)
        self.assertNotIn(("intel", "26"), noted)
        self.assertEqual({n for m, n in noted if m == "amd"}, {str(n) for n in range(16, 28)})

    def test_figure_data(self):
        fig7 = read_csv(self.out / "fig7.csv")
        ours = [r for r in fig7 if r["machine"] == "intel" and r["panel"] == "single" and r["system"] == "ours"]
        self.assertEqual(len(ours), 15)  # 2^16..2^30
        self.assertEqual(sum(1 for r in ours if r["ops_per_second"]), 15)
        h2o2ram = [r for r in fig7 if r["machine"] == "amd" and r["system"] == "h2o2ram" and r["ops_per_second"]]
        self.assertEqual([int(r["log2_capacity"]) for r in h2o2ram], list(range(16, 28)))
        self.assertTrue(all(r["ratio_to_paper"] == "1.0000" for r in ours if r["ops_per_second"]))
        fig8 = read_csv(self.out / "fig8.csv")
        hybrid = [r for r in fig8 if r["machine"] == "intel" and r["system"] == "hybrid" and r["value_bytes"] == "1024"]
        self.assertEqual((hybrid[0]["memory_metric"], hybrid[0]["memory_over_data"]), ("library_reserved", "2.0904"))

    def test_markdown_outputs(self):
        table = (self.out / "table1.md").read_text()
        self.assertIn("1.17 M [1.17 M]", table)
        self.assertIn("No cell uses a flagged row.", table)
        self.assertIn("## Notes", table)
        claims = (self.out / "claims.md").read_text()
        self.assertIn("## ours-vs-h2o2ram-k4v8", claims)
        self.assertIn("Statements outside the campaigns", claims)
        rows = read_csv(self.out / "rows.csv")
        used = [r for r in rows if "claim:ours-vs-h2o2ram-k4v8" in r["used_for"]]
        self.assertEqual(len(used), 2)
        # SONIC's 2^21 settle and 0.3 N window at 2^27 are the presets' own: notes, not flags.
        sonic = [r for r in rows if r["system"] == "sonic" and r["capacity"] == str(N27)]
        self.assertTrue(sonic)
        for r in sonic:
            self.assertEqual(r["flags"], "")
            self.assertIn("settle_below_N(2097152)", r["notes"])
        self.assertIn("completed_below_N(0.30N)", ";".join(r["notes"] for r in sonic))


class Selection(unittest.TestCase):
    def reduce(self, builder, **kwargs):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        out = Path(tmp.name) / "out"
        report = run(builder.write(tmp.name), out, **kwargs)
        claims = {r["id"]: r for r in read_csv(out / "claims.csv")}
        return report, cells_of(out), claims, out

    def test_methodology_flags_and_preference(self):
        b = Builder()
        n = 1 << 27
        b.row("c4-tdx-table1-scalar", UMAP, 4, 8, n, ops=1441661)
        b.row("c4-tdx-table1-scalar", UMAP, 4, 8, n, ops=1.6e6, completed=n // 2)  # faster, but < N requests
        b.row("c4-tdx-table1-scalar", "auto", 4, 8, n, ops=1.2e6, blockers=["queue_overloaded"])
        _, cells, _, out = self.reduce(b)
        umap = cells[("throughput", "single", "umap", "k4v8", "intel", "ops")]
        self.assertEqual((umap["reproduced"], umap["flags"], umap["alternatives"]), ("1.44 M", "", "1"))
        ours = cells[("throughput", "single", "ours", "k4v8", "intel", "ops")]
        self.assertEqual((ours["reproduced"], ours["flags"]), ("1.20 M", "queue_overloaded"))
        self.assertIn("1.20 M! [1.17 M]", (out / "table1.md").read_text())
        rows = {r["drained_ops_per_second"]: r for r in read_csv(out / "rows.csv")}
        self.assertEqual(rows["1600000.0"]["flags"], "completed_below_N(0.50N)")
        self.assertEqual(rows["1441661.0"]["notes"], "cycle_coverage_unknown")  # expected for baselines

    def test_method_deviations_are_flagged(self):
        b = Builder()
        n = 1 << 27
        good, _ = b.row("c4-tdx-table1-scalar", UMAP, 4, 8, n, ops=1441661)
        deviations = {"settle": ("timing", {"settle_requests": 4096}, "settle_below_N(4096)"),
                      "keys": ("workload", {"distribution": "uniform"}, "key_distribution_uniform"),
                      "reads": ("workload", {"read_ppm": 500_000}, "read_ppm_500000"),
                      "hits": ("workload", {"hit_ppm": 900_000}, "hit_ppm_900000"),
                      "verification": ("instrumentation", {"verification": "full"}, "verification_full"),
                      "spin": ("resources", {"spin_before_park_ns": None}, "spin_before_park_ns_unset")}
        for i, (block, change, _) in enumerate(deviations.values()):
            b.row("c4-tdx-table1-scalar", UMAP, 4, 8, n, ops=2e6 + i)  # faster, each departing from the method
            b.campaigns["c4-tdx-table1-scalar"][-1]["spec"][block].update(change)
        # SONIC settles 2^21 by design (a note); below 2^21 it is a flag.
        b.row("c4-tdx-baseline-sonic-table-scalar", SONIC, 4, 8, n, ops=22741)
        b.row("c4-tdx-baseline-sonic-table-scalar", SONIC, 4, 8, n, ops=30000, settle=4096)
        report, cells, _, out = self.reduce(b)
        umap = cells[("throughput", "single", "umap", "k4v8", "intel", "ops")]
        self.assertEqual((umap["reproduced"], umap["trial_id"], umap["flags"]), ("1.44 M", good, ""))
        flags = {r["drained_ops_per_second"]: r["flags"] for r in read_csv(out / "rows.csv")}
        for i, (_, _, flag) in enumerate(deviations.values()):
            self.assertEqual(flags[f"{2e6 + i:.1f}"], flag)
        self.assertEqual(flags["22741.0"], "")
        self.assertEqual(flags["30000.0"], "settle_below_N(4096)")
        self.assertEqual(cells[("throughput", "single", "sonic", "k4v8", "intel", "ops")]["reproduced"], "23 K")

    def test_non_paper_presets_are_never_preferred(self):
        b = Builder()
        n = 1 << 27
        b.row("c4-tdx-table1-scalar", "auto", 4, 8, n, ops=1165738)
        b.row("c4-tdx-throughput-k4v8", "auto", 4, 8, n, ops=1.1e6)
        # The release's general presets share the target prefix: faster rows here must not feed the paper.
        b.row("c4-tdx", "auto", 4, 8, n, ops=1.3e6)
        b.row("c4-tdx-latency", UMAP, 4, 8, n, ops=1.9e6)
        b.row("c4-tdx-value-width", "tree", 8, 1024, 1 << 20, ops=500000, reserved=2.0 * (1 << 20) * 1032)
        b.row("c4-tdx-width", "tree", 8, 1024, 1 << 20, ops=341193, reserved=2.0904 * (1 << 20) * 1032)
        b.row("c4-native-table1-scalar", "auto", 4, 8, n, ops=1.25e6)  # a paper item on a target it never runs
        b.row("rehearsal-c4-tdx-table1-scalar", UMAP, 8, 48, 1 << 25, ops=1.49e6)  # a rehearsal copy is a preset
        report, cells, claims, out = self.reduce(b)
        ours = cells[("throughput", "single", "ours", "k4v8", "intel", "ops")]
        self.assertEqual((ours["reproduced"], ours["campaign"], ours["flags"]), ("1.17 M", "c4-tdx-table1-scalar", ""))
        self.assertEqual(ours["alternatives"], "1")  # the throughput-k4v8 row; never the general presets'
        self.assertEqual(report["campaigns_not_paper_presets"],
                         ["c4-native-table1-scalar", "c4-tdx", "c4-tdx-latency", "c4-tdx-value-width"])
        fig8 = [r for r in read_csv(out / "fig8.csv") if r["system"] == "hybrid" and r["value_bytes"] == "1024"
                and r["machine"] == "intel"][0]
        self.assertEqual((fig8["campaign"], fig8["ops_per_second"]), ("c4-tdx-width", "341193"))
        # With no paper row at all, a general preset's row stands in, flagged.
        umap = cells[("throughput", "single", "umap", "k4v8", "intel", "ops")]
        self.assertEqual((umap["campaign"], umap["flags"]), ("c4-tdx-latency", "not_paper_preset"))
        self.assertEqual(report["not_paper_preset_campaigns_used"], ["c4-native-table1-scalar", "c4-tdx-latency"])
        self.assertIn("not_paper_preset", claims["ours-vs-umap-k4v8"]["flags"])
        # The native side has no paper row at all, so the TEE pair is flagged twice over.
        tee = claims["tee-overhead-intel"]
        self.assertIn("1,165,738 req/s / 1,250,000 req/s", tee["formula"])
        self.assertIn("not_paper_preset", tee["flags"])
        self.assertIn(pn.TEE_PAIR_FLAG, tee["flags"])
        umap48 = cells[("throughput", "single", "umap", "k8v48", "intel", "ops")]
        self.assertEqual((umap48["campaign"], umap48["flags"]), ("rehearsal-c4-tdx-table1-scalar", ""))

    def test_missing_inputs(self):
        b = Builder()
        b.row("c4-tdx-table1-scalar", "auto", 4, 8, 1 << 27, ops=1165738)
        report, cells, claims, out = self.reduce(b)
        self.assertEqual(report["table1_reproduced"], 1)
        self.assertEqual(claims["ours-vs-h2o2ram-k4v8"]["status"], "missing input")
        self.assertIn("H2O2 single row, 4 B / 8 B, 2^27, c4-tdx, saturated", claims["ours-vs-h2o2ram-k4v8"]["missing"])
        self.assertIn("--write-throughput c4-tdx=OPS", claims["write-vs-lookup"]["missing"])
        self.assertIn("Ours single row, 4 B / 8 B, 2^27, oci-zen5-snp, saturated",
                      claims["write-vs-lookup"]["missing"])
        self.assertEqual(cells[("response", "single", "ours", "k4v8", "intel", "mean")]["status"], "missing input")
        md = (out / "claims.md").read_text()
        self.assertIn("- reproduced: missing input", md)
        self.assertIn("## Missing inputs", (out / "table1.md").read_text())

    def test_bad_inputs_are_reported_not_fatal(self):
        b = Builder()
        n = 1 << 27
        # A saturated source without a drained rate and no fixed row: the response fallback must not crash.
        b.row("c4-tdx-baseline-h2o2ram-table", "h2o2ram", 4, 8, n, ops=None)
        b.row("c4-tdx-baseline-h2o2ram-table", "h2o2ram", 4, 8, n, arrival="fixed", mean=4e9, p99=9e10,
              rate={"kind": "absolute", "ops_per_second": 40755})
        b.row("c4-tdx-table1-scalar", "auto", 4, 8, n, ops=1165738)
        reps = b.campaigns["c4-tdx-table1-scalar"]
        reps.append({"trial_id": "trial-v1-nospec", "summary": {}})  # no spec
        reps.append({"trial_id": "trial-v1-nosummary", "spec": reps[0]["spec"]})  # no summary
        report, cells, _, _ = self.reduce(b)
        self.assertEqual(cells[("throughput", "single", "ours", "k4v8", "intel", "ops")]["reproduced"], "1.17 M")
        h2 = cells[("throughput", "single", "h2o2ram", "k4v8", "intel", "ops")]
        self.assertEqual(h2["status"], "missing input")
        self.assertIn("no drained rate", h2["note"])
        self.assertEqual(cells[("response", "single", "h2o2ram", "k4v8", "intel", "mean")]["status"],
                         "missing input")
        self.assertEqual([(s["trial_id"], s["reason"]) for s in report["skipped_repetitions"]],
                         [("trial-v1-nospec", "no spec"), ("trial-v1-nosummary", "no summary")])

    def test_raw_files_are_optional(self):
        b = Builder()
        n = 1 << 27
        b.row("c4-tdx-table1-batch", P88, 4, 8, n, api="batch", batch=64, ops=3374988)
        b.row("c4-tdx-baseline-sonic-table-batch", SONIC, 4, 8, n, api="batch", batch=64, ops=47721)
        source, _ = b.row("c4-tdx-baseline-h2o2ram-table", "h2o2ram", 4, 8, n, ops=81511)
        b.fixed("c4-tdx-baseline-h2o2ram-table", source, 500_000, 4.02e9, 90.4e9, maximum=117.4e9,
                candidate="h2o2ram", key=4, value=8, capacity=n)
        _, _, claims, _ = self.reduce(b)
        sonic = claims["ours-vs-sonic-data-tree-k4v8"]
        self.assertEqual(sonic["status"], "missing input")
        self.assertIn("worker/sonic_phases.json", sonic["missing"])
        self.assertIn("--campaign c4-tdx-baseline-sonic-table-batch=DIR", sonic["missing"])
        rebuild = claims["h2o2ram-top-rebuild"]
        self.assertTrue(rebuild["reproduced"].startswith("117 s; missing input"), rebuild["reproduced"])
        self.assertIn("used the half-rate row's maximum response", rebuild["notes"])

    def test_sonic_phases_fall_back_to_a_same_tier_row(self):
        """The K4/V8 cell's row is the faster sweep row (raw files not passed): the table-batch row's phases
        stand in, noted; with neither passed, the missing input names both campaigns."""
        b = Builder()
        n = 1 << 27
        b.row("c4-tdx-table1-batch", P88, 4, 8, n, api="batch", batch=64, ops=3374988)
        table, attempt = b.row("c4-tdx-baseline-sonic-table-batch", SONIC, 4, 8, n, api="batch", batch=64,
                               ops=47721)
        sweep, _ = b.row("c4-tdx-baseline-sonic-throughput", SONIC, 4, 8, n, api="batch", batch=64, ops=48500,
                         formation="fixed_count")
        b.row("c4-tdx-baseline-sonic-throughput", SONIC, 4, 8, n, api="batch", batch=8, ops=99000,
              formation="fixed_count")  # another tier: never read
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        raw = b.worker_file(tmp.name, "c4-tdx-baseline-sonic-table-batch", table, attempt, "sonic_phases.json",
                            phases_json(248981, 0.808))
        _, cells, claims, _ = self.reduce(b, campaign_dirs=[f"c4-tdx-baseline-sonic-table-batch={raw}"])
        self.assertEqual(cells[("throughput", "batch", "sonic", "k4v8", "intel", "ops")]["trial_id"], sweep)
        claim = claims["ours-vs-sonic-data-tree-k4v8"]
        self.assertEqual((claim["reproduced"], claim["status"]), ("14x", "matches"))
        self.assertIn("SONIC phases from c4-tdx-baseline-sonic-table-batch/", claim["notes"])
        self.assertIn("has no worker/sonic_phases.json", claim["notes"])
        _, _, claims, _ = self.reduce(b)
        missing = claims["ours-vs-sonic-data-tree-k4v8"]["missing"]
        self.assertIn("--campaign c4-tdx-baseline-sonic-throughput=DIR", missing)
        self.assertIn("--campaign c4-tdx-baseline-sonic-table-batch=DIR", missing)

    def test_memory_with_either_arrival_alone(self):
        b = Builder()
        n = 1 << 27
        b.row("c4-tdx-baseline-sonic-table-batch", SONIC, 4, 8, n, api="batch", batch=64, ops=47721,
              rss=27.69 + SERVICE_BUFFER)  # no half-rate row
        source, _ = b.row("c4-tdx-baseline-sonic-table-batch", SONIC, 8, 48, 1 << 25, api="batch", batch=64,
                          ops=59626, rss=None)
        b.fixed("c4-tdx-baseline-sonic-table-batch", source, 500_000, 1.1e6, 2.5e6, candidate=SONIC, key=8, value=48,
                capacity=1 << 25, api="batch", batch=64, rss=15.0)  # no saturated peak
        _, cells, _, _ = self.reduce(b)
        k4 = cells[("memory", "single", "sonic", "k4v8", "intel", "peak_rss")]
        self.assertEqual(k4["reproduced"], "27.7 GiB")
        self.assertIn("less its 1024 MiB event buffer", k4["note"])
        k8 = cells[("memory", "single", "sonic", "k8v48", "intel", "peak_rss")]
        self.assertEqual((k8["reproduced"], k8["note"]), ("15.0 GiB", ""))

    def test_full_event_rows_deduct_a_rate_sized_buffer(self):
        spec = {"arrival": "fixed", "caller_batch_size": 1, "batch_policy": {"formation": "fixed_count"},
                "timing": {"measurement_ns": 10**9, "max_accesses": 10**9},
                "instrumentation": {"logging": "full_events", "buffer_bytes": 256 << 20}}
        self.assertEqual(pn.resident_event_buffer(spec, {"offered_ops_per_second": 1000}),
                         (2 * 1016 + 1016 + 1024) * 64)
        self.assertIsNone(pn.resident_event_buffer(spec, {}))
        self.assertEqual(pn.resident_event_buffer({**spec, "instrumentation": {"logging": "histogram_checkpoints"}},
                                                  {}), 0)
        self.assertEqual(pn.resident_event_buffer({**spec, "arrival": "saturated"}, {}), 256 << 20)
        self.assertIsNone(pn.resident_event_buffer({"arrival": "saturated"}, {}))

    def test_sonic_batch_8_rows_are_not_read_and_batch_formation(self):
        b = Builder()
        n = 1 << 27
        b.row("oci-zen5-snp-baseline-sonic-table-batch", SONIC, 4, 8, n, api="batch", batch=8, ops=48360)
        source, _ = b.row("oci-zen5-snp-table1-batch", UMAP, 4, 8, n, api="batch", batch=64, ops=2399532)
        b.fixed("oci-zen5-snp-table1-batch", source, 500_000, 9e3, 9e3, candidate=UMAP, key=4, value=8, capacity=n,
                api="batch", batch=64, formation="fixed_count")  # requests not arriving as whole batches
        _, cells, _, _ = self.reduce(b)
        self.assertEqual(cells[("throughput", "batch", "sonic", "k4v8", "amd", "ops")]["status"], "missing input")
        self.assertEqual(cells[("response", "batch", "umap", "k4v8", "amd", "mean")]["status"], "missing input")

    def test_absolute_rate_fallback(self):
        b = Builder()
        n = 1 << 27
        b.row("c4-tdx-baseline-h2o2ram-table", "h2o2ram", 4, 8, n, ops=81511)
        for rate, mean in ((24453, 1e9), (40755, 4.02e9)):  # 0.3 S is too far; 0.5 S stands in for the fraction
            b.row("c4-tdx-baseline-h2o2ram-table", "h2o2ram", 4, 8, n, arrival="fixed", mean=mean, p99=90.4e9,
                  rate={"kind": "absolute", "ops_per_second": rate})
        _, cells, _, _ = self.reduce(b)
        cell = cells[("response", "single", "h2o2ram", "k4v8", "intel", "mean")]
        self.assertEqual(cell["reproduced"], "4.0 s")
        self.assertIn("absolute rate 40,755 req/s, 0.500 of", cell["note"])

    def test_response_uses_the_fastest_source(self):
        b = Builder()
        n = 1 << 27
        slow, _ = b.row("c4-tdx-table1-scalar", "auto", 4, 8, n, ops=1.0e6)
        fast, _ = b.row("c4-tdx-table1-scalar", "auto", 4, 8, n, ops=1.16e6, boot="b2")  # a second boot
        b.fixed("c4-tdx-table1-scalar", slow, 500_000, 700, 1000, candidate="auto", key=4, value=8, capacity=n)
        b.fixed("c4-tdx-table1-scalar", fast, 500_000, 880, 1320, candidate="auto", key=4, value=8, capacity=n,
                boot="b2")
        _, cells, _, _ = self.reduce(b)
        self.assertEqual(cells[("response", "single", "ours", "k4v8", "intel", "mean")]["reproduced"], "0.88 µs")
        self.assertEqual(cells[("throughput", "single", "ours", "k4v8", "intel", "ops")]["reproduced"], "1.16 M")

    def test_tee_pair_prefers_tee_campaigns(self):
        b = Builder()
        n = 1 << 27
        b.row("c4-tdx-throughput-k4v8", "auto", 4, 8, n, ops=1165738)
        b.row("c4-tdx-tee", "auto", 4, 8, n, ops=1043168)
        b.row("c4-native-tee", "auto", 4, 8, n, ops=1162739)
        _, _, claims, _ = self.reduce(b)
        tee = claims["tee-overhead-intel"]
        self.assertTrue(tee["reproduced"].startswith("10%; missing input"), tee["reproduced"])
        self.assertIn("1,043,168 req/s / 1,162,739 req/s", tee["formula"])
        self.assertEqual(tee["flags"], "")

    def test_tee_pair_uses_one_option_on_both_sides(self):
        """AMD: both sides use the 8 x 8 batch-64 rows; a batch-512 (8 x 64) row on one side is never read."""
        b = Builder()
        n = 1 << 27
        for campaign, single, b512, b64 in (("oci-zen5-snp-tee", 860869, 6566756, 5531267),
                                            ("oci-e6-native-tee", 1394892, None, 7400000)):
            b.row(campaign, "auto", 4, 8, n, ops=single)
            if b512:
                b.row(campaign, "parallel-8x64", 4, 8, n, api="batch", batch=512, ops=b512)
            b.row(campaign, P88, 4, 8, n, api="batch", batch=64, ops=b64)
        _, _, claims, _ = self.reduce(b)
        tee = claims["tee-overhead-amd"]
        self.assertEqual(tee["reproduced"], "38%; 25%")
        self.assertIn("5,531,267 req/s / 7,400,000 req/s", tee["formula"])
        self.assertEqual(tee["flags"], "")
        # No common option at all: missing input, not a mixed pair.
        b = Builder()
        b.row("oci-zen5-snp-tee", "parallel-8x64", 4, 8, n, api="batch", batch=512, ops=6566756)
        b.row("oci-e6-native-tee", P88, 4, 8, n, api="batch", batch=64, ops=7400000)
        _, _, claims, _ = self.reduce(b)
        tee = claims["tee-overhead-amd"]
        self.assertEqual(tee["reproduced"], "missing input; missing input")
        self.assertIn("same candidate and batch size", tee["missing"])

    def test_tee_pair_outside_tee_campaigns_is_flagged(self):
        b = Builder()
        n = 1 << 27
        b.row("c4-tdx-table1-scalar", "auto", 4, 8, n, ops=1165738)  # no c4-tdx-tee summary
        b.row("c4-native-tee", "auto", 4, 8, n, ops=1162739)
        _, _, claims, _ = self.reduce(b)
        tee = claims["tee-overhead-intel"]
        self.assertTrue(tee["reproduced"].startswith("-0%"), tee["reproduced"])
        self.assertIn(pn.TEE_PAIR_FLAG, tee["flags"])
        self.assertIn("not from a '<target>-tee' campaign on c4-tdx", tee["notes"])

    def test_top_rebuild_uses_the_largest_level_across_rows(self):
        b = Builder()
        n = 1 << 27
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        source, a1 = b.row("c4-tdx-baseline-h2o2ram-table", "h2o2ram", 4, 8, n, ops=81511)
        half, a2 = b.fixed("c4-tdx-baseline-h2o2ram-table", source, 500_000, 4.02e9, 90.4e9, candidate="h2o2ram",
                           key=4, value=8, capacity=n)
        b.worker_file(tmp.name, "c4-tdx-baseline-h2o2ram-table", source, a1, "markers.csv",
                      markers_csv([(3, 0.5), (16, 60.0)]))  # its window never reached level 17
        raw = b.worker_file(tmp.name, "c4-tdx-baseline-h2o2ram-table", half, a2, "markers.csv",
                            markers_csv([(3, 0.4), (17, 117.0)]))
        _, _, claims, _ = self.reduce(b, campaign_dirs=[str(raw)])
        rebuild = claims["h2o2ram-top-rebuild"]
        self.assertTrue(rebuild["reproduced"].startswith("117 s"), rebuild["reproduced"])
        self.assertIn("1 top-level rebuild spans (level 17, 1 row), mean 117.0 s", rebuild["formula"])
        self.assertIn("no level-17 rebuild in the markers of", rebuild["notes"])

    def test_figure8_reads_value_width_stages_only(self):
        """Rehearsal: Figure 8 ignores capacity, so it must take the value_width stages only, and Table 1 never
        takes them (SONIC's dense K8 / 1 KiB width row matches its 1 KiB Table 1 shape)."""
        b = Builder()
        small = 1 << 12
        b.row("rehearsal-c4-tdx-table1-scalar", UMAP, 8, 48, small, ops=5e6)  # Table 1 row, K8/V48
        b.row("rehearsal-c4-tdx-width-std-unordered-map", UMAP, 8, 64, small, ops=4e6)
        b.row("rehearsal-c4-tdx-baseline-sonic-table-scalar", SONIC, 8, 1024, small, ops=30000)
        b.row("rehearsal-c4-tdx-baseline-sonic-width", SONIC, 8, 1024, small, ops=45000)
        report, cells, _, out = self.reduce(b, rehearsal=True)
        fig8 = {(r["system"], r["value_bytes"]): r for r in read_csv(out / "fig8.csv") if r["ops_per_second"]}
        self.assertEqual(set(fig8), {("umap", "64"), ("sonic", "1024")})
        self.assertEqual(fig8[("sonic", "1024")]["campaign"], "rehearsal-c4-tdx-baseline-sonic-width")
        sonic = cells[("throughput", "single", "sonic", "k32v1024", "intel", "ops")]
        self.assertEqual((sonic["reproduced"], sonic["campaign"]),
                         ("30 K", "rehearsal-c4-tdx-baseline-sonic-table-scalar"))

    def test_targets(self):
        self.assertEqual(pn.target_of_name("oci-zen5-snp-tee"), "oci-zen5-snp")
        self.assertEqual(pn.target_of_name("c4-native-tee"), "c4-native")
        self.assertIsNone(pn.target_of_name("local-run"))
        self.assertEqual(pn.target_and_item("rehearsal-c4-tdx-table1-scalar", {}), ("c4-tdx", "table1-scalar"))
        self.assertEqual(pn.target_and_item("oci-e6-native-tee", {}), ("oci-e6-native", "tee"))
        self.assertEqual(pn.target_and_item("mine", {"mine": "c4-tdx"}), ("c4-tdx", "mine"))
        self.assertEqual(pn.target_and_item("mine", {"mine": "c4-tdx-table1-scalar"}), ("c4-tdx", "table1-scalar"))
        b = Builder()
        b.row("local-run", "auto", 4, 8, 1 << 27, ops=1165738, runtime="tdx")  # runtime decides: c4-tdx
        b.row("local-native", "auto", 4, 8, 1 << 27, ops=844715)  # native without a mapping: no target
        report, cells, _, _ = self.reduce(b)
        ours = cells[("throughput", "single", "ours", "k4v8", "intel", "ops")]
        self.assertEqual((ours["reproduced"], ours["flags"]), ("1.17 M", "not_paper_preset"))
        self.assertEqual(report["campaigns_without_target"], ["local-native"])
        report, cells, _, _ = self.reduce(b, targets={"local-native": "oci-zen5-snp"})
        amd = cells[("throughput", "single", "ours", "k4v8", "amd", "ops")]
        self.assertEqual((amd["reproduced"], amd["flags"]),
                         ("845 K", "not_paper_preset;runtime_native_on_oci-zen5-snp"))
        # A renamed copy of a preset is declared with NAME=TARGET-ITEM.
        report, cells, _, _ = self.reduce(b, targets={"local-run": "c4-tdx-table1-scalar"})
        ours = cells[("throughput", "single", "ours", "k4v8", "intel", "ops")]
        self.assertEqual((ours["reproduced"], ours["flags"]), ("1.17 M", ""))
        self.assertNotIn("local-run", report["campaigns_not_paper_presets"])
        for bad in ("laptop", "c4-tdx-nonsense", "c4-native-table1-scalar"):
            with self.assertRaises(SystemExit):
                self.reduce(b, targets={"local-native": bad})

    def test_summary_given_twice_counts_once(self):
        b = Builder()
        b.row("c4-tdx-table1-scalar", "auto", 4, 8, 1 << 27, ops=1165738)
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        paths = b.write(tmp.name)
        report = run(paths + paths, Path(tmp.name) / "out")
        self.assertEqual(report["rows"], 1)

    def test_command_line(self):
        b = Builder()
        b.row("c4-tdx-table1-scalar", "auto", 4, 8, 1 << 27, ops=1165738)
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        paths = b.write(tmp.name)
        out = Path(tmp.name) / "cli"
        stream = io.StringIO()
        with contextlib.redirect_stdout(stream):
            code = pn.main([str(paths[0]), "--output", str(out), "--no-figures",
                            "--write-throughput", "c4-tdx=4710600", "--target", "x=c4-tdx"])
        self.assertEqual(code, 0)
        self.assertEqual(json.loads(stream.getvalue())["table1_reproduced"], 1)
        for name in ("table1.md", "table1.csv", "fig7.csv", "fig8.csv", "claims.md", "claims.csv", "rows.csv"):
            self.assertTrue((out / name).exists(), name)
        claims = {r["id"]: r for r in read_csv(out / "claims.csv")}
        self.assertTrue(claims["write-vs-lookup"]["reproduced"].startswith("4.0x"))
        with self.assertRaises(SystemExit), contextlib.redirect_stderr(io.StringIO()):
            pn.main([str(paths[0]), "--output", str(out), "--target", "nonsense"])


class LocalReducedSummaries(unittest.TestCase):
    """Two summaries reduced from a scaled native run of the release harness (N = 2^14..2^16), scrubbed of build,
    environment, group and trial hashes. Rehearsal mode maps them onto the Table 1 and Figure 8 cells."""

    def test_fixtures_hold_no_host_hashes(self):
        for path in FIXTURES.glob("*.json"):
            text = path.read_text()
            hashes = [h for h in re.findall(r"[0-9a-f]{16,}", text) if set(h) != {"0"} and not h.isdigit()]
            self.assertEqual(hashes, [], path.name)

    def test_rehearsal_over_real_summaries(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        out = Path(tmp.name) / "out"
        paths = [FIXTURES / "local-table-summary.json", FIXTURES / "local-width-summary.json"]
        targets = {"local-paper-numbers-table": "c4-tdx", "local-paper-numbers-width": "c4-tdx"}
        strict = run(paths, Path(tmp.name) / "strict", targets=targets)
        self.assertEqual((strict["rows"], strict["table1_reproduced"]), (19, 0))  # no row at the paper's N
        report = run(paths, out, targets=targets, rehearsal=True)
        self.assertTrue(report["rehearsal"])
        self.assertEqual(report["campaigns_not_paper_presets"],
                         ["local-paper-numbers-table", "local-paper-numbers-width"])
        cells = cells_of(out)
        present = {k for k, r in cells.items() if r["reproduced"]}
        expected = {("throughput", "single", "ours", "k4v8", "intel", "ops"),
                    ("throughput", "batch", "ours", "k4v8", "intel", "ops"),
                    ("throughput", "single", "umap", "k4v8", "intel", "ops"),
                    ("throughput", "batch", "umap", "k4v8", "intel", "ops"),
                    ("throughput", "single", "ours", "k32v1024", "intel", "ops"),
                    ("response", "single", "ours", "k4v8", "intel", "mean"),
                    ("response", "batch", "ours", "k4v8", "intel", "p99"),
                    ("response", "batch", "umap", "k4v8", "intel", "mean"),
                    ("response", "single", "ours", "k32v1024", "intel", "p99"),
                    ("memory", "single", "ours", "k4v8", "intel", "peak_rss")}
        self.assertLessEqual(expected, present)
        self.assertEqual(report["table1_reproduced"], 18)
        for key in present:  # native rows of local campaigns standing in for a TDX target are flagged
            self.assertIn("runtime_native_on_c4-tdx", cells[key]["flags"])
            self.assertIn("not_paper_preset", cells[key]["flags"])
        batch = cells[("throughput", "batch", "ours", "k4v8", "intel", "ops")]
        self.assertEqual(batch["row_capacity"], "65536")
        self.assertIn("Rehearsal", (out / "table1.md").read_text())
        claims = {r["id"]: r for r in read_csv(out / "claims.csv")}
        self.assertNotEqual(claims["ours-vs-umap-k4v8"]["status"], "missing input")
        self.assertNotEqual(claims["hybrid-vs-hierarchy-1k"]["reproduced"].split(";")[0], "missing input")
        fig8 = [r for r in read_csv(out / "fig8.csv") if r["ops_per_second"]]
        self.assertEqual({r["value_bytes"] for r in fig8}, {"32", "64", "96", "1024"})
        self.assertTrue(all(r["memory_metric"] == "library_reserved" for r in fig8))
        # Declared as a renamed copy of the width preset, the width summary's rows are paper rows.
        report = run(paths, Path(tmp.name) / "mapped", rehearsal=True,
                     targets={"local-paper-numbers-table": "c4-tdx", "local-paper-numbers-width": "c4-tdx-width"})
        self.assertEqual(report["campaigns_not_paper_presets"], ["local-paper-numbers-table"])


if __name__ == "__main__":
    unittest.main()
