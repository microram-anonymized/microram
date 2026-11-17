"""analysis/paper_micro.py without running a real driver: CPU choices on fake
sysfs trees (adjacent and k/k+N sibling numbering), the planned commands, the
summarizers on synthetic driver output, the whole-L3 judge on canned curves,
and the runner end to end with stub executables."""
from pathlib import Path
import contextlib
import io
import json
import os
import socket
import stat
import sys
import tempfile
import textwrap
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "analysis"))
import paper_micro as pm


def fake_sysfs(root, siblings, l3, offline=()):
    """siblings / l3: cpu -> sysfs list text; offline CPUs get only `online` = 0."""
    for cpu in sorted(set(siblings) | set(offline)):
        base = Path(root) / ("cpu%d" % cpu)
        base.mkdir(parents=True)
        if cpu in offline:
            (base / "online").write_text("0\n")
            continue
        (base / "online").write_text("1\n")
        (base / "topology").mkdir()
        (base / "topology" / "thread_siblings_list").write_text(siblings[cpu] + "\n")
        for index, level, shared in (("index0", "1", siblings[cpu]), ("index2", "2", siblings[cpu]),
                                     ("index3", "3", l3[cpu])):
            (base / "cache" / index).mkdir(parents=True)
            (base / "cache" / index / "level").write_text(level + "\n")
            (base / "cache" / index / "shared_cpu_list").write_text(shared + "\n")
    (Path(root) / "cpufreq").mkdir()  # a non-CPU entry is ignored


def oracle_tree(root, offline=()):
    """Oracle E6 16 OCPU: siblings 2k, 2k+1; two CCDs at 0-15 and 16-31."""
    cpus = [c for c in range(32) if c not in offline]
    fake_sysfs(root, {c: "%d-%d" % (c & ~1, c | 1) for c in cpus},
               {c: "0-15" if c < 16 else "16-31" for c in cpus}, offline)
    return pm.read_topology(root)


def c4_tree(root):
    """C4 c4-standard-32: siblings k, k+16; one L3."""
    fake_sysfs(root, {c: "%d,%d" % (c % 16, c % 16 + 16) for c in range(32)}, {c: "0-31" for c in range(32)})
    return pm.read_topology(root)


def write(path, text):
    Path(path).write_text(textwrap.dedent(text).lstrip())


def jsonl(path, rows):
    Path(path).write_text("".join(json.dumps(r) + "\n" for r in rows))


def run_main(argv, topo=None):
    out = io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(io.StringIO()):
        code = pm.main(argv, topo_loader=(lambda: topo) if topo is not None else None)
    return code, out.getvalue()


def values(summary):
    return {it["name"]: it for it in summary["items"]}


def fit_output(run, levels=()):
    lines = ["level arena: incremental storage ..."]
    lines.append("FIT_ROW " + json.dumps(dict(fit_row="run", **run)))
    lines += ["FIT_ROW " + json.dumps(dict(fit_row="level", level=i + 1, job_nanos=j)) for i, j in enumerate(levels)]
    return "\n".join(lines) + "\n"


class TopologyTest(unittest.TestCase):
    def test_parse_cpulist(self):
        self.assertEqual(pm.parse_cpulist("0-3,8,10-11\n"), [0, 1, 2, 3, 8, 10, 11])
        self.assertEqual(pm.parse_cpulist(""), [])
        self.assertEqual(pm.cpulist([2, 4, 6]), "2,4,6")

    def test_adjacent_siblings_oracle(self):
        with tempfile.TemporaryDirectory() as d:
            topo = oracle_tree(d)
        self.assertEqual(pm.physical_cores(topo), list(range(0, 32, 2)))
        self.assertEqual(pm.paper_cpus(topo), list(range(2, 32, 2)))
        self.assertEqual(pm.l3_domains(topo), [list(range(0, 16, 2)), list(range(16, 32, 2))])
        self.assertEqual(pm.l3_check_cpus(topo), [2, 18])
        lay = pm.layout(pm.paper_cpus(topo))
        self.assertEqual(lay["caller"], [2])
        self.assertEqual(lay["rebuild"], list(range(4, 32, 2)))
        self.assertEqual(lay["batch"], list(range(16, 32, 2)))  # CCD 1
        self.assertEqual(lay["batch_rebuild"], list(range(2, 16, 2)))  # CCD 0

    def test_k_plus_n_siblings_c4(self):
        with tempfile.TemporaryDirectory() as d:
            topo = c4_tree(d)
        self.assertEqual(pm.physical_cores(topo), list(range(16)))
        self.assertEqual(pm.paper_cpus(topo), list(range(1, 16)))
        self.assertEqual(pm.l3_check_cpus(topo), [1])
        lay = pm.layout(pm.paper_cpus(topo))
        self.assertEqual((lay["caller"], lay["rebuild"]), ([1], list(range(2, 16))))
        self.assertEqual((lay["batch"], lay["batch_rebuild"]), (list(range(8, 16)), list(range(1, 8))))

    def test_offline_cpus_and_no_smt(self):
        with tempfile.TemporaryDirectory() as d:
            topo = oracle_tree(d, offline=(3,))
        self.assertNotIn(3, topo)
        self.assertIn(2, pm.paper_cpus(topo))
        with tempfile.TemporaryDirectory() as d:
            fake_sysfs(d, {c: str(c) for c in range(8)}, {c: "0-7" for c in range(8)})
            topo = pm.read_topology(d)
        self.assertEqual(pm.paper_cpus(topo), list(range(1, 8)))
        self.assertEqual(pm.l3_check_cpus(topo), [1])

    def test_cpus_subcommand_and_sysfs_flag(self):
        with tempfile.TemporaryDirectory() as d:
            oracle_tree(d)
            code, text = run_main(["--sysfs", d, "cpus"])
        self.assertEqual(code, 0)
        self.assertIn("l3_check_cpus", text)
        self.assertIn("[2, 18]", text)


class PlanTest(unittest.TestCase):
    def test_arena_rows_use_one_cpu_per_core(self):
        with tempfile.TemporaryDirectory() as d:
            topo = oracle_tree(d)
            code, text = run_main(["tables-per-lookup", "--out", d + "/o", "--dry-run"], topo)
            self.assertEqual(code, 0)
            scalar, batch = [line for line in text.splitlines() if line.startswith("tables-")]
            self.assertIn("taskset -c 2 build/benchmarks/cpu_byteslice_level_arena_benchmark", scalar)
            self.assertIn("--rebuild-threads 14 --rebuild-cpus 4,6,8,10,12,14,16,18,20,22,24,26,28,30", scalar)
            self.assertIn("--capacity 134217728", scalar)
            self.assertIn("--read-only --probe-counts", scalar)
            self.assertIn("taskset -c 16,18,20,22,24,26,28,30 ", batch)
            self.assertIn("--rebuild-threads 7 --rebuild-cpus 2,4,6,8,10,12,14", batch)
            self.assertIn("--batch 64 --lanes 8 --participants 8 --parallel", batch)
            code, text = run_main(["write-throughput", "--out", d + "/w", "--dry-run", "--caller", "1",
                                   "--rebuild-cpus", "2-15"], topo)
            self.assertIn("taskset -c 1 ", text)
            self.assertIn("--rebuild-threads 14 --rebuild-cpus 2,3,4,5,6,7,8,9,10,11,12,13,14,15 --write-only "
                          "--merge-rows --probe-counts", text)
            self.assertFalse(Path(d, "o").exists())  # a dry run writes nothing

    def test_table_rebuild_steps_port_the_record_pass(self):
        a = pm.build_parser().parse_args(["table-rebuild", "--out", "x", "--max-log2", "14", "--values", "8",
                                          "64", "--cpu", "3"])
        pm.resolve(a, lambda: None)
        steps = pm.plan_table_rebuild(a)
        self.assertEqual(len(steps), 2 * (5 + 1 + 2 * 5))
        chain = [argv for stem, argv, _ in steps if stem == "ours-chain-v8"]
        self.assertEqual(chain[0][chain[0].index("--capacity") + 1], str(1 << 16))
        h2 = [argv for stem, argv, _ in steps if stem == "h2o2ram-v64-s128"]
        self.assertEqual(h2[0][:3], ["taskset", "-c", "3"])
        self.assertIn("--bucket-slots", h2[0])

    def test_eviction_rotates_the_arm_order(self):
        a = pm.build_parser().parse_args(["eviction", "--out", "x", "--cpu", "1"])
        pm.resolve(a, lambda: None)
        steps = pm.plan_eviction(a)
        self.assertEqual(len(steps), 9)
        by_round = [[s[0].split("-", 2)[2] for s in steps[i:i + 3]] for i in (0, 3, 6)]
        for position in range(3):
            self.assertEqual(sorted(r[position] for r in by_round),
                             ["enigmap", "read_path", "read_path_transposed"])
        argv = steps[0][1]
        for flag, value in (("--capacity", "2097152"), ("--key-bytes", "4"), ("--fold", "4"),
                            ("--stash-registers", "3"), ("--passes", "20000"), ("--verify-passes", "1000")):
            self.assertEqual(argv[argv.index(flag) + 1], value)
        self.assertEqual(pm.eviction_arms("cpu_tree_eviction_comparator_benchmark"),
                         ["read_path", "read_path_transposed"])

    def test_placement_is_validated(self):
        for extra in (["--batch-cpus", "20-23"], ["--caller", "2", "--rebuild-cpus", "2-15"]):
            code, _ = run_main(["tables-per-lookup", "--out", "x", "--dry-run"] + extra)
            self.assertEqual(code, 2, extra)

    def test_memory_latency_needs_a_touch_size(self):
        code, _ = run_main(["memory-latency", "--out", "x", "--region-core", "2"])
        self.assertEqual(code, 2)  # a usage error, never the 0/1 of a result
        a = pm.build_parser().parse_args(["memory-latency", "--out", "x", "--touch-gib", "110", "--region-core",
                                          "2", "--sudo"])
        pm.resolve(a, lambda: None)
        touch, core = pm.plan_memory_latency(a)
        self.assertEqual(touch[1][:4], ["sudo", "build/benchmarks/cpu_host_topology_probe", "--tests", "region"])
        self.assertIn("--region-lines-per-page", touch[1])
        self.assertEqual(core[1][1:], ["--tests", "core"])


class SummaryTest(unittest.TestCase):
    def test_table_rebuild(self):
        with tempfile.TemporaryDirectory() as d:
            sizes = (1 << 10, 1 << 20)
            jsonl(Path(d, "ours-init-v8.jsonl"),
                  [dict(mode="init", table_entries=n, median_ms=n / 1e5) for n in sizes])
            jsonl(Path(d, "ours-chain-v8.jsonl"),
                  [dict(mode="chain", row="window", accesses=5)] +
                  [dict(mode="chain", row="cascade", top=False, table_entries=n, median_ms=n / 2e4) for n in sizes] +
                  [dict(mode="chain", row="cascade", top=True, table_entries=1 << 22, median_ms=1.0),
                   dict(mode="chain", row="job", table_entries=1 << 20, median_ms=9.0)])
            for slots, scale in ((64, 1), (128, 1.8)):
                jsonl(Path(d, "h2o2ram-v8-s%d.jsonl" % slots),
                      [dict(live=n, median_ms=scale * n / 400.0 * (1 + (n > 1024)), lost_to_overflow=0)
                       for n in sizes])
            s = pm.summarize_table_rebuild(d)
        q = values(s)
        # speedups with dups: 1024 -> (1024/400)/(1024/2e4) = 50x; 2^20 -> 100x.
        self.assertEqual(q["V8 speedup with duplicates (H2O2RAM 64-slot / ours chain), 2^10..2^20"]["reproduced"],
                         "50x .. 100x")
        self.assertAlmostEqual(q["V8 2^20: ours with duplicates (chain cascade)"]["reproduced"], (1 << 20) / 2e4)
        self.assertAlmostEqual(q["V8 2^20: H2O2RAM 64-slot build"]["reproduced"], 2 * (1 << 20) / 400.0)
        self.assertIn("Intel 30-54x", q["V8 speedup with duplicates (H2O2RAM 64-slot / ours chain), 2^10..2^20"]
                      ["paper"])
        self.assertEqual(s["problems"], [])

    def test_routing_locality_quotes_the_lower_run(self):
        with tempfile.TemporaryDirectory() as d:
            for i, ratio in ((1, 3.47), (2, 3.22)):
                jsonl(Path(d, "routes-%d.jsonl" % i), [
                    dict(mode="instances", network="flat", status="ok", route_ms_median=80.0),
                    dict(mode="instances", network="cache_oblivious", status="ok", route_ms_median=80 / ratio),
                    dict(mode="instances_ratio", route_ratio_median=ratio, route_ratio_min=ratio - 0.1,
                         route_ratio_max=ratio + 0.1, instances=8, cpus="1-8")])
            s = pm.summarize_routing_locality(d)
        q = values(s)
        self.assertEqual(q["lower of the runs (the paper quotes the lower)"]["reproduced"], 3.22)
        self.assertEqual(s["problems"], [])

    def test_vp2intersect_merge_ratio(self):
        with tempfile.TemporaryDirectory() as d:
            for arm, compiled, scale in (("native", 1, 1.0), ("fallback", 0, 1.7)):
                write(Path(d, "%s-dedup-half.txt" % arm), """
                    cpu_byteslice_dedup_kernel_benchmark: ns per 64 x 64 bucket pair, 2000000 pairs x 1 reps \
(VP2INTERSECT compiled: %d)
                      key  kernel               min   median      max
                      4 B  self                 6.7      6.7      6.7
                    """ % compiled)
                for n in (2048, 32768):
                    text = "".join(fit_output(dict(capacity=n, key_bytes=4, value_bytes=8),
                                              [scale * n * k for k in (100, 200)]) for _ in range(3))
                    Path(d, "%s-merge-%d-plain.txt" % (arm, n)).write_text(text)
            s = pm.summarize_vp2intersect_merge(d)
        q = values(s)
        self.assertAlmostEqual(q["N=2,048: complete merge, fallback / native"]["reproduced"], 1.7)
        self.assertEqual(q["range over the sizes"]["reproduced"], "1.70x .. 1.70x")
        self.assertEqual(s["problems"], [])
        self.assertTrue(s["details"]["native_vp2intersect_compiled"])
        self.assertAlmostEqual(s["details"]["sizes"][2048]["native_merge_ms"], 2048 * 300 / 1e6)

    def test_vp2intersect_without_the_instruction_is_flagged(self):
        with tempfile.TemporaryDirectory() as d:
            for arm in ("native", "fallback"):
                Path(d, "%s-dedup-half.txt" % arm).write_text("x (VP2INTERSECT compiled: 0)\n")
                Path(d, "%s-merge-2048-plain.txt" % arm).write_text(fit_output(dict(capacity=2048), [1e6]))
            s = pm.summarize_vp2intersect_merge(d)
        self.assertTrue(any("no VP2INTERSECT" in p for p in s["problems"]))

    def test_tables_per_lookup(self):
        with tempfile.TemporaryDirectory() as d:
            for name, mean in (("tables-read-only-scalar", 6.26), ("tables-read-only-batch64", 7.771),
                               ("tables-mixed-scalar", 6.4)):
                Path(d, name + ".txt").write_text(fit_output(dict(
                    capacity=pm.N27, levels=7, owners=6, top_helpers=5, lookup_mains_mean=mean, lookup_mains_max=8,
                    completed_records_per_s=1.2e6)))
            Path(d, "tables-mixed-batch64.txt").write_text("crashed\n")
            s = pm.summarize_tables_per_lookup(d)
        names = [it["name"] for it in s["items"]]
        self.assertTrue(names[0].startswith("read-only scalar"))
        self.assertTrue(names[1].startswith("read-only batch64"))
        self.assertEqual(s["items"][0]["reproduced"], 6.26)
        self.assertEqual(s["items"][0]["paper"], pm.PAPER["tables_scalar"])
        self.assertEqual(s["items"][1]["paper"], pm.PAPER["tables_batch"])
        self.assertEqual(s["problems"], ["tables-mixed-batch64.txt: no FIT_ROW run row"])

    def test_write_throughput(self):
        with tempfile.TemporaryDirectory() as d:
            Path(d, "write-only.txt").write_text(
                "MERGE_ROW {}\n" + fit_output(dict(capacity=pm.N27, accesses=pm.N27, owners=6, top_helpers=5,
                                                   write_only=True, preroute=True,
                                                   completed_records_per_s=4.71e6)))
            s = pm.summarize_write_throughput(d, scalar_rate=1165738)
        q = values(s)
        self.assertAlmostEqual(q["all-write rate"]["reproduced"], 4.71)
        self.assertIn("11 rebuild threads", q["all-write rate"]["note"])
        ratio = [it for it in s["items"] if it["name"].startswith("over the measured")][0]
        self.assertAlmostEqual(ratio["reproduced"], 4.71e6 / 1165738)
        self.assertEqual(s["problems"], [])

    def test_eviction_medians_over_rounds(self):
        with tempfile.TemporaryDirectory() as d:
            for r, (t, e) in enumerate(((8000, 440000), (8100, 442000), (8300, 450000)), 1):
                for arm, ns in (("read_path_transposed", t), ("enigmap", e), ("read_path", t - 500)):
                    jsonl(Path(d, "evict-r%d-%s.jsonl" % (r, arm)), [
                        dict(arm=arm, value_bytes=1024, ns_per_pass=ns, status="ok", capacity=2097152, fold=4,
                             stash_registers=3),
                        dict(arm=arm, value_bytes=64, ns_per_pass=ns / 10, status="overflow")])
            s = pm.summarize_eviction(d)
        q = values(s)
        self.assertAlmostEqual(q["V=1024: ours (read_path_transposed), median over rounds"]["reproduced"], 8.1)
        self.assertAlmostEqual(q["V=1024: EnigMap, median over rounds"]["reproduced"], 442.0)
        self.assertEqual(len(s["problems"]), 9)  # the non-ok rows are reported and left out
        self.assertTrue(any("55x" in line for line in s["table"]))

    def test_memory_latency(self):
        with tempfile.TemporaryDirectory() as d:
            Path(d, "touch.txt").write_text('PROBE_SUMMARY {"cores":16,"region_ns_median":210.0}\n')
            Path(d, "core.txt").write_text('[core] ...\n  cpu  2  204.0\n\nPROBE_SUMMARY {"cores":16,'
                                           '"core_dram_ns_min":199.0,"core_dram_ns_median":205.2,'
                                           '"core_dram_ns_max":214.0}\n')
            s = pm.summarize_memory_latency(d)
            self.assertEqual(s["items"][0]["reproduced"], 205.2)
            self.assertEqual(s["problems"], [])
            os.remove(Path(d, "touch.txt"))
            self.assertTrue(pm.summarize_memory_latency(d)["problems"])


WHOLE = """
cpu 2; sysfs L1d 48 KiB, L2 1024 KiB, L3 32768 KiB; buffer 64 MiB, 64 MiB on huge pages; one line per 64 B
  working set    ns/load
       8.0 MiB      9.80
      13.5 MiB     11.90
      16.0 MiB     14.10
      19.0 MiB     16.60
      22.6 MiB     19.70
      26.9 MiB     21.80
      32.0 MiB     28.00
L1 1.00 ns, L2 3.00 ns, L3 10.0 ns (at 4096 KiB), DRAM 120.00 ns (at 64 MiB); usable cache 32.0 MiB
"""
CAPPED = WHOLE.replace("     19.70", "     82.10").replace("     21.80", "     98.40")
LLCPAR_WHOLE = """
[llcpar] llc chase on 8 cores at once (one slot per 128 B), ns per core: 0 2 4 6 8 10 12 14
    1 MiB each (   8 MiB together)  median 12.1  max 12.5
    4 MiB each (  32 MiB together)  median 15.2  max 15.9
"""


class L3JudgeTest(unittest.TestCase):
    def test_whole_and_capped_curves(self):
        verdict, failures, points = pm.judge_l3([("cpu2", WHOLE), ("cpu18", WHOLE)], [("ccd0", LLCPAR_WHOLE)])
        self.assertEqual((verdict, failures), ("WHOLE", []))
        self.assertEqual(points["cpu2"], {"16.0": 14.1, "22.6": 19.7, "26.9": 21.8})
        verdict, failures, _ = pm.judge_l3([("cpu2", WHOLE), ("cpu18", CAPPED)])
        self.assertEqual(verdict, "CAPPED")
        self.assertEqual(len(failures), 2)
        self.assertTrue(failures[0].startswith("cpu18: 22.6 MiB 82.10 ns"))

    def test_llcpar_missing_points_and_no_curves(self):
        slow = LLCPAR_WHOLE.replace("median 15.2", "median 31.0")
        self.assertEqual(pm.judge_l3([("cpu2", WHOLE)], [("ccd0", slow)])[0], "CAPPED")
        short = "\n".join(line for line in WHOLE.splitlines() if "26.9 MiB" not in line)
        verdict, failures, _ = pm.judge_l3([("cpu2", short)])
        self.assertEqual(verdict, "CAPPED")
        self.assertIn("no 26.9 MiB point", failures[0])
        self.assertEqual(pm.judge_l3([])[0], "CAPPED")
        self.assertEqual(pm.parse_limits("16:16,22.6:23.5"), {"16.0": 16.0, "22.6": 23.5})

    def test_plan_one_core_per_l3_domain(self):
        with tempfile.TemporaryDirectory() as d:
            topo = oracle_tree(d)
        a = pm.build_parser().parse_args(["l3-check", "--out", "x", "--llcpar", "--rounds", "2"])
        pm.resolve(a, lambda: topo)
        stems = [s[0] for s in pm.plan_l3_check(a)]
        self.assertEqual(stems, ["l3-r1-cpu2", "l3-r1-cpu18", "llcpar-r1-d0", "llcpar-r1-d1",
                                 "l3-r2-cpu2", "l3-r2-cpu18", "llcpar-r2-d0", "llcpar-r2-d1"])
        llcpar = pm.plan_l3_check(a)[2][1]
        self.assertEqual(llcpar[llcpar.index("--llcpar-cores") + 1], "0,2,4,6,8,10,12,14")
        a = pm.build_parser().parse_args(["l3-check", "--out", "x", "--llcpar", "--cpus", "4",
                                          "--llcpar-cores", "1-4;5-8", "--max-mib", "512"])
        pm.resolve(a, lambda: topo)
        steps = pm.plan_l3_check(a)
        self.assertEqual(steps[0][1][1:], ["--cpu", "4", "--max-mib", "512"])
        self.assertEqual([s[1][s[1].index("--llcpar-cores") + 1] for s in steps[1:]], ["1,2,3,4", "5,6,7,8"])

    def test_exit_status_from_a_saved_check(self):
        with tempfile.TemporaryDirectory() as d:
            Path(d, "l3-r1-cpu2.txt").write_text(WHOLE)
            Path(d, "l3-r1-cpu18.txt").write_text(WHOLE)
            code, text = run_main(["l3-check", "--out", d, "--summarize-only"])
            self.assertEqual(code, 0)
            self.assertIn("WHOLE", text)
            Path(d, "l3-r2-cpu18.txt").write_text(CAPPED)
            code, text = run_main(["l3-check", "--out", d, "--summarize-only"])
            self.assertEqual(code, 1)
            self.assertEqual(json.loads(Path(d, "summary.json").read_text())["verdict"], "CAPPED")
            # Relaxed limits judge the same curves whole.
            code, _ = run_main(["l3-check", "--out", d, "--summarize-only", "--limits", "16.0:20,22.6:90,26.9:99"])
            self.assertEqual(code, 0)


STUB_OURS = """#!%s
import json, sys
args = dict(zip(sys.argv[1::2], sys.argv[2::2]))
n = int(args["--capacity"])
if args["--mode"] == "init":
    print(json.dumps({"mode": "init", "table_entries": n, "median_ms": n / 1e5}))
else:
    print(json.dumps({"mode": "chain", "row": "window"}))
    e = 512
    while e < n:
        print(json.dumps({"mode": "chain", "row": "cascade", "top": False, "table_entries": e,
                          "median_ms": e / 4e4}))
        e *= 2
    print(json.dumps({"mode": "chain", "row": "cascade", "top": True, "table_entries": n, "median_ms": 1}))
sys.stderr.write("stub done\\n")
"""


class RunnerTest(unittest.TestCase):
    def stub(self, d, name, text):
        path = Path(d) / name
        path.write_text(text % sys.executable)
        path.chmod(path.stat().st_mode | stat.S_IXUSR)
        return str(path)

    def test_table_rebuild_end_to_end_with_a_stub(self):
        with tempfile.TemporaryDirectory() as d:
            ours = self.stub(d, "cpu_byteslice_table_rebuild_benchmark", STUB_OURS)
            out = Path(d) / "out"
            argv = ["table-rebuild", "--out", str(out), "--ours", ours, "--h2o2ram-bench", "", "--cpu", "0",
                    "--max-log2", "12", "--values", "8"]
            code, text = run_main(argv)
            self.assertEqual(code, 0)
            self.assertIn("V8 speedup without duplicates", text)
            log = (out / "commands.log").read_text()
            self.assertIn("binary cpu_byteslice_table_rebuild_benchmark sha256 ", log)
            self.assertEqual(log.count(" exit=0 "), 3 + 1)
            self.assertNotIn(d, log)  # base names only: no home directory
            host = socket.gethostname()
            if len(host) >= 6:  # a short name can occur inside a hash by chance
                self.assertNotIn(host, log.split())
            self.assertEqual(len((out / "ours-init-v8.jsonl").read_text().splitlines()), 3)
            summary = json.loads((out / "summary.json").read_text())
            self.assertTrue(any("no H2O2RAM 64-slot rows" in p for p in summary["problems"]))
            code, _ = run_main(argv)  # a second run never appends to the first
            self.assertEqual(code, 2)
            code, again = run_main(["table-rebuild", "--out", str(out), "--summarize-only"])
            self.assertEqual(code, 0)
            self.assertIn("V8 speedup without duplicates (H2O2RAM 64-slot / ours init): -", again)

    def test_failing_step_sets_the_exit_status(self):
        with tempfile.TemporaryDirectory() as d:
            bad = self.stub(d, "cpu_byteslice_stash_rebuild_benchmark", "#!%s\nimport sys\nsys.exit(3)\n")
            out = Path(d) / "out"
            code, text = run_main(["routing-locality", "--out", str(out), "--binary", bad, "--cpus", "0-7",
                                   "--repeats", "1"])
            self.assertEqual(code, 2)
            summary = json.loads((out / "summary.json").read_text())
            self.assertEqual(summary["failed_steps"], ["routes-1"])
            self.assertIn("exit=3", (out / "commands.log").read_text())


if __name__ == "__main__":
    unittest.main()
