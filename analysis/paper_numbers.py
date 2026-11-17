#!/usr/bin/env python3
"""The paper's measured numbers from reduced campaign summaries.

    python3 analysis/paper_numbers.py SUMMARY.json... [--campaign [NAME=]DIR ...]
        [--target NAME=TARGET ...] [--write-throughput TARGET=OPS ...] --output DIR

Each SUMMARY.json is the summary.json that `python3 -m analysis.oram_bench reduce`
wrote for one campaign (a directory holding summary.json is accepted too). The
campaign name selects the target and the item: a paper preset is named
<target>-<item> (benchmarks/campaigns/paper/<target>-<item>.json; a rehearsal
copy adds the prefix rehearsal-), with target c4-tdx, c4-native, oci-zen5-snp or
oci-e6-native and an item of make_presets.py's ITEMS (mirrored in PAPER_ITEMS
below). `--target NAME=TARGET` assigns any other campaign to a target, and
`--target NAME=TARGET-ITEM` declares a renamed copy of that paper preset; a
campaign without a target prefix or mapping falls back to its rows' runtime (tdx
or snp; native rows need a mapping).

Only the paper presets' rows feed the paper's numbers. Rows of any other campaign
(the release's general presets such as c4-tdx.json or c4-tdx-value-width.json,
local runs, or a preset name on a target the item does not run on) are flagged
not_paper_preset and never preferred: a number uses them only when no paper
preset row qualifies at all. The JSON report lists those campaigns.

Rows are selected by their spec only, never by stage name: candidate name, key
and value bytes, capacity, API and caller batch size, arrival (saturated or
fixed at a saturation fraction), batch formation and stage kind (Figure 8 reads
the value_width stages only; Table 1 never does). When several rows qualify for
one number (several campaigns or boots), the reducer prefers rows that meet the
paper's methodology and, among those, takes the fastest (the paper quotes the
fastest boot); a response cell takes the fixed row whose saturation source was
fastest. Every number lists the trial ids it used. Rows that fail the paper's
methodology are used only when nothing else qualifies, and are flagged: fewer
than N completed requests in the window (SONIC's presets hold 0.25-1.1 N: a note
from 0.25 N), an unstable queue, any publication blocker of the reducer
(cycle_coverage_unknown is expected for the baselines, whose backends expose no
rebuild counter, and is not flagged there), and any departure from the presets'
settings: fewer than N settle requests (SONIC's presets settle 2^21: a note
from 2^21), workload.distribution other than counter, a read/hit/occupancy mix
other than 950000/1000000/1000000 ppm, instrumentation.verification other than
off, or resources.spin_before_park_ns other than 1 s.

`--campaign NAME=DIR` (or `--campaign DIR`, which reads DIR/plan.json for the
name) names a campaign's raw directory, from which the reducer reads SONIC's
worker/sonic_phases.json (position-map share, data-tree-only throughput) and
H2O2RAM's worker/markers.csv (top-level rebuild spans). SONIC's phases come from
the row of the batch throughput cell or, failing that, from the fastest row of
the same candidate and batch size that has the file (the K4/V8 cell's row may
be the baseline-sonic-throughput sweep's 2^27 row, so pass that campaign's
directory too).

Outputs in DIR: table1.md and table1.csv (every Table 1 cell), fig7.csv and
fig8.csv (with fig7.pdf/png and fig8.pdf/png when matplotlib is installed),
claims.md and claims.csv (every derived number of the text), and rows.csv
(every row read, its flags and the numbers it fed). The paper's values are
embedded below as data. Standard library only; matplotlib is optional.
"""
import argparse
import csv
import json
import math
import statistics
import sys
from decimal import ROUND_HALF_UP, Decimal
from pathlib import Path

# ---------------------------------------------------------------------------
# Targets, systems and Table 1 columns

TARGETS = {
    "c4-tdx": {"machine": "intel", "tee": True, "runtime": "tdx", "label": "Intel TDX"},
    "c4-native": {"machine": "intel", "tee": False, "runtime": "native", "label": "Intel, no TEE"},
    "oci-zen5-snp": {"machine": "amd", "tee": True, "runtime": "snp", "label": "AMD SEV-SNP"},
    "oci-e6-native": {"machine": "amd", "tee": False, "runtime": "native", "label": "AMD, no TEE"},
}
TEE_TARGET = {"intel": "c4-tdx", "amd": "oci-zen5-snp"}
NATIVE_TARGET = {"intel": "c4-native", "amd": "oci-e6-native"}

# The paper preset family: item -> the targets it runs on. A mirror of ITEMS in
# benchmarks/campaigns/paper/make_presets.py (tests/analysis/test_paper_numbers.py checks they agree).
_PROTECTED = ("c4-tdx", "oci-zen5-snp")
PAPER_ITEMS = {
    "throughput-k4v8": _PROTECTED,
    "table1-scalar": _PROTECTED,
    "table1-batch": _PROTECTED,
    "width": _PROTECTED,
    "width-hierarchy-wide": _PROTECTED,
    "width-std-unordered-map": _PROTECTED,
    "tee": tuple(TARGETS),
    "baseline-h2o2ram-table": _PROTECTED,
    "baseline-h2o2ram-throughput": _PROTECTED,
    "baseline-h2o2ram-shipped-throughput": _PROTECTED,
    "baseline-h2o2ram-width": _PROTECTED,
    "baseline-h2o2ram-width-large": ("oci-zen5-snp",),
    "baseline-sonic-table-scalar": _PROTECTED,
    "baseline-sonic-table-batch": _PROTECTED,
    "baseline-sonic-throughput": _PROTECTED,
    "baseline-sonic-width": _PROTECTED,
}
# The settings every paper preset row runs with (make_presets.py: counter keys, verification off, a 1 s spin
# before any library thread parks, the schema's default read/hit/occupancy mix, at least N settle requests and
# 2^21 for SONIC).
PAPER_WORKLOAD = {"distribution": "counter", "read_ppm": 950_000, "hit_ppm": 1_000_000, "occupancy_ppm": 1_000_000}
PAPER_VERIFICATION = "off"
PAPER_SPIN_BEFORE_PARK_NS = 10**9
SONIC_SETTLE = 1 << 21
SONIC_MIN_COVERAGE = 0.25  # SONIC's table windows hold 0.25 N (2^27), 0.5 N (2^25, sweeps) and 1.1 N (2^21)


def is_paper_preset(target, item):
    return target is not None and target in PAPER_ITEMS.get(item, ())
MACHINES = ("intel", "amd")
MACHINE_LABEL = {"intel": "Intel TDX", "amd": "AMD SEV-SNP"}

SONIC = "sonic_zingoram_recursive"
UMAP = "std_unordered_map"
BASELINE_SCHEMES = {UMAP: "umap", "h2o2ram": "h2o2ram", "h2o2ram_shipped": "h2o2ram_shipped",
                    "sonic_zingoram": "sonic", SONIC: "sonic"}
SYSTEM_LABEL = {"ours": "Ours", "h2o2ram": "H2O2", "sonic": "SONIC", "umap": "Non-oblivious",
                "hybrid": "Ours, hybrid ORAM", "hierarchy": "Ours, hierarchical ORAM",
                "h2o2ram_shipped": "H2O2RAM shipped"}


class Column:
    def __init__(self, key, label, key_bytes, value_bytes, capacity):
        self.key, self.label = key, label
        self.key_bytes, self.value_bytes, self.capacity = key_bytes, value_bytes, capacity


COLUMNS = [Column("k4v8", "4 B / 8 B, 2^27", 4, 8, 1 << 27),
           Column("k8v48", "8 B / 48 B, 2^25", 8, 48, 1 << 25),
           Column("k32v1024", "32 B / 1 KiB, 2^21", 32, 1024, 1 << 21)]
COLUMN = {c.key: c for c in COLUMNS}


def cell_candidates(system, column, setting):
    """Candidate names (in preference order) for a Table 1 cell, or None when the system has no such row."""
    if system == "ours":
        if column == "k32v1024":  # MICRORAM's hybrid ORAM: auto selects it at 1 KiB
            return ("auto", "tree")
        return ("auto",) if setting == "single" else ("parallel-8x8",)
    if system == "h2o2ram":
        return ("h2o2ram",) if setting == "single" else None
    return ((SONIC,) if system == "sonic" else (UMAP,))


def cell_key_bytes(system, column):
    """SONIC serves dense keys: its 1 KiB column is the 8-byte-key dense shape."""
    if system == "sonic" and column == "k32v1024":
        return (8, 32)
    return (COLUMN[column].key_bytes,)


def cell_batch_sizes(system, setting):
    """Caller batch sizes in preference order: every batch row is a batch of 64, SONIC's included."""
    return (1,) if setting == "single" else (64,)


# Paper cells whose measured row was not what the presets run (noted on the cell).
PAPER_CELL_NOTES = {
    ("throughput", "batch", "sonic", "k4v8"): "the paper's value was a batch-8 row (Intel 47,721, AMD 48,360 req/s); "
                                              "the presets run batch 64 (within 2% of batch 8 at 2^18-2^24)",
}


# ---------------------------------------------------------------------------
# The paper's values (Table 1 cells as printed; order: per column, Intel then AMD)

_T1 = {
    ("throughput", "single"): {
        "ours": "1.17 M|845 K|568 K|616 K|269 K|293 K",
        "h2o2ram": "82 K|87 K|57 K|59 K|4.0 K|4.7 K",
        "sonic": "23 K|20 K|35 K|27 K|32 K|28 K",
        "umap": "1.44 M|715 K|1.49 M|1.34 M|1.17 M|1.05 M"},
    ("throughput", "batch"): {
        "ours": "3.37 M|5.53 M|1.45 M|2.13 M|334 K|364 K",
        "sonic": "48 K|48 K|60 K|64 K|47 K|52 K",
        "umap": "5.08 M|2.40 M|5.46 M|4.71 M|1.98 M|1.81 M"},
    ("response", "single"): {
        "ours": "0.88 µs|1.3 µs|1.3 µs|2.5 µs|1.8 µs|2.4 µs|1.7 µs|3.0 µs|3.6 µs|6.1 µs|3.3 µs|6.2 µs",
        "h2o2ram": "4.0 s|90 s|2.2 s|61 s|1.5 s|32 s|1.3 s|28 s|0.73 s|20 s|0.76 s|20 s",
        "sonic": "97 µs|604 µs|84 µs|573 µs|85 µs|535 µs|78 µs|526 µs|130 µs|758 µs|110 µs|711 µs",
        "umap": "0.82 µs|1.3 µs|1.5 µs|3.5 µs|0.98 µs|1.3 µs|1.1 µs|2.4 µs|0.80 µs|1.4 µs|1.1 µs|2.9 µs"},
    ("response", "batch"): {
        "ours": "16 µs|20 µs|11 µs|16 µs|34 µs|45 µs|33 µs|46 µs|202 µs|218 µs|171 µs|185 µs",
        "sonic": "1.3 ms|2.7 ms|1.3 ms|2.6 ms|1.1 ms|2.5 ms|1.0 ms|2.2 ms|1.6 ms|3.8 ms|1.4 ms|3.3 ms",
        "umap": "12 µs|14 µs|28 µs|34 µs|11 µs|12 µs|14 µs|18 µs|23 µs|26 µs|30 µs|37 µs"},
    # One value per column, measured on the Intel rows (the AMD rows are reported beside them).
    ("memory", "single"): {
        "ours": "9.8 GiB|9.1 GiB|4.4 GiB",
        "h2o2ram": "22.1 GiB|19.7 GiB|36.2 GiB",
        "sonic": "27.7 GiB|14.9 GiB|8.8 GiB",
        "umap": "7.1 GiB|2.8 GiB|2.2 GiB"},
}


def paper_table1():
    """{(section, setting, system, column, machine, metric): paper text, or None for a cell the paper does not
    print (AMD memory)}."""
    out = {}
    for (section, setting), systems in _T1.items():
        for system, joined in systems.items():
            values = joined.split("|")
            for ci, column in enumerate(COLUMNS):
                if section == "memory":  # the paper prints the Intel rows' value; AMD's is reported, not graded
                    out[(section, setting, system, column.key, "intel", "peak_rss")] = values[ci]
                    out[(section, setting, system, column.key, "amd", "peak_rss")] = None
                    continue
                for mi, machine in enumerate(MACHINES):
                    if section == "throughput":
                        out[(section, setting, system, column.key, machine, "ops")] = values[2 * ci + mi]
                    else:
                        base = 4 * ci + 2 * mi
                        out[(section, setting, system, column.key, machine, "mean")] = values[base]
                        out[(section, setting, system, column.key, machine, "p99")] = values[base + 1]
    return out


PAPER_TABLE1 = paper_table1()


def _series(start, values):
    return {start + i: v for i, v in enumerate(values) if v is not None}


# Figure 7 (K4/V8 throughput by N): the values the figure was drawn from. Ours matches the
# figure's embedded path data. SONIC's batch curves are batch 8 on AMD (d) at every N and on Intel (b)
# at 2^27 (47,721, the Table 1 cell); the other Intel points are batch 64 (PAPER_FIG7_BATCH8). The presets
# run batch 64 throughout: with SONIC's Par8 threads (recursive map, C = 2,048, counter keys, saturated),
# batch 64 ran within 2% of batch 8 at 2^18, 2^21 and 2^24 on a 32-core Ice Lake host (interleaved runs).
PAPER_FIG7 = {
    ("intel", "single", "ours"): _series(16, [4177791, 3783637, 3678776, 3352546, 3318871, 2705831, 2214642,
                                              1902912, 1642798, 1484097, 1332410, 1165738, 1056817, 965831, 840452]),
    ("intel", "batch64", "ours"): _series(16, [4805305, 4640982, 4535249, 4287083, 4460451, 4259953, 4149790,
                                               3932985, 3975806, 3891940, 3533493, 3374988, 3328364, 3112513,
                                               2993297]),
    ("intel", "single", "umap"): _series(16, [9908351, 8008449, 7249892, 6741507, 6258107, 4010170, 2823225,
                                              1727399, 1591206, 1518216, 1483494, 1441661, 1376826, 1186842,
                                              1018627]),
    ("intel", "batch64", "umap"): _series(16, [20371588, 18433170, 17497932, 16363279, 15487828, 12499806,
                                               9551463, 6031765, 5770563, 5323644, 5152781, 5075162, 5010380,
                                               4900942, 4131709]),
    ("intel", "single", "h2o2ram"): _series(16, [279837, 257616, 233501, 209105, 174464, 150806, 134668, 119487,
                                                 109651, 99011, 87541, 81511]),
    ("intel", "single", "sonic"): _series(16, [110018, 94336, 76509, 59562, 58112, 50577, 43086, 36141, 33562,
                                               29559, 25645, 22741]),
    ("intel", "batch64", "sonic"): _series(16, [127607, 115135, 98849, 80525, 86367, 78617, 70072, 59606, 61994,
                                                56557, 51967, 47721]),
    ("amd", "single", "ours"): _series(16, [4060118, 3817226, 3601267, 3278364, 2838405, 2200905, 1607714,
                                            1704476, 1415783, 1137176, 959835, 844715, 748986, 672773, 554974]),
    ("amd", "batch64", "ours"): _series(16, [9221006, 8746696, 8449175, 8237647, 7976604, 7954533, 6692624,
                                             7140929, 6631635, 6200627, 5723991, 5531267, 5125248, 4869045,
                                             4430612]),
    ("amd", "single", "umap"): _series(16, [14193322, 13391029, 12584145, 9300213, 2886630, 2310178, 2234057,
                                            1655834, 1352836, 1154297, 995617, 714514, 576875, 518567, 488528]),
    ("amd", "batch64", "umap"): _series(16, [24416719, 23707171, 22952229, 19546710, 8657763, 6625794, 6416368,
                                             5181723, 4605432, 4041842, 3264830, 2399532, 1883599, 1701304,
                                             1593642]),
    ("amd", "single", "h2o2ram"): _series(16, [297050, 286094, 269745, 243259, 201740, 179151, 156506, 139301,
                                               124805, 111080, 98475, 87203]),
    ("amd", "single", "sonic"): _series(16, [102580, 87776, 71889, 57757, 56079, 46912, 40067, 33110, 29791,
                                             25858, 23607, 19963]),
    ("amd", "batch64", "sonic"): _series(16, [157229, 139691, 115642, 90863, 105306, 94732, 81918, 65983, 70744,
                                              65933, 57578, 48360]),
}
# Figure 7 reference points that were batch-8 rows (the presets run batch 64): (machine, panel, system, log2 N).
PAPER_FIG7_BATCH8 = {("intel", "batch64", "sonic", 27)} | {("amd", "batch64", "sonic", n)
                                                           for n in PAPER_FIG7[("amd", "batch64", "sonic")]}

FIG8_WIDTHS = (8, 16, 32, 48, 64, 96, 128, 192, 256, 512, 1024, 2048, 4096)


def _widths(widths, values):
    return {w: v for w, v in zip(widths, values) if v is not None}


# Figure 8 (K8, N = 2^20, single requests): throughput, and memory over N x (8 + V) for ours
# (library reserved bytes; the same on both machines).
PAPER_FIG8 = {
    ("intel", "hierarchy"): _widths(FIG8_WIDTHS, [2188649, 1821105, 1303960, 989955, 799500, 578393, 432307,
                                                  279573, 203711, 93476, 47862, 21433, 7275]),
    ("intel", "hybrid"): _widths(FIG8_WIDTHS, [1008658, 988164, 732603, 638885, 634859, 602299, 570209, 559188,
                                               540251, 447779, 341193, 229949, 146151]),
    ("amd", "hierarchy"): _widths(FIG8_WIDTHS, [2260027, 1960234, 1552900, 1221483, 992610, 723154, 581606,
                                                417175, 327127, 172488, 82710, 39495, 19479]),
    ("amd", "hybrid"): _widths(FIG8_WIDTHS, [1038410, 1025616, 946668, 901865, 875803, 853110, 852292, 773246,
                                             759187, 555794, 370644, 247558, 160714]),
    ("intel", "h2o2ram"): _widths((8, 16, 32, 64, 128, 256, 512),
                                  [212535, 156943, 131654, 99892, 35962, 19560, 10217]),
    ("amd", "h2o2ram"): _widths((8, 16, 32, 64, 128, 256, 512, 1024),
                                [179081, 123875, 106755, 85599, 38203, 18562, 9813, 5218]),
    ("intel", "sonic"): _widths((8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096),
                                [58773, 57312, 56310, 54004, 51271, 47892, 41409, 30880, 21306, 13047]),
    ("amd", "sonic"): _widths((8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096),
                              [53513, 53069, 52151, 51742, 49137, 43627, 39692, 27195, 19167, 12249]),
    ("intel", "umap"): _widths((8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096),
                               [6272228, 6277210, 5971881, 5492937, 3486003, 1986936, 1592325, 1287760, 1041943,
                                692741]),
    ("amd", "umap"): _widths((8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096),
                             [3177946, 3081302, 2642873, 2250955, 1972211, 1842838, 1602741, 1277107, 904270,
                              529518]),
}
PAPER_FIG8_MEMORY = {
    "hierarchy": _widths(FIG8_WIDTHS, [5.91, 5.55, 5.31, 5.2, 5.1, 5.0, 5.0, 5.0, 5.0, 4.9, 4.89, 4.88, 4.87]),
    "hybrid": _widths(FIG8_WIDTHS, [8.39, 5.59, 4.20, 3.6, 3.2, 2.8, 2.6, 2.4, 2.3, 2.2, 2.09, 2.04, 2.02]),
}
FIG8_CANDIDATES = {"hierarchy": ("hierarchy-frozen",), "hybrid": ("tree",), "h2o2ram": ("h2o2ram",),
                   "sonic": (SONIC,), "umap": (UMAP,)}

# Statements the campaigns cannot reproduce; the guide gives their commands.
OUTSIDE_CAMPAIGNS = [
    ("Rebuilds 30-54x (Intel) and 60-139x (AMD) faster than H2O2RAM's; 48.2 / 18.0 ms against about 2.5 s "
     "at 2^20 (Sections 1.1, 2)", "table-rebuild micro-benchmark against h2o2ram_routing_bench"),
    ("Routing on eight cores 3.2x faster than one pass per stage (Section 2.4)", "concurrent routing benchmark"),
    ("VP2INTERSECT: 16 instructions per bucket pair, about 1.7x faster merges (Section 2.4)",
     "merge micro-benchmark with and without VP2INTERSECT"),
    ("Constant-time test bounds: 0.0030 (TDX) and 0.012 (SEV-SNP) cycles per instruction (Section 2)",
     "constant-time test driver"),
    ("Memory latency about 205 ns under SEV-SNP, 150-180 ns under TDX, 128 ns without SNP (Sections 4.1, 4.2)",
     "cpu_host_topology_probe --tests core (core_dram_ns_median)"),
    ("Write throughput 4.7 M (Intel) and 10.1 M (AMD) writes/s (Section 4.2)",
     "cpu_byteslice_level_arena_benchmark --write-only; pass --write-throughput for the 4.0x / 12x ratios"),
    ("Thread split: 1 request + 11 rebuild threads, 8 + 7 for batches (Section 4.2)",
     "the campaign's resolution.json (hierarchy.owner_threads, top_helpers, rebuild_threads_used)"),
    ("A lookup probes about six (6.3 / 6.0) hash tables, 7.8 / 7.1 with batches; tables of the four smallest "
     "levels at most 8 MiB (Section 4.2, Appendix B)", "probe-count runs of the level-arena benchmark"),
    ("Allocated memory within 1% of the model; Table 2 (Appendix B)",
     "allocation_reconcile.py and the deamortization model"),
    ("SONIC's own OMAP serves 145 requests/s at 2^20 with batches of 64 (Section 4.1)",
     "SONIC's pmchain demo"),
    ("Eviction 8.1 / 4.3 µs against EnigMap's 442 / 274 µs (Section 4.3)",
     "cpu_tree_eviction_comparator_benchmark_enigmap"),
    ("Stash tails, Figure 9 and the failure probabilities of Appendix A", "stash-tail simulation and Lean"),
]

# ---------------------------------------------------------------------------
# Rounding and the paper's number formats


def _decimal(value):
    return Decimal(repr(float(value)))


def round_sig(value, digits):
    """Round half up to `digits` significant digits; returns a Decimal (99.96 -> 100, not 100.0)."""
    if value == 0:
        return Decimal(0)
    d = _decimal(value)
    rounded = d.quantize(Decimal(1).scaleb(d.adjusted() - digits + 1), rounding=ROUND_HALF_UP)
    if rounded.adjusted() != d.adjusted():  # a carry into a new digit
        rounded = rounded.quantize(Decimal(1).scaleb(rounded.adjusted() - digits + 1), rounding=ROUND_HALF_UP)
    return rounded


def round_places(value, places):
    """Round half up to `places` decimals; returns a Decimal."""
    return _decimal(value).quantize(Decimal(1).scaleb(-places), rounding=ROUND_HALF_UP)


def _plain(d):
    text = format(d, "f")
    return text


def format_rate(ops):
    """Table 1 throughput: three significant digits from 100 K, two below (1.17 M, 845 K, 82 K, 4.0 K)."""
    if ops is None:
        return None
    digits = 3 if ops >= 99_950 else 2
    rounded = round_sig(ops, digits)
    if rounded >= 1_000_000:
        return _plain(round_sig(ops / 1e6, 3)) + " M"
    if rounded >= 1_000:
        return _plain(round_sig(ops / 1e3, digits)) + " K"
    return _plain(round_places(ops, 0))


TIME_UNITS = {"ns": 1, "µs": 1e3, "ms": 1e6, "s": 1e9}


def format_time(ns, unit):
    """Table 1 response: two significant digits in the paper cell's unit, integers from 100."""
    if ns is None:
        return None
    value = ns / TIME_UNITS[unit]
    rounded = round_places(value, 0) if value >= 99.5 else round_sig(value, 2)
    return f"{_plain(rounded)} {unit}"


def format_gib(nbytes):
    return None if nbytes is None else f"{_plain(round_places(nbytes / 2**30, 1))} GiB"


def parse_paper(text):
    """'1.17 M' -> 1.17e6 ops/s; '0.88 µs' -> 880 ns; '10.0 GiB' -> bytes."""
    number, unit = text.split()
    value = float(number)
    if unit in ("M", "K"):
        return value * (1e6 if unit == "M" else 1e3)
    if unit == "GiB":
        return value * 2**30
    return value * TIME_UNITS[unit]


def format_like_paper(metric, value, paper_text):
    if value is None:
        return None
    if metric == "ops":
        return format_rate(value)
    if metric == "peak_rss":
        return format_gib(value)
    return format_time(value, paper_text.split()[1])


def decimals(number_text):
    return len(number_text.split(".")[1]) if "." in number_text else 0


def grouped(value):
    return f"{value:,.0f}"


def raw_text(metric, value):
    """Unrounded value for the CSV/markdown detail columns."""
    if value is None:
        return ""
    if metric == "ops":
        return f"{grouped(value)} req/s"
    if metric == "peak_rss":
        return f"{value / 2**30:.3f} GiB"
    if value >= 1e9:
        return f"{value / 1e9:.3f} s"
    if value >= 1e6:
        return f"{value / 1e6:.3f} ms"
    return f"{value / 1e3:.3f} µs"


# ---------------------------------------------------------------------------
# Rows


class Row:
    """One repetition of a reduced summary, with the spec fields the reducer selects on."""

    def __init__(self, **fields):
        self.__dict__.update(fields)
        self.used_for = []

    @property
    def short(self):
        return f"{self.campaign}/{self.trial_id[:21]}"

    @property
    def key(self):
        return (self.summary_index, self.environment_class, self.trial_id)

    @property
    def memory(self):
        """The paper's memory: peak RSS less the resident event buffer (None when either is unknown)."""
        if not self.peak_rss or self.event_buffer is None:
            return None
        return self.peak_rss - self.event_buffer


def system_of(candidate, scheme):
    if scheme in BASELINE_SCHEMES:
        return BASELINE_SCHEMES[scheme]
    if candidate in BASELINE_SCHEMES:
        return BASELINE_SCHEMES[candidate]
    return "ours"


def target_of_name(name):
    best = None
    for target in TARGETS:
        if name == target or name.startswith(target + "-"):
            if best is None or len(target) > len(best):
                best = target
    return best


def load_summary(path):
    path = Path(path)
    if path.is_dir():
        path = path / "summary.json"
    with open(path) as stream:
        document = json.load(stream)
    if not isinstance(document.get("groups"), list) or not isinstance(document.get("campaign"), dict):
        raise SystemExit(f"{path}: not a reduced campaign summary (run `oram_bench reduce`)")
    return path, document


REHEARSAL_PREFIX = "rehearsal-"  # benchmarks/campaigns/paper/make_presets.py --rehearsal names its copies so


def parse_mapping(value):
    """A --target value: (target, item or None). TARGET, or TARGET-ITEM naming a paper preset."""
    if value in TARGETS:
        return value, None
    target = target_of_name(value)
    item = value[len(target) + 1:] if target else None
    if target and is_paper_preset(target, item):
        return target, item
    return None, None


def target_and_item(campaign, target_map):
    """(target, item) of a campaign name: an explicit mapping first, then the name's target prefix."""
    stem = campaign[len(REHEARSAL_PREFIX):] if campaign.startswith(REHEARSAL_PREFIX) else campaign
    if campaign in target_map:
        target, item = parse_mapping(target_map[campaign])
        if item is not None:  # NAME=TARGET-ITEM: a renamed copy of that preset
            return target, item
    else:
        target = target_of_name(stem)
    item = stem[len(target) + 1:] if target and stem.startswith(target + "-") else stem
    return target, item


class SkippedRepetition(Exception):
    pass


def _required(mapping, key, what):
    value = mapping.get(key) if isinstance(mapping, dict) else None
    if value is None:
        raise SkippedRepetition(f"no {what}")
    return value


def rows_of(index, path, document, target_map, skipped=None):
    """The rows of one summary. A repetition without the fields the reducer selects on (spec, summary, shape,
    capacity, API, arrival, trial id) is skipped and recorded in `skipped` instead of stopping the run."""
    campaign = (document.get("campaign") or {}).get("name") or Path(path).parent.name
    target, item = target_and_item(campaign, target_map)
    paper = is_paper_preset(target, item)
    rows = []
    for group in document["groups"]:
        if not isinstance(group, dict):
            continue
        for rep in group.get("repetitions") or []:
            try:
                row = _row(index, path, document, campaign, target, item, paper, group, rep)
            except SkippedRepetition as reason:
                if skipped is not None:
                    trial = rep.get("trial_id") if isinstance(rep, dict) else None
                    skipped.append({"summary": str(path), "campaign": campaign, "trial_id": trial,
                                    "reason": str(reason)})
                continue
            rows.append(row)
    for row in rows:
        row.flags, row.notes = methodology(row)
    return rows


EVENT_RECORD_BYTES, EVENT_SLACK_RECORDS = 64, 1024


def resident_event_buffer(spec, rep):
    """Bytes of the benchmark's own event buffer resident in the row's peak RSS, which the paper's memory
    leaves out; None when the spec does not say. The worker allocates and pre-faults it before the fill
    (benchmarks/support/worker.hpp), sized as oram_bench.resolution.event_buffer_bytes sizes it: a saturated
    row holds instrumentation.buffer_bytes (256 MiB in the paper presets, 1 GiB with service timing), a
    histogram-checkpoint fixed-rate row none, and a full-event fixed-rate row a buffer sized by its rate."""
    instrumentation = spec.get("instrumentation")
    if not isinstance(instrumentation, dict):
        return None
    if spec.get("arrival") == "saturated":
        return instrumentation.get("buffer_bytes")
    if instrumentation.get("logging") != "full_events":
        return 0
    rate, timing = rep.get("offered_ops_per_second"), spec.get("timing") or {}
    if rate is None or "measurement_ns" not in timing or "max_accesses" not in timing:
        return None
    requests = min(math.ceil(rate * timing["measurement_ns"] / 1e9) + 16, timing["max_accesses"] + 1)
    batch = spec.get("caller_batch_size") or 1
    fixed_count = (spec.get("batch_policy") or {}).get("formation") != "max_count_or_timeout"
    calls = requests if batch == 1 or not fixed_count else math.ceil(requests / batch) + 1
    return (2 * requests + calls + EVENT_SLACK_RECORDS) * EVENT_RECORD_BYTES


def _row(index, path, document, campaign, target, item, paper, group, rep):
    if not isinstance(rep, dict):
        raise SkippedRepetition("repetition is not an object")
    trial_id = _required(rep, "trial_id", "trial_id")
    spec = _required(rep, "spec", "spec")
    summary = _required(rep, "summary", "summary")
    shape = _required(spec, "shape", "spec.shape")
    key_bytes, value_bytes = _required(shape, "key_bytes", "shape.key_bytes"), _required(shape, "value_bytes",
                                                                                          "shape.value_bytes")
    capacity = _required(spec, "requested_capacity", "spec.requested_capacity")
    api, arrival = _required(spec, "api_mode", "spec.api_mode"), _required(spec, "arrival", "spec.arrival")
    rate = spec.get("rate") or {}
    response = summary.get("response") or {}
    memory = rep.get("memory") or {}
    runtime = rep.get("runtime") or group.get("runtime") or (spec.get("execution") or {}).get("runtime")
    row_target = target
    if row_target is None:  # no name prefix and no mapping: the runtime decides for TEE rows
        row_target = {"tdx": "c4-tdx", "snp": "oci-zen5-snp"}.get(runtime)
    candidate = spec.get("candidate")
    scheme = (spec.get("overrides") or {}).get("scheme")
    workload = spec.get("workload")
    timing = spec.get("timing")
    instrumentation = spec.get("instrumentation")
    resources = spec.get("resources")
    return Row(
        summary_index=index, summary_path=str(path), campaign=campaign, plan_id=document.get("plan_id"),
        target=row_target, item=item, paper_preset=paper, environment_class=rep.get("environment_class"),
        trial_id=trial_id, executed_trial_id=rep.get("executed_trial_id") or trial_id,
        attempt_id=rep.get("attempt_id"), candidate=candidate, scheme=scheme,
        system=system_of(candidate, scheme), stage=spec.get("stage"), kind=spec.get("kind"),
        key_bytes=key_bytes, value_bytes=value_bytes,
        key_layout=shape.get("key_layout") or rep.get("key_layout"),
        capacity=capacity, api=api, batch=spec.get("caller_batch_size") or 1,
        formation=(spec.get("batch_policy") or {}).get("formation"),
        arrival=arrival, rate_kind=rate.get("kind"), fraction_ppm=rate.get("fraction_ppm"),
        source_trial_ids=list(rate.get("source_trial_ids") or []),
        offered=rep.get("offered_ops_per_second"),
        drained=summary.get("drained_ops_per_second"), completed=summary.get("completed"),
        mean_ns=response.get("mean_ns"), p50_ns=response.get("p50_ns"), p99_ns=response.get("p99_ns"),
        p999_ns=response.get("p999_ns"), max_ns=response.get("maximum_ns"),
        peak_rss=memory.get("trial_peak_rss_bytes"), event_buffer=resident_event_buffer(spec, rep),
        reserved=rep.get("library_reserved_bytes"),
        modeled=rep.get("library_modeled_bytes"), logical=rep.get("logical_bytes"),
        live=rep.get("live_entries"), blockers=list(rep.get("publication_blockers") or []),
        stability=rep.get("queue_stability"), coverage=rep.get("cycle_coverage"),
        runtime=runtime, protected_verified=rep.get("protected_verified"),
        diagnostic=bool(spec.get("diagnostic")),
        # The method settings (None: the summary does not carry the block, so nothing is checked).
        settle=timing.get("settle_requests") if isinstance(timing, dict) else None,
        workload={k: workload.get(k) for k in PAPER_WORKLOAD} if isinstance(workload, dict) else None,
        verification=instrumentation.get("verification") if isinstance(instrumentation, dict) else None,
        spin=resources.get("spin_before_park_ns") if isinstance(resources, dict) else None,
        has_resources=isinstance(resources, dict))


def methodology(row):
    """(flags, notes): flags fail the paper's methodology; notes are expected labels."""
    flags, notes = [], []
    if not row.paper_preset:
        flags.append("not_paper_preset")
    if row.target is None:
        flags.append("no_target")
    elif TARGETS[row.target]["runtime"] != row.runtime:
        flags.append(f"runtime_{row.runtime}_on_{row.target}")
    if row.completed is not None and row.capacity and row.completed < row.capacity:
        label = f"completed_below_N({row.completed / row.capacity:.2f}N)"
        if row.system == "sonic" and row.completed >= SONIC_MIN_COVERAGE * row.capacity:
            notes.append(label)  # SONIC's preset windows hold 0.25-1.1 N
        else:
            flags.append(label)
    if row.settle is not None and row.capacity and row.settle < row.capacity:
        label = f"settle_below_N({row.settle})"
        if row.system == "sonic" and row.settle >= SONIC_SETTLE:
            notes.append(label)  # SONIC's presets settle 2^21 at every N
        else:
            flags.append(label)
    if row.workload is not None:
        for field, expected in PAPER_WORKLOAD.items():
            if row.workload.get(field) != expected:
                flags.append(f"{'key_' if field == 'distribution' else ''}{field}_{row.workload.get(field)}")
    if row.verification is not None and row.verification != PAPER_VERIFICATION:
        flags.append(f"verification_{row.verification}")
    if row.has_resources and row.spin != PAPER_SPIN_BEFORE_PARK_NS:
        flags.append(f"spin_before_park_ns_{'unset' if row.spin is None else row.spin}")
    for blocker in row.blockers:
        if blocker == "cycle_coverage_unknown" and row.system != "ours":
            notes.append(blocker)  # baselines expose no rebuild counter
        elif blocker not in flags:
            flags.append(blocker)
    if row.stability in ("overloaded", "backlog_growth") and "queue_" + row.stability not in flags:
        flags.append("queue_" + row.stability)
    if row.diagnostic and "diagnostic_stage" not in flags:
        flags.append("diagnostic_stage")
    return flags, notes


# ---------------------------------------------------------------------------
# Selection


class Pick:
    """A selected row (or a missing one) with the alternatives it was chosen from."""

    def __init__(self, row=None, value=None, alternatives=(), missing=None, note=None):
        self.row, self.value, self.alternatives, self.missing, self.note = row, value, list(alternatives), missing, note

    @property
    def flags(self):
        return list(self.row.flags) if self.row else []


ABSOLUTE_RATE_TOLERANCE = 0.02


class Index:
    def __init__(self, rows, rehearsal=False):
        self.rows = rows
        self.by_key = {row.key: row for row in rows}
        # Rehearsal: scaled local campaigns; a number ignores the paper's capacity and uses the
        # largest capacity among the rows that match everything else.
        self.rehearsal = rehearsal

    def find(self, *, target, candidates, key_bytes, value_bytes, capacity, api, batches=(1,),
             arrival="saturated", fraction_ppm=None, formation=None, items=None, exact=False,
             avoid_items=("tee",), value_width=False):
        """Matching rows, each with its preference tier (candidate order, then batch order).

        arrival None matches every arrival; a fixed arrival must be a saturation fraction. value_width True
        takes only value_width stages (Figure 8), False none of them (Table 1 and the rest), None both.
        Rows of campaigns that are not paper presets stand in only when no paper preset row matches.
        """
        out = []
        for row in self.rows:
            if row.target != target or row.candidate not in candidates or row.key_bytes not in key_bytes:
                continue
            if row.value_bytes != value_bytes or row.api != api:
                continue
            if value_width is not None and (row.kind == "value_width") != value_width:
                continue
            if row.capacity != capacity and (exact or not self.rehearsal):
                continue
            if row.batch not in batches or (arrival is not None and row.arrival != arrival):
                continue
            if arrival == "fixed" and (row.rate_kind != "saturation_fraction" or row.fraction_ppm != fraction_ppm):
                continue
            if formation is not None and row.formation != formation:
                continue
            if items is not None and row.item not in items:
                continue
            out.append(((candidates.index(row.candidate), batches.index(row.batch)), row))
        if any(r.paper_preset for _, r in out):
            out = [(t, r) for t, r in out if r.paper_preset]
        # The TEE-overhead pair is its own experiment: its rows stand in elsewhere only when nothing else matches.
        if avoid_items and any(r.item not in avoid_items for _, r in out):
            out = [(t, r) for t, r in out if r.item not in avoid_items]
        if self.rehearsal and not exact and out:
            largest = max(r.capacity for _, r in out)
            out = [(t, r) for t, r in out if r.capacity == largest]
        return out

    def source_rate(self, row):
        rates = [self.by_key[(row.summary_index, row.environment_class, t)].drained
                 for t in row.source_trial_ids if (row.summary_index, row.environment_class, t) in self.by_key]
        rates = [r for r in rates if r is not None]
        return max(rates) if rates else None

    @staticmethod
    def _best_tier(matches):
        tier = min(t for t, _ in matches)
        return [r for t, r in matches if t == tier], tier

    def throughput(self, matches, what, preferred_batch=64):
        rated = [(t, r) for t, r in matches if r.drained is not None]
        if not rated:
            unrated = ", ".join(r.short for _, r in matches)
            return Pick(missing=what + (f" (no drained rate: {unrated})" if unrated else ""))
        rows, tier = self._best_tier(rated)
        rows = sorted(rows, key=lambda r: (bool(r.flags), -r.drained, r.campaign, r.trial_id))
        chosen = rows[0]
        note = None
        if tier[1] > 0:  # a fallback batch size (none of the paper's numbers has one)
            note = f"{chosen.short}: batch {chosen.batch} row, no batch-{preferred_batch} row"
        return Pick(chosen, chosen.drained, [r for _, r in matches if r is not chosen], note=note)

    @staticmethod
    def same_tier(pick):
        """The pick's row and its alternatives of the same candidate and batch size, unflagged and fastest
        first."""
        if pick.row is None:
            return []
        rows = [pick.row] + [r for r in pick.alternatives if r.candidate == pick.row.candidate and
                             r.batch == pick.row.batch]
        return [pick.row] + sorted(rows[1:], key=lambda r: (bool(r.flags), -(r.drained or 0), r.campaign,
                                                             r.trial_id))

    def response(self, matches, what):
        if not matches:
            return Pick(missing=what)
        rows, _ = self._best_tier(matches)
        rows = sorted(rows, key=lambda r: (bool(r.flags), r.mean_ns is None, -(self.source_rate(r) or 0),
                                           r.campaign, r.trial_id))
        chosen = rows[0]
        return Pick(chosen, None, [r for _, r in matches if r is not chosen])

    def fixed_response(self, common, fraction_ppm, formation, what):
        """The fixed row at a saturation fraction; failing that, a fixed row at an absolute rate within
        ABSOLUTE_RATE_TOLERANCE of that fraction of the fastest matching saturated row (labelled)."""
        matches = self.find(**common, arrival="fixed", fraction_ppm=fraction_ppm, formation=formation)
        if matches:
            return self.response(matches, what)
        source = self.throughput(self.find(**common), "")
        if source.row is not None and source.value:
            wanted = source.value * fraction_ppm / 1e6
            near = [(t, r) for t, r in self.find(**common, arrival=None)
                    if r.arrival == "fixed" and r.rate_kind == "absolute" and r.offered and
                    (formation is None or r.formation == formation) and
                    abs(r.offered / wanted - 1) <= ABSOLUTE_RATE_TOLERANCE]
            if near:
                pick = self.response(near, what)
                pick.note = (f"{pick.row.short}: absolute rate {grouped(pick.row.offered)} req/s, "
                             f"{pick.row.offered / source.value:.3f} of {source.row.short}")
                return pick
        return Pick(missing=what)

    def memory(self, matches, what):
        """The row with the highest peak RSS, less the event buffer it holds (Row.memory)."""
        matches = [(t, r) for t, r in matches if r.memory]
        if not matches:
            return Pick(missing=what + " (with peak RSS and a known event buffer)")
        rows, _ = self._best_tier(matches)
        rows.sort(key=lambda r: (bool(r.flags), -r.peak_rss, r.campaign, r.trial_id))
        chosen = rows[0]
        note = None
        if chosen.event_buffer:
            note = (f"{chosen.short}: peak RSS {chosen.peak_rss / 2**30:.3f} GiB less its "
                    f"{chosen.event_buffer / 2**20:.0f} MiB event buffer")
        return Pick(chosen, chosen.memory, [r for r in rows if r is not chosen], note=note)


def describe(target, system, column, setting, extra=""):
    col = COLUMN[column]
    return (f"{SYSTEM_LABEL.get(system, system)} {setting} row, {col.label}, {target}" + extra)


# ---------------------------------------------------------------------------
# Table 1


class Cell:
    def __init__(self, key, paper, pick, metric, value):
        self.key, self.paper, self.pick, self.metric, self.value = key, paper, pick, metric, value
        self.text = format_like_paper(metric, value, paper) if value is not None else None

    @property
    def status(self):
        if self.value is None:
            return "missing input"
        if self.paper is None:  # a cell the paper does not print (AMD memory)
            return "reported"
        return "match" if self.text == self.paper else "differs"

    @property
    def relative(self):
        if self.value is None or self.paper is None:
            return None
        return self.value / parse_paper(self.paper) - 1


def table1(index):
    cells = {}
    for (section, setting, system, column, machine, metric), paper in PAPER_TABLE1.items():
        target = TEE_TARGET[machine]
        col = COLUMN[column]
        # Memory: the single-request rows, except SONIC's batch rows (the paper's designated rows), any arrival.
        row_setting = ("batch" if system == "sonic" else "single") if section == "memory" else setting
        common = dict(target=target, candidates=cell_candidates(system, column, row_setting),
                      key_bytes=cell_key_bytes(system, column), value_bytes=col.value_bytes,
                      capacity=col.capacity, api="scalar" if row_setting == "single" else "batch",
                      batches=cell_batch_sizes(system, row_setting))
        key = (section, setting, system, column, machine, metric)
        if section == "throughput":
            pick = index.throughput(index.find(**common), describe(target, system, column, setting,
                                                                   ", saturated"))
            value = pick.value
        elif section == "response":
            extra = ", fixed at 0.5 of its saturation" + (", whole batches arriving" if setting == "batch" else "")
            pick = index.fixed_response(common, 500_000, "arrive_together" if setting == "batch" else None,
                                        describe(target, system, column, setting, extra))
            value = None if pick.row is None else (pick.row.mean_ns if metric == "mean" else pick.row.p99_ns)
            if pick.row is not None and value is None:
                pick = Pick(missing=f"response statistics of {pick.row.short}")
        else:
            pick = index.memory(_all_arrivals(index, common),
                                describe(target, system, column, row_setting, ", any arrival"))
            value = pick.value
        extra_note = PAPER_CELL_NOTES.get((section, setting, system, column))
        if extra_note and pick.row is not None:
            pick.note = "; ".join(n for n in (pick.note, extra_note) if n)
        cells[key] = Cell(key, paper, pick, metric, value)
        if pick.row is not None:
            pick.row.used_for.append("table1:" + ":".join(key))
    return cells


def _all_arrivals(index, common):
    """The designated rows of a memory cell: saturated and fixed alike."""
    return index.find(**common, arrival=None)


# ---------------------------------------------------------------------------
# Figures 7 and 8 data

FIG7_SERIES = [("single", "ours", ("auto",), (1,)), ("batch64", "ours", ("parallel-8x8",), (64,)),
               ("single", "h2o2ram", ("h2o2ram",), (1,)),
               ("single", "sonic", (SONIC,), (1,)), ("batch64", "sonic", (SONIC,), (64,)),
               ("single", "umap", (UMAP,), (1,)), ("batch64", "umap", (UMAP,), (64,))]


def fig7(index):
    points = []
    for machine in MACHINES:
        target = TEE_TARGET[machine]
        for panel, system, candidates, batches in FIG7_SERIES:
            capacities = {r.capacity for r in index.rows if r.target == target and r.candidate in candidates
                          and r.key_bytes == 4 and r.value_bytes == 8 and r.arrival == "saturated"
                          and r.kind != "value_width"
                          and r.api == ("scalar" if panel == "single" else "batch") and r.batch in batches
                          and r.capacity > 0 and r.capacity & (r.capacity - 1) == 0}
            reference = PAPER_FIG7.get((machine, panel, system), {})
            for log2 in sorted({c.bit_length() - 1 for c in capacities} | set(reference)):
                capacity = 1 << log2
                matches = index.find(target=target, candidates=candidates, key_bytes=(4,), value_bytes=8,
                                     capacity=capacity, api="scalar" if panel == "single" else "batch",
                                     batches=batches, exact=True)
                pick = index.throughput(matches, "")
                if pick.row is not None:
                    pick.row.used_for.append(f"fig7:{machine}:{panel}:{system}:2^{log2}")
                note = ("the paper's point is a batch-8 row (batch 64 within 2% of it)" if log2 in reference and
                        (machine, panel, system, log2) in PAPER_FIG7_BATCH8 else "")
                points.append({"machine": machine, "target": target, "panel": panel, "system": system,
                               "capacity": capacity, "log2": log2, "pick": pick,
                               "paper": reference.get(log2), "note": note})
    return points


def fig8(index):
    points = []
    for machine in MACHINES:
        target = TEE_TARGET[machine]
        for system, candidates in FIG8_CANDIDATES.items():
            # Figure 8's rows are the value_width stages (in a rehearsal, their scaled capacity).
            widths = {r.value_bytes for r in index.rows if r.target == target and r.candidate in candidates
                      and r.kind == "value_width" and r.key_bytes == 8
                      and (r.capacity == 1 << 20 or index.rehearsal) and r.api == "scalar"
                      and r.arrival == "saturated"}
            reference = PAPER_FIG8.get((machine, system), {})
            for width in sorted(widths | set(reference)):
                matches = index.find(target=target, candidates=candidates, key_bytes=(8,), value_bytes=width,
                                     capacity=1 << 20, api="scalar", value_width=True)
                pick = index.throughput(matches, "")
                row = pick.row
                memory, metric = None, None
                if row is not None:
                    row.used_for.append(f"fig8:{machine}:{system}:{width}")
                    if system in ("hierarchy", "hybrid"):
                        metric = "library_reserved"
                        if row.reserved and row.logical:
                            memory = row.reserved / row.logical
                    else:
                        metric = "peak_rss_less_event_buffer"
                        if row.memory and row.logical:
                            memory = row.memory / row.logical
                points.append({"machine": machine, "target": target, "system": system, "width": width,
                               "pick": pick, "paper": reference.get(width), "memory": memory,
                               "memory_metric": metric,
                               "paper_memory": PAPER_FIG8_MEMORY.get(system, {}).get(width)})
    return points


# ---------------------------------------------------------------------------
# Raw worker files


class Raw:
    def __init__(self, campaign_dirs):
        self.dirs = campaign_dirs  # {name or None: [Path]}

    def worker_dir(self, row):
        if not row.attempt_id:
            return None
        for directory in self.dirs.get(row.campaign, []) + self.dirs.get(None, []):
            attempts = Path(directory) / "trials" / row.executed_trial_id / "attempts"
            for candidate in sorted(attempts.glob(f"*-{row.attempt_id}")):
                if (candidate / "worker").is_dir():
                    return candidate / "worker"
        return None

    def sonic_phases(self, row):
        worker = self.worker_dir(row)
        path = worker / "sonic_phases.json" if worker else None
        if path is None or not path.exists():
            return None
        with open(path) as stream:
            phases = json.load(stream)
        part = phases.get("after_fill") or {}
        accesses, map_ns, data_ns = part.get("accesses"), part.get("map_ns"), part.get("data_ns")
        if not accesses or not data_ns:
            return None
        return {"accesses": accesses, "map_ns": map_ns, "data_ns": data_ns,
                "map_share": map_ns / (map_ns + data_ns) if map_ns is not None else None,
                "data_tree_ops_per_second": accesses * 1e9 / data_ns}

    def rebuild_spans(self, row):
        """H2O2RAM's rebuild spans (seconds) by level from worker/markers.csv, or None."""
        worker = self.worker_dir(row)
        path = worker / "markers.csv" if worker else None
        if path is None or not path.exists():
            return None
        levels = {}
        with open(path, newline="") as stream:
            for record in csv.DictReader(stream):
                if record.get("role") != "h2o2ram_rebuild":
                    continue
                try:
                    level, start, end = int(record["level"]), int(record["start_ns"]), int(record["end_ns"])
                except (KeyError, TypeError, ValueError):
                    continue
                levels.setdefault(level, []).append((end - start) / 1e9)
        return levels or None


def parse_campaign_dirs(values):
    dirs = {}
    for value in values or []:
        name, sep, directory = value.partition("=")
        if not sep:
            directory, name = value, None
            plan = Path(directory) / "plan.json"
            if plan.exists():
                with open(plan) as stream:
                    name = json.load(stream).get("campaign", {}).get("name")
        dirs.setdefault(name, []).append(Path(directory))
    return dirs


# ---------------------------------------------------------------------------
# Claims


class Q:
    """A reproduced quantity: its value, the rows behind it, what is missing, and flags of its own (beside its
    rows' flags) when it departs from the paper's method."""

    def __init__(self, value=None, rows=(), missing=(), text="", notes=(), flags=()):
        self.value, self.rows, self.missing = value, list(rows), list(missing)
        self.text, self.notes, self.flags = text, list(notes), list(flags)

    @property
    def ok(self):
        return self.value is not None and not self.missing

    @staticmethod
    def combine(value, parts, text, notes=()):
        rows, missing, all_notes, flags = [], [], list(notes), []
        for part in parts:
            rows += [r for r in part.rows if r not in rows]
            missing += [m for m in part.missing if m not in missing]
            all_notes += [n for n in part.notes if n not in all_notes]
            flags += [f for f in part.flags if f not in flags]
        if missing:
            value = None
        return Q(value, rows, missing, text, all_notes, flags)


def q_cell(cells, section, setting, system, column, machine, metric):
    cell = cells[(section, setting, system, column, machine, metric)]
    if cell.value is None:
        return Q(missing=[cell.pick.missing or "row"])
    notes = [cell.pick.note] if cell.pick.note else []
    return Q(cell.value, [cell.pick.row], text=raw_text(metric, cell.value), notes=notes)


def q_ratio(a, b):
    value = a.value / b.value if a.ok and b.ok and b.value else None
    return Q.combine(value, [a, b], f"{a.text or '?'} / {b.text or '?'}")


def q_percent(a, b):
    value = 100 * a.value / b.value if a.ok and b.ok and b.value else None
    return Q.combine(value, [a, b], f"100 x {a.text or '?'} / {b.text or '?'}")


def q_drop(a, b):
    """100 x (1 - a / b): how much lower a is than b."""
    value = 100 * (1 - a.value / b.value) if a.ok and b.ok and b.value else None
    return Q.combine(value, [a, b], f"100 x (1 - {a.text or '?'} / {b.text or '?'})")


def q_given(value, what):
    if value is None:
        return Q(missing=[what])
    return Q(value, text=f"{grouped(value)} (given)")


class Claim:
    """One derived number of the text: paper values (as printed) against reproduced quantities.

    The status is 'matches' when every reproduced value, rounded to the paper's decimals, equals the paper's;
    'within N%' for an 'about' statement; 'holds' / 'does not hold' for an inequality (check); 'reported'
    when the paper gives no number; 'missing input' when a row is absent.
    """

    def __init__(self, cid, where, statement, paper, quantities, *, unit="x", scale=1.0, check=None,
                 tolerance=None, fmt=None):
        self.cid, self.where, self.statement = cid, where, statement
        self.paper, self.quantities, self.unit, self.scale = paper, quantities, unit, scale
        self.check, self.tolerance, self.fmt = check, tolerance, fmt

    def reproduced_text(self):
        parts = []
        for i, q in enumerate(self.quantities):
            if not q.ok:
                parts.append("missing input")
                continue
            value = q.value / self.scale
            if self.fmt is not None:
                parts.append(self.fmt(q.value))
            elif i < len(self.paper):
                parts.append(_plain(round_places(value, decimals(self.paper[i]))))
            else:
                parts.append(f"{value:.3g}")
        return parts

    @property
    def status(self):
        if not all(q.ok for q in self.quantities):
            return "missing input"
        if self.check is not None:
            return "holds" if self.check([q.value for q in self.quantities]) else "does not hold"
        if not self.paper:
            return "reported"
        if self.tolerance is not None:
            close = all(abs(q.value / self.scale / float(p) - 1) <= self.tolerance
                        for q, p in zip(self.quantities, self.paper))
            return f"within {self.tolerance:.0%}" if close else "differs"
        texts = self.reproduced_text()
        return "matches" if all(t == p for t, p in zip(texts, self.paper)) else "differs"

    @property
    def rows(self):
        out = []
        for q in self.quantities:
            out += [r for r in q.rows if r not in out]
        return out

    @property
    def missing(self):
        out = []
        for q in self.quantities:
            out += [m for m in q.missing if m not in out]
        return out

    @property
    def notes(self):
        out = []
        for q in self.quantities:
            out += [n for n in q.notes if n not in out]
        return out

    @property
    def flags(self):
        out = []
        for q in self.quantities:
            out += [f for f in q.flags if f not in out]
        for row in self.rows:
            out += [f for f in row.flags if f not in out]
        return out


def per_n_ratios(index, machine):
    """Ours / H2O2RAM single-request throughput per N in 2^16..2^27 (Figure 7)."""
    target = TEE_TARGET[machine]
    ratios, rows = {}, []
    for log2 in range(16, 28):
        n = 1 << log2
        ours = index.throughput(index.find(target=target, candidates=("auto",), key_bytes=(4,), value_bytes=8,
                                           capacity=n, api="scalar", exact=True), "")
        theirs = index.throughput(index.find(target=target, candidates=("h2o2ram",), key_bytes=(4,),
                                             value_bytes=8, capacity=n, api="scalar", exact=True), "")
        if ours.row and theirs.row and theirs.value:
            ratios[log2] = ours.value / theirs.value
            rows += [ours.row, theirs.row]
    return ratios, rows


TEE_PAIR_FLAG = "tee_pair_not_from_tee_campaigns"


def tee_pair(index, machine, setting):
    """The TEE and native quantities of one TEE-overhead number: each side's mean over its qualifying rows.

    Both sides use the same option (candidate and batch size) and, where possible, the 'tee' campaigns: the
    first option with rows on both sides wins, taken from the tee campaigns when both sides have them there,
    else from any campaign (the pair is then flagged). Nothing on both sides: missing input."""
    if setting == "single":
        options = [(("auto",), (1,), "scalar")]
    else:
        options = [(("parallel-8x8",), (64,), "batch")]
    targets = (TEE_TARGET[machine], NATIVE_TARGET[machine])

    def side_rows(target, candidates, batches, api, tee_only):
        common = dict(target=target, candidates=candidates, key_bytes=(4,), value_bytes=8, capacity=1 << 27,
                      api=api, batches=batches)
        rows = [r for _, r in index.find(**common, items=("tee",), avoid_items=()) if r.drained is not None]
        if not rows and not tee_only:  # the 'tee' campaign's rows first, else one other campaign's
            rows = [r for _, r in index.find(**common, avoid_items=()) if r.drained is not None]
            if rows:  # the campaign holding the best row (unflagged first, then fastest)
                best = min(rows, key=lambda r: (bool(r.flags), -r.drained, r.campaign, r.trial_id))
                rows = [r for r in rows if r.campaign == best.campaign]
        return [r for r in rows if not r.flags] or rows

    def side_q(rows, notes, flags):
        value = statistics.fmean(r.drained for r in rows)
        text = f"{grouped(value)} req/s" + (f" (mean of {len(rows)})" if len(rows) > 1 else "")
        return Q(value, rows, text=text, notes=notes, flags=flags)

    for candidates, batches, api in options:
        for tee_only in (True, False):
            sides = [side_rows(target, candidates, batches, api, tee_only) for target in targets]
            if not all(sides):
                continue
            notes, flags = [], []
            outside = [t for t, rows in zip(targets, sides) if any(r.item != "tee" for r in rows)]
            if outside:
                flags.append(TEE_PAIR_FLAG)
                notes.append(f"rows not from a '<target>-tee' campaign on {', '.join(outside)}")
            return [side_q(rows, notes, flags) for rows in sides]
    what = (f"{setting} rows at 4 B / 8 B, 2^27, saturated, with the same candidate and batch size on "
            f"{' and '.join(targets)} (" + "; ".join(f"{c[0]} batch {b[0]}" for c, b, _ in options) + ")")
    return [Q(missing=[what]), Q(missing=[what])]


def fig8_lookup(points, machine, system, width):
    for p in points:
        if p["machine"] == machine and p["system"] == system and p["width"] == width:
            return p
    return None


def fig8_q(points, machine, system, width, what="throughput"):
    p = fig8_lookup(points, machine, system, width)
    label = f"{SYSTEM_LABEL[system]} at {width} B, K8, 2^20, {TEE_TARGET[machine]}"
    if p is None or p["pick"].row is None:
        return Q(missing=[label])
    if what == "throughput":
        return Q(p["pick"].value, [p["pick"].row], text=f"{grouped(p['pick'].value)} req/s")
    if p["memory"] is None:
        return Q(missing=[label + " memory"])
    return Q(p["memory"], [p["pick"].row], text=f"{p['memory']:.3f} x data")


def crossover(points, machine, metric):
    """The smallest measured width from which the hybrid ORAM beats the hierarchy at every larger width."""
    widths = sorted({p["width"] for p in points if p["machine"] == machine and p["pick"].row is not None
                     and p["system"] in ("hierarchy", "hybrid")})
    pairs = []
    for w in widths:
        h, t = fig8_lookup(points, machine, "hierarchy", w), fig8_lookup(points, machine, "hybrid", w)
        if not (h and t and h["pick"].row and t["pick"].row):
            continue
        if metric == "throughput":
            pairs.append((w, t["pick"].value > h["pick"].value, [h["pick"].row, t["pick"].row]))
        elif h["memory"] is not None and t["memory"] is not None:
            pairs.append((w, t["memory"] < h["memory"], [h["pick"].row, t["pick"].row]))
    if not pairs:
        return Q(missing=[f"hierarchy-frozen and tree rows at K8, 2^20 on {TEE_TARGET[machine]}"])
    first = None
    for i, (w, better, _) in enumerate(pairs):
        if all(b for _, b, _ in pairs[i:]):
            first = i
            break
    rows = [r for _, _, rs in pairs for r in rs]
    measured = ", ".join(str(w) for w, _, _ in pairs)
    if first is None:
        return Q(None, rows, ["no width from which the hybrid ORAM stays ahead"], text=f"widths {measured}")
    below = pairs[first - 1][0] if first > 0 else None
    text = f"first width {pairs[first][0]} B" + (f" (behind at {below} B)" if below else " (smallest measured)")
    notes = [] if below else [f"the hybrid ORAM already leads at the smallest measured width ({measured} B)"]
    return Q(pairs[first][0], rows, text=text + f"; widths {measured}", notes=notes)


def compute_claims(index, cells, f7, f8, raw, writes):
    C = lambda *k: q_cell(cells, *k)  # noqa: E731
    T, B, R, M = "throughput", "batch", "response", "memory"
    claims = []

    def add(*args, **kwargs):
        claims.append(Claim(*args, **kwargs))

    ours_i, ours_a = C(T, "single", "ours", "k4v8", "intel", "ops"), C(T, "single", "ours", "k4v8", "amd", "ops")
    ob_i, ob_a = C(T, B, "ours", "k4v8", "intel", "ops"), C(T, B, "ours", "k4v8", "amd", "ops")
    um_i, um_a = C(T, "single", "umap", "k4v8", "intel", "ops"), C(T, "single", "umap", "k4v8", "amd", "ops")
    umb_i, umb_a = C(T, B, "umap", "k4v8", "intel", "ops"), C(T, B, "umap", "k4v8", "amd", "ops")
    h2_i, h2_a = C(T, "single", "h2o2ram", "k4v8", "intel", "ops"), C(T, "single", "h2o2ram", "k4v8", "amd", "ops")
    sb_i, sb_a = C(T, B, "sonic", "k4v8", "intel", "ops"), C(T, B, "sonic", "k4v8", "amd", "ops")

    # Abstract and introduction
    add("ours-vs-h2o2ram-k4v8", "Abstract; 1.1", "Ours / H2O2RAM single-request throughput, Intel, 4 B / 8 B, 2^27",
        ["14.3"], [q_ratio(ours_i, h2_i)])
    add("ours-vs-umap-k4v8", "Abstract", "Ours / std::unordered_map single-request throughput, Intel, 2^27",
        ["0.81"], [q_ratio(ours_i, um_i)])
    add("ours-vs-umap-k4v8-percent", "1.1; 4.2", "Ours reaches this percentage of the hash table's single-request "
        "throughput, Intel, 2^27", ["81"], [q_percent(ours_i, um_i)], unit="%")
    q08 = []
    for metric in ("mean_ns", "p99_ns"):
        pick = index.fixed_response(dict(target="c4-tdx", candidates=("auto",), key_bytes=(4,), value_bytes=8,
                                         capacity=1 << 27, api="scalar"), 800_000, None,
                                    "Ours single row, 4 B / 8 B, 2^27, c4-tdx, fixed at 0.8 of its saturation")
        if pick.row is None or getattr(pick.row, metric) is None:
            q08.append(Q(missing=[pick.missing or "response statistics"]))
        else:
            pick.row.used_for.append("claim:response-0.8")
            q08.append(Q(getattr(pick.row, metric), [pick.row], text=raw_text("mean", getattr(pick.row, metric))))
    add("response-at-0.8", "Abstract; 4.2", "Ours average and P99 response time (µs) when single requests arrive "
        "at 80% of its throughput, Intel, 4 B / 8 B, 2^27", ["1.6", "3.4"], q08, unit=" µs", scale=1e3)
    add("ours-vs-sonic-batch-k4v8", "Abstract; 1.1; 4.2", "Ours / SONIC batch throughput, Intel, 4 B / 8 B, 2^27",
        ["71"], [q_ratio(ob_i, sb_i)])
    h2m_i = C(R, "single", "h2o2ram", "k4v8", "intel", "mean")
    om_i = C(R, "single", "ours", "k4v8", "intel", "mean")
    add("response-vs-h2o2ram-million", "1.1", "H2O2RAM's / Ours' average response time at half of each system's "
        "own throughput, Intel, 4 B / 8 B, 2^27 (millions)", ["4.6"], [q_ratio(h2m_i, om_i)], scale=1e6,
        unit=" million x")
    umm_i = C(R, "single", "umap", "k4v8", "intel", "mean")
    add("response-vs-umap", "1.1", "Ours / std::unordered_map average response time at half of own throughput, "
        "Intel, 2^27 ('nearly as fast'; paper cells 0.88 / 0.82 µs)", [], [q_ratio(om_i, umm_i)])
    mem = {s: C(M, "single", s, c, "intel", "peak_rss") for s in ("ours", "h2o2ram", "sonic") for c in ("k4v8",)}
    add("memory-vs-h2o2ram-k4v8", "Abstract; 1.1; 4.2", "H2O2RAM / Ours peak memory, 4 B / 8 B, 2^27 (Intel rows)",
        ["2.3"], [q_ratio(mem["h2o2ram"], mem["ours"])])
    add("memory-vs-sonic-k4v8", "4.2", "SONIC / Ours peak memory, 4 B / 8 B, 2^27 (Intel rows)",
        ["2.8"], [q_ratio(mem["sonic"], mem["ours"])])
    ob32_i, ob32_a = C(T, B, "ours", "k32v1024", "intel", "ops"), C(T, B, "ours", "k32v1024", "amd", "ops")
    sb32_i, sb32_a = C(T, B, "sonic", "k32v1024", "intel", "ops"), C(T, B, "sonic", "k32v1024", "amd", "ops")
    add("ours-vs-sonic-batch-k32", "1.1; 4.3", "Ours / SONIC batch throughput, 2^21 records of 1 KiB values "
        "(Intel; AMD)", ["7.2", "7.0"], [q_ratio(ob32_i, sb32_i), q_ratio(ob32_a, sb32_a)])
    hy = {m: fig8_q(f8, m, "hybrid", 1024) for m in MACHINES}
    hi = {m: fig8_q(f8, m, "hierarchy", 1024) for m in MACHINES}
    add("hybrid-vs-hierarchy-1k", "Abstract; 1.1; 4.3", "Hybrid / hierarchical ORAM throughput at 1 KiB values, "
        "2^20 records (Intel; AMD)", ["7.1", "4.5"], [q_ratio(hy["intel"], hi["intel"]),
                                                       q_ratio(hy["amd"], hi["amd"])])
    hym = {m: fig8_q(f8, m, "hybrid", 1024, "memory") for m in MACHINES}
    him = {m: fig8_q(f8, m, "hierarchy", 1024, "memory") for m in MACHINES}
    add("hybrid-memory-1k", "Abstract; 1.1; 4.3", "Memory reduction of the hybrid ORAM at 1 KiB values, 2^20 records "
        "(library reserved bytes; Intel; AMD)", ["57", "57"], [q_drop(hym["intel"], him["intel"]),
                                                              q_drop(hym["amd"], him["amd"])], unit="%")

    # Section 4.2
    for machine, paper in (("intel", ["14.3", "19.0"]), ("amd", ["9.7", "14.1"])):
        ratios, rows = per_n_ratios(index, machine)
        if ratios:
            lo, hi_ = min(ratios.values()), max(ratios.values())
            detail = ", ".join(f"2^{n}: {r:.2f}" for n, r in sorted(ratios.items()))
            notes = [] if len(ratios) == 12 else [f"{len(ratios)} of the 12 sizes 2^16..2^27 measured"]
            qs = [Q(lo, rows, text=detail, notes=notes), Q(hi_, rows, text="")]
        else:
            what = f"Ours and H2O2RAM single rows at 4 B / 8 B, 2^16..2^27, {TEE_TARGET[machine]}"
            qs = [Q(missing=[what]), Q(missing=[what])]
        add(f"ours-vs-h2o2ram-by-n-{machine}", "4.2 (Figure 7)", f"Ours / H2O2RAM single-request throughput over "
            f"N = 2^16..2^27, minimum and maximum, {MACHINE_LABEL[machine]}", paper, qs)
    add("ours-vs-h2o2ram-k8v48", "4.2", "Ours / H2O2RAM single-request throughput, 8 B / 48 B, 2^25 (Intel; AMD)",
        ["10", "10"], [q_ratio(C(T, "single", "ours", "k8v48", m, "ops"), C(T, "single", "h2o2ram", "k8v48", m, "ops"))
                       for m in MACHINES])
    add("ours-vs-umap-amd", "4.2", "Ours / std::unordered_map single-request throughput, AMD, 2^27",
        ["1.18"], [q_ratio(ours_a, um_a)])
    add("intel-to-amd-umap", "4.2", "Drop of the hash table's single-request throughput from Intel to AMD, 2^27 "
        "('falls by half', graded as 'about')", ["50"], [q_drop(um_a, um_i)], unit="%", tolerance=0.10)
    add("intel-to-amd-ours", "4.2", "Drop of Ours' single-request throughput from Intel to AMD, 2^27",
        ["28"], [q_drop(ours_a, ours_i)], unit="%")
    add("batch-gain-ours", "4.2", "Ours batch / single-request throughput at 2^27 (Intel; AMD)", ["2.9", "6.5"],
        [q_ratio(ob_i, ours_i), q_ratio(ob_a, ours_a)])
    add("batch-faster-on-amd", "4.2", "With batching, Ours is faster on AMD: AMD / Intel batch throughput, 2^27",
        [], [q_ratio(ob_a, ob_i)], check=lambda v: v[0] > 1)
    add("ours-vs-sonic-batch-both", "4.2", "Ours / SONIC batch throughput, 4 B / 8 B, 2^27 (Intel; AMD)",
        ["71", "114"], [q_ratio(ob_i, sb_i), q_ratio(ob_a, sb_a)])
    claims.append(sonic_without_map(cells, raw, "ours-vs-sonic-data-tree-k4v8", "4.2",
                                    "Ours / SONIC batch throughput when SONIC's recursive position map is not "
                                    "counted, Intel, 4 B / 8 B, 2^27", ["14"], [("k4v8", "intel")]))
    add("umap-batch-gain", "4.2", "std::unordered_map batch / single-request throughput, 2^27 (Intel; AMD): "
        "'more than 3x'", [], [q_ratio(umb_i, um_i), q_ratio(umb_a, um_a)], check=lambda v: min(v) > 3)
    add("ours-vs-umap-batch-intel", "4.2", "Ours / std::unordered_map batch throughput, Intel, 2^27",
        ["67"], [q_percent(ob_i, umb_i)], unit="%")
    add("ours-vs-umap-batch-amd", "4.2", "Ours / std::unordered_map batch throughput, AMD, 2^27",
        ["2.3"], [q_ratio(ob_a, umb_a)])
    w = {m: q_given(writes.get(TEE_TARGET[m]), f"--write-throughput {TEE_TARGET[m]}=OPS") for m in MACHINES}
    add("write-throughput", "4.2", "All-write throughput at 2^27 (millions per second; Intel; AMD), from the "
        "arena benchmark", ["4.7", "10.1"], [w["intel"], w["amd"]], scale=1e6, unit=" M/s")
    add("write-vs-lookup", "4.2", "All-write / single-request lookup throughput at 2^27 (Intel; AMD)",
        ["4.0", "12"], [q_ratio(w["intel"], ours_i), q_ratio(w["amd"], ours_a)])
    claims.append(top_rebuild(index, raw))
    add("response-vs-h2o2ram-both", "4.2", "H2O2RAM's / Ours' average response time at half of own throughput, "
        "2^27 (Intel; AMD): 'more than a million times'", [],
        [q_ratio(h2m_i, om_i), q_ratio(C(R, "single", "h2o2ram", "k4v8", "amd", "mean"),
                                        C(R, "single", "ours", "k4v8", "amd", "mean"))],
        check=lambda v: min(v) > 1e6, fmt=lambda v: f"{v:.3g}")
    ours_mem = C(M, "single", "ours", "k4v8", "intel", "peak_rss")
    logical = Q(None, missing=["logical bytes of the Ours memory row"])
    cell = cells[(M, "single", "ours", "k4v8", "intel", "peak_rss")]
    if cell.pick.row is not None and cell.pick.row.logical:
        logical = Q(cell.pick.row.logical, [cell.pick.row], text=f"{cell.pick.row.logical / 2**30:.3f} GiB of data")
    add("memory-over-data-k4v8", "4.2", "Ours peak memory / keys and values, 4 B / 8 B, 2^27 (Intel)",
        ["6.5"], [q_ratio(ours_mem, logical)])
    for machine, paper in (("intel", ["10", "5"]), ("amd", ["39", "4"])):
        pairs = [tee_pair(index, machine, s) for s in ("single", "batch")]
        add(f"tee-overhead-{machine}", "4.2", f"Throughput loss under {MACHINE_LABEL[machine]} against the same VM "
            f"without TEE, 4 B / 8 B, 2^27 (single requests; batches)", paper,
            [q_drop(tee, native) for tee, native in pairs], unit="%")

    # Section 4.3
    for metric, cid, paper, statement in (
            ("throughput", "hybrid-crossover", ["96", "96"], "Smallest value size (bytes) from which the hybrid "
             "ORAM's throughput exceeds the hierarchical ORAM's, 2^20 records (Intel; AMD)"),
            ("memory", "hybrid-memory-crossover", ["32", "32"], "Smallest value size (bytes) from which the hybrid "
             "ORAM uses less memory (library reserved bytes), 2^20 records (Intel; AMD)")):
        add(cid, "4.3 (Figure 8)", statement, paper, [crossover(f8, m, metric) for m in MACHINES], unit=" B")
    add("ours-vs-h2o2ram-k32", "4.3", "Ours / H2O2RAM single-request throughput, 32 B / 1 KiB, 2^21 (Intel; AMD)",
        ["67", "62"], [q_ratio(C(T, "single", "ours", "k32v1024", m, "ops"),
                               C(T, "single", "h2o2ram", "k32v1024", m, "ops")) for m in MACHINES])
    m32 = {s: C(M, "single", s, "k32v1024", "intel", "peak_rss") for s in ("ours", "h2o2ram", "sonic")}
    add("memory-vs-h2o2ram-k32", "4.3", "H2O2RAM / Ours peak memory, 32 B / 1 KiB, 2^21 (Intel rows)",
        ["8.3"], [q_ratio(m32["h2o2ram"], m32["ours"])])
    add("ours-vs-sonic-single-k32", "4.3", "Ours / SONIC single-request throughput, 1 KiB values, 2^21 "
        "(Intel; AMD)", ["8.4", "10.5"], [q_ratio(C(T, "single", "ours", "k32v1024", m, "ops"),
                                                  C(T, "single", "sonic", "k32v1024", m, "ops")) for m in MACHINES])
    add("memory-vs-sonic-k32", "4.3", "SONIC / Ours peak memory, 1 KiB values, 2^21 (Intel rows)",
        ["2.0"], [q_ratio(m32["sonic"], m32["ours"])])
    claims.append(sonic_without_map(cells, raw, "ours-vs-sonic-data-tree-k32", "4.3",
                                    "Ours / SONIC batch throughput at 1 KiB values, 2^21, when SONIC's position map "
                                    "is not counted (Intel; AMD): 'about 4x'", ["4", "4"],
                                    [("k32v1024", "intel"), ("k32v1024", "amd")]))
    claims.append(shipped_vs_patched(index))
    return claims


def sonic_without_map(cells, raw, cid, where, statement, paper, keys):
    """Ours batch throughput over SONIC's data-tree-only throughput (worker/sonic_phases.json). The phases come
    from the row of SONIC's batch throughput cell or, when its raw files were not passed, from the fastest row
    of the same candidate and batch size that has them (noted)."""
    quantities = []
    for column, machine in keys:
        ours = q_cell(cells, "throughput", "batch", "ours", column, machine, "ops")
        cell = cells[("throughput", "batch", "sonic", column, machine, "ops")]
        if cell.pick.row is None:
            sonic = Q(missing=[cell.pick.missing])
        else:
            tier = Index.same_tier(cell.pick)
            found = next(((row, phases) for row in tier for phases in [raw.sonic_phases(row)] if phases), None)
            if found is None:
                campaigns = list(dict.fromkeys(r.campaign for r in tier))
                sonic = Q(None, [cell.pick.row], [
                    f"worker/sonic_phases.json of {cell.pick.row.short} or another {cell.pick.row.candidate} "
                    f"batch-{cell.pick.row.batch} row ("
                    + " or ".join(f"pass --campaign {c}=DIR" for c in campaigns) + ")"])
            else:
                row, phases = found
                share = phases["map_share"]
                notes = [f"{machine}: SONIC position-map share {share:.1%} of its access time"
                         if share is not None else ""]
                if row is not cell.pick.row:
                    notes.append(f"{machine}: SONIC phases from {row.short} ({grouped(row.drained or 0)} req/s); "
                                 f"the cell's row {cell.pick.row.short} has no worker/sonic_phases.json")
                sonic = Q(phases["data_tree_ops_per_second"], [row],
                          text=f"{grouped(phases['data_tree_ops_per_second'])} req/s data tree alone",
                          notes=[n for n in notes if n])
        quantities.append(q_ratio(ours, sonic))
    return Claim(cid, where, statement, paper, quantities)


def top_rebuild(index, raw):
    """H2O2RAM's top-level rebuild spans at K4/V8 2^27: the largest level rebuilt in any of the target's rows
    (half-rate and saturated); rows whose markers never reach that level are skipped."""
    quantities = []
    for machine in MACHINES:
        target = TEE_TARGET[machine]
        common = dict(target=target, candidates=("h2o2ram",), key_bytes=(4,), value_bytes=8, capacity=1 << 27,
                      api="scalar")
        fixed = index.response(index.find(**common, arrival="fixed", fraction_ppm=500_000), "")
        rows = [r for _, r in index.find(**common, arrival="fixed", fraction_ppm=500_000)] + \
               [r for _, r in index.find(**common)]
        markers = [(row, raw.rebuild_spans(row)) for row in rows]
        markers = [(row, levels) for row, levels in markers if levels]
        top = max((level for _, levels in markers for level in levels), default=None)
        used = [row for row, levels in markers if top in levels]
        spans = [s for _, levels in markers for s in levels.get(top, [])]
        skipped = [row.short for row, levels in markers if top not in levels]
        max_note = (f"{target}: maximum response of the half-rate row {fixed.row.max_ns / 1e9:.1f} s"
                    if fixed.row is not None and fixed.row.max_ns else None)
        if spans:
            value = statistics.fmean(spans)
            notes = [n for n in [max_note] if n]
            if skipped:
                notes.append(f"{target}: no level-{top} rebuild in the markers of {', '.join(skipped)}")
            quantities.append(Q(value, used, text=f"{len(spans)} top-level rebuild spans (level {top}, "
                                f"{len(used)} row{'s' if len(used) > 1 else ''}), mean {value:.1f} s, "
                                f"max {max(spans):.1f} s", notes=notes))
        elif fixed.row is not None and fixed.row.max_ns:
            quantities.append(Q(fixed.row.max_ns / 1e9, [fixed.row],
                                text=f"maximum response {fixed.row.max_ns / 1e9:.1f} s",
                                notes=[f"{target}: no markers read (pass --campaign); used the half-rate row's "
                                       f"maximum response"]))
        else:
            quantities.append(Q(missing=[f"H2O2RAM single row at 4 B / 8 B, 2^27 on {target} "
                                         f"(markers.csv or a half-rate row)"]))
    return Claim("h2o2ram-top-rebuild", "4.2", "H2O2RAM's rebuild of its largest level inside one access, "
                 "seconds (Intel; AMD): 'about'", ["117", "90"], quantities, unit=" s", tolerance=0.10)


def shipped_vs_patched(index):
    ratios, rows = [], []
    for machine in MACHINES:
        target = TEE_TARGET[machine]
        for row in index.rows:
            if row.target != target or row.candidate != "h2o2ram_shipped" or row.key_bytes != 4 or \
                    row.value_bytes != 8 or row.api != "scalar" or row.arrival != "saturated":
                continue
            shipped = index.throughput(index.find(target=target, candidates=("h2o2ram_shipped",), key_bytes=(4,),
                                                  value_bytes=8, capacity=row.capacity, api="scalar", exact=True),
                                       "")
            patched = index.throughput(index.find(target=target, candidates=("h2o2ram",), key_bytes=(4,),
                                                  value_bytes=8, capacity=row.capacity, api="scalar", exact=True),
                                       "")
            if shipped.row is row and patched.row is not None and patched.value:
                ratios.append((shipped.value / patched.value, machine, row.capacity))
                rows += [row, patched.row]
    if not ratios:
        q = Q(missing=["H2O2RAM shipped and patched single rows at 4 B / 8 B, same N and target"])
    else:
        best = max(ratios)
        per = "; ".join(f"{m} max {max(r for r, mm, _ in ratios if mm == m):.3f}" for m in MACHINES
                        if any(mm == m for _, mm, _ in ratios))
        q = Q(100 * (best[0] - 1), rows, text=f"max shipped / patched {best[0]:.3f} at 2^{best[2].bit_length() - 1} "
              f"({best[1]}); {per}")
    return Claim("h2o2ram-shipped-vs-patched", "4.1", "How much faster the released H2O2RAM build is than the "
                 "patched one at most, 8-byte values (percent over all N and both machines)", ["26"], [q], unit="%")


# ---------------------------------------------------------------------------
# Writers


def write_csv(path, header, rows):
    with open(path, "w", newline="") as stream:
        writer = csv.writer(stream)
        writer.writerow(header)
        writer.writerows(rows)


SECTION_ORDER = [("throughput", "single"), ("throughput", "batch"), ("response", "single"), ("response", "batch"),
                 ("memory", "single")]
SYSTEM_ORDER = ["ours", "h2o2ram", "sonic", "umap"]


REHEARSAL_BANNER = ("**Rehearsal:** the paper's capacities were ignored (each number uses the largest capacity "
                    "among otherwise matching rows). These values check the pipeline, not the paper.")


def write_table1(cells, output, rehearsal=False):
    header = ["section", "setting", "system", "column", "key_bytes", "value_bytes", "capacity", "machine",
              "target", "metric", "paper", "reproduced", "status", "relative_difference", "value", "unit",
              "row_capacity", "campaign", "trial_id", "attempt_id", "flags", "alternatives", "note"]
    lines = []
    for key in sorted(cells, key=_cell_order):
        cell = cells[key]
        section, setting, system, column, machine, metric = key
        col, row = COLUMN[column], cell.pick.row
        unit = {"ops": "ops/s", "peak_rss": "bytes"}.get(metric, "ns")
        lines.append([section, setting, system, column, col.key_bytes, col.value_bytes, col.capacity, machine,
                      TEE_TARGET[machine], metric, cell.paper or "", cell.text or "", cell.status,
                      "" if cell.relative is None else f"{cell.relative:+.4f}",
                      "" if cell.value is None else repr(float(cell.value)), unit,
                      row.capacity if row else "", row.campaign if row else "", row.trial_id if row else "",
                      row.attempt_id if row else "",
                      ";".join(cell.pick.flags), len(cell.pick.alternatives),
                      cell.pick.note or (cell.pick.missing if row is None else "")])
    write_csv(output / "table1.csv", header, lines)

    md = ["# Table 1, reproduced", "",
          "Each cell is `reproduced [paper]`, rounded as the paper rounds. `!` marks a row that fails the paper's "
          "methodology (see Flags); `-` marks a missing input. Memory is the highest peak RSS among a cell's rows "
          "(single-request rows; SONIC's batch rows), less the benchmark's event buffer that row holds (256 MiB, "
          "or 1 GiB with service timing, in saturated rows; none in half-rate rows). The paper prints memory for the Intel rows only; the AMD memory cells are reported, not graded. Trial ids "
          "and notes are in table1.csv.", ""]
    if rehearsal:
        md[1:1] = ["", REHEARSAL_BANNER]
    head = "| | " + " | ".join(f"{c.label} {MACHINE_LABEL[m].split()[0]}" for c in COLUMNS for m in MACHINES) + " |"
    rule = "|---|" + "---|" * (2 * len(COLUMNS))
    matched = sum(1 for c in cells.values() if c.status == "match")
    present = sum(1 for c in cells.values() if c.value is not None)
    graded = sum(1 for c in cells.values() if c.paper is not None)
    for section, setting in SECTION_ORDER:
        title = {"throughput": "Throughput", "response": "Response time (avg / P99)", "memory": "Memory"}[section]
        md += [f"## {title}" + ("" if section == "memory" else f", {setting}"), "", head, rule]
        for system in SYSTEM_ORDER:
            row_cells = []
            any_cell = False
            for column in COLUMNS:
                for machine in MACHINES:
                    metrics = {"throughput": ["ops"], "response": ["mean", "p99"], "memory": ["peak_rss"]}[section]
                    parts = []
                    for metric in metrics:
                        cell = cells.get((section, setting, system, column.key, machine, metric))
                        if cell is None:
                            continue
                        any_cell = True
                        mark = "!" if cell.pick.flags else ""
                        parts.append(f"{cell.text or '-'}{mark} [{cell.paper or 'not printed'}]")
                    row_cells.append(" / ".join(parts))
            if any_cell:
                md.append(f"| {SYSTEM_LABEL[system]} | " + " | ".join(row_cells) + " |")
        md.append("")
    md += [f"{present} of {len(cells)} cells reproduced; {matched} of the {graded} printed cells round to the "
           f"paper's value.", "", "## Flags", ""]
    flagged = [(k, c) for k, c in sorted(cells.items(), key=lambda kv: _cell_order(kv[0])) if c.pick.flags]
    if not flagged:
        md.append("No cell uses a flagged row.")
    for key, cell in flagged:
        md.append(f"- {' '.join(key)}: {', '.join(cell.pick.flags)} ({cell.pick.row.short})")
    noted = [(k, c) for k, c in sorted(cells.items(), key=lambda kv: _cell_order(kv[0])) if c.pick.note]
    md += ["", "## Notes", ""]
    md += [f"- {' '.join(k)}: {c.pick.note}" for k, c in noted] or ["None."]
    missing = [(k, c) for k, c in sorted(cells.items(), key=lambda kv: _cell_order(kv[0])) if c.value is None]
    md += ["", "## Missing inputs", ""]
    md += [f"- {' '.join(k)}: {c.pick.missing}" for k, c in missing] or ["None."]
    (output / "table1.md").write_text("\n".join(md) + "\n")
    return present, matched


def _cell_order(key):
    section, setting, system, column, machine, metric = key
    return (SECTION_ORDER.index((section, setting)), SYSTEM_ORDER.index(system),
            [c.key for c in COLUMNS].index(column), MACHINES.index(machine), metric)


def write_fig7(points, output):
    header = ["machine", "target", "panel", "system", "capacity", "log2_capacity", "ops_per_second", "paper",
              "ratio_to_paper", "candidate", "batch", "campaign", "trial_id", "flags", "note"]
    lines = []
    for p in points:
        row = p["pick"].row
        value = p["pick"].value
        lines.append([p["machine"], p["target"], p["panel"], p["system"], p["capacity"], p["log2"],
                      "" if value is None else round(value, 1), p["paper"] or "",
                      f"{value / p['paper']:.4f}" if value and p["paper"] else "",
                      row.candidate if row else "", row.batch if row else "", row.campaign if row else "",
                      row.trial_id if row else "", ";".join(row.flags) if row else "", p["note"]])
    write_csv(output / "fig7.csv", header, lines)


def write_fig8(points, output):
    header = ["machine", "target", "system", "value_bytes", "ops_per_second", "paper", "ratio_to_paper",
              "memory_over_data", "memory_metric", "paper_memory_over_data", "campaign", "trial_id", "flags"]
    lines = []
    for p in points:
        row = p["pick"].row
        value = p["pick"].value
        lines.append([p["machine"], p["target"], p["system"], p["width"], "" if value is None else round(value, 1),
                      p["paper"] or "", f"{value / p['paper']:.4f}" if value and p["paper"] else "",
                      "" if p["memory"] is None else f"{p['memory']:.4f}", p["memory_metric"] or "",
                      p["paper_memory"] or "", row.campaign if row else "", row.trial_id if row else "",
                      ";".join(row.flags) if row else ""])
    write_csv(output / "fig8.csv", header, lines)


def write_claims(claims, output, rehearsal=False):
    header = ["id", "where", "statement", "paper", "reproduced", "status", "formula", "notes", "missing",
              "flags", "rows"]
    lines = []
    md = ["# Derived numbers of the paper, reproduced", "",
          "Each entry gives the paper's value, the reproduced value rounded as the paper rounds it, and the rows "
          "used (campaign/trial id). 'missing input' lists what to run; flags mark rows that fail the paper's "
          "methodology (rows.csv has every row's flags) and TEE pairs not taken from the tee campaigns on both "
          "sides.", ""]
    counts = {}
    for claim in claims:
        status = claim.status
        counts[status] = counts.get(status, 0) + 1
        paper = "; ".join(p + claim.unit for p in claim.paper) if claim.paper else "-"
        reproduced = "; ".join(t if t == "missing input" else t + ("" if claim.fmt else claim.unit)
                               for t in claim.reproduced_text())
        formula = " | ".join(q.text for q in claim.quantities if q.text)
        rows = [r.short for r in claim.rows]
        full_rows = [f"{r.campaign}/{r.trial_id}" for r in claim.rows]
        lines.append([claim.cid, claim.where, claim.statement, paper, reproduced, status, formula,
                      " | ".join(claim.notes), " | ".join(claim.missing), ";".join(claim.flags),
                      ";".join(full_rows)])
        for row in claim.rows:
            row.used_for.append("claim:" + claim.cid)
        md += [f"## {claim.cid}", "", f"- {claim.statement} ({claim.where})", f"- paper: {paper}",
               "- reproduced: missing input" if status == "missing input" else
               f"- reproduced: {reproduced} ({status})"]
        if formula:
            md.append(f"- from: {formula}")
        if claim.missing:
            md.append("- missing: " + "; ".join(claim.missing))
        if claim.notes:
            md.append("- notes: " + "; ".join(claim.notes))
        if claim.flags:
            md.append("- flags: " + ", ".join(claim.flags))
        if rows:
            shown = rows if len(rows) <= 8 else rows[:6] + [f"... {len(rows)} rows in all (claims.csv)"]
            md.append("- rows: " + ", ".join(shown))
        md.append("")
    md += ["## Statements outside the campaigns", "",
           "These numbers come from micro-benchmarks, simulations or proofs, not from campaign summaries:", ""]
    md += [f"- {statement}: {source}" for statement, source in OUTSIDE_CAMPAIGNS]
    md.insert(4, "Status counts: " + ", ".join(f"{v} {k}" for k, v in sorted(counts.items())) + ".")
    md.insert(5, "")
    if rehearsal:
        md[4:4] = [REHEARSAL_BANNER, ""]
    write_csv(output / "claims.csv", header, lines)
    (output / "claims.md").write_text("\n".join(md) + "\n")
    return counts


def write_rows(rows, output):
    header = ["campaign", "target", "item", "paper_preset", "trial_id", "attempt_id", "environment_class", "stage",
              "kind", "candidate", "scheme", "system", "key_bytes", "value_bytes", "capacity", "api", "batch",
              "formation", "arrival", "fraction", "offered_ops_per_second", "drained_ops_per_second", "completed",
              "completed_over_n", "settle_requests", "key_distribution", "read_ppm", "hit_ppm", "occupancy_ppm",
              "verification", "spin_before_park_ns", "mean_us", "p50_us", "p99_us", "p999_us", "max_us",
              "trial_peak_rss_gib", "event_buffer_gib", "memory_gib", "library_reserved_gib", "logical_gib",
              "queue_stability", "cycle_coverage",
              "publication_blockers", "flags", "notes", "used_for"]
    us = lambda v: "" if v is None else f"{v / 1e3:.3f}"  # noqa: E731
    gib = lambda v: "" if not v else f"{v / 2**30:.4f}"  # noqa: E731
    blank = lambda v: "" if v is None else v  # noqa: E731
    lines = []
    for r in sorted(rows, key=lambda r: (r.campaign, r.trial_id, str(r.environment_class))):
        workload = r.workload or {}
        lines.append([r.campaign, r.target or "", r.item, "yes" if r.paper_preset else "no", r.trial_id,
                      r.attempt_id, r.environment_class, r.stage, blank(r.kind), r.candidate, r.scheme, r.system,
                      r.key_bytes, r.value_bytes, r.capacity, r.api, r.batch, r.formation, r.arrival,
                      "" if r.fraction_ppm is None else r.fraction_ppm / 1e6,
                      "" if r.offered is None else r.offered,
                      "" if r.drained is None else round(float(r.drained), 1),
                      r.completed, "" if not r.completed or not r.capacity else f"{r.completed / r.capacity:.3f}",
                      blank(r.settle), blank(workload.get("distribution")), blank(workload.get("read_ppm")),
                      blank(workload.get("hit_ppm")), blank(workload.get("occupancy_ppm")), blank(r.verification),
                      blank(r.spin), us(r.mean_ns), us(r.p50_ns), us(r.p99_ns), us(r.p999_ns), us(r.max_ns),
                      gib(r.peak_rss), "" if r.event_buffer is None else f"{r.event_buffer / 2**30:.4f}",
                      gib(r.memory), gib(r.reserved), gib(r.logical), r.stability, r.coverage,
                      ";".join(r.blockers), ";".join(r.flags), ";".join(r.notes), ";".join(sorted(set(r.used_for)))])
    write_csv(output / "rows.csv", header, lines)


# ---------------------------------------------------------------------------
# Figures (optional matplotlib)

# Categorical slots in a fixed order (validated for adjacent-pair CVD separation); each entity keeps its color.
COLORS = {"ours": "#2a78d6", "hierarchy": "#2a78d6", "h2o2ram": "#eb6834", "sonic": "#1baf7a",
          "umap": "#eda100", "hybrid": "#e87ba4"}
MARKERS = {"ours": "o", "hierarchy": "o", "hybrid": "D", "h2o2ram": "s", "sonic": "^", "umap": "v"}
LEGEND = {"ours": "Ours", "hierarchy": "Ours, hierarchical ORAM", "hybrid": "Ours, hybrid ORAM",
          "h2o2ram": "H2O2RAM", "sonic": "SONIC", "umap": "std::unordered_map (not oblivious)"}


def _matplotlib():
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        return plt
    except ImportError:
        return None


def _style(ax):
    for side in ("top", "right"):
        ax.spines[side].set_visible(False)
    for side in ("left", "bottom"):
        ax.spines[side].set_color("#8a8984")
    ax.tick_params(colors="#52514e", labelsize=7)
    ax.grid(alpha=0.25, linewidth=0.5)


def _legend(fig, systems):
    from matplotlib.lines import Line2D
    handles = [Line2D([], [], color=COLORS[s], marker=MARKERS[s], linewidth=2, markersize=6) for s in systems]
    labels = [LEGEND[s] for s in systems]
    handles.append(Line2D([], [], color="#52514e", marker="o", linestyle="", markerfacecolor="none", markersize=6))
    labels.append("hollow: the paper's value")
    fig.legend(handles, labels, loc="lower center", ncol=len(handles), fontsize=7, frameon=False,
               bbox_to_anchor=(0.5, -0.02))


def plot_fig7(points, output, plt):
    fig, axes = plt.subplots(1, 4, figsize=(12, 3.4), sharey=True)
    panels = [("intel", "single"), ("intel", "batch64"), ("amd", "single"), ("amd", "batch64")]
    systems = ["ours", "h2o2ram", "sonic", "umap"]
    for ax, (machine, panel) in zip(axes, panels):
        for system in systems:
            series = [p for p in points if p["machine"] == machine and p["panel"] == panel and p["system"] == system]
            measured = [(p["capacity"], p["pick"].value) for p in series if p["pick"].value]
            paper = [(p["capacity"], p["paper"]) for p in series if p["paper"]]
            if measured:
                ax.plot(*zip(*measured), color=COLORS[system], marker=MARKERS[system], linewidth=2, markersize=5)
            if paper:
                ax.plot(*zip(*paper), color=COLORS[system], marker=MARKERS[system], linestyle="", markersize=6,
                        markerfacecolor="none", alpha=0.7)
        ax.set_xscale("log", base=2)
        ax.set_yscale("log")
        ax.set_xlabel("Records N", fontsize=8, color="#52514e")
        ax.set_title(f"{MACHINE_LABEL[machine]}, {'one at a time' if panel == 'single' else 'batches of 64'}",
                     fontsize=8)
        _style(ax)
    axes[0].set_ylabel("Requests/s", fontsize=8, color="#52514e")
    _legend(fig, systems)
    fig.tight_layout(rect=(0, 0.08, 1, 1))
    for suffix in ("pdf", "png"):
        fig.savefig(output / f"fig7.{suffix}", dpi=150, facecolor="#fcfcfb")
    plt.close(fig)


def _width_axis(ax):
    ax.set_xscale("log", base=2)
    ax.set_xticks([8, 64, 512, 4096])
    ax.set_xticklabels(["8", "64", "512", "4096"])
    ax.set_xlabel("Value size (bytes)", fontsize=8, color="#52514e")


def plot_fig8(points, output, plt):
    fig, axes = plt.subplots(1, 3, figsize=(10.5, 3.4))
    systems = ["hierarchy", "hybrid", "h2o2ram", "sonic", "umap"]
    for ax, machine in zip(axes[:2], MACHINES):
        for system in systems:
            series = [p for p in points if p["machine"] == machine and p["system"] == system]
            measured = [(p["width"], p["pick"].value) for p in series if p["pick"].value]
            paper = [(p["width"], p["paper"]) for p in series if p["paper"]]
            if measured:
                ax.plot(*zip(*measured), color=COLORS[system], marker=MARKERS[system], linewidth=2, markersize=5)
            if paper:
                ax.plot(*zip(*paper), color=COLORS[system], marker=MARKERS[system], linestyle="", markersize=6,
                        markerfacecolor="none", alpha=0.7)
        _width_axis(ax)
        ax.set_yscale("log")
        ax.set_title(f"Throughput, {MACHINE_LABEL[machine]}", fontsize=8)
        _style(ax)
    axes[0].set_ylabel("Requests/s", fontsize=8, color="#52514e")
    machine = "intel" if any(p["memory"] for p in points if p["machine"] == "intel") else "amd"
    ax = axes[2]
    for system in systems:
        series = [p for p in points if p["machine"] == machine and p["system"] == system]
        measured = [(p["width"], p["memory"]) for p in series if p["memory"]]
        paper = [(p["width"], p["paper_memory"]) for p in series if p["paper_memory"]]
        if measured:
            ax.plot(*zip(*measured), color=COLORS[system], marker=MARKERS[system], linewidth=2, markersize=5)
        if paper:
            ax.plot(*zip(*paper), color=COLORS[system], marker=MARKERS[system], linestyle="", markersize=6,
                    markerfacecolor="none", alpha=0.7)
    _width_axis(ax)
    ax.set_ylim(bottom=0)
    ax.set_ylabel("Memory / data", fontsize=8, color="#52514e")
    ax.set_title(f"Memory ({MACHINE_LABEL[machine]}; ours: reserved, baselines: peak RSS)", fontsize=8)
    _style(ax)
    _legend(fig, systems)
    fig.tight_layout(rect=(0, 0.08, 1, 1))
    for suffix in ("pdf", "png"):
        fig.savefig(output / f"fig8.{suffix}", dpi=150, facecolor="#fcfcfb")
    plt.close(fig)


# ---------------------------------------------------------------------------


def parse_pairs(values, what, convert=str):
    out = {}
    for value in values or []:
        name, sep, rest = value.partition("=")
        if not sep or not name or not rest:
            raise SystemExit(f"{what} expects NAME=VALUE, got {value!r}")
        out[name] = convert(rest)
    return out


def reduce_paper(summary_paths, output, *, campaign_dirs=(), targets=None, writes=None, figures=True,
                 rehearsal=False):
    """Read the summaries, write every output file and return a small report."""
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    targets = dict(targets or {})
    for name, target in targets.items():
        if parse_mapping(target)[0] is None:
            raise SystemExit(f"--target {name}={target}: give a target ({', '.join(TARGETS)}) or a paper preset "
                             f"<target>-<item> (items: {', '.join(PAPER_ITEMS)})")
    writes = dict(writes or {})
    rows, seen, skipped = [], set(), []
    for index, path in enumerate(summary_paths):
        path, document = load_summary(path)
        for row in rows_of(index, path, document, targets, skipped):
            identity = (row.campaign, row.plan_id, row.environment_class, row.trial_id, row.attempt_id)
            if identity in seen:  # the same summary given twice
                continue
            seen.add(identity)
            rows.append(row)
    index = Index(rows, rehearsal=rehearsal)
    raw = Raw(parse_campaign_dirs(campaign_dirs))
    cells = table1(index)
    f7, f8 = fig7(index), fig8(index)
    claims = compute_claims(index, cells, f7, f8, raw, writes)
    present, matched = write_table1(cells, output, rehearsal)
    write_fig7(f7, output)
    write_fig8(f8, output)
    counts = write_claims(claims, output, rehearsal)
    write_rows(rows, output)
    plotted = False
    if figures:
        plt = _matplotlib()
        if plt is not None:
            plot_fig7(f7, output, plt)
            plot_fig8(f8, output, plt)
            plotted = True
    untargeted = sorted({r.campaign for r in rows if r.target is None})
    not_paper = sorted({r.campaign for r in rows if not r.paper_preset})
    used_not_paper = sorted({r.campaign for r in rows if not r.paper_preset and r.used_for})
    for entry in skipped:
        print(f"paper_numbers: skipped a repetition of {entry['campaign']} ({entry['trial_id']}): "
              f"{entry['reason']}", file=sys.stderr)
    return {"output": str(output), "rehearsal": rehearsal, "rows": len(rows), "table1_cells": len(cells),
            "table1_graded": sum(1 for c in cells.values() if c.paper is not None),
            "table1_reproduced": present,
            "table1_matching": matched, "claims": counts, "figures": plotted, "campaigns_without_target": untargeted,
            "campaigns_not_paper_presets": not_paper, "not_paper_preset_campaigns_used": used_not_paper,
            "skipped_repetitions": skipped}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0],
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("summaries", nargs="+", help="reduced summary.json files (or directories holding one)")
    parser.add_argument("--campaign", action="append", default=[], metavar="[NAME=]DIR",
                        help="a campaign's raw directory, for SONIC phases and H2O2RAM markers (repeatable)")
    parser.add_argument("--target", action="append", default=[], metavar="NAME=TARGET[-ITEM]",
                        help="assign campaign NAME to a target (" + ", ".join(TARGETS) + "), or declare it a "
                             "renamed copy of the paper preset TARGET-ITEM")
    parser.add_argument("--write-throughput", action="append", default=[], metavar="TARGET=OPS",
                        help="all-write throughput from the arena benchmark, for the write/lookup ratios")
    parser.add_argument("--no-figures", action="store_true", help="skip the matplotlib figures")
    parser.add_argument("--rehearsal", action="store_true",
                        help="scaled local campaigns: ignore the paper's capacities and use, for each number, "
                             "the largest capacity among otherwise matching rows (pipeline check only)")
    parser.add_argument("--output", required=True)
    args = parser.parse_args(argv)
    report = reduce_paper(args.summaries, args.output, campaign_dirs=args.campaign,
                          targets=parse_pairs(args.target, "--target"),
                          writes=parse_pairs(args.write_throughput, "--write-throughput", float),
                          figures=not args.no_figures, rehearsal=args.rehearsal)
    json.dump(report, sys.stdout, indent=2)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
