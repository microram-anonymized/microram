"""Reconcile measured allocations with the main-table model (level_arena_model.py).

Input: audit rows, one JSON object per line, from
  cpu_oram_allocation_audit [--sites]      ("AUDIT_ROW {...}": ours)
  oram_baseline_*_audit --allocation-audit 1   ("ALLOC_AUDIT {...}": baselines)
and optionally a resolver envelope (`cpu_oram_benchmark --resolve-only`) for a
row whose own plan is missing.  Output: every quantity as (row, quantity,
value, unit, basis, note), as CSV or Markdown.

Quantities, per row:
  * heap: library live/peak bytes, requested and granted, and VmHWM, each
    over requested_capacity*(key+value) and over actual_capacity*(key+value).
    VmHWM is process-wide RSS (runtime and harness included); it is never
    added to heap bytes.  The audit resets it before each row; a row whose
    `hwm` is null (the reset was refused) reports none.  Harness allocations
    are reported apart.
  * ours, split by role: main payload, residual tiers, retained tier holes,
    online stash, rebuild stashes, scratch, position map, tree,
    masks/tags/metadata, the library's own huge-page padding, unattributed.
    The split is a partition of the library's live requested bytes: its
    residual row must be 0.
  * main payload against 64*M*W from the exact resolved fanout ladder
    (analysis/level_arena_model.py slot enumeration, bank-first run slots
    included): measured minus model, and total minus main.
  * library live requested bytes over that model, `library_live_over_model_main`
    (from the plan alone, so it needs no site names): the paper's "within 1%"
    of the model is this ratio minus 1, which equals
    `total_minus_main_pct_of_main` when every level block matches its model
    size.

Site names need an audit built with debug information and without
position-independent code (-DCMAKE_CXX_FLAGS='-g -fno-pie'
-DCMAKE_EXE_LINKER_FLAGS=-no-pie): with a default (PIE) build every block is
`unattributed`, no level block matches, and the role split stays whole; the
output then says so in a note.

Basis column: `measured` is a counted block (roles from the audit's site
rules); `matched` is a counted block whose size equals the model's exact size
for that slot (the match is the evidence); `model` is derived from the plan or
the layout and was NOT counted separately (the arena allocates mains and the
retained tier holes in one buffer).  Nothing is split by guess: a block that
matches no expected size stays in its audit role, or in `unattributed`.

`main_arena_bytes()` (plan mains + tiers + holes + masks) is NOT bare payload;
it is reported as its own row, apart from 64*M*W.

A failed audit row (`"ok": false`) is reported as a `failed` quantity with its
error and named on stderr; the exit status is 1 when any row failed or the
input held no audit row, and 0 otherwise.
"""
import argparse
import csv
import io
import json
import os
import sys
from dataclasses import dataclass

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import level_arena_model as model  # noqa: E402

HUGE_PAGE = 2 << 20
LIBRARY_ROLES_NOT_HEAP = ("harness_runtime",)
NO_SITE_NAMES = ("the audit named no allocation site (every block is unattributed): rebuild "
                 "cpu_oram_allocation_audit with -DCMAKE_CXX_FLAGS='-g -fno-pie' "
                 "-DCMAKE_EXE_LINKER_FLAGS=-no-pie and rerun it with --sites to split the arena by level; "
                 "library_live_over_model_main needs no site names")
NO_LEVEL_MATCH = ("no level data block matched the model: the role split keeps the arena whole and "
                  "the counted-main rows are omitted")


def aligned64_bytes(n):
    """What AllocateAligned64 asks the allocator for (cpu_byteslice_layout.hpp):
    a request of at least 2 MiB is rounded up to a 2 MiB multiple."""
    return -(-n // HUGE_PAGE) * HUGE_PAGE if n >= HUGE_PAGE else n


@dataclass
class Q:
    name: str
    value: object
    unit: str
    basis: str
    note: str = ""


def load_rows(path):
    rows = []
    with open(path) as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            for prefix in ("AUDIT_ROW ", "ALLOC_AUDIT "):
                if line.startswith(prefix):
                    line = line[len(prefix):]
                    break
            if not line.startswith("{"):
                continue
            rows.append(json.loads(line))
    return rows


def plan_view(row, envelope):
    """(choices, components) as dicts from the row's own plan or an envelope."""
    choices, components = {}, {}
    if envelope is not None:
        raw = envelope.get("choices", [])
        choices = {c["field"]: c["value"] for c in raw} if isinstance(raw, list) else dict(raw)
        components = {c["component"]: c["requested_bytes"]
                      for c in envelope.get("memory_components", [])}
    if "choices" in row:
        raw = row["choices"]
        choices = {c["field"]: c["value"] for c in raw} if isinstance(raw, list) else dict(raw)
    if "components" in row:
        components = {c["component"]: c["bytes"] for c in row["components"]}
    return choices, components


def rowid(row):
    return "%s/k%d:v%d/N%d" % (row["scheme"], row["key_bytes"], row["value_bytes"],
                               row["capacity"])


def heap_quantities(row):
    out = []
    k, v = row["key_bytes"], row["value_bytes"]
    requested_capacity = row["capacity"]
    actual = row.get("actual_capacity") or requested_capacity
    den_req = requested_capacity * (k + v)
    den_act = actual * (k + v)
    out.append(Q("requested_capacity", requested_capacity, "entries", "input"))
    out.append(Q("actual_capacity", actual, "entries", "plan"))
    out.append(Q("denominator_requested", den_req, "bytes",
                 "input", "requested_capacity*(key_bytes+value_bytes)"))
    out.append(Q("denominator_actual", den_act, "bytes", "plan",
                 "actual_capacity*(key_bytes+value_bytes)"))
    phases = [p for p in ("constructed", "filled", "steady") if p in row]
    steady = row.get("steady") or row.get("filled")
    filled = row.get("filled") or steady
    lib = lambda p, f: (p["library"][f] if "library" in p else p[f])  # noqa: E731
    items = [
        ("library_live_after_fill_requested", lib(filled, "live_requested")),
        ("library_live_after_fill_granted", lib(filled, "live_granted")),
        ("library_live_requested", lib(steady, "live_requested")),
        ("library_live_granted", lib(steady, "live_granted")),
        ("library_peak_requested", max(lib(row[p], "peak_requested") for p in phases)),
        ("library_peak_granted", max(lib(row[p], "peak_granted") for p in phases)),
    ]
    for name, value in items:
        out.append(Q(name + "_bytes", value, "bytes", "measured"))
        out.append(Q(name + "_per_requested", value / den_req, "ratio", "measured",
                     "over denominator_requested"))
        out.append(Q(name + "_per_actual", value / den_act, "ratio", "measured",
                     "over denominator_actual"))
    hwms = [row[p].get("hwm") for p in phases]
    if all(h is not None for h in hwms):
        hwm = max(hwms)
        out.append(Q("vmhwm_bytes", hwm, "bytes", "measured",
                     "process-wide peak RSS: runtime, harness and library; never summed with heap"))
        out.append(Q("vmhwm_per_requested", hwm / den_req, "ratio", "measured"))
        out.append(Q("vmhwm_per_actual", hwm / den_act, "ratio", "measured"))
    else:
        # The audit could not reset the peak before this row (a null `hwm`):
        # the process's peak may belong to an earlier row.
        out.append(Q("note", "no VmHWM for this row: the audit could not reset the process's peak RSS",
                     "text", "note"))
    harness = steady.get("harness_live_requested")
    if harness is None and "harness" in steady:
        harness = steady["harness"]["live_requested"]
    if harness is not None:
        out.append(Q("harness_live_requested_bytes", harness, "bytes", "measured",
                     "audit-driver buffers; not in library_*"))
    if "all_peak_requested" in steady:
        out.append(Q("library_plus_harness_peak_requested_bytes",
                     max(row[p].get("all_peak_requested", 0) for p in phases), "bytes",
                     "measured", "heap only (library+harness), no RSS"))
    if "leaked_requested" in row:
        out.append(Q("library_left_live_after_destruction_bytes", row["leaked_requested"],
                     "bytes", "measured"))
    if "allocations" in steady.get("library", steady):
        out.append(Q("library_allocations_while_accessing",
                     lib(steady, "allocations"), "count", "measured"))
    return out


class Blocks:
    """Counted blocks of one role, matched to model sizes by exact size."""

    def __init__(self, blocks):
        self.items = [[b["bytes"], b["count"], b["granted"], b.get("where", "")] for b in blocks]

    def take(self, size):
        for item in self.items:
            if item[0] == size and item[1] > 0:
                item[1] -= 1
                return True
        return False

    def leftover(self):
        return sum(i[0] * i[1] for i in self.items)

    def leftover_blocks(self):
        return [(i[0], i[1], i[3]) for i in self.items if i[1] > 0]


def pct(numerator, denominator):
    return 100.0 * numerator / denominator if denominator else float("nan")


def live_over_model(live, model_main):
    """Library live requested bytes over the main-table model 64*M*W."""
    return [Q("library_live_over_model_main", live / model_main if model_main else float("nan"), "ratio",
              "model", "library live requested / 64*M*W (from the plan; needs no site names); "
              "the paper's 'within 1%' is this minus 1"),
            Q("library_live_minus_model_main_pct", pct(live - model_main, model_main), "%", "model",
              "(library live requested - 64*M*W) / 64*M*W")]


def model_main_payload(row, choices, components):
    """64*M*W from the plan alone, or None: M from the slot enumeration of the
    resolved ladder, W = plan mains / (64*M)."""
    scheme = row["scheme"]
    if scheme not in ("hierarchical_incremental", "hierarchical_synchronous") or "hierarchy.levels" not in choices:
        return None
    fan = fanouts_of(choices)
    D = int(choices["hierarchy.top_digit"])
    z = model.ladder_from_capacity(fan, D, row.get("actual_capacity") or row["capacity"])
    if scheme == "hierarchical_incremental":
        m_buckets = model.ladder_main_buckets(fan, D, z)["M"]
    else:
        m_buckets = sum(r[0] for r in model.synchronous_regions(fan, D, z, tiers_of(choices)))
    mains = components.get("hierarchy.mains")
    if mains is None or not m_buckets or mains % (64 * m_buckets):
        return None
    return mains


def fanouts_of(choices):
    levels = int(choices["hierarchy.levels"])
    return [int(choices["hierarchy.fanout.%d" % l]) for l in range(1, levels)]


def tiers_of(choices):
    levels = int(choices["hierarchy.levels"])
    return [int(choices["hierarchy.tier.%d" % l]) for l in range(1, levels + 1)]


def role_split(row, choices, components):
    """The partition of the library's live requested bytes by role, plus the
    main-payload model comparison.  Only for rows that carry `blocks`."""
    out, notes = [], []
    scheme = row["scheme"]
    blocks = row["blocks"]
    by_role = {}
    for b in blocks:
        by_role.setdefault(b["role"], []).append(b)
    live = (row["filled"]["library"]["live_requested"] if "library" in row["filled"]
            else row["filled"]["live_requested"])
    live_granted = (row["filled"]["library"]["live_granted"] if "library" in row["filled"]
                    else row["filled"]["live_granted"])
    role_bytes = {r: sum(b["bytes"] * b["count"] for b in bl) for r, bl in by_role.items()}
    harness_role = sum(role_bytes.get(r, 0) for r in LIBRARY_ROLES_NOT_HEAP)
    counted = sum(role_bytes.values()) - harness_role
    uncaptured = live - counted
    rows = {}  # partition rows: name -> (bytes, basis, note)

    def add(name, value, basis, note=""):
        old = rows.get(name, (0, basis, note))
        rows[name] = (old[0] + value, basis if (not old[0] or old[1] == basis) else "mixed",
                      note or old[2])

    if blocks and all(b["role"] == "unattributed" or b["role"] in LIBRARY_ROLES_NOT_HEAP for b in blocks):
        notes.append(NO_SITE_NAMES)
    main_payload = None
    model_main = None
    model_note = ""
    padding = 0
    k, v = row["key_bytes"], row["value_bytes"]
    mains_plan = components.get("hierarchy.mains")
    arena = Blocks(by_role.get("arena_combined", []) + by_role.get("sync_tables", []))
    ladder = None
    if scheme in ("hierarchical_incremental", "hierarchical_synchronous") and "hierarchy.levels" in choices:
        fan = fanouts_of(choices)
        D = int(choices["hierarchy.top_digit"])
        actual = row["actual_capacity"]
        z = model.ladder_from_capacity(fan, D, actual)
        tiers = tiers_of(choices)
        bank_first = {"0": "off", "1": "no-clone"}.get(str(choices.get("hierarchy.bank_first", "0")))
        if bank_first is None:
            raise ValueError("bank_first value outside the model (off, no-clone)")
        if scheme == "hierarchical_incremental":
            slots = model.ladder_slots(fan, D, z, tiers, bank_first)
            m_buckets = sum(s[1] for lv in slots for s in lv)
            assert m_buckets == model.ladder_main_buckets(fan, D, z)["M"]
            level_mains = [sum(s[1] for s in lv) for lv in slots]
            level_tiers = [sum(s[2] for s in lv) for lv in slots]
            run_tiers = sum(1 for lv in slots for s in lv if s[0] == "run")
        else:
            regions = model.synchronous_regions(fan, D, z, tiers)
            level_mains = [r[0] for r in regions]
            level_tiers = [2 * r[1] for r in regions]
            m_buckets = sum(level_mains)
            run_tiers = 0
        ladder = dict(fanouts=fan, D=D, z=z, M=m_buckets, run_tiers=run_tiers,
                      bank_first=bank_first, level_mains=level_mains, level_tiers=level_tiers)
        out.append(Q("ladder_fanouts", "-".join(map(str, fan)), "text", "plan", "b_1..b_(L-1)"))
        out.append(Q("ladder_top_digit_D", D, "digit", "plan"))
        out.append(Q("ladder_U1", z, "buckets", "model", "capacity = 32*D*U1*prod(fanouts)"))
        out.append(Q("model_main_buckets_M", m_buckets, "64-slot buckets", "model",
                     "slot enumeration%s" % (
                         "; bank-first run slots add %d tier(s), no main bucket" % run_tiers
                         if run_tiers else "")))
        if mains_plan is not None and mains_plan % (64 * m_buckets) == 0:
            width = mains_plan // (64 * m_buckets)
            out.append(Q("stored_slot_width_W", width, "bytes/slot", "plan",
                         "plan mains / (64*M); key+value+%d tag/meta bytes" % (width - k - v)))
            model_main = 64 * m_buckets * width
            bucket = 64 * width
            out.append(Q("model_main_payload", model_main, "bytes", "model", "64*M*W"))
            out.append(Q("plan_mains_equals_model", int(model_main == mains_plan), "bool",
                         "plan", "resolver mains == 64*M*W"))
            # Each level's data buffer holds its mains plus its tier regions
            # (holes for the arena, live stashes for the synchronous mode) and
            # is rounded by AllocateAligned64.  Exact-size matches first, then
            # the largest leftover block pairs with the largest unmatched
            # level when within 25%: the pair's difference is the finding.
            incremental = scheme == "hierarchical_incremental"
            expected = []
            for l in range(len(level_mains)):
                buckets = level_mains[l] + level_tiers[l]
                mask_words = buckets if incremental else level_mains[l]
                expected.append(dict(level=l + 1, buckets=buckets, mask=mask_words * 8,
                                     size=aligned64_bytes(buckets * bucket),
                                     pad=aligned64_bytes(buckets * bucket) - buckets * bucket,
                                     tier=level_tiers[l] * bucket, main=level_mains[l] * bucket))
            measured_block = {}
            for e in expected:
                if arena.take(e["size"]):
                    measured_block[e["level"]] = e["size"]
            for e in sorted((e for e in expected if e["level"] not in measured_block),
                            key=lambda e: -e["size"]):
                near = [i for i in arena.items if i[1] > 0 and abs(i[0] - e["size"]) <= e["size"] // 4]
                if near:
                    pick = max(near, key=lambda i: i[0])
                    pick[1] -= 1
                    measured_block[e["level"]] = pick[0]
                    notes.append("level %d data block is %d bytes, model %d (paired, not exact)"
                                 % (e["level"], pick[0], e["size"]))
                elif arena.items:  # with no arena block at all, NO_LEVEL_MATCH says it once
                    notes.append("level %d data block (model %d bytes) not found"
                                 % (e["level"], e["size"]))
            tier_regions = mains_in_data = 0
            matched_levels = 0
            for e in expected:
                if e["level"] not in measured_block:
                    continue
                matched_levels += 1
                block = measured_block[e["level"]]
                padding += e["pad"]
                tier_regions += e["tier"]
                mains_in_data += block - e["tier"] - e["pad"]
                if arena.take(e["mask"]):
                    add("masks_tags_metadata", e["mask"], "matched", "occupancy words, exact size")
            out.append(Q("ladder_level_blocks_found", "%d/%d" % (matched_levels, len(expected)),
                         "levels", "matched", "data buffers matched to the slot enumeration"))
            if not matched_levels:
                # Nothing was taken from the arena role: it stays whole below
                # (arena_or_tables_unsplit), and there is no counted main.
                notes.append(NO_LEVEL_MATCH)
            elif incremental:
                pool = aligned64_bytes(sum(level_tiers) * bucket)
                if arena.take(pool):
                    add("residual_tiers", sum(level_tiers) * bucket, "matched",
                        "the set's tier pool, exact size (less its padding)")
                    padding += pool - sum(level_tiers) * bucket
                add("retained_tier_holes", tier_regions, "model",
                    "tier regions embedded in the data buffers (unused)")
            else:
                add("residual_tiers", tier_regions, "model",
                    "two tier stashes per level inside the data buffers")
            if matched_levels:
                main_payload = mains_in_data
                if len(arena.leftover_blocks()) and arena.leftover():
                    add("masks_tags_metadata", arena.leftover(), "measured",
                        "arena blocks with no exact model size (slot runtimes, directories)")
                    notes.append("unmatched arena blocks: %s" % arena.leftover_blocks())
        else:
            notes.append("stored slot width not recoverable: plan mains %s not a multiple of 64*M=%d"
                         % (mains_plan, 64 * m_buckets))
    if scheme == "tree":
        arenas = components.get("tree.arenas")
        tree_blocks = Blocks(by_role.get("tree", []))
        if arenas is not None and tree_blocks.take(aligned64_bytes(arenas)):
            main_payload = arenas
            padding += aligned64_bytes(arenas) - arenas
            model_main = arenas
            model_note = "plan tree.arenas (modeled, requested); single-allocation assumption"
        else:
            notes.append("tree arena block not found at the modeled size")
        # With no matched arena the whole tree role is reported once, as
        # role_tree below; counting its blocks here too would double it.
        if main_payload is not None and tree_blocks.leftover():
            add("masks_tags_metadata", tree_blocks.leftover(), "measured",
                "tree-role blocks other than the arena (objects, knobs)")
        pm = sum(b for n, b in components.items() if n.startswith("position_map."))
        if pm:
            out.append(Q("position_map_model_bytes", pm, "bytes", "model", "sum of position_map.*"))
    # The rest of the roles come straight from the counted blocks.
    if main_payload is not None:
        add("main_payload", main_payload, "matched" if scheme != "tree" else "matched",
            "mains in the matched data buffers (buffer less model tier regions and padding)")
    add("online_stash", role_bytes.get("online_stash", 0), "measured", "dense prefix ring")
    add("rebuild_stashes", 0, "n/a",
        "no separate allocation: sheds live inside the merge scratch")
    add("scratch", role_bytes.get("scratch", 0) + role_bytes.get("plans", 0), "measured",
        "merge, request, batch scratch and the probe-plan pool")
    add("position_map", role_bytes.get("position_map", 0), "measured",
        "the tree's hierarchical position map (all its allocations)")
    add("masks_tags_metadata", role_bytes.get("metadata", 0), "measured",
        "engine objects, wiring, plan data")
    add("library_huge_page_padding", padding, "model",
        "AllocateAligned64 rounds buffers of >= 2 MiB up; inside `requested`")
    unattr = role_bytes.get("unattributed", 0) + uncaptured
    add("unattributed", unattr, "measured",
        "unattributed-role blocks + live bytes with no captured site")
    if scheme == "tree" and main_payload is None:
        add("tree", role_bytes.get("tree", 0), "measured")
    if scheme != "tree" and main_payload is None:
        add("arena_or_tables_unsplit", role_bytes.get("arena_combined", 0)
            + role_bytes.get("sync_tables", 0), "measured",
            "no ladder match: kept whole")
    total = 0
    for name, (value, basis, note) in rows.items():
        out.append(Q("role_" + name + "_bytes", value, "bytes", basis, note))
        total += value
    out.append(Q("role_partition_residual_bytes", live - total, "bytes", "check",
                 "library live requested - sum of role rows; must be 0"))
    out.append(Q("allocator_granted_minus_requested_bytes", live_granted - live, "bytes",
                 "measured", "glibc rounding and 2 MiB alignment slack (address space)"))
    # Main payload against the model.
    if main_payload is not None and model_main is not None:
        delta = main_payload - model_main
        out.append(Q("counted_main_payload_bytes", main_payload, "bytes", "matched"))
        out.append(Q("measured_minus_model_main_bytes", delta, "bytes", "matched",
                     model_note or "counted main - 64*M*W; 0 when every level block has its exact size"))
        out.append(Q("measured_minus_model_main_pct", pct(delta, model_main), "%", "matched"))
        tm = live - main_payload
        out.append(Q("total_minus_main_bytes", tm, "bytes", "matched",
                     "library live requested - counted main payload"))
        out.append(Q("total_minus_main_pct_of_main", pct(tm, main_payload), "%", "matched"))
        out.append(Q("total_minus_main_pct_of_total", pct(tm, live), "%", "matched"))
    if model_main is not None and scheme != "tree":
        out += live_over_model(live, model_main)
    if mains_plan is not None:
        arena_bill = sum(components.get("hierarchy." + n, 0) for n in
                         ("mains", "tiers", "retained tier holes", "masks"))
        out.append(Q("main_arena_bytes_model", arena_bill, "bytes", "model",
                     "mains+tiers+holes+masks: NOT bare payload"))
        if model_main is not None:
            out.append(Q("main_arena_minus_bare_payload_bytes", arena_bill - model_main,
                         "bytes", "model"))
    for n in notes:
        out.append(Q("note", n, "text", "note"))
    # Role rows vs the plan's own components, where the plan has a role.
    for role, comps in (("online_stash", ("dense", "dense masks")),
                        ("scratch", ("persistent scratch", "transient scratch", "request scratch",
                                     "batch scratch", "plan pool"))):
        prefix = "hierarchy." if scheme != "tree" else "position_map."
        if scheme == "tree":
            continue
        modeled = sum(components.get(prefix + c, 0) for c in comps)
        if modeled:
            counted_role = rows[role][0]
            out.append(Q("plan_%s_bytes" % role, modeled, "bytes", "model"))
            out.append(Q("measured_minus_plan_%s_bytes" % role, counted_role - modeled,
                         "bytes", "measured"))
    return out


def reduce_row(row, envelope=None):
    choices, components = plan_view(row, envelope)
    out = [Q("role_attribution", "none" if row.get("role_attribution") == "none" else
             ("sites" if "blocks" in row else "absent"), "text", "note")]
    out += heap_quantities(row)
    if row.get("role_attribution") == "none":
        out.append(Q("main_payload", "n/a", "text", "note",
                     "baseline: no allocation-site roles; totals only (all bytes unattributed)"))
    elif "blocks" in row:
        out += role_split(row, choices, components)
    else:
        out.append(Q("main_payload", "n/a", "text", "note",
                     "audit row has no `blocks`: run cpu_oram_allocation_audit --sites"))
        model_main = model_main_payload(row, choices, components)
        if model_main is not None:
            filled = row["filled"]
            live = filled["library"]["live_requested"] if "library" in filled else filled["live_requested"]
            out.append(Q("model_main_payload", model_main, "bytes", "model", "64*M*W"))
            out += live_over_model(live, model_main)
    return out


def to_csv(results):
    buf = io.StringIO()
    writer = csv.writer(buf, lineterminator="\n")
    writer.writerow(["row", "quantity", "value", "unit", "basis", "note"])
    for rid, qs in results:
        for q in qs:
            value = "%.6g" % q.value if isinstance(q.value, float) else q.value
            writer.writerow([rid, q.name, value, q.unit, q.basis, q.note])
    return buf.getvalue()


def to_markdown(results):
    parts = []
    for rid, qs in results:
        parts.append("### %s\n\n| quantity | value | unit | basis | note |\n|---|---:|---|---|---|" % rid)
        for q in qs:
            if isinstance(q.value, float):
                value = "%.4f" % q.value
            elif isinstance(q.value, int):
                value = "{:,}".format(q.value)
            else:
                value = str(q.value)
            parts.append("| %s | %s | %s | %s | %s |" % (q.name, value, q.unit, q.basis,
                                                        q.note.replace("|", "/")))
        parts.append("")
    return "\n".join(parts)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("audit", nargs="+", help="audit JSON lines (ours or baseline)")
    ap.add_argument("--plan", help="resolver envelope for a row without its own plan")
    ap.add_argument("--csv", help="write the long-form CSV here")
    ap.add_argument("--md", help="write Markdown here (default: stdout)")
    args = ap.parse_args(argv)
    envelope = None
    if args.plan:
        with open(args.plan) as handle:
            envelope = json.load(handle)
    results, failed = [], []
    for path in args.audit:
        for row in load_rows(path):
            if not row.get("ok", True):
                # A failed audit row has nothing to reconcile; it is reported,
                # not dropped.
                error = row.get("error", "no error recorded")
                failed.append((rowid(row), error))
                results.append((rowid(row), [Q("failed", error, "text", "note",
                                               "the audit row failed: nothing reconciled")]))
                continue
            results.append((rowid(row), reduce_row(row, envelope)))
    if args.csv:
        with open(args.csv, "w") as handle:
            handle.write(to_csv(results))
    text = to_markdown(results)
    if args.md:
        with open(args.md, "w") as handle:
            handle.write(text)
    else:
        print(text)
    for rid, error in failed:
        print("allocation_reconcile: audit row %s failed: %s" % (rid, error), file=sys.stderr)
    if not results:
        print("allocation_reconcile: no audit rows in the input", file=sys.stderr)
    # Nonzero when a row failed or there was nothing to reconcile.
    return 1 if failed or not results else 0


if __name__ == "__main__":
    sys.exit(main())
