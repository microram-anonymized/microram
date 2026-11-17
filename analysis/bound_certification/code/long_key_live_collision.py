#!/usr/bin/env python3
"""Export exact per-member tightened allocations and normalization comparisons.

All probability columns are in units of 2^-64. JSON retains exact rationals;
CSV decimals are presentation only. The global birthday term uses the existing
model theorem. The live-N endpoints are registered Lean theorems. N-1 is not
a valid general bound (a miss at a full map has N live partners) and appears
only as a diagnostic column. The original components are regenerated
from their Lean/structural inputs. The tightened allocation changes three local
numerical bounds, retaining the same analytic witnesses and adaptive population
cutoffs. The registered Lean statements, not this Python report, prove validity.
"""
import argparse
import csv
from collections import Counter
from decimal import Decimal, localcontext
from fractions import Fraction
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

import linear_wide_key_components as components


HERE = Path(__file__).resolve().parent
SPEC = HERE.parents[2] / "lean/RebuildBound/Spec"
ACCESS_ENVELOPE = 2**32
TOTAL_INPUT_LIMIT = 2**31
SCALE = 2**64
OUTPUT = HERE / "long_key_live_collision.json"
CSV_OUTPUT = HERE / "long_key_live_collision.csv"
CONTROL_CSV_OUTPUT = HERE / "long_key_live_collision_controls.csv"
SUMMARY_CSV_OUTPUT = HERE / "long_key_live_collision_summary.csv"
LIVE_ENDPOINT_STATUS = "NativeMatchLivePublicFailure/Observation and NativeMatchLiveWindowError registered and integrated; owned, branch, and main package checks, axiom audits, kernel replay, and library tests passed"
MODES = ("original_global_birthday", "tightened_global_birthday",
         "original_live_n", "tightened_live_n",
         "original_diagnostic_n_minus_1", "tightened_diagnostic_n_minus_1")


def fraction(value):
    return Fraction(value["numerator"], value["denominator"])


def decimal(value):
    with localcontext() as ctx:
        ctx.prec = 36
        return format(Decimal(value.numerator) / Decimal(value.denominator), ".18f")


def amount(value):
    return dict(**components.rational(value), decimal=decimal(value))


def tight_registry():
    """Read the three new full-shape rational overrides, failing on drift."""
    path = SPEC / "NativeMatch/TightBudget.lean"
    source = path.read_text()

    def shape(name):
        match = re.search(r"def " + name + r" : \w+ := ⟨([^⟩]+)⟩", source)
        if match is None:
            raise ValueError(f"Missing tight shape: {name}")
        return tuple(json.loads("[" + match[1] + "]"))

    def budget(name):
        match = re.search(r"if g = " + name + r" then (\d+) / \((\d+) \* 2 \^ (\d+)\)", source)
        if match is None:
            raise ValueError(f"Missing tight rational: {name}")
        num, den, exponent = map(int, match.groups())
        return Fraction(num, den * 2**exponent)

    return {"top": {shape("topShape"): budget("topShape")},
            "range": {shape(name): budget(name) for name in ("rangeShape14", "rangeShape20")}}


def ordinal_counts(fixture):
    for level, fanout in enumerate(fixture["level_fanouts"], 1):
        carry = fixture["carry_buckets"][level - 1]
        ordinals = ACCESS_ENVELOPE // (32 * carry) + 1
        seed = fixture["seeded_carries"][level - 1]
        for digit in range(1, fanout + 1):
            count = (seed + ordinals - digit) // fanout - (seed - digit) // fanout
            yield level, digit, count


def overflow_components(fixture, registries, tight):
    """The initialized exposure envelope is deliberately used for both starts."""
    parts = Counter()
    improved = Counter()
    sep = {(s["level"], s["digit"]): s for s in fixture["shapes"]["sep"]}
    for level, digit, count in ordinal_counts(fixture):
        if level == 1:
            value = Fraction(1, 2**117)
            if digit != 1:
                value += Fraction(1, 2**99) + Fraction(1, 2**111)
            parts["level_one"] += count * value
            improved["level_one"] += count * value
        elif digit != 1:
            shape = sep[level, digit]
            key = tuple(shape[field] for field in components.SHAPE_FIELDS["sep"])
            for kind in ("rest", "range"):
                value = components.shape_budget(registries[kind], shape, "sep")
                parts["separated_" + kind] += count * value
                improved["separated_" + kind] += count * tight.get(kind, {}).get(key, value)
    top_count = ACCESS_ENVELOPE // (32 * fixture["carry_buckets"][-1]) + 1
    for job, kind, count, label in (("top", "top", top_count, "top_finish"),
                                    ("prep", "prep", top_count, "top_prepare"),
                                    ("init", "prep", 1, "initialization")):
        shape = fixture["shapes"][job]
        value = components.shape_budget(registries[kind], shape, kind)
        key = tuple(shape[field] for field in components.SHAPE_FIELDS[kind])
        parts[label] += count * value
        improved[label] += count * tight.get(kind, {}).get(key, value)
    return ({key: value * SCALE for key, value in parts.items()},
            {key: value * SCALE for key, value in improved.items()})


def matching_sites(fixture):
    """Disaggregate the existing S_min; this proposes no new comparison bound."""
    out = Counter()
    carries, tiers, stashes = (fixture[k] for k in
                             ("carry_buckets", "level_tier_buckets", "stash_buckets"))
    r0 = fixture["r0"]
    for level, digit, count in ordinal_counts(fixture):
        out["prefix_dedup"] += count * (64 * (r0 * (r0 - 1) // 2) if level == 1 else 0)
        if digit < 2:
            continue
        carry = carries[level - 1]
        fanout = fixture["level_fanouts"][level - 1]
        e = (digit & -digit).bit_length() - 1
        odd = digit // 2**e
        output, rec_a, rec_b = digit * carry, 32 * (digit - 1) * carry, 32 * carry
        t_b = 1 if level == 1 else tiers[level - 2]
        t_a = tiers[level - 2] if level >= 2 and digit == 2 and fanout > 2 else tiers[level - 1]
        stash, tier = stashes[level - 1], tiers[level - 1]
        merge_stash = max(stash, tiers[0]) if level == 1 else stash
        a_slots = stash * (carry.bit_length() - 1 + e + (odd > 1)) + t_a
        a_res, b_tier = min(rec_a, 64 * a_slots), min(rec_b, 64 * t_b)
        output_recs = min(rec_a + rec_b, 64 * output)
        charges = dict(
            ordinary_fixed_dedup=min(rec_a, 64 * output),
            ordinary_offer_a_leaf=a_res,
            ordinary_offer_b_tier=min(t_b * output_recs, b_tier),
            ordinary_pool_dedup=min(t_b * a_res, a_slots * b_tier),
            ordinary_leftover_dedup=tier * min(64 * merge_stash, rec_b)
                + merge_stash * min(64 * tier, rec_a),
        )
        for key, value in charges.items():
            out[key] += count * value
    rec_a, rec_b = 32 * 8 * carries[-1], 32 * carries[-1]
    t_b, stash, tier = tiers[-2], stashes[-1], tiers[-1]
    a_main, retained = min(rec_a, 64 * 8 * carries[-1]), min(64 * stash, rec_a)
    b_tier = min(rec_b, 64 * t_b)
    charges = dict(
        top_fixed_dedup=a_main, top_resolve_a_leaf=retained,
        top_resolve_b_tier=min(t_b * a_main, b_tier),
        top_pool_dedup=min(t_b * retained, stash * b_tier),
        top_leftover_dedup=tier * min(64 * stash, rec_b) + stash * min(64 * tier, rec_a),
    )
    for key, value in charges.items():
        out[key] += (ACCESS_ENVELOPE // (32 * carries[-1]) + 1) * value
    return out


def max_accesses(overflow, matching, initial, capacity, subtract_one):
    """Largest n meeting the strict target, conditional on the chosen formula."""
    initial_charge = Fraction(initial * (initial - 1), 2 * SCALE)
    budget = 1 - overflow - matching - initial_charge
    if budget <= 0:
        return 0
    upper = budget * SCALE / (capacity - int(subtract_one))
    return min(ACCESS_ENVELOPE, max(0, -(-upper.numerator // upper.denominator) - 1))


def outcome(overflow, matching, collision, existing_birthday=False, diagnostic=False):
    values = dict(overflow=overflow, matching=matching, collision=collision)
    total = sum(values.values())
    return dict(**{key: amount(value) for key, value in values.items()}, total=amount(total),
                dominant_term=max(values, key=values.get), target_met=total < 1,
                collision_bound_status=("existing_model_birthday" if existing_birthday else
                    "diagnostic_only_invalid_for_full_map_misses" if diagnostic else "live_N_registered_endpoint_checked_and_kernel_replayed"),
                margin_to_target=amount(1 - total), excess_over_target=amount(max(0, total - 1)))


def report():
    source = components.report()
    if json.loads(components.OUTPUT.read_text()) != source:
        raise ValueError("Existing component export is stale; its original source must be reconciled first")
    fixtures = {m["name"]: m for m in json.loads(
        (HERE / "configuration_family_structure.json").read_text())["members"]}
    registries = {kind: components.budget_registry(kind) for kind in ("top", "prep", "rest", "range")}
    tight = tight_registry()
    rows = []
    for row in source["members"]:
        fixture = fixtures[row["name"]]
        original_parts, tight_parts = overflow_components(fixture, registries, tight)
        overflow = fraction(row["capacity_initialized_exposure_budget"]) * SCALE
        matching = fraction(row["matching_probability_budget"]) * SCALE
        if sum(original_parts.values()) != overflow:
            raise ValueError("Overflow decomposition disagrees with existing export")
        sites = matching_sites(fixture)
        if sum(sites.values()) != row["matching_s_min"]:
            raise ValueError("Matching decomposition disagrees with existing export")
        initial = row["capacity"] if row["initialized"] else 0
        accesses = TOTAL_INPUT_LIMIT - initial
        if accesses < 0:
            raise ValueError("Member capacity exceeds the requested total-input window")
        birthday_pairs = initial * (initial - 1) // 2
        collision_proposed = Fraction(birthday_pairs + accesses * (row["capacity"] - 1), SCALE)
        collision_conservative = Fraction(birthday_pairs + accesses * row["capacity"], SCALE)
        control_proposed = Fraction(birthday_pairs + ACCESS_ENVELOPE * (row["capacity"] - 1), SCALE)
        control_conservative = Fraction(birthday_pairs + ACCESS_ENVELOPE * row["capacity"], SCALE)
        tight_overflow = sum(tight_parts.values())
        global_collision = Fraction(TOTAL_INPUT_LIMIT * (TOTAL_INPUT_LIMIT - 1), 2 * SCALE)
        control_q = initial + ACCESS_ENVELOPE
        control_global = Fraction(control_q * (control_q - 1), 2 * SCALE)
        rows.append(dict(
            name=row["name"], initialized=row["initialized"], capacity=row["capacity"],
            initial_records=initial, accesses=accesses, total_initial_records_and_accesses=TOTAL_INPUT_LIMIT,
            original_global_birthday=outcome(overflow, matching, global_collision, True),
            tightened_global_birthday=outcome(tight_overflow, matching, global_collision, True),
            original_diagnostic_n_minus_1=outcome(overflow, matching, collision_proposed, diagnostic=True),
            tightened_diagnostic_n_minus_1=outcome(tight_overflow, matching, collision_proposed, diagnostic=True),
            original_live_n=outcome(overflow, matching, collision_conservative),
            tightened_live_n=outcome(tight_overflow, matching, collision_conservative),
            controls_at_2pow32_accesses=dict(
                original_global_birthday=outcome(overflow, matching, control_global, True),
                tightened_global_birthday=outcome(tight_overflow, matching, control_global, True),
                original_live_n=outcome(overflow, matching, control_conservative),
                tightened_live_n=outcome(tight_overflow, matching, control_conservative),
                original_diagnostic_n_minus_1=outcome(overflow, matching, control_proposed, diagnostic=True),
                tightened_diagnostic_n_minus_1=outcome(tight_overflow, matching, control_proposed, diagnostic=True),
            ),
            observation_collision=amount(Fraction(birthday_pairs, SCALE)),
            tightened_observation_total=amount(tight_overflow + matching + Fraction(birthday_pairs, SCALE)),
            original_overflow_components={key: amount(value) for key, value in original_parts.items()},
            tightened_overflow_components={key: amount(value) for key, value in tight_parts.items()},
            matching_s_min_per_access=amount(Fraction(sum(sites.values()), ACCESS_ENVELOPE)),
            matching_s_min_sites_per_access={key: amount(Fraction(value, ACCESS_ENVELOPE)) for key, value in sites.items()},
            matching_rebuild=amount(Fraction(row["matching_rebuild_weight"], SCALE)),
            matching_dense=amount(Fraction(row["matching_dense_weight"], SCALE)),
            gap_options_with_live_n_collision=dict(
                overflow_must_be_strictly_below=amount(1 - collision_conservative - matching),
                original_overflow_reduction_must_exceed=amount(max(0, overflow + matching + collision_conservative - 1)),
                tightened_overflow_reduction_must_exceed=amount(max(0, tight_overflow + matching + collision_conservative - 1)),
                matching_alone_can_close_remaining_gap=tight_overflow + collision_conservative < 1,
                largest_access_count_original=max_accesses(overflow, matching, initial, row["capacity"], False),
                largest_access_count_tightened=max_accesses(tight_overflow, matching, initial, row["capacity"], False),
            ),
        ))
    if len(rows) != 188 or len({(r["name"], r["initialized"]) for r in rows}) != 188:
        raise ValueError("Expected all 94 certified members and both starts")
    summary = {}
    for mode in MODES:
        worst = max(rows, key=lambda r: fraction(r[mode]["total"]))
        summary[mode] = dict(rows_meeting_target=sum(r[mode]["target_met"] for r in rows),
                             rows_missing_target=sum(not r[mode]["target_met"] for r in rows),
                             worst_member=worst["name"], worst_total=worst[mode]["total"],
                             minimum_margin=worst[mode]["margin_to_target"])
    return dict(
        format="long-key-normalization-comparison/3", probability_unit="2^-64",
        allocation_access_envelope=ACCESS_ENVELOPE, main_total_input_limit=TOTAL_INPUT_LIMIT, control_accesses=ACCESS_ENVELOPE, chunks=1, initial_records="I=0 for empty; I=N=member capacity for initialized",
        key_widths=list(range(17, 65)),
        scope="Exact tightened allocations, corrected live-N semantic failure totals, separate observation totals, and original-birthday controls",
        total_endpoint_status=LIVE_ENDPOINT_STATUS,
        integrated_fallback="NativeMatchTightPublicFailure/Observation and NativeMatchTightWindowError: 1<=h<=4 and I+n<=h*2^31 with the original birthday term.",
        collision_status="The corrected coefficient is N, covering a miss while N distinct keys are live. Its complete native endpoint passed the registered package workflow. N-1 is a diagnostic, not a valid general bound.",
        collision_formulas=dict(global_birthday="choose(I+n,2)/2^128", live_n="(choose(I,2) + n*N)/2^128",
                                diagnostic_n_minus_1="(choose(I,2) + n*(N-1))/2^128"),
        primary_formula="live_n; global_birthday is an integrated fallback; N-1 is a historical diagnostic only",
        window_interpretation="Arbitrary positive h is a cumulative-run allowance: I+n<=h*2^31 and failure<3*h/4*2^-64. This is not a conditional guarantee for each subsequent cycle.",
        observation_formula="h*(overflow+matching)+choose(I,2)/2^128; only initial aliases are charged; physical observation remains a separate distributional event.",
        semantic_event="New semantic failure covers actual stops, original logical replies and prefix states, and public result/address counts. Existing pointwise original-reference address correctness is unchanged and is not asserted under dead aliases.",
        allocation_notes=[
            "Overflow uses the initialized exposure envelope for both starts, exactly as the existing checked allocation.",
            "Both overflow versions retain every existing matching charge from the full 2^32-access envelope. The corrected live collision coefficient N is proved by the integrated native endpoint.",
            "The main window is I+n=2^31. Initialized rows use I=member capacity and n=2^31-I; empty rows use I=0 and n=2^31.",
            "For any intermediate I<=N and I+n<=2^31, choose(I,2)+n*N <= 2^31*N; the empty-start collision row therefore bounds every allowed initialization size.",
            "Separate controls retain n=2^32 without limiting I+n; maximum-n gap options are capped at the current h=1 envelope.",
            "Tightened overflow replaces only three full-shape numerical budgets under the same analytic bounds and population cutoffs.",
            "The fixed-request conditional Python ledger and affine normalization allowance are not inputs.",
            "All comparisons and target decisions use exact rational arithmetic; decimals are display values.",
        ],
        matching_investigation=[
            "The per-row S_min breakdown includes prefix deduplication, ordinary fixed deduplication, ordinary residual sites, top fixed deduplication, and top residual sites separately.",
            "The allocation uses the full 2^32-access envelope and includes the existing extra top ordinal; this can exceed a count of completed rebuilds alone.",
            "A smaller range-local residual inventory needs a new execution-count proof. Omitting prefix deduplication or the ordinal guard from the existing allocation does not establish that bound.",
            "No matching refinement is used here: the three overflow refinements already give overflow plus matching below 0.5 in units of 2^-64 for every member and both starts.",
        ],
        certificate_statements=["NativeMatchTightLocalNumerics", "NativeMatchTightExposure", "NativeMatchTightArithmetic",
                                "NativeMatchTightAdaptiveCapacity", "NativeMatchTightPublicAllocation",
                                "NativeMatchTightPublicFailure", "NativeMatchTightPublicObservation", "NativeMatchTightWindowError"],
        endpoint_statements=["NativeMatchLivePublicFailure", "NativeMatchLivePublicObservation", "NativeMatchLiveWindowError"],
        summary=summary,
        control_summary={mode: dict(
            rows_meeting_target=sum(row["controls_at_2pow32_accesses"][mode]["target_met"] for row in rows),
            rows_missing_target=sum(not row["controls_at_2pow32_accesses"][mode]["target_met"] for row in rows),
        ) for mode in MODES},
        source_sha256={**source["source_sha256"],
                       **{f"lean/RebuildBound/Spec/NativeMatch/{name}.lean": hashlib.sha256(
                           (SPEC / f"NativeMatch/{name}.lean").read_bytes()).hexdigest()
                          for name in ("TightBudget", "TightPublic", "LivePairs", "Semantic", "LivePublic")},
                       "code/linear_wide_key_components.py": hashlib.sha256(
                           (HERE / "linear_wide_key_components.py").read_bytes()).hexdigest(),
                       "code/configuration_family_structure.json": source["structural_fixture_sha256"]},
        members=rows,
    )


def csv_report(data, control=False):
    output = io.StringIO(newline="")
    fields = ["name", "start", "capacity"]
    for mode in MODES:
        fields += [f"{mode}_{term}_in_2pow_minus64" for term in
                   ("overflow", "matching", "collision", "total", "margin_to_target")]
        fields += [mode + "_dominant_term", mode + "_target_met"]
    fields += ["initial_records", "accesses", "max_accesses_with_tightened_allocation_and_live_n_collision", "matching_s_min_per_access"]
    writer = csv.DictWriter(output, fields, lineterminator="\n")
    writer.writeheader()
    for row in data["members"]:
        values = dict(name=row["name"], start="initialized" if row["initialized"] else "empty",
                      capacity=row["capacity"],
                      initial_records=row["initial_records"], accesses=ACCESS_ENVELOPE if control else row["accesses"],
                      max_accesses_with_tightened_allocation_and_live_n_collision=row["gap_options_with_live_n_collision"]["largest_access_count_tightened"],
                      matching_s_min_per_access=row["matching_s_min_per_access"]["decimal"])
        results = row["controls_at_2pow32_accesses"] if control else row
        for mode in MODES:
            for term in ("overflow", "matching", "collision", "total", "margin_to_target"):
                values[f"{mode}_{term}_in_2pow_minus64"] = results[mode][term]["decimal"]
            values[mode + "_dominant_term"] = results[mode]["dominant_term"]
            values[mode + "_target_met"] = results[mode]["target_met"]
        writer.writerow(values)
    return output.getvalue()


def summary_csv_report(data):
    """One readable row per member/start; all probability terms use 2^-64."""
    output = io.StringIO(newline="")
    fields = ["member", "start", "N", "I", "n", "tight_overflow", "matching",
              "linear_collision", "total", "dominant", "target"]
    writer = csv.DictWriter(output, fields, lineterminator="\n")
    writer.writeheader()
    for row in data["members"]:
        bound = row["tightened_live_n"]
        writer.writerow(dict(member=row["name"], start="initialized" if row["initialized"] else "empty",
            N=row["capacity"], I=row["initial_records"], n=row["accesses"],
            tight_overflow=bound["overflow"]["decimal"], matching=bound["matching"]["decimal"],
            linear_collision=bound["collision"]["decimal"], total=bound["total"]["decimal"],
            dominant=bound["dominant_term"], target="met" if bound["target_met"] else "missed"))
    return output.getvalue()


def check_lean_coefficients(data):
    """Independent evaluator cross-check, separate from the registered proofs."""
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    source = """import RebuildBound.Spec.NativeMatch.TightBudget
open RebuildBound.Spec
#eval do
  for m in ConfigurationFamily.members do
    for initialized in [false, true] do
      let q := NativeMatchTightBudget.exposureBudget m
      let w := NativeMatchInventory.weight m initialized
      IO.println s!"{m.name}|{initialized}|{q.num}|{q.den}|{w}"
"""
    with tempfile.TemporaryDirectory(prefix="long-key-coefficients-") as directory:
        path = Path(directory) / "Export.lean"
        path.write_text(source)
        result = subprocess.run([lake, "env", "lean", str(path)], cwd=SPEC.parents[1],
                                capture_output=True, text=True, check=True)
    expected = {(row["name"], row["initialized"]): row for row in data["members"]}
    seen = set()
    for line in result.stdout.splitlines():
        name, start, numerator, denominator, weight = line.split("|")
        if start not in ("true", "false"):
            raise ValueError("Unexpected Lean start flag")
        key = name, start == "true"
        if key in seen:
            raise ValueError("Duplicate Lean export row")
        seen.add(key)
        row = expected[key]
        if Fraction(int(numerator), int(denominator)) * SCALE != fraction(row["tightened_live_n"]["overflow"]):
            raise ValueError(f"Lean/Python overflow mismatch: {key}")
        if Fraction(int(weight), SCALE) != fraction(row["tightened_live_n"]["matching"]):
            raise ValueError(f"Lean/Python matching mismatch: {key}")
    if seen != set(expected):
        raise ValueError("Incomplete Lean coefficient export")
    print("PASS: all 188 exact overflow/matching coefficients equal direct Lean evaluation")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check all four committed exports")
    parser.add_argument("--check-lean", action="store_true",
                        help="also compare all coefficients against direct Lean evaluation")
    args = parser.parse_args()
    data = report()
    rendered = {OUTPUT: json.dumps(data, indent=2) + "\n", CSV_OUTPUT: csv_report(data),
                CONTROL_CSV_OUTPUT: csv_report(data, control=True), SUMMARY_CSV_OUTPUT: summary_csv_report(data)}
    for path, contents in rendered.items():
        if args.check:
            if not path.exists() or path.read_text() != contents:
                raise SystemExit(f"Missing or stale export: {path}")
        else:
            path.write_text(contents)
    if args.check_lean:
        check_lean_coefficients(data)
    print("PASS: 188 exact allocations and certified live-N totals (endpoint package workflow passed); " + ", ".join(
        f"{mode} {data['summary'][mode]['rows_meeting_target']}/188 below target"
        for mode in MODES))


if __name__ == "__main__":
    main()
