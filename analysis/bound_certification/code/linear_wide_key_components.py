#!/usr/bin/env python3
"""Report exact, probe, completed-build and routing-pair coefficients and margins.

This is the reproducible coefficient report for the checked ideal complete-message
linear and best-bound endpoints. Lean regressions independently check the
family-wide ranges. Raw crossovers retain the endpoint's field/counter-fit
premises and the stated initialization size; they compare uncapped counts.
Capacity/matching margins reproduce the existing certified rational allocation;
they do not absorb normalization into that allocation.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re


HERE = Path(__file__).resolve().parent
BASE = HERE.parent
SPEC = BASE.parents[1] / "lean/RebuildBound/Spec"
OUTPUT = HERE / "linear_wide_key_components.json"
SOURCES = [
    "ConfigurationFamilyData.lean", "ConfigurationFamilyGeometry.lean",
    "Model/Config.lean", "NativeMatch/Physical.lean",
    "NativeMatch/ExactCounts.lean", "NativeRouting/FamilyExposure.lean",
    "NativeRouting/BuildSupport.lean", "NativeRouting/LocalPairs.lean",
    "NativeNormalize.lean", "NativeMatch/LocalBound.lean", "NativeMatch/LinearCoded.lean",
    "ConfigurationFamilyBudget.lean", "ConfigurationFamilyTop.lean",
    "ConfigurationFamilyPrep.lean", "ConfigurationFamilyRange.lean",
    "ConfigurationFamilyRest.lean", "NativeMatch/Allocation.lean",
]

SHAPE_FIELDS = {
    "sep": ("C", "K", "e", "r", "range_bits", "I", "stash_pages",
            "a_tier_pages", "b_tier_pages", "tier_pages"),
    "top": ("C", "k", "e", "rho", "I", "dfs", "r_pages", "b_pages",
            "merge_pages", "tier_pages"),
    "prep": ("C", "k", "stash_pages", "a_tier_pages", "drain_pages",
             "range_bits", "I", "dfs"),
}


def rational(value):
    return {"numerator": value.numerator, "denominator": value.denominator}


def budget_registry(kind):
    """Read exact certified dyadics, keyed by the complete Lean shape tuple."""
    source = (SPEC / f"ConfigurationFamily{kind.title()}.lean").read_text()
    body = source.split(f"def {kind}Budgets", 1)[1].split(":= [", 1)[1].split("]", 1)[0]
    registry = {}
    for line in body.strip().splitlines():
        match = re.fullmatch(
            r"\s*\(\(?⟨([^⟩]+)⟩(?: : SepGeom\))?, (\d+)(?:, (\d+))?\),?\s*", line)
        if match is None:
            raise ValueError(f"Unrecognized {kind} budget row: {line}")
        shape = tuple(json.loads("[" + match[1] + "]"))
        if shape in registry:
            raise ValueError(f"Duplicate {kind} budget shape: {shape}")
        registry[shape] = sum((Fraction(1, 2**int(e)) for e in match.groups()[1:]
                               if e is not None), Fraction())
    return registry


def shape_budget(registry, shape, kind):
    # Fail on a missing shape: the proof's fallback budget of one cannot certify
    # any member here, and should not conceal a changed numerical inventory.
    return registry[tuple(shape[field] for field in SHAPE_FIELDS[kind])]


def allocation_components(fixture, registries, initialized):
    """Reproduce exposureBudget and NativeMatchInventory.weight exactly.

    The capacity reserve uses initialized exposures for BOTH starts, as in
    NativeMatchInventory.Fits. Matching uses the requested start's exposures;
    the seeded ordinary digit counts agree and initialization has zero charge.
    Native full-shape fixtures supply the checked budget lookup geometry.
    """
    r0, fanouts = fixture["r0"], fixture["level_fanouts"]
    carries, tiers, stashes = (fixture[k] for k in
                             ("carry_buckets", "level_tier_buckets", "stash_buckets"))
    horizon = fixture["horizon_accesses"]
    if horizon != 2**32 or fixture["load"] != 32 or fixture["top_digit"] != 8:
        raise ValueError("Unsupported capacity-allocation configuration")
    sep = {(s["level"], s["digit"]): s for s in fixture["shapes"]["sep"]}
    expected_clocks = {}
    capacity_budget, s_min = Fraction(), 0
    for level, fanout in enumerate(fanouts, 1):
        carry = carries[level - 1]
        ordinals = horizon // (32 * carry) + 1
        seed = fixture["seeded_carries"][level - 1]
        if seed != 8 * carries[-1] // carry:
            raise ValueError("Structural fixture seed mismatch")
        for digit in range(1, fanout + 1):
            count = (seed + ordinals - digit) // fanout - (seed - digit) // fanout
            match_seed = seed if initialized else 0
            match_count = ((match_seed + ordinals - digit) // fanout
                           - (match_seed - digit) // fanout)
            expected_clocks[f"ordinary_L{level}_d{digit}"] = count
            if level == 1:
                budget = Fraction(1, 2**117)
                if digit != 1:
                    budget += Fraction(1, 2**99) + Fraction(1, 2**111)
            elif digit == 1:
                budget = Fraction()
            else:
                shape = sep[level, digit]
                budget = sum((shape_budget(registries[k], shape, "sep")
                              for k in ("rest", "range")), Fraction())
            capacity_budget += count * budget

            # NativeMatchInventory.ordinary, including the prefix-dedup charge.
            charge = 64 * (r0 * (r0 - 1) // 2) if level == 1 else 0
            if digit >= 2:
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
                charge += (min(rec_a, 64 * output) + a_res + min(t_b * output_recs, b_tier)
                           + min(t_b * a_res, a_slots * b_tier)
                           + tier * min(64 * merge_stash, rec_b)
                           + merge_stash * min(64 * tier, rec_a))
            s_min += match_count * charge

    top_count = horizon // (32 * carries[-1]) + 1
    expected_clocks.update(top_prepare=top_count, top_finish=top_count, initialization=1)
    if expected_clocks != {c["name"]: c["exposures"] for c in fixture["clocks"]}:
        raise ValueError("Structural fixture exposure mismatch")
    for job, kind, count in (("top", "top", top_count), ("prep", "prep", top_count),
                             ("init", "prep", 1)):
        capacity_budget += count * shape_budget(registries[kind], fixture["shapes"][job], kind)

    # NativeMatchInventory.top; top preparation and initialization have charge 0.
    rec_a, rec_b = 32 * 8 * carries[-1], 32 * carries[-1]
    t_b, stash, tier = tiers[-2], stashes[-1], tiers[-1]
    a_main, retained, b_tier = min(rec_a, 64 * 8 * carries[-1]), min(64 * stash, rec_a), min(rec_b, 64 * t_b)
    top_charge = (a_main + retained + min(t_b * a_main, b_tier)
                  + min(t_b * retained, stash * b_tier)
                  + tier * min(64 * stash, rec_b) + stash * min(64 * tier, rec_a))
    s_min += top_count * top_charge
    arena_slots = sum(1 + (b == 8) for b in fanouts) + 2 * len(fanouts) + 2
    dense_buckets = 3 * r0 + arena_slots
    rebuild_weight = 64**4 * s_min
    dense_weight = 2**32 * dense_buckets * 14 * 8**2
    matching = Fraction(rebuild_weight + dense_weight, 2**128)
    remaining = Fraction(1, 2**64) - capacity_budget - matching
    if remaining < 0:
        raise ValueError(f"Certified allocation exceeded: {fixture['name']}")
    return dict(capacity_initialized_exposure_budget=rational(capacity_budget),
                matching_s_min=s_min, matching_dense_buckets=dense_buckets,
                matching_rebuild_weight=rebuild_weight, matching_dense_weight=dense_weight,
                matching_probability_budget=rational(matching),
                capacity_matching_probability_budget=rational(capacity_budget + matching),
                capacity_matching_remaining_to_target=rational(remaining),
                capacity_matching_remaining_fraction_of_target=rational(remaining * 2**64))


def raw_crossover(initial_keys, allowance, per_access):
    """First q after which A+B*q <= choose(initial_keys+q, 2)."""
    def holds(q):
        total = initial_keys + q
        return allowance + per_access * q <= total * (total - 1) // 2

    # The difference birthday-linear is increasing beyond its integer minimum.
    low = max(0, per_access - initial_keys)
    if holds(low):
        return 0
    high = max(1, 2 * low)
    while not holds(high):
        high *= 2
    while low + 1 < high:
        middle = (low + high) // 2
        if holds(middle):
            high = middle
        else:
            low = middle
    assert holds(high) and not holds(high - 1)
    return high


def report():
    source = (SPEC / "ConfigurationFamilyData.lean").read_text()
    pattern = re.compile(
        r'^\s*⟨("[^"]+"), (\d+), (\[[^\]]*\]), (\[[^\]]*\]), (\[[^\]]*\])⟩,?\s*$',
        re.MULTILINE,
    )
    members = pattern.findall(source)
    if len(members) != 94 or len({row[0] for row in members}) != 94:
        raise ValueError("Expected exactly the 94 distinct certified members")
    fixtures = {
        m["name"]: m
        for m in json.loads((HERE / "configuration_family_structure.json").read_text())["members"]
    }
    registries = {kind: budget_registry(kind) for kind in ("top", "prep", "rest", "range")}
    rows = []
    for encoded_name, encoded_r0, encoded_fanouts, encoded_tiers, encoded_stashes in members:
        name, r0, fanouts = json.loads(encoded_name), int(encoded_r0), json.loads(encoded_fanouts)
        carry = [2 * r0]
        for fanout in fanouts:
            carry.append(carry[-1] * fanout)
        capacity = 32 * 8 * carry[-1]
        fixture = fixtures[name]
        if (capacity != fixture["capacity_entries"] or carry != fixture["carry_buckets"]
                or fanouts != fixture["level_fanouts"] or r0 != fixture["r0"]
                or json.loads(encoded_tiers) != fixture["level_tier_buckets"]
                or json.loads(encoded_stashes) != fixture["stash_buckets"]):
            raise ValueError(f"Structural fixture mismatch: {name}")
        # NativeMatchPhysical.levelSlots, including top slots and lower inboxes.
        bank_run_end = lambda b: b // 2 if (b // 2) % 2 == 1 else max(0, b // 2 - 1)
        slots = sum(1 + (bank_run_end(b) >= 2) for b in fanouts) + 2 * len(fanouts) + 2
        lower_populations = [32 * b * c for b, c in zip(fanouts, carry)]
        max_records = max([capacity] + lower_populations)
        width = max(lower_populations, default=0)
        exact = 192 + 192 * r0 + slots * max_records
        span = slots * width + 3 * (64 * r0) + 64
        build_coordinate = 3 * max_records + 64 * r0 + capacity
        build_family = len(carry) * build_coordinate
        carry_positions = [32 * c for c in carry]
        family_keys = build_family + span
        family_pairs = family_keys * (family_keys - 1) // 2
        route_a = len(carry) * family_pairs
        route_b = sum((family_pairs + d - 1) // d for d in carry_positions)
        combined_b = exact + route_b
        for initialized in (False, True):
            initial_keys = capacity if initialized else 0
            crossover = raw_crossover(initial_keys, route_a, combined_b)
            crossover_allowance = Fraction(route_a + crossover * combined_b, 2**128)
            rows.append(dict(
                name=name, initialized=initialized, capacity=capacity, r0=r0,
                allocated_slots=slots, max_records=max_records, non_top_width=width,
                exact_pairs_per_access=exact, probe_keys_per_family=span,
                build_keys_per_coordinate=build_coordinate,
                build_keys_per_family=build_family,
                carry_positions=carry_positions,
                routing_keys_per_family=family_keys,
                routing_pairs_per_family=family_pairs,
                routing_initial_allowance=route_a,
                routing_pairs_per_access=route_b,
                combined_pairs_per_access=combined_b,
                routing_initial_probability=rational(Fraction(route_a, 2**128)),
                combined_probability_per_access=rational(Fraction(combined_b, 2**128)),
                combined_raw_allowance_at_2pow32_accesses=rational(
                    Fraction(route_a + 2**32 * combined_b, 2**128)),
                crossover_initial_keys=initial_keys,
                raw_birthday_crossover_accesses=crossover,
                raw_allowance_at_crossover=rational(crossover_allowance),
                crossover_before_probability_saturation=crossover_allowance < 1,
                exact_probability_per_access=rational(Fraction(exact, 2**128)),
                exact_allowance_at_2pow32_accesses=rational(Fraction(exact, 2**96)),
                **allocation_components(fixture, registries, initialized),
            ))
    return dict(
        format="linear-wide-key-components/5",
        scope="Checked ideal complete-message linear and best-bound endpoints; raw crossovers retain field/counter-fit and initialization premises",
        base_horizon_accesses=2**32,
        base_probability_target=rational(Fraction(1, 2**64)),
        formulas=dict(
            exact="q * exact_pairs_per_access (ring-ready); initialization allowance is zero",
            probe_keys="probe_keys_per_family (ring-ready)",
            probe_ordinals="at level l: at most 1 + floor(q / carry_positions[l-1])",
            build_keys="build_keys_per_family (unconditional reference completed-table support)",
            build_coordinate="3 * max_records + 64 * r0 + capacity",
            build_ordinals="at level l: at most 1 + floor(q / carry_positions[l-1]); includes seeded bases",
            routing_pairs="A_route + q * B_route (ring-ready), for the canonical full-run family inventory",
            routing_initial="A_route = levels * choose(build_keys_per_family + probe_keys_per_family, 2)",
            routing_per_access="B_route = sum_l ceil(routing_pairs_per_family / carry_positions[l-1])",
            combined_pairs="A_route + q * (B_route + exact_pairs_per_access); one normalization charge in NativeMatchLinearCoded",
            best_normalization="Widths 17-64: min(1, min(choose(initial_keys + q, 2), combined_pairs) / 2^128); width 16: zero; NativeMatchBestCoded compares identical failure/observation events",
            crossover="Eventual raw count crossover against choose(initial_keys + q, 2); initialized rows use full-capacity initialization, empty-start rows use zero",
            crossover_saturation="crossover_before_probability_saturation tests only the normalization allowance < 1; it does not certify total error < 1 or field/counter fit at that horizon",
            capacity_matching="At base horizon 2^32: exposureBudget(member) + weight(member,start)/2^128; exact rational allocation from NativeMatchInventory.Fits, using initialized capacity exposures for both starts",
            matching="weight = 64^4 * sMin + 2^32 * denseBuckets * 14 * 8^2; includes rebuild and dense VP2 matching",
            remaining_margin="2^-64 - capacity_initialized_exposure_budget - matching_probability_budget; nonnegative residual of the existing certified allocation, not an additional failure bound or a normalization absorption claim",
            chunk_scaling="For h chunks multiply the capacity, matching, target and residual by h; the checked endpoint remains h * 2^-64 + normalization",
        ),
        source_sha256={str(Path("lean/RebuildBound/Spec") / p): hashlib.sha256(
            (SPEC / p).read_bytes()).hexdigest() for p in SOURCES},
        structural_fixture_sha256=hashlib.sha256(
            (HERE / "configuration_family_structure.json").read_bytes()).hexdigest(),
        members=rows,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="compare the committed report")
    args = parser.parse_args()
    rendered = json.dumps(report(), indent=2) + "\n"
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text() != rendered:
            raise SystemExit("Component report is missing or stale; regenerate it")
        print("PASS: component report matches all 94 geometries and both starts")
    else:
        OUTPUT.write_text(rendered)
        print(f"Wrote {OUTPUT}")


if __name__ == "__main__":
    main()
