#!/usr/bin/env python3
"""Audit completed non-top preparation inputs, old-home bias and families.

This source/geometry audit supports main-only deletion and the prospective
late reset. It is not a full capacity certificate or engine-history proof.
"""
from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
import hashlib
import itertools
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile

from audit_ordinary_ranges import require
from source_scope import provenance, scoped

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def home_mass_bound(bits, radix, total):
    """Exact upper density relative to uniform bucket labels.

    For N independent old-home words, dP/dQ <= (M*p_max)^N.
    Bound this by 1/(1-N*delta), avoiding huge rational powers.
    This is multiplicative; an additive statistical-distance allowance would
    swamp the desired rare-event probability.
    """
    block = 1 << bits
    words = 1 << (64 - bits)
    q, rem = divmod(words, radix)
    minimum = Fraction(q, 1 << 64)
    maximum = Fraction(q + bool(rem), 1 << 64)
    delta = block * radix * maximum - 1
    require(0 <= total * delta < 1, 'density bound needs N*delta < 1')
    return dict(minimum_bucket_mass=str(minimum),
                maximum_bucket_mass=str(maximum),
                exactly_uniform=rem == 0,
                per_key_relative_excess=str(delta),
                joint_density_upper_bound=str(1 / (1 - total * delta)))


def offer_count_checks():
    """Count algebra of the two allocation rounds in PlanResidualOfferMerge.

    Distinct candidates imply each cleared main key has a different fresh
    replacement: clear <= fresh. Dropped stale duplicates are excluded here.
    """
    checks = 0
    for capacity in range(1, 9):
        for main in range(capacity + 1):
            for stale in range(capacity + 1):
                for fresh in range(capacity - stale + 1):
                    for clear in range(min(main, fresh) + 1):
                        take_stale = min(stale, capacity - main)
                        after_stale = main - clear + take_stale
                        take_fresh = min(fresh, capacity - after_stale)
                        final = after_stale + take_fresh
                        require(final >= main, 'offer cannot lower occupancy')
                        if stale > take_stale or fresh > take_fresh:
                            require(final == capacity, 'leftover needs full home')
                        checks += 1
    return checks


def likelihood_checks():
    # An intentionally visible odd-modulus bias: 3-bit words reduced mod 3.
    # Check the bound for EVERY retained count state, not just a few
    # exponential tests. The finite model has 3 buckets, 4 keys, capacity 2.
    probabilities = (Fraction(3, 8), Fraction(3, 8), Fraction(2, 8))
    actual, reference = defaultdict(Fraction), defaultdict(Fraction)
    for homes in itertools.product(range(3), repeat=4):
        counts = tuple(homes.count(i) for i in range(3))
        probability = Fraction(1)
        for i in homes:
            probability *= probabilities[i]
        retained = tuple(min(n, 2) for n in counts)
        actual[retained] += probability
        reference[retained] += Fraction(1, 3**4)
    factor = (3 * max(probabilities))**4
    require(sum(actual.values()) == sum(reference.values()) == 1, 'total mass')
    require(all(p <= factor * reference[state] for state, p in actual.items()),
            'pushed-forward likelihood comparison')
    delta = 3 * max(probabilities) - 1
    require(factor <= 1 / (1 - 4 * delta), 'rational geometric upper bound')
    require(actual[(2, 1, 1)] != actual[(1, 1, 2)],
            'biased old homes do not give exact retained exchangeability')
    return dict(states=len(actual), density_factor=str(factor),
                biased_permutation_witness={
                    '2,1,1': str(actual[(2, 1, 1)]),
                    '1,1,2': str(actual[(1, 1, 2)])})


def main():
    inventory = json.loads((HERE / 'ordinary_range_audit.json').read_text())
    for name, digest in scoped(inventory['source_sha256']).items():
        require(hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest,
                f'stale ordinary inventory: rerun audit_ordinary_ranges.py ({name})')
    with tempfile.TemporaryDirectory(prefix='preparation-contract-') as tmp:
        exe = str(Path(tmp) / 'probe')
        subprocess.run(shlex.split(os.environ.get('CXX', 'g++')) + [
            '-O2', '-std=c++17', '-march=native', '-pthread', '-I', str(ROOT),
            str(HERE / 'preparation_contract_probe.cpp'), '-o', exe], check=True)
        rows = [json.loads(line) for line in
                subprocess.check_output([exe], text=True).splitlines()]
    require({(r['level'], r['digit']) for r in rows} ==
            set(itertools.product(range(1, 6), range(2, 9))), 'all A boundaries')
    for row in rows:
        require(row['old_buckets'] * 32 == row['population_bound'], 'half load')
        row['old_home_law'] = home_mass_bound(
            row['old_low_bits'], row['old_radix'], row['population_bound'])
    max_density = max(Fraction(r['old_home_law']['joint_density_upper_bound'])
                      for r in rows)
    require(max_density < Fraction(1000001, 1000000), 'small multiplicative bias')
    names = set(inventory['source_sha256']) | {
        'analysis/bound_certification/code/audit_preparation_contract.py',
        'analysis/bound_certification/code/preparation_contract_probe.cpp',
        'src/oram/levelarena/cpu_byteslice_level_arena_engine.hpp',
        'src/oram/levelarena/cpu_byteslice_level_arena_batch.hpp',
        'src/oram/levelarena/cpu_byteslice_level_arena_dense.hpp',
        'src/oram/levelarena/cpu_byteslice_level_arena_level.hpp',
        'src/oram/levelarena/cpu_byteslice_level_arena_publication.hpp',
        'src/oram/rebuild/cpu_byteslice_second_chance.hpp',
        'tests/oram/cpu_byteslice_level_arena_job_test.cpp',
        'src/oram/rebuild/cpu_byteslice_dfs_residual.hpp',
        'src/oram/scheduler/cpu_byteslice_residual_pass.hpp',
        'tests/oram/cpu_byteslice_dfs_reference.hpp',
        'tests/oram/cpu_byteslice_level_arena_top_test.cpp',
        'tests/oram/cpu_byteslice_level_arena_init_test.cpp',
    }
    result = dict(
        scope='Completed non-top inputs; conditional source audit, not capacity certification',
        full_home_claim='On successful completed non-top jobs, distinct main/tier keys imply a_i=min(x_i,64)',
        ideal_family_premise='Independent ideal words for the complete logical key set; do not condition on selected residuals or successful capacity',
        ordinary_boundaries=len(rows),
        family_checks=sum(r['family_checks'] for r in rows),
        biased_boundaries=sum(not r['old_home_law']['exactly_uniform'] for r in rows),
        maximum_density_upper_bound=str(max_density),
        offer_count_checks=offer_count_checks(),
        likelihood_checks=likelihood_checks(),
        source_sha256=provenance({name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                              for name in sorted(names)}),
        boundaries=rows, pooled_source_inventory='ordinary_range_audit.json',
        unchanged_adoptions=inventory['adoption_cases'],
        open_obligations=[
            'Joint A/B marks and B current-family selection in capacity tests',
            'Engine input-history independence for old/new family words and logical key sets',
            'Partial-job storage ledger, source failures and lifetime union bound',
            'Joint preparation/finish stash bounds and every residual range shape'],
        all_checks_passed=True)
    (HERE / 'preparation_contract_audit.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in (
        'ordinary_boundaries', 'family_checks', 'biased_boundaries',
        'maximum_density_upper_bound', 'offer_count_checks',
        'likelihood_checks', 'all_checks_passed')}, indent=2))


if __name__ == '__main__':
    main()
