#!/usr/bin/env python3
"""Audit ordinary range maps and dependencies; deliberately not a certificate.

Compile the production-header probe, check maps with independent arithmetic,
and write an obligation ledger for all 40 non-top level/digit combinations.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction
import hashlib
import itertools
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
from source_scope import provenance, scoped

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def range_masses(word_bits, low_bits, radix, index_bits, range_bits):
    """Exact fresh-word masses of flat ranges, including unused padded ones.

    The low field and high word are independent. Count the high-word residues
    by quotient/remainder, then intersect each digit block with each range.
    This is NOT the law of a selected residual or an input tier.
    """
    block = 1 << low_bits
    width = 1 << index_bits
    q, rem = divmod(1 << (word_bits-low_bits), radix)
    masses = []
    for r in range(1 << range_bits):
        count = 0
        for digit in range(radix):
            overlap = max(0, min((r+1)*width, (digit+1)*block)
                          - max(r*width, digit*block))
            count += overlap*(q + (digit < rem))
        masses.append(Fraction(count, 1 << word_bits))
    require(sum(masses) == 1, "range mass conservation")
    return masses


def check_small_masses():
    checks = 0
    for word_bits in range(4, 11):
        for low_bits in range(word_bits-2):
            for radix in (1, 3, 5, 7):
                main_bits = (radix*(1 << low_bits)-1).bit_length()
                for index_bits in range(main_bits+1):
                    actual = Counter(((t % (1 << low_bits)) + (1 << low_bits)*
                        ((t >> low_bits) % radix)) >> index_bits
                        for t in range(1 << word_bits))
                    masses = range_masses(word_bits, low_bits, radix,
                                          index_bits, main_bits-index_bits)
                    require(all(p == Fraction(actual[r], 1 << word_bits)
                                for r, p in enumerate(masses)), "enumerated radix mass")
                    checks += 1
    return checks


def expected_plan(pages, main_bits):
    if pages == 0:
        return 0, main_bits, 1, 1, 64
    if main_bits <= 3:
        return 0, main_bits, pages, pages, 64
    bits = min((8*pages-1).bit_length(), main_bits)
    sub = 1 << bits
    per = next(p for p in (8, 16, 32, 64) if pages*(64//p) <= sub or p == 64)
    groups = (pages*(64//per)+sub-1)//sub
    return bits, main_bits-bits, groups*sub, groups, per


PLAN_KEYS = ('range_bits', 'index_bits', 'range_buckets', 'groups', 'scatter_per_bucket')


def check_plan(row):
    pages, main_bits = row['pool_buckets'], row['main_bits']
    require(tuple(row[k] for k in PLAN_KEYS) == expected_plan(pages, main_bits),
            "production planner differs from independent integer geometry")
    b, i, buckets, groups, per = (row[k] for k in PLAN_KEYS)
    # Each origin retains its group through every butterfly stage. Check the
    # scatter inverse and the offer's group/range addressing for all slots and
    # three destination boundaries (no probabilistic assumption).
    for page in range(pages):
        for slot in range(64):
            initial = page*(64//per)+slot//per
            group = initial >> b
            require(group < groups, "scatter group outside table")
            require((initial//(64//per), (initial % (64//per))*per+slot % per)
                    == (page, slot), "scatter inverse")
            for destination in {0, (1 << main_bits)//2, (1 << main_bits)-1}:
                routed = (initial & ~((1 << b)-1)) | (destination >> i)
                offer = group*(1 << b)+(destination >> i)
                require(routed == offer and routed < buckets, "group/offer mismatch")
    return ('empty' if pages == 0 else 'direct' if b == 0 else
            'stacked' if groups > 1 else 'packed' if per > 8 else 'eight_way')


def source_ledger(row):
    """Completed A-only route sources; B's tier is offered directly."""
    if not row['finish_pass']:
        require(row['dense_direct'] and row['digit'] == 1 and
                row['pool_buckets'] == 0, 'digit-one direct build has no finish pool')
        return [], None
    sources = [dict(source='older_route_shed', pages=row['stash_buckets'],
                    rank=2, tier_class=False, stage=stage)
               for stage in range(1, row['block_bits']+1)]
    if row['radix'] > 1:
        sources.append(dict(source='older_radix_shed', pages=row['stash_buckets'],
                            rank=2, tier_class=False))
    sources.extend([
        dict(source='older_tier', pages=row['older_tier_buckets'], rank=2,
             tier_class=False, selection_family='older'),
        dict(source='direct_B_tier' if row['dense_direct'] else 'incoming_tier',
             pages=row['carry_tier_buckets'], rank=0, tier_class=True,
             selection_family='current', offered_directly=True)])
    require(sum(x['pages'] for x in sources) == row['pool_buckets'], 'source pool sum')
    require(row['direct_buckets'] == row['carry_tier_buckets'], 'direct B-tier width')
    return sources, 'merge_stash'


def check_current_plan(row):
    pages = row['pool_buckets'] - row['direct_buckets']
    bits = row['main_bits']
    base = expected_plan(pages, bits)
    if pages and bits > 3:
        rb, ib = base[:2]
        rb, ib = rb + max(0, ib-18), min(ib, 18)
        expected = rb, ib, 1 << rb, 1, 64
        regime = 'A_only_DFS'
    else:
        expected, regime = base, 'direct' if pages else 'no_finish'
    require(tuple(row[k] for k in PLAN_KEYS) == expected,
            'production DFS differs from independent integer geometry')
    return regime


def exact_comparison_checks():
    # Distinctness alone does not imply deferred selection: choose the first
    # zero-bit key, if one exists. This is an abstract counterexample to that
    # implication, not a claimed execution of the production tier builder.
    selected = sum(Fraction(any(bit == 0 for bit in bits), 4)
                   for bits in itertools.product((0, 1), repeat=2))
    require(selected == Fraction(3, 4) > Fraction(1, 2), "selection witness")
    # A dependence-safe fallback: (sum X_i - sum c_i)+ <= sum (X_i-c_i)+.
    # Thus marginal stop losses can be combined WITHOUT multiplying MGFs.
    checks = 0
    for values in itertools.product(range(5), repeat=3):
        for capacities in itertools.product(range(4), repeat=3):
            require(max(sum(values)-sum(capacities), 0) <=
                    sum(max(x-c, 0) for x, c in zip(values, capacities)),
                    "dependence-safe stop-loss split")
            checks += 1
    return dict(distinct_selected_range_probability=str(selected),
                independent_one_key_probability='1/2',
                selection_witness_scope='Abstract selection, not a production failure example',
                dependence_safe_stoploss_checks=checks)


def main():
    with tempfile.TemporaryDirectory(prefix='ordinary-range-audit-') as tmp:
        exe = str(Path(tmp)/'probe')
        subprocess.run(shlex.split(os.environ.get('CXX', 'g++')) +
            ['-O2', '-std=c++17', '-march=native', '-I', str(ROOT), '-pthread',
             str(HERE/'ordinary_range_probe.cpp'), '-o', exe], check=True)
        rows = [json.loads(line) for line in subprocess.check_output([exe], text=True).splitlines()]
    ordinary = [r for r in rows if r['kind'] == 'ordinary']
    adoptions = [r for r in rows if r['kind'] == 'adoption']
    half = [r for r in rows if r['kind'] == 'half_fanout_ordinary']
    half_adoptions = [r for r in rows if r['kind'] == 'half_fanout_adoption']
    require({(r['level'], r['digit']) for r in ordinary+adoptions} ==
            set(itertools.product(range(1, 6), range(1, 9))), 'all uniform digits covered')
    ladder = (4, 4, 4, 8, 8, 8)
    require({(r['level'], r['digit']) for r in half+half_adoptions} ==
            {(l, d) for l in range(1, 7) for d in range(1, ladder[l-1]+1)},
            'all half-fanout digits covered')
    planner_regimes = Counter(check_plan(r) for r in rows if r['kind'] == 'planner')
    for row in ordinary+half:
        row['regime'] = check_current_plan(row)
        row['sources'], row['drain_only'] = source_ledger(row)
        require(row['map_checks'] > 0 and row['family_checks'] ==
                3*(int(row['level'] > 1)+int(row['digit'] > 1)), 'map/family checks')
        low_bits = row['block_bits'] if row['radix'] > 1 else row['main_bits']
        masses = range_masses(64, low_bits, row['radix'], row['index_bits'], row['range_bits'])
        row['fresh_key_range_mass_histogram'] = [dict(probability=str(p), patterns=count)
            for p, count in sorted(Counter(masses).items())]
        row['reachable_patterns'] = sum(p > 0 for p in masses)
        row['fresh_key_max_range_probability'] = str(max(masses))
        row['source_selection_law_certified'] = False
        row['capacity_certified_by_this_audit'] = False
    reference = HERE/'ordinary_geometry_reference.json'
    frozen = json.loads(reference.read_text())
    keys = PLAN_KEYS + ('main_bits', 'pool_buckets', 'direct_buckets', 'stash_buckets',
                       'older_tier_buckets', 'carry_tier_buckets', 'finish_pass', 'dense_direct')
    for name, current in [('passes', ordinary), ('half_fanout_passes', half)]:
        previous = {(r['level'], r['digit']): r for r in frozen[name]}
        require(set(previous) == {(r['level'], r['digit']) for r in current}, 'snapshot coverage')
        for row in current:
            require(all(row[k] == previous[row['level'], row['digit']][k] for k in keys),
                    'snapshot geometry')
    names = ('src/oram/levelarena/cpu_byteslice_level_arena_pass_shape.hpp',
             'src/oram/levelarena/cpu_byteslice_level_arena_merge.hpp',
             'src/oram/levelarena/cpu_byteslice_level_arena_family.hpp',
             'src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp',
             'src/oram/levelarena/cpu_byteslice_level_arena_stash.hpp',
             'src/oram/rebuild/cpu_byteslice_residual_range.hpp',
             'src/oram/rebuild/cpu_byteslice_dfs_residual.hpp',
             'src/oram/table/cpu_byteslice_routing_map.hpp',
             'analysis/bound_certification/code/ordinary_range_probe.cpp',
             'analysis/bound_certification/code/audit_ordinary_ranges.py')
    result = dict(
        scope='Current direct level one and separated ordinary finishes at both selected ladders; '
              'map/dependency audit, not a capacity certificate. Digit one has no finish pass.',
        assumptions='Fresh-word masses use an ideal uniform 64-bit tag; selected residuals are not assigned this law',
        excluded_maps='kFoldDuplicate and other engines are outside this audit',
        source_ledger_method='Completed A route sheds and older tier, with direct B-tier offers; native pool-size checks',
        source_sha256=provenance({n: hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in names}),
        ordinary_passes=len(ordinary), adoption_cases=adoptions,
        nonterminal_passes=sum(not r['terminal_digit'] for r in ordinary),
        scalar_production_map_checks=sum(r['map_checks'] for r in ordinary),
        small_exact_mass_checks=check_small_masses(),
        planner_cases=sum(planner_regimes.values()), planner_regimes=dict(planner_regimes),
        comparison_checks=exact_comparison_checks(), passes=ordinary,
        half_fanout_passes=half, half_fanout_adoption_cases=half_adoptions,
        half_fanout_family_checks=sum(r['family_checks'] for r in half),
        input_sha256={reference.name: hashlib.sha256(reference.read_bytes()).hexdigest()},
        all_checks_passed=True)
    (HERE/'ordinary_range_audit.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ('passes', 'half_fanout_passes', 'source_sha256')}, indent=2))


if __name__ == '__main__':
    main()
