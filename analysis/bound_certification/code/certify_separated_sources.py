#!/usr/bin/env python3
"""Fresh native adapter for separated ordinary jobs, excluding other source classes.

Runs at both selected configurations: the uniform-eight worked configuration
and the default half-fanout ladder at the same capacity (fanout four at levels
one to three). Every sparse digit of every level below the top is covered.
"""
from decimal import localcontext
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import tempfile

from audit_preparation_contract import home_mass_bound
from certify_completed_a import evaluate as range_bound
from certify_oram import UP, ZERO, describe, upper_fraction
from certify_preparation import stage_bound
from certify_tier_router import positive_excess_bound
from check_configuration import ROOT, SELECTED, compile_probe, digit_exposures, normalize, probe
from loss_tree import initial, next_tree
from source_scope import provenance, scoped

HERE = Path(__file__).resolve().parent


def old_law(row):
    old = (row['digit']-1)*(1 << row['carry_bits'])
    power = (old & -old).bit_length()-1
    return home_mass_bound(power, old >> power, 32*old)


def check_shape(row):
    k, b, r, d, i = (row[key] for key in
                       ('carry_bits', 'block_bits', 'radix', 'digit', 'index_bits'))
    if not (row['kind'] == 'ordinary' and row['separated_sources']
            and row['level'] > 1 and 2 <= d <= 8 and not row['dense_bits']
            and 0 <= i < 64 and 0 < k <= b < 64 and r % 2 == 1
            and (not row['dfs'] or i < k)
            and d*(1 << k) == r*(1 << b) == row['out_buckets']
            and row['direct_buckets'] == row['carry_tier_buckets'] > 0
            and row['older_tier_buckets'] > 0 and row['tier_buckets'] > 0
            and row['stash_buckets'] > 0
            and (not row['dfs'] or row['groups'] == 1)):
        raise ValueError('Outside the separated ordinary source contract')
    a_pages = row['older_tier_buckets']+(b+int(r > 1))*row['stash_buckets']
    if row['pool_buckets'] != a_pages+row['direct_buckets']:
        raise ValueError('A pool omits a completed route stash or includes another source')
    if not row['dfs'] and not (
            row['main_bits'] <= 3 and i == row['main_bits']
            and row['range_bits'] == 0
            and row['groups'] == row['range_buckets'] == a_pages
            and row['scatter_per_bucket'] == 64):
        raise ValueError('Not the native direct A partition')
    if row['dfs'] and (row['range_bits'] != row['main_bits']-i
                      or row['range_buckets'] != 1 << row['range_bits']):
        raise ValueError('Not the native one-page coarse partition')


def subset_bound(nodes, slots):
    """B_sub(nodes, 64, 32, slots, 1) (Proposition general-subset), by
    certify_preparation.stage_bound.  Its finite part sums the first
    `cutoff` subset sizes exactly and bounds the rest by a geometric tail,
    valid once the tail ratio is below one.  The default cutoff (64) is kept
    wherever that holds, so every such value is unchanged; for a larger
    output (over about 2^23 homes) the cutoff is doubled until it holds.
    The cutoff is an evaluation parameter of the same sum, not a new bound."""
    cutoff = 64
    while True:
        try:
            return stage_bound(nodes, slots, cutoff)[0]
        except ValueError as error:
            if 'Increase cutoff' not in str(error):
                raise
            cutoff *= 2


def storage_bounds(row):
    """Binary raw-arrival stages; final radix; shared insertion/output excess."""
    check_shape(row)
    nodes, b, r = row['out_buckets'], row['block_bits'], row['radix']
    slots = 64*row['stash_buckets']
    a_count = 32*(row['digit']-1)*(1 << row['carry_bits'])
    previous = old_law(row)
    current_a = home_mass_bound(b, r, a_count)
    current_union = home_mass_bound(b, r, 32*nodes)
    # Complete raw destinations are independent categorical trials under the
    # uniform old-home reference, with mass <= 1/((d-1)U). Native source
    # induction supplies this premise; restricted-excess then gives Phi at
    # mean 32. Transfer the old-map density once, outside either bound.
    raw = min(subset_bound(nodes, slots), positive_excess_bound(nodes, slots))
    packing_slots = 64*min(row['stash_buckets'], row['tier_buckets'])
    packing_raw = min(subset_bound(nodes, packing_slots),
                      positive_excess_bound(nodes, packing_slots))
    with localcontext(UP):
        binary = raw*upper_fraction(Q(previous['joint_density_upper_bound']))
        radix = raw*upper_fraction(Q(current_a['joint_density_upper_bound'])) if r > 1 else ZERO
        stages = describe('completed_A_route_stashes', min(1,b*binary+radix),
            binary_stage_count=b, binary_per_stage_upper=str(binary),
            radix_upper=str(radix), capacity_slots=slots,
            padded_destinations=nodes, old_map_law=previous, current_A_map_law=current_a)
        packing = describe('insertion_and_published_tier',
            min(1,packing_raw*upper_fraction(Q(current_union['joint_density_upper_bound']))),
            capacity_slots=packing_slots, logical_union_upper=32*nodes,
            current_union_map_law=current_union, charged_once=True)
    return stages, packing


GATE_KEYS = ('branching', 'levels', 'top_digit', 'prefix_flushes', 'stash_buckets',
             'dense_prefixes', 'level_fanouts')


def expected_domain(native):
    """Every sparse (level, digit >= 2) below the top, at each level's fanout."""
    seeds = {row['level']: row for row in native if row['kind'] == 'ordinal_seed'}
    top = max(seeds)
    return {(level, digit) for level in range(2, top)
            for digit in range(2, seeds[level]['fanout']+1)}


def certify_configuration(name, config, exe):
    native = probe(config, exe)
    selected = [row for row in native if row['kind'] == 'ordinary' and row['level'] > 1 and row.get('separated_sources')]
    if {(row['level'],row['digit']) for row in selected} != expected_domain(native):
        raise ValueError(f'Native selected domain changed ({name})')
    for row in selected:
        check_shape(row)
    wanted = {row['block_bits']-row['index_bits'] for row in selected if row['dfs']}
    trees, f = {}, initial()
    for depth in range(1,max(wanted)+1):
        if depth in wanted:
            trees[depth] = f
        if depth < max(wanted):
            f = next_tree(f)
    levels = {row['level']: row for row in native if row['kind']=='level'}
    seeds = {row['level']: row for row in native if row['kind']=='ordinal_seed'}
    cases, subtotal, components = [], Q(0), {name:Q(0) for name in ('stages','ranges','packing')}
    per_level = {}
    for row in selected:
        stage, packing = storage_bounds(row)
        i = row['index_bits']
        density = Q(old_law(row)['joint_density_upper_bound'])
        ranges = (range_bound(trees[row['block_bits']-i], k=row['carry_bits'],
                  digit=row['digit'], index_bits=i,
                  early=64*(row['older_tier_buckets']+i*row['stash_buckets']), density=density)
                  if row['dfs'] else describe('direct_A_pool',ZERO))
        seed = seeds[row['level']]
        if seed['seeded_carries'] % seed['fanout']:
            raise ValueError('Initialization seed is not a whole digit cycle')
        exposures = digit_exposures(config['horizon_accesses'],
            levels[row['level']]['carry_positions'], seed['fanout'],row['digit'],seed['seeded_carries'])
        parts = dict(stages=stage,ranges=ranges,packing=packing)
        total = min(1,sum((Q(v['probability_upper_decimal']) for v in parts.values()),Q(0)))
        cases.append(dict(shape=row, **parts, per_job_upper_exact=str(total),exposures=exposures))
        subtotal += exposures*total
        per_level[row['level']] = per_level.get(row['level'], Q(0)) + exposures*total
        for part,value in parts.items():
            components[part] += exposures*Q(value['probability_upper_decimal'])
        print(name, row['level'],row['digit'], ranges['approximate_log2_for_display_only'],
              describe('',upper_fraction(total))['approximate_log2_for_display_only'],flush=True)
    return dict(ladder=name, configuration=config,
        configuration_gate={key:config[key] for key in GATE_KEYS},
        level_fanouts_native={level: seeds[level]['fanout'] for level in sorted(seeds) if level < max(seeds)},
        cases=cases, lifetime_subtotal_exact=str(subtotal),
        lifetime_subtotal=describe('selected_ordinary_jobs',upper_fraction(subtotal)),
        levels={str(level): describe(f'level_{level}', upper_fraction(value))
                for level, value in sorted(per_level.items())},
        components={part:describe(part,upper_fraction(value)) for part,value in components.items()},
        below_2_minus_64= subtotal < Q(1,1 << 64))


def main():
    with tempfile.TemporaryDirectory(prefix='separated-certificate-') as tmp:
        exe, sources = compile_probe(tmp)
        sections = [certify_configuration(name, normalize(config), exe)
                    for name, config in SELECTED.items()]
    for name in ('certify_separated_sources.py','certify_completed_a.py','loss_tree.py',
                 'gmp_square.cpp','certify_oram.py','certify_preparation.py','certify_tier_router.py',
                 'certify_sorted_range.py','audit_preparation_contract.py',
                 'audit_ordinary_ranges.py','check_configuration.py'):
        sources[str((HERE/name).relative_to(ROOT))] = hashlib.sha256((HERE/name).read_bytes()).hexdigest()
    uniform, *others = sections
    result = dict(scope=__doc__, **uniform, additional_configurations=others,
        source_sha256=provenance(sources), complete_configuration_certified=False,
        assumptions=[
            'Native source and frontier propositions, ideal independent families, tombstones included.',
            'First-failure witnesses use fixed logical populations, not conditioning on execution success.',
            'Completed blank-B binary stages, no reinsertion; terminal radix uses the current full-home law.',
            'Separated source recipe includes all A route losses and old tier; direct B tier reuses its producer.',
            'Fixed B insertion deduplicates before capacity, with unchanged original-source and coordinated drain rules.',
            'Empty or directly initialized start; per-digit ordinal lists include next speculative preparation.',
            'Each section applies only under its configuration gate and at its exact native shapes; the half-fanout section covers the default ladder at the uniform section\'s capacity, r0, D, s, q and horizon.',
        ], exclusions=['Dense level one, top preparation/finish, initialization, other configurations, and the complete deterministic inventory audit.',
                       'Cryptographic and key-equality errors are separate.'])
    (HERE/'separated_sources_certificates.json').write_text(json.dumps(result,indent=2)+'\n')
    for section in sections:
        print('Selected ordinary subtotal', section['ladder'],
              section['lifetime_subtotal']['approximate_log2_for_display_only'],flush=True)

if __name__ == '__main__':
    main()
