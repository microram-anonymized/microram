#!/usr/bin/env python3
"""Evaluate the binary top finish as a separated pass, like every sparse ordinary digit.

The top merge (BuildTopMergePass) distributes A's class alone -- the
preparation's retained carry R -- through one one-page DFS leaf per coarse
range and offers B's carry tier directly to every destination
(Proposition separated-capacity).  Its capacity events are
  * the A-only coarse-range event max_r R_r > 64 (DFS containment), where
    R_r = sum over the range's 2^I homes of (Y^A_v - 64)_+ is exactly A's
    complete-home excess (the b_A marginal of Proposition top-finish-ranges
    at the leaf: no intermediate stage, no stars);
  * none for B's direct pages (its tier's capacity is charged at its
    producer);
  * the merge stash and published tier, one live-set excess at the smaller
    capacity (Proposition top-excess), charged once.
Both selected configurations (uniform-eight and the default half-fanout
ladder) have one gated section each.
"""
from decimal import localcontext
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import tempfile

from check_configuration import ROOT, SELECTED, compile_probe, normalize, probe
from certify_oram import UP, describe, upper_fraction
from certify_tier_router import positive_excess_bound
from source_scope import provenance, scoped

HERE = Path(__file__).resolve().parent
CAPACITY = 64  # one 64-slot bucket per home, one page per DFS leaf


def check_shape(row):
    """The native separated binary-top finish: A = the retained carry
    (stash_buckets pages), B = the carry tier offered directly, and the
    finish range plan of that pool (a one-page DFS leaf table, or the direct
    plan of a small main, which routes nothing)."""
    if (row['kind'] != 'top_finish' or row['radix'] != 1 or row['dense_bits']
            or not 1 <= row['main_bits'] < 64 or row['block_bits'] != row['main_bits']
            or row['out_buckets'] != 1 << row['main_bits']
            or not row['separated_sources']
            or row['direct_buckets'] != row['carry_tier_buckets'] or row['direct_buckets'] < 1
            or row['older_tier_buckets'] != 0
            or row['stash_buckets'] < 1 or row['tier_buckets'] < 1
            or row['pool_buckets'] != row['stash_buckets'] + row['direct_buckets']):
        raise ValueError('Outside the separated binary-top finish contract')
    # The positive series picks its own truncation for every capacity
    # (certify_tier_router.series_cutoff), so no capacity gate is needed.
    a_pages = row['pool_buckets'] - row['direct_buckets']
    if row['dfs']:
        if not (row['groups'] == 1 and row['scatter_per_bucket'] == 64
                and row['range_bits'] + row['index_bits'] == row['main_bits']
                and row['range_buckets'] == 1 << row['range_bits']):
            raise ValueError('Not the native one-page coarse partition')
    elif not (row['range_bits'] == 0 and row['index_bits'] == row['main_bits']
              and row['groups'] == row['range_buckets'] == a_pages):
        raise ValueError('A non-DFS top finish must be the direct plan')


def evaluate(row, exposures):
    check_shape(row)
    stash_slots = CAPACITY*row['stash_buckets']
    if not row['dfs']:
        # Direct plan: the range table is the pool itself; no range test.
        ranges = dict(name='direct_A_pool', probability_upper_decimal='0',
                      approximate_log2_for_display_only=None, deterministic=True)
        per_range = Q(0)
    elif stash_slots <= CAPACITY:
        # R never exceeds its physical cap, which fits one page.
        ranges = dict(name='A_only_top_finish_ranges', probability_upper_decimal='0',
                      approximate_log2_for_display_only=None, deterministic=True,
                      retained_carry_slots=stash_slots, range_capacity=CAPACITY)
        per_range = Q(0)
    else:
        homes = 1 << row['index_bits']
        per_range = Q(positive_excess_bound(homes, CAPACITY))
        with localcontext(UP):
            total = min(1, upper_fraction(per_range*(1 << row['range_bits'])))
        ranges = describe('A_only_top_finish_ranges', total, deterministic=False,
            coarse_ranges=1 << row['range_bits'], homes_per_range=homes,
            per_range_upper=str(per_range), range_capacity=CAPACITY, pages=1,
            retained_carry_slots=stash_slots,
            event='max_r sum_{v in range r} (Y^A_v - 64)_+ > 64',
            witness='The retained carry is exactly A\'s complete-home excess; pool dedup '
                    'and unshadowed drops only delete.')
    capacity = CAPACITY*min(row['stash_buckets'], row['tier_buckets'])
    packing_value = positive_excess_bound(row['out_buckets'], capacity)
    packing = describe('top_finish_merge_and_tier', packing_value, capacity_slots=capacity,
                       complete_population_upper=32*row['out_buckets'])
    per_job = min(Q(1), Q(ranges['probability_upper_decimal']) + Q(packing_value))
    lifetime = min(Q(1), exposures*per_job)
    return dict(shape=row, exposures=exposures, ranges=ranges,
        direct_B_pages=dict(pages=row['direct_buckets'], probability_upper_decimal='0',
            reason='B\'s carry tier is offered directly to every destination; no range '
                   'is materialized or capacity-tested, and its capacity is charged at its producer.'),
        packing=packing,
        lifetime=describe('top_finish_total', upper_fraction(lifetime)),
        meets_2_minus_64=exposures*per_job < Q(1, 1 << 64))


GATE_KEYS = ('branching', 'levels', 'top_digit', 'prefix_flushes', 'stash_buckets',
             'dense_prefixes', 'level_fanouts')


def evaluate_configuration(name, config, exe):
    rows = probe(config, exe)
    row, = [r for r in rows if r['kind'] == 'top_finish']
    level, = [r for r in rows if r['kind'] == 'level' and r['level'] == row['level']]
    return dict(ladder=name, configuration_gate={key: config[key] for key in GATE_KEYS},
        case=evaluate(row, config['horizon_accesses']//level['carry_positions']+1))


def main():
    with tempfile.TemporaryDirectory(prefix='top-finish-evaluation-') as tmp:
        exe, sources = compile_probe(tmp)
        sections = [evaluate_configuration(name, normalize(config), exe)
                    for name, config in SELECTED.items()]
    for name in ('evaluate_top_finish.py', 'certify_tier_router.py', 'certify_oram.py',
                 'check_configuration.py'):
        sources[str((HERE/name).relative_to(ROOT))] = hashlib.sha256((HERE/name).read_bytes()).hexdigest()
    uniform, *others = sections
    artifact = dict(scope=__doc__, **uniform, additional_configurations=others,
        source_sha256=provenance(sources), complete_configuration_certified=False,
        assumptions=['Binary top, fixed logical A set at most 32T under the current top map (p_* = 1/T).',
                     'The retained carry is exactly A\'s complete-home excess after A-only preparation; pool dedup and unshadowed drops only delete.',
                     'Public one-page DFS leaves at the finish range plan; DFS containment reduces every distributor capacity test to the coarse-range event.',
                     'B\'s carry tier is offered directly (no range event); its tier capacity is charged at its producer.',
                     'Top-resolution theorem bounds merge stash and tier by one live-set excess at the smaller capacity.',
                     'Each section applies only under its configuration gate and at its exact native top-finish shape.'],
        conclusion='Evaluates a conservative upper bound, not a lower bound on actual failure probability.')
    (HERE/'top_finish_evaluation.json').write_text(json.dumps(artifact, indent=2)+'\n')
    for section in sections:
        case = section['case']
        print(section['ladder'], 'ranges', case['ranges']['approximate_log2_for_display_only'],
              'packing', case['packing']['approximate_log2_for_display_only'],
              'lifetime', case['lifetime']['approximate_log2_for_display_only'])


if __name__ == '__main__':
    main()
