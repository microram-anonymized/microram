#!/usr/bin/env python3
"""Parameterized conditional bounds for binary top preparation/initialization.

One distinct A-only population, before B is consumed. Route-stage raw arrivals
have a categorical Poisson comparison; packing uses complete final-home
excess. Final ranges retain the deferred-bit/shadow assumptions. One-page DFS
transfers this same event to every distributor node by deterministic containment.
Production butterfly intermediate ranges and top finish are excluded.
"""
from decimal import localcontext
from fractions import Fraction
from functools import lru_cache
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile

from certify_oram import UP, ZERO, describe, upper_fraction
from certify_sorted_range import mixed_stoploss, tree_at_depth
from certify_tier_router import positive_excess_bound
from loss_tree import K, LAM, SCALE, thinned_weights, truncation_error
from source_scope import provenance, scoped

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SHAPE_KEYS = ('carry_bits', 'block_bits', 'radix', 'out_buckets', 'main_bits',
              'pool_buckets', 'stash_buckets', 'tier_buckets', 'dense_bits',
              'range_bits', 'index_bits', 'range_buckets', 'groups', 'scatter_per_bucket')


def signature(row, initialization):
    return tuple(row[k] for k in SHAPE_KEYS)+(initialization,)


def validate_binary(row):
    bits = row['main_bits']
    if (row['kind'] != 'top_prepare' or row['radix'] != 1 or row['dense_bits'] != 0
            or not 2 <= bits < 64 or row['block_bits'] != bits
            or row['out_buckets'] != 1 << bits
            or row['stash_buckets'] < 1 or row['tier_buckets'] < 1
            or row['pool_buckets'] != (bits-1)*row['stash_buckets']+row['tier_buckets']):
        raise ValueError('Outside binary A-only top preparation domain')
    # Stage/packing thresholds use the adaptive complete-excess series.
    # The fixed-K loss tree tests only the 64-slot final range; stash/tier
    # widths enter its untruncated early binomial population, not its cutoff.


@lru_cache(maxsize=None)
def sorted_range_bound(bits, index, stash_slots, tier_slots, initialization):
    """Final-only A range bound: early binomial plus late shadow roots.

    Last main stage `bits` is drain-only. Stages <=index and the old tier
    form the deferred early population; stages index+1..bits-1 are late.
    One top bit remains to thin the late losses, hence 2**(index+1) roots.
    """
    depth = bits-index-1
    if not 0 <= index < bits-1 or min(stash_slots, tier_slots) < 1:
        raise ValueError('Sorted top shadow comparison requires at least one late stage')
    patterns, groups = 1 << (bits-index), 1 << (index+1)
    early = index*stash_slots+(0 if initialization else tier_slots)
    weights = thinned_weights(tree_at_depth(depth), 1)
    w = [ZERO]+[upper_fraction(Fraction(weights[e], SCALE)) for e in range(1, K+1)]
    with localcontext(UP):
        parts = mixed_stoploss(w, groups, early, Fraction(1, patterns), 64)
        error = truncation_error(depth, groups, 1)
        total = patterns*(parts['truncated_process_stoploss_upper']+error)
    return describe('sorted_top_final_ranges', total,
        tree_depth=depth, remaining_pattern_bits=1, groups=groups,
        patterns=patterns, early_population_cap=early,
        early_probability_exact=str(Fraction(1, patterns)),
        tree_truncation_error_per_column=str(error),
        **{key: str(value) for key, value in parts.items()})


def evaluate_shape(row, initialization=False):
    validate_binary(row)
    bits, homes = row['main_bits'], row['out_buckets']
    stash_slots = 64*row['stash_buckets']
    drain_slots = 64*(row['tier_buckets'] if initialization else row['stash_buckets'])
    # No success conditioning: a hypothetical first failing append at stage b
    # is dominated by that stage's raw categorical-arrival excess.
    per_stage = positive_excess_bound(homes, stash_slots)
    stage_count = bits-int(initialization)  # Initial scatter <=32: first stage cannot shed.
    with localcontext(UP):
        stage_total = stage_count*per_stage
    packing = positive_excess_bound(homes, drain_slots)
    result = dict(shape={k: row[k] for k in SHAPE_KEYS}, initialization=initialization,
        stages=describe('binary_top_route_stashes', stage_total,
            slots=stash_slots, first_potentially_shedding_stage=2 if initialization else 1,
            last_stage=bits, stage_count=stage_count, per_stage_upper_decimal=str(per_stage),
            final_stage_drain_only=True),
        packing=describe('initial_tier' if initialization else 'preparation_carry', packing,
            slots=drain_slots, complete_population_upper=32*homes,
            witness='Every packing prefix is bounded by sum_v (X_v-64)+ for one distinct complete A population.'),
        sorted_ranges=None)
    if (row['groups'] == 1 and row['scatter_per_bucket'] == 8
            and row['range_bits'] >= 2 and row['range_bits'] <= 20
            and row['index_bits']+row['range_bits'] == bits
            and row['range_buckets'] == 1 << row['range_bits']):
        result['sorted_ranges'] = sorted_range_bound(bits, row['index_bits'],
            stash_slots, 64*row['tier_buckets'], initialization)
    return result


def native_checks():
    with tempfile.TemporaryDirectory(prefix='top-preparation-') as tmp:
        exe, deps = Path(tmp)/'probe', Path(tmp)/'probe.d'
        subprocess.run([*shlex.split(os.environ.get('CXX', 'g++')), '-O2',
            '-std=c++17', '-march=native', '-I.', '-pthread', '-MMD', '-MF', str(deps),
            str(HERE/'top_preparation_probe.cpp'), '-o', str(exe)], cwd=ROOT, check=True)
        rows = [json.loads(line) for line in subprocess.check_output([str(exe)], text=True).splitlines()]
        names = shlex.split(deps.read_text().replace('\\\n', ' ').split(':', 1)[1])
        hashes = {str((ROOT/name).resolve().relative_to(ROOT)):
                  hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in names}
    if len(rows) != 41 or not all(r['passed'] for r in rows):
        raise ValueError('Missing native top preparation boundary/scatter checks')
    return rows, hashes


def main():
    # Imported only by the artifact driver to avoid a numerical-kernel/checker
    # cycle. The checker itself consumes this artifact, never recomputes trees.
    from audit_ordinary_ranges import PLAN_KEYS, expected_plan
    from check_configuration import compile_probe, domain_configs, normalize, probe
    domain = json.loads((HERE/'configuration_domain.json').read_text())
    shapes = {}
    dfs_shapes = []
    with tempfile.TemporaryDirectory(prefix='top-geometry-') as tmp:
        exe, hashes = compile_probe(tmp)
        for config in domain_configs(domain):
            for row in probe(normalize(config), exe):
                if row['kind'] != 'top_prepare':
                    continue
                # The final-range theorem is stated on the production plan's
                # partition of this pool (the independent integer model of
                # PlanResidualRange); the one-page DFS keeps its widths.
                partition = row | dict(zip(PLAN_KEYS, expected_plan(row['pool_buckets'], row['main_bits'])))
                for initialization in (False, True):
                    shapes[signature(partition, initialization)] = evaluate_shape(partition, initialization)
                if row not in dfs_shapes:
                    if not (row['dfs'] and row['groups'] == 1
                            and row['scatter_per_bucket'] == 64
                            and row['range_buckets'] == 1 << row['range_bits']
                            and (row['range_bits'], row['index_bits']) ==
                                (partition['range_bits'], partition['index_bits'])):
                        raise ValueError('Declared top DFS domain does not use one-page leaves '
                                         'at the production widths')
                    dfs_shapes.append(row)
    checks, native_hashes = native_checks()
    hashes.update(native_hashes)
    for name in ('certify_top_preparation.py', 'test_top_preparation.py', 'certify_tier_router.py',
                 'certify_oram.py', 'certify_sorted_range.py', 'loss_tree.py',
                 'check_configuration.py', 'test_sorted_range.py'):
        hashes[str((HERE/name).relative_to(ROOT))] = hashlib.sha256((HERE/name).read_bytes()).hexdigest()
    for name in ('cpu_byteslice_level_arena_top_test.cpp',
                 'cpu_byteslice_level_arena_init_test.cpp', 'cpu_byteslice_dfs_residual_test.cpp'):
        path = ROOT/'tests/oram'/name
        hashes[str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
    cases = list(shapes.values())
    depths = {c['sorted_ranges']['tree_depth'] for c in cases if c['sorted_ranges']}
    result = dict(scope=__doc__, cases=cases, native_checks=checks,
        dfs_shapes=dfs_shapes,
        dfs_transfer=dict(pages=1, capacity_slots=64,
            witness='Any DFS node overflow implies a swept final range exceeds 64; charge once.',
            main_route_and_packing_separate=True, ordinary_pages_ignored=True),
        capacity=64, categorical_comparison_mean_exact='32', shadow_comparison_mean_exact=str(LAM),
        assumptions=[
            'One distinct tombstone-free complete A population of at most 32T keys, independent of its ideal routing families; this is not the later A/B union.',
            'For preparation, old binary homes are independent uniform choices on T; main membership may depend on old words but each retained key remains at its old home. Old and new families are independent.',
            'For initialization, the public source scatter has at most 32 records per bucket and is independent of the new ideal words; old tier is empty.',
            'Current words of distinct keys are independent; no conditioning on earlier capacity success. Deleted records only reduce the raw route witness.',
            'No sheds return to main until the final fused stage. All no-dedup sources partition A; the range distributor must succeed and preserve that partition before the final offers and drains.',
            'Final ranges (sorted or DFS) additionally use the report\'s independent-key ideal-arrival reset/shadow comparison and disjoint-key deferred-bit selection; early membership ignores the remaining high bits.',
            'Native geometry/kernel checks do not prove integrated family histories, source population bounds, or cryptographic/equality assumptions.',
        ],
        exclusions=['No production-butterfly intermediate range certificate and no top-finish B-source or tombstone-sweep certificate.',
                    'No integrated-history proof or complete lifetime capacity claim.'],
        input_sha256={'configuration_domain.json': hashlib.sha256((HERE/'configuration_domain.json').read_bytes()).hexdigest()},
        source_sha256=provenance(hashes),
        tree_cache_sha256={f'tree_{d}.json': hashlib.sha256((HERE/f'tree_{d}.json').read_bytes()).hexdigest() for d in sorted(depths)})
    (HERE/'top_preparation_certificates.json').write_text(json.dumps(result, indent=2)+'\n')
    print('Wrote', len(cases), 'conditional top preparation/init shapes;', len(checks), 'native checks')
    for c in cases:
        if c['shape']['out_buckets'] == 1 << 22:
            print('init' if c['initialization'] else 'prepare',
                  {k: v['approximate_log2_for_display_only'] for k, v in c.items()
                   if k in ('stages', 'packing', 'sorted_ranges') and v})


if __name__ == '__main__':
    main()
