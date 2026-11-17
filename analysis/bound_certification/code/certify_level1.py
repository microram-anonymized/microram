#!/usr/bin/env python3
"""Conditional dense-direct L1: producer excess, completed A, output excess.

Uses fixed unfiltered logical populations and never conditions a tail law on
producer success. A and B share the current family; no independent carry
selection law is imported. This covers the native direct level-one path.
"""
from decimal import localcontext
from fractions import Fraction as Q
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import tempfile
from audit_preparation_contract import home_mass_bound
from certify_completed_a import evaluate as range_bound
from certify_oram import UP, describe, upper_fraction
from certify_separated_sources import storage_bounds, old_law
from certify_tier_router import positive_excess_bound
from check_configuration import ROOT, SELECTED, compile_probe, digit_exposures, normalize, probe
from loss_tree import initial, next_tree
from source_scope import provenance
HERE = Path(__file__).resolve().parent
BACKEND = 'dense-direct-v1'

@lru_cache(maxsize=None)
def tree(depth):
    f = initial()
    for _ in range(1, depth):
        f = next_tree(f)
    return f

def sparse_shape(row):
    """Reuse A routing storage formulas under the separated public shape.

    The level label selects that adapter, and dense_bits is legacy carry-width
    metadata, not an executed dense routing stage. Only A stage bounds are
    reused; no independent-current-B selection law or sparse packing bound is
    imported. The direct producer and final shared-family union are separate.
    """
    return row | dict(level=2,dense_bits=0,merge_stash_buckets=row['stash_buckets'])

def check_shape(row):
    k,d,b,r = (row[x] for x in ('carry_bits','digit','block_bits','radix'))
    if not (row.get('dense_direct') is True and row['kind']=='ordinary' and row['level']==1
            and 1 <= d <= 8 and 2 <= k == row['dense_bits'] <= 6
            and d*(1 << k)==r*(1 << b)==row['out_buckets']
            and row['stash_buckets']>0 and row['tier_buckets']>0
            and row['carry_tier_buckets']==1
            and row['merge_stash_buckets']>=row['tier_buckets']):
        raise ValueError('Outside dense-direct L1 contract')
    if d==1:
        if row['pool_buckets'] or row['direct_buckets'] or row['separated_sources'] or row['dfs']:
            raise ValueError('Digit one must have no finish pass')
    else:
        from certify_separated_sources import check_shape as check_sparse
        check_sparse(sparse_shape(row))

def evaluate(row):
    check_shape(row)
    d,k = row['digit'],row['carry_bits']
    def zero(name):
        return dict(name=name, probability_upper_decimal='0',
                    approximate_log2_for_display_only=None)
    # Digit one drains into the full output tier; no narrower producer event.
    if d > 1:
        dense = describe(
            'direct_B_producer_excess', positive_excess_bound(1 << k, 64),
            capacity_slots=64, logical_population_upper=32 * (1 << k),
            same_current_family=True, backend=BACKEND)
    else:
        dense = zero('no_separate_producer')
    if d>1:
        stages,_ = storage_bounds(sparse_shape(row))
        i=row['index_bits']
        ranges=(range_bound(tree(row['block_bits']-i),k=k,digit=d,index_bits=i,
                    early=64*(row['older_tier_buckets']+i*row['stash_buckets']),
                    density=Q(old_law(row)['joint_density_upper_bound']))
                if row['dfs'] else zero('direct_A_pool_no_range_test'))
        roots=[dict(depth=row['block_bits']-i)] if row['dfs'] else []
    else:
        stages,ranges,roots=zero('no_A_route'),zero('no_A_range'),[]
    law=home_mass_bound(row['block_bits'],row['radix'],32*row['out_buckets'])
    with localcontext(UP):
        packing=describe('merge_shed_and_output_excess',min(1,positive_excess_bound(
                    row['out_buckets'],64*row['tier_buckets'])*upper_fraction(Q(law['joint_density_upper_bound']))),
                    capacity_slots=64*row['tier_buckets'],current_union_map_law=law,
                    merge_stash_capacity_slots=64*row['merge_stash_buckets'],charged_once=True,
                    witness='Saturated output; distinct B-main sheds and obsolete A leftovers inject into final excess')
    return dict(shape=row,backend=BACKEND,dense=dense,stages=stages,ranges=ranges,
                range_sources=[dict(roots=roots)] if roots else [],packing=packing,
                final_shed_and_publication_charged_once=d>1)

def validate_inventory(rows, fanout=8):
    """Check one planner inventory's domains and aggregate source capacities.

    This is not an independent writer extraction. The deterministic inventory
    probe enumerates actual tasks and failure sites separately.
    """
    if len(rows) != fanout or {r['digit'] for r in rows} != set(range(1, fanout + 1)):
        raise ValueError('Incomplete direct L1 inventory')
    for row in rows:
        check_shape(row)
        sources = expected_sources(row)
        if sum(s['pages'] for s in sources if not s['drain_only']) != row['pool_buckets']:
            raise ValueError('Direct L1 source capacities disagree with planner pool')
        if sum(s['pages'] for s in sources if s['tier_class']) != row['direct_buckets']:
            raise ValueError('Direct L1 source capacities disagree with direct tier')
        if any(s['pages'] <= 0 or s['index'] < 0 for s in sources):
            raise ValueError('Invalid direct L1 source domain')

def expected_sources(row):
    """Manual source recipe; validate aggregate sizes against planner rows."""
    check_shape(row)
    if row['digit'] == 1:
        return []
    b, r = (row['block_bits'], row['radix'])
    result = [dict(storage='older_shed', index=b + 2, pages=row['merge_stash_buckets'], rank=0, tier_class=False, drain_only=True)]
    for bit in range(b):
        result.append(dict(storage='older_shed', index=bit, pages=row['stash_buckets'], rank=2, tier_class=False, drain_only=False))
    if r > 1:
        result.append(dict(storage='older_shed', index=b + 1, pages=row['stash_buckets'], rank=2, tier_class=False, drain_only=False))
    result.extend([dict(storage='older_tier', index=0, pages=row['older_tier_buckets'], rank=2, tier_class=False, drain_only=False), dict(storage='carry_tier', index=0, pages=1, rank=0, tier_class=True, drain_only=False)])
    return result
GATE_KEYS=('branching','levels','prefix_flushes','dense_prefixes','separated_sources','level_fanouts')
def certify_configuration(name, config, exe):
    inventory = probe(config, exe)
    rows = [r for r in inventory if r['kind'] == 'ordinary' and r['level'] == 1]
    seed = next((r for r in inventory if r['kind'] == 'ordinal_seed' and r['level'] == 1))
    validate_inventory(rows, seed['fanout'])
    level = next((r for r in inventory if r['kind'] == 'level' and r['level'] == 1))
    cases, total = ([], Q(0))
    for row in rows:
        result = evaluate(row)
        count = digit_exposures(config['horizon_accesses'], level['carry_positions'], seed['fanout'], row['digit'], seed['seeded_carries'])
        bound = sum((Q(result[k]['probability_upper_decimal']) for k in ('dense', 'stages', 'ranges', 'packing')), Q(0))
        result.update(exposures=count, per_job_upper_exact=str(bound))
        total += count * bound
        cases.append(result)
        print(name, row['digit'], {k: result[k]['approximate_log2_for_display_only'] for k in ('dense', 'stages', 'ranges', 'packing')}, flush=True)
    return dict(ladder=name, configuration=config, backend=BACKEND, level_one_fanout=seed['fanout'], cases=cases, native_inventory=rows, lifetime_subtotal_exact=str(total), lifetime_subtotal=describe('level_one_complete', upper_fraction(total)), configuration_gate={k: config[k] for k in GATE_KEYS})
def main():
    with tempfile.TemporaryDirectory() as tmp:
        exe, sources = compile_probe(tmp)
        sections = [certify_configuration(n, normalize(c), exe) for n, c in SELECTED.items()]
    for name in ('certify_level1.py', 'test_level1.py', 'check_configuration.py', 'certify_separated_sources.py', 'certify_completed_a.py', 'loss_tree.py', 'certify_oram.py', 'certify_preparation.py', 'certify_tier_router.py', 'certify_sorted_range.py', 'audit_preparation_contract.py', 'gmp_square.cpp'):
        sources[str((HERE / name).relative_to(ROOT))] = hashlib.sha256((HERE / name).read_bytes()).hexdigest()
    depths = {r['depth'] for s in sections for c in s['cases'] for g in c['range_sources'] for r in g['roots']}
    artifact = dict(
        scope=__doc__, **sections[0], additional_configurations=sections[1:],
        source_sha256=provenance(sources),
        tree_cache_sha256={
            f'tree_{d}.json': hashlib.sha256((HERE / f'tree_{d}.json').read_bytes()).hexdigest()
            for d in depths},
        complete_configuration_certified=False,
        assumptions=[
            'Fixed logical B key set independent of current word family; independent uniform distinct-key words; exact-key dedup only reduces the population.',
            'Native source/frontier premises for completed A; independent old/current families, with shared current family between A and B.',
            'First-failure witnesses use unfiltered A and fixed logical union; no tail bound is conditioned on producer success.',
            'Native saturated output and freshness epilogue imply merge sheds and obsolete A drain copies are dominated by final excess.',
            'Native digit exposure schedule including next speculative preparation; no retry or overflow-triggered rehash.',
            'Conditional capacity bound only; cryptographic and wide-key equality errors remain separate.'],
        exclusions=['Unconditional whole-hierarchy certificate, Lean theorem, unlisted geometries/horizons.'])
    (HERE / 'level1_certificates.json').write_text(json.dumps(artifact, indent=2) + '\n')
if __name__ == '__main__':
    main()
