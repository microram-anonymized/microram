#!/usr/bin/env python3
"""Generate compact Lean family parameters and fresh native structural fixtures.

Only public geometry and class clocks are copied. The native shape probe
allocates no record tables; no probability certificate is generated here.
--check reruns every probe and compares both artifacts, including provenance.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

import bound_table as bt
import check_configuration as cc
import configuration_family as family
from lean_configuration_inventory import direct_shape, sep_shape

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
OUTPUT = HERE/'configuration_family_structure.json'
LEAN = ROOT/'lean/RebuildBound/Spec/ConfigurationFamilyData.lean'
FORMAT = 'configuration-family-structure/1'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def extract_member(member, registry, rows, initialization):
    """Link a fresh native result to exactly the inventoried member and jobs."""
    config = member['configuration']
    fixed = family.space.FIXED | dict(top_digit=8, tier_buckets=0, **cc.CERTIFIED_ROUTING)
    if any(config[k] != v for k, v in fixed.items()):
        raise ValueError('Configuration is outside the fixed structural family')
    metadata = [r for r in rows if r['kind'] not in
                ('ordinary', 'top_prepare', 'top_finish')]
    if metadata != member['native_metadata']:
        raise ValueError('Native metadata differs from the family manifest')
    levels = [r for r in rows if r['kind'] == 'level']
    seeds = [r for r in rows if r['kind'] == 'ordinal_seed']
    indices = list(range(1, config['levels']+1))
    if [r['level'] for r in levels] != indices or [r['level'] for r in seeds] != indices:
        raise ValueError('Missing, duplicate or reordered native level')
    if any(r['carry_positions'] != 32*r['carry_buckets'] for r in levels):
        raise ValueError('Native load differs from the structural family')
    fanouts = config['level_fanouts'] or [config['branching']]*(config['levels']-1)
    if [r['fanout'] for r in seeds] != fanouts + [config['top_digit']]:
        raise ValueError('Native fanouts differ from the configuration')
    name = (f'L{config["levels"]}_r{config["prefix_flushes"]}_D{config["top_digit"]}_'
            + '.'.join(map(str, fanouts)))
    if name != member['name']:
        raise ValueError('Member name differs from its public parameters')
    clocks = []
    for level, seed in zip(levels[:-1], seeds[:-1]):
        for digit in range(1, seed['fanout']+1):
            clocks.append(dict(name=f'ordinary_L{level["level"]}_d{digit}',
                exposures=cc.digit_exposures(config['horizon_accesses'],
                    level['carry_positions'], seed['fanout'], digit, seed['seeded_carries'])))
    top_count = config['horizon_accesses']//levels[-1]['carry_positions']+1
    clocks.extend([dict(name='top_prepare', exposures=top_count),
                   dict(name='top_finish', exposures=top_count),
                   dict(name='initialization', exposures=1)])
    counts = {c['name']: c for c in clocks}
    expected_jobs = family.jobs_for(rows, counts)
    if member['jobs'] != expected_jobs:
        raise ValueError('Native jobs, keys or exposures differ from the family manifest')
    for job in expected_jobs:
        entry = registry[job['key_id']]
        if bt.key_id(entry['key']) != job['key_id']:
            raise ValueError('Mismatched certificate key')
        if job['clock'] == 'initialization' and entry['native_initialization'] != initialization:
            raise ValueError('Native initialization differs from the family manifest')
    geometry, = [r for r in metadata if r['kind'] == 'geometry']
    if geometry['capacity_entries'] != member['capacity_entries']:
        raise ValueError('Native capacity differs from the family manifest')
    direct = [direct_shape(r) for r in rows if r['kind'] == 'ordinary' and r['level'] == 1]
    sep = [dict(level=r['level'], digit=r['digit'], **sep_shape(r))
           for r in rows if r['kind'] == 'ordinary' and r['level'] > 1]
    finish, = [r for r in rows if r['kind'] == 'top_finish']
    prep_row, = [r for r in rows if r['kind'] == 'top_prepare']
    top = dict(C=64, k=finish['carry_bits'], e=finish['block_bits']-finish['carry_bits'],
               rho=finish['range_bits'], I=finish['index_bits'], dfs=finish['dfs'],
               r_pages=finish['stash_buckets'], b_pages=finish['carry_tier_buckets'],
               merge_pages=finish['merge_stash_buckets'], tier_pages=finish['tier_buckets'])
    init = {k: v for k, v in initialization.items() if k != 'kind'}
    # The preparation row's older_tier_buckets is zero: the top source is
    # represented in its pool instead. Recover that source's actual tier from
    # the pool accounting, rather than copying initialization's fields.
    routed_pool = prep_row['pool_buckets'] - prep_row['direct_buckets']
    route_pages = (prep_row['block_bits']-1)*prep_row['stash_buckets']
    if routed_pool < route_pages or prep_row['direct_buckets'] != 0:
        raise ValueError('Unsupported native preparation pool layout')
    prep = dict(C=prep_row['scatter_per_bucket'], k=prep_row['block_bits'],
                stash_pages=prep_row['stash_buckets'],
                a_tier_pages=routed_pool-route_pages, drain_pages=prep_row['stash_buckets'],
                range_bits=prep_row['range_bits'], I=prep_row['index_bits'], dfs=prep_row['dfs'])
    return dict(name=name, capacity_entries=member['capacity_entries'],
        r0=config['prefix_flushes'], level_fanouts=fanouts,
        carry_buckets=[r['carry_buckets'] for r in levels],
        level_tier_buckets=[r['tier_buckets'] for r in levels],
        stash_buckets=[r['stash_buckets'] for r in levels],
        seeded_carries=[r['seeded_carries'] for r in seeds],
        top_digit=config['top_digit'], horizon_accesses=config['horizon_accesses'], load=32,
        clocks=clocks, shapes=dict(direct=direct, sep=sep, top=top, prep=prep, init=init))


def lean_source(members):
    lines = ['import RebuildBound.Spec.ConfigurationFamilyGeometry', '',
             '/-! Generated by code/configuration_family_structure.py. Public parameters only.',
             'The structural proofs and native field comparison are separate consumers. -/', '',
             'namespace RebuildBound.Spec.ConfigurationFamily', '', 'def members : List Member := [']
    for index, member in enumerate(members):
        values = [json.dumps(member['name']), str(member['r0']),
                  str(member['level_fanouts']), str(member['level_tier_buckets']),
                  str(member['stash_buckets'])]
        lines.append('  ⟨' + ', '.join(values) + '⟩' + (',' if index+1 < len(members) else ''))
    return '\n'.join(lines + [']', '', 'end RebuildBound.Spec.ConfigurationFamily', ''])


def validate_members(manifest):
    names = [m['name'] for m in manifest['members']]
    expected = [n for c in manifest['capacities'] for n in c['candidate_names']]
    if len(names) != 94 or len(set(names)) != len(names) or Counter(names) != Counter(expected):
        raise ValueError('Missing or duplicate family member')
    if {m['capacity_entries'] for m in manifest['members']} != {1 << k for k in family.EXPONENTS}:
        raise ValueError('Incomplete capacity domain')


def generate():
    manifest = json.loads(family.OUTPUT.read_text())
    validate_members(manifest)
    exe, hashes = cc.compile_probe(None)
    members = []
    for member in manifest['members']:
        rows, initialization = family.native_rows(exe, member['configuration'])
        members.append(extract_member(member, manifest['jobs'], rows, initialization))
    lean = lean_source(members)
    paths = [Path(__file__), family.OUTPUT, HERE/'configuration_family.py',
             HERE/'lean_configuration_inventory.py', HERE/'check_configuration.py',
             HERE/'bound_table.py', HERE/'probe_build.py']
    paths += [LEAN.parent/'ConfigurationFamilyGeometry.lean']
    paths += [ROOT/'lean/spec_tests'/name for name in
              ('ConfigurationFamily.lean', 'ConfigurationFamilyNative.lean')]
    for path in paths:
        hashes[path.relative_to(ROOT).as_posix()] = sha(path)
    artifact = dict(format=FORMAT, members=members,
        source_sha256=dict(sorted(hashes.items())),
        generated_sha256={LEAN.relative_to(ROOT).as_posix():
                          hashlib.sha256(lean.encode()).hexdigest()})
    return artifact, lean


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    artifact, lean = generate()
    if args.check:
        if json.loads(OUTPUT.read_text()) != artifact or LEAN.read_text() != lean:
            raise SystemExit('Family structural fixture differs; regenerate after reviewing changes')
    else:
        OUTPUT.write_text(json.dumps(artifact, indent=2)+'\n')
        LEAN.write_text(lean)
    print(f'{"Checked" if args.check else "Wrote"} {len(artifact["members"])} native family shapes '
          'and compact Lean parameters')


if __name__ == '__main__':
    main()
