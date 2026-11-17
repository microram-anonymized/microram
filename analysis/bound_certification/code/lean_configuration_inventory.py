#!/usr/bin/env python3
"""Extract one candidate's shape-only Lean inventory against current headers.

Python probability estimates are evidence, not Lean certificates. The
current native probe allocates no record tables. --check reruns that probe
and compares the entire artifact, including provenance and class coverage.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from check_configuration import compile_probe, probe_arguments
from source_scope import SELF_NAME, scope_current, scoped

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sep_shape(row):
    return dict(C=64, K=row['carry_bits'], e=row['block_bits']-row['carry_bits'],
                r=row['radix'], range_bits=row['range_bits'], I=row['index_bits'],
                stash_pages=row['stash_buckets'], a_tier_pages=row['older_tier_buckets'],
                b_tier_pages=row['carry_tier_buckets'], tier_pages=row['tier_buckets'])


def direct_shape(row):
    d = row['digit']
    ranges = dict(kind='direct')
    if row['dfs']:
        ranges = dict(kind='dfs', index_bits=row['index_bits'], range_bits=row['range_bits'],
                      pool_capacity=64*(row['pool_buckets']-row['direct_buckets']))
    return dict(digit=d, K=row['carry_bits'], output_homes=row['out_buckets'],
                output_capacity=64*row['tier_buckets'],
                a_tier_capacity=64*row['older_tier_buckets'] if d > 1 else 0,
                route_capacity=64*row['stash_buckets'], radix_capacity=64*row['stash_buckets'],
                insertion_capacity=64*row['merge_stash_buckets'],
                copy_capacity=64*row['tier_buckets'], ranges=ranges)


def extract(ledger_path, name):
    ledger = json.loads(ledger_path.read_text())
    candidate, = [c for c in ledger['candidates'] if c['name'] == name]
    exe, hashes = compile_probe(None)
    result = subprocess.run([str(exe), *probe_arguments(candidate['configuration']), '--init-shape'],
                            check=True, capture_output=True, text=True)
    native = [json.loads(line) for line in result.stdout.splitlines()]
    init, = [r for r in native if r['kind'] == 'initialization']
    current = [r for r in native if r['kind'] != 'initialization']
    if current != candidate['native_inventory']:
        raise ValueError('Current native geometry differs from the chosen ledger candidate')
    selected_paths = [HERE/'selected_configuration_check.json',
                      HERE/'selected_configuration_half_fanout_check.json']
    selected_rows = []
    for path in selected_paths:
        selected = json.loads(path.read_text())
        for config in selected['configurations']:
            selected_rows.extend(config['native_inventory'])
    old_sep = [sep_shape(r) for r in selected_rows if r['kind'] == 'ordinary' and r['level'] > 1]
    old_direct = [direct_shape(r) for r in selected_rows if r['kind'] == 'ordinary' and r['level'] == 1]
    direct, sep, obligations = [], [], []
    for row in current:
        if row['kind'] != 'ordinary':
            continue
        level, digit = row['level'], row['digit']
        pass_name = f'ordinary_L{level}_d{digit}'
        if level == 1:
            shape = direct_shape(row)
            direct.append(shape)
            reused = shape in old_direct
        else:
            shape = sep_shape(row)
            sep.append(dict(level=level, digit=digit, **shape))
            reused = shape in old_sep
        obligations.append(dict(name=pass_name, role='direct' if level == 1 else 'separated',
                                exposures=candidate['clocks'][pass_name]['exposures'],
                                numerics='reused' if reused else 'new',
                                heavy_classes=(1 << (64-row['block_bits'])) % row['radix'],
                                light_classes=row['radix'] - (1 << (64-row['block_bits'])) % row['radix']))
    finish, = [r for r in current if r['kind'] == 'top_finish']
    prep_row, = [r for r in current if r['kind'] == 'top_prepare']
    top = dict(C=64, k=finish['carry_bits'], e=finish['block_bits']-finish['carry_bits'],
               rho=finish['range_bits'], I=finish['index_bits'], dfs=finish['dfs'],
               r_pages=finish['stash_buckets'], b_pages=finish['carry_tier_buckets'],
               merge_pages=finish['merge_stash_buckets'], tier_pages=finish['tier_buckets'])
    init = {k: v for k, v in init.items() if k != 'kind'}
    prep = init | dict(drain_pages=prep_row['stash_buckets'])
    assert (prep['k'], prep['range_bits'], prep['I'], prep['dfs']) == (
        prep_row['block_bits'], prep_row['range_bits'], prep_row['index_bits'], prep_row['dfs'])
    for name in ('top_prepare', 'top_finish', 'initialization'):
        obligations.append(dict(name=name, role=name,
                                exposures=candidate['clocks'][name]['exposures'], numerics='new'))
    stale = [p for p, digest in scoped(ledger['source_sha256']).items() if sha(ROOT/p) != digest]
    if not scope_current(ledger['source_sha256']):
        stale.append(SELF_NAME)
    for path in [Path(__file__), HERE/'check_configuration.py', HERE/'probe_build.py',
                 ledger_path, *selected_paths]:
        hashes[str(path.resolve().relative_to(ROOT))] = sha(path)
    fields = ('name', 'configuration', 'level_fanouts', 'carry_buckets', 'stash_buckets',
              'level_tier_buckets', 'top_digit', 'geometry')
    return dict(format='lean-configuration-inventory/1',
                **{k: candidate[k] for k in fields},
                clocks={k: v for k, v in candidate['clocks'].items()
                        if k not in ('integrated_inventory', 'native_applicability')},
                native_inventory=native, shapes=dict(direct=direct, sep=sep, top=top, prep=prep, init=init),
                certificate_inventory=obligations,
                law_parameters=dict(word_bits=64, load=32, ordinary_cutoffs=[256, 256]),
                historical_ledger=dict(source_sha256=ledger['source_sha256'],
                    changed_sources=stale, conditional_bound=candidate['conditional_lifetime_upper_exact'],
                    component_estimates=candidate['components']),
                source_sha256=dict(sorted(hashes.items())))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ledger', type=Path, default=HERE/'configuration_space_2p31.json')
    parser.add_argument('--candidate', default='L8_r8_D8_4.4.8.8.8.8.8')
    parser.add_argument('--output', type=Path, default=HERE/'lean_configuration_2p31.json')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    artifact = extract(args.ledger, args.candidate)
    if args.check:
        if json.loads(args.output.read_text()) != artifact:
            raise SystemExit('Lean configuration inventory differs; regenerate after reviewing changes')
    else:
        args.output.write_text(json.dumps(artifact, indent=2)+'\n')
    rows = artifact['certificate_inventory']
    print(f"{'Checked' if args.check else 'Wrote'} {args.output.name}: {len(rows)} jobs; "
          f"{sum(r['numerics'] == 'reused' for r in rows)} reused, "
          f"{sum(r['numerics'] == 'new' for r in rows)} new numerical obligations")


if __name__ == '__main__':
    main()
