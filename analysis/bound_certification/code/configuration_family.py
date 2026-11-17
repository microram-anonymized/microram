#!/usr/bin/env python3
"""Inventory and recompose the standard D=8 planner family, without record tables.

This is native/Python evidence for the Lean extension, not a family theorem.
The existing exact adapters compute missing job keys; every candidate gets a
fresh applicability/inventory audit. Full job keys are stored once, separately
from exposure counts. --check reruns the probes and rejects any changed field.
"""
import argparse
from collections import Counter
from fractions import Fraction as Q
import json
from pathlib import Path
import subprocess
import tempfile

import audit_deterministic_inventory as adi
import bound_table as bt
import certify_configuration_space as space
import check_configuration as cc
from source_scope import provenance

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
OUTPUT = HERE/'configuration_family.json'
EXPONENTS = range(11, 32)


def candidates_at(exe, exponent):
    capacity = 1 << exponent
    rows = space.enumerate_space(exe, capacity)
    counts = [r for r in rows if r['kind'] == 'planner_count']
    if not counts or any(r['planner_candidates'] != r['enumerated'] for r in counts):
        raise ValueError('Candidate probe disagrees with the planner count')
    candidates = [c for c in space.theorem_candidates(rows, capacity)
                  if c['top_digit'] == 8]
    if not candidates:
        raise ValueError(f'No standard candidates at 2^{exponent}')
    names = {c['name'] for c in candidates}
    defaults = [r for r in rows if r['kind'] == 'planner_default']
    if not defaults or any(space.candidate_name(r) not in names for r in defaults):
        raise ValueError('A default planner choice is absent from the family')
    return candidates, dict(exponent=exponent, candidate_names=sorted(names),
                           planner_counts=counts,
                           defaults=[dict(value_bytes=r['value_bytes'],
                                          name=space.candidate_name(r)) for r in defaults])


def native_rows(exe, config):
    result = subprocess.run([str(exe), *cc.probe_arguments(config), '--init-shape'],
                            check=True, capture_output=True, text=True)
    rows = [json.loads(line) for line in result.stdout.splitlines()]
    init, = [r for r in rows if r['kind'] == 'initialization']
    return [r for r in rows if r['kind'] != 'initialization'], init


def jobs_for(rows, clocks):
    """Retain each occurrence (including duplicate shapes at different levels)."""
    jobs = []
    for row in rows:
        if row['kind'] not in ('ordinary', 'top_prepare', 'top_finish'):
            continue
        clock = (f'ordinary_L{row["level"]}_d{row["digit"]}'
                 if row['kind'] == 'ordinary' else row['kind'])
        for init in ((False, True) if row['kind'] == 'top_prepare' else (False,)):
            name = 'initialization' if init else clock
            key = bt.shape_key(row, init)
            jobs.append(dict(clock=name, level=row['level'], digit=row['digit'],
                             key_id=bt.key_id(key), exposures=clocks[name]['exposures']))
    return jobs


def validate_member(member, registry):
    """Fail closed on omitted rows, wrong keys, changed counts or undercounted sums."""
    rows = member['native_metadata'] + [
        bt.representative_row(registry[j['key_id']]['key'], j['level'])
        for j in member['jobs'] if j['clock'] != 'initialization']
    config = member['configuration']
    # Recompute public clocks independently of the recorded jobs. No probability
    # arithmetic or large tables are needed for these phase checks.
    levels = {r['level']: r for r in rows if r['kind'] == 'level'}
    seeds = {r['level']: r for r in rows if r['kind'] == 'ordinal_seed'}
    expected = set()
    for level in range(1, config['levels']):
        fanout = (config['level_fanouts'][level-1] if config['level_fanouts']
                  else config['branching'])
        if seeds[level]['fanout'] != fanout:
            raise ValueError('Ordinal fanout differs from configuration')
        for digit in range(1, fanout+1):
            if not any(r['kind'] == 'adoption' and r['level'] == level and
                       r['digit'] == digit for r in rows):
                expected.add(f'ordinary_L{level}_d{digit}')
    expected.update(('top_prepare', 'top_finish', 'initialization'))
    if Counter(j['clock'] for j in member['jobs']) != Counter({n: 1 for n in expected}):
        raise ValueError('Missing or duplicate job occurrence')
    total = Q(0)
    initialization = Q(0)
    for job in member['jobs']:
        entry = registry[job['key_id']]
        key = entry['key']
        if bt.key_id(key) != job['key_id']:
            raise ValueError('Mismatched certificate key')
        level = job['level']
        if job['clock'] == 'initialization':
            count = 1
            if key['role'] != 'initialization' or level != config['levels']:
                raise ValueError('Wrong initialization job')
        elif key['kind'] == 'ordinary':
            if job['clock'] != f'ordinary_L{level}_d{job["digit"]}':
                raise ValueError('Ordinary job clock differs from its level/digit')
            if key['digit'] != job['digit'] or key['role'] != (
                    'dense_level_one' if level == 1 else 'separated_ordinary'):
                raise ValueError('Wrong ordinary job')
            seed = seeds[level]
            if seed['seeded_carries'] % seed['fanout']:
                raise ValueError('Non-cycle initialization seed')
            count = cc.digit_exposures(config['horizon_accesses'],
                levels[level]['carry_positions'], seed['fanout'], job['digit'])
        else:
            if key['role'] != job['clock'] or level != config['levels']:
                raise ValueError('Wrong top job')
            count = config['horizon_accesses']//levels[level]['carry_positions']+1
        if job['exposures'] != count:
            raise ValueError('Exposure count differs from the public clock')
        term = count*Q(entry['per_job_upper_exact'])
        total += term
        if job['clock'] == 'initialization':
            initialization = term
    ledger = member['ledger']
    if min(1, total) != Q(ledger['initialized_upper_exact']):
        raise ValueError('Initialized ledger does not equal its exposure sum')
    if min(1, total-initialization) != Q(ledger['empty_upper_exact']):
        raise ValueError('Empty ledger does not remove exactly initialization')


def generate(check=False):
    import configuration_family_lean as lean
    table = bt.BoundTable()
    if table.errors:
        raise ValueError('Stale bound table; regenerate its producers: ' + '; '.join(table.errors))
    prior_validation = lean.validate()
    with tempfile.TemporaryDirectory(prefix='configuration-family-') as tmp:
        exes, sources = space.compile_all(tmp)
        sites = adi.census(adi.closure(tmp))
        census = dict(sites=sites, gaps=list(adi.classify_census(sites)[-1]))
        found, candidates, capacity_rows = {}, [], []
        for exponent in EXPONENTS:
            selected, capacity = candidates_at(exes['space'], exponent)
            capacity_rows.append(capacity)
            for c in selected:
                config = space.candidate_config(c)
                rows, init = native_rows(exes['configuration'], config)
                candidates.append((c, config, rows, init))
                for kid, occurrence in bt.occurrences_of(config, rows,
                        dict(configuration=c['name'])).items():
                    if kid in found and found[kid][0] != occurrence[0]:
                        raise ValueError('Job key digest collision')
                    found.setdefault(kid, occurrence)
        absent = set(found)-set(table.entries)
        if check and absent:
            raise ValueError(f'{len(absent)} missing job keys; regenerate the family first')
        if absent:
            table.ensure(found)
            table.save()
        if any(table.lookup(key) is None for key, _ in found.values()):
            raise ValueError('Unresolved numerical job keys')
        registry = {kid: dict(key=key,
                             per_job_upper_exact=table.lookup(key)['per_job_upper_exact'])
                    for kid, (key, _) in sorted(found.items())}
        members, native_members = [], []
        import configuration_family_structure as structure
        for c, config, rows, init in candidates:
            result = space.certify_candidate(c, exes, table, census)
            if rows != result['native_inventory']:
                raise ValueError('Native shape probe changed during generation')
            if result['missing_keys'] or result['coverage_gaps'] or not result['inventory']['complete']:
                raise ValueError(f'Incomplete candidate audit: {c["name"]}')
            jobs = jobs_for(rows, result['clocks'])
            for job in jobs:
                if Q(registry[job['key_id']]['per_job_upper_exact']) != Q(
                        result['clocks'][job['clock']]['per_exposure_upper_exact']):
                    raise ValueError('Table and ledger per-job bounds disagree')
                if job['clock'] == 'initialization':
                    entry = registry[job['key_id']]
                    if entry.setdefault('native_initialization', init) != init:
                        raise ValueError('One initialization key has two native shapes')
            total = sum((j['exposures']*Q(registry[j['key_id']]['per_job_upper_exact'])
                         for j in jobs), Q(0))
            init_bound = Q(result['clocks']['initialization']['per_exposure_upper_exact'])
            member = dict(name=c['name'], capacity_entries=c['capacity_entries'],
                configuration=config, generators=c['generators'],
                native_metadata=[r for r in rows if r['kind'] not in
                                 ('ordinary', 'top_prepare', 'top_finish')],
                jobs=jobs,
                ledger=dict(initialized_upper_exact=result['conditional_lifetime_upper_exact'],
                    empty_upper_exact=str(min(1, total-init_bound)),
                    meets_target=result['meets_target'],
                    margin_bits_display=result['margin_bits_display'],
                    components=result['components'], status=result['status'],
                    unconditional_upper_exact='1'),
                inventory=result['inventory'], level_one_native=result['level_one_native'],
                families=result['families'])
            validate_member(member, registry)
            members.append(member)
            native_members.append(structure.extract_member(member, registry, rows, init))
            print(f'{c["name"]}: margin {result["margin_bits_display"]:.3f} bits; '
                  f'{len(jobs)} jobs; inventory complete', flush=True)
        lean_validation = lean.validate_family(
            dict(format=structure.FORMAT, members=native_members), registry)
        lean_validation['prior_shape_validation'] = prior_validation
        for entry in registry.values():
            entry['lean'] = lean.classify(entry['key'])
    paths = [Path(__file__), HERE/'certify_configuration_space.py',
             HERE/'audit_deterministic_inventory.py', HERE/'check_configuration.py',
             HERE/'configuration_family_lean.py', *lean.evidence_paths()]
    sources.update({p.resolve().relative_to(ROOT).as_posix(): bt._sha(p) for p in paths})
    sources.update(table.source_sha256)
    # Keep the full probe closure too: the numerical source scope deliberately
    # omits capacity.hpp and byte pricing, but a planner-domain claim cannot.
    strict_sources = dict(sorted(sources.items()))
    return dict(format='configuration-family/1',
        scope=dict(capacity_exponents=list(EXPONENTS), **space.FIXED, top_digit=8,
                   tier_buckets=0, bank_first='kNoClone', starts=['initialized', 'empty'],
                   target_exact=str(space.TARGET),
                   status='native/Python ledger; family membership linked to the separate Lean certificate'),
        summary=dict(candidates=len(members), unique_job_keys=len(registry),
            job_occurrences=sum(len(m['jobs']) for m in members),
            keys_by_role=dict(Counter(e['key']['role'] for e in registry.values())),
            lean_status_counts=dict(Counter(e['lean']['status'] for e in registry.values())),
            all_meet_conditional_target=all(m['ledger']['meets_target'] for m in members),
            tightest=min(members, key=lambda m: m['ledger']['margin_bits_display'])['name']),
        capacities=capacity_rows, members=members, jobs=registry,
        lean_validation=lean_validation,
        bound_table_entries=table.entry_digests(registry),
        source_sha256=provenance(sources), strict_source_sha256=strict_sources)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=OUTPUT)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    artifact = generate(args.check)
    if args.check:
        if json.loads(args.output.read_text()) != artifact:
            raise SystemExit('Family inventory differs; regenerate after reviewing changes')
    else:
        args.output.write_text(json.dumps(artifact, indent=1)+'\n')
    print(('Checked' if args.check else 'Wrote'), args.output.name, artifact['summary'])


if __name__ == '__main__':
    main()
