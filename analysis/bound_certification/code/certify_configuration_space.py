#!/usr/bin/env python3
"""Every valid configuration at one capacity, composed from the bound table.

A VALID CONFIGURATION at capacity N (default 2^27 entries) is a geometry the
capacity planner itself prices for a request of N entries -- every feasible
candidate of PlanLevelArenaCapacity's loop over L, r0 in {2,4,8}, binary
D <= B, the half-fanout prefix length a and the bottom fanout b_1, with the
caller's fixed B = 8, s = 1, q = 2, horizon 2^32, automatic tier sizing and
native stash sizing -- whose rounded capacity 32T is exactly N.  Candidates
of larger rounded capacity are configurations of that larger N and are
listed, not certified.  For each configuration this script

  1. runs the native configuration probe and lists its jobs;
  2. checks native applicability: the level-one planner domains and aggregate source capacities
     (configuration_probe.cpp, certify_level1.validate_inventory), the routing-map and
     canonical-family checks at every transition (configuration_space_probe),
     and that every job's key is in bound_table.json;
  3. composes the ledger from the table with check_configuration's own
     builders and exact exposure counts (a missing key is a gap charged one);
  4. runs the deterministic inventory audit's probe and mapping at that
     configuration against that ledger, discharging its inventory line only
     when the audit is complete;
  5. assembles the conditional bound and states whether every configuration
     meets the target.

    python3 certify_configuration_space.py [--capacity N] [--output FILE]
"""
import argparse
from collections import Counter
from fractions import Fraction as Q
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import tempfile

import audit_deterministic_inventory as adi
import bound_table as bt
from source_scope import provenance, scoped
import certify_level1 as cl1
import check_configuration as cc

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PROBE = 'configuration_space_probe.cpp'
CAPACITY = 1 << 27
# The caller's choices (capacity.hpp: B, s and q are the WORKLOAD's, not
# searched) and the stash certificate's horizon.
FIXED = dict(branching=8, stash_buckets=1, dense_prefixes=2, horizon_accesses=1 << 32)
# The online-stash settings certified besides the default:
# each is its own space, one artifact per capacity (`artifact_name`).
SETTINGS = ((1, 2), (2, 2), (4, 2))


def fixed_setting(stash_buckets=FIXED['stash_buckets'], dense_prefixes=FIXED['dense_prefixes']):
    return dict(FIXED, stash_buckets=stash_buckets, dense_prefixes=dense_prefixes)


def artifact_name(exponent, fixed=FIXED):
    """configuration_space_2p{e}.json at the default s and q, otherwise
    configuration_space_s{s}_q{q}_2p{e}.json."""
    s, q = fixed['stash_buckets'], fixed['dense_prefixes']
    tag = '' if (s, q) == (FIXED['stash_buckets'], FIXED['dense_prefixes']) else f's{s}_q{q}_'
    return f'configuration_space_{tag}2p{exponent}.json'
TARGET = Q(1, 1 << 64)


def fixed_floor(fixed=FIXED):
    """LevelArenaMinTopDigit's default: B/2 + 1."""
    return fixed['branching']//2 + 1


def log2(value):
    value = Q(value)
    return None if value == 0 else math.log2(value.numerator) - math.log2(value.denominator)


def enumerate_space(exe, capacity=CAPACITY, fixed=FIXED):
    run = subprocess.run([str(exe), 'candidates', str(capacity), str(fixed['branching']),
                          str(fixed['stash_buckets']), str(fixed['dense_prefixes']),
                          str(fixed['horizon_accesses'])], text=True, capture_output=True)
    if run.returncode:
        raise RuntimeError(run.stderr)
    return [json.loads(line) for line in run.stdout.splitlines()]


def candidate_name(c):
    return (f'L{c["levels"]}_r{c["prefix_flushes"]}_D{c["top_digit"]}_'
            + '.'.join(str(f) for f in c['level_fanouts']))


def theorem_candidates(rows, capacity=CAPACITY):
    """The distinct geometries of exact rounded capacity, each with every
    (ladder, axis) that generates it (a = 1 and b_1 = 4 are one ladder)."""
    result = {}
    for r in rows:
        if r['kind'] != 'candidate' or r['capacity_entries'] != capacity:
            continue
        name = candidate_name(r)
        entry = result.setdefault(name, dict(r, name=name, generators=[]))
        for field in ('levels', 'prefix_flushes', 'top_digit', 'level_fanouts',
                      'tier_buckets', 'level_tier_buckets', 'stash_buckets', 'carry_buckets',
                      'bill_requested'):
            if entry[field] != r[field]:
                raise ValueError(f'One ladder, two geometries: {name}')
        entry['generators'].append(dict(ladder=r['ladder'], axis=r['axis']))
    for entry in result.values():
        entry.pop('ladder'), entry.pop('axis')
    return sorted(result.values(), key=lambda c: (c['levels'], c['prefix_flushes'],
                                                  c['top_digit'], c['level_fanouts']))


def candidate_config(c, fixed=FIXED):
    return cc.normalize(dict(fixed, levels=c['levels'], top_digit=c['top_digit'],
                             prefix_flushes=c['prefix_flushes'], tier_buckets=0,
                             level_fanouts=list(c['level_fanouts'])))


def families(exe, config):
    run = subprocess.run([str(exe), 'families', *cc.probe_arguments(config)], text=True,
                         capture_output=True)
    if run.returncode:
        return dict(passed=False, error=run.stderr.strip())
    return json.loads(run.stdout)


def level_one_native(rows):
    """Validate planner shapes; actual task sites are checked by the audit."""
    ordinary = [r for r in rows if r['kind'] == 'ordinary' and r['level'] == 1]
    seed = next(r for r in rows if r['kind'] == 'ordinal_seed' and r['level'] == 1)
    try:
        cl1.validate_inventory(ordinary, seed['fanout'])
    except ValueError as error:
        return dict(passed=False, error=str(error))
    return dict(passed=True, digits=len(ordinary),
                scope='planner shapes and aggregate source capacities',
                actual_task_sites='checked by deterministic inventory audit')


class CandidateCertificates(bt.TableCertificates):
    """Table lookups for one candidate; level one requires valid planner shapes."""

    def __init__(self, table, level_one_ok):
        super().__init__(table)
        self.level_one_ok = level_one_ok

    def level_one_case(self, config, row):
        return super().level_one_case(config, row) if self.level_one_ok else None


def component_of(name):
    if name.startswith('ordinary_L1_'):
        return 'level_one'
    if name.startswith(('ordinary_', 'adoption_')):
        return 'separated_ordinary'
    if name.startswith('top_prepare') or name == 'initialization':
        return 'top_preparation_and_initialization'
    if name.startswith('top_finish'):
        return 'top_finish'
    return 'other'


def ledger_summary(passes):
    per_pass, components = [], Counter()
    for p in passes:
        known = [Q(o['conditional_upper_exact']) for o in p['obligations']
                 if o['conditional_upper_exact'] is not None]
        missing = sum(o['conditional_upper_exact'] is None for o in p['obligations'])
        value = p['exposures']*min(1, sum(known, Q(0))+missing)
        worst = max(((o['name'], Q(o['conditional_upper_exact'])) for o in p['obligations']
                     if o['conditional_upper_exact'] is not None), key=lambda x: x[1],
                    default=(None, Q(0)))
        per_pass.append((value, p['name'], p['exposures'], worst))
        components[component_of(p['name'])] += value
    per_pass.sort(key=lambda x: -x[0])
    dominant = [dict(pass_name=n, exposures=e, lifetime_exact=str(v),
                     lifetime_log2_display=log2(v), largest_obligation=w[0],
                     largest_obligation_log2_display=log2(w[1]))
                for v, n, e, w in per_pass[:6] if v]
    return dominant, {k: dict(exact=str(v), log2_display=log2(v))
                      for k, v in sorted(components.items())}


def certify_candidate(c, exes, table, census, fixed=FIXED):
    config = candidate_config(c, fixed)
    rows = cc.probe(config, exes['configuration'])
    level_one = level_one_native(rows)
    fam = families(exes['space'], config)
    certs = CandidateCertificates(table, level_one['passed'])
    found = bt.occurrences_of(config, rows, dict(configuration=c['name']))
    # A key absent from the table is a gap charged one; where the adapter's
    # own domain check refused its shape, the refusal names the blocker.
    missing_keys = [dict(key_id=k, role=key['role'], level=where['level'], digit=where['digit'],
                         adapter_refusal=table.refusal(key))
                    for k, (key, where) in found.items() if table.lookup(key) is None]
    passes = cc.native_passes(config, rows, certs)
    inventory_rows = adi.run_probe(exes['inventory'], config)
    section = adi.audit_configuration(c['name'], config, inventory_rows, rows, passes, certs,
                                      census['sites'], census['gaps'])
    if section['deterministic_inventory_complete']:
        line = cc.obligation('remaining_storage_and_partial_jobs', None, '0',
            f'deterministic inventory audit at this configuration (see inventory.{c["name"]})',
            census_sites=section['census_sites'], capacity_sites=len(section['capacity_site_mapping']),
            probe_checks=section['probe']['checks'])
    else:
        line = cc.obligation('remaining_storage_and_partial_jobs', None,
                             reason='Deterministic inventory audit incomplete: '
                                    + '; '.join(section['gaps']))
    passes.append(dict(name='integrated_inventory', clock='integrated_inventory', exposures=1,
                       obligations=[line]))
    native_ok = level_one['passed'] and fam.get('passed') is True
    passes.append(dict(name='native_applicability', clock='native_applicability', exposures=1,
        obligations=[cc.obligation('native_applicability', None, '0' if native_ok else None,
            'level-one writer inventory and map/family checks at this configuration',
            reason='A native applicability check failed')]))
    premises = [
        'Native-source and frontier propositions supply logical histories; imported historical artifacts still require their own applicability audits.',
        'Every imported certificate retains all assumptions recorded in its assumptions field; native geometry does not discharge them.',
        'Empty or directly initialized start; public per-digit ordinal lists include the next speculative job. Arbitrary warm-start producer inventory is outside this checker.',
        'The deterministic inventory classifies non-capacity census sites (public refusals, liveness, unreachable paths) by reviewed per-rule arguments and a lexical occupancy lint, not by a machine proof; scheduler liveness, C++ memory safety beyond the audited extents and allocation failure are outside it.',
    ]
    result = cc.assemble(passes, str(TARGET), premises)
    dominant, components = ledger_summary(passes)
    total = Q(result['conditional_lifetime_upper_exact'])
    return dict(
        name=c['name'], configuration=config, generators=c['generators'],
        levels=c['levels'], prefix_flushes=c['prefix_flushes'], top_digit=c['top_digit'],
        level_fanouts=c['level_fanouts'], carry_buckets=c['carry_buckets'],
        stash_buckets=c['stash_buckets'], tier_buckets=c['tier_buckets'],
        level_tier_buckets=c['level_tier_buckets'],
        bill_requested=c['bill_requested'], feasible_value_bytes=c['feasible_value_bytes'],
        geometry=rows[0],
        jobs=sum(r['kind'] in ('ordinary', 'top_prepare', 'top_finish') for r in rows) + 1,
        adoptions=sum(r['kind'] == 'adoption' for r in rows),
        keys=sorted(found), missing_keys=missing_keys,
        level_one_native=level_one, families=fam,
        inventory=dict(complete=section['deterministic_inventory_complete'], gaps=section['gaps'],
                       capacity_site_status=section['capacity_site_status'],
                       probe_checks=section['probe']['checks'],
                       ledger_passes=section['ledger_passes'],
                       ledger_obligations_sha256=section['ledger_obligations_sha256'],
                       metadata_checks=section['metadata_checks']),
        status=result['status'], coverage_gaps=result['coverage_gaps'],
        conditional_lifetime_upper_exact=result['conditional_lifetime_upper_exact'],
        conditional_lifetime_log2_display=log2(total),
        margin_bits_display=None if total == 0 else -64 - log2(total),
        meets_target=total <= TARGET and not result['coverage_gaps'],
        components=components, dominant_terms=dominant,
        clocks=result['clocks'], inventory_line=line,
        native_applicability_line=passes[-1]['obligations'][0], native_inventory=rows)


def compile_all(tmp):
    exes, sources = {}, {}
    exes['configuration'], hashes = cc.compile_probe(tmp)
    sources.update(hashes)
    exes['space'], hashes = cc.compile_probe(tmp, PROBE)
    sources.update(hashes)
    exes['inventory'], names = adi.compile_probe(tmp)
    sources.update({str((ROOT/n).resolve().relative_to(ROOT)): bt._sha(ROOT/n) for n in names})
    return exes, sources


def main():
    parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    parser.add_argument('--capacity', type=int, default=CAPACITY)
    parser.add_argument('--output', type=Path, default=None)
    parser.add_argument('--stash-buckets', type=int, default=FIXED['stash_buckets'])
    parser.add_argument('--dense-prefixes', type=int, default=FIXED['dense_prefixes'])
    args = parser.parse_args()
    fixed = fixed_setting(args.stash_buckets, args.dense_prefixes)
    exponent = args.capacity.bit_length()-1
    if args.capacity != 1 << exponent:
        raise ValueError('The capacity must be a power of two (32T with T a power of two)')
    output = args.output or HERE/artifact_name(exponent, fixed)
    table = bt.BoundTable()
    if table.errors:
        raise SystemExit('bound_table.json is stale: ' + '; '.join(table.errors[:5]))
    with tempfile.TemporaryDirectory(prefix='configuration-space-') as tmp:
        exes, sources = compile_all(tmp)
        files = adi.closure(tmp)
        sites = adi.census(files)
        census_gaps = list(adi.classify_census(sites)[-1])
        census = dict(sites=sites, gaps=census_gaps)
        space = enumerate_space(exes['space'], args.capacity, fixed=fixed)
        candidates = theorem_candidates(space, args.capacity)
        results = []
        for c in candidates:
            results.append(certify_candidate(c, exes, table, census, fixed=fixed))
            r = results[-1]
            print(f'{r["name"]:28s} {r["status"]:24s} 2^{r["conditional_lifetime_log2_display"]:.3f} '
                  f'missing={len(r["missing_keys"])} inventory={r["inventory"]["complete"]} '
                  f'native={r["level_one_native"]["passed"] and r["families"].get("passed")}',
                  flush=True)
    counts = [r for r in space if r['kind'] == 'planner_count']
    if any(r['planner_candidates'] != r['enumerated'] for r in counts):
        raise ValueError('The enumeration disagrees with the planner\'s own candidate count')
    default = next(r for r in space if r['kind'] == 'planner_default' and r['value_bytes'] == 16)
    default_name = candidate_name(default)
    # The planner's unpinned choice must not depend on the value width.
    default_widths = {candidate_name(r) for r in space if r['kind'] == 'planner_default'}
    for r in results:
        r['planner_default'] = r['name'] == default_name
    pinned = [r for r in space if r['kind'].startswith('planner_pinned')]
    over = [r for r in space if r['kind'] == 'candidate' and r['capacity_entries'] > args.capacity]
    failing = [r for r in results if not r['meets_target']]
    worst = max(results, key=lambda r: Q(r['conditional_lifetime_upper_exact']))
    keys_used = sorted({k for r in results for k in r['keys']})
    theorem = dict(
        statement=(f'Every valid configuration at N = 2^{exponent} (B = {fixed["branching"]}, '
                   f's = {fixed["stash_buckets"]}, q = {fixed["dense_prefixes"]}, '
                   f'horizon 2^32, automatic tier and native stash sizing, the certified '
                   f'routing) has conditional capacity-failure probability at most 2^-64 over '
                   f'the horizon, under the premises listed with each candidate.'),
        proved=not failing and bool(results),
        reading=('proved means every candidate\'s composed conditional bound is at most the target '
                 'with no coverage gap.  A candidate above the target is not certified by these '
                 'component bounds; that does not show its failures are frequent.'),
        candidates=len(results), failing=[r['name'] for r in failing],
        worst=dict(name=worst['name'], conditional_lifetime_upper_exact=worst['conditional_lifetime_upper_exact'],
                   log2_display=worst['conditional_lifetime_log2_display'],
                   dominant_terms=worst['dominant_terms'][:3]),
        best=min((dict(name=r['name'], log2_display=r['conditional_lifetime_log2_display']) for r in results),
                 key=lambda x: x['log2_display']),
        planner_default=dict(name=default_name, request=default,
                             value_width_independent=default_widths == {default_name},
                             meets_target=next((r['meets_target'] for r in results
                                                if r['name'] == default_name), None),
                             log2_display=next((r['conditional_lifetime_log2_display'] for r in results
                                                if r['name'] == default_name), None)),
        # Every adapter refusal behind a missing key, once per (role, reason).
        blockers=sorted({(m['role'], m['adapter_refusal'] or 'key not computed')
                         for r in results for m in r['missing_keys']}),
        certified_subset=[r['name'] for r in results if r['meets_target']],
        # The planner's own D floor, B/2 + 1 (LevelArenaMinTopDigit): with it
        # the planner never builds D < 5, i.e. at B = 8 it builds D = 8 only.
        planner_default_top_digit_floor=dict(
            min_top_digit=fixed_floor(fixed),
            candidates=[r['name'] for r in results if r['top_digit'] >= fixed_floor(fixed)],
            proved=all(r['meets_target'] for r in results if r['top_digit'] >= fixed_floor(fixed)),
            worst_log2_display=max(r['conditional_lifetime_log2_display'] for r in results
                                   if r['top_digit'] >= fixed_floor(fixed))),
        by_top_digit={str(d): dict(
            candidates=sum(r['top_digit'] == d for r in results),
            meeting_target=sum(r['meets_target'] for r in results if r['top_digit'] == d),
            worst_log2_display=max(r['conditional_lifetime_log2_display'] for r in results
                                   if r['top_digit'] == d),
            best_log2_display=min(r['conditional_lifetime_log2_display'] for r in results
                                  if r['top_digit'] == d))
            for d in sorted({r['top_digit'] for r in results})},
        unconditional_bound='1 (the premises are undischarged, as for the two selected configurations)')
    artifact = dict(
        scope=__doc__, capacity_entries=args.capacity, fixed_choices=fixed,
        target_exact=str(TARGET), theorem=theorem,
        candidates=results,
        distinct_keys_used=len(keys_used),
        keys_by_role=dict(Counter(table.entries[k]['key']['role'] for k in keys_used if k in table.entries)),
        planner_counts=counts, planner_defaults=[r for r in space if r['kind'].startswith('planner_default')
                                                 or r['kind'] == 'planner_min_top_digit_1'],
        planner_pinned=pinned,
        larger_capacity_candidates=dict(
            count=len(over), capacities=dict(Counter(str(r['capacity_entries']) for r in over)),
            note='Feasible for the planner (capacity >= N) but of larger rounded capacity: '
                 'configurations of that larger N, outside this theorem.  The planner returns '
                 'one only when a pinned ladder axis cannot reach N exactly (planner_pinned).'),
        excluded_options=EXCLUDED,
        # The table entries this space was composed from, not the table file:
        # a key added for another capacity or setting leaves it current.  The
        # code that computed those entries is in source_sha256 (the table's
        # own module hashes).
        bound_table_entries=table.entry_digests(keys_used),
        source_sha256=provenance(dict(sorted((sources | table.source_sha256 | {
            str((HERE/n).relative_to(ROOT)): bt._sha(HERE/n) for n in (
                'certify_configuration_space.py', 'bound_table.py', 'check_configuration.py',
                'audit_deterministic_inventory.py', 'certify_level1.py', PROBE,
                'test_bound_table.py')}).items()))))
    output.write_text(json.dumps(artifact, indent=1)+'\n')
    print(f'{len(results)} configurations, {len(keys_used)} distinct keys; conditional target met: '
          f'{theorem["proved"]}; worst {worst["name"]} 2^{worst["conditional_lifetime_log2_display"]:.3f}; '
          f'planner default {default_name}: {theorem["planner_default"]["meets_target"]}')
    print('Wrote', output.name)


EXCLUDED = [
    dict(option='bank_first = kOff',
         reason='Opt-in storage placement the checker does not model (implementation_scope: '
                'default no-clone bank placement).'),
    dict(option='explicit level_fanouts outside the planner\'s two ladders',
         reason='Accepted by LevelArenaGeometry but never produced by the capacity planner; not '
                'in the planner\'s candidate space.  The table composes any such ladder whose '
                'job keys it holds; none is claimed here.'),
    dict(option='B, s, q, horizon other than 8, 1, 2, 2^32; other capacities',
         reason='The caller\'s fixed choices for this theorem; each other setting is its own '
                'configuration space (run with --capacity, and a table extended to its keys).'),
]


if __name__ == '__main__':
    main()
