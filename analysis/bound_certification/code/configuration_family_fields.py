#!/usr/bin/env python3
"""Classify planner/public options and check fixed-candidate job-key invariance.

This is finite native evidence, not a proof of planner linkage or refinement.
No record tables are allocated. --check reruns the probes and compares the
complete artifact, including the full native source closure.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

import check_configuration as cc
import certify_configuration_space as space
from source_scope import provenance

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REQUEST_HEADER = 'src/oram/levelarena/cpu_byteslice_level_arena_capacity.hpp'
OPTIONS_HEADER = 'include/cpu_byteslice_oram/byte_map.hpp'
PROBE = 'configuration_family_fields_probe.cpp'


def classification(category, effect, family_scope):
    return dict(category=category, effect=effect, family_scope=family_scope)


DOMAIN = 'domain-changing'
BILL = 'bill-only'
RUNTIME = 'runtime-only'
REQUEST_FIELDS = {
    'entries': classification(DOMAIN, 'Filters capacities below the requested count.',
                              'Returned capacity must be 2^11..2^31; positive smaller requests are covered.'),
    'key_bytes': classification(BILL, 'Changes stored layout and pricing; may refuse oversized layouts.',
                                'Any accepted width; finite representative checks below.'),
    'value_bytes': classification(BILL, 'Changes layout, pricing and selected candidate.',
                                  'Any accepted width; finite representative checks below.'),
    'max_accesses': classification(DOMAIN, 'Sizes stashes and tiers.', 'Fixed at 2^32.'),
    'branching': classification(DOMAIN, 'Changes fanout ladder and top digit domain.', 'Fixed at 8.'),
    'bank_first': classification(BILL, 'Changes storage pricing, placement and bank/lease schedule, not probed job keys.',
                                 'Both modes have identical probed job keys; semantic/native applicability remains separate.'),
    'stash_buckets': classification(DOMAIN, 'Changes online stash and carry widths.', 'Fixed at 1.'),
    'dense_prefixes': classification(DOMAIN, 'Changes outstanding dense prefixes.', 'Fixed at 2.'),
    'tier_buckets': classification(DOMAIN, 'Pins tier capacities when nonzero.', 'Fixed at 0 (automatic).'),
    'owner_threads': classification(DOMAIN, 'Raises minimum levels to max(2, owner_threads); also changes bill.',
                                    'Restricts the family; accepted outputs with capacity <= 2^31 remain covered.'),
    'synchronous': classification(BILL, 'Prices synchronous storage; requires no owners or multiple lanes.',
                                  'Both pricing modes; execution applicability is separate.'),
    'batch_participants': classification(BILL, 'Prices participant tiles.', 'Accepted counts; finite check at 4.'),
    'batch_bucket_scan': classification(BILL, 'Prices dense batch bucket storage.', 'Both values; runtime constraints remain.'),
    'near_max_level': classification(RUNTIME, 'Reports a clamped grouping boundary; no job-shape input.',
                                     'Any accepted boundary.'),
    'lanes': classification(BILL, 'lanes and min_buckets price private lane storage.',
                            'Accepted settings; finite checks activate lanes at min_buckets=1.'),
    'half_fanout_prefix': classification(DOMAIN, 'Chooses one of the two enumerated ladder searches.',
                                         'Both ladders included.'),
    'top_digit': classification(DOMAIN, 'Pins D, potentially below the default floor.', 'Fixed at 0 (unpinned).'),
    'prefix_flushes': classification(DOMAIN, 'Restricts r0 to one of 2, 4, 8 when pinned.',
                                      'All three included; pins only restrict the family.'),
    'half_prefix_levels': classification(DOMAIN, 'Restricts the half-fanout prefix length.',
                                         'All accepted pins included.'),
    'bottom_fanout': classification(DOMAIN, 'Restricts the bottom-fanout ladder.', 'All accepted pins included.'),
    'min_top_digit': classification(DOMAIN, 'Changes the unpinned D floor.', 'Fixed at 0 (default).'),
    'byte_slack': classification(BILL, 'Changes selection among feasible candidates.', 'Does not create a geometry.'),
    'max_levels': classification(DOMAIN, 'Truncates the level search.', 'Only restricts the family at these capacities.'),
}

OPTION_TO_REQUEST = {
    'max_accesses': 'max_accesses',
    'deamortized_branching_factor': 'branching',
    'deamortized_half_fanout_prefix': 'half_fanout_prefix',
    'deamortized_bank_first': 'bank_first',
    'deamortized_online_stash_entries': 'stash_buckets',
    'deamortized_prefix_flushes': 'prefix_flushes',
    'deamortized_top_digit': 'top_digit',
    'deamortized_dense_prefixes': 'dense_prefixes',
    'deamortized_tier_buckets': 'tier_buckets',
    'deamortized_owner_threads': 'owner_threads',
    'deamortized_near_max_level': 'near_max_level',
    'deamortized_batch_participants': 'batch_participants',
    'deamortized_batch_bucket_scan': 'batch_bucket_scan',
    'deamortized_rebuild_lanes': 'lanes',
    'deamortized_lane_min_buckets': 'lanes',
}
RUNTIME_OPTIONS = (
    'deamortized_value_workers', 'deamortized_value_tail', 'deamortized_value_kernel',
    'deamortized_value_spin_nanos', 'deamortized_value_pause', 'deamortized_value_monitor_wait',
    'deamortized_value_demote', 'deamortized_value_profile', 'deamortized_value_thread_init',
    'deamortized_batch_lanes', 'deamortized_batch_execution', 'deamortized_batch_profile',
    'deamortized_batch_result_layout', 'deamortized_batch_spin_nanos', 'deamortized_batch_thread_init',
    'deamortized_owner_spin_nanos', 'deamortized_park_retry_micros', 'deamortized_level_groups',
    'deamortized_slice_target_rate', 'deamortized_slice_touches', 'deamortized_inline_work_factor',
    'deamortized_top_helpers', 'deamortized_bottom_helpers', 'deamortized_time_rebuild_stages',
    'deamortized_preroute', 'deamortized_merge_log_capacity', 'deamortized_wait_limit_millis',
    'worker_thread_init', 'deamortized_helper_thread_init', 'secret_seed',
)
OPTIONS_FIELDS = {
    name: dict(REQUEST_FIELDS[request], request_field=request)
    for name, request in OPTION_TO_REQUEST.items()
}
OPTIONS_FIELDS.update({name: classification(
    RUNTIME, 'Changes execution, validation, diagnostics or randomness; not the numerical job shape.',
    'Run/schedule and ideal-tape premises still apply; native refinement is separate.')
    for name in RUNTIME_OPTIONS})
for _name in ('deamortized_rebuild_threads', 'deamortized_near_rebuild_threads',
              'deamortized_far_rebuild_threads', 'deamortized_rebuild_cost'):
    OPTIONS_FIELDS[_name] = classification(
        DOMAIN, 'Budget/group heuristic can re-plan with different owner floors and lane bills.',
        'Only restricts or reselects within the family; accepted returned capacity must be <= 2^31.')
OPTIONS_FIELDS['deamortized_online_stash_entries']['family_scope'] = 'Fixed at 64 (= one bucket).'
OPTIONS_FIELDS['deamortized_near_max_level'] = classification(
    DOMAIN, 'Explicit boundary or host-cache auto detection; with a thread budget it can change owner floors and lane bills.',
    'Does not create job shapes outside the family; no host-independent selected-default claim.')
OPTIONS_FIELDS['secret_seed']['effect'] = 'Selects native random words; not a numerical job-shape field.'
OPTIONS_FIELDS['secret_seed']['family_scope'] = 'Ideal-tape law and cryptographic substitution are separate premises.'
OPTIONS_FIELDS['max_key_normalizations'] = classification(
    RUNTIME, 'Limits normalization admission and retries; does not change planner geometry or job shapes.',
    'Normalization input/block allowance is separate from the ideal capacity bound and native refinement.')
OPTIONS_FIELDS['max_routing_evaluations'] = classification(
    RUNTIME, 'Limits routing evaluations and stops execution on exhaustion; does not change job shapes.',
    'Routing query/block allowance is separate from the ideal capacity bound and native refinement.')


def struct_fields(path, name):
    """Read the present plain data structs; fail closed on unfamiliar declarations."""
    text = path.read_text().split('struct ' + name + ' {', 1)[1].split('\n};', 1)[0]
    text = re.sub(r'/\*.*?\*/|//[^\n]*', '', text, flags=re.S)
    fields = []
    for declaration in text.split(';'):
        declaration = declaration.strip()
        if not declaration:
            continue
        name = declaration.split('=', 1)[0].split()[-1]
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', name):
            raise ValueError(f'Unrecognized field declaration: {declaration}')
        fields.append(name)
    if len(set(fields)) != len(fields):
        raise ValueError('Duplicate field declaration')
    return fields


def checked_classifications():
    result = {}
    for name, path, fields in (('LevelArenaCapacityRequest', REQUEST_HEADER, REQUEST_FIELDS),
                               ('Options', OPTIONS_HEADER, OPTIONS_FIELDS)):
        actual = struct_fields(ROOT/path, name)
        if set(actual) != set(fields):
            raise ValueError(f'{name} classification mismatch: missing={set(actual)-set(fields)}, '
                             f'extra={set(fields)-set(actual)}')
        result[name] = {field: fields[field] for field in actual}
    return result


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def split_variations(rows):
    variants = {}
    current = None
    for row in rows:
        if row['kind'] == 'variation':
            name = row['name']
            if name in variants:
                raise ValueError('Duplicate variation: ' + name)
            current = variants[name] = dict(bill_bytes=row['bill_bytes'], rows=[])
        elif current is None:
            raise ValueError('Shape before variation header')
        else:
            current['rows'].append(row)
    return variants


def compare_variations(variants):
    baseline = variants['baseline']['rows']
    if not baseline or not any(r['kind'] == 'initialization' for r in baseline):
        raise ValueError('Incomplete baseline inventory')
    for name, variant in variants.items():
        if variant['rows'] != baseline:
            raise ValueError(f'{name} changed native job shape fields')
    return hashlib.sha256(json.dumps(baseline, sort_keys=True).encode()).hexdigest()


def audit_fields(candidates):
    """Candidates have `name` and `configuration`, or are raw planner rows."""
    classifications = checked_classifications()
    exe, hashes = cc.compile_probe(None, PROBE)
    inventory_exe, inventory_hashes = cc.compile_probe(None)
    hashes.update(inventory_hashes)
    checked = []
    variant_names = None
    for candidate in candidates:
        config = candidate.get('configuration') or space.candidate_config(candidate)
        run = subprocess.run([str(exe), *cc.probe_arguments(config)],
                             check=True, text=True, capture_output=True)
        variants = split_variations([json.loads(line) for line in run.stdout.splitlines()])
        digest = compare_variations(variants)
        inventory = subprocess.run([str(inventory_exe), *cc.probe_arguments(config), '--init-shape'],
                                   check=True, text=True, capture_output=True)
        native = [json.loads(line) for line in inventory.stdout.splitlines()]
        jobs = [row for row in native if row['kind'] in
                ('ordinary', 'top_prepare', 'top_finish', 'initialization')]
        if jobs != variants['baseline']['rows']:
            raise ValueError('Field-audit baseline differs from the configuration probe')
        if variant_names is not None and list(variants) != variant_names:
            raise ValueError('Variation coverage differs between candidates')
        variant_names = list(variants)
        checked.append(dict(name=candidate['name'], configuration=config,
                            native_shapes_sha256=digest,
                            job_count=len(variants['baseline']['rows']),
                            bill_bytes={name: item['bill_bytes'] for name, item in variants.items()}))
    if not checked:
        raise ValueError('Empty candidate inventory')
    for name in (REQUEST_HEADER, OPTIONS_HEADER,
                 'analysis/bound_certification/code/configuration_family_fields.py',
                 'analysis/bound_certification/code/check_configuration.py',
                 'analysis/bound_certification/code/certify_configuration_space.py',
                 'analysis/bound_certification/code/probe_build.py'):
        hashes[name] = sha(ROOT/name)
    return dict(format='configuration-family-field-audit/1', classifications=classifications,
                evidence=dict(candidates=len(checked), variants=variant_names,
                              comparisons=len(checked)*(len(variant_names)-1),
                              all_job_fields_unchanged=True,
                              bank_first_job_keys_unchanged=True),
                scope=[
                    'Full ordinary, top preparation/finish and distinct initialization rows compared at fixed geometries.',
                    'Finite evidence for listed layouts/pricing variants, not universal C++ planner linkage or native refinement.',
                    'Owner count at or below each candidate level count tests pricing; larger counts restrict the level domain.',
                    'Bank modes share numerical keys; this does not establish bank-mode structural or schedule equivalence.',
                    'Every Options field is classified from source; callbacks, execution and host-budget behavior are not executed.',
                ], candidates=checked, source_sha256=provenance(hashes),
                strict_source_sha256=dict(sorted(hashes.items())))


def family_candidates():
    exe, _ = cc.compile_probe(None, space.PROBE)
    rows = space.enumerate_space(exe, 1 << 11)
    return [candidate for exponent in range(11, 32)
            for candidate in space.theorem_candidates(rows, 1 << exponent)
            if candidate['top_digit'] == 8]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=HERE/'configuration_family_fields.json')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    artifact = audit_fields(family_candidates())
    if args.check:
        if json.loads(args.output.read_text()) != artifact:
            raise SystemExit('Family field audit differs; regenerate after reviewing changes')
    else:
        args.output.write_text(json.dumps(artifact, indent=2)+'\n')
    print(f"{'Checked' if args.check else 'Wrote'} {args.output.name}: "
          f"{artifact['evidence']['candidates']} candidates, "
          f"{artifact['evidence']['comparisons']} fixed-geometry comparisons")


if __name__ == '__main__':
    main()
