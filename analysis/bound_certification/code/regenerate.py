#!/usr/bin/env python3
"""Regenerate the certification artifacts, skipping every step that is current.

A producer step is CURRENT when each artifact it writes exists and every hash
it recorded still matches: its sources (only the files source_scope.py
tracks: the engine files that decide job shapes and stash sizes, and the
analysis code), its input artifacts, its tree caches and, for a
configuration-space artifact, the bound-table entries it was composed from.
A current step is skipped.  So an edit outside source_scope.CERTIFIED_SOURCES
recomputes nothing, and a new shape recomputes only the artifacts that reach
it -- the bound table itself computes only keys it does not hold.

Test steps run whenever a producer or a test has changed. Report-only edits
rebuild the PDF without recomputing numerical certificates. The exported table
and manifest are refreshed after successful validation and checked at the end.

    python3 regenerate.py            # recompute what is stale
    python3 regenerate.py --dry-run  # list what would run
    python3 regenerate.py --force    # recompute everything
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

import source_scope
import tree_caches

HERE = Path(__file__).resolve().parent
ROOT = source_scope.ROOT
CAPACITY_EXPONENTS = range(15, 32)
STASH_SETTINGS = (1, 2, 4)


def space_artifact(exponent, stash):
    return (f'configuration_space_2p{exponent}.json' if stash == 1
            else f'configuration_space_s{stash}_q2_2p{exponent}.json')


# (command, artifacts it writes); no artifacts marks a test step.
STEPS = [
    (['test_regenerate.py'], []),
    (['test_tree_caches.py'], []),
    (['test_abstract_completion.py'], []),
    (['test_direct_frontier.py'], []),
    (['test_sorted_range.py'], []),
    (['audit_ordinary_ranges.py'], ['ordinary_range_audit.json']),
    (['audit_preparation_contract.py'], ['preparation_contract_audit.json']),
    (['test_preparation.py'], []),
    (['test_pooled_finish.py'], []),
    (['test_tier_router.py'], []),
    (['test_top_preparation.py'], []),
    (['certify_top_preparation.py'], ['top_preparation_certificates.json']),
    (['certify_separated_sources.py'], ['separated_sources_certificates.json']),
    (['certify_level1.py'], ['level1_certificates.json']),
    (['test_tier_sizes.py'], []),
    (['analyze_tier_sizes.py'], ['tier_size_analysis.json']),
    (['evaluate_top_finish.py'], ['top_finish_evaluation.json']),
    (['audit_deterministic_inventory.py'], ['deterministic_inventory_audit.json']),
    (['-m', 'unittest', 'test_deterministic_inventory'], []),
    (['test_level1.py'], []),
    (['test_separated_sources.py'], []),
    (['test_configuration.py'], []),
    (['check_configuration.py'], ['configuration_checks.json']),
    (['check_configuration.py', '--config', 'selected_configuration.json', '--details',
      '--output', 'selected_configuration_check.json'], ['selected_configuration_check.json']),
    (['check_configuration.py', '--config', 'selected_configuration_half_fanout.json', '--details',
      '--output', 'selected_configuration_half_fanout_check.json'],
     ['selected_configuration_half_fanout_check.json']),
    # The configuration space: per setting, the table's keys first, then each
    # capacity.  Its own handling below (one artifact per capacity).
    ('space', []),
    (['-m', 'unittest', 'test_export_certified_bounds', 'test_bound_table'], []),
    (['audit_separated_sources.py'], ['separated_sources_audit.json']),
    (['test_completed_a_shadow.py'], []),
    (['test_completed_a_numerics.py'], []),
    (['test_separated_certification.py'], []),
    (['test_top_finish_evaluation.py'], []),
    (['lean_configuration_inventory.py'], ['lean_configuration_2p31.json']),
    (['configuration_family.py'], ['configuration_family.json']),
    (['configuration_family_fields.py'], ['configuration_family_fields.json']),
    (['configuration_family_structure.py'], ['configuration_family_structure.json']),
    (['configuration_family_numerics.py', '--check'], []),
    (['-m', 'unittest', 'test_configuration_family', 'test_configuration_family_lean',
      'test_configuration_family_fields', 'test_configuration_family_structure',
      'test_configuration_family_numerics'], []),
]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


_TABLE = []


def table():
    if not _TABLE:
        import bound_table
        _TABLE.append(bound_table.BoundTable())
    return _TABLE[0]


def current(name):
    """Whether one artifact exists and every hash it recorded still holds."""
    path = HERE/name
    if not path.exists():
        return False
    data = json.loads(path.read_text())
    sources = data.get('source_sha256', {})
    # Shape fixtures record the full native/ledger closure, rather than the
    # numerical source-scope identifier. Refresh them before their consumers.
    if data.get('format') in ('lean-configuration-inventory/1', 'configuration-family-structure/1'):
        generated = data.get('generated_sha256', {})
        if data['format'] == 'configuration-family-structure/1' and not generated:
            return False
        return bool(sources) and all((ROOT/rel).exists() and sha(ROOT/rel) == digest
                                     for rel, digest in (sources | generated).items())
    # Written before the scope existed, or under another list of tracked
    # files: its recorded set is not today's.
    if not source_scope.scope_current(sources):
        return False
    for rel, digest in source_scope.scoped(sources).items():
        if not (ROOT/rel).exists() or sha(ROOT/rel) != digest:
            return False
    # Family membership also depends on planner/pricing headers outside the
    # narrower numerical provenance scope.
    for rel, digest in data.get('strict_source_sha256', {}).items():
        if not (ROOT/rel).exists() or sha(ROOT/rel) != digest:
            return False
    for field in ('input_sha256', 'tree_cache_sha256'):
        for rel, digest in data.get(field, {}).items():
            if not (HERE/rel).exists() or sha(HERE/rel) != digest:
                return False
    entries = data.get('bound_table_entries')
    if entries is not None:
        if table().errors or table().stale_entries(entries):
            return False
    return True


def anything_stale():
    return (any(not current(a) for _, artifacts in STEPS if artifacts != [] and
                isinstance(artifacts, list) for a in artifacts) or
            any(not current(space_artifact(k, s))
                for s in STASH_SETTINGS for k in CAPACITY_EXPONENTS))


def recorded_manifest():
    path = HERE/'SHA256SUMS.json'
    try:
        return json.loads(path.read_text())
    except (OSError, ValueError):
        return {}


def tests_changed(recorded):
    current_tests = {p.name: sha(p) for p in HERE.glob('test_*.py')}
    prior_tests = {name: digest for name, digest in recorded.items()
                   if name.startswith('test_') and name.endswith('.py')}
    # A driver edit can change which tests are run.
    return (current_tests != prior_tests or
            recorded.get('regenerate.py') != sha(HERE/'regenerate.py'))


def report_changed(recorded):
    return any(not (HERE/name).exists() or recorded.get(name) != sha(HERE/name)
               for name in ('../REPORT.tex', '../REPORT.pdf', 'build_report.py'))


class Runner:
    def __init__(self, dry_run, force):
        self.dry_run, self.force, self.ran = dry_run, force, 0
        self.recorded = recorded_manifest()
        self.dirty = force or anything_stale() or tests_changed(self.recorded)

    def run(self, command):
        print(f'=== {time.strftime("%H:%M:%S")} python3 {" ".join(command)}', flush=True)
        if not self.dry_run:
            subprocess.run([sys.executable, *command], cwd=HERE, check=True)
            _TABLE.clear()  # the command may have extended the bound table

    def producer(self, command, artifacts):
        if not self.force and all(current(a) for a in artifacts):
            return False
        self.run(command)
        self.ran += 1
        return True

    def test(self, command):
        if self.dirty:
            self.run(command)

    def space(self):
        for stash in STASH_SETTINGS:
            stale = [k for k in CAPACITY_EXPONENTS
                     if self.force or not current(space_artifact(k, stash))]
            if not stale:
                continue
            # The base call extends the table to the selected configurations
            # and the space at 2^27; a capacity's own call adds its keys.
            self.run(['bound_table.py', '--stash-buckets', str(stash)])
            for k in stale:
                if k != 27:
                    self.run(['bound_table.py', '--capacity', str(1 << k),
                              '--stash-buckets', str(stash)])
            for k in stale:
                self.run(['certify_configuration_space.py', '--capacity', str(1 << k),
                          '--stash-buckets', str(stash)])
            self.ran += 1


def main():
    parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    parser.add_argument('--dry-run', action='store_true')
    parser.add_argument('--force', action='store_true')
    parser.add_argument('--configuration-family', action='store_true',
                        help='regenerate only the standard D=8 family inventory and its audits')
    args = parser.parse_args()
    # A fresh checkout has no tree caches; rebuild the recorded ones first so
    # that staleness reflects sources, not the missing gitignored files.
    tree_caches.ensure_recorded()
    runner = Runner(args.dry_run, args.force)
    if args.configuration_family:
        runner.producer(['lean_configuration_inventory.py'], ['lean_configuration_2p31.json'])
        runner.producer(['configuration_family.py'], ['configuration_family.json'])
        runner.producer(['configuration_family_fields.py'], ['configuration_family_fields.json'])
        runner.producer(['configuration_family_structure.py'], ['configuration_family_structure.json'])
        runner.run(['configuration_family_numerics.py', '--check'])
        runner.run(['-m', 'unittest', 'test_configuration_family',
                    'test_configuration_family_lean', 'test_configuration_family_fields',
                    'test_configuration_family_structure', 'test_configuration_family_numerics', 'test_regenerate'])
        runner.run(['manifest.py'])
        if not args.dry_run:
            runner.run(['manifest.py', '--check'])
        return
    for command, artifacts in STEPS:
        if command == 'space':
            runner.space()
        elif artifacts:
            runner.producer(command, artifacts)
        else:
            runner.test(command)
    # Export validates its inputs before writing; stale evidence still fails closed.
    runner.run(['export_certified_bounds.py'])
    if runner.ran or report_changed(runner.recorded):
        runner.run(['build_report.py'])
    runner.run(['manifest.py'])
    if not args.dry_run:
        runner.run(['export_certified_bounds.py', '--check'])
        runner.run(['manifest.py', '--check'])
    print(f'{runner.ran} producer step(s) ran' + (' (dry run)' if args.dry_run else ''))


if __name__ == '__main__':
    main()
