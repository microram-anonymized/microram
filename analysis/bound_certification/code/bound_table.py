#!/usr/bin/env python3
"""Shape-keyed table of per-job conditional capacity bounds.

Every per-job bound of the certified routing is a function of the job's
public native shape alone: the configuration probe's row for that job,
without its level number (see KEY below and CONFIGURATION_SPACE.md).
This module computes each such bound ONCE per key, by calling the existing
adapters' own per-row functions with unchanged exact arithmetic, and caches
it in bound_table.json with the SHA-256 of every Python module and loss-tree
cache the computation read.  Any configuration's ledger is then composed
from the table (TableCertificates) with its own exact exposure counts; a job
whose key is not in the table is a coverage gap charged one.

    python3 bound_table.py            # extend the table to every key used by
                                      # the two selected configurations and by
                                      # the configuration space at 2^27
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import sys

import check_configuration as cc
from source_scope import scoped

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
TABLE = HERE/'bound_table.json'

# ---------------------------------------------------------------------------
# The key
# ---------------------------------------------------------------------------

# Fields of a configuration-probe pass row that are NOT part of the key.  The
# level number is a label: every adapter reads it only in its role test
# (level one is the dense job, levels above it the separated jobs) and in
# display names.  The role replaces it.  Everything else the probe prints is
# kept, including fields no current bound reads (e.g. the top's digit in the
# preparation key), so two jobs share a key only when their whole public
# shape agrees.
NON_KEY_FIELDS = ('level',)
ROLES = ('dense_level_one', 'separated_ordinary', 'top_prepare', 'initialization',
         'top_finish')


def role_of(row, initialization=False):
    kind = row['kind']
    if kind == 'ordinary' and row['level'] == 1 and row.get('dense_direct'):
        return 'dense_level_one'
    if kind == 'ordinary' and row['level'] > 1 and row['separated_sources']:
        return 'separated_ordinary'
    if kind == 'top_prepare':
        return 'initialization' if initialization else 'top_prepare'
    if kind == 'top_finish' and not initialization:
        return 'top_finish'
    raise ValueError(f'No tabled role for this row: {row}')


def shape_key(row, initialization=False):
    """The key of one native job: its role and its whole native row, less
    the level number.  Initialization is the top preparation row's second
    job (one exposure, its own capacity for the published tier)."""
    key = dict(role=role_of(row, initialization))
    key.update({k: v for k, v in sorted(row.items()) if k not in NON_KEY_FIELDS})
    return key


def key_id(key):
    return hashlib.sha256(json.dumps(key, sort_keys=True).encode()).hexdigest()


def representative_row(key, level):
    row = {k: v for k, v in key.items() if k != 'role'}
    row['level'] = level
    return row


# ---------------------------------------------------------------------------
# Per-key computation: the adapters' own per-row functions
# ---------------------------------------------------------------------------

def _sum_parts(case, parts):
    return str(min(1, sum((Q(case[p]['probability_upper_decimal']) for p in parts
                           if case[p] is not None), Q(0))))


def compute_case(key, level):
    """(case, tree depths read).  `level` is the representative row's level
    (1 for the dense job); no bound depends on it beyond the role test."""
    role, row = key['role'], representative_row(key, level)
    depths = []
    if role == 'separated_ordinary':
        import certify_separated_sources as css
        from certify_completed_a import evaluate as range_bound
        from certify_sorted_range import tree_at_depth
        stages, packing = css.storage_bounds(row)
        i = row['index_bits']
        density = Q(css.old_law(row)['joint_density_upper_bound'])
        if row['dfs']:
            depths.append(row['block_bits']-i)
            ranges = range_bound(tree_at_depth(row['block_bits']-i), k=row['carry_bits'],
                                 digit=row['digit'], index_bits=i,
                                 early=64*(row['older_tier_buckets']+i*row['stash_buckets']),
                                 density=density)
        else:
            ranges = dict(name='direct_A_pool', probability_upper_decimal='0',
                          approximate_log2_for_display_only=None)
        case = dict(stages=stages, ranges=ranges, packing=packing)
        case['per_job_upper_exact'] = _sum_parts(case, ('stages', 'ranges', 'packing'))
        return case, depths
    if role == 'dense_level_one':
        import certify_level1 as cl1
        case = cl1.evaluate(row)
        case.pop('shape')
        depths = sorted({r['depth'] for g in case['range_sources'] for r in g['roots']})
        case['per_job_upper_exact'] = _sum_parts(case, ('dense', 'stages', 'ranges', 'packing'))
        return case, depths
    if role in ('top_prepare', 'initialization'):
        from audit_ordinary_ranges import PLAN_KEYS, expected_plan
        import certify_top_preparation as ctp
        partition = row | dict(zip(PLAN_KEYS, expected_plan(row['pool_buckets'], row['main_bits'])))
        # certify_top_preparation.main's own DFS domain check.
        if not (row['dfs'] and row['groups'] == 1 and row['scatter_per_bucket'] == 64
                and row['range_buckets'] == 1 << row['range_bits']
                and (row['range_bits'], row['index_bits']) ==
                    (partition['range_bits'], partition['index_bits'])):
            raise ValueError('Top DFS row does not use one-page leaves at the production widths')
        case = ctp.evaluate_shape(partition, role == 'initialization')
        if case['sorted_ranges'] is not None:
            depths.append(case['sorted_ranges']['tree_depth'])
        case['per_job_upper_exact'] = _sum_parts(case, ('sorted_ranges', 'stages', 'packing'))
        return case, depths
    if role == 'top_finish':
        import evaluate_top_finish as etf
        case = etf.evaluate(row, 1)
        for field in ('shape', 'exposures', 'lifetime', 'meets_2_minus_64'):
            case.pop(field)
        case['per_job_upper_exact'] = _sum_parts(case, ('ranges', 'packing'))
        return case, depths
    raise ValueError(f'Unknown role {role}')


# The adapter modules whose functions compute_case calls; their whole Python
# import closure inside this directory is hashed (see _module_hashes).
ADAPTERS = ('certify_separated_sources', 'certify_completed_a', 'certify_sorted_range',
            'certify_level1', 'certify_top_preparation', 'evaluate_top_finish',
            'audit_ordinary_ranges', 'bound_table')


# Imported by the adapters but not part of any bound: which sources count as
# provenance, and the compile cache.  Editing them keeps the table.
TOOLING = ('source_scope.py', 'probe_build.py')


def _module_hashes():
    """SHA-256 of the adapters' whole import closure in this directory, found
    in a fresh interpreter that imports only them, plus the GMP helper."""
    import subprocess
    script = ('import sys, importlib, json\n'
              f'for m in {list(ADAPTERS)!r}: importlib.import_module(m)\n'
              'print(json.dumps(sorted(getattr(m, "__file__", None) or "" for m in list(sys.modules.values()))))')
    files = json.loads(subprocess.run([sys.executable, '-c', script], cwd=HERE, check=True,
                                      text=True, capture_output=True).stdout)
    hashes = {}
    for name in files:
        path = Path(name).resolve() if name else None
        if path and path.suffix == '.py' and path.parent == HERE and path.name not in TOOLING:
            hashes[str(path.relative_to(ROOT))] = _sha(path)
    for name in ('gmp_square.cpp',):
        hashes[str((HERE/name).relative_to(ROOT))] = _sha(HERE/name)
    return dict(sorted(hashes.items()))


def _sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


# ---------------------------------------------------------------------------
# The cached table
# ---------------------------------------------------------------------------

class BoundTable:
    """bound_table.json: entries keyed by key_id, each with its key, case,
    representative occurrence and the tree caches it read.  Loaded entries
    are usable only while every recorded source and tree hash matches."""

    def __init__(self, path=TABLE):
        self.path, self.entries, self.errors = Path(path), {}, []
        self.refused = {}  # key_id -> entry whose adapter refused the shape
        self.source_sha256 = {}
        if not self.path.exists():
            return
        data = json.loads(self.path.read_text())
        self.source_sha256 = data.get('source_sha256', {})
        for name, digest in scoped(self.source_sha256).items():
            if not (ROOT/name).exists() or _sha(ROOT/name) != digest:
                self.errors.append(f'Stale table source: {name}')
        trees = data.get('tree_cache_sha256', {})
        for name, digest in trees.items():
            if not (HERE/name).exists() or _sha(HERE/name) != digest:
                self.errors.append(f'Stale tree cache: {name}')
        if not self.errors:
            for entry in data.get('entries', []):
                if key_id(entry['key']) != entry['key_id']:
                    self.errors.append(f'Entry key digest mismatch: {entry["key_id"]}')
                    continue
                self.entries[entry['key_id']] = entry
            for entry in data.get('refused', []):
                if key_id(entry['key']) == entry['key_id']:
                    self.refused[entry['key_id']] = entry
        if self.errors:
            self.entries, self.refused = {}, {}

    def entry_digests(self, key_ids):
        """key_id -> digest of its stored entry or refusal, for each of
        `key_ids` the table holds: what an artifact composed from those
        entries depends on, rather than on the whole table file, so a key
        added for another shape does not stale it."""
        out = {}
        for kid in key_ids:
            entry = self.entries.get(kid) or self.refused.get(kid)
            if entry is not None:
                out[kid] = hashlib.sha256(json.dumps(entry, sort_keys=True).encode()).hexdigest()
        return out

    def stale_entries(self, recorded):
        """The recorded key_ids whose entry is gone or differs."""
        current = self.entry_digests(recorded)
        return sorted(k for k, d in recorded.items() if current.get(k) != d)

    def lookup(self, key):
        entry = self.entries.get(key_id(key))
        return None if entry is None else entry['case']

    def refusal(self, key):
        """The adapter's reason for refusing this key's shape, or None."""
        entry = self.refused.get(key_id(key))
        return None if entry is None else entry['reason']

    def ensure(self, occurrences, log=print):
        """Compute every missing key.  `occurrences` maps key_id to
        (key, first occurrence dict with at least 'level')."""
        if self.errors:
            log('Discarding stale table:', '; '.join(self.errors[:3]))
            self.entries, self.refused, self.errors = {}, {}, []
        added = 0
        sources = _module_hashes()
        for kid, (key, where) in occurrences.items():
            if kid in self.entries or kid in self.refused:
                continue
            try:
                case, depths = compute_case(key, where['level'])
            except ValueError as error:
                # The adapter's own domain check refuses this shape: no entry,
                # so every job with this key stays a gap charged one.  The
                # refusal is kept (with its reason) to report the blocker.
                self.refused[kid] = dict(key_id=kid, key=key, first_occurrence=where,
                                         reason=str(error))
                log('refused', key['role'], {k: key[k] for k in ('carry_bits', 'digit',
                    'stash_buckets', 'tier_buckets') if k in key}, str(error), flush=True)
                continue
            self.entries[kid] = dict(key_id=kid, key=key, first_occurrence=where,
                                     tree_depths=depths, case=case)
            added += 1
            if added % 10 == 0:
                self.save(sources)  # keep finished work if a later key fails
            log('computed', key['role'], {k: key[k] for k in ('carry_bits', 'digit', 'block_bits',
                'index_bits', 'stash_buckets', 'tier_buckets') if k in key},
                case['per_job_upper_exact'][:12], flush=True)
        return added

    def save(self, sources=None):
        depths = sorted({d for e in self.entries.values() for d in e['tree_depths']})
        entries = sorted(self.entries.values(),
                         key=lambda e: (ROLES.index(e['key']['role']), e['key'].get('carry_bits', 0),
                                        e['key'].get('digit', 0), e['key_id']))
        data = dict(scope=__doc__,
            key=dict(fields='Every field of the configuration-probe pass row except '
                            + ', '.join(NON_KEY_FIELDS) + ', plus the role.',
                     roles=list(ROLES)),
            entry_count=len(entries),
            role_counts={r: sum(e['key']['role'] == r for e in entries) for r in ROLES},
            entries=entries,
            refused=sorted(self.refused.values(), key=lambda e: (ROLES.index(e['key']['role']),
                           e['key'].get('carry_bits', 0), e['key'].get('digit', 0), e['key_id'])),
            source_sha256=sources or _module_hashes(),
            tree_cache_sha256={f'tree_{d}.json': _sha(HERE/f'tree_{d}.json') for d in depths},
            assumptions=['Each case keeps every assumption of the adapter that computed it '
                         '(certify_separated_sources, certify_level1, certify_top_preparation, '
                         'evaluate_top_finish); a table entry is a conditional per-job bound, '
                         'applicable to a configuration only at a native job whose key equals '
                         'the entry key (checked by the composing script).'])
        self.path.write_text(json.dumps(data, indent=1)+'\n')


def occurrences_of(config, rows, where):
    """key_id -> (key, first occurrence) for every tabled job of one
    configuration's native inventory."""
    found = {}
    for row in rows:
        if row['kind'] == 'ordinary' or row['kind'] in ('top_prepare', 'top_finish'):
            inits = (False, True) if row['kind'] == 'top_prepare' else (False,)
            for init in inits:
                key = shape_key(row, init)
                found.setdefault(key_id(key), (key, dict(where, level=row['level'],
                                                         digit=row['digit'])))
    return found


# ---------------------------------------------------------------------------
# A certificate source for check_configuration's builders
# ---------------------------------------------------------------------------

class TableCertificates(cc.Certificates):
    """check_configuration.Certificates served from the table.

    Every lookup is by exact key; a missing key returns None, which the
    checker's builders turn into a coverage gap charged one (fail closed).
    """

    def __init__(self, table):
        self.table = table
        self.data, self.errors, self.hashes = {}, {}, {}
        self._checked, self._active = {}, set()
        if table.errors:
            self.errors['bound_table'] = '; '.join(table.errors)

    def evidence(self, name):
        return f'{TABLE.name} ({name})'

    def _case(self, row, initialization=False):
        try:
            return self.table.lookup(shape_key(row, initialization))
        except ValueError:
            return None

    def separated_case(self, config, row):
        return self._case(row) if row.get('separated_sources') else None

    def level_one_case(self, config, row):
        return self._case(row)

    def top_finish_case(self, config, row):
        return self._case(row)

    def top_preparation_case(self, row, initialization):
        if row['kind'] != 'top_prepare':
            return None
        return self._case(row, initialization)

    def inventory_section(self, config, ledger_sha256):
        return None, 'The table does not carry inventory audits'


def selected_occurrences(exe):
    found = {}
    for name, config in cc.SELECTED.items():
        config = cc.normalize(config)
        found.update({k: v for k, v in occurrences_of(config, cc.probe(config, exe),
                      dict(configuration=name)).items() if k not in found})
    return found


def restamp(path=TABLE):
    """Re-record the adapters' and tree caches' current hashes over the stored
    entries, unchanged.  The table otherwise discards every entry when any
    adapter module changes, which is right for a change to a bound's
    arithmetic and wasteful for one that cannot touch it."""
    data = json.loads(Path(path).read_text())
    data['source_sha256'] = _module_hashes()
    data['tree_cache_sha256'] = {name: _sha(HERE/name) for name in data.get('tree_cache_sha256', {})}
    Path(path).write_text(json.dumps(data, indent=1)+'\n')
    print('Restamped', len(data.get('entries', [])), 'entries of', Path(path).name)


def main():
    import tempfile
    import certify_configuration_space as space
    parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    parser.add_argument('--capacity', type=int, default=space.CAPACITY)
    parser.add_argument('--selected-only', action='store_true')
    parser.add_argument('--stash-buckets', type=int, default=space.FIXED['stash_buckets'])
    parser.add_argument('--dense-prefixes', type=int, default=space.FIXED['dense_prefixes'])
    parser.add_argument('--restamp', action='store_true',
                        help='keep every entry and re-record the adapters\' current hashes; '
                             'only after an edit that cannot change a bound (provenance, '
                             'tooling, comments), reviewed as such')
    args = parser.parse_args()
    if args.restamp:
        restamp()
        return
    fixed = space.fixed_setting(args.stash_buckets, args.dense_prefixes)
    table = BoundTable()
    with tempfile.TemporaryDirectory(prefix='bound-table-') as tmp:
        exe, _ = cc.compile_probe(tmp)
        found = selected_occurrences(exe)
        if not args.selected_only:
            space_exe, _ = cc.compile_probe(tmp, space.PROBE)
            for candidate in space.theorem_candidates(
                    space.enumerate_space(space_exe, args.capacity, fixed=fixed), args.capacity):
                config = space.candidate_config(candidate, fixed)
                for k, v in occurrences_of(config, cc.probe(config, exe),
                                           dict(configuration=candidate['name'])).items():
                    found.setdefault(k, v)
    added = table.ensure(found)
    table.save()
    print(f'{len(table.entries)} table entries ({added} computed); wrote {TABLE.name}')


if __name__ == '__main__':
    main()
