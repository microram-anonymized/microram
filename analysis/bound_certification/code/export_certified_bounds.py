#!/usr/bin/env python3
"""Export the certified configuration bounds as a C++ table for the planner.

Reads every configuration_space_2p*.json in this directory (the output of
certify_configuration_space.py, one file per capacity) and writes
src/oram/levelarena/cpu_byteslice_level_arena_certified_bounds.inc: one
record per candidate configuration WITHOUT coverage gaps, holding the public
shape the record was certified at (B, s, q, horizon, L, r0, D, the fanout
ladder, the shared tier width and the per-level stash depths) and the
composed conditional lifetime bound as ceil(1000 log2 bound), computed from
the exact rational with integer arithmetic (never from the display float),
so the exported number is an upper bound on the certified one.

The header that reads the table (cpu_byteslice_level_arena_certification.hpp)
is included only from the public layer (include/cpu_byteslice_oram/
byte_map.hpp), never from a header any native probe here compiles against:
the artifacts hash every header the probes include, so a table inside that
closure would make regenerating it invalidate the certificates it was built
from.  This script checks that with the compiler's own dependency lists
(-MM) for every *.cpp here and refuses to write if one reaches either file.

Inputs are refused when stale: each artifact's recorded input_sha256 (the
bound table) and source_sha256 (every tool, probe and production header the
run read) must match the current tree, and bound_table.json must load
without errors.  --allow-stale writes anyway, for development only, and
marks the table stale (kCertifiedBoundsStale), which the C++ reports in
every result's reason.

    python3 export_certified_bounds.py              # write the .inc
    python3 export_certified_bounds.py --check      # fail if it is out of date
    python3 export_certified_bounds.py --allow-stale
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
import math
import os
from pathlib import Path
import shlex
import subprocess
import sys
from source_scope import scope_current, scoped

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
OUTPUT = ROOT/'src/oram/levelarena/cpu_byteslice_level_arena_certified_bounds.inc'
GUARDED = ('src/oram/levelarena/cpu_byteslice_level_arena_certification.hpp',
           'src/oram/levelarena/cpu_byteslice_level_arena_certified_bounds.inc')
TARGET = Q(1, 1 << 64)
MILLI = 1000


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def ceil_log2_millis(value):
    """The smallest integer m with value <= 2^(m/1000), for 0 < value <= 1,
    by exact integer comparison: value^1000 <= 2^m."""
    value = Q(value)
    if value <= 0:
        raise ValueError('A zero bound has no logarithm; refusing to export it')
    if value >= 1:
        return 0
    n, d = value.numerator, value.denominator
    n_pow, d_pow = n**MILLI, d**MILLI

    def holds(m):  # n^1000 / d^1000 <= 2^m, m <= 0
        return n_pow << -m <= d_pow if m <= 0 else n_pow <= d_pow << m

    m = math.ceil(MILLI*(math.log2(n) - math.log2(d)))
    while holds(m - 1):
        m -= 1
    while not holds(m):
        m += 1
    return m


def stale_reasons(artifact, name):
    reasons = []
    for rel, digest in artifact.get('input_sha256', {}).items():
        path = HERE/rel
        if not path.exists() or sha(path) != digest:
            reasons.append(f'{name}: input {rel} changed since the run')
    if not scope_current(artifact.get('source_sha256', {})):
        reasons.append(f'{name}: written under other source_scope.py lists')
    for rel, digest in scoped(artifact.get('source_sha256', {})).items():
        path = ROOT/rel
        if not path.exists() or sha(path) != digest:
            reasons.append(f'{name}: source {rel} changed since the run')
    entries = artifact.get('bound_table_entries', {})
    if entries:
        for kid in bound_table().stale_entries(entries):
            reasons.append(f'{name}: bound table entry {kid[:12]} changed since the run')
    if not (artifact.get('input_sha256') or entries) or not artifact.get('source_sha256'):
        reasons.append(f'{name}: records no input/source hashes')
    return reasons


_TABLE = []


def bound_table():
    """The bound table, loaded once."""
    if not _TABLE:
        sys.path.insert(0, str(HERE))
        import bound_table as bt
        _TABLE.append(bt.BoundTable())
    return _TABLE[0]


def table_errors():
    sys.path.insert(0, str(HERE))
    import bound_table as bt
    return [f'bound_table.json: {e}' for e in bt.BoundTable().errors]


def include_closure_violations(sources=None):
    """Every *.cpp here (or in `sources`) whose compiler dependency list
    reaches a guarded file."""
    cxx = shlex.split(os.environ.get('CXX', 'g++'))
    bad = []
    for source in sorted(sources or HERE.glob('*.cpp')):
        run = subprocess.run([*cxx, '-std=c++17', '-march=native', '-I.', '-MM', str(source)],
                             cwd=ROOT, text=True, capture_output=True)
        if run.returncode:
            raise SystemExit(f'Cannot list the includes of {source.name}:\n{run.stderr}')
        names = shlex.split(run.stdout.replace('\\\n', ' ').split(':', 1)[1])
        closure = {str((ROOT/n).resolve().relative_to(ROOT)) for n in names
                   if (ROOT/n).resolve().is_relative_to(ROOT)}
        bad += [f'{source.name} includes {g}' for g in GUARDED if g in closure]
    return bad


def records_of(artifact, name):
    out = []
    for c in artifact['candidates']:
        if c['coverage_gaps'] or c.get('missing_keys'):
            continue
        config = c['configuration']
        exact = Q(c['conditional_lifetime_upper_exact'])
        meets = exact <= TARGET
        if meets != bool(c['meets_target']):
            raise SystemExit(f'{name}: {c["name"]} meets_target disagrees with its exact bound')
        if (len(c['level_fanouts']) != c['levels'] - 1 or len(c['stash_buckets']) != c['levels']
                or len(c['level_tier_buckets']) != c['levels']):
            raise SystemExit(f'{name}: {c["name"]} has a malformed ladder, stash or tier list')
        out.append(dict(
            name=c['name'], artifact=name,
            capacity=c['geometry']['capacity_entries'],
            branching=config['branching'], s=config['stash_buckets'],
            q=config['dense_prefixes'], horizon=config['horizon_accesses'],
            levels=c['levels'], r0=c['prefix_flushes'], top_digit=c['top_digit'],
            fanouts=','.join(str(f) for f in c['level_fanouts']),
            stash=','.join(str(b) for b in c['stash_buckets']),
            tiers=','.join(str(b) for b in c['level_tier_buckets']),
            millis=ceil_log2_millis(exact), meets=meets))
    return out


def render(records, inputs, stale):
    lines = [
        '// GENERATED by analysis/bound_certification/code/export_certified_bounds.py.',
        '// Do not edit; rerun the script after regenerating the artifacts below.',
        '//',
        '// Included only by cpu_byteslice_level_arena_certification.hpp, which only',
        '// the public layer includes: no native probe of the certification may reach',
        '// this file (the script checks every probe\'s -MM closure).',
        '//',
        '// Inputs (SHA-256 of the file as read):',
    ]
    lines += [f'//   {n}  {d}' for n, d in inputs]
    if stale:
        lines += ['//', '// STALE: written with --allow-stale; these inputs do not match the tree:']
        lines += [f'//   {r}' for r in stale[:40]]
        if len(stale) > 40:
            lines.append(f'//   ... and {len(stale) - 40} more')
    lines += [
        '//',
        '// Each record: name, artifact, capacity (32T entries), B, s, q, horizon,',
        '// L, r0, D, fanouts of levels 1..L-1, per-level stash depths (buckets,',
        '// levels 1..L), per-level tier widths (levels 1..L), ceil(1000 log2',
        '// conditional bound),',
        '// whether the exact bound meets 2^-64.',
        '',
        f'inline constexpr bool kCertifiedBoundsStale = {"true" if stale else "false"};',
        f'inline constexpr size_t kCertifiedBoundRecordCount = {len(records)};',
        'inline constexpr CertifiedBoundRecord kCertifiedBoundRecords[] = {',
    ]
    for r in records:
        lines.append(
            f'    {{"{r["name"]}", "{r["artifact"]}", {r["capacity"]}ull, {r["branching"]}, '
            f'{r["s"]}, {r["q"]}, {r["horizon"]}ull, {r["levels"]}, {r["r0"]}, {r["top_digit"]}, '
            f'"{r["fanouts"]}", "{r["stash"]}", "{r["tiers"]}", {r["millis"]}, '
            f'{"true" if r["meets"] else "false"}}},')
    if not records:  # a C++ array cannot be empty; the count says there is none
        lines.append('    {"", "", 0ull, 0, 0, 0, 0ull, 0, 0, 0, "", "", "", 0, false},')
    lines.append('};')
    return '\n'.join(lines) + '\n'


def build(allow_stale):
    # Every certified online-stash setting: configuration_space_2p*.json (the
    # default s, q) and configuration_space_s*_q*_2p*.json.
    artifacts = sorted(HERE.glob('configuration_space_*2p*.json'),
                       key=lambda p: (p.stem.rsplit('2p', 1)[0], int(p.stem.rsplit('2p', 1)[1])))
    if not artifacts:
        raise SystemExit('No configuration_space_2p*.json to export')
    stale, records, inputs = table_errors(), [], []
    for path in artifacts:
        artifact = json.loads(path.read_text())
        stale += stale_reasons(artifact, path.name)
        records += records_of(artifact, path.name)
        inputs.append((path.name, sha(path)))
    inputs.append(('bound_table.json', sha(HERE/'bound_table.json')))
    if stale and not allow_stale:
        raise SystemExit('Stale certification inputs (rerun bound_table.py and '
                         'certify_configuration_space.py, or pass --allow-stale for a '
                         'development table):\n  ' + '\n  '.join(stale[:20]))
    keys = [(r['capacity'], r['branching'], r['s'], r['q'], r['horizon'], r['levels'], r['r0'],
             r['top_digit'], r['fanouts'], r['stash'], r['tiers']) for r in records]
    if len(set(keys)) != len(keys):
        raise SystemExit('Two records share one shape')
    records.sort(key=lambda r: (r['s'], r['q'], r['capacity'], r['horizon'], r['levels'], r['r0'],
                                r['top_digit'], r['fanouts']))
    return render(records, inputs, stale), records, stale


def main():
    parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    parser.add_argument('--allow-stale', action='store_true',
                        help='development only: export stale artifacts, marked stale')
    parser.add_argument('--check', action='store_true',
                        help='fail if the .inc differs from what this would write')
    parser.add_argument('--output', type=Path, default=OUTPUT)
    args = parser.parse_args()
    import tree_caches
    tree_caches.ensure_recorded()  # rebuild missing gitignored caches; hashes still checked
    violations = include_closure_violations()
    if violations:
        raise SystemExit('A certification probe reaches the exported table (a hash cycle):\n  '
                         + '\n  '.join(violations))
    text, records, stale = build(args.allow_stale)
    if args.check:
        if not args.output.exists() or args.output.read_text() != text:
            raise SystemExit(f'{args.output.relative_to(ROOT)} is out of date; rerun '
                             'export_certified_bounds.py')
        print(f'{args.output.relative_to(ROOT)} is current ({len(records)} records).')
        return
    args.output.write_text(text)
    print(f'Wrote {len(records)} records to {args.output.relative_to(ROOT)}'
          + (f' (STALE: {len(stale)} mismatched inputs)' if stale else ''))


if __name__ == '__main__':
    main()
