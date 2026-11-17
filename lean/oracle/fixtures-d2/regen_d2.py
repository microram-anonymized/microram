#!/usr/bin/env python3
"""Generate all 1964 d = 2 knob sets: 1949 fixtures and 15 checked refusals.

    regen_d2.py OUTDIR [--exe FD2] [--jobs J] [--from DIR] [SUB...]

Each fixture's knobs are encoded in its file name (decode() below). The
battery's names are:

  fx/f_SEED_OLDER_FRESH.json            96 names listed in names.txt
                                        (--seed --forced-older --forced-fresh);
  fy/f_SEED_A_OLDER_BFA_BF_AF.json      the full grid FY_GRID below, each name
                                        also with the suffix --tombs (1536);
  fy/g_SEED_OLDER_FRESH_X.json          166 names listed in names.txt, each
                                        also with --tombs (332).

`--from DIR` takes the names from an existing battery instead (every *.json
under DIR/fx and DIR/fy). SUB restricts the run to fx or fy.

Writes OUTDIR/fx/*.json, OUTDIR/fy/*.json and OUTDIR/manifest.json (one
entry per run: sub, name, arguments, exit status, stderr tail and
expected_refusal). The dumper exits 0 when its self-check passes; 15 named
input-construction refusals must exit 2 with the exact diagnostic below.
Any other nonzero result, missing result or changed known refusal exits 1.
The fixtures do not depend on the worker count. Compare two batteries with
cmp_d2.py; check one with ../check_fixtures.sh.

The dumper defaults to $ORACLE_D2_WORK/fd2 (ORACLE_D2_WORK defaults to
lean/.lake/oracle/fixtures-d2), as built by build_fd2.sh.
"""
import argparse, itertools, json, os, subprocess, sys
from collections import Counter
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(os.path.dirname(HERE))
WORK = os.environ.get('ORACLE_D2_WORK',
                      os.path.join(LEAN, '.lake', 'oracle', 'fixtures-d2'))

# fy/f_SEED_A_OLDER_BFA_BF_AF: --seed, --a-per-bucket, --forced-older,
# --btier-from-atier, --btier-forced, --atier-forced.
FY_GRID = (['1', '2', '5EED0C0DE', 'ABCDEF'], ['16', '30', '40', '64'],
           ['0', '60', '100', '200'], ['0', '6'], ['0', '10', '40'],
           ['0', '8'])
G_X_FLAG = '--btier-from-atier'   # the meaning of a g_ name's last field
EXPECTED = 1964

# These knob sets no longer construct a valid B main under two-block CBC
# routing: the forced keys plus the seeded filler shed during input setup,
# before the merge job starts. Keep every case and require this exact refusal;
# a new refusal or a changed outcome must be reviewed, never silently skipped.
EXPECTED_CARRY_REFUSALS = frozenset({
    'fx/f_2_60_50.json',
    'fx/f_3_40_50.json',
    'fx/f_ABCDEF_60_50.json',
    'fy/g_ABCDEF_64@0,60@1_50@1_0--tombs.json',
    'fy/g_ABCDEF_64@0,60@1_50@1_0.json',
    'fy/g_ABCDEF_64@0,60@1_50@1_6--tombs.json',
    'fy/g_ABCDEF_64@0,60@1_50@1_6.json',
    'fy/g_ABCDEF_64@0,64@1_50@1_0--tombs.json',
    'fy/g_ABCDEF_64@0,64@1_50@1_0.json',
    'fy/g_ABCDEF_64@0,64@1_50@1_6--tombs.json',
    'fy/g_ABCDEF_64@0,64@1_50@1_6.json',
    'fy/g_ABCDEF_64@0,64@8_40@0,20@1_0--tombs.json',
    'fy/g_ABCDEF_64@0,64@8_40@0,20@1_0.json',
    'fy/g_ABCDEF_64@0,64@8_40@0,20@1_6--tombs.json',
    'fy/g_ABCDEF_64@0,64@8_40@0,20@1_6.json',
})
EXPECTED_REFUSAL_STDERR = (
    "fixture_dump: harness error: the fixture's carry shed while routing"
)


def battery_names():
    listed = []
    with open(os.path.join(HERE, 'names.txt')) as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith('#'):
                listed.append(line)
    names = [n for n in listed if n.startswith('fx/')]
    gs = [n for n in listed if n.startswith('fy/g_')]
    assert len(names) + len(gs) == len(listed), 'names.txt: unexpected entry'
    for n in gs:
        names += [n, n[:-5] + '--tombs.json']
    for knobs in itertools.product(*FY_GRID):
        stem = 'fy/f_' + '_'.join(knobs)
        names += [stem + '.json', stem + '--tombs.json']
    assert len(set(names)) == len(names)
    return sorted(names)


def names_from(directory):
    return sorted(f'{sub}/{n}' for sub in ('fx', 'fy')
                  if os.path.isdir(os.path.join(directory, sub))
                  for n in os.listdir(os.path.join(directory, sub))
                  if n.endswith('.json'))


def decode(sub, name):
    stem = name[:-5]
    tombs = stem.endswith('--tombs')
    if tombs:
        stem = stem[:-len('--tombs')]
    p = stem.split('_')
    if sub == 'fx':
        assert p[0] == 'f' and len(p) == 4, name
        a = ['--seed', p[1], '--forced-older', p[2], '--forced-fresh', p[3]]
    elif p[0] == 'f':
        assert len(p) == 7, name
        a = ['--seed', p[1], '--a-per-bucket', p[2], '--forced-older', p[3],
             '--btier-from-atier', p[4], '--btier-forced', p[5],
             '--atier-forced', p[6]]
    else:
        assert p[0] == 'g' and len(p) == 5, name
        a = ['--seed', p[1], '--older-list', p[2], '--fresh-list', p[3],
             G_X_FLAG, p[4]]
    if tombs:
        a.append('--tombs')
    return a


def run(job):
    exe, out_root, rel = job
    sub, name = rel.split('/')
    args = decode(sub, name)
    out = os.path.join(out_root, sub, name)
    pr = subprocess.run([exe, out] + args, capture_output=True, text=True)
    return {'sub': sub, 'name': name, 'args': args, 'status': pr.returncode,
            'stderr': (pr.stderr or '').strip()[-300:]}


def validate_results(results, selected_names):
    """Annotate exact known refusals and reject incomplete or changed outcomes."""
    errors = []
    selected = set(selected_names)
    if len(selected) != len(selected_names):
        errors.append('duplicate selected fixture names')
    seen = Counter()
    for row in results:
        name = row['sub'] + '/' + row['name']
        seen[name] += 1
        row['expected_refusal'] = (
            name in EXPECTED_CARRY_REFUSALS and row['status'] == 2 and
            row['stderr'] == EXPECTED_REFUSAL_STDERR)
        if name not in selected:
            errors.append('unexpected result: ' + name)
        if name in EXPECTED_CARRY_REFUSALS:
            if not row['expected_refusal']:
                errors.append('known carry refusal changed: ' + name)
        elif row['status'] != 0:
            errors.append('unexpected nonzero result: ' + name)
    for name in sorted(selected - seen.keys()):
        errors.append('missing result: ' + name)
    for name, count in sorted(seen.items()):
        if count != 1:
            errors.append('duplicate result: ' + name)
    return errors


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('out')
    ap.add_argument('subs', nargs='*', choices=['fx', 'fy'])
    ap.add_argument('--exe', default=os.path.join(WORK, 'fd2'))
    ap.add_argument('--jobs', type=int, default=24)
    ap.add_argument('--from', dest='src', default=None)
    a = ap.parse_args()
    canonical = battery_names()
    if not EXPECTED_CARRY_REFUSALS.issubset(canonical):
        sys.exit('known carry refusals are not all in the canonical inventory')
    names = names_from(a.src) if a.src else canonical
    if not a.src and len(names) != EXPECTED:
        sys.exit(f'battery has {len(names)} names, expected {EXPECTED}')
    subs = a.subs or ['fx', 'fy']
    names = [n for n in names if n.split('/')[0] in subs]
    if not os.access(a.exe, os.X_OK):
        sys.exit(f'no dumper at {a.exe} (run build_fd2.sh)')
    for sub in subs:
        os.makedirs(os.path.join(a.out, sub), exist_ok=True)
    with Pool(a.jobs) as pool:
        res = pool.map(run, [(a.exe, a.out, n) for n in names], chunksize=8)
    errors = validate_results(res, names)
    for r in res:
        fixture = os.path.join(a.out, r['sub'], r['name'])
        if r['expected_refusal'] and os.path.exists(fixture):
            errors.append('known refusal has a stale fixture: ' + r['sub'] + '/' + r['name'])
        elif r['status'] == 0 and not os.path.isfile(fixture):
            errors.append('successful run has no fixture: ' + r['sub'] + '/' + r['name'])
    with open(os.path.join(a.out, 'manifest.json'), 'w') as f:
        json.dump(res, f)
    print(dict(Counter((r['sub'], r['status']) for r in res)))
    produced = sum(r['status'] == 0 for r in res)
    refused = sum(r['expected_refusal'] for r in res)
    print(f'{produced} fixtures produced; {refused} expected carry-construction '
          f'refusals; {len(names)} knob sets attempted')
    for r in res:
        if r['expected_refusal']:
            print('EXPECTED_REFUSAL', r)
    for error in errors:
        print('ERROR', error)
    sys.exit(1 if errors else 0)


if __name__ == '__main__':
    main()
