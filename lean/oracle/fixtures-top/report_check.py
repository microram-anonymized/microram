#!/usr/bin/env python3
"""Check REPORT.tex Proposition prop:top-resolution / Lemma
lem:resolved-compression against the ENGINE'S OUTPUT on every fixture that
satisfies the proposition's premises.

The reference is logical: A = C u R, B = B_main u B_tier; B beats A; a winning
tombstone removes the key; X_v = live winners of home v; E = sum (X_v - 64)+.
Claims checked (success runs): C[v] holds min(X_v, 64) records, all in W_v with
the winner's value; the tier holds exactly E records; neither holds a
tombstone; every key of W appears exactly once.  Failure runs: a merge-stash
failure needs E > merge-stash capacity, a drain failure needs E > output-tier
capacity (every append prefix is at most E), a DFS failure needs the model's
leaf count.

Fixtures of the contract-violation families (badflag, dupmain, dupmain2,
misplace, misplacefull) are excluded: they break a premise on purpose.
"""
import glob, json, os, sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
WORK = os.environ.get('ORACLE_TOP_WORK', os.path.join(
    os.path.dirname(os.path.dirname(HERE)), '.lake', 'oracle', 'fixtures-top'))
sys.dont_write_bytecode = True
sys.path.insert(0, HERE)
import model_top as m

VIOLATING = ('badflag', 'dupmain', 'dupmain2', 'misplace', 'misplacefull')


def check(path):
    fam = os.path.basename(path).split('_')[1]
    if fam in VIOLATING:
        return fam, 'excluded', ''
    f = m.load(path)
    g = f['geometry']
    T = g['T']
    words = {w['key']: int(w['word'], 16) for w in f['words']}
    home = lambda k: words[k] & (T - 1)
    newest = {}
    for r in f['inputs']['C_main'] + f['inputs']['R']:
        newest[r['key']] = r
    for r in f['inputs']['B_main'] + f['inputs']['B_tier']:
        newest[r['key']] = r              # B beats A (B is disjoint from itself)
    W = {k: r for k, r in newest.items() if not r['tombstone']}
    X = Counter(home(k) for k in W)
    E = sum(max(0, x - 64) for x in X.values())
    out = f['outputs']
    if out['verdict'] == 'failure':
        if out['kind'] == 'fixed-merge-offers':
            ok = E > g['merge_stash_capacity']
        elif out['kind'] == 'residual-drain':
            ok = E > g['out_tier_capacity']
        else:
            ok = True      # a DFS leaf event: not an E event
        return fam, 'ok' if ok else 'FAIL-E-bound', 'E=%d kind=%s' % (E, out['kind'])
    bad = []
    seen = Counter()
    per_home = Counter()
    for r in out['main']:
        seen[r['key']] += 1
        per_home[r['bucket']] += 1
        if r['tombstone']:
            bad.append('tombstone in main')
        if r['key'] not in W or W[r['key']]['value'] != r['value']:
            bad.append('main record not a winner')
        if home(r['key']) != r['bucket']:
            bad.append('main record off its home')
    for r in out['tier']:
        seen[r['key']] += 1
        if r['tombstone']:
            bad.append('tombstone in tier')
        if r['key'] not in W or W[r['key']]['value'] != r['value']:
            bad.append('tier record not a winner')
    if set(seen) != set(W) or any(v != 1 for v in seen.values()):
        bad.append('winner set differs (%d vs %d)' % (len(seen), len(W)))
    for v in range(T):
        if per_home[v] != min(X[v], 64):
            bad.append('home %d holds %d, min(X,64)=%d' % (v, per_home[v], min(X[v], 64)))
            break
    if len(out['tier']) != E:
        bad.append('tier holds %d, E=%d' % (len(out['tier']), E))
    cn = m.model(f).counters
    if cn['shed_records'] > E or cn['drain1_records'] > E:
        bad.append('an append prefix exceeds E: shed %d, first drain %d, E=%d' % (
            cn['shed_records'], cn['drain1_records'], E))
    if cn['shed_records'] + cn['drain1_records'] != E:
        bad.append('shed + first drain = %d != E=%d' % (
            cn['shed_records'] + cn['drain1_records'], E))
    return fam, 'ok' if not bad else 'FAIL', '; '.join(sorted(set(bad))[:3])


if __name__ == '__main__':
    d = sys.argv[1] if len(sys.argv) > 1 else os.path.join(WORK, 'fx')
    files = sorted(glob.glob(os.path.join(d, 'f*.json')))
    from multiprocessing import Pool
    with Pool(32) as p:
        rows = p.map(check, files, chunksize=4)
    c = Counter((fam, st) for fam, st, _ in rows)
    tot = Counter(st for _, st, _ in rows)
    print('premise-satisfying fixtures checked against the proposition:',
          tot['ok'] + tot['FAIL'] + tot['FAIL-E-bound'], ' agree:', tot['ok'],
          ' disagree:', tot['FAIL'] + tot['FAIL-E-bound'], ' excluded (violating):', tot['excluded'])
    for (fam, st), n in sorted(c.items()):
        if st.startswith('FAIL'):
            print('  ', fam, st, n)
    for (fam, st, detail), p in zip(rows, files):
        if st.startswith('FAIL'):
            print(os.path.basename(p), st, detail)
            break
