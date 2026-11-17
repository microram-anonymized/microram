#!/usr/bin/env python3
"""Compare two radix batteries written by gen.py.

    cmp_radix.py OLD_DIR NEW_DIR

Compares the two results.json files job by job (arguments, harness refusals,
engine verdict and failure kind, model verdict, match, self-check, schedule
orders) and every fixture file present in either directory byte for byte
(a battery generated with --keep holds all of them). Exit 0 iff the job
sets, arguments and verdicts agree and every fixture is byte-identical.
"""
import collections, json, os, sys

if len(sys.argv) != 3:
    sys.exit('usage: cmp_radix.py OLD_DIR NEW_DIR')
od, nd = sys.argv[1:3]
status = 0
old = {(r['label'], r['idx']): r for r in json.load(open(os.path.join(od, 'results.json')))}
new = {(r['label'], r['idx']): r for r in json.load(open(os.path.join(nd, 'results.json')))}
print('jobs old', len(old), 'new', len(new), 'same keys', set(old) == set(new))
if set(old) != set(new):
    status = 1
c = collections.Counter(); ex = []
for k in sorted(set(old) & set(new)):
    a, b = old[k], new[k]
    c['args_same'] += a['args'] == b['args']
    if a['args'] != b['args']:
        status = 1
    ha, hb = 'harness' in a, 'harness' in b
    c[('harness', ha, hb)] += 1
    if ha or hb:
        if ha != hb:
            ex.append((k, 'harness', a.get('harness'), b.get('harness'))); status = 1
        continue
    same = all(a.get(f) == b.get(f) for f in ('engine', 'eng_kind', 'model', 'ok', 'selfcheck'))
    c['verdict_kind_ok_same'] += same
    if not same:
        status = 1
        ex.append((k, {f: (a.get(f), b.get(f)) for f in ('engine', 'eng_kind', 'model', 'ok', 'selfcheck') if a.get(f) != b.get(f)}))
    if a.get('orders') != b.get('orders'): c['orders_differ'] += 1
print(dict(c))
for e in ex[:40]: print(' ', e)
hm = collections.Counter(r['harness'][:90] for r in new.values() if 'harness' in r)
for m, n in hm.most_common(8): print('  harness', n, m)


def fixtures(d):
    return {os.path.join(lb, n) for lb in os.listdir(d) if os.path.isdir(os.path.join(d, lb))
            for n in os.listdir(os.path.join(d, lb)) if n.endswith('.json')}


fo, fn = fixtures(od), fixtures(nd)
same_bytes = sum(open(os.path.join(od, p), 'rb').read() == open(os.path.join(nd, p), 'rb').read()
                 for p in sorted(fo & fn))
print('fixture files: old', len(fo), 'new', len(fn), 'common', len(fo & fn),
      'byte-identical', same_bytes)
if fo != fn or same_bytes != len(fo & fn):
    status = 1
print('agree:', 'yes' if status == 0 else 'NO')
sys.exit(status)
