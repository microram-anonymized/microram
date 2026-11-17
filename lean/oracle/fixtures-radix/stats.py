#!/usr/bin/env python3
"""Per-digit match statistics and path coverage from gen.py's results.json.

    stats.py OUTDIR/results.json"""
import json, sys
from collections import Counter, defaultdict
sys.dont_write_bytecode = True
import gen
rs = json.load(open(sys.argv[1]))
by = defaultdict(list)
for r in rs:
    if 'harness' not in r:
        by[gen.CONFIGS[r['label']][3]].append(r)
KINDS = ['butterfly', 'route-level', 'radix-route', 'residual-dfs-partition',
         'fixed-merge-offers', 'residual-drain']
print('digit fixtures match success ' + ' '.join(KINDS))
for d in sorted(by):
    x = by[d]; k = Counter(r.get('eng_kind') for r in x if r['engine'] == 'failure')
    print(d, len(x), sum(r['ok'] for r in x), sum(r['engine'] == 'success' for r in x),
          ' '.join(str(k[q]) for q in KINDS))
print('total', sum(len(v) for v in by.values()), sum(r['ok'] for v in by.values() for r in v))
print('harness skips (fixture B-carry contract):', sum('harness' in r for r in rs))
print('\npath coverage: number of fixtures exercising each path, per digit')
cov = defaultdict(Counter)
for d, x in by.items():
    for r in x:
        for key, v in r.get('cov', {}).items():
            if v:
                cov[key][d] += 1
for key in sorted(cov):
    print(f'{key:34s}', ' '.join(f'd{d}:{cov[key][d]}' for d in sorted(by) if cov[key][d]))

print('\nschedule variants vs engine: fixtures with (same verdict, same kind, record-exact, lane-exact)')
for o in ('blank-full', 'canonical'):
    for d in sorted(by):
        x = [r['orders'][o] for r in by[d] if 'orders' in r]
        succ = [r['orders'][o] for r in by[d] if 'orders' in r and r['engine'] == 'success']
        print(f'{o:10s} d{d}: n={len(x)} verdict={sum(a[0] for a in x)} kind={sum(a[1] for a in x)} '
              f'| successes={len(succ)} record_exact={sum(a[2] for a in succ)} lane_exact={sum(a[3] for a in succ)}')
