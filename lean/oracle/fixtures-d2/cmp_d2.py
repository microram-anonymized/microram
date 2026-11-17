#!/usr/bin/env python3
"""Compare two d = 2 batteries (directories holding fx/ and fy/).

    cmp_d2.py OLD_DIR NEW_DIR

Per subdirectory: the name sets, the inputs / words / families / job /
geometry (decode_ok), the outputs (verdict, message, main, tier), the parsed
JSON and the raw bytes. Prints the geometry fields that differ and the first
100 output differences. Exit 0 iff the name sets are equal and every fixture
is byte-identical.
"""
import collections, json, os, sys

if len(sys.argv) != 3:
    sys.exit('usage: cmp_d2.py OLD_DIR NEW_DIR')
status = 0
for sub in ('fx', 'fy'):
    old_d = os.path.join(sys.argv[1], sub)
    new_d = os.path.join(sys.argv[2], sub)
    old_n = sorted(n for n in os.listdir(old_d) if n.endswith('.json'))
    new_n = sorted(n for n in os.listdir(new_d) if n.endswith('.json'))
    if old_n != new_n:
        status = 1
        print(sub, 'name sets differ: only old', len(set(old_n) - set(new_n)),
              'only new', len(set(new_n) - set(old_n)))
    names = sorted(set(old_n) & set(new_n))
    c = collections.Counter(); diffs = []
    geo_diff = collections.Counter()
    for n in names:
        ra = open(os.path.join(old_d, n), 'rb').read()
        rb = open(os.path.join(new_d, n), 'rb').read()
        c['bytes_identical'] += ra == rb
        if ra != rb:
            status = 1
        a = json.loads(ra); b = json.loads(rb)
        ok_in = all(a[k] == b[k] for k in ('inputs', 'words', 'families'))
        ga, gb = a['geometry'], b['geometry']
        ok_geo = ga == gb
        for k in set(ga) | set(gb):
            if ga.get(k) != gb.get(k): geo_diff[(k, ga.get(k), gb.get(k))] += 1
        ok_job = a['job'] == b['job']
        c[('decode_ok', ok_in and ok_geo and ok_job)] += 1
        oa, ob = a['outputs'], b['outputs']
        same = all(oa[k] == ob[k] for k in ('verdict', 'message', 'main', 'tier'))
        c[('outputs_same', same)] += 1
        c[('verdict', oa['verdict'], ob['verdict'])] += 1
        if not same:
            d = {k: (oa[k] if k in ('verdict', 'message') else len(oa[k]),
                     ob[k] if k in ('verdict', 'message') else len(ob[k]))
                 for k in ('verdict', 'message', 'main', 'tier') if oa[k] != ob[k]}
            diffs.append((n, d))
        c['json_equal'] += a == b
    print(sub, len(names), dict(c))
    print('  geometry diffs:', dict(geo_diff))
    for n, d in diffs[:100]: print('  DIFF', n, d)
print('byte-identical:', 'yes' if status == 0 else 'NO')
sys.exit(status)
