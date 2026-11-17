#!/usr/bin/env python3
"""Independent A-phase reference regressions; no native correspondence claim."""
import copy
import json
import pathlib
import random
import subprocess
import tempfile
from direct_job_tests import ROOT, rec, fixture


def factor(d):
    e = 0
    while d % 2 == 0:
        d //= 2
        e += 1
    return e, d


def route_ops(base, start, levels):
    if levels > 4:
        low = levels // 2 - (levels // 2) % 2
        high = levels - low
        return ([op for h in range(1 << high) for op in route_ops(base + (h << (start + low)), start, low)] +
                [op for l in range(1 << low) for op in route_ops(base + (l << start), start + low, high)])
    out = []
    for lev in range(0, levels - 1, 2):
        for mid in range(1 << levels):
            if (mid >> lev) % 4 == 0:
                i, b = base + (mid << start), start + lev
                out += [(b, i), (b, i + (2 << b)), (b + 1, i), (b + 1, i + (1 << b))]
    if levels % 2:
        lev = levels - 1
        out += [(start + lev, base + (mid << start)) for mid in range(1 << levels) if not (mid >> lev) % 2]
    return out


def pool_capacity(g):
    e, r = factor(g['digit'])
    return (g['K'] + e) * g['route_capacity'] + (g['radix_capacity'] if r > 1 else 0) + g['a_tier_capacity']


def ranges(g, index_bits=0):
    if g['output_homes'] <= 8 or not pool_capacity(g):
        g['ranges'] = dict(kind='direct')
    else:
        rb = max(0, (g['output_homes'] - 1).bit_length() - index_bits)
        g['ranges'] = dict(kind='dfs', index_bits=index_bits, range_bits=rb, pool_capacity=pool_capacity(g))


def event(phase, site, ordinal, occupancy, capacity):
    return dict(phase=phase, site=site, ordinal=ordinal, occupancy=occupancy, capacity=capacity)


def reference(f):
    g, inp = f['geometry'], f['inputs']
    k, d = g['K'], g['digit']
    u = 1 << k
    e, radix = factor(d)
    bits, block = k + e, 1 << (k + e)
    words = {w['key']: w['word'] for w in f['words'] if w['family'] == 'current'}
    main = [[None] * 64 for _ in range(u)] + copy.deepcopy(inp['a_main'])
    stashes, rad, trace = [[] for _ in range(bits)], [], []
    ops = [op for q in range(1, radix) for op in route_ops(q * block, 0, bits)]
    ops += [op for v in reversed(range(e)) for op in route_ops(1 << (k + v), 0, k + v)]
    ops += [(k + v, i) for v in range(e) for i in range(1 << (k + v))]
    for bit, i in ops:
        first, second = main[i], main[i + (1 << bit)]
        outputs = [[x if x is not None and ((words[x['key']] >> bit) & 1) == side else None
                    for x in first] for side in range(2)]
        shed = []
        for x in second:
            if x is None:
                continue
            side = (words[x['key']] >> bit) & 1
            holes = [n for n, v in enumerate(outputs[side]) if v is None]
            if holes:
                outputs[side][holes[0]] = x
            else:
                shed.append(x)
        main[i], main[i + (1 << bit)] = outputs
        stashes[bit] += shed
        trace.append(event('prepareA', dict(kind='route', bit=bit, continuation=i < (1 << bit)),
                           len(trace), len(stashes[bit]), g['route_capacity']))
    if radix > 1:
        for p in range(block):
            indices = [a * block + p for a in range(radix)]
            sources = [main[i] for i in indices]
            placed, outputs = set(), []
            for a in range(radix):
                out = [x if x is not None and (words[x['key']] // block) % radix == a else None
                       for x in sources[a]]
                placed.update(x['key'] for x in out if x is not None)
                for b in range(radix):
                    if a == b:
                        continue
                    for x in sources[b]:
                        if x is not None and (words[x['key']] // block) % radix == a and None in out:
                            out[out.index(None)] = x
                            placed.add(x['key'])
                outputs.append(out)
            rad += [x for src in sources for x in src if x is not None and x['key'] not in placed]
            for i, out in zip(indices, outputs):
                main[i] = out
            trace.append(event('prepareA', dict(kind='radix'), len(trace), len(rad), g['radix_capacity']))
    unfiltered = sum(stashes, []) + rad + inp['a_tier']
    latest = {x['key']: (ui, lane) for ui, unit in enumerate(inp['units'])
              for lane, x in enumerate(unit) if x is not None}
    bmain, btier, btrace = [[] for _ in range(u)], [], []
    for ui, unit in enumerate(inp['units']):
        for lane, x in enumerate(unit):
            if x is None or latest[x['key']] != (ui, lane):
                continue
            home = words[x['key']] % u
            if len(bmain[home]) < 64:
                bmain[home].append(x)
            else:
                btier.append(x)
        btrace.append(event('produceB', dict(kind='bTier'), ui, len(btier), 64))
    bkeys = {x['key'] for x in btier}
    pool = [x for x in unfiltered if x['key'] not in bkeys]
    plan, dt = g['ranges'], []
    if plan['kind'] == 'direct':
        leaves = [pool]
    else:
        rb, ib, cap = plan['range_bits'], plan['index_bits'], plan['pool_capacity']
        home_range = lambda x: (words[x['key']] % (d * u)) >> ib
        leaves = [[x for x in pool if home_range(x) == v] for v in range(1 << rb)]
        for depth in range(rb + 1):
            for pre in range(1 << depth):
                occupancy = sum(home_range(x) >> (rb - depth) == pre for x in pool)
                dt.append(event('distributeA', dict(kind='dfs', depth=depth, pre=pre), len(dt),
                                occupancy, min(cap, 64 << (rb - depth))))
    failure = next((ev for ev in trace + btrace + dt if ev['occupancy'] > ev['capacity']), None)
    return dict(a_main=main, a_stashes=stashes, a_radix=rad, a_trace=trace,
                unfiltered_pool=unfiltered, b_tier=btier, operational_pool=pool,
                leaves=leaves, distribution_trace=dt,
                bounded=dict(kind='failed', event=failure) if failure else dict(kind='phases-completed'))


def make(d, k, lengths, tier=0, seed=0, concentrated=False):
    rng = random.Random(seed)
    key, am = 0, []
    old = []
    for home, length in enumerate(lengths):
        bucket = [rec(i, tombstone=i % 7 == 0) for i in range(key, key + length)] + [None] * (64 - length)
        rng.shuffle(bucket)
        old += [dict(family='old', key=i, word=home) for i in range(key, key + length)]
        key += length
        am.append(bucket)
    at = [rec(i, tombstone=i % 3 == 0) for i in range(key, key + tier)]
    old += [dict(family='old', key=i, word=0) for i in range(key, key + tier)]
    words = {i: 0 if concentrated else rng.randrange(d * (1 << k) * 13) for i in range(key + tier)}
    f = fixture([], k=k, digit=d, words=words, a_main=am, a_tier=at)
    f['format'] = 'direct-job-a-reference/0'
    f['words'] += old
    f['geometry']['a_tier_capacity'] = max(64, tier)
    ranges(f['geometry'])
    return f


def cases():
    out = []
    def add(name, f, code=0):
        f['expected'] = copy.deepcopy(reference(f))
        out.append((name, f, code))
        return f
    def mutate(name, f, change, code=1):
        m = copy.deepcopy(f)
        change(m)
        out.append((name, m, code))
    for d in range(2, 9):
        for k in [0, 1, 2]:
            n = (d - 1) * (1 << k)
            add(f'empty-{d}-{k}', make(d, k, [0]*n))
            add(f'mixed-{d}-{k}', make(d, k, [(i*23 + 17) % 65 for i in range(n)], tier=9, seed=d+k))
            full = make(d, k, [64]*n, concentrated=True)
            baseline = reference(full)
            for kind, field in [('route', 'route_capacity'), ('radix', 'radix_capacity')]:
                maximum = max([ev['occupancy'] for ev in baseline['a_trace'] if ev['site']['kind'] == kind] or [0])
                if maximum:
                    for delta in [0, -1]:
                        f = copy.deepcopy(full)
                        f['geometry'][field] = maximum + delta
                        ranges(f['geometry'])
                        add(f'{kind}-boundary-{d}-{k}-{delta}', f)
    # A residual must survive a B-main version until finish, but B-tier copies
    # (including tombstones) remove it before distribution.
    for tomb in [False, True]:
        f = make(2, 0, [0], tier=1, concentrated=True)
        f['inputs']['units'] = [[rec(100+i) for i in range(64)] + [rec(0, 999, tomb)]]
        f['words'] += [dict(family='current', key=100+i, word=0) for i in range(64)]
        add(f'b-tier-freshness-{tomb}', f)
        f = make(2, 0, [0], tier=1, concentrated=True)
        f['inputs']['units'] = [[rec(0, 999, tomb)]]
        add(f'b-main-deferred-{tomb}', f)
    for n in [64, 65]:
        add(f'dfs-leaf-{n}', make(3, 2, [0]*8, tier=n, concentrated=True))
        add(f'direct-no-dfs-{n}', make(2, 0, [0], tier=n, concentrated=True))
    add('recursive-schedule', make(3, 5, [i % 3 for i in range(64)], tier=2, seed=42))
    zero = make(3, 2, [0]*8)
    zero['geometry'].update(route_capacity=0, radix_capacity=0, a_tier_capacity=0)
    ranges(zero['geometry'])
    add('zero-pool-direct-large-output', zero)
    indexed = make(3, 2, [9]*8, tier=7, seed=4)
    ranges(indexed['geometry'], index_bits=2)
    add('dfs-multiple-homes-per-range', indexed)
    for n in [128, 129]:
        f = make(3, 2, [0]*8, tier=65, concentrated=True)
        f['inputs']['units'] = [[rec(1000+i) for i in range(n)]]
        f['words'] += [dict(family='current', key=1000+i, word=0) for i in range(n)]
        add(f'B-before-DFS-priority-{n}', f)
    f = make(4, 2, [64]*12, tier=65, concentrated=True)
    f['inputs']['units'] = [[rec(1000+i) for i in range(129)]]
    f['words'] += [dict(family='current', key=1000+i, word=0) for i in range(129)]
    add('A-before-B-before-DFS-priority', f)
    sample = add('mutation-control', make(3, 2, [12]*8, tier=3, seed=17))
    mutate('wrong-main-lane', sample, lambda f: f['expected']['a_main'].reverse())
    mutate('wrong-trace-capacity', sample, lambda f: f['expected']['a_trace'][0].update(capacity=999))
    mutate('wrong-record-payload', sample, lambda f: f['expected']['unfiltered_pool'][0].update(value=999))
    mutate('wrong-publication', sample, lambda f: f['expected']['bounded'].update(kind='published'))
    mutate('wrong-pool-order', sample, lambda f: f['expected']['operational_pool'].reverse())
    mutate('bad-A-duplicate', sample, lambda f: f['inputs']['a_tier'].append(copy.deepcopy(f['inputs']['a_tier'][0])), 2)
    mutate('bad-A-width', sample, lambda f: f['inputs']['a_main'][0].pop(), 2)
    mutate('missing-word', sample, lambda f: f['words'].pop(0), 2)
    mutate('bad-DFS-capacity', sample, lambda f: f['geometry']['ranges'].update(pool_capacity=1), 2)
    mutate('digit-one', sample, lambda f: f['geometry'].update(digit=1), 2)
    return out


def main():
    entries = cases()
    with tempfile.TemporaryDirectory(prefix='direct-job-a-') as tmp:
        paths = []
        for name, f, code in entries:
            path = pathlib.Path(tmp) / f'{name}.json'
            path.write_text(json.dumps(f))
            run = subprocess.run([str(ROOT/'.lake/build/bin/oracle'), '--direct-a', str(path)],
                                 text=True, capture_output=True, timeout=90)
            assert run.returncode == code, (name, code, run.returncode, run.stdout[:3000], run.stderr)
            payload = json.loads(run.stdout)
            if code < 2:
                assert payload['comparison'] == ('pass' if code == 0 else 'fail'), (name, payload)
            else:
                assert payload['o1'] == 'malformed', (name, payload)
            paths.append((path, code))
        batch_paths = [next(p for p, c in paths if c == code) for code in [2, 0, 1]]
        batch = subprocess.run([str(ROOT/'.lake/build/bin/oracle'), '--direct-a', *map(str, batch_paths)], capture_output=True)
        assert batch.returncode == 2 and len(batch.stdout.splitlines()) == 3
    counts = [sum(c == code for _, _, c in entries) for code in [0, 1, 2]]
    print(f'A reference regression: {len(entries)} passed ({counts[0]} matches, {counts[1]} mutations, {counts[2]} malformed); mixed batch exit 2')


if __name__ == '__main__':
    main()
