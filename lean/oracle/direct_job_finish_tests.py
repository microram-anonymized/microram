#!/usr/bin/env python3
"""Independent complete direct-job regressions; no native correspondence claim.

Run after ``lake build oracle``: python3 oracle/direct_job_finish_tests.py.
``--keep DIR`` retains generated original-input reference fixtures.
"""
import argparse
import copy
import json
import pathlib
import random
import subprocess
import tempfile

import direct_job_a_tests as a_tests
import direct_job_tests as b_tests
from direct_job_tests import ROOT, fixture, rec


def produce(f):
    g, inp = f['geometry'], f['inputs']
    words = {v['key']: v['word'] for v in f['words'] if v['family'] == 'current'}
    latest = {x['key']: (u, lane) for u, unit in enumerate(inp['units'])
              for lane, x in enumerate(unit) if x is not None}
    main, tier, trace = [[] for _ in range(1 << g['K'])], [], []
    cap = g['output_capacity'] if g['digit'] == 1 else 64
    site = 'outputTier' if g['digit'] == 1 else 'bTier'
    for ordinal, unit in enumerate(inp['units']):
        for lane, x in enumerate(unit):
            if x is None or latest[x['key']] != (ordinal, lane):
                continue
            home = words[x['key']] % len(main)
            if len(main[home]) < 64:
                main[home].append(copy.deepcopy(x))
            else:
                tier.append(copy.deepcopy(x))
        trace.append(a_tests.event('produceB', dict(kind=site), ordinal, len(tier), cap))
    return main, tier, trace


def fill(main, candidates):
    """Stable source selection into ascending free destination lanes."""
    main = copy.deepcopy(main)
    holes = [i for i, x in enumerate(main) if x is None]
    taken = min(len(holes), len(candidates))
    for lane, x in zip(holes, candidates):
        main[lane] = copy.deepcopy(x)
    return main, candidates[taken:]


def reference(f):
    g = f['geometry']
    words = {v['key']: v['word'] for v in f['words'] if v['family'] == 'current'}
    u, d = 1 << g['K'], g['digit']
    bmain, btier, btrace = produce(f)
    lanes = [xs + [None] * (64 - len(xs)) for xs in bmain]
    if d == 1:
        main, insertion, leaves, bcopy, tier, trace = lanes, [], [], [], btier, []
        all_trace = btrace
    else:
        a = a_tests.reference(f)
        main, insertion = copy.deepcopy(a['a_main']), []
        leaves, bcopy, trace = copy.deepcopy(a['leaves']), [copy.deepcopy(btier)], []
        home = lambda x: words[x['key']] % (d * u)
        for source in range(u):
            keys = {x['key'] for x in bmain[source]}
            for q in range(d):
                ci = source + q * u
                main[ci] = [None if x is not None and x['key'] in keys else x for x in main[ci]]
            sheds = []
            for q in range(d):
                ci = source + q * u
                candidates = [x for x in bmain[source] if home(x) // u == q]
                main[ci], remaining = fill(main[ci], candidates)
                sheds.extend(remaining)
                if q + 1 == d:
                    insertion.extend(sheds)
                    trace.append(a_tests.event('finish', dict(kind='insertion'), source,
                                               len(insertion), g['insertion_capacity']))
                ri = 0 if g['ranges']['kind'] == 'direct' else ci >> g['ranges']['index_bits']
                candidates = [x for x in leaves[ri] if home(x) == ci]
                main_keys = {x['key'] for x in main[ci] if x is not None}
                drop = {x['key'] for x in candidates if x['key'] in main_keys}
                stale = [x for x in candidates if x['key'] not in main_keys]
                main[ci], remaining = fill(main[ci], stale)
                placed = {x['key'] for x in stale[:len(stale) - len(remaining)]}
                leaves[ri] = [x for x in leaves[ri] if x['key'] not in drop | placed]
                for page in range(len(bcopy)):
                    candidates = [x for x in bcopy[page] if home(x) == ci]
                    fresh_keys = {x['key'] for x in candidates}
                    cleared = [None if x is not None and x['key'] in fresh_keys else x for x in main[ci]]
                    main[ci], remaining = fill(cleared, candidates)
                    placed = {x['key'] for x in candidates[:len(candidates) - len(remaining)]}
                    bcopy[page] = [x for x in bcopy[page] if x['key'] not in placed]
        tagged = []
        chunks = [[(x, True) for x in xs] for xs in leaves] + [[(x, False) for x in xs] for xs in bcopy]
        for ordinal, chunk in enumerate(chunks):
            tagged.extend(chunk)
            trace.append(a_tests.event('drain', dict(kind='outputTier'), ordinal,
                                       len(tagged), g['output_capacity']))
        shed_keys = {x['key'] for x in insertion}
        tagged = [None if is_a and x['key'] in shed_keys else (x, is_a) for x, is_a in tagged]
        swept_b = {slot[0]['key'] for slot in tagged if slot is not None and not slot[1]}
        remaining = [x for x in insertion if x['key'] not in swept_b]
        holes = [i for i, slot in enumerate(tagged) if slot is None]
        for i, x in zip(holes, remaining):
            tagged[i] = (x, False)
        tagged.extend((x, False) for x in remaining[len(holes):])
        tier = [None if slot is None else slot[0] for slot in tagged]
        trace.append(a_tests.event('drain', dict(kind='outputTier'), len(chunks),
                                   sum(x is not None for x in tier), g['output_capacity']))
        all_trace = a['a_trace'] + btrace + a['distribution_trace'] + trace
    failed = next((ev for ev in all_trace if ev['occupancy'] > ev['capacity']), None)
    bounded = (dict(kind='failed', event=failed) if failed else
               dict(kind='published', main=main, tier=tier + [None] * max(0, g['output_capacity'] - len(tier))))
    result = dict(finish_main=main, insertion=insertion, remaining_leaves=leaves,
                  remaining_b_tier=bcopy, raw_tier=tier, finish_trace=trace, bounded=bounded)
    if not failed:
        # Check against a separate newest-key map, independent of finish selection.
        winners = {x['key']: x for xs in f['inputs']['a_main'] + [f['inputs']['a_tier']] for x in xs if x is not None}
        for unit in f['inputs']['units']:
            winners.update((x['key'], x) for x in unit if x is not None)
        output = [x for xs in main for x in xs if x is not None] + [x for x in tier if x is not None]
        assert len(output) == len(winners) and {x['key']: x for x in output} == winners
        for ci, bucket in enumerate(main):
            population = sum(words[x['key']] % (d * u) == ci for x in winners.values())
            assert sum(x is not None for x in bucket) == min(64, population)
            assert all(words[x['key']] % (d * u) == ci for x in bucket if x is not None)
        assert sum(x is not None for x in tier) == sum(
            max(0, sum(words[x['key']] % (d * u) == ci for x in winners.values()) - 64) for ci in range(d * u))
    return result


def cases():
    out = []
    def add(name, f):
        f = copy.deepcopy(f)
        f.update(format='direct-job-finish-reference/0', expected=None)
        f['expected'] = copy.deepcopy(reference(f))
        out.append((name, f, 0))
        return f
    def mutate(name, f, change, code=1):
        m = copy.deepcopy(f)
        change(m)
        out.append((name, m, code))
    for name, f, code in a_tests.cases():
        if code == 0:
            add('A-' + name, f)
    for name, f, code in b_tests.cases():
        if code == 0 and f['geometry']['digit'] == 1:
            add('digit-one-' + name, f)
    for d in range(2, 9):
        for seed in range(4):
            rng = random.Random(d * 100 + seed)
            k = seed % 3
            n = (d - 1) * (1 << k)
            f = a_tests.make(d, k, [rng.randrange(0, 40) for _ in range(n)], tier=13, seed=seed)
            source_keys = [x['key'] for xs in f['inputs']['a_main'] + [f['inputs']['a_tier']] for x in xs if x]
            limit = max(source_keys, default=0) + 1
            new_keys = list(range(limit, limit + 90))
            current = {v['key']: v['word'] for v in f['words'] if v['family'] == 'current'}
            current.update((key, rng.randrange(d * (1 << k) * 7)) for key in new_keys)
            units = []
            for ui in range(3):
                keys = rng.sample(source_keys + new_keys, min(65, len(source_keys + new_keys)))
                unit = [rec(key, 10000 + ui * 1000 + key, bool(rng.randrange(2))) for key in keys]
                unit.insert(rng.randrange(len(unit) + 1), None)
                units.append(unit)
            f['inputs']['units'] = [[], *units, [None]]
            f['words'] = [v for v in f['words'] if v['family'] == 'old'] + [dict(family='current', key=key, word=word) for key, word in current.items()]
            add(f'generated-overlap-{d}-{seed}', f)
    for tombstone in [False, True]:
        for mode in ['direct', 'dfs']:
            d, k = (2, 0) if mode == 'direct' else (3, 2)
            # A home starts full; newer B key 64 sheds while stale A waits.
            lengths = [64] + [0] * ((d - 1) * (1 << k) - 1)
            f = a_tests.make(d, k, lengths, tier=1, concentrated=True)
            f['inputs']['units'] = [[rec(64, 999, tombstone)]]
            f['geometry'].update(output_capacity=2, insertion_capacity=2, copy_capacity=2)
            add(f'original-B-shed-{mode}-tombstone-{tombstone}', f)
    # Insertion and final drain exact/one-over controls with A's full home.
    base = a_tests.make(2, 0, [64], concentrated=True)
    base['inputs']['units'] = [[rec(1000+i) for i in range(3)]]
    base['words'] += [dict(family='current', key=1000+i, word=0) for i in range(3)]
    for output, insertion in [(3, 3), (2, 3), (2, 2), (0, 3)]:
        f = copy.deepcopy(base)
        f['geometry'].update(output_capacity=output, insertion_capacity=insertion, copy_capacity=max(3, output))
        add(f'insertion-drain-boundary-{output}-{insertion}', f)
    multi = a_tests.make(2, 1, [64, 64], seed=42)
    for entry in multi['words']:
        if entry['family'] == 'current':
            entry['word'] = entry['key'] // 64
    multi['inputs']['units'] = [[rec(1000+i) for i in range(4)]]
    multi['words'] += [dict(family='current', key=1000+i, word=i//2) for i in range(4)]
    for output, insertion in [(4, 4), (3, 3), (3, 4)]:
        f = copy.deepcopy(multi)
        f['geometry'].update(output_capacity=output, insertion_capacity=insertion, copy_capacity=4)
        add(f'multiple-source-check-boundary-{output}-{insertion}', f)
    # Surviving lane holes, zero output capacity, and configured widths >64.
    for capacity in [0, 1, 63, 64, 65, 128]:
        f = a_tests.make(2, 0, [1], tier=5, seed=23)
        f['geometry'].update(output_capacity=capacity, insertion_capacity=capacity, copy_capacity=capacity)
        add(f'configured-output-{capacity}', f)
    sample = add('mutation-control', base)
    mutate('wrong-finish-main-order', sample, lambda f: f['expected']['finish_main'].reverse())
    mutate('wrong-insertion-order', sample, lambda f: f['expected']['insertion'].reverse())
    mutate('wrong-full-payload', sample, lambda f: f['expected']['insertion'][0].update(value=42))
    mutate('wrong-tombstone', sample, lambda f: f['expected']['insertion'][0].update(tombstone=True))
    mutate('wrong-raw-tier-order', sample, lambda f: f['expected']['raw_tier'].reverse())
    mutate('wrong-remaining-B-tier', sample, lambda f: f['expected']['remaining_b_tier'][0].append(rec(999999)))
    mutate('wrong-remaining-leaves', sample, lambda f: f['expected']['remaining_leaves'][0].append(rec(999998)))
    mutate('wrong-trace-capacity', sample, lambda f: f['expected']['finish_trace'][0].update(capacity=999))
    mutate('wrong-trace-ordinal', sample, lambda f: f['expected']['finish_trace'][0].update(ordinal=999))
    mutate('wrong-published-padding', sample, lambda f: f['expected']['bounded']['tier'].__setitem__(-1, rec(999997)))
    mutate('bad-publication', sample, lambda f: f['expected'].update(bounded=dict(kind='failed', event=f['expected']['finish_trace'][0])))
    fail = next(f for _, f, _ in out if f['expected']['bounded']['kind'] == 'failed')
    mutate('wrong-first-failure', fail, lambda f: f['expected']['bounded']['event'].update(phase='publish'))
    mutate('bad-A-width', sample, lambda f: f['inputs']['a_main'][0].pop(), 2)
    mutate('duplicate-prefix-key', sample, lambda f: f['inputs']['units'][0].append(copy.deepcopy(f['inputs']['units'][0][0])), 2)
    mutate('duplicate-A-key', sample, lambda f: f['inputs']['a_tier'].append(copy.deepcopy(next(x for x in f['inputs']['a_main'][0] if x))), 2)
    mutate('missing-word', sample, lambda f: f['words'].pop(0), 2)
    mutate('bad-geometry', sample, lambda f: f['geometry'].update(output_homes=999), 2)
    mutate('wrong-evidence', sample, lambda f: f.update(evidence='native-differential'), 2)
    mutate('malformed-record', sample, lambda f: f['inputs']['units'][0][0].update(tombstone=1), 2)
    mutate('inconsistent-current-word', sample, lambda f: f['words'].append(dict(family='current', key=1000, word=999)), 2)
    return out


def run(directory):
    entries, paths = cases(), []
    for name, f, code in entries:
        path = directory / f'{name}.json'
        path.write_text(json.dumps(f))
        result = subprocess.run([str(ROOT/'.lake/build/bin/oracle'), '--direct-finish', str(path)],
                                text=True, capture_output=True, timeout=90)
        assert result.returncode == code, (name, code, result.returncode, result.stdout[:5000], result.stderr)
        lines = result.stdout.splitlines()
        assert len(lines) == 1, (name, result.stdout)
        payload = json.loads(lines[0])
        if code < 2:
            assert payload['comparison'] == ('pass' if code == 0 else 'fail'), (name, payload)
            assert payload['evidence'] == 'reference-regression', (name, payload)
        else:
            assert payload['o1'] == 'malformed', (name, payload)
        paths.append((path, code))
    representatives = [next(p for p, c in paths if c == code) for code in [2, 0, 1]]
    batch = subprocess.run([str(ROOT/'.lake/build/bin/oracle'), '--direct-finish', *map(str, representatives)],
                           text=True, capture_output=True, timeout=90)
    assert batch.returncode == 2 and len(batch.stdout.splitlines()) == 3
    counts = [sum(c == code for _, _, c in entries) for code in [0, 1, 2]]
    print(f'Complete direct reference regression: {len(entries)} passed ({counts[0]} matches, {counts[1]} mutations, {counts[2]} malformed); mixed batch exit 2')
    print('Evidence: independent reference regression only (no native execution).')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--keep', type=pathlib.Path)
    args = parser.parse_args()
    if args.keep:
        args.keep.mkdir(parents=True, exist_ok=True)
        run(args.keep)
    else:
        with tempfile.TemporaryDirectory(prefix='direct-job-finish-') as tmp:
            run(pathlib.Path(tmp))


if __name__ == '__main__':
    main()
