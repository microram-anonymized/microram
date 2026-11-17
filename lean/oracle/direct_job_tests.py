#!/usr/bin/env python3
"""Independent digit-one hand/model regression; this is NOT native differential evidence.

Run from the Lean project after `lake build oracle`:
    python3 oracle/direct_job_tests.py
Fixtures live only in a temporary directory; optional --keep DIR retains them.
"""
import argparse
import copy
import json
import pathlib
import random
import subprocess
import tempfile
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]


def rec(key, value=None, tombstone=False):
    return dict(key=key, value=key * 17 if value is None else value, tombstone=tombstone)


def fixture(units, capacity=64, k=0, digit=1, words=None, a_main=None, a_tier=None):
    u = 1 << k
    rs = [r for lanes in (a_main or []) + [a_tier or []] + units for r in lanes if r is not None]
    by_key = {r['key']: r['key'] % u for r in rs} if words is None else words
    return dict(format='direct-job-reference/0', evidence='reference-regression', geometry=dict(
        K=k, digit=digit, output_homes=digit*u, output_capacity=capacity,
        a_tier_capacity=0 if digit == 1 else 64, route_capacity=64,
        radix_capacity=64, insertion_capacity=capacity, copy_capacity=capacity,
        ranges=dict(kind='direct')), inputs=dict(a_main=a_main or [], a_tier=a_tier or [], units=units),
        words=[dict(family='current', key=key, word=word) for key, word in by_key.items()],
        expected=None)


def reference(f):
    """Direct newest-key map + independent occurrence walk (no Lean calls)."""
    g, inp = f['geometry'], f['inputs']
    if g['digit'] != 1:
        return dict(kind='rejected', reason='requiresLaterPhases')
    units = inp['units']
    latest = {}
    for ui, unit in enumerate(units):
        for lane, r in enumerate(unit):
            if r is not None:
                latest[r['key']] = (ui, lane)
    words = {w['key']: w['word'] for w in f['words'] if w['family'] == 'current'}
    main = [[] for _ in range(1 << g['K'])]
    residual_units = [[] for _ in units]
    for ui, unit in enumerate(units):
        for lane, r in enumerate(unit):
            if r is None or latest[r['key']] != (ui, lane):
                continue
            home = words[r['key']] % len(main)
            if len(main[home]) < 64:
                main[home].append(r)
            else:
                residual_units[ui].append(r)
    tier = []
    for ordinal, chunk in enumerate(residual_units):
        tier.extend(chunk)
        if len(tier) > g['output_capacity']:
            return dict(kind='failed', event=dict(phase='produceB', site=dict(kind='outputTier'),
                ordinal=ordinal, occupancy=len(tier), capacity=g['output_capacity']))
    return dict(kind='published', main=main, tier=tier)


def cases():
    out = []

    def add(name, f):
        f['expected'] = copy.deepcopy(reference(f))
        out.append((name, f, 0))
        return f

    def mutate(name, f, change, code=1):
        m = copy.deepcopy(f)
        change(m)
        out.append((name, m, code))

    empty = add('empty', fixture([]))
    for population in [0, 1, 63, 64, 65, 128, 129, 193]:
        add(f'population-{population}', fixture([[rec(i) for i in range(population)]]))
    excess64 = add('excess64', fixture([[rec(i) for i in range(128)]]))
    excess65 = add('excess65', fixture([[rec(i) for i in range(129)]]))
    add('configured-capacity65', fixture([[rec(i) for i in range(129)]], capacity=65))
    add('configured-capacity31-exact', fixture([[rec(i) for i in range(95)]], capacity=31))
    add('configured-capacity31-overflow', fixture([[rec(i) for i in range(96)]], capacity=31))
    add('tombstone-to-value-replacement', fixture([[rec(7, 10, True)], [], [rec(7, 20, False)]]))
    add('capacity-zero-full-main', fixture([[rec(i) for i in range(64)]], capacity=0))
    add('capacity-zero-first-excess', fixture([[rec(i) for i in range(65)]], capacity=0))
    distributed = add('distributed-excess-source-order', fixture(
        [[rec(i) for i in range(130)], [], [rec(i) for i in range(130, 192)]], k=1))
    add('distributed-excess65', fixture([[rec(i) for i in range(193)]], k=1))
    holes = add('holes-empty-cleared-units-versions-tombstones', fixture([
        [None, rec(1, 10), rec(2, 20), None], [], [rec(1, 30), None],
        [None, rec(1, 40, True), rec(3, 50)], [None]], k=1))
    ordinal = add('first-failure-ordinal3', fixture([
        [rec(i) for i in range(64)], [], [rec(i) for i in range(64, 100)],
        [None] + [rec(i) for i in range(100, 129)], []]))
    add('cleared-unit-keeps-first-failure-ordinal', fixture([
        [rec(i, 1) for i in range(64)], [None], [rec(i, 2) for i in range(64)],
        [rec(i) for i in range(64, 129)]]))
    repeated = add('consistent-repeat-word', fixture([[rec(1, 1)], [rec(1, 2)]]))
    repeated['words'].append(copy.deepcopy(repeated['words'][0]))
    wide_words = fixture([[rec(2**80+7, 2**96+9), None, rec(5)]], k=1,
        words={2**80+7: 2**130+1, 5: 2**100})
    add('arbitrary-precision-keys-values-words', wide_words)
    later = fixture([[rec(7)]], digit=2, a_main=[[None]*64])
    add('later-digit-explicit-rejection', later)
    placement = fixture([], digit=2, k=1, a_main=[[rec(8)]+[None]*63, [None]*64])
    placement['words'].append(dict(family='old', key=8, word=0))
    add('later-digit-valid-A-placement', placement)
    add('digit-one-large-U-direct-without-pool', fixture([[rec(i) for i in range(145)]], k=4))
    dfs = fixture([[rec(i) for i in range(145)]], k=3, digit=2, a_main=[[None]*64 for _ in range(8)])
    dfs['geometry']['ranges'] = dict(kind='dfs', index_bits=2, range_bits=2, pool_capacity=320)
    add('valid-dfs-geometry-later-digit-rejection', dfs)

    for seed in range(16):
        rng = random.Random(seed)
        units = []
        for _ in range(rng.randrange(2, 6)):
            keys = rng.sample(range(200), rng.randrange(0, 90))
            lanes = [rec(key, rng.randrange(1 << 24), bool(rng.randrange(2))) for key in keys]
            for _ in range(rng.randrange(4)):
                lanes.insert(rng.randrange(len(lanes)+1), None)
            units.append(lanes)
        add(f'random-{seed}', fixture(units, capacity=rng.choice([0, 1, 32, 64, 65, 128]), k=seed % 3))

    mutate('wrong-full-value', holes, lambda m: m['expected']['main'][1][0].update(value=999))
    mutate('wrong-tombstone', holes, lambda m: m['expected']['main'][1][0].update(tombstone=False))
    mutate('wrong-home-order', holes, lambda m: m['expected']['main'].reverse())
    mutate('wrong-within-home-order', excess64, lambda m: m['expected']['main'][0].reverse())
    mutate('wrong-tier-order', distributed, lambda m: m['expected']['tier'].reverse())
    mutate('missing-tier-record', excess64, lambda m: m['expected']['tier'].pop())
    for field, value in [('ordinal', 2), ('occupancy', 130), ('capacity', 65), ('phase', 'finish')]:
        mutate(f'wrong-failure-{field}', ordinal, lambda m, field=field, value=value: m['expected']['event'].update({field: value}))
    mutate('wrong-failure-site', excess65, lambda m: m['expected']['event']['site'].update(kind='bTier'))
    mutate('wrong-verdict', excess65, lambda m: m.update(expected=copy.deepcopy(empty['expected'])))

    mutate('missing-current-word', holes, lambda m: m['words'].clear(), 2)
    mutate('inconsistent-key-word', repeated, lambda m: m['words'].append(dict(family='current', key=1, word=9)), 2)
    mutate('duplicate-within-unit', holes, lambda m: m['inputs']['units'][0].append(rec(2)), 2)
    mutate('A-main-wrong-width', later, lambda m: m['inputs']['a_main'][0].pop(), 2)
    mutate('A-main-wrong-count', later, lambda m: m['inputs']['a_main'].clear(), 2)
    mutate('invalid-old-placement', placement, lambda m: m['words'][-1].update(word=1), 2)
    mutate('missing-old-word', placement, lambda m: m['words'].pop(), 2)
    mutate('duplicate-A-key', placement, lambda m: m['inputs']['a_tier'].append(rec(8)), 2)
    mutate('invalid-digit', empty, lambda m: m['geometry'].update(digit=0), 2)
    mutate('invalid-home-count', empty, lambda m: m['geometry'].update(output_homes=2), 2)
    mutate('invalid-A-capacity-digit-one', empty, lambda m: m['geometry'].update(a_tier_capacity=1), 2)
    mutate('invalid-insertion-capacity', empty, lambda m: m['geometry'].update(insertion_capacity=63), 2)
    mutate('invalid-copy-capacity', empty, lambda m: m['geometry'].update(copy_capacity=63), 2)
    mutate('invalid-direct-ranges', dfs, lambda m: m['geometry'].update(ranges=dict(kind='direct')), 2)
    mutate('invalid-dfs-pool', dfs, lambda m: m['geometry']['ranges'].update(pool_capacity=319), 2)
    mutate('invalid-dfs-cover', dfs, lambda m: m['geometry']['ranges'].update(range_bits=1), 2)
    mutate('malformed-unit-lane', holes, lambda m: m['inputs']['units'][0].append(3), 2)
    mutate('malformed-negative-word', repeated, lambda m: m['words'][0].update(word=-1), 2)
    mutate('malformed-value-type', holes, lambda m: m['inputs']['units'][0][1].update(value='deadbeef'), 2)
    mutate('malformed-tombstone-type', holes, lambda m: m['inputs']['units'][0][1].update(tombstone=0), 2)
    mutate('malformed-publication-home-count', holes, lambda m: m['expected']['main'].pop(), 2)
    mutate('malformed-evidence-native', empty, lambda m: m.update(evidence='native-differential'), 2)
    return out


def run(directory):
    started = time.monotonic()
    entries = cases()
    paths = []
    for name, f, expected_code in entries:
        path = directory / f'{name}.json'
        path.write_text(json.dumps(f))
        result = subprocess.run([str(ROOT/'.lake/build/bin/oracle'), '--direct', str(path)],
            text=True, capture_output=True, timeout=30)
        lines = result.stdout.splitlines()
        assert result.returncode == expected_code, (name, expected_code, result.returncode, result.stdout, result.stderr)
        assert len(lines) == 1, (name, result.stdout)
        payload = json.loads(lines[0])
        if expected_code < 2:
            assert payload['comparison'] == ('pass' if expected_code == 0 else 'fail'), (name, payload)
            assert payload['evidence'] == 'reference-regression', (name, payload)
        else:
            assert payload['o1'] == 'malformed', (name, payload)
        paths.append((path, expected_code))
    # Put malformed first and mismatch last: verifies max exit code differs from last.
    representatives = [next(p for p, c in paths if c == code) for code in [2, 0, 1]]
    batch = subprocess.run([str(ROOT/'.lake/build/bin/oracle'), '--direct', *map(str, representatives)],
        text=True, capture_output=True, timeout=30)
    assert batch.returncode == 2 and len(batch.stdout.splitlines()) == 3
    totals = {code: sum(c == code for _, _, c in entries) for code in [0, 1, 2]}
    print(f"direct reference regression: {len(entries)} cases passed ({totals[0]} accepted, {totals[1]} mismatches, {totals[2]} malformed), plus mixed batch exit 2")
    print(f'Elapsed: {time.monotonic() - started:.2f} seconds')
    print('Evidence: hand/model reference regression only (no native execution).')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--keep', type=pathlib.Path, help='retain generated reference fixtures here')
    args = parser.parse_args()
    if args.keep:
        args.keep.mkdir(parents=True, exist_ok=True)
        run(args.keep)
    else:
        with tempfile.TemporaryDirectory(prefix='direct-job-reference-') as tmp:
            run(pathlib.Path(tmp))


if __name__ == '__main__':
    main()
