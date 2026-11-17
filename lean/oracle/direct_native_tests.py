#!/usr/bin/env python3
"""Export real native jobs, compare using existing --direct-finish, mutate evidence.

No expected reference results or intermediate reference states are generated here.
Native failures compare phase/check class; logical ordinal/occupancy remain open.
"""
import argparse
import copy
import json
import pathlib
import subprocess
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
LEAN = HERE.parent
REPO = LEAN.parent


def build_dumper(path):
    path.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(['/usr/bin/c++', '-O2', '-UNDEBUG', '-std=c++17', '-march=native',
                    '-mno-avx512vp2intersect', '-Wno-stringop-overread',
                    '-Wno-stringop-overflow', f'-I{REPO / "include"}', f'-I{REPO}',
                    str(HERE / 'direct_native_dump.cpp'), '-o', str(path), '-pthread'], check=True)


def compare(oracle, paths, expected_code=0):
    result = subprocess.run([str(oracle), '--direct-finish', *map(str, paths)],
                            text=True, capture_output=True)
    reports = [json.loads(line) for line in result.stdout.splitlines() if line.strip()]
    if result.returncode != expected_code or len(reports) != len(paths):
        raise AssertionError((result.returncode, expected_code, result.stderr, reports[:1]))
    if expected_code == 0:
        bad = [r for r in reports if r.get('comparison') != 'pass' or r.get('snapshots') != 'pass']
        if bad:
            raise AssertionError([(r['file'], r.get('comparison'), r.get('snapshots')) for r in bad])
    return reports


def run(args, out):
    dumper = args.dumper or LEAN / '.lake/oracle-build/direct_native_dump'
    if not args.dumper:
        build_dumper(dumper)
    oracle = LEAN / '.lake/build/bin/oracle'
    if not oracle.is_file():
        raise RuntimeError('Build the existing oracle with lake build oracle first')
    cases = []
    # These eight K4 rows are exactly the selected native probability inventory.
    for digit in range(1, 9):
        cases += [(f'selected-d{digit}-versions', dict(digit=digit, flushes=8,
                    fresh=192, older=32 if digit > 1 else 0,
                    **{'old-tier': 5 if digit > 1 else 0}, versions=1)),
                  (f'selected-d{digit}-empty', dict(digit=digit, flushes=8, fresh=0)),
                  (f'selected-d{digit}-b-exact64', dict(digit=digit, flushes=8,
                                                       fresh=128, target=0)),
                  (f'selected-d{digit}-b-over65', dict(digit=digit, flushes=8,
                                                      fresh=129, target=0))]
    # Boundary controls stay separate from selected probability rows.
    cases += [ ('direct-a', dict(digit=2, flushes=2, older=40, **{'old-tier': 9}, versions=1)),
               ('spread-exact64', dict(digit=3, flushes=8, fresh=192, target=0, spread=2)),
               ('spread-over65', dict(digit=3, flushes=8, fresh=193, target=0, spread=2)),
               ('output128-exact', dict(flushes=8, tier=2, fresh=192, target=0)),
               ('output128-over', dict(flushes=8, tier=2, fresh=193, target=0)),
               ('output512-configured', dict(flushes=8, tier=8, fresh=128, target=0)),
               ('radix-exact64', dict(digit=5, flushes=8, fresh=0, older=128, target=0)),
               ('radix-over65', dict(digit=5, flushes=8, fresh=0, older=129, target=0)),
               ('route-exact64', dict(digit=8, flushes=8, fresh=0, older=192, target=0)),
               ('route-over65', dict(digit=8, flushes=8, fresh=0, older=193, target=0)),
               ('insertion-exact64', dict(digit=2, flushes=8, older=128, fresh=64, target=0, spread=2)),
               ('insertion-over65', dict(digit=2, flushes=8, older=128, fresh=65, target=0, spread=2)),
               ('drain-exact64', dict(digit=2, flushes=8, older=64, fresh=64, target=0)),
               ('drain-over65', dict(digit=2, flushes=8, older=64, fresh=65, target=0)),
               ('a-range-exact64', dict(digit=3, flushes=8, fresh=0, older=128, target=0)),
               ('a-range-over65', dict(digit=3, flushes=8, fresh=0, older=128, **{'old-tier':1}, target=0))]
    fixtures = []
    for name, config in cases:
        path = out / (name + '.json')
        command = [str(dumper), str(path)]
        for k, v in config.items():
            command += ['--' + k, str(v)]
        subprocess.run(command, check=True)
        if name.startswith('selected-'):
            geometry = json.loads(path.read_text())['geometry']
            assert geometry['K'] == 4 and geometry['output_capacity'] == 64
            assert all(geometry[field] == 64 for field in
                       ('route_capacity', 'radix_capacity', 'insertion_capacity', 'copy_capacity'))
        fixtures.append(path)
    reports = compare(oracle, fixtures)
    (out/'native_reports.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in reports))
    failures = { (json.loads(p.read_text())['expected'].get('phase'),
                  json.loads(p.read_text())['expected'].get('site', {}).get('kind'))
                 for p in fixtures if json.loads(p.read_text())['expected']['kind'] == 'failed' }
    assert {('produceB', 'bTier'), ('produceB', 'outputTier'), ('prepareA', 'route'),
            ('prepareA', 'radix'), ('distributeA', 'dfs'), ('finish', 'insertion'),
            ('drain', 'outputTier')} <= failures
    print(f'{len(reports)} native comparisons passed (exact full lanes and exported boundaries)', flush=True)
    base = json.loads((out / 'selected-d3-versions.json').read_text())
    tierbase = json.loads((out / 'selected-d2-b-exact64.json').read_text())
    failure = json.loads((out / 'selected-d2-b-over65.json').read_text())
    mutations = []
    def mutate(name, fixture, change):
        f = copy.deepcopy(fixture)
        change(f)
        p = out / (name + '.json')
        p.write_text(json.dumps(f))
        mutations.append(p)
    def first_main(f):
        return next(r for b in f['expected']['main'] for r in b if r is not None)
    mutate('mutation-value', base, lambda f: first_main(f).__setitem__('value', first_main(f)['value'] ^ 1))
    mutate('mutation-tombstone', base, lambda f: first_main(f).__setitem__('tombstone', not first_main(f)['tombstone']))
    def move_lane(f):
        b = next(b for b in f['expected']['main'] if any(r is not None for r in b) and any(r is None for r in b))
        i = next(i for i,r in enumerate(b) if r is not None)
        j = next(i for i,r in enumerate(b) if r is None)
        b[i], b[j] = b[j], b[i]
    mutate('mutation-lane', base, move_lane)
    mutate('mutation-b-tier-order', tierbase, lambda f: f['observations']['b_tier'].reverse())
    mutate('mutation-failure-class', failure, lambda f: f['expected']['site'].__setitem__('kind', 'outputTier'))
    mutate('mutation-publication', failure, lambda f: f['expected'].__setitem__('kind','published'))
    mutation_reports = compare(oracle, mutations, 1)
    for path, report in zip(mutations, mutation_reports):
        if report.get('comparison') != 'fail':
            raise AssertionError('mutation was not detected: ' + str(path))
    print(f'{len(mutations)} native observation mutations detected', flush=True)
    malformed = []
    for name, change in [('missing-word', lambda f: f.__setitem__('words', [])),
                         ('wrong-evidence', lambda f: f.__setitem__('evidence','generated-answer')),
                         ('bad-geometry', lambda f: f['geometry'].__setitem__('output_homes',1))]:
        f = copy.deepcopy(base); change(f)
        path = out / (name + '.json');path.write_text(json.dumps(f));malformed.append(path)
    compare(oracle, malformed, 2)
    compare(oracle, [fixtures[0], mutations[0], malformed[0]], 2)
    print(f'{len(malformed)} malformed rejections and mixed-batch exit code passed', flush=True)
    for options in [ ['--digit','1','--older','1'], ['--old-tier','65'], ['--digit','0'] ]:
        result = subprocess.run([str(dumper), str(out/'invalid.json'), *options], capture_output=True)
        if result.returncode != 2:
            raise AssertionError(('invalid exporter input accepted', options, result.returncode))
    (out/'summary.json').write_text(json.dumps({'native_matches': len(fixtures),
        'mutations_detected': len(mutations), 'malformed_rejections': len(malformed),
        'selected_K': 4, 'selected_digits': list(range(1,9)),
        'failure_identity': 'phase and check class only',
        'evidence': 'regression, not native correspondence proof'}, indent=2)+'\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--keep', type=pathlib.Path)
    parser.add_argument('--dumper', type=pathlib.Path, help='Reuse a freshly compiled exporter')
    args = parser.parse_args()
    if args.keep:
        args.keep.mkdir(parents=True, exist_ok=True)
        run(args, args.keep.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix='direct-native-') as tmp:
            run(args, pathlib.Path(tmp))
