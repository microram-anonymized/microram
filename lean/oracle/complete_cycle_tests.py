#!/usr/bin/env python3
"""Empty/full initialization and at least two complete top rebuilds against Lean.

Uses the original dense hierarchy evaluator, 4-byte keys and payloads. No top
contents are skipped. The public API cases also check every call's dense state.
"""
import argparse
import concurrent.futures
import copy
import datetime
import hashlib
import json
import math
import pathlib
import subprocess
import time

HERE = pathlib.Path(__file__).resolve().parent
LEAN = HERE.parent
REPO = LEAN.parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=pathlib.Path, default=LEAN / '.lake/oracle/complete-cycle')
    parser.add_argument('--no-build', action='store_true')
    parser.add_argument('--no-generate', action='store_true')
    parser.add_argument('-j', type=int, default=4)
    args = parser.parse_args()
    if args.j < 1:
        parser.error('-j must be positive')
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    if not args.no_build:
        for script in ['build_hierarchy_dump.sh', 'build_api_dump.sh']:
            subprocess.run([str(HERE / script)], cwd=LEAN, check=True)
        subprocess.run(['lake', 'build', 'oracle', 'spec_tests.PublicApiReplay'], cwd=LEAN, check=True)
    cases = []
    for r0, fanouts in [(2, (4, 8)), (2, (4, 4, 2)), (2, (2,)), (4, (2,))]:
        prefix_accesses = 64 * r0
        period = prefix_accesses * math.prod(fanouts)
        capacity = 8 * period
        for full in [False, True]:
            for batch in [False, True]:
                name = 'hierarchy-' + '-'.join(map(str, fanouts))
                if len(fanouts) == 1:
                    name += '-r' + str(r0)
                name += ('-full' if full else '-empty') + ('-batch' if batch else '-scalar')
                options = ['--B', '8', '--fanouts', ','.join(map(str, fanouts)), '--D', '8',
                           '--r0', str(r0), '--K', '4', '--V', '4', '--sequential-keys',
                           '--keys', str(capacity), '--init', str(capacity if full else 0),
                           '--accesses', str(2 * period + prefix_accesses), '--view', '--sync-check']
                if batch:
                    options += ['--batch', '100', '--batch-vary', '--batch-lanes', '64', '--batch-scalar', '2']
                cases.append((name, 'hierarchy_dump', '--hierarchy', options, full))
    # All N keys are nonzero. Only the old numeric-bound premise is expected
    # to fail; native execution and every table/view comparison must succeed.
    cases.append(('hierarchy-4-8-full-nonzero', 'hierarchy_dump', '--hierarchy',
                  ['--B', '8', '--fanouts', '4,8', '--D', '8', '--r0', '2',
                   '--K', '4', '--V', '4', '--keys', '32768', '--key-bound', '32769',
                   '--init', '32768', '--accesses', '8320', '--view', '--sync-check'], True))
    for full in [False, True]:
        for width in [5, 64]:
            name = 'api-' + ('full' if full else 'empty') + '-w' + str(width)
            options = ['--cycles', '--rounds', '112', '--width', str(width)]
            if full:
                options += ['--full-init']
            cases.append((name, 'api_native_dump', '--api', options, full))

    def generate(case):
        name, binary, _, options, _ = case
        with (out / (name + '.native.log')).open('w') as log:
            subprocess.run([str(LEAN / '.lake/oracle-build' / binary), str(out / (name + '.json')), *options],
                           cwd=LEAN, stdout=log, stderr=subprocess.STDOUT, check=True)
        print('generated ' + name, flush=True)
    if not args.no_generate:
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.j) as pool:
            list(pool.map(generate, cases))

    def compare(item):
        name, mode, path = item
        proc = subprocess.run([str(LEAN / '.lake/build/bin/oracle'), mode, str(path)],
                              capture_output=True, text=True)
        try:
            report = json.loads(proc.stdout)
        except json.JSONDecodeError as exc:
            raise AssertionError((name, proc.returncode, proc.stderr[:1000])) from exc
        return name, proc.returncode, report

    def coverage(fixture, full, nonzero=False):
        cfg = fixture['config']
        assert cfg['selected'] is None and not cfg['skip_top_contents']
        assert cfg['key_bytes'] == 4 and cfg['user_value_bytes'] == 4 and cfg['value_bytes'] == 5
        period = cfg['load'] * cfg['carry1'] * math.prod(cfg['fanouts'])
        capacity = cfg['top_digit'] * period
        assert len(fixture['init']) == (capacity if full else 0)
        assert cfg['address_space'] == capacity and cfg['key_bound'] == capacity + int(nonzero)
        if nonzero:
            assert {r['key'] for r in fixture['init']} == set(range(1, capacity + 1))
        accesses = fixture['outcome']['accesses']
        cycles = accesses // period
        assert cycles >= 2, 'trace did not reach two top rebuilds'
        seed = cfg['top_digit'] if full else 0
        level = len(cfg['fanouts']) + 1
        tops = [t for t in fixture['tables'] if t['ident'][0] == level and t['ident'][1] > seed]
        assert [t['ident'][1] for t in tops] == list(range(seed + 1, seed + cycles + 1))
        assert all(t['main'] is not None and t['tier'] is not None for t in fixture['tables'])
        return {'capacity': capacity, 'initial_records': len(fixture['init']),
                'accesses': accesses, 'top_carry_period': period, 'completed_top_rebuilds': cycles,
                'levels': level, 'expected_numeric_bound_failure': nonzero}

    counts = {}
    for name, _, _, _, full in cases:
        counts[name] = coverage(json.loads((out / (name + '.json')).read_text()), full, name.endswith('-nonzero'))
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.j) as pool:
        results = list(pool.map(compare, [(n, mode, out / (n + '.json')) for n, _, mode, _, _ in cases]))
    for name, code, report in results:
        (out / (name + '.report.json')).write_text(json.dumps(report, indent=2) + '\n')
        if name.endswith('-nonzero'):
            assert code == 1 and report['failures'] == ['trace_premises.N'], (name, code, report)
            assert report['trace_premises']['N_check'] == 'fail'
        else:
            assert code == 0 and report['result'] == 'pass', (name, code, report)
        assert report['compared'] == report['tables'] and report['skipped_top'] == 0
        if name.startswith('api-'):
            assert report['extension']['result'] == 'pass' and report['extension']['api_calls'] == 896
        counts[name]['tables_compared'] = report['compared']
        counts[name]['state_result'] = 'pass'
        counts[name]['api_calls'] = report.get('extension', {}).get('api_calls', 0)
        print('PASS ' + name + (' (state/view match; numeric premise rejected as expected)' if name.endswith('-nonzero') else ''), flush=True)

    mutations = []
    mutdir = out / 'mutations'
    mutdir.mkdir(exist_ok=True)
    base = json.loads((out / 'hierarchy-4-8-full-scalar.json').read_text())
    def top(f):
        return next(t for t in reversed(f['tables']) if t['ident'][0] == 3)
    def first(f):
        return next(r for b in top(f)['main'] for r in b if r is not None)
    def mutate(name, source, change, mode='--hierarchy'):
        f = copy.deepcopy(source)
        change(f)
        path = mutdir / (name + '.json')
        path.write_text(json.dumps(f, separators=(',', ':')))
        mutations.append((name, mode, path))
    mutate('rebuilt-top-value', base, lambda f: first(f).__setitem__('value', first(f)['value'] ^ 1))
    mutate('rebuilt-top-key', base, lambda f: first(f).__setitem__('key', first(f)['key'] ^ 1))
    mutate('rebuilt-top-tombstone', base, lambda f: first(f).__setitem__('tombstone', True))
    mutate('rebuilt-top-lanes', base, lambda f: next(b for b in top(f)['main'] if any(r is not None for r in b)).reverse())
    mutate('rebuilt-top-tier', base, lambda f: top(f)['tier'].__setitem__(0, copy.deepcopy(first(f))))
    mutate('rebuilt-top-omitted', base, lambda f: top(f).__setitem__('main', None))
    api = json.loads((out / 'api-full-w5.json').read_text())
    mutate('api-retirement-disabled', api, lambda f: f['api'].__setitem__('settle_after_call', False), '--api')
    mutate('api-top-ordinal', api, lambda f: f['api']['calls'][-1].__setitem__('top_ordinal', 0), '--api')
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.j) as pool:
        negative = list(pool.map(compare, mutations))
    for name, code, report in negative:
        assert code in (1, 2), ('mutation accepted', name, report)
    (out / 'mutation-results.json').write_text(json.dumps(negative, indent=2) + '\n')
    sources = sorted(set(list((REPO / 'src').rglob('*.hpp')) + list((REPO / 'include').rglob('*.hpp')) +
                         list((LEAN / 'RebuildBound').rglob('*.lean')) + list((LEAN / 'spec_tests').rglob('*.lean')) +
                         list(HERE.glob('*.cpp')) + list(HERE.glob('*.py')) + list(HERE.glob('*.sh'))))
    hashes = {str(p.relative_to(REPO)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    manifest = json.dumps(hashes, indent=2) + '\n'
    (out / 'source-hashes.json').write_text(manifest)
    summary = {'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds'),
               'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=LEAN, text=True).strip(),
               'modified_checkout': bool(subprocess.check_output(['git', 'status', '--porcelain'], cwd=LEAN)),
               'source_manifest_sha256': hashlib.sha256(manifest.encode()).hexdigest(),
               'runs': counts, 'native_runs': len(cases), 'all_ok': True,
               'api_calls': sum(c['api_calls'] for c in counts.values()),
               'primitive_accesses': sum(c['accesses'] for c in counts.values()),
               'top_rebuilds': sum(c['completed_top_rebuilds'] for c in counts.values()),
               'tables_compared': sum(c['tables_compared'] for c in counts.values()),
               'skipped_tables': 0, 'mutations_rejected': len(negative),
               'seconds': round(time.monotonic() - start, 1),
               'scope': 'Smaller full-cycle configurations; original dense Lean hierarchy model; no geometry31 top-rebuild claim.'}
    (out / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2), flush=True)

if __name__ == '__main__':
    main()
