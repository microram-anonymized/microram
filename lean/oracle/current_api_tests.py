#!/usr/bin/env python3
"""Native geometry31 and public API state replay, including negative controls.

Default: rebuild exporters/oracle, regenerate 7 runs, compare, mutate evidence.
Full geometry31 generation uses substantial RAM (roughly 120 GiB per engine).
--small-only runs the four small public API cases. --no-generate reuses fixtures;
use it only with evidence freshly generated from this checkout.
"""
import argparse
import concurrent.futures
import copy
import datetime
import hashlib
import json
import pathlib
import subprocess
import time

HERE = pathlib.Path(__file__).resolve().parent
LEAN = HERE.parent


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out', type=pathlib.Path, default=LEAN / '.lake/oracle/current-api')
    ap.add_argument('--no-build', action='store_true')
    ap.add_argument('--no-generate', action='store_true')
    ap.add_argument('--small-only', action='store_true')
    ap.add_argument('-j', type=int, default=4)
    args = ap.parse_args()
    if args.j < 1:
        ap.error('-j must be positive')
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    if not args.no_build:
        for script in ['build_api_dump.sh', 'build_hierarchy_dump.sh']:
            subprocess.run([str(HERE / script)], cwd=LEAN, check=True)
        subprocess.run(['lake', 'build', 'oracle', 'spec_tests.SelectedReplay',
                        'spec_tests.PublicApiReplay'], cwd=LEAN, check=True)
    oracle = LEAN / '.lake/build/bin/oracle'
    api = LEAN / '.lake/oracle-build/api_native_dump'
    hierarchy = LEAN / '.lake/oracle-build/hierarchy_dump'
    cases = [(f'api-w{w}', '--api', api, ['--rounds', '56', '--width', str(w)])
             for w in (1, 5, 16, 64)]
    if not args.small_only:
        cases += [('api-geometry31', '--api', api, ['--geometry31', '--rounds', '56', '--width', '5'])]
        for batch in (False, True):
            options = ['--selected', 'geometry31', '--V', '1', '--accesses', '70000',
                       '--keys', '1500', '--view']
            if batch:
                options += ['--batch', '40', '--batch-vary', '--batch-scalar', '2']
            cases.append(('geometry31-' + ('batch' if batch else 'scalar'), '--geometry31', hierarchy, options))
    if not args.no_generate:
        def generate(case):
            name, _, binary, options = case
            with (out / (name + '.native.log')).open('w') as log:
                subprocess.run([str(binary), str(out / (name + '.json')), *options],
                               cwd=LEAN, stdout=log, stderr=subprocess.STDOUT, check=True)
            print('generated ' + name, flush=True)
        # At most two full-size native allocations simultaneously.
        with concurrent.futures.ThreadPoolExecutor(max_workers=min(2, args.j)) as pool:
            list(pool.map(generate, cases))

    def compare(item):
        name, mode, path = item
        proc = subprocess.run([str(oracle), mode, str(path)], capture_output=True, text=True)
        try:
            report = json.loads(proc.stdout)
        except json.JSONDecodeError as exc:
            raise AssertionError((name, proc.returncode, proc.stdout[:500], proc.stderr[:500])) from exc
        return name, proc.returncode, report

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.j) as pool:
        results = list(pool.map(compare, [(n, m, out / (n + '.json')) for n, m, _, _ in cases]))
    reports = {}
    for name, code, report in results:
        (out / (name + '.report.json')).write_text(json.dumps(report, indent=2) + '\n')
        assert code == 0 and report['result'] == 'pass', (name, code, report)
        assert report['extension']['result'] == 'pass' and report['compared'] > 0
        if 'geometry31' in name:
            assert report['extension']['exact_sparse_top_snapshots'] == 3
            assert report['tables'] == report['compared'] + 2
        else:
            assert report['tables'] == report['compared'] and report['skipped_top'] == 0
        if name.startswith('api-'):
            assert report['extension']['api_calls'] == 448
            assert report['extension']['api_probe_groups'] > 0
        reports[name] = report
        print('PASS ' + name, flush=True)

    # The ordinary hierarchy entry point must not silently omit the extensions.
    entrypoints = [('api-w5', '--hierarchy', out / 'api-w5.json')]
    if not args.small_only:
        entrypoints.append(('api-geometry31', '--hierarchy', out / 'api-geometry31.json'))
    for name, code, report in map(compare, entrypoints):
        assert code == 0 and report['extension'] == reports[name]['extension'], (name, report)

    base = json.loads((out / 'api-w5.json').read_text())
    mutations = []
    mutdir = out / 'mutations'
    mutdir.mkdir(exist_ok=True)

    def mutate(name, fixture, change, mode='--api'):
        fx = copy.deepcopy(fixture)
        change(fx)
        path = mutdir / (name + '.json')
        path.write_text(json.dumps(fx, separators=(',', ':')))
        mutations.append((name, mode, path))

    def callback(f):
        return next(c for c in f['api']['calls'] if c['kind'] == 'callback')

    def batch(f):
        return next(c for c in f['api']['calls'] if c['kind'] == 'batch' and len(c['groups']) > 1)

    def dense(f):
        return next(c for c in f['api']['calls'] if any(r is not None for r in c['current']))

    def live(bucket):
        return next(r for r in bucket if r is not None)

    mutate('callback-input', base, lambda f: callback(f).__setitem__('input', callback(f)['input'] ^ 1))
    mutate('callback-presence', base, lambda f: callback(f).__setitem__('found', not callback(f)['found']))
    mutate('callback-count', base, lambda f: callback(f).__setitem__('invocations', 0))
    mutate('callback-exception', base, lambda f: callback(f).__setitem__('exception', True))
    mutate('callback-return', base, lambda f: callback(f).__setitem__('returned', not callback(f)['returned']))
    mutate('callback-destination', base, lambda f: next(c for c in f['api']['calls']
        if c['kind'] == 'callback' and c['mutable_key'] and not c['throws']).__setitem__('destination', 9999))
    mutate('group-missing', base, lambda f: batch(f)['groups'].pop())
    mutate('group-width', base, lambda f: batch(f)['groups'][0].__setitem__(1, batch(f)['groups'][0][1] + 1))
    mutate('batch-global-presence', base, lambda f: batch(f).__setitem__('found_output', not batch(f)['found_output']))
    mutate('width-metadata', base, lambda f: f['api'].__setitem__('width', 6))
    mutate('position', base, lambda f: dense(f).__setitem__('position', 0))
    mutate('current-value', base, lambda f: live(dense(f)['current']).__setitem__('value', 123))

    def swap_lane(f):
        b = dense(f)['current']
        i = next(i for i, r in enumerate(b) if r is not None)
        k = next(i for i, r in enumerate(b) if r is None)
        b[i], b[k] = b[k], b[i]
    mutate('current-lane-swap', base, swap_lane)
    mutate('hierarchy-current', base, lambda f: live(dense(f)['current']).__setitem__('value', 123), '--hierarchy')
    mutate('current-missing', base, lambda f: dense(f).__delitem__('current'))
    mutate('calls-empty', base, lambda f: f['api'].__setitem__('calls', []))
    mutate('calls-truncated', base, lambda f: f['api']['calls'].pop())
    mutate('primitive-kind', base, lambda f: f['ops'][0].__setitem__('op', 'read'))
    mutate('primitive-value', base, lambda f: f['ops'][0].__setitem__('value', 255))
    mutate('partial-value', base, lambda f: live(next(c['partial'] for c in f['api']['calls']
        if any(r is not None for r in c['partial']))).__setitem__('value', 123))
    mutate('unit-value', base, lambda f: live(f['units'][0]['units'][0]).__setitem__('value', 123))
    mutate('table-lane', base, lambda f: live(next(b for t in f['tables'] for b in (t['main'] or [])
        if any(r is not None for r in b))).__setitem__('value', 123))

    if not args.small_only:
        geo = json.loads((out / 'api-geometry31.json').read_text())
        def top(f):
            return next(t for t in f['sparse_top'] if t['main'])
        mutate('top-value', geo, lambda f: live(top(f)['main'][0][1]).__setitem__('value', 999))
        mutate('top-lane', geo, lambda f: top(f)['main'][0][1].reverse())
        mutate('top-bucket', geo, lambda f: top(f)['main'][0].__setitem__(0, 2**26))
        mutate('top-record-dropped', geo, lambda f: top(f)['main'].pop())
        mutate('top-scan-coverage', geo, lambda f: top(f).__setitem__('scanned_buckets', 2**26-1))
        mutate('top-tier', geo, lambda f: top(f)['tier'].__setitem__(0, copy.deepcopy(live(top(f)['main'][0][1]))))
        mutate('top-final-missing', geo, lambda f: f['sparse_top'].pop())
        mutate('hierarchy-top', geo, lambda f: f.__setitem__('sparse_top', []), '--hierarchy')
        mutate('top-evidence-empty', geo, lambda f: f.__setitem__('sparse_top', []))
        mutate('geometry31-label', geo, lambda f: f['config'].__setitem__('selected', 'half'))
        mutate('geometry31-fanout', geo, lambda f: f['config']['fanouts'].__setitem__(0, 8))
        mutate('geometry31-init-drain', geo, lambda f: f['shapes']['init'].__setitem__('drain_pages', 4))
        mutate('geometry31-horizon', geo, lambda f: f['config'].__setitem__('horizon', 2**31))
        mutate('geometry31-key-bound', geo, lambda f: f['config'].__setitem__('key_bound', 2**31+1))
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.j) as pool:
        negative = list(pool.map(compare, mutations))
    for name, code, report in negative:
        assert code in (1, 2), ('mutation accepted', name, report)
    repo = LEAN.parent
    # Include the uncommitted oracle, trusted model, native headers and exporter
    # contents: HEAD alone would not identify a run from a modified checkout.
    sources = sorted(set(list((repo / 'include').rglob('*.hpp')) +
                         list((repo / 'include').rglob('*.h')) +
                         list((repo / 'src').rglob('*.hpp')) +
                         list((repo / 'src').rglob('*.h')) +
                         list((LEAN / 'RebuildBound').rglob('*.lean')) +
                         list((LEAN / 'spec_tests').rglob('*.lean')) +
                         list(HERE.glob('*.cpp')) + list(HERE.glob('*.sh')) +
                         list(HERE.glob('*.py'))))
    hashes = {str(p.relative_to(repo)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    (out / 'source-hashes.json').write_text(json.dumps(hashes, indent=2) + '\n')
    summary = {'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds'),
               'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=LEAN, text=True).strip(),
               'modified_checkout': bool(subprocess.check_output(['git', 'status', '--porcelain'], cwd=LEAN)),
               'source_manifest_sha256': hashlib.sha256((out / 'source-hashes.json').read_bytes()).hexdigest(),
               'cases': list(reports), 'native_runs': len(reports),
               'api_calls': sum(r['extension']['api_calls'] for r in reports.values()),
               'primitive_accesses': sum(r['accesses'] for r in reports.values()),
               'published_tables': sum(r['tables'] for r in reports.values()),
               'dense_model_tables': sum(r['compared'] for r in reports.values()),
               'sparse_top_snapshots': sum(r['extension']['exact_sparse_top_snapshots'] for r in reports.values()),
               'mutations_rejected': len(negative), 'seconds': round(time.monotonic()-start, 1),
               'all_ok': True,
               'limits': ['sparse geometry31 initializer: 1..32 initial records',
                          'no geometry31 top replacement/overflow exercised',
                          'one-byte API payloads, 64-bit keys, inline executor, VP2INTERSECT disabled',
                          'sparse evaluator tested against dense model, not generally proved equivalent',
                          'no universal native correspondence proof']}
    (out / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    (out / 'mutation-results.json').write_text(json.dumps(negative, indent=2) + '\n')
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == '__main__':
    main()
