#!/usr/bin/env python3
"""Driver: compare model_top.py with the engine on every fixture of a
directory and print the match counts, the breakdown and the coverage counters.

    run_top.py [DIR] [--detail]
"""
import glob, json, os, sys
from collections import Counter
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
WORK = os.environ.get('ORACLE_TOP_WORK', os.path.join(
    os.path.dirname(os.path.dirname(HERE)), '.lake', 'oracle', 'fixtures-top'))
sys.dont_write_bytecode = True
sys.path.insert(0, HERE)
import model_top as m


def one(path):
    f = m.load(path)
    ok, detail, res = m.compare(f)
    g = f['geometry']
    out = f['outputs']
    return {
        'file': os.path.basename(path), 'ok': ok, 'detail': detail,
        'D': g['D'], 'T': g['T'], 'U': g['U'], 'rho': g['range_bits'],
        'I': g['range_index_bits'], 'dfs': g['dfs'], 'S_R': g['r_pages'],
        'bt_pages': g['b_tier_pages'], 'ms_pages': g['merge_stash_pages'],
        'out_tier_pages': g['out_tier_pages'],
        'verdict': out['verdict'], 'kind': out['kind'],
        'engine_main': len(out['main']), 'engine_tier': len(out['tier']),
        'counters': dict(res.counters),
        'inputs': {k: len(v) for k, v in f['inputs'].items()},
        'R_page1': any(x['page'] >= 1 for x in f['inputs']['R']),
        'R_gt64': len(f['inputs']['R']) > 64,
        'Bt_pages_used': len({x['page'] for x in f['inputs']['B_tier']}),
        'Bt_gt64': len(f['inputs']['B_tier']) > 64,
    }


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    d = args[0] if args else os.path.join(WORK, 'fx')
    files = sorted(p for p in glob.glob(os.path.join(d, 'f*.json')))
    with Pool(32) as pool:
        rows = pool.map(one, files, chunksize=4)
    n = len(rows)
    ok = sum(r['ok'] for r in rows)
    succ = [r for r in rows if r['verdict'] == 'success']
    fail = [r for r in rows if r['verdict'] == 'failure']
    print('fixtures: %d   model == engine: %d   mismatches: %d' % (n, ok, n - ok))
    print('lane-exact on success: %d/%d   verdict+kind on failure: %d/%d' % (
        sum(r['ok'] for r in succ), len(succ), sum(r['ok'] for r in fail), len(fail)))
    if '--detail' in sys.argv or ok != n:
        for r in rows:
            if not r['ok']:
                print('MISMATCH', r['file'], r['detail'])
    print('\nby D (fixtures / success / failures):')
    for D in (1, 2, 4, 8):
        rs = [r for r in rows if r['D'] == D]
        print('  D=%d  %4d  %4d  %4d   failures by kind: %s' % (
            D, len(rs), sum(r['verdict'] == 'success' for r in rs),
            sum(r['verdict'] == 'failure' for r in rs),
            dict(Counter(r['kind'] for r in rs if r['verdict'] == 'failure'))))
    print('\nfailure kinds:', dict(Counter(r['kind'] for r in fail)))
    geoms = Counter((r['T'], r['D'], r['U'], r['rho'], r['I'], r['S_R'], r['dfs'],
                     r['bt_pages'], r['ms_pages'], r['out_tier_pages']) for r in rows)
    print('\ngeometries (T, D, U, rho, I, S_R, dfs, Btier pages, merge-stash pages, out-tier pages): fixtures')
    for k, v in sorted(geoms.items()):
        print('  ', k, v)
    cov = Counter()
    for r in rows:
        for k, v in r['counters'].items():
            if v:
                cov[k] += 1
    print('\ncoverage: fixtures with a nonzero effect (of %d; counters of a failing run stop at its failure)' % n)
    for k in sorted(cov):
        print('  %-26s %d' % (k, cov[k]))
    # the success-only view of the counters
    cov_s = Counter()
    for r in succ:
        for k, v in r['counters'].items():
            if v:
                cov_s[k] += 1
    print('\ncoverage over the %d successful runs:' % len(succ))
    for k in sorted(cov_s):
        print('  %-26s %d' % (k, cov_s[k]))
    print('\ninput shapes: R on page>=1: %d, R > 64 records: %d, B tier > 64 records: %d, B tier on >=2 pages: %d' % (
        sum(r['R_page1'] for r in rows), sum(r['R_gt64'] for r in rows),
        sum(r['Bt_gt64'] for r in rows), sum(r['Bt_pages_used'] >= 2 for r in rows)))
    with open(os.path.join(d, 'summary.json'), 'w') as fh:
        json.dump({'n': n, 'ok': ok, 'rows': rows}, fh)
    sys.exit(0 if ok == n else 1)


if __name__ == '__main__':
    main()
