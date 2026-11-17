#!/usr/bin/env python3
"""Fixture battery for the general-digit separated merge: random knob sets
aimed at every capacity test, run through the engine (fd3) and the model
(model3.py), lane-exactly.

    gen.py OUTDIR N_PER_CONFIG [--keep] [--jobs J] [config...]

The canonical battery is `gen.py OUTDIR 500 --keep` (18 configurations x 500
knob sets; the knobs are seeded by label and index, so the battery does not
depend on J). Writes OUTDIR/<label>/<idx>.json and OUTDIR/results.json (one
entry per knob set: arguments, harness refusal or the model comparison).
Without --keep (or KEEP=1 in the environment) a matching fixture with
idx >= 2 is deleted after the comparison. Exits 1 on a model mismatch or a
self-check failure.

The dumper defaults to $FD3, else $ORACLE_RADIX_WORK/fd3 (ORACLE_RADIX_WORK
defaults to lean/.lake/oracle/fixtures-radix), as built by build_fd3.sh."""
import json, os, random, subprocess, sys
from collections import Counter, defaultdict
from multiprocessing import Pool

sys.dont_write_bytecode = True
import model3

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(os.path.dirname(HERE))
WORK = os.environ.get('ORACLE_RADIX_WORK',
                      os.path.join(LEAN, '.lake', 'oracle', 'fixtures-radix'))
FD3 = os.environ.get('FD3', os.path.join(WORK, 'fd3'))

# label: (branching, levels, level, digit, tier_buckets, horizon_log2, U)
CONFIGS = {}
for d in (2, 3, 4):
    CONFIGS[f'b4d{d}'] = (4, 3, 2, d, 1, 32, 16)
    CONFIGS[f'b4t2d{d}'] = (4, 3, 2, d, 2, 32, 16)
    CONFIGS[f'b4L4d{d}'] = (4, 4, 3, d, 1, 32, 64)
for d in (5, 6, 7, 8):
    CONFIGS[f'b8d{d}'] = (8, 3, 2, d, 1, 32, 32)
CONFIGS['b4d3h48'] = (4, 3, 2, 3, 1, 48, 16)
CONFIGS['b4d4h48'] = (4, 3, 2, 4, 1, 48, 16)
CONFIGS['b8d6h48'] = (8, 3, 2, 6, 1, 48, 32)
CONFIGS['b8d5t2'] = (8, 3, 2, 5, 2, 32, 32)
CONFIGS['b2d2'] = (2, 3, 2, 2, 1, 32, 8)

MODES = ['natural', 'bfly', 'radix', 'cont', 'dfs', 'ins', 'drain', 'tier']


def shape(d, U):
    K = U.bit_length() - 1
    e = (d & -d).bit_length() - 1
    r = d >> e
    return K, e, r, K + e


def knobs(label, idx):
    B, L, l, d, tb, hz, U = CONFIGS[label]
    K, e, r, k = shape(d, U)
    N = d * U
    rnd = random.Random(f'{label}/{idx}')
    modes = [m for m in MODES if not (m == 'radix' and r == 1)
             and not (m == 'cont' and e < 2)]
    mode = modes[idx % len(modes)]
    a = ['--branching', B, '--levels', L, '--level', l, '--digit', d,
         '--tier-buckets', tb, '--horizon-log2', hz,
         '--seed', '%x' % rnd.getrandbits(40),
         '--a-per-bucket', rnd.choice([8, 16, 24, 32, 40])]
    if rnd.random() < 0.5 or mode in ('radix', 'cont'):
        a.append('--a-at-homes')
    if rnd.random() < 0.3:
        a.append('--tombs')
    if rnd.random() < 0.3:
        a.append('--stale-blank')
    home = lambda: rnd.randrange(N)
    older, fresh, atier, btier = [], [], [], []
    if mode == 'natural':
        a += ['--forced-older', rnd.choice([0, 60, 120, 200])]
    elif mode == 'bfly':
        if rnd.random() < 0.5:
            a += ['--forced-older', rnd.randrange(120, 600)]
        else:
            j = rnd.randrange(1, k + 1)
            for _ in range(rnd.randrange(1, 4)):
                older.append(f'{rnd.randrange(60, 260)}@{rnd.randrange(1 << j)}/{j}')
    elif mode == 'radix':
        for _ in range(rnd.randrange(1, 5)):
            older.append(f'{rnd.randrange(40, 120)}@{home()}')
    elif mode == 'cont':
        j = rnd.choice([K + 2, K + 2, k]) if e >= 2 else K + 1
        for _ in range(rnd.randrange(1, 4)):
            older.append(f'{rnd.randrange(60, 150)}@{rnd.randrange(1 << j)}/{j}')
    elif mode == 'dfs' and rnd.random() < 0.3 and k + 3 < 12:
        # a leaf over-full only as a SUM of its homes (range_index_bits > 0)
        width = 4
        base = home() // width * width
        for h in range(base, min(N, base + width)):
            atier.append(f'{rnd.randrange(12, 22)}@{h}')
            older.append(f'{rnd.randrange(60, 70)}@{h}')
    elif mode == 'dfs':
        H = home()
        older.append(f'{64 + rnd.randrange(0, 70)}@{H}')
        I = None  # spread the A tier over H's range neighbours
        width = rnd.choice([1, 2, 4])
        base = H - H % width
        for h in range(base, min(N, base + width)):
            atier.append(f'{rnd.randrange(5, 60 // width + 10)}@{h}')
    elif mode == 'ins':
        cis = rnd.sample(range(N), rnd.randrange(2, 6))
        seen = set()
        for ci in cis:
            if ci % U in seen:
                continue
            seen.add(ci % U)
            older.append(f'{rnd.randrange(56, 72)}@{ci}')
            fresh.append(f'{rnd.randrange(12, 36)}@{ci}')
    elif mode == 'drain':
        for _ in range(rnd.randrange(1, 4)):
            older.append(f'{64 + rnd.randrange(10, 60)}@{home()}')
        if rnd.random() < 0.5:
            H = home()
            older.append(f'{rnd.randrange(60, 70)}@{H}')
            btier.append(f'{rnd.randrange(5, 40)}@{H}')
    elif mode == 'tier':
        a += ['--forced-older', rnd.choice([0, 60])]
        a += ['--btier-from-atier', rnd.randrange(0, 13)]
        for _ in range(rnd.randrange(0, 4)):
            btier.append(f'{rnd.randrange(1, 20)}@{home()}')
        for _ in range(rnd.randrange(0, 4)):
            atier.append(f'{rnd.randrange(1, 20)}@{home()}')
        if rnd.random() < 0.5:
            H = home()
            older.append(f'{rnd.randrange(60, 80)}@{H}')
            btier.append(f'{rnd.randrange(3, 20)}@{H}')
            atier.append(f'{rnd.randrange(3, 20)}@{H}')
        if tb > 1 and rnd.random() < 0.85:          # fill past one tier bucket
            for _ in range(rnd.randrange(20, 40)):
                btier.append(f'{rnd.randrange(1, 4)}@{home()}')
            for _ in range(rnd.randrange(0, 30)):
                atier.append(f'{rnd.randrange(1, 4)}@{home()}')
            if rnd.random() < 0.5:                   # a full home, late groups
                H = home()
                older.append(f'{rnd.randrange(62, 70)}@{H}')
                btier.append(f'{rnd.randrange(3, 12)}@{H}')
    # sprinkle: extra tier traffic on any mode
    if mode != 'tier' and rnd.random() < 0.4:
        a += ['--btier-from-atier', rnd.randrange(0, 13)]
    for flag, lst in (('--older-list', older), ('--fresh-list', fresh),
                      ('--atier-list', atier), ('--btier-list', btier)):
        if lst:
            a += [flag, ','.join(lst)]
    return mode, [str(x) for x in a]


def work(job):
    outdir, label, idx = job
    mode, args = knobs(label, idx)
    path = os.path.join(outdir, label, f'{idx:04d}.json')
    p = subprocess.run([FD3, path] + args, capture_output=True, text=True)
    res = {'label': label, 'idx': idx, 'mode': mode, 'args': args}
    if p.returncode == 2 or not os.path.exists(path):
        res['harness'] = (p.stderr or p.stdout).strip()[-200:]
        return res
    res['selfcheck'] = p.returncode == 0
    cov = Counter()
    try:
        cmp = model3.compare(path, cov=cov)
    except Exception as ex:  # model crash counts as a mismatch
        cmp = {'ok': False, 'why': 'model exception %r' % ex, 'engine': '?',
               'model': '?', 'kind': None}
    res.update({k: cmp.get(k) for k in ('ok', 'why', 'engine', 'model', 'kind')})
    if cmp.get('engine') == 'failure':
        msg = json.load(open(path))['outputs']['message']
        res['eng_kind'] = msg.split(' at ')[1].split(';')[0]
    res['cov'] = dict(cov)
    if 'harness' not in res and cmp.get('ok'):
        fj = json.load(open(path))
        res['orders'] = {o: model3.order_agreement(fj, o)
                         for o in ('blank-full', 'canonical')}
    if cmp.get('ok') and idx >= 2 and not os.environ.get('KEEP'):
        os.remove(path)
    return res


def main():
    args = sys.argv[1:]
    jobs_n = 8
    if '--keep' in args:
        args.remove('--keep')
        os.environ['KEEP'] = '1'
    if '--jobs' in args:
        i = args.index('--jobs')
        jobs_n = int(args[i + 1])
        del args[i:i + 2]
    if len(args) < 2:
        sys.exit('usage: gen.py OUTDIR N_PER_CONFIG [--keep] [--jobs J] [config...]')
    outdir, n = args[0], int(args[1])
    labels = args[2:] or list(CONFIGS)
    if not os.access(FD3, os.X_OK):
        sys.exit(f'no dumper at {FD3} (run build_fd3.sh)')
    for lb in labels:
        os.makedirs(os.path.join(outdir, lb), exist_ok=True)
    jobs = [(outdir, lb, i) for lb in labels for i in range(n)]
    with Pool(jobs_n) as pool:
        results = pool.map(work, jobs, chunksize=4)
    json.dump(results, open(os.path.join(outdir, 'results.json'), 'w'))
    bad = summarize(results)
    sys.exit(1 if bad else 0)


def summarize(results):
    by = defaultdict(list)
    for r in results:
        by[r['label']].append(r)
    tot = Counter()
    for lb, rs in by.items():
        run = [r for r in rs if 'harness' not in r]
        ok = sum(1 for r in run if r['ok'])
        succ = sum(1 for r in run if r['engine'] == 'success')
        kinds = Counter(r.get('eng_kind') for r in run if r['engine'] == 'failure')
        sc = sum(1 for r in run if r['engine'] == 'success' and not r['selfcheck'])
        print(f"{lb:10s} run={len(run):4d} match={ok:4d} harness_skip={len(rs)-len(run):3d} "
              f"success={succ:4d} selfcheck_fail={sc} fail={dict(kinds)}")
        tot['run'] += len(run); tot['ok'] += ok; tot['skip'] += len(rs) - len(run)
        for r in run:
            if not r['ok']:
                print('   MISMATCH', r['idx'], r['mode'], r.get('why'), ' '.join(r['args']))
        tot['bad'] += sum(1 for r in run if not r['ok']
                          or (r['engine'] == 'success' and not r['selfcheck']))
    print('TOTAL', dict(tot))
    return tot['bad']


if __name__ == '__main__':
    main()
