#!/usr/bin/env python3
"""Generate the top-preparation and initialization fixtures: run `fdtp` over a
deterministic list of scenarios (families x geometries x seeds).

    gen_tp.py [--n-prep N] [--n-init M] [--out DIR] [--jobs J] [--seed S]

Writes DIR/p%04d_<family>_T<T>.json (top-prep-fixture/0), DIR/i%04d_...json
(top-init-fixture/0) and DIR/manifest.json.  Every run is kept (a failing run
is a fixture); only harness errors are dropped.
"""
import argparse, json, os, random, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
WORK = os.path.abspath(os.environ.get(
    'ORACLE_TP_WORK', os.path.join(HERE, '..', '..', '.lake', 'oracle', 'fixtures-tp')))

# (B, L, D, r0, s) with U = 2*r0*s*B^(L-1), T = D*U.  A spread over T = 8 ..
# 4096 and D in {1,2,4,8}; each T and D appears with more than one shape.
GEOMS = []


def _build_geoms():
    seen = {}
    for B in (2, 4, 8):
        for L in range(2, 9):
            for r0 in (2, 4, 8):
                for s in (1, 2, 4, 8):
                    for D in (1, 2, 4, 8):
                        if D > B:
                            continue
                        U = 2 * r0 * s * B ** (L - 1)
                        T = D * U
                        if T < 8 or T > 4096:
                            continue
                        seen.setdefault((T, D), []).append((B, L, D, r0, s))
    rnd = random.Random(7)
    out = []
    for (T, D), lst in sorted(seen.items()):
        rnd.shuffle(lst)
        out.extend(lst[:2])
    return out


GEOMS = _build_geoms()
ACCS = (32, 48, 56)


def dims(g):
    B, L, D, r0, s = g
    U = 2 * r0 * s * B ** (L - 1)
    return U, D * U


def plan(T, S, tb):
    """(rho, I, direct) as the engine's DfsResidualRangePlan derives them."""
    bb = T.bit_length() - 1
    swept = (bb - 1) * S + tb
    if bb <= 3:
        return 0, bb, True
    rho = 0
    while (1 << rho) < 8 * swept:
        rho += 1
    rho = min(rho, bb)
    I = bb - rho
    if I > 18:
        rho += I - 18
        I = 18
    return rho, I, False


def force(pairs):
    return ','.join('%d:%d' % p for p in pairs)


PREP_FAMS = [
    'sparse', 'moderate', 'tomb', 'flag', 'tierfill', 'hot', 'lastshed',
    'leafedge', 'fulltier', 'early', 'dfsfail', 'lowlanes', 'dense', 'tierflag',
    'randomold', 'hotflag', 'drainedge', 'hot', 'earlypack', 'hotmany',
    'tiermix', 'stagefail', 'stagefail', 'densehot', 'leafmix', 'leafmix',
    'leafmix', 'orderprobe', 'orderprobe', 'orderprobe',
]
INIT_FAMS = [
    'half', 'partial', 'tiny', 'boundary', 'hot', 'hotmany', 'hotleaf', 'edge',
    'quarter', 'hot', 'full_hot', 'orderinit', 'orderinit', 'orderinit',
]


def pick_geom(rnd, fam, kind):
    D = rnd.choice([1, 2, 4, 8])
    g = rnd.choice([x for x in GEOMS if x[2] == D])
    B, L, D, r0, s = g
    U, T = dims(g)
    heavy = fam in ('moderate', 'dense', 'densehot', 'stagefail', 'tierfill', 'tomb', 'flag', 'tiermix',
                    'quarter', 'half', 'partial', 'randomold', 'lowlanes')
    if heavy and T > 256:
        # heavy loads only where the fixture stays small
        small = [x for x in GEOMS if dims(x)[1] <= 256]
        g = rnd.choice(small)
    if fam == 'orderprobe':
        for _ in range(200):
            g = rnd.choice(GEOMS)
            U, T = dims(g)
            if T >= 128:
                break
    if fam == 'orderinit':
        for _ in range(200):
            g = rnd.choice(GEOMS)
            U, T = dims(g)
            if T >= 64:
                break
    if fam in ('dfsfail', 'leafedge', 'hotleaf'):
        big = [x for x in GEOMS if dims(x)[1] >= 16]
        g = rnd.choice(big)
    return g


def base_args(g, rnd, acc, tb):
    B, L, D, r0, s = g
    return ['--B', B, '--L', L, '--D', D, '--r0', r0, '--s', s, '--acc', acc,
            '--tb', tb, '--seed', rnd.randrange(1 << 30),
            '--key-seed', '%x' % rnd.randrange(1, 1 << 40)]


def prep_scenario(i, rnd):
    fam = PREP_FAMS[i % len(PREP_FAMS)]
    g = pick_geom(rnd, fam, 'prep')
    U, T = dims(g)
    bb = T.bit_length() - 1
    acc = rnd.choice(ACCS)
    S = 1 if acc == 32 else 2
    tb = rnd.choice([1, 2, 4, 8])
    if fam in ('dfsfail', 'leafedge', 'drainedge', 'fulltier'):
        tb = rnd.choice([2, 4, 8])
    rho, I, direct = plan(T, S, tb)
    a = base_args(g, rnd, acc, tb)
    opts = {}
    # per-home density of the background load
    if T <= 64:
        dmax = rnd.randint(2, 14)
    elif T <= 256:
        dmax = rnd.randint(1, 8)
    elif T <= 1024:
        dmax = rnd.randint(0, 4)
    else:
        dmax = rnd.randint(0, 2)

    def put(k, v):
        opts[k] = v

    homes = lambda m: rnd.sample(range(T), min(T, m))
    hot_count = lambda: rnd.randint(64 + 8, 64 + 70 * S)
    if fam == 'sparse':
        put('--a-max', dmax)
    elif fam == 'moderate':
        hi = rnd.randint(24, 52) if T <= 64 else rnd.randint(12, 40)
        lo = rnd.randint(0, hi // 2)
        put('--a-min', lo); put('--a-max', hi)
        if rnd.random() < 0.5:
            put('--a-tier-extra', rnd.randint(1, 64 * tb))
    elif fam == 'dense':
        hi = rnd.randint(46, 64)
        put('--a-min', rnd.randint(32, hi)); put('--a-max', hi)
        if rnd.random() < 0.4:
            put('--a-tier-fill', rnd.randint(1, 64 * tb))
    elif fam == 'tomb':
        put('--a-max', rnd.randint(8, 40) if T <= 64 else dmax + 4)
        put('--a-tomb', rnd.choice([10, 25, 50]))
        if rnd.random() < 0.5:
            put('--a-tier-extra', rnd.randint(1, 64 * tb))
        if rnd.random() < 0.6:
            put('--a-force', force([(h, hot_count()) for h in homes(rnd.randint(1, 3))]))
    elif fam == 'flag':
        put('--a-max', rnd.randint(8, 40) if T <= 64 else dmax + 4)
        put('--a-tomb', rnd.choice([10, 20])); put('--a-flag', rnd.choice([10, 25, 40]))
        put('--a-tier-extra', rnd.randint(1, 64 * tb))
        put('--a-force', force([(h, hot_count()) for h in homes(rnd.randint(1, 3))]))
    elif fam == 'tierflag':
        put('--a-max', dmax)
        put('--a-tomb', 20); put('--a-flag', 40)
        put('--a-tier-fill', rnd.randint(1, 64 * tb))
        put('--a-tier-extra', rnd.randint(0, 64))
    elif fam == 'tierfill':
        put('--a-max', rnd.randint(0, 30) if T <= 128 else dmax)
        put('--a-tier-fill', 64 * tb)
    elif fam == 'tiermix':
        put('--a-max', rnd.randint(4, 36) if T <= 128 else dmax)
        put('--a-tier-fill', rnd.randint(1, 64 * tb))
        put('--a-tier-extra', rnd.randint(1, 64 * tb))
        put('--a-tomb', rnd.choice([0, 10]))
    elif fam in ('hot', 'hotflag'):
        put('--a-max', dmax)
        put('--a-force', force([(h, hot_count()) for h in homes(rnd.randint(1, 5))]))
        if fam == 'hotflag':
            put('--a-tomb', 20); put('--a-flag', 15)
        if rnd.random() < 0.5:
            put('--a-tier-fill', rnd.randint(1, 64 * tb))
    elif fam == 'hotmany':
        put('--a-max', dmax)
        m = rnd.randint(4, 16)
        put('--a-force', force([(h, rnd.randint(66, 64 + 12 * S + 24)) for h in homes(m)]))
    elif fam == 'lastshed':
        # a few homes whose excess sums to about the last-level stash capacity
        put('--a-max', rnd.randint(0, 3))
        cap = 64 * S
        m = rnd.randint(1, 3)
        tot = cap + rnd.choice([-6, -3, -2, -1, 0, 1, 2, 3, 6])
        per = max(1, tot // m)
        put('--a-force', force([(h, 64 + per + rnd.randint(0, 3)) for h in homes(m)]))
    elif fam == 'drainedge':
        # full homes plus tier records aimed at them: leftover = tier size
        put('--a-max', rnd.randint(0, 3))
        m = rnd.randint(2, 6)
        hs = homes(m)
        cap = 64 * S
        tot = min(64 * tb, cap + rnd.choice([-3, -2, -1, 0, 1, 2, 3]))
        per = max(1, tot // m)
        put('--a-force', force([(h, 64) for h in hs]))
        put('--a-tier-force', force([(h, per) for h in hs]))
    elif fam == 'fulltier':
        put('--a-max', rnd.randint(0, 3))
        m = rnd.randint(1, 4)
        hs = homes(m)
        put('--a-force', force([(h, 64) for h in hs]))
        put('--a-tier-force', force([(h, rnd.randint(8, 64)) for h in hs]))
    elif fam == 'leafedge':
        # A main empty or sparse; the tier holds a leaf's worth: 64 +- 2
        put('--a-max', 0)
        if not direct:
            base = rnd.randrange(0, T, 1 << I)
            n_h = min(1 << I, rnd.randint(1, 3))
            hs = rnd.sample([base + k for k in range(1 << I)], n_h)
            tot = 64 + rnd.choice([-2, -1, 0, 1, 2])
            tot = min(tot, 64 * tb)
            put('--a-tier-force', force([(h, max(1, tot // len(hs))) for h in hs]))
        else:
            put('--a-tier-fill', rnd.randint(1, 64 * tb))
    elif fam == 'dfsfail':
        put('--a-max', rnd.randint(0, 3))
        if not direct:
            base = rnd.randrange(0, T, 1 << I)
            n_h = min(1 << I, rnd.randint(1, 3))
            hs = rnd.sample([base + k for k in range(1 << I)], n_h)
            tot = rnd.randint(66, 64 * tb)
            put('--a-tier-force', force([(h, max(1, tot // len(hs))) for h in hs]))
        else:
            put('--a-tier-fill', 64 * tb)
    elif fam == 'early' or fam == 'earlypack':
        # old buckets packed with records of one low-bit pattern: sheds at the
        # first levels (the recursion's low levels)
        put('--a-max', rnd.randint(0, 2))
        j = rnd.randint(1, 2)
        base = rnd.randrange(0, T, 1 << j)
        val = rnd.randrange(1 << j)
        per = rnd.randint(20, 64) if j == 1 else rnd.randint(12, 40)
        packs = ['%d:%d:%d:%d' % (base + k, per, j, val) for k in range(1 << j)]
        if fam == 'earlypack' and T >= 16:
            j2 = rnd.randint(1, min(3, bb - 1))
            base2 = rnd.randrange(0, T, 1 << j2)
            packs += ['%d:%d:%d:%d' % (base2 + k, rnd.randint(8, 30), j2,
                                       rnd.randrange(1 << j2)) for k in range(1 << j2)]
        put('--a-pack', ';'.join(packs))
        if rnd.random() < 0.5:
            put('--a-force', force([(h, hot_count()) for h in homes(rnd.randint(1, 2))]))
    elif fam == 'stagefail':
        # whole groups of old buckets full of one direction: the early stages shed a lot
        put('--a-max', rnd.randint(0, 2))
        j = rnd.randint(1, min(3, bb - 1))
        base = rnd.randrange(0, T, 1 << j)
        val = rnd.randrange(1 << j)
        packs = ['%d:%d:%d:%d' % (base + k, rnd.randint(40, 64), j, val) for k in range(1 << j)]
        put('--a-pack', ';'.join(packs))
    elif fam == 'leafmix':
        # several homes of ONE leaf, each spread over a block of old buckets:
        # sheds at low and high levels from different pairs whose records meet
        # in the same leaf (the order of the stash decides the leaf's lanes)
        put('--a-max', rnd.randint(0, 2))
        if direct or T < 64:
            put('--a-max', 2)
        else:
            j = rnd.randint(3, min(bb - 1, 8))
            B0 = rnd.randrange(0, T, 1 << j)
            leaf_base = rnd.randrange(0, T, 1 << I) if I >= 1 else rnd.randrange(T)
            span = 1 << I if I >= 1 else 1
            hs = rnd.sample([leaf_base + k for k in range(span)], min(span, rnd.randint(2, 6)))
            if I == 0:
                hs = list({(h & ~3) + k for h in hs for k in range(4)})[:6]
            sp = ';'.join('%d:%d:%d:%d' % (h, rnd.randint(40, 64 + 40 * S), B0, B0 + (1 << j)) for h in hs)
            put('--a-spread', sp)
            if rnd.random() < 0.5:
                put('--a-tier-fill', rnd.randint(1, 32))
    elif fam == 'orderprobe':
        # homes of one leaf with distinct low bits, each just over 64 records
        # concentrated in half of a 16-bucket old block: each sheds a few records
        # at bit 2 from DIFFERENT pairs; the stash order decides the leaf lanes
        put('--a-max', 0)
        if I >= 1 and not direct:
            leaf_base = rnd.randrange(0, T, 1 << I)
            span = 1 << I
            hs = rnd.sample([leaf_base + k for k in range(span)], min(span, rnd.randint(2, 4)))
            nb = 16 if bb - 1 >= 4 else 8
            B0 = rnd.randrange(0, T, nb)
            sp = []
            for h in hs:
                lo = B0 + rnd.choice([0, nb // 2])
                tot = 64 + rnd.randint(3, 12 * S)
                sp.append('%d:%d:%d:%d' % (h, tot, lo, lo + nb // 2))
            put('--a-spread', ';'.join(sp))
            if rnd.random() < 0.3:
                put('--a-tier-fill', rnd.randint(1, 20))
    elif fam == 'densehot':
        put('--a-min', rnd.randint(36, 60) if T <= 32 else rnd.randint(8, 30))
        put('--a-max', rnd.randint(50, 64) if T <= 32 else rnd.randint(30, 44))
        put('--a-force', force([(h, hot_count()) for h in homes(rnd.randint(1, 3))]))
    elif fam == 'lowlanes':
        put('--a-max', rnd.randint(2, 30) if T <= 128 else dmax)
        put('--lanes', 'low')
        if rnd.random() < 0.5:
            put('--a-force', force([(h, hot_count()) for h in homes(rnd.randint(1, 3))]))
    elif fam == 'randomold':
        put('--a-max', rnd.randint(2, 30) if T <= 128 else dmax)
        put('--random-old', '')
        if rnd.random() < 0.5:
            put('--a-force', force([(h, hot_count()) for h in homes(rnd.randint(1, 3))]))
    for k, v in opts.items():
        a.append(k)
        if v != '':
            a.append(v)
    return 'prep', fam, T, [str(x) for x in a]


def init_scenario(i, rnd):
    fam = INIT_FAMS[i % len(INIT_FAMS)]
    g = pick_geom(rnd, fam, 'init')
    U, T = dims(g)
    bb = T.bit_length() - 1
    acc = rnd.choice(ACCS)
    S = 1 if acc == 32 else 2
    tb = rnd.choice([1, 2, 4, 8])
    if fam in ('hotleaf', 'edge', 'full_hot', 'hotmany'):
        tb = rnd.choice([1, 2, 4])
    rho, I, direct = plan(T, S, tb)
    a = base_args(g, rnd, acc, tb) + ['--mode', 'init']
    cap = 32 * T
    homes = lambda m: rnd.sample(range(T), min(T, m))
    opts = {}
    if fam == 'half':
        cnt = cap if T <= 512 else rnd.randint(1, 4000)
    elif fam == 'quarter':
        cnt = rnd.randint(1, cap // 2) if T <= 512 else rnd.randint(1, 3000)
    elif fam == 'partial':
        cnt = rnd.randint(1, cap) if T <= 512 else rnd.randint(1, 3000)
    elif fam == 'tiny':
        cnt = rnd.randint(1, 40)
    elif fam == 'boundary':
        cnt = max(1, min(cap, 32 * rnd.randint(1, max(1, min(T, 6))) + rnd.choice([-1, 0, 1])))
    elif fam in ('hot', 'full_hot'):
        cnt = min(cap, rnd.randint(1, 600) if fam == 'hot' else cap if T <= 128 else 3000)
        hs = homes(rnd.randint(1, 4))
        opts['--in-force'] = force([(h, rnd.randint(64 + 6, 64 + 60 * max(S, tb))) for h in hs])
        cnt = max(cnt, sum(int(x.split(':')[1]) for x in opts['--in-force'].split(',')))
        cnt = min(cnt, cap)
    elif fam == 'hotmany':
        cnt = min(cap, rnd.randint(200, 1500))
        hs = homes(rnd.randint(4, 14))
        opts['--in-force'] = force([(h, rnd.randint(66, 64 + 10 * S + 24)) for h in hs])
        cnt = max(cnt, sum(int(x.split(':')[1]) for x in opts['--in-force'].split(',')))
        cnt = min(cnt, cap)
    elif fam == 'orderinit':
        # consecutive blocks of records of homes of one leaf: the scatter puts
        # each block into adjacent buckets, which shed at the first levels
        if not direct and I >= 1:
            base = rnd.randrange(0, T, 1 << I)
            span = 1 << I
            hs = rnd.sample([base + k for k in range(span)], min(span, rnd.randint(2, 4)))
        else:
            hs = homes(rnd.randint(2, 3))
        opts['--in-force'] = force([(h, rnd.randint(66, 64 + 12 * S + 24)) for h in hs])
        cnt = min(cap, sum(int(x.split(':')[1]) for x in opts['--in-force'].split(',')) + rnd.randint(0, 80))
        a += ['--no-shuffle']
    elif fam == 'hotleaf':
        # records of one leaf (homes sharing high bits): a leaf test of 64 +- 2
        if not direct:
            base = rnd.randrange(0, T, 1 << I)
            n_h = min(1 << I, rnd.randint(1, 3))
            hs = rnd.sample([base + k for k in range(1 << I)], n_h)
            tot = rnd.randint(60, 70 + 40 * S)
            opts['--in-force'] = force([(h, max(1, tot // len(hs))) for h in hs])
        else:
            opts['--in-force'] = force([(h, rnd.randint(64, 140)) for h in homes(2)])
        cnt = min(cap, rnd.randint(1, 400) + sum(int(x.split(':')[1]) for x in opts['--in-force'].split(',')))
    elif fam == 'edge':
        # excess about the published tier / last stash capacity
        capd = 64 * tb
        tot = capd + rnd.choice([-3, -2, -1, 0, 1, 2, 3])
        m = rnd.randint(1, 3)
        hs = homes(m)
        opts['--in-force'] = force([(h, 64 + max(1, tot // m)) for h in hs])
        cnt = min(cap, rnd.randint(1, 200) + sum(int(x.split(':')[1]) for x in opts['--in-force'].split(',')))
    cnt = max(1, min(cnt, cap))
    a += ['--count', cnt]
    for k, v in opts.items():
        a += [k, v]
    if rnd.random() < 0.15:
        a += ['--no-shuffle']
    return 'init', fam, T, [str(x) for x in a]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n-prep', type=int, default=1500)
    ap.add_argument('--n-init', type=int, default=700)
    ap.add_argument('--out', default=os.path.join(WORK, 'fx'))
    ap.add_argument('--jobs', type=int, default=48)
    ap.add_argument('--seed', type=int, default=20261002)
    ap.add_argument('--exe', default=os.path.join(WORK, 'fdtp'))
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    rnd = random.Random(args.seed)
    scen = [prep_scenario(i, rnd) for i in range(args.n_prep)]
    scen += [init_scenario(i, rnd) for i in range(args.n_init)]
    manifest = []

    def work(idx):
        kind, fam, T, argv = scen[idx]
        name = '%s%04d_%s_T%d.json' % ('p' if kind == 'prep' else 'i', idx if kind == 'prep' else idx - args.n_prep, fam, T)
        path = os.path.join(args.out, name)
        try:
            r = subprocess.run([args.exe, path] + argv, capture_output=True, text=True,
                               timeout=300)
        except subprocess.TimeoutExpired:
            return idx, name, 124, '', 'timeout'
        return idx, name, r.returncode, r.stdout.strip(), r.stderr.strip()[:300]

    bad = 0
    with ThreadPoolExecutor(args.jobs) as ex:
        for idx, name, rc, out, err in ex.map(work, range(len(scen))):
            kind, fam, T, argv = scen[idx]
            e = {'file': name, 'kind': kind, 'family': fam, 'T': T, 'argv': argv, 'status': rc}
            if rc != 0:
                bad += 1
                e['error'] = err
            else:
                e['summary'] = out
            manifest.append(e)
    with open(os.path.join(args.out, 'manifest.json'), 'w') as fh:
        json.dump({'seed': args.seed, 'n': len(scen), 'harness_errors': bad,
                   'attempts': manifest}, fh, indent=0)
    print('ran %d scenarios, %d harness errors' % (len(scen), bad))
    for e in manifest:
        if e['status'] != 0:
            print('ERR', e['file'], e.get('error'), file=sys.stderr)


if __name__ == '__main__':
    main()
