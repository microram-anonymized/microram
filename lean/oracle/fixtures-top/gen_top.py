#!/usr/bin/env python3
"""Generate the top-finish fixtures: run `fdtop` over a deterministic list of
scenarios (families x geometries x seeds) and keep the runs whose preparation
succeeded.  Usage:

    gen_top.py [--n N] [--out DIR] [--exe FDTOP] [--jobs J] [--seed S]

Writes DIR/fNNNN_<family>_<geometry>.json and DIR/manifest.json (one entry
per attempt, including the preparation failures that were skipped). The
canonical battery is the defaults: 1000 fixtures, seed 20261001. The
scenarios are drawn before any run and kept in attempt order, so the
battery does not depend on J.

DIR defaults to $ORACLE_TOP_WORK/fx and FDTOP to $ORACLE_TOP_WORK/fdtop
(ORACLE_TOP_WORK defaults to lean/.lake/oracle/fixtures-top), as built by
build_fdtop.sh.
"""
import argparse, json, os, random, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(os.path.dirname(HERE))
WORK = os.environ.get('ORACLE_TOP_WORK',
                      os.path.join(LEAN, '.lake', 'oracle', 'fixtures-top'))

# name: (B, L, D, r0, s).  U = 2*r0*s*B^(L-1), T = D*U.
GEOMS = {
    'g1': (2, 2, 1, 2, 1),   # T=8   U=8   D=1  direct plan (rho=0)
    'g2': (2, 2, 2, 2, 1),   # T=16  U=8   D=2
    'g3': (2, 3, 1, 2, 1),   # T=16  U=16  D=1
    'g4': (4, 2, 4, 2, 1),   # T=64  U=16  D=4
    'g5': (4, 2, 2, 2, 1),   # T=32  U=16  D=2
    'g6': (8, 2, 8, 2, 1),   # T=256 U=32  D=8  (the test geometry)
    'g7': (8, 2, 4, 2, 1),   # T=128 U=32  D=4
    'g8': (8, 2, 1, 2, 1),   # T=32  U=32  D=1
}


def dims(name):
    B, L, D, r0, s = GEOMS[name]
    U = 2 * r0 * s * B ** (L - 1)
    return U, D * U


def plan(name, acc):
    """(S_R, direct, rho, I) as the engine's PlanResidualRange derives them."""
    U, T = dims(name)
    ml = T.bit_length() - 1
    sr = 1 if acc == 32 else 2
    if ml <= 3:
        return sr, True, 0, ml
    bits = 0
    while (1 << bits) < sr * 8:
        bits += 1
    rho = min(bits, ml)
    return sr, False, rho, ml - rho


def force(pairs):
    return ','.join('%d:%d' % p for p in pairs)


def scenario(i, rnd):
    """The i-th scenario: (family, geometry name, argv)."""
    fams = ['plain', 'tomb', 'absent', 'flag', 'badflag', 'full', 'rleaf',
            'rfail', 'shedfail', 'drainfail', 'drain2', 'inject', 'lowlanes',
            'fullflag', 'absorb', 'absorb', 'bigtier', 'dupmain', 'misplace',
            'injectfull', 'rfail', 'rfail1', 'rboundary', 'rflag', 'edge_merge',
            'edge_drain1', 'edge_drain2', 'multiway', 'misplacefull',
            'dupmain2']
    fam = fams[i % len(fams)]
    gname = rnd.choice(list(GEOMS))
    # the failure families need S_R = 2 and a coarse range of >= 2 homes
    if fam in ('rfail', 'rleaf', 'rboundary', 'rflag'):
        gname = rnd.choice(['g5', 'g7', 'g8', 'g6', 'g4'])
    if fam == 'multiway':
        gname = rnd.choice(['g2', 'g5', 'g4', 'g7', 'g6'])
    if fam == 'misplacefull':
        gname = rnd.choice(['g1', 'g2', 'g3'])
    if fam == 'rfail1':
        gname = 'g8'
        fam = 'rfail'
    acc = rnd.choice([32, 56]) if fam not in ('rfail', 'rleaf') else 48
    if fam in ('rfail', 'rleaf', 'rboundary', 'rflag'):
        acc = 56
    tb = rnd.choice([1, 2, 4, 8]) if fam not in ('drainfail',) else rnd.choice([1, 2])
    B, L, D, r0, s = GEOMS[gname]
    U, T = dims(gname)
    sr, direct, rho, I = plan(gname, acc)
    a = ['--B', B, '--L', L, '--D', D, '--r0', r0, '--s', s, '--acc', acc,
         '--tb', tb, '--seed', rnd.randrange(1 << 30),
         '--key-seed', '%x' % rnd.randrange(1, 1 << 40)]
    # density: keep large-T fixtures small
    dmax = 12 if T <= 64 else (8 if T <= 128 else 6)
    a += ['--a-max', rnd.randint(2, dmax), '--b-max', rnd.randint(2, dmax)]
    shadow = rnd.choice([0, 20, 40])
    a += ['--b-shadow', shadow]
    if rnd.random() < 0.5:
        a += ['--b-target-r', 1]
    if fam == 'plain':
        a += ['--bt-new', rnd.randint(0, 10), '--bt-c', rnd.randint(0, 6),
              '--bt-r', rnd.randint(0, 4)]
    elif fam == 'tomb':
        a += ['--a-tomb', rnd.choice([10, 20, 30]), '--b-tomb', rnd.choice([20, 30, 40]),
              '--bt-tomb', rnd.choice([30, 50, 70]), '--bt-c', rnd.randint(2, 10),
              '--bt-r', rnd.randint(0, 6), '--bt-new', rnd.randint(0, 8)]
    elif fam == 'absent':
        a[a.index('--b-shadow') + 1] = 0
        a += ['--b-tomb', rnd.choice([30, 50, 100]), '--bt-new', rnd.randint(2, 12),
              '--bt-tomb', rnd.choice([50, 100])]
    elif fam == 'flag':
        a += ['--a-tomb', 10, '--a-flag', 15, '--b-tomb', 40, '--b-flag', 60,
              '--bt-tomb', 60, '--bt-flag', 60, '--bt-new', rnd.randint(2, 12),
              '--bt-c', rnd.randint(0, 5), '--bt-r', rnd.randint(0, 4)]
    elif fam == 'badflag':      # unshadowed on tombstones over keys A has: a
        # violation of the flag's contract; the engine trusts the flag
        a += ['--a-tomb', 10, '--b-tomb', 50, '--b-flag-bad', 70, '--b-flag', 50,
              '--bt-tomb', 80, '--bt-flag-bad', 70, '--bt-flag', 50,
              '--bt-c', rnd.randint(2, 8), '--bt-r', rnd.randint(0, 6),
              '--bt-new', rnd.randint(0, 6)]
    elif fam == 'inject':       # flagged tombstones in R and C (synthetic)
        a += ['--a-tomb', 25, '--inject-flag', rnd.choice([40, 100]), '--b-tomb', 30,
              '--bt-tomb', 50, '--bt-r', rnd.randint(2, 8), '--bt-c', rnd.randint(0, 6)]
        a[a.index('--a-max') + 1] = rnd.randint(2, dmax)
    elif fam == 'lowlanes':
        a += ['--lanes', 'low', '--b-tomb', rnd.choice([0, 25]),
              '--bt-c', rnd.randint(0, 6), '--bt-new', rnd.randint(0, 6)]
    if fam in ('absorb', 'injectfull', 'dupmain', 'misplace', 'bigtier'):
        # A overloads a few homes; B tombstones / replaces C's copies there so
        # that the retained candidates can be absorbed
        homes = rnd.sample(range(T), min(T, rnd.randint(2, 4)))
        a += ['--a-force', force([(h, rnd.randint(66, 100)) for h in homes]),
              '--a-tomb', rnd.choice([0, 15, 30])]
        a += ['--b-force', force([(h, rnd.randint(1, 12)) for h in homes]),
              '--b-shadow', 100, '--b-tomb', rnd.choice([40, 70, 100]),
              '--bt-c', rnd.randint(0, 6), '--bt-r', rnd.randint(0, 8),
              '--bt-tomb', rnd.choice([0, 30, 60])]
        if fam == 'injectfull':
            a += ['--inject-flag', rnd.choice([30, 100]), '--bt-flag', 40]
        if fam == 'dupmain':
            a += ['--bt-dup-main', rnd.randint(2, 20), '--bt-tomb', rnd.choice([0, 40])]
        if fam == 'misplace':
            a += ['--b-misplace', rnd.randint(2, 12)]
        if fam == 'bigtier':
            a += ['--bt-new', rnd.randint(80, max(81, 60 * tb)), '--bt-full', rnd.randint(1, 4)]
    if fam in ('full', 'fullflag', 'rleaf', 'rfail', 'shedfail', 'drainfail', 'drain2'):
        # force A to overload some homes (C full, and R/leftovers)
        homes = rnd.sample(range(T), min(T, rnd.randint(2, 5)))
        pairs = []
        for h in homes:
            pairs.append((h, rnd.randint(60, 118) if sr == 2 else rnd.randint(60, 100)))
        if fam in ('rleaf', 'rfail'):
            # two or three homes of one coarse range (same finish leaf)
            base = rnd.randrange(0, T, 1 << I) if I >= 1 else 0
            mates = [base + k for k in range(1 << I)]
            rnd.shuffle(mates)
            mates = mates[:rnd.randint(2, min(3, len(mates)))] if len(mates) >= 2 else mates
            lo, hi = (96, 124) if fam == 'rfail' else (66, 92)
            pairs = [(h, rnd.randint(lo, hi)) for h in mates]
        a += ['--a-force', force(pairs)]
        bh = [h for h, _ in pairs]
        bp = []
        for h in bh:
            bp.append((h, rnd.randint(2, 30)))
        if fam == 'shedfail':
            bp = [(h, rnd.randint(34, 64)) for h in bh]
        a += ['--b-force', force(bp)]
        a += ['--bt-full', rnd.randint(1, 3)]
        if fam in ('full', 'drain2', 'fullflag'):
            a += ['--b-tomb', rnd.choice([0, 20]), '--bt-tomb', rnd.choice([0, 30]),
                  '--bt-c', rnd.randint(0, 4), '--bt-r', rnd.randint(0, 6)]
        if fam == 'fullflag':
            a += ['--a-tomb', 10, '--a-flag', 10, '--b-flag', 50, '--bt-flag', 50,
                  '--bt-tomb', 50, '--b-tomb', 30]
        if fam == 'drainfail':
            a += ['--bt-force', force([(h, rnd.randint(20, 60)) for h in bh[:3]])]
        if fam == 'drain2':
            a += ['--bt-force', force([(h, rnd.randint(4, 20)) for h in bh[:3]])]
        if fam in ('rleaf', 'rfail'):
            a += ['--b-tomb', rnd.choice([0, 15]), '--bt-r', rnd.randint(0, 6)]


    def set_opt(opt, val):
        if opt in a:
            a[a.index(opt) + 1] = val
        else:
            a.extend([opt, val])

    def reset_sparse():
        for opt in ('--a-min', '--a-max', '--b-min', '--b-max', '--b-shadow'):
            set_opt(opt, 0)

    def homes_distinct_buckets(m):
        bs_ = rnd.sample(range(U), min(m, U))
        return [i + rnd.randrange(D) * U for i in bs_]

    def leaves_distinct(m):
        """m homes in different coarse ranges (leaves)."""
        nleaf = T >> I if not direct else T
        ls = rnd.sample(range(nleaf), min(m, nleaf))
        return [(l << I) + rnd.randrange(1 << I) for l in ls] if not direct else ls

    if fam == 'rboundary' and I >= 1:
        reset_sparse()
        base = rnd.randrange(0, T, 1 << I)
        h1, h2 = rnd.sample([base + k for k in range(1 << I)], 2)
        tot = 64 + rnd.choice([-2, -1, 0, 1, 2])        # R of the leaf
        r1 = rnd.randint(max(1, tot - 64), min(64, tot - 1))
        a += ['--a-force', force([(h1, 64 + r1), (h2, 64 + tot - r1)])]
    if fam == 'rflag' and I >= 1:
        base = rnd.randrange(0, T, 1 << I)
        mates = rnd.sample([base + k for k in range(1 << I)], 2)
        a += ['--a-force', force([(h, rnd.randint(100, 124)) for h in mates]),
              '--a-tomb', rnd.choice([40, 50, 60]), '--inject-flag', 100]
    if fam == 'edge_merge':
        reset_sparse()
        cap = 64 * sr
        tot = cap + rnd.choice([-2, -1, 0, 1, 2])
        m = (tot + 63) // 64
        hs = homes_distinct_buckets(m)
        counts = [64] * (m - 1) + [tot - 64 * (m - 1)]
        a += ['--a-force', force([(h, 64) for h in hs]),
              '--b-force', force(list(zip(hs, counts)))]
    if fam in ('edge_drain1', 'edge_drain2'):
        reset_sparse()
        cap = 64 * tb
        # leftovers of the first drain: r from R, t from B's tier (full homes)
        leftover = cap + rnd.choice([-2, -1, 0, 1, 2]) if fam == 'edge_drain1' \
            else rnd.randint(max(2, cap - 80), cap - 1)
        leftover = max(2, leftover)
        rmax = 64 * (2 if (sr == 2 and not direct and I >= 1) else 1)
        rmax = min(rmax, 64) if not direct else min(64 * sr, 64)
        r = rnd.randint(max(1, leftover - 64 * tb), min(rmax, leftover - 1)) \
            if leftover - 1 >= 1 else 1
        r = min(r, leftover - 1)
        t = leftover - r
        hs = leaves_distinct(3)
        a += ['--a-force', force([(hs[0], 64 + r), (hs[1], 64)])]
        if t <= 64 * tb:
            a += ['--bt-force', force([(hs[1], t)])]
        if fam == 'edge_drain2':
            s_ = cap - leftover + rnd.choice([-2, -1, 0, 1, 2])
            s_ = max(1, min(s_, 64))
            h3 = homes_distinct_buckets(1)[0]
            if h3 in (hs[0], hs[1]):
                h3 = (h3 + 1) % T
            a[a.index('--a-force') + 1] += ',%d:64' % h3
            a += ['--b-force', force([(h3, s_)])]
    if fam == 'multiway' and D >= 2:
        reset_sparse()
        i = rnd.randrange(U)
        hs = [i + q * U for q in range(D)]
        a += ['--a-force', force([(h, rnd.randint(60, 90)) for h in hs]),
              '--b-force', force([(h, rnd.randint(3, 12)) for h in hs])]
        if rnd.random() < 0.5:
            a += ['--b-tomb', 20]
    if fam == 'misplacefull':
        reset_sparse()
        set_opt('--a-min', 65)
        set_opt('--a-max', 68)
        set_opt('--b-max', 3)
        set_opt('--b-shadow', 100)
        a += ['--b-target-r', 1, '--b-misplace', rnd.randint(3, 30)]
    if fam == 'dupmain2':
        reset_sparse()
        hs = homes_distinct_buckets(rnd.randint(1, 3))
        a += ['--a-force', force([(h, 64) for h in hs]),
              '--b-force', force([(h, rnd.randint(3, 20)) for h in hs]),
              '--bt-dup-main', rnd.randint(2, 20)]
    return fam, gname, [str(x) for x in a]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, default=1000, help='fixtures to keep')
    ap.add_argument('--out', default=os.path.join(WORK, 'fx'))
    ap.add_argument('--exe', default=os.path.join(WORK, 'fdtop'))
    ap.add_argument('--jobs', type=int, default=24)
    ap.add_argument('--seed', type=int, default=20261001)
    ap.add_argument('--max-attempts', type=int, default=6000)
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    rnd = random.Random(args.seed)
    scen = [scenario(i, rnd) for i in range(args.max_attempts)]
    exe = args.exe
    if not os.access(exe, os.X_OK):
        sys.exit(f'no dumper at {exe} (run build_fdtop.sh)')
    manifest = []

    def work(idx):
        fam, gname, argv = scen[idx]
        path = os.path.join(args.out, 'tmp%05d.json' % idx)
        r = subprocess.run([exe, path] + argv, capture_output=True, text=True)
        return idx, r.returncode, r.stdout.strip(), r.stderr.strip()[:300], path

    kept = 0
    skipped = 0
    batch = 96
    nexti = 0
    while kept < args.n and nexti < len(scen):
        idxs = list(range(nexti, min(nexti + batch, len(scen))))
        nexti += len(idxs)
        with ThreadPoolExecutor(args.jobs) as ex:
            results = list(ex.map(work, idxs))
        for idx, rc, out, err, path in results:
            fam, gname, argv = scen[idx]
            entry = {'attempt': idx, 'family': fam, 'geom': gname, 'argv': argv,
                     'status': rc}
            if rc == 0 and kept < args.n:
                final = os.path.join(args.out, 'f%04d_%s_%s.json' % (kept, fam, gname))
                os.replace(path, final)
                entry['file'] = os.path.basename(final)
                entry['summary'] = out
                kept += 1
            else:
                if rc == 3:
                    skipped += 1
                elif rc != 0:
                    entry['error'] = err
                if os.path.exists(path):
                    os.remove(path)
            manifest.append(entry)
        print('attempts %d kept %d prep-skipped %d' % (nexti, kept, skipped),
              file=sys.stderr)
    with open(os.path.join(args.out, 'manifest.json'), 'w') as fh:
        json.dump({'seed': args.seed, 'kept': kept, 'prep_failed': skipped,
                   'attempts': manifest}, fh, indent=0)
    print('kept %d fixtures, %d preparation failures skipped, of %d attempts' % (
        kept, skipped, nexti))


if __name__ == '__main__':
    main()
