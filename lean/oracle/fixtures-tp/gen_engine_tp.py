#!/usr/bin/env python3
"""Initialization through the REAL public engine (LevelArenaEngine::Initialize),
read back from the publisher's live table; a small battery (the engine builds
every level, so geometries are kept small).  Deterministic (seed 20261002)."""
import os, random, subprocess, sys, json
from concurrent.futures import ThreadPoolExecutor
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
WORK = os.path.abspath(os.environ.get(
    'ORACLE_TP_WORK', os.path.join(HERE, '..', '..', '.lake', 'oracle', 'fixtures-tp')))
OUT = sys.argv[1] if len(sys.argv) > 1 else os.path.join(WORK, 'fx-engine')
EXE = sys.argv[2] if len(sys.argv) > 2 else os.path.join(WORK, 'fdtp_engine')
os.makedirs(OUT, exist_ok=True)
rnd = random.Random(20261002)
GEOMS = [(2, 2, 1, 2, 1), (2, 2, 2, 2, 1), (2, 3, 1, 2, 1), (2, 3, 2, 2, 1), (4, 2, 4, 2, 1),
         (4, 2, 2, 2, 1), (4, 2, 1, 2, 1), (4, 3, 2, 2, 1), (8, 2, 8, 2, 1), (8, 2, 4, 2, 1),
         (4, 3, 4, 2, 1), (4, 2, 4, 4, 1), (2, 3, 2, 4, 1)]
scen = []
for i in range(120):
    B, L, D, r0, s = rnd.choice(GEOMS)
    U = 2 * r0 * s * B ** (L - 1)
    T = D * U
    cap = 32 * T
    kind = i % 6
    a = ['--B', B, '--L', L, '--D', D, '--r0', r0, '--s', s, '--seed', rnd.randrange(1 << 30),
         '--key-seed', '%x' % rnd.randrange(1, 1 << 40)]
    if kind == 0:
        cnt = cap
    elif kind == 1:
        cnt = rnd.randint(1, cap)
    elif kind == 2:
        cnt = max(1, 32 * rnd.randint(1, T) + rnd.choice([-1, 0, 1]))
        cnt = min(cnt, cap)
    else:
        hs = rnd.sample(range(T), min(T, rnd.randint(1, 4)))
        forced = [(h, rnd.randint(66, 64 + 70)) for h in hs]
        a += ['--in-force', ','.join('%d:%d' % x for x in forced)]
        cnt = min(cap, sum(n for _, n in forced) + rnd.randint(0, 200))
        if kind == 5:
            a += ['--no-shuffle']
    cnt = max(1, min(cnt, cap))
    a += ['--count', cnt]
    scen.append((i, [str(x) for x in a]))
def work(x):
    i, argv = x
    p = os.path.join(OUT, 'e%03d.json' % i)
    r = subprocess.run([EXE, p] + argv, capture_output=True, text=True, timeout=600)
    return i, r.returncode, r.stdout.strip(), r.stderr.strip()[:200]
with ThreadPoolExecutor(16) as ex:
    bad = 0
    for i, rc, out, err in ex.map(work, scen):
        if rc != 0:
            bad += 1
            print('ERR', i, err, file=sys.stderr)
print('ran %d engine-path initializations, %d harness errors' % (len(scen), bad))
sys.exit(0 if bad == 0 else 1)
