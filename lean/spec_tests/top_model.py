#!/usr/bin/env python3
"""A literal Python transcription of the Lean top-finish model
(RebuildBound/Spec/Model/Top.lean, with the parts of Job.lean it reuses),
for testing the statements T3top, T4top and G3 numerically.

Records are tuples (key, val, tomb); buckets are lists of records or None.
Every function mirrors the Lean definition of the same name. `run_fixture`
runs it on an engine fixture (top-finish-fixture/0) so the transcription can
be checked against the engine, as the Lean oracle checks the Lean model.
"""
from __future__ import annotations

import json


class Geom:
    def __init__(self, C, k, e, rho, I, dfs, rPages, bPages, mergePages, tierPages):
        self.C, self.k, self.e, self.rho, self.I, self.dfs = C, k, e, rho, I, dfs
        self.rPages, self.bPages, self.mergePages, self.tierPages = rPages, bPages, mergePages, tierPages

    U = property(lambda g: 2 ** g.k)
    D = property(lambda g: 2 ** g.e)
    T = property(lambda g: 2 ** (g.k + g.e))
    ranges = property(lambda g: 2 ** g.rho)
    SR = property(lambda g: g.rPages * g.C)
    SB = property(lambda g: g.bPages * g.C)
    SMerge = property(lambda g: g.mergePages * g.C)
    STier = property(lambda g: g.tierPages * g.C)

    def valid(g):
        return 1 <= g.k + g.e and g.rho + g.I == g.k + g.e and (g.dfs or g.rho == 0)

    # toGeom: the d = 2 geometry (k' = k + e - 1, lo = I, poolSlots = SR)
    def kprime(g):
        return max(g.k + g.e - 1, 0)

    def depth(g):  # Geom.depth = k' + 1 - lo (truncated)
        return max(g.kprime() + 1 - g.I, 0)


KEY, VAL, TOMB = 0, 1, 2


def recs(B):
    return [s for s in B if s is not None]


def keys(B):
    return [r[KEY] for r in recs(B)]


def clear(p, B):
    return [None if (s is not None and p(s[KEY])) else s for s in B]


def fill(B, L):
    out, L = [], list(L)
    for s in B:
        if s is not None:
            out.append(s)
        elif L:
            out.append(L.pop(0))
        else:
            out.append(None)
    return out, L


def append_fill(B, L):
    f = fill(B, L)
    return f[0] + list(f[1])


def occupied(B):
    return sum(1 for s in B if s is not None)


def drain_step(acc, L):
    t = append_fill(acc[0], L)
    return t, acc[1] + [(('drain',), occupied(t))]


def drain(st):
    first = [[(r, True) for r in leaf] for leaf in st['leaves']] + [[(r, False) for r in st['bcopy']]]
    d = ([], [])
    for L in first:
        d = drain_step(d, L)
    ins_keys = {r[KEY] for r in st['ins']}
    t = [None if (s is not None and s[1] and s[0][KEY] in ins_keys) else s for s in d[0]]
    b_keys = {s[0][KEY] for s in t if s is not None and not s[1]}
    ins = [r for r in st['ins'] if r[KEY] not in b_keys]
    d2 = drain_step((t, d[1]), [(r, False) for r in ins])
    return [None if s is None else s[0] for s in d2[0]], d2[1]


def top_home(g, w, r):
    return w(r[KEY]) % g.T


def top_way(g, w, r):
    return top_home(g, w, r) // g.U


def range_of(g, w, r):  # rangeOf g.toGeom: home mod 2^(k'+1), div 2^lo
    return (w(r[KEY]) % 2 ** (g.kprime() + 1)) // 2 ** g.I


def leaves_of(g, w, pool):
    return [[r for r in pool if range_of(g, w, r) == R] for R in range(2 ** g.depth())]


def dfs_trace(g, w, pool):
    out = []
    dep = g.depth()
    for d in range(dep + 1):
        for c in range(2 ** d):
            out.append((('dfs', d, c), sum(1 for r in pool if range_of(g, w, r) // 2 ** (dep - d) == c)))
    return out


def cap_of(g, t):
    if t[0] == 'dfs':
        return min(g.SR, g.C * 2 ** max(g.depth() - t[1], 0))
    if t[0] == 'insertion':
        return g.SMerge
    if t[0] == 'drain':
        return g.STier
    return None


def early(unsh, r):
    return r[TOMB] and unsh(r)


def top_pool(unsh, inp):
    bt = {r[KEY] for r in inp['bTier']}
    return [r for r in inp['carry'] if r[KEY] not in bt and not early(unsh, r)]


def top_tier_copy(unsh, inp):
    return [r for r in inp['bTier'] if not early(unsh, r)]


def drop_tombs(B):
    return [None if (s is not None and s[TOMB]) else s for s in B]


def getd(L, i, d):
    return L[i] if i < len(L) else d


def setl(L, i, x):
    L = list(L)
    if i < len(L):
        L[i] = x
    return L


def top_resolve(g, w, ci, dk, st):
    R = ci // 2 ** g.I
    leaf = [r for r in getd(st['leaves'], R, [])
            if not (top_home(g, w, r) == ci and (r[KEY] in dk or r[TOMB]))]
    fc = {r[KEY] for r in st['bcopy'] if top_home(g, w, r) == ci}
    m = clear(lambda k: k in fc, drop_tombs(getd(st['main'], ci, [])))
    return dict(st, main=setl(st['main'], ci, m), leaves=setl(st['leaves'], R, leaf),
                bcopy=[r for r in st['bcopy'] if not (top_home(g, w, r) == ci and r[TOMB])])


def top_offer(g, w, ci, st):
    R = ci // 2 ** g.I
    leaf = getd(st['leaves'], R, [])
    ca = [r for r in leaf if top_home(g, w, r) == ci]
    fa = fill(getd(st['main'], ci, []), ca)
    ga = {r[KEY] for r in ca[:len(ca) - len(fa[1])]}
    cb = [r for r in st['bcopy'] if top_home(g, w, r) == ci]
    fb = fill(fa[0], cb)
    gb = {r[KEY] for r in cb[:len(cb) - len(fb[1])]}
    return dict(st, main=setl(st['main'], ci, fb[0]),
                leaves=setl(st['leaves'], R, [r for r in leaf if r[KEY] not in ga]),
                bcopy=[r for r in st['bcopy'] if r[KEY] not in gb])


def top_dest(g, w, Bi, i, q, st):
    ci = i + q * g.U
    d = [r for r in recs(Bi) if top_way(g, w, r) == q]
    st = top_resolve(g, w, ci, {r[KEY] for r in d}, st)
    f = fill(getd(st['main'], ci, []), [r for r in d if not r[TOMB]])
    return top_offer(g, w, ci, dict(st, main=setl(st['main'], ci, f[0]))), f[1]


def top_bucket(g, w, bMain, i, st):
    Bi = getd(bMain, i, [])
    bk = set(keys(Bi))
    main = st['main']
    for q in range(g.D):
        main = setl(main, i + q * g.U, clear(lambda k: k in bk, getd(main, i + q * g.U, [])))
    acc = (dict(st, main=main), [])
    for q in range(g.D):
        p = top_dest(g, w, Bi, i, q, acc[0])
        acc = (p[0], acc[1] + p[1])
    ins = acc[0]['ins'] + acc[1]
    return dict(acc[0], ins=ins, trace=acc[0]['trace'] + [(('insertion',), len(ins))])


def top_sweep(g, w, inp, leaves, bcopy):
    st = dict(main=inp['cMain'], ins=[], leaves=leaves, bcopy=bcopy, trace=[])
    for i in range(g.U):
        st = top_bucket(g, w, inp['bMain'], i, st)
    return st


def top_reference(g, unsh, w, inp):
    pool = top_pool(unsh, inp)
    leaves = leaves_of(g, w, pool)
    fin = top_sweep(g, w, inp, leaves, top_tier_copy(unsh, inp))
    dr = drain(fin)
    main = [drop_tombs(B) for B in fin['main']]
    tier = [None if (s is not None and s[TOMB]) else s for s in dr[0]]
    trace = (dfs_trace(g, w, pool) if g.dfs else []) + fin['trace'] + dr[1]
    return dict(pool=pool, leaves=leaves, fin=fin, main=main, tier=tier, trace=trace)


def first_failure(g, trace):
    for t, n in trace:
        c = cap_of(g, t)
        if c is not None and c < n:
            return t
    return None


def top_job(g, unsh, w, inp):
    r = top_reference(g, unsh, w, inp)
    t = first_failure(g, r['trace'])
    return ('error', t, r) if t is not None else ('ok', None, r)


# --- contract quantities -------------------------------------------------------

def a_all(inp):
    return [r for B in inp['cMain'] for r in recs(B)] + list(inp['carry'])


def b_all(inp):
    return [r for B in inp['bMain'] for r in recs(B)] + list(inp['bTier'])


def winners(inp):
    bk = {r[KEY] for r in b_all(inp)}
    return b_all(inp) + [r for r in a_all(inp) if r[KEY] not in bk]


def live(inp):
    return [r for r in winners(inp) if not r[TOMB]]


def top_count(g, w, L, v):
    return sum(1 for r in L if top_home(g, w, r) == v)


def top_excess(g, w, inp):
    lv = live(inp)
    return sum(max(top_count(g, w, lv, v) - g.C, 0) for v in range(g.T))


def range_excess_a(g, w, inp, r):
    A = a_all(inp)
    return sum(max(top_count(g, w, A, r * 2 ** g.I + i) - g.C, 0) for i in range(2 ** g.I))


def top_shape(g, unsh, w, inp):
    """TopShape, clause by clause; returns the list of failing clause names."""
    bad = []
    if len(inp['cMain']) != g.T: bad.append('cLen')
    if any(len(B) != g.C for B in inp['cMain']): bad.append('cLanes')
    if len(inp['bMain']) != g.U: bad.append('bLen')
    if any(len(B) != g.C for B in inp['bMain']): bad.append('bLanes')
    ak = [r[KEY] for r in a_all(inp)]
    bk = [r[KEY] for r in b_all(inp)]
    if len(set(ak)) != len(ak): bad.append('aNodup')
    if len(set(bk)) != len(bk): bad.append('bNodup')
    if any(top_home(g, w, r) != v for v in range(g.T) for r in recs(getd(inp['cMain'], v, []))):
        bad.append('cHome')
    if any(w(r[KEY]) % g.U != i for i in range(g.U) for r in recs(getd(inp['bMain'], i, []))):
        bad.append('bHome')
    if any(len(recs(getd(inp['cMain'], top_home(g, w, r), []))) != g.C for r in inp['carry']):
        bad.append('carryFull')
    ck = {r[KEY] for B in inp['cMain'] for r in recs(B) if not r[TOMB]}
    if any(early(unsh, r) and r[KEY] in ck for r in inp['bTier']):
        bad.append('tierUnsh')
    return bad


def tiers_fit(g, inp):
    return len(inp['carry']) <= g.SR and len(inp['bTier']) <= g.SB


# --- engine fixtures -------------------------------------------------------------

def run_fixture(f):
    G = f['geometry']
    g = Geom(G['bucket_capacity'], G['K'], G['e'], G['range_bits'], G['range_index_bits'],
             bool(G['dfs']), G['r_pages'], G['b_tier_pages'], G['merge_stash_pages'], G['out_tier_pages'])
    words = {int(x['key'], 16): int(x['word'], 16) for x in f['words']}
    w = lambda k: words.get(k, 0)
    rec = lambda x: (int(x['key'], 16), int(x['value'], 16), x['tombstone'])

    def buckets(n, rs):
        out = [[None] * g.C for _ in range(n)]
        for x in rs:
            out[x['bucket']][x['lane']] = rec(x)
        return out

    def ordered(rs):
        return [rec(x) for x in sorted(rs, key=lambda x: (x['page'], x['lane']))]

    inp = dict(cMain=buckets(g.T, f['inputs']['C_main']), carry=ordered(f['inputs']['R']),
               bMain=buckets(g.U, f['inputs']['B_main']), bTier=ordered(f['inputs']['B_tier']))
    unsh = lambda r: (r[VAL] >> 5) & 1 == 1
    return g, unsh, w, inp, top_job(g, unsh, w, inp)


KIND = {'dfs': 'residual-dfs-partition', 'insertion': 'fixed-merge-offers', 'drain': 'residual-drain'}


def compare_fixture(path):
    f = json.load(open(path))
    g, unsh, w, inp, (status, t, r) = run_fixture(f)
    out = f['outputs']
    if out['verdict'] == 'failure':
        return status == 'error' and KIND[t[0]] == out['kind']
    if status != 'ok':
        return False
    main = sorted((b, l, s[KEY], s[VAL], s[TOMB]) for b, B in enumerate(r['main'])
                  for l, s in enumerate(B) if s is not None)
    tier = sorted((i // g.C, i % g.C, s[KEY], s[VAL], s[TOMB]) for i, s in enumerate(r['tier'])
                  if s is not None)
    em = sorted((x['bucket'], x['lane'], int(x['key'], 16), int(x['value'], 16), x['tombstone'])
                for x in out['main'])
    et = sorted((x['page'], x['lane'], int(x['key'], 16), int(x['value'], 16), x['tombstone'])
                for x in out['tier'])
    return main == em and tier == et


if __name__ == '__main__':
    import glob
    import sys
    if len(sys.argv) != 2:
        sys.exit('usage: top_model.py <fixture directory>')
    files = sorted(glob.glob(sys.argv[1] + '/f*.json'))
    if not files:
        print(f'no fixtures (f*.json) in {sys.argv[1]!r}', file=sys.stderr)
        sys.exit(2)
    ok = sum(compare_fixture(p) for p in files)
    print(f'{ok}/{len(files)} fixtures: transcription == engine')
    sys.exit(0 if ok == len(files) else 1)
