#!/usr/bin/env python3
"""Tests of T3top, T4top and G3 (RebuildBound/Spec/TopT.lean,
RebuildBound/Spec/G3.lean) on spec_tests/top_model.py, the literal
transcription of the Lean model (checked lane-exactly against the engine
fixtures by `top_model.py <dir>`).

* T3top and T4top on random small inputs that meet TopShape: C in 1..3, up to
  8 homes, every D, both plans, tombstones and unshadowed flags everywhere,
  shared keys, oversized R and B tiers (T3top must hold on every outcome).
* Negative controls, each of which must break a statement somewhere:
  - R records at non-full homes (no fullness identity): T4top's DFS clause;
  - a flagged B-tier tombstone over a C record: T3top;
  - the late-offer order (B's tier offered and its tombstones dropped only
    after the merge): T3top's excess identity (the report's capacity-one
    example is the first case);
  - G3's bound without the 2^rho union factor.
* G3 exhaustively on tiny shapes: every assignment of homes to the keys of
  fixed record sets, under the canonical law (Spec/Model/TopCanonical.lean), against
  topFinishBound evaluated with mpmath.

Usage: spec_tests/top_statements.py [--trials N] [--seed S] [--g3]
"""
from __future__ import annotations

import argparse
import itertools
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import top_model as M  # noqa: E402
from p7_statements import phi  # noqa: E402


def rand_geom(rng):
    while True:
        k, e = rng.randint(0, 2), rng.randint(0, 2)
        if 1 <= k + e <= 3:
            break
    dfs = rng.random() < 0.8
    rho = rng.randint(0, k + e) if dfs else 0
    C = rng.randint(1, 3)
    return M.Geom(C, k, e, rho, k + e - rho, dfs, rng.randint(1, 3), rng.randint(1, 3),
                  rng.randint(1, 3), rng.randint(1, 3))


def make_inputs(rng, g, words, A, B, carry_full=True, tier_unsh=True, unsh=None):
    """Place fixed record sets as a preparation and a producer might: C keeps
    a random C-subset of each home (R the rest, so R names full homes), B's
    main a random C-subset of each carry bucket (its tier the rest); lanes
    and orders random."""
    T, U, C = g.T, g.U, g.C
    w = lambda x: words[x]
    cMain = [[None] * C for _ in range(T)]
    carry = []
    for v in range(T):
        here = [r for r in A if w(r[0]) % T == v]
        rng.shuffle(here)
        keep = here[:C] if carry_full else here[:rng.randint(0, min(C, len(here)))]
        lanes = rng.sample(range(C), len(keep))
        for l, r in zip(lanes, keep):
            cMain[v][l] = r
        carry += here[len(keep):]
    rng.shuffle(carry)
    bMain = [[None] * C for _ in range(U)]
    bTier = []
    for i in range(U):
        here = [r for r in B if w(r[0]) % U == i]
        rng.shuffle(here)
        keep = here[:C]
        for l, r in zip(rng.sample(range(C), len(keep)), keep):
            bMain[i][l] = r
        bTier += here[C:]
    rng.shuffle(bTier)
    inp = dict(cMain=cMain, carry=carry, bMain=bMain, bTier=bTier)
    if tier_unsh:
        ck = {r[0] for Bk in cMain for r in M.recs(Bk) if not r[2]}
        # The flag's promise: a flagged B-tier tombstone has no live copy in C.
        inp['bTier'] = [(r[0], r[1] & ~32, r[2]) if (M.early(unsh, r) and r[0] in ck) else r
                        for r in inp['bTier']]
    return inp


def rand_case(rng, g, **kw):
    T = g.T
    nA = rng.randint(0, 3 * g.C * T)
    nB = rng.randint(0, 2 * g.C * g.U)
    akeys = rng.sample(range(1, 400), nA)
    shared = [x for x in akeys if rng.random() < 0.3]
    fresh = [x for x in rng.sample(range(400, 800), nB)]
    bkeys = list(dict.fromkeys(shared + fresh))[:max(nB, 0)]
    words = {x: rng.randrange(64) for x in set(akeys) | set(bkeys)}
    # value: id * 256 + meta byte (0x80 tombstone, 0x20 unshadowed)
    def mk(x, src):
        tomb = rng.random() < 0.25
        flag = rng.random() < 0.4
        return (x, (src * 1000 + x) * 256 + (0x80 if tomb else 0) + (0x20 if flag else 0), tomb)
    A = [mk(x, 1) for x in akeys]
    B = [mk(x, 2) for x in bkeys]
    unsh = lambda r: (r[1] >> 5) & 1 == 1
    inp = make_inputs(rng, g, words, A, B, unsh=unsh, **kw)
    return unsh, (lambda x: words.get(x, 0)), inp


def check_t3(g, unsh, w, inp):
    r = M.top_reference(g, unsh, w, inp)
    lv = M.live(inp)
    E = M.top_excess(g, w, inp)
    bad = []
    if len(r['main']) != g.T or any(len(B) != g.C for B in r['main']):
        bad.append('lanes')
    for v in range(g.T):
        rs = M.recs(M.getd(r['main'], v, []))
        if any(x not in lv or M.top_home(g, w, x) != v for x in rs):
            bad.append('placement')
        if len(rs) != min(M.top_count(g, w, lv, v), g.C):
            bad.append('count')
    out = [x for B in r['main'] for x in M.recs(B)] + [s for s in r['tier'] if s is not None]
    if sorted(out) != sorted(lv):
        bad.append('perm')
    if any(t[0][0] in ('insertion', 'drain') and t[1] > E for t in r['trace']):
        bad.append('prefix')
    return bad


def check_t4(g, unsh, w, inp):
    status, t, _ = M.top_job(g, unsh, w, inp)
    if status == 'ok':
        return []
    if t[0] == 'dfs':
        ok = g.C < g.SR and any(g.C < M.range_excess_a(g, w, inp, r) for r in range(g.ranges))
    else:
        ok = min(g.SMerge, g.STier) < M.top_excess(g, w, inp)
    return [] if ok else ['T4top ' + t[0]]


def pre_repair_reference(g, unsh, w, inp):
    """The late-offer order (the d = 2 model's finish with a trailing drop):
    no resolution before the merge; the A offer consumes candidates already in
    main; the B-tier offer clears main copies of its keys only after the
    merge; tombstones dropped at the end."""
    def offerA(ci, st):
        R = ci // 2 ** g.I
        leaf = M.getd(st['leaves'], R, [])
        Bk = set(M.keys(M.getd(st['main'], ci, [])))
        cand = [r for r in leaf if M.top_home(g, w, r) == ci]
        drop = [r for r in cand if r[0] in Bk]
        stale = [r for r in cand if r[0] not in Bk]
        f = M.fill(M.getd(st['main'], ci, []), stale)
        gone = {r[0] for r in drop + stale[:len(stale) - len(f[1])]}
        return dict(st, main=M.setl(st['main'], ci, f[0]),
                    leaves=M.setl(st['leaves'], R, [r for r in leaf if r[0] not in gone]))

    def offerB(ci, st):
        fc = [r for r in st['bcopy'] if M.top_home(g, w, r) == ci]
        fk = {r[0] for r in fc}
        Bm = M.clear(lambda k: k in fk, M.getd(st['main'], ci, []))
        f = M.fill(Bm, fc)
        placed = {r[0] for r in fc[:len(fc) - len(f[1])]}
        return dict(st, main=M.setl(st['main'], ci, f[0]),
                    bcopy=[r for r in st['bcopy'] if r[0] not in placed])

    pool = M.top_pool(unsh, inp)
    st = dict(main=inp['cMain'], ins=[], leaves=M.leaves_of(g, w, pool),
              bcopy=M.top_tier_copy(unsh, inp), trace=[])
    for i in range(g.U):
        Bi = M.getd(inp['bMain'], i, [])
        bk = set(M.keys(Bi))
        sheds = []
        for q in range(g.D):
            ci = i + q * g.U
            m = M.clear(lambda k: k in bk, M.getd(st['main'], ci, []))
            f = M.fill(m, [r for r in M.recs(Bi) if M.top_way(g, w, r) == q])
            st = dict(st, main=M.setl(st['main'], ci, f[0]))
            sheds += f[1]
            st = offerB(ci, offerA(ci, st))
        st = dict(st, ins=st['ins'] + sheds)
    tier = M.drain(st)[0]
    return [x for B in st['main'] for x in M.recs(B) if not x[2]], [s for s in tier if s is not None and not s[2]]


def report_example():
    """The report's capacity-one example: A's main holds live a, B's main
    live b, B's tier a tombstone of a, all at one home."""
    g = M.Geom(1, 0, 1, 0, 1, True, 1, 1, 1, 1)  # T = 2, U = 1, D = 2, C = 1
    words = {1: 0, 2: 0}
    a, b, ta = (1, 100, False), (2, 200, False), (1, 300, True)
    inp = dict(cMain=[[a], [None]], carry=[], bMain=[[b]], bTier=[ta])
    unsh = lambda r: False
    w = lambda x: words[x]
    assert not M.top_shape(g, unsh, w, inp), M.top_shape(g, unsh, w, inp)
    E = M.top_excess(g, w, inp)
    r = M.top_reference(g, unsh, w, inp)
    new_tier = [s for s in r['tier'] if s is not None]
    old_main, old_tier = pre_repair_reference(g, unsh, w, inp)
    print(f"report example: E_f = {E}; model tier {len(new_tier)} record(s); "
          f"late-offer order tier {len(old_tier)} record(s)")
    assert E == 0 and not new_tier and len(old_tier) == 1


def random_tests(rng, trials):
    stats = dict(t3=0, t4=0, fails=0, dfs=0, merge=0, drain=0, oversizeR=0)
    neg = dict(carry=0, unsh=0, prerepair=0)
    for _ in range(trials):
        g = rand_geom(rng)
        unsh, w, inp = rand_case(rng, g)
        assert not M.top_shape(g, unsh, w, inp), M.top_shape(g, unsh, w, inp)
        if len(inp['carry']) > g.SR:
            stats['oversizeR'] += 1
        bad = check_t3(g, unsh, w, inp)
        if bad:
            stats['t3'] += 1
            print('T3top FALSE', bad, vars(g))
        if M.tiers_fit(g, inp):
            status, t, _ = M.top_job(g, unsh, w, inp)
            if status == 'error':
                stats['fails'] += 1
                stats[{'dfs': 'dfs', 'insertion': 'merge', 'drain': 'drain'}[t[0]]] += 1
            bad = check_t4(g, unsh, w, inp)
            if bad:
                stats['t4'] += 1
                print('T4top FALSE', bad, vars(g))
        # negative controls
        unsh2, w2, inp2 = rand_case(rng, g, carry_full=False)
        if M.tiers_fit(g, inp2) and check_t4(g, unsh2, w2, inp2):
            neg['carry'] += 1
        unsh3, w3, inp3 = rand_case(rng, g, tier_unsh=False)
        if check_t3(g, unsh3, w3, inp3):
            neg['unsh'] += 1
        om, ot = pre_repair_reference(g, unsh, w, inp)
        if len(ot) != M.top_excess(g, w, inp):
            neg['prerepair'] += 1
    print(f"random: {trials} trials; T3top violations {stats['t3']}, T4top violations "
          f"{stats['t4']}; failures {stats['fails']} (dfs {stats['dfs']}, merge {stats['merge']}, "
          f"drain {stats['drain']}); oversized R {stats['oversizeR']}")
    print(f"negative controls (must be > 0): no fullness identity breaks T4top in {neg['carry']}, "
          f"bad flag breaks T3top in {neg['unsh']}, late-offer order breaks the excess identity "
          f"in {neg['prerepair']}")
    return stats['t3'] + stats['t4'], min(neg.values())


def top_finish_bound(g, lam, K1, K2):
    import mpmath as mp
    first = (2 ** g.rho) * phi(K1, 2 ** g.I, g.C, lam, g.C) if g.C < g.SR else mp.mpf(0)
    return first + phi(K2, g.T, g.C, lam, min(g.SMerge, g.STier))


def g3_exhaustive(rng, cases):
    """P(TopTiersFit and fail) under the canonical law, exactly, against the
    bound; also against the bound without the union factor 2^rho."""
    import mpmath as mp
    worst = 0
    tight_violations = 0
    for g, nA, nB, nShared in cases:
        T = g.T
        akeys = list(range(1, nA + 1))
        bkeys = akeys[:nShared] + list(range(100, 100 + nB - nShared))
        A = [(x, x * 256, False) for x in akeys]
        B = [(x, (1000 + x) * 256, rng.random() < 0.2) for x in bkeys]
        allk = sorted(set(akeys) | set(bkeys))
        unsh = lambda r: False
        fails = 0
        total = 0
        for hs in itertools.product(range(T), repeat=len(allk)):
            words = dict(zip(allk, hs))
            w = lambda x: words.get(x, 0)
            # canonical placement in key order (Spec/Model/TopCanonical.lean)
            cMain = [[None] * g.C for _ in range(T)]
            carry = []
            for v in range(T):
                here = [r for r in A if w(r[0]) % T == v]
                for l, r in enumerate(here[:g.C]):
                    cMain[v][l] = r
                carry += here[g.C:]
            bMain = [[None] * g.C for _ in range(g.U)]
            bTier = []
            for i in range(g.U):
                here = [r for r in B if w(r[0]) % g.U == i]
                for l, r in enumerate(here[:g.C]):
                    bMain[i][l] = r
                bTier += here[g.C:]
            inp = dict(cMain=cMain, carry=carry, bMain=bMain, bTier=bTier)
            total += 1
            if M.tiers_fit(g, inp) and M.top_job(g, unsh, w, inp)[0] == 'error':
                fails += 1
        p = mp.mpf(fails) / total
        nW = len(M.live(inp))
        lam = mp.mpf(max(nA, nW)) / T
        K1, K2 = g.C + 30, min(g.SMerge, g.STier) + 30
        bound = top_finish_bound(g, lam, K1, K2)
        ratio = p / bound if bound > 0 else 0
        worst = max(worst, ratio)
        no_union = (phi(K1, 2 ** g.I, g.C, lam, g.C) if g.C < g.SR else 0) + \
            phi(K2, T, g.C, lam, min(g.SMerge, g.STier))
        if p > no_union:
            tight_violations += 1
        print(f"G3 T={T} D={g.D} rho={g.rho} C={g.C} SR={g.SR} S={min(g.SMerge, g.STier)} "
              f"|A|={nA} |B|={nB}: P(fit and fail) = {mp.nstr(p, 6)}, bound {mp.nstr(bound, 6)}"
              f"{'  VIOLATED' if p > bound else ''}")
        if p > bound:
            return False, tight_violations
    print(f"G3: worst P/bound = {mp.nstr(worst, 4)}")
    return True, tight_violations


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--trials', type=int, default=3000)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--g3', action='store_true')
    args = ap.parse_args()
    rng = random.Random(args.seed)
    report_example()
    bad, neg = random_tests(rng, args.trials)
    ok = bad == 0 and neg > 0
    if args.g3:
        cases = [
            (M.Geom(1, 1, 1, 1, 1, True, 2, 2, 1, 1), 5, 2, 1),   # T=4, D=2
            (M.Geom(1, 2, 0, 2, 0, True, 3, 2, 1, 1), 6, 1, 0),   # T=4, D=1, one-home ranges
            (M.Geom(1, 0, 2, 1, 1, True, 2, 1, 1, 2), 6, 1, 1),   # T=4, U=1, D=4
            (M.Geom(2, 1, 1, 1, 1, True, 2, 1, 1, 1), 7, 1, 0),   # C=2
            (M.Geom(1, 1, 1, 0, 2, False, 2, 1, 1, 1), 5, 2, 1),  # direct plan
            (M.Geom(3, 1, 1, 1, 1, True, 2, 1, 1, 1), 8, 1, 0),   # bound < 1 and P > 0
        ]
        g3ok, tight = g3_exhaustive(rng, cases)
        print(f"G3 without the 2^rho factor exceeded on {tight} of {len(cases)} cases "
              "(informational: the factor is a union bound)")
        ok = ok and g3ok
    print('PASS' if ok else 'FAIL')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
