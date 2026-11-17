#!/usr/bin/env python3
"""Tests of P7 and P8a (RebuildBound/Spec/P7.lean) and of the
definition Phi (RebuildBound/Spec/Prob/Series.lean).

* Phi: the Lean definition transcribed literally (seriesW, seriesCoeff with
  i = j - 1, the Icc sum and the tail), in mpmath at 120 digits. At the
  production parameters it must agree with analysis/bound_certification/code/certify_tier_router.py's
  positive_excess_bound (an upward-rounded evaluation of the same formula).
* P7: E (sum_{v in J} (Z_v - C)_+ - S)_+ for iid Z_v ~ Po(lam), computed
  exactly as E X - S + sum_{x < S} (S - x) P(X = x), against Phi_K for every
  small cutoff K > S, over a grid of (|J|, C, lam, S) including lam = 0,
  C = 0 and |J| = 0.
* P8a: the exact stop-loss of the restricted excess under independent
  categorical homes (enumerating all assignments) against the Poisson one,
  for random masses p_i(v) <= p_* and lam = len * p_* (and larger).
  Negative control: with lam < len * p_* the inequality must fail somewhere.

Usage: spec_tests/p7_statements.py [--trials N] [--seed S] [--production]
"""
from __future__ import annotations

import argparse
import itertools
import random
import sys
from fractions import Fraction
from pathlib import Path

import mpmath as mp

mp.mp.dps = 120
TOL = mp.mpf(10) ** -60


def series_w(C, lam, j):
    return mp.e ** (-lam) * lam ** (C + j) / mp.factorial(C + j)


def series_coeffs(n, C, lam, K):
    """seriesCoeff n C lam k for k = 0..K, exactly as the Lean recursion."""
    c = [mp.mpf(1)]
    for k in range(K):  # c[k+1]
        s = mp.fsum((i + 1) * series_w(C, lam, i + 1) * c[k - i] for i in range(k + 1))
        c.append(mp.mpf(n) / (k + 1) * s)
    return c


def phi(K, n, C, lam, S):
    lam = mp.mpf(lam)
    c = series_coeffs(n, C, lam, K)
    finite = mp.fsum((k - S) * c[k] for k in range(S + 1, K + 1))
    tail = mp.mpf(max(K + 1 - S, 0)) / mp.mpf(2) ** (K + 1) * mp.e ** (mp.mpf(n) / mp.mpf(2) ** C * mp.e ** lam)
    return finite + tail


def excess_pmf(C, lam, M):
    """pmf of (Z - C)_+ for Z ~ Po(lam), on 0..M (mass beyond M dropped)."""
    lam = mp.mpf(lam)
    p = [mp.e ** (-lam) * lam ** z / mp.factorial(z) for z in range(C + M + 1)]
    q = [mp.fsum(p[:C + 1])] + [p[C + j] for j in range(1, M + 1)]
    return q


def conv(a, b, M):
    out = [mp.mpf(0)] * (M + 1)
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b[:M + 1 - i]):
            out[i + j] += x * y
    return out


def poisson_stop_loss(n, C, lam, S):
    """E (sum of n iid (Z - C)_+ - S)_+, exactly: E X - S + sum_{x<S} (S-x) P(X=x)."""
    lam = mp.mpf(lam)
    # E (Z - C)_+ = sum_{z > C} (z - C) p_z = lam - C + sum_{z <= C} (C - z) p_z
    pz = [mp.e ** (-lam) * lam ** z / mp.factorial(z) for z in range(C + 1)]
    mean_excess = lam - C + mp.fsum((C - z) * pz[z] for z in range(C + 1))
    q = excess_pmf(C, lam, S)
    dist = [mp.mpf(1)] + [mp.mpf(0)] * S
    for _ in range(n):
        dist = conv(dist, q, S)
    low = mp.fsum((S - x) * dist[x] for x in range(S))
    return n * mean_excess - S + low


def check_p7(rng, trials):
    bad = 0
    count = 0
    grid = [(n, C, lam, S) for n in range(0, 6) for C in range(0, 4)
            for lam in (0, 0.25, 1, 2.5, 4, 7) for S in range(0, 5)]
    rng.shuffle(grid)
    for n, C, lam, S in grid[:trials]:
        lhs = poisson_stop_loss(n, C, lam, S)
        for K in list(range(S + 1, S + 7)) + [S + 20, S + 40]:
            rhs = phi(K, n, C, lam, S)
            count += 1
            if lhs > rhs + TOL:
                bad += 1
                print(f"P7 FALSE: n={n} C={C} lam={lam} S={S} K={K} lhs={lhs} phi={rhs}")
    # Tightness sanity: at a large cutoff Phi is close to the exact stop-loss
    # when lam is small (the majorization loses little).
    lhs = poisson_stop_loss(3, 2, 0.5, 1)
    rhs = phi(60, 3, 2, 0.5, 1)
    assert lhs <= rhs + TOL and rhs < 1.5 * lhs, (lhs, rhs)
    print(f"P7: {count} (instance, cutoff) pairs, {bad} violations; "
          f"tightness at (3,2,0.5,1): exact {mp.nstr(lhs, 8)} vs Phi_60 {mp.nstr(rhs, 8)}")
    return bad


def check_p7alg(rng, trials):
    """cauchyPow (excessPmf C lam) n k <= seriesCoeff n C lam k, every k <= 24."""
    bad = 0
    count = 0
    for _ in range(trials):
        n = rng.randint(0, 7)
        C = rng.randint(0, 4)
        lam = rng.choice([0, 0.1, 0.5, 1, 3, 6, 10])
        K = 24
        q = excess_pmf(C, lam, K)
        dist = [mp.mpf(1)] + [mp.mpf(0)] * K
        for _ in range(n):
            dist = conv(dist, q, K)
        c = series_coeffs(n, C, mp.mpf(lam), K)
        for k in range(K + 1):
            count += 1
            if dist[k] > c[k] + TOL:
                bad += 1
                print(f"P7alg FALSE: n={n} C={C} lam={lam} k={k} pow={dist[k]} c={c[k]}")
    print(f"P7alg: {count} coefficients, {bad} violations")
    return bad


def categorical_stop_loss(T, J, C, S, ps):
    total = mp.mpf(0)
    for homes in itertools.product(range(T), repeat=len(ps)):
        pr = mp.mpf(1)
        for p, h in zip(ps, homes):
            pr *= p[h]
        if pr == 0:
            continue
        y = [0] * T
        for h in homes:
            y[h] += 1
        ex = sum(max(y[v] - C, 0) for v in J)
        total += pr * max(ex - S, 0)
    return total


def rand_masses(rng, T, pstar):
    """A random categorical law on T homes with every mass <= pstar (Fractions)."""
    while True:
        raw = [Fraction(rng.randint(0, 12)) for _ in range(T)]
        s = sum(raw)
        if s == 0:
            continue
        p = [x / s for x in raw]
        if max(p) <= pstar:
            return p


def check_p8a(rng, trials):
    bad = 0
    neg = 0
    for _ in range(trials):
        T = rng.randint(1, 4)
        N = rng.randint(0, 6 if T <= 3 else 5)
        J = [v for v in range(T) if rng.random() < 0.7]
        C = rng.randint(0, 2)
        S = rng.randint(0, 3)
        pstar = Fraction(1, T) + Fraction(rng.randint(0, 3), 8) * (1 - Fraction(1, T))
        ps = [rand_masses(rng, T, pstar) for _ in range(N)]
        ps_mp = [[mp.mpf(x.numerator) / x.denominator for x in p] for p in ps]
        lhs = categorical_stop_loss(T, J, C, S, ps_mp)
        lam = mp.mpf(N) * mp.mpf(pstar.numerator) / pstar.denominator
        rhs = poisson_stop_loss(len(J), C, lam, S)
        if lhs > rhs + TOL:
            bad += 1
            print(f"P8a FALSE: T={T} J={J} C={C} S={S} N={N} pstar={pstar} lhs={lhs} rhs={rhs}")
        # Negative control: too small a Poisson mean.
        rhs_small = poisson_stop_loss(len(J), C, lam / 3, S)
        if lhs > rhs_small + TOL:
            neg += 1
    print(f"P8a: {trials} trials, {bad} violations; negative control (mean / 3) "
          f"violated in {neg} trials")
    return bad, neg


def check_production():
    sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'analysis/bound_certification/code'))
    from certify_tier_router import positive_excess_bound
    for n, S in ((1 << 18, 64), (1 << 22, 128)):
        ours = phi(256, n, 64, 32, S)
        theirs = mp.mpf(str(positive_excess_bound(n, S)))
        rel = abs(ours - theirs) / theirs
        print(f"Phi_256({n}, 64, 32, {S}) = 2^{mp.nstr(mp.log(ours, 2), 8)}; "
              f"certify_tier_router 2^{mp.nstr(mp.log(theirs, 2), 8)}; rel. diff {mp.nstr(rel, 3)}")
        assert ours <= theirs and rel < mp.mpf(10) ** -40, "Lean Phi disagrees with the certifier"
    total = 16 * phi(256, 1 << 18, 64, 32, 64) + phi(256, 1 << 22, 64, 32, 128)
    print(f"TopNum instance: 16 Phi_256(2^18,64,32,64) + Phi_256(2^22,64,32,128) = "
          f"2^{mp.nstr(mp.log(total, 2), 8)} (statement: <= 2^-78)")
    assert total <= mp.mpf(2) ** -78


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--trials', type=int, default=200)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--production', action='store_true')
    args = ap.parse_args()
    rng = random.Random(args.seed)
    bad = check_p7(rng, args.trials) + check_p7alg(rng, args.trials)
    bad8, neg = check_p8a(rng, args.trials)
    if args.production:
        check_production()
    if bad or bad8 or neg == 0:
        print("FAIL")
        sys.exit(1)
    print("PASS")


if __name__ == '__main__':
    main()
