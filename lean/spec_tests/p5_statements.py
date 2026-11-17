#!/usr/bin/env python3
"""Randomized tests of the P5 statements (RebuildBound/Spec/P5.lean).

* P5a: E f(x + V_1 + ... + V_n) <= E f(x + W_1 + ... + W_n) with W_i compound
  Poisson(1, law of V_i), for random directionally convex f on N^2 and random
  finite laws of the V_i (dependent coordinates allowed).
* P5b_split: the pmf of compoundPoisson(r, unitLaw p) equals the product of
  Po(r p_k) pmfs, pointwise on a grid.

Laws are truncated at a total count where the neglected Poisson mass is below
1e-12; f grows polynomially, so the truncation error is far below TOL.
Negative control: a concave f must violate P5a in some trials.

Usage: spec_tests/p5_statements.py [--trials N] [--seed S]
"""
from __future__ import annotations

import argparse
import itertools
import math
import random

TOL = 1e-7
KMAX = 18  # Poisson(1) terms kept per key; tail < 1e-16
DIM = 2


def add(u, v):
    return tuple(a + b for a, b in zip(u, v))


def conv(p, q):
    out = {}
    for u, a in p.items():
        for v, b in q.items():
            w = add(u, v)
            out[w] = out.get(w, 0.0) + a * b
    return out


def compound_poisson(mu, r=1.0, kmax=KMAX):
    out = {}
    power = {(0,) * DIM: 1.0}
    for k in range(kmax + 1):
        pk = math.exp(-r) * r ** k / math.factorial(k)
        for v, a in power.items():
            out[v] = out.get(v, 0.0) + pk * a
        power = conv(power, mu)
    return out


def expect(f, x, law):
    return sum(a * f(add(x, v)) for v, a in law.items())


def random_dirconvex(rng, concave=False):
    """Sums of h(<w, y>) with w >= 0 and h convex nondecreasing, plus products
    y_0 y_1 (supermodular); all directionally convex on N^2."""
    terms = []
    for _ in range(rng.randint(1, 3)):
        w = (rng.randint(0, 2), rng.randint(0, 2))
        t = rng.randint(0, 4)
        c = rng.uniform(0.1, 1.5)
        kind = rng.randrange(3)
        terms.append((w, t, c, kind))
    prod = rng.uniform(0, 0.5)

    def f(y):
        s = 0.0
        for w, t, c, kind in terms:
            z = w[0] * y[0] + w[1] * y[1]
            if kind == 0:
                h = c * max(z - t, 0)
            elif kind == 1:
                h = c * z * z
            else:
                h = c * max(z - t, 0) ** 2
            s += -math.sqrt(h) if concave else h
        return s + (0 if concave else prod * y[0] * y[1]) + (100 if concave else 0)
    return f


def random_law(rng):
    support = {}
    for _ in range(rng.randint(1, 3)):
        v = (rng.randint(0, 2), rng.randint(0, 2))
        support[v] = support.get(v, 0.0) + rng.uniform(0.1, 1)
    total = sum(support.values())
    return {v: a / total for v, a in support.items()}


def conv_list(laws):
    out = {(0,) * DIM: 1.0}
    for m in laws:
        out = conv(out, m)
    return out


def trial_p5a(rng, concave=False):
    f = random_dirconvex(rng, concave)
    n = rng.randint(1, 3)
    laws = [random_law(rng) for _ in range(n)]
    x = (rng.randint(0, 3), rng.randint(0, 3))
    lhs = expect(f, x, conv_list(laws))
    rhs = expect(f, x, conv_list([compound_poisson(m) for m in laws]))
    return lhs <= rhs + TOL, lhs, rhs


def trial_split(rng):
    k = rng.randint(1, 3)
    p = [rng.uniform(0.05, 1) for _ in range(k)]
    s = sum(p)
    p = [a / s for a in p]
    r = rng.uniform(0.1, 2.5)
    global DIM
    old = DIM
    DIM = k
    try:
        unit = {tuple(1 if j == i else 0 for j in range(k)): p[i] for i in range(k)}
        cp = compound_poisson(unit, r, kmax=40)
        worst = 0.0
        for n in itertools.product(range(5), repeat=k):
            want = 1.0
            for i in range(k):
                lam = r * p[i]
                want *= math.exp(-lam) * lam ** n[i] / math.factorial(n[i])
            worst = max(worst, abs(cp.get(n, 0.0) - want))
    finally:
        DIM = old
    return worst < 1e-12, worst


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--trials', type=int, default=150)
    ap.add_argument('--seed', type=int, default=1)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    fails = 0
    for i in range(args.trials):
        ok, lhs, rhs = trial_p5a(rng)
        if not ok:
            fails += 1
            print(f'P5a FAIL trial {i}: {lhs} > {rhs}')
    print(f'P5a: {args.trials - fails}/{args.trials} pass')
    neg = sum(not trial_p5a(rng, concave=True)[0] for _ in range(args.trials))
    print(f'P5a negative control (concave f): {neg}/{args.trials} violate (want > 0)')
    sfails = 0
    for i in range(args.trials // 3):
        ok, worst = trial_split(rng)
        if not ok:
            sfails += 1
            print(f'P5b_split FAIL trial {i}: max error {worst}')
    print(f'P5b_split: {args.trials // 3 - sfails}/{args.trials // 3} pass')
    raise SystemExit(1 if fails or sfails or neg == 0 else 0)


if __name__ == '__main__':
    main()
