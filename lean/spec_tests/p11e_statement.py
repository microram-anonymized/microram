#!/usr/bin/env python3
"""Numerical test of P11e (RebuildBound/Spec/P11de.lean).

LHS: E firstArrivalTest(N) for independent Po(lam) arrivals N at every node,
computed with the backward forest test of spec_tests/p11_statements.py.
Arrivals at nodes whose bit lo differs from R's never reach the range, so they
are set to zero (P11a's locality); the others are truncated at NMAX.
RHS: the stop-loss of rangeLaw, from the shadowTree recursion (Spec/Prob/
ShadowTree.lean) truncated at the same total.

Usage: spec_tests/p11e_statement.py
"""
from __future__ import annotations

import itertools
import math
import random
import sys
from fractions import Fraction

sys.path.insert(0, __file__.rsplit('/', 1)[0])
import p11_statements as t  # noqa: E402

NMAX = 7


def pois(lam, n):
    return math.exp(-lam) * lam ** n / math.factorial(n)


def binom(n, k, p):
    return math.comb(n, k) * p ** k * (1 - p) ** (n - k)


def shadow_tree(C, lam, depth):
    F = {}
    for n in range(NMAX + 1):
        s = (min(n, C), n - min(n, C))
        F[s] = F.get(s, 0.0) + pois(lam, n)
    for _ in range(depth - 1):
        child = {}
        for (m, r), w in F.items():
            for a in range(m + 1):
                for c in range(r + 1):
                    key = (a, c)
                    child[key] = child.get(key, 0.0) + w * binom(m, a, .5) * binom(r, c, .5)
        G = {}
        for (m1, r1), w1 in child.items():
            for (m2, r2), w2 in child.items():
                u, v = m1 + m2, r1 + r2
                s = (min(u, C), v + max(u - C, 0))
                G[s] = G.get(s, 0.0) + w1 * w2
        F = G
    return F


def range_law_stoploss(C, lam, P, p, g, depth, L):
    F = shadow_tree(C, lam, depth)
    Z = {}
    for (_, r), w in F.items():
        Z[r] = Z.get(r, 0.0) + w
    Y = {e: binom(P, e, p) for e in range(P + 1)}
    for _ in range(g):
        Y2 = {}
        for y, a in Y.items():
            for z, b in Z.items():
                Y2[y + z] = Y2.get(y + z, 0.0) + a * b
        Y = Y2
    return sum(w * max(y - L, 0) for y, w in Y.items())


class Inst(t.Instance):
    def __init__(self, b, C, lo, R, P, L):
        self.b, self.C, self.lo, self.R, self.P, self.L = b, C, lo, R, P, L
        self.nodes = list(itertools.product((0, 1), repeat=b))


def lhs(inst, lam):
    forest = [v for v in inst.nodes if v[inst.lo] == inst.R[inst.lo]]
    total = 0.0
    for ns in itertools.product(range(NMAX + 1), repeat=len(forest)):
        w = 1.0
        for n in ns:
            w *= pois(lam, n)
        if w < 1e-14:
            continue
        N = {v: 0 for v in inst.nodes}
        for v, n in zip(forest, ns):
            N[v] = n
        total += w * float(inst.first_arrival_test(N))
    return total


def main():
    rng = random.Random(5)
    worst = 0.0
    cases = [(2, 1, 0), (2, 1, 1), (3, 1, 1), (3, 2, 2), (3, 1, 0), (2, 2, 0)]
    for b, C, lo in cases:
        R = tuple(rng.randint(0, 1) for _ in range(b))
        P, L = rng.randint(0, 2), rng.randint(0, 2)
        lam = rng.uniform(0.2, 0.6)
        inst = Inst(b, C, lo, R, P, L)
        a = lhs(inst, lam)
        c = range_law_stoploss(C, lam, P, 0.5 ** (b - lo), 2 ** lo, b - lo, L)
        rel = abs(a - c) / max(c, 1e-12)
        worst = max(worst, rel)
        print(f'b={b} C={C} lo={lo} P={P} L={L} lam={lam:.3f}: forest {a:.10f} tree {c:.10f} rel {rel:.2e}')
    print('PASS' if worst < 1e-5 else 'FAIL')
    raise SystemExit(0 if worst < 1e-5 else 1)


if __name__ == '__main__':
    main()
