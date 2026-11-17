#!/usr/bin/env python3
"""Randomized floating-point tests of the X1/X2 statements (RebuildBound/Spec/Phase0.lean).

Plausible cannot test statements about ENNReal-valued tests and measures, so
this script evaluates the same definitions in floating point on small grids:

* X1_cap, X1_thin, X1_add: random tests phi in class T(c) are pushed through
  capAt, thinAt and sumAlong, and the three class conditions are checked on
  every grid point whose neighbours stay in the grid.
* X1_terminal: g(total shadow) for random convex nondecreasing g.
* X2: E f(x + V) <= E f(x + V_1 + ... + V_K), K ~ Po(1), for random
  directionally convex f and random finite laws of V.

Negative controls check that each test can fail: a cap above the threshold,
a test without condition 3, and a concave f.

Usage: spec_tests/phase0_statements.py [--trials N] [--seed S]
"""
from __future__ import annotations

import argparse
import itertools
import math
import random

TOL = 1e-9
INF = float('inf')


# --- tests as functions of a state vector ----------------------------------
# A state vector is a tuple indexed by (node, slot), slot 0 = main, 1 = shadow,
# flattened as 2*node + slot.

def convex_seq(rng, nondecreasing=True):
    """A random convex function on N, as a closure."""
    a = rng.uniform(0, 2) if nondecreasing else rng.uniform(-3, 2)
    b = rng.uniform(0, 1)
    t = rng.randint(0, 6)
    kind = rng.randrange(3)
    if kind == 0:
        return lambda s: a * s + b * s * s if nondecreasing else (s - t) ** 2 * b + a * s
    if kind == 1:
        return lambda s: b * max(s - t, 0) + (a * s if nondecreasing else 0)
    return lambda s: b * max(s - t, 0) ** 2 + (a * s if nondecreasing else -abs(a) * min(s, t))


def random_class_t(rng, nodes, threshold=None):
    """phi in T(c): sums of h(<w, x>) with w(R_a) >= w(M_a), plus, when
    `threshold = (a, C)`, a penalty on M_a >= C that breaks condition 3 there
    (so phi is in T(c) with c_a = C, and not in T(top) at a)."""
    terms = []
    for _ in range(rng.randint(1, 3)):
        w = []
        for _a in range(nodes):
            m = rng.randint(0, 2)
            w += [m, m + rng.randint(0, 2)]
        terms.append((rng.uniform(0.1, 2), w, convex_seq(rng)))
    pen = None
    if threshold is not None:
        a, C = threshold
        k = rng.uniform(0.5, 3)
        pen = (a, C, k)

    def phi(x):
        v = sum(c * h(sum(wi * xi for wi, xi in zip(w, x))) for c, w, h in terms)
        if pen is not None:
            a, C, k = pen
            v += k * max(x[2 * a] - C, 0) ** 2
        return v
    return phi


def unit(n, k):
    e = [0] * n
    e[k] = 1
    return tuple(e)


def add(x, y):
    return tuple(a + b for a, b in zip(x, y))


def check_class_t(phi, nodes, c, N):
    """Check the three conditions of T(c) on the grid [0, N)^(2*nodes).
    c[a] is None for top. Returns the first violation or None."""
    n = 2 * nodes
    for x in itertools.product(range(N), repeat=n):
        fx = phi(x)
        for k in range(n):
            xk = add(x, unit(n, k))
            if phi(xk) < fx - TOL * (1 + abs(fx)):
                return ('mono', x, k)
            for l in range(k, n):
                xl = add(x, unit(n, l))
                lhs = phi(xk) + phi(xl)
                rhs = phi(add(xk, unit(n, l))) + fx
                if lhs > rhs + TOL * (1 + abs(rhs)):
                    return ('dirconvex', x, k, l)
        for a in range(nodes):
            if c[a] is None or x[2 * a] < c[a]:
                if phi(add(x, unit(n, 2 * a))) > phi(add(x, unit(n, 2 * a + 1))) + TOL * (1 + abs(fx)):
                    return ('main_le_shadow', x, a)
    return None


def cap_at(phi, a, C):
    def chi(x):
        x = list(x)
        m, r = x[2 * a], x[2 * a + 1]
        x[2 * a], x[2 * a + 1] = min(m, C), r + max(m - C, 0)
        return phi(tuple(x))
    return chi


def binom_pmf(n, p):
    return [math.comb(n, k) * p ** k * (1 - p) ** (n - k) for k in range(n + 1)]


def thin_at(phi, a, p):
    def psi(x):
        bm, br = binom_pmf(x[2 * a], p), binom_pmf(x[2 * a + 1], p)
        total = 0.0
        for m, pm in enumerate(bm):
            for r, pr in enumerate(br):
                y = list(x)
                y[2 * a], y[2 * a + 1] = m, r
                total += pm * pr * phi(tuple(y))
        return total
    return psi


def sum_along(phi, parent, parents):
    def psi(x):
        y = [0] * (2 * parents)
        for b, a in enumerate(parent):
            y[2 * a] += x[2 * b]
            y[2 * a + 1] += x[2 * b + 1]
        return phi(tuple(y))
    return psi


# --- X2 -----------------------------------------------------------------------

def random_dirconvex(rng, dim, convex=True):
    terms = []
    for _ in range(rng.randint(1, 3)):
        w = [rng.randint(0, 2) for _ in range(dim)]
        terms.append((rng.uniform(0.1, 2), w, convex_seq(rng, nondecreasing=rng.random() < 0.5)))
    if convex:
        # a constant shift keeps the values nonnegative on the region used
        return lambda x: 50 + sum(c * h(sum(wi * xi for wi, xi in zip(w, x))) for c, w, h in terms)
    return lambda x: 50 + 10 * math.sqrt(1 + sum(x))  # concave: a negative control


def random_law(rng, dim):
    support = {tuple(rng.randint(0, 2) for _ in range(dim)) for _ in range(rng.randint(1, 4))}
    weights = [rng.random() for _ in support]
    s = sum(weights)
    return [(v, w / s) for v, w in zip(sorted(support), weights)]


def conv(law_a, law_b):
    out = {}
    for va, pa in law_a:
        for vb, pb in law_b:
            v = add(va, vb)
            out[v] = out.get(v, 0.0) + pa * pb
    return list(out.items())


def x2_gap(f, law, x, kmax=40):
    lhs = sum(p * f(add(x, v)) for v, p in law)
    dim = len(x)
    power = [(tuple([0] * dim), 1.0)]
    rhs = 0.0
    for k in range(kmax + 1):
        pk = math.exp(-1) / math.factorial(k)
        rhs += pk * sum(p * f(add(x, v)) for v, p in power)
        power = conv(power, law)
        # merge tiny masses to keep the support small
        power = [(v, p) for v, p in power if p > 1e-300]
    return rhs - lhs


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--trials', type=int, default=60)
    ap.add_argument('--seed', type=int, default=1)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    N = 5
    failures = 0
    controls = {'cap_above_threshold': 0, 'no_condition3': 0, 'concave_x2': 0}

    for t in range(args.trials):
        nodes = 2
        C = rng.randint(1, 3)
        a = rng.randrange(nodes)
        # phi in T(c) with c_a = C (condition 3 only below C), c_other = top.
        phi = random_class_t(rng, nodes, threshold=(a, C))
        c = [None] * nodes
        c[a] = C
        assert check_class_t(phi, nodes, c, N) is None, 'generator broke T(c)'

        # X1_cap with C <= c_a: result in T(update c a top).
        Ccap = rng.randint(0, C)
        v = check_class_t(cap_at(phi, a, Ccap), nodes, [None] * nodes, N)
        if v is not None:
            failures += 1
            print('X1_cap FAILED', t, v)
        # Control: capacity above the threshold usually breaks condition 2 or 3.
        if check_class_t(cap_at(phi, a, C + 2), nodes, [None] * nodes, N) is not None:
            controls['cap_above_threshold'] += 1

        # X1_thin keeps T(c).
        p = rng.choice([0.0, 0.5, 1.0, rng.random()])
        b = rng.randrange(nodes)
        v = check_class_t(thin_at(phi, b, p), nodes, c, N - 1)
        if v is not None:
            failures += 1
            print('X1_thin FAILED', t, v)

        # X1_add: phi2 in T(top) on 2 parents, 3 children.
        phi2 = random_class_t(rng, 2)
        assert check_class_t(phi2, 2, [None, None], N) is None
        parent = [rng.randrange(2) for _ in range(3)]
        v = check_class_t(sum_along(phi2, parent, 2), 3, [None] * 3, 3)
        if v is not None:
            failures += 1
            print('X1_add FAILED', t, v)
        # Control: addition of a T(c) test with a finite threshold can break
        # condition 3 when two children feed the capped node.
        if check_class_t(sum_along(phi, [a, a, 1 - a], 2), 3, [C, C, None], 3) is not None:
            controls['no_condition3'] += 1

        # X1_terminal.
        g = convex_seq(rng)
        term = lambda x, g=g: g(sum(x[1::2]))
        v = check_class_t(term, 2, [None, None], N)
        if v is not None:
            failures += 1
            print('X1_terminal FAILED', t, v)

        # X2.
        dim = rng.randint(1, 3)
        f = random_dirconvex(rng, dim)
        assert all(f(add(y, unit(dim, k))) + f(add(y, unit(dim, l)))
                   <= f(add(add(y, unit(dim, k)), unit(dim, l))) + f(y) + 1e-9
                   for y in itertools.product(range(6), repeat=dim)
                   for k in range(dim) for l in range(dim)), 'generator broke DirConvex'
        law = random_law(rng, dim)
        x = tuple(rng.randint(0, 3) for _ in range(dim))
        gap = x2_gap(f, law, x)
        if gap < -1e-7:
            failures += 1
            print('X2 FAILED', t, gap, law, x)
        if x2_gap(random_dirconvex(rng, dim, convex=False), law, x) < -1e-7:
            controls['concave_x2'] += 1

    print(f'{args.trials} trials, {failures} statement failures; negative controls that '
          f'failed as they may: {controls}')
    raise SystemExit(1 if failures else 0)


if __name__ == '__main__':
    main()
