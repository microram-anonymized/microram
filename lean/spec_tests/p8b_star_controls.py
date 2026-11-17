#!/usr/bin/env python3
"""Rate/stoploss controls. Numerical expectations are smoke checks,
not certificates or substitutes for the Lean comparison theorem."""
from fractions import Fraction as F
from itertools import product
from math import exp

shapes = [(4, 2), (6, 2), (8, 2), (8, 4)]
checked = 0
for L, (d, t), j in product([F(0), F(32), F(32) + F(1, 2**36)], shapes, range(32)):
    lo, hi = F(j, 32), F(j + 1, 32)
    def center(theta):
        return L * (1 - theta * F(t - 1, (d - 1) * t))
    def shared(theta):
        return L * theta / (d - 1)
    for theta in [lo, (lo + hi)/2, hi]:
        assert theta <= 1
        assert theta * F(t - 1, (d - 1)*t) <= 1
        assert center(theta) <= center(lo)
        assert shared(theta) <= shared(hi)
        assert (d//t - 1) * shared(hi) <= center(lo)
        assert shared(hi) <= L
        checked += 1

# Edge increasing differences of capacity stoploss, including strict examples.
strict = 0
for a, b, da, db, other, C, S in product(range(4), repeat=7):
    def f(x, y):
        return max(max(x-C, 0) + max(y-C, 0) + other - S, 0)
    mixed = f(a+da,b+db) + f(a,b) - f(a+da,b) - f(a,b+db)
    assert mixed >= 0
    strict += mixed > 0
assert strict > 0

def poisson(rate, cutoff=13):
    p = [exp(-rate)]
    for k in range(1, cutoff + 1):
        p.append(p[-1] * rate / k)
    return p

def expectation(mu, lam, gamma, C, S):
    # Distribute sum(shared counts) and sum(leaf excess); retain shared counts
    # whole in both center and leaf. Independent b/y primitives per edge.
    table = {(0, 0): 1.0}
    for l, g in zip(lam, gamma):
        edge = {}
        for b, pb in enumerate(poisson(l-g)):
            for y, py in enumerate(poisson(g)):
                key = (y, max(b+y-C, 0))
                edge[key] = edge.get(key, 0.0) + pb*py
        out = {}
        for (ys, es), p in table.items():
            for (y, e), q in edge.items():
                key = (ys+y, es+e)
                out[key] = out.get(key, 0.0) + p*q
        table = out
    return sum(p*pa*max(max(a+y-C, 0)+e-S, 0)
               for (y,e),p in table.items()
               for a,pa in enumerate(poisson(mu-sum(gamma))))

smokes = 0
for n, C, S in product([1,2,3], [0,1], [0,1]):
    mu, lam = 1.0, [0.5]*n
    low, high = [0.05]*n, [0.2]*n
    a, b = expectation(mu, lam, low, C, S), expectation(mu, lam, high, C, S)
    assert a <= b + 1e-8, (n,C,S,a,b)
    smokes += 1
print(f"P8bStar controls PASS: {checked} exact rate cases; "
      f"16384 mixed differences ({strict} strict); {smokes} truncated numerical star comparisons")
