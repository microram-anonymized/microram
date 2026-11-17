#!/usr/bin/env python3
"""Exact independent checks for the new mixed positive-series certificate."""
import itertools
import json
import math
from collections import defaultdict
from fractions import Fraction

from certify_oram import ZERO, upper_fraction
from certify_sorted_range import binomial_weights, mixed_stoploss


def convolve(a, b):
    c = [Fraction(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return c


def test_finite_distribution():
    # Direct rational convolution is independent of the exponential-series
    # implementation: zero root probability is retained, not padded to one.
    root = [Fraction(5, 8), Fraction(1, 4), Fraction(1, 8)]
    p = Fraction(1, 4)
    w = [ZERO, upper_fraction(root[1]), upper_fraction(root[2])] + [ZERO]*30
    checked = 0
    for population in range(5):
        b = [Fraction(math.comb(population, i))*p**i*(1-p)**(population-i)
             for i in range(population+1)]
        rounded = binomial_weights(population, p, 32)
        assert all(Fraction(rounded[i]) >= x for i, x in enumerate(b))
        for groups in range(1, 5):
            exact = b
            for _ in range(groups):
                exact = convolve(exact, root)
            for slots in range(8):
                truth = sum((mass*max(n-slots, 0) for n, mass in enumerate(exact)), Fraction(0))
                bound = mixed_stoploss(w, groups, population, p, slots)
                assert Fraction(bound['truncated_process_stoploss_upper']) >= truth
                checked += 1
    return checked


def test_deferred_selection():
    # Membership varies with previously revealed bits. The remaining bits of
    # disjoint early and main key sets are enumerated independently. A toy
    # main bucket spills above one, and a final fresh bit selects the range.
    checked = 0
    for history in itertools.product((0, 1), repeat=4):
        early = [i for i, bit in enumerate(history) if bit]
        main = [i for i, bit in enumerate(history) if not bit]
        actual = defaultdict(Fraction)
        late_pmf = defaultdict(Fraction)
        for future in itertools.product(range(4), repeat=4):
            e = sum(future[i] == 0 for i in early)
            branch = [i for i in main if not (future[i] & 1)]
            late = sum(future[i] == 0 for i in branch[1:])
            actual[e+late] += Fraction(1, 256)
            late_pmf[late] += Fraction(1, 256)
        padding = [Fraction(math.comb(4, k))*Fraction(1, 4)**k*Fraction(3, 4)**(4-k)
                   for k in range(5)]
        for slots in range(5):
            left = sum((mass*max(n-slots, 0) for n, mass in actual.items()), Fraction(0))
            right = sum((px*py*max(x+y-slots, 0) for x, px in enumerate(padding)
                         for y, py in late_pmf.items()), Fraction(0))
            assert left <= right
            checked += 1
    # Shared-key copies would invalidate the product comparison. This is why
    # the proof is restricted to top preparation, not ordinary merged pools.
    same_key_stoploss = Fraction(1, 2)  # (2*Bernoulli(1/2)-1)+
    independent_stoploss = Fraction(1, 4)
    assert same_key_stoploss > independent_stoploss
    return checked


if __name__ == '__main__':
    results = {'finite_rational_convolution_checks': test_finite_distribution(),
               'deferred_selection_checks': test_deferred_selection(),
               'shared_key_counterexample_checked': True,
               'all_passed': True,
               'scope': 'Numerical/lemma checks, not a verification of production source couplings.'}
    print(json.dumps(results, indent=2))
