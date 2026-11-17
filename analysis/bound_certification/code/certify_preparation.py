#!/usr/bin/env python3
"""Conditional A-only main-preparation certificate by coordinatewise deletion.

Use a subset witness and the positive exponential envelope of original
old-home counts. No balancing, retained-load exchangeability or nonlinear
capped-loss comparison is needed. Old-tier placement, cross/radix finish,
merged residual pools and engine-history independence remain outside scope.
"""
from __future__ import annotations

from decimal import localcontext
from fractions import Fraction
from functools import lru_cache
from math import comb, factorial

from certify_oram import ZERO, UP, exp_upper, upper_fraction

CUTOFF = 64
CAPACITY = 64
MEAN = Fraction(32)


@lru_cache(maxsize=None)
def witness_term(size, slots, capacity=CAPACITY, mean=MEAN):
    """One subset's Chernoff bound; its chosen z is an exact rational.

    P[sum Z_i >= capacity*size+slots+1] <= exp(mean*size*(z-1))/z^threshold.
    Optimizing this elementary expression gives z=threshold/(mean*size).
    """
    if size < 1 or slots < 0 or not 0 < mean <= capacity:
        raise ValueError('Invalid subset witness parameters')
    threshold = capacity * size + slots + 1
    rate = mean * size
    z = Fraction(threshold) / rate
    with localcontext(UP):
        return exp_upper(rate * (z - 1)) * upper_fraction(z**(-threshold))


def stage_bound(nodes, slots, cutoff=CUTOFF, capacity=CAPACITY, mean=MEAN):
    """Bound sum of capped excesses using only a joint exponential envelope.

    Finite subset sizes use their individual rational tilts. For the rest,
    choose z=2 and C(nodes,j) <= nodes^j/j!. The exponential-series tail
    has a geometric ratio bound after cutoff. All arithmetic rounds upward;
    the tail denominator is formed as an exact rational from an upper bound.
    """
    if nodes < 1 or slots < 0 or cutoff < 1 or not 0 < mean <= capacity:
        raise ValueError('Invalid stage parameters')
    with localcontext(UP):
        finite = sum((comb(nodes, j) * witness_term(j, slots, capacity, mean)
                      for j in range(1, min(nodes, cutoff) + 1)), ZERO)
        tail = ZERO
        if nodes > cutoff:
            mu = nodes * exp_upper(mean) * upper_fraction(Fraction(1, 2**capacity))
            first = cutoff + 1
            ratio_upper = Fraction(mu) / (first + 1)
            if ratio_upper >= 1:
                raise ValueError('Increase cutoff for a decreasing tail')
            tail = (upper_fraction(Fraction(1, 2**(slots + 1))) *
                    mu**first * upper_fraction(Fraction(1, factorial(first))) *
                    upper_fraction(1 / (1 - ratio_upper)))
        return finite + tail, finite, tail
