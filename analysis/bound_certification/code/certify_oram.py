#!/usr/bin/env python3
"""Positive-series, outward-rounded ORAM overflow certificates.

Python 3.10+; standard library only.

This certifies the numerical inequalities in the accompanying proof review,
not the implementation's structural/routing invariants. All acceptance tests
use exact rational comparisons with an outward-rounded Decimal upper bound.
No simulation, floating-point optimization, or assumed inter-stage
independence is used. The displayed log2 values are descriptive only.
"""
from __future__ import annotations
import math
from decimal import Decimal, Context, ROUND_CEILING, localcontext
from fractions import Fraction

PRECISION = 90
CUTOFF = 256
UP = Context(prec=PRECISION, rounding=ROUND_CEILING)
LAM = Fraction(32) + Fraction(1, 2**36)
ZERO, ONE = Decimal(0), Decimal(1)


def upper_fraction(x: Fraction | int) -> Decimal:
    x = Fraction(x)
    return UP.divide(Decimal(x.numerator), Decimal(x.denominator))


def exp_upper(x: Fraction | Decimal) -> Decimal:
    """exp is correctly rounded; one upward ulp encloses its exact value."""
    argument = upper_fraction(x) if isinstance(x, Fraction) else x
    return UP.next_plus(UP.exp(argument))


def weighted_poisson_pmf(a: Fraction, b: Fraction, maximum: int) -> list[Decimal]:
    """Upper bounds for Pr[Pois(a) + 2 Pois(b) = n], independent counts."""
    if a < 0 or b < 0 or maximum < 0:
        raise ValueError("Nonnegative rates and maximum are required")
    aa, bb = upper_fraction(a), upper_fraction(b)
    p = [ZERO] * (maximum + 1)
    p[0] = exp_upper(-a-b)
    with localcontext(UP):
        for n in range(1, maximum + 1):
            value = aa * p[n-1]
            if n >= 2:
                value += 2 * bb * p[n-2]
            p[n] = value / n
    return p


def witnesses(mu: Fraction, lam: Fraction, gamma: Fraction, leaves: int,
              cutoff: int = CUTOFF) -> tuple[list[Decimal], Decimal]:
    """w[e] majorizes the subset-witness mass at positive excess e.

    Also returns a bound on W(2)=sum_{e>=1} w_e 2^e, including the full tail.
    Center mean mu, each leaf mean lam, each center/leaf shared rate gamma.
    """
    if leaves < 0 or mu < leaves*gamma or lam < gamma or gamma < 0:
        raise ValueError("Invalid nonnegative star rates")
    w = [ZERO] * (cutoff + 1)
    w2 = ZERO
    # (multiplicity, subset size, single-count rate, double-count rate)
    subsets: list[tuple[int,int,Fraction,Fraction]] = []
    for k in range(leaves+1):
        subsets.append((math.comb(leaves,k), k+1,
                        mu+k*lam-2*k*gamma, k*gamma))
    for k in range(1,leaves+1):
        subsets.append((math.comb(leaves,k), k, k*lam, Fraction(0)))
    with localcontext(UP):
        for multiplicity, size, a, b in subsets:
            threshold = 64 * size
            pmf = weighted_poisson_pmf(a,b,threshold+cutoff)
            for e in range(1,cutoff+1):
                w[e] += multiplicity * pmf[threshold+e]
            # Drop the truncation in E[2^(X-threshold); X>threshold].
            w2 += multiplicity * upper_fraction(Fraction(1,2**threshold)) * exp_upper(a+3*b)
    return w, w2


def certificate(w: list[Decimal], w2: Decimal, groups: int, slots: int,
                patterns: int = 1) -> Decimal:
    """Upper bound patterns * E[(total comparison excess - slots)_+]."""
    K = len(w)-1
    if not (groups >= 1 and patterns >= 1 and 0 <= slots < K):
        raise ValueError("Invalid groups, patterns, slots, or series cutoff")
    c = [ZERO] * (K+1)
    c[0] = ONE
    with localcontext(UP):
        kw = [k*w[k] for k in range(K+1)]
        for n in range(1,K+1):
            value = sum((kw[k]*c[n-k] for k in range(1,n+1)), ZERO)
            c[n] = groups * value / n
        finite = sum(((n-slots)*c[n] for n in range(slots+1,K+1)), ZERO)
        # For n>K, (n-slots)/2^n is decreasing, since K>=slots+1.
        tail = upper_fraction(Fraction(K+1-slots,2**(K+1))) * exp_upper(groups*w2)
        return patterns * (finite + tail)


def describe(name: str, bound: Decimal, **metadata: object) -> dict:
    if bound <= 0:
        raise ValueError("A positive computed upper bound was expected")
    approximation = math.log2(float(bound))
    exponent = math.floor(-approximation)
    exact_bound = Fraction(bound)
    def threshold(e: int) -> Fraction:
        return Fraction(1, 2**e) if e >= 0 else Fraction(2**(-e))
    while exact_bound > threshold(exponent):
        exponent -= 1
    while exact_bound <= threshold(exponent+1):
        exponent += 1
    return {"name": name, "probability_upper_decimal": str(bound),
            "certified_power_of_two_exponent": exponent,
            "approximate_log2_for_display_only": approximation, **metadata}
