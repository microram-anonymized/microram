#!/usr/bin/env python3
"""The positive-series stop-loss bound for complete-home excesses
(positive_excess_bound, with its cutoff rule) and the incoming-carry shape
check."""
from decimal import localcontext
from fractions import Fraction
from functools import lru_cache

from certify_oram import (UP, ZERO, certificate, exp_upper, upper_fraction,
                          weighted_poisson_pmf)


def validate_carry(row, shapes):
    if row['level'] == 1:
        return
    producer = shapes[row['level']-1, 8]
    if (not producer['terminal_digit'] or producer['radix'] != 1
            or producer['out_buckets'] != 1 << row['carry_bits']
            or producer['main_bits'] != row['carry_bits']):
        raise ValueError('Incoming tier is not the audited full binary carry')


# The positive series' truncation: the smallest cutoff, doubling from 256,
# whose omitted tail (K+1-s) 2^-(K+1) exp(nodes W(2)) -- the certificate's own
# tail term -- is at most 2^-128.  It is an evaluation parameter only: every
# cutoff gives a valid upper bound, and this one keeps the omitted tail far
# below any target.  Up to 2^24 homes at 64 slots per home 256 already
# suffices, so those values are the fixed-256 ones.
SERIES_TAIL_TARGET = Fraction(1, 1 << 128)
SERIES_MIN_CUTOFF = 256


def series_cutoff(nodes, slots, capacity=64, mean=Fraction(32)):
    with localcontext(UP):
        at_two = upper_fraction(Fraction(1, 1 << capacity))*exp_upper(mean)
        growth = exp_upper(nodes*at_two)
        cutoff = SERIES_MIN_CUTOFF
        while (cutoff <= slots or
               upper_fraction(Fraction(cutoff+1-slots, 2**(cutoff+1)))*growth
               > upper_fraction(SERIES_TAIL_TARGET)):
            cutoff *= 2
    return cutoff


@lru_cache(maxsize=None)
def positive_excess_bound(nodes, slots, capacity=64, mean=Fraction(32), cutoff=None):
    """Stop-loss upper bound for complete-home excesses in independent families.

    Poissonize the two independent complete-home vectors separately with the
    existing increasing-differences comparison, then pad each mean to `mean`.
    One Poisson home's excess has positive weights w[e]=P(Pois(mean)=C+e).
    The existing certificate majorizes (1+W)^nodes by exp(nodes*W), including
    its infinite tail. This is not a fresh-selected-tier comparison.
    `cutoff` defaults to series_cutoff (above); an explicit one is used as is.
    """
    if cutoff is None and nodes >= 1 and capacity >= 1 and 0 < mean <= capacity and slots >= 0:
        cutoff = series_cutoff(nodes, slots, capacity, mean)
    if nodes < 1 or capacity < 1 or not 0 < mean <= capacity or not 0 <= slots < cutoff:
        raise ValueError('Invalid positive excess parameters')
    pmf = weighted_poisson_pmf(mean, Fraction(0), capacity+cutoff)
    weights = [ZERO] + pmf[capacity+1:]
    with localcontext(UP):
        # Drop N>C in E[2**(N-C); N>C] for a simple upper bound on W(2).
        at_two = upper_fraction(Fraction(1, 1 << capacity))*exp_upper(mean)
    return certificate(weights, at_two, nodes, slots)
