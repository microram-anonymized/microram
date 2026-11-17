#!/usr/bin/env python3
"""Conditional final-range certificate for sorted top preparation/init.

This does not certify the intermediate buckets of the current butterfly,
ordinary merges, the complete source-coupling premises, or cryptography.
See REPORT.tex for the disjoint-key deferred-bit proof. No unconditional
independence between early and late selected residuals is assumed.
"""
from __future__ import annotations

from decimal import Decimal, localcontext
from fractions import Fraction

from certify_oram import UP, ZERO, ONE, exp_upper, upper_fraction
from loss_tree import initial, load_tree, next_tree, save_tree


def binomial_weights(population: int, probability: Fraction,
                     cutoff: int) -> list[Decimal]:
    """Upper PMF coefficients; initialize with an exact rational probability."""
    if population < 0 or not 0 < probability < 1 or cutoff < 0:
        raise ValueError("Invalid binomial parameters")
    out = [ZERO] * (cutoff + 1)
    out[0] = upper_fraction((1-probability)**population)
    with localcontext(UP):
        for n in range(1, min(population, cutoff) + 1):
            ratio = Fraction(population-n+1, n)*probability/(1-probability)
            out[n] = out[n-1]*upper_fraction(ratio)
    return out


def mixed_stoploss(w: list[Decimal], groups: int, population: int,
                   probability: Fraction, slots: int) -> dict[str, Decimal]:
    """Bound E[(Bin(population,p) + sum independent root losses - slots)+].

    w[1:] majorizes the full positive mass of a bounded root loss; w[0]=0.
    Coefficient domination uses B(z) exp(groups W(z)), all coefficients
    nonnegative. An external correction must cover truncated root processes.
    """
    cutoff = len(w)-1
    if groups < 1 or not 0 <= slots < cutoff or w[0] != 0 or min(w) < 0:
        raise ValueError("Invalid positive-series parameters")
    b = binomial_weights(population, probability, cutoff)
    c = [ONE] + [ZERO]*cutoff
    with localcontext(UP):
        for n in range(1, cutoff+1):
            c[n] = groups*sum((k*w[k]*c[n-k] for k in range(1, n+1)), ZERO)/n
        coefficients = [sum((b[j]*c[n-j] for j in range(n+1)), ZERO)
                        for n in range(cutoff+1)]
        finite = sum(((n-slots)*coefficients[n]
                      for n in range(slots+1, cutoff+1)), ZERO)
        w2 = sum((w[e]*(1 << e) for e in range(1, cutoff+1)), ZERO)
        b2 = upper_fraction((1+probability)**population)
        tail = (upper_fraction(Fraction(cutoff+1-slots, 1 << (cutoff+1)))
                * b2 * exp_upper(groups*w2))
        return {"finite_positive_series": finite,
                "series_tail_upper": tail,
                "truncated_process_stoploss_upper": finite+tail}


def tree_at_depth(depth: int):
    # Validate the existing cache's arithmetic parameters in load_tree.
    try:
        return load_tree(depth)
    except FileNotFoundError:
        pass
    for previous in range(depth-1, 0, -1):
        try:
            f = load_tree(previous)
            break
        except FileNotFoundError:
            continue
    else:
        previous = 1
        f = initial()
        save_tree(f, 1)
    for d in range(previous+1, depth+1):
        f = next_tree(f)
        save_tree(f, d)
        print(f"Computed shadow-loss tree depth {d}", flush=True)
    return f
