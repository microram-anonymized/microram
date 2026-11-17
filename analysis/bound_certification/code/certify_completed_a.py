#!/usr/bin/env python3
"""Completed-A joint-state numerical kernel.

Native shapes, applicability and lifetime accounting are evaluated by
certify_separated_sources.py. All coefficients are upward enclosures.
"""
from __future__ import annotations
import math
from decimal import localcontext
from fractions import Fraction as Q

from certify_oram import UP, ZERO, LAM, describe, upper_fraction, weighted_poisson_pmf
from certify_sorted_range import mixed_stoploss
from loss_tree import K, Z, SCALE, ceildiv, square_bytes


def binomial_rows(n, p, scale):
    """Exact rational binomial coefficients, individually rounded upwards."""
    if not 0 <= p <= 1 or n < 0 or scale < 1:
        raise ValueError("Invalid binomial parameters")
    a, d = p.numerator, p.denominator
    return [[ceildiv(scale * math.comb(m, j) * a**j * (d-a)**(m-j), d**m)
             for j in range(m+1)] for m in range(n+1)]


def thin(f, p, scale=SCALE):
    rows, cutoff = len(f), len(f[0])-1
    bm, br = binomial_rows(rows-1, p, scale), binomial_rows(cutoff, p, scale)
    tmp = [[0]*(cutoff+1) for _ in f]
    for m, row in enumerate(f):
        for v in range(cutoff+1):
            tmp[m][v] = ceildiv(sum(row[r]*br[r][v] for r in range(v, cutoff+1)), scale)
    return [[ceildiv(sum(tmp[m][v]*bm[m][u] for m in range(u, rows)), scale)
             for v in range(cutoff+1)] for u in range(rows)]


def convolve(f, h, cutoff=K, scale=SCALE):
    """Exact packed convolution, dropping only states with total > cutoff.

    No cap is applied here: partial radix sums must retain their main count.
    The carry-free digit width is derived from the actual integer inputs.
    """
    stride = 2*cutoff+1
    bound = min(len(f), len(h))*(cutoff+1)*max(map(max, f))*max(map(max, h))
    size = max(1, (bound.bit_length()+7)//8)
    def pack(a):
        raw = bytearray(((len(a)-1)*stride+cutoff+1)*size)
        for m, row in enumerate(a):
            for r, mass in enumerate(row):
                offset = (m*stride+r)*size
                raw[offset:offset+size] = mass.to_bytes(size, 'little')
        return int.from_bytes(raw, 'little')
    a, b = pack(f), pack(h)
    # Polarization reuses the optional exact GMP square accelerator.
    def square(x):
        return int.from_bytes(square_bytes(x.to_bytes(max(1, (x.bit_length()+7)//8), 'little')), 'little')
    product = (square(a+b)-square(abs(a-b)))//4
    raw = product.to_bytes(max(1, (product.bit_length()+7)//8), 'little')
    result = [[0]*(cutoff+1) for _ in range(min(cutoff+1, len(f)+len(h)-1))]
    for m, row in enumerate(result):
        for r in range(cutoff-m+1):
            offset = (m*stride+r)*size
            row[r] = ceildiv(int.from_bytes(raw[offset:offset+size], 'little'), scale)
    return result


def terminal(f, radix, p, capacity=Z, cutoff=K, scale=SCALE):
    q = thin(f, p, scale)
    total = q
    for _ in range(1, radix):
        total = convolve(total, q, cutoff, scale)
    result = [0]*(cutoff+1)
    for m, row in enumerate(total):
        for v in range(cutoff-m+1):
            result[v+max(m-capacity, 0)] += row[v]
    return result


def poisson_tail(mean, cutoff=K):
    if mean >= cutoff+2:
        raise ValueError('Poisson tail ratio requires mean < cutoff+2')
    with localcontext(UP):
        return (weighted_poisson_pmf(mean, Q(0), cutoff+1)[cutoff+1]
                * upper_fraction(1/(1-mean/Q(cutoff+2))))


def truncation(depth, radix, p, groups, cutoff=K):
    """Union over binary nodes and the terminal total; CS per completed root."""
    mu = LAM if radix == 1 else radix*LAM*p
    with localcontext(UP):
        bad = radix*((1 << depth)-1)*poisson_tail(LAM, cutoff)
        if radix > 1:
            bad += poisson_tail(mu, cutoff)
        return groups*UP.next_plus(UP.sqrt(upper_fraction(mu+mu*mu)*bad))


def radix_classes(word_bits, block_bits, radix):
    words = 1 << (word_bits-block_bits)
    low, extra = divmod(words, radix)
    return [(Q(low+1, words), extra), (Q(low, words), radix-extra)] if extra else [(Q(low, words), radix)]


def evaluate(f, *, k, digit, index_bits, early, density=Q(1), word_bits=64):
    if digit <= 1 or not 0 <= index_bits < k or density < 1 or early < 0:
        raise ValueError('Outside ordinary completed-A domain')
    radix, e = digit, 0
    while radix % 2 == 0:
        radix //= 2
        e += 1
    b = k+e
    if b >= word_bits:
        raise ValueError('No high word remains')
    depth, groups = b-index_bits, 1 << index_bits
    rows = []
    with localcontext(UP):
        job = ZERO
        for p, multiplicity in radix_classes(word_bits, b, radix):
            if not multiplicity or not p:
                continue
            weights = ([sum(row[v] for row in f) for v in range(K+1)]
                       if radix == 1 else terminal(f, radix, p))
            w = [ZERO]+[upper_fraction(Q(weights[v], SCALE)) for v in range(1, K+1)]
            parts = mixed_stoploss(w, groups, early, p/Q(1 << depth), Z)
            error = truncation(depth, radix, p, groups)
            column = parts['truncated_process_stoploss_upper']+error
            job += multiplicity*(1 << depth)*column*upper_fraction(density)
            rows.append(dict(q_exact=str(p), multiplicity=multiplicity,
                             truncation_upper=str(error), column_upper=str(column),
                             **{key: str(value) for key, value in parts.items()}))
        return describe('completed_A_ranges', min(job, 1), k=k, digit=digit,
                        index_bits=index_bits, depth=depth, early_cap=early,
                        density_exact=str(density), radix_classes=rows)
