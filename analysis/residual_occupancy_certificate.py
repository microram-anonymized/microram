"""Finite balls-in-bins excess bounds, with outward-rounded arithmetic.

This certifies occupancy inequalities, NOT the complete ORAM. Distinct keys
must have independent uniform destinations. The couplings that apply these
inequalities to the rebuild (binary initialization, the ideal-permutation
correction) are in analysis/bound_certification/REPORT.tex.
No independence between bins or between butterfly stages is assumed.
Its outward-rounded Interval arithmetic is shared by the other certificate
scripts and by gen_residual_tier_bound.py.

Run: python3 analysis/residual_occupancy_certificate.py
"""

import argparse
from dataclasses import dataclass
from decimal import Decimal, Context, ROUND_FLOOR, ROUND_CEILING
from functools import lru_cache
from math import comb, factorial, exp, lgamma, log, log2


DOWN = Context(prec=80, rounding=ROUND_FLOOR)
UP = Context(prec=80, rounding=ROUND_CEILING)


@dataclass(frozen=True)
class Interval:
    low: Decimal
    high: Decimal

    @staticmethod
    def exact(n):
        # Float inputs would obscure which rational quantity is certified.
        if not isinstance(n, (int, Decimal)):
            raise TypeError("use integers or exact Decimal inputs")
        value = Decimal(n)
        return Interval(value, value)

    def __add__(self, other):
        other = interval(other)
        return Interval(DOWN.add(self.low, other.low),
                        UP.add(self.high, other.high))

    def __sub__(self, other):
        other = interval(other)
        return Interval(DOWN.subtract(self.low, other.high),
                        UP.subtract(self.high, other.low))

    def __mul__(self, other):
        other = interval(other)
        ends = ((a, b) for a in (self.low, self.high)
                for b in (other.low, other.high))
        ends = list(ends)
        return Interval(min(DOWN.multiply(a, b) for a, b in ends),
                        max(UP.multiply(a, b) for a, b in ends))

    def __truediv__(self, other):
        other = interval(other)
        if other.low <= 0:
            raise ValueError("denominator must be strictly positive")
        return self * Interval(DOWN.divide(Decimal(1), other.high),
                               UP.divide(Decimal(1), other.low))

    def __pow__(self, exponent):
        if not isinstance(exponent, int) or exponent < 0 or self.low < 0:
            raise ValueError("use a nonnegative base and integer exponent")
        result, base = interval(1), self
        while exponent:
            if exponent & 1:
                result = result * base
            exponent //= 2
            if exponent:
                base = base * base
        return result


def interval(value):
    return value if isinstance(value, Interval) else Interval.exact(value)


def binomial_point(n, bins, k):
    """Enclose P[Bin(n, 1/bins) = k]."""
    if n < 0 or bins < 1 or k < 0:
        raise ValueError("invalid binomial parameters")
    if k > n:
        return interval(0)
    if bins == 1:
        return interval(int(k == n))
    result = (interval(bins - 1) / bins) ** (n - k)
    for j in range(k):
        result = result * (n - j) / (bins * (j + 1))
    return result


def binomial_tail_upper(n, bins, threshold):
    """Geometric bound on the finite tail, not a Poisson approximation."""
    if threshold <= 0:
        return Decimal(1)
    if threshold > n:
        return Decimal(0)
    if bins == 1:
        return Decimal(1)
    ratio = interval(n - threshold) / ((threshold + 1) * (bins - 1))
    if ratio.high >= 1:
        return Decimal(1)
    tail = binomial_point(n, bins, threshold) / (interval(1) - ratio)
    return min(Decimal(1), tail.high)


def choose_z(mean, outputs, slots, cap):
    """Heuristic only. The selected rational z is subsequently certified."""
    best = (float("inf"), 128)
    for numerator in range(65, 225):
        z = numerator / 64
        # This Poisson computation selects a candidate; neither its value nor
        # its optimality is used as a bound. The certificate below is finite.
        delta = sum(exp(-mean + k * log(mean) - lgamma(k + 1)) *
                    (z ** (k - cap) - 1) for k in range(cap + 1, 257))
        score = -(slots + 1) * log(z) + outputs * log(1 + delta)
        best = min(best, (score, numerator))
    return interval(best[1]) / 64


def excess_upper(records, buckets, slots, cap=64, outputs=None, z=None):
    """Upper bound for sum of positively clipped multinomial loads.

    Ordinary occupancy uses outputs=buckets. A balanced butterfly stage can
    use outputs equal to the whole network width, with records/buckets
    describing each disjoint source subnetwork. Negative association gives
    E[product z^excess] <= product E[z^excess].
    """
    if records < 0 or buckets < 1 or slots < 0 or cap < 1:
        raise ValueError("invalid occupancy parameters")
    outputs = buckets if outputs is None else outputs
    if outputs < 1:
        raise ValueError("outputs must be positive")
    if records <= cap:
        return Decimal(0)
    if buckets == 1:
        return Decimal(int(outputs * (records - cap) > slots))
    z = choose_z(records / buckets, outputs, slots, cap) if z is None else z
    z = interval(z)
    if z.low <= 1:
        raise ValueError("Chernoff parameter must exceed one")
    point = binomial_point(records, buckets, cap)
    power, delta = interval(1), interval(0)
    # After this cutoff, the weighted binomial tail has a decreasing ratio.
    # Retain an upper geometric tail; do not silently truncate the sum.
    cutoff = min(records, max(256, cap + 128))
    for k in range(cap + 1, cutoff + 1):
        point = point * (records - k + 1) / (k * (buckets - 1))
        power = power * z
        delta = delta + point * (power - 1)
    if cutoff < records:
        ratio = z * (records - cutoff) / ((cutoff + 1) * (buckets - 1))
        if ratio.high >= 1:
            raise ValueError("increase the cutoff for this mean/z")
        # Drop the negative '-1' part only in the omitted tail.
        delta = delta + point * power * ratio / (interval(1) - ratio)
    upper = ((interval(1) + delta) ** outputs) / (z ** (slots + 1))
    return min(Decimal(1), upper.high)


@lru_cache(None)
def excess_coefficients(cap, threshold):
    """[x^threshold](sum_(e>=1) x^e/(cap+e)!)^k, k=1..threshold."""
    weights = [interval(0)] + [interval(1) / factorial(cap + e)
                               for e in range(1, threshold + 1)]
    coeff = [interval(1)] + [interval(0)] * threshold
    result = []
    for _ in range(threshold):
        next_coeff = [interval(0)] * (threshold + 1)
        for t in range(1, threshold + 1):
            for e in range(1, t + 1):
                next_coeff[t] = next_coeff[t] + coeff[t - e] * weights[e]
        coeff = next_coeff
        result.append(coeff[threshold])
    return tuple(result)


def excess_lower(records, buckets, slots, cap=64):
    """Lower bound from exactly slots+1 excess, with no other full bins.

    For k overloaded bins and total excess t, multinomial probability summed
    over positive excess compositions gives M_k below. Conditional on those
    occupancies, the remaining balls are uniform over the other bins. A union
    bound there gives P[no other overloaded bin] >= 1-(N-k)*tail. Events with
    different k and no other overloaded bins are disjoint, so their lower
    bounds add.
    """
    if records < 0 or buckets < 1 or slots < 0 or cap < 1:
        raise ValueError("invalid occupancy parameters")
    threshold = slots + 1
    total = interval(0)
    for k, coefficient in enumerate(excess_coefficients(cap, threshold), 1):
        used = cap * k + threshold
        if k > buckets or used > records:
            continue
        remain, other_bins = records - used, buckets - k
        mass = interval(comb(buckets, k)) * coefficient
        for j in range(used):
            mass = mass * (records - j) / buckets
        mass = mass * ((interval(other_bins) / buckets) ** remain)
        if other_bins:
            tail = binomial_tail_upper(remain, other_bins, cap + 1)
            no_others = (interval(1) - interval(other_bins) * tail).low
        else:
            no_others = Decimal(int(remain == 0))
        if no_others > 0:
            total = total + mass * no_others
    return max(Decimal(0), total.low)


def permutation_distance(records, bits=128):
    """Upper coupling error between independent outputs and a permutation."""
    return (interval(records * (records - 1)) / (1 << (bits + 1))).high


def binary_initialization_stash_upper(buckets, slots, load=32, cap=64):
    """Union over routing-stage stashes for a balanced binary initialization.

    The uncapacitated ideal network has a multinomial load vector in each
    disjoint subnetwork. The actual network only removes records from it.
    At bit j, each output is Bin(load*2^(j+1), 2^-(j+1)). There are `buckets`
    outputs across the stage. Stage probabilities add; they never multiply.
    The final tier and the residual range route are NOT included here.
    """
    if buckets < 1 or buckets & (buckets - 1) or not 0 <= load <= cap:
        raise ValueError("expected binary buckets and a bounded initial load")
    total = interval(0)
    for bit in range(1, buckets.bit_length()):
        width = 1 << bit
        bound = excess_upper(load * width, width, slots, cap, outputs=buckets)
        total = total + bound
    return min(Decimal(1), total.high)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bucket-bits", type=int, default=22)
    parser.add_argument("--tier-buckets", type=int, default=1)
    args = parser.parse_args()
    if not 1 <= args.bucket_bits <= 30 or not 1 <= args.tier_buckets <= 8:
        parser.error("bucket bits must be 1..30; tier buckets must be 1..8")
    buckets = 1 << args.bucket_bits
    records, slots = 32 * buckets, 64 * args.tier_buckets
    upper = excess_upper(records, buckets, slots)
    print(f"Independent uniform destinations: records={records}, buckets={buckets}, slots={slots}")
    bits = log2(upper) if upper else float("-inf")
    print(f"Certified occupancy upper bound: {upper} (log2 ~ {bits:.6f})")
    if slots >= 128:
        route_upper = binary_initialization_stash_upper(buckets, slots)
        print(f"Binary initialization main-stage stash union: {route_upper}")
    # Lower-bound enumeration is cubic in the threshold; use it for the
    # one-bucket counterexample, not to price every larger tier.
    if slots == 64:
        lower = excess_lower(records, buckets, slots)
        corrected = max(Decimal(0), DOWN.subtract(lower, permutation_distance(records)))
        print(f"Certified occupancy lower bound: {lower}")
        print(f"Ideal 128-bit permutation lower bound: {corrected}")
        target = interval(1) / (1 << 64)
        print(f"Exceeds the entire 2^-64 lifetime target: {corrected > target.high}")
    print("These are occupancy bounds. Intermediate residual range routing is a separate obligation.")


if __name__ == "__main__":
    main()
