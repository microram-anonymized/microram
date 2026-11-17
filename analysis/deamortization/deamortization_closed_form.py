"""Exact steady-state formulas for the report's streamable B-ary model.

Speeds are per-level work units per incoming-carry interval. Probe counts
include current, triggering, and waiting tables, with an initially empty
level and completions preceding simultaneous arrivals.
"""

from fractions import Fraction
from math import isqrt


def minimum_speed_exact(B: int) -> Fraction:
    """Minimum speed for power-of-two B, including the average-work bound."""
    if B < 2 or B & (B - 1):
        raise ValueError("B must be a power of two and at least 2")
    # Smallest integer r with r(r+1) >= 4(B+1), clipped to [2, B].
    r = (isqrt(16 * B + 17) - 1) // 2
    if r * (r + 1) < 4 * (B + 1):
        r += 1
    r = min(B, max(2, r))
    average = Fraction(B + 1, 2) - Fraction(1, B)
    burst = Fraction(2 * B + 5 - r, 2) - Fraction(2 * (B + 1), r)
    return max(average, burst)


def average_at_minimum_exact(B: int) -> Fraction:
    """Average online tables per regular level at the minimum speed."""
    s = minimum_speed_exact(B)
    if B == 2:
        return Fraction(3, 2)
    if B == 4:
        return Fraction(11, 6)
    h = s.numerator // s.denominator
    t = B - h
    return (1 + Fraction(1, B) + 1 / s
            + t * (t + 1) * (3 * h + t + 2 - 3 * s) / (6 * B * s))
