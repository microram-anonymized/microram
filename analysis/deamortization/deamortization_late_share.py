#!/usr/bin/env python3
"""
Sensitivity of the minimum rebuild speed to work that follows a carry.

The streamable model of deamortization_analysis.py lets the k units of a
k -> k+1 merge run before the carry arrives, so only the carry's own unit
follows its arrival.  Here a share c of the merge's k+1 units (but at least
the carry's unit) follows the arrival instead:

    D_n = max(n, D_{n-1} + (k+1-late)/s) + late/s,   late = max(c(k+1), 1),

with the same zero-cost adoption at k=0 and the same stall rule D_n <= n+2.
c=1 means that no preparation runs before the carry arrives.

Run with no arguments to print, for B = 2, 4, 8, the largest share that keeps
the model's minimum speed, and the speed when every merge starts at arrival.
Exact rational arithmetic; the bisection tolerance is printed with each value.
"""

from fractions import Fraction as F

CYCLES = 300


def average_work(B: int) -> F:
    return F(B + 1, 2) - F(1, B)


def no_stall(B: int, speed: F, share: F, cycles: int = CYCLES) -> bool:
    if speed < average_work(B):
        return False
    previous = None
    for n in range(B * cycles):
        k = n % B
        if previous is None:
            publication = F(0)
        elif k == 0:
            publication = max(F(n), previous)
        else:
            late = max(share * (k + 1), F(1))
            publication = (max(F(n), previous + (k + 1 - late) / speed)
                           + late / speed)
        if publication > n + 2:
            return False
        previous = publication
    return True


def minimum_speed(B: int, share: F, steps: int = 40) -> float:
    lo, hi = F(1, 2), F(4 * B)
    for _ in range(steps):
        mid = (lo + hi) / 2
        if no_stall(B, mid, share):
            hi = mid
        else:
            lo = mid
    return float(hi)


def largest_share(B: int, steps: int = 30) -> float:
    """Largest share c whose minimum speed equals that of c = 1/(k+1)."""
    target = F(minimum_speed(B, F(0))).limit_denominator(1000)
    lo, hi = F(0), F(1)
    for _ in range(steps):
        mid = (lo + hi) / 2
        if no_stall(B, target, mid):
            lo = mid
        else:
            hi = mid
    return float(lo)


def main() -> None:
    for B in (2, 4, 8):
        base = minimum_speed(B, F(0))
        on_arrival = minimum_speed(B, F(1))
        print(f"B={B}: average work {float(average_work(B)):.4f}, "
              f"minimum speed {base:.4f} with pre-routing, "
              f"{on_arrival:.4f} when merges start at arrival; "
              f"unchanged up to share {largest_share(B):.4f}")


if __name__ == "__main__":
    main()
