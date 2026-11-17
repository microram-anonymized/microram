#!/usr/bin/env python3
"""Exact occupancy enumeration for the finite-multinomial lower witness."""
from collections import defaultdict
from fractions import Fraction
from math import comb
import unittest

from analyze_tier_sizes import exact_excess_event_lower


def exact_overflow(homes, population, capacity, slots):
    """Count labeled allocations by occupied balls and saturated excess."""
    threshold = slots+1
    counts = {(0, 0): 1}
    for _ in range(homes):
        after = defaultdict(int)
        for (used, excess), ways in counts.items():
            for k in range(population-used+1):
                e = min(threshold, excess+max(k-capacity, 0))
                after[used+k, e] += ways*comb(used+k, k)
        counts = after
    assert sum(ways for (used, _), ways in counts.items() if used == population) == homes**population
    return Fraction(counts.get((population, threshold), 0), homes**population)


class TierSizeTests(unittest.TestCase):
    def test_lower_bound_below_exact_finite_multinomial_probability(self):
        for m, n, c, s in ((12, 24, 4, 0), (12, 36, 6, 0), (48, 48, 4, 1)):
            lower = Fraction(exact_excess_event_lower(m, n, c, s)['probability_lower_exact'])
            exact = exact_overflow(m, n, c, s)
            self.assertGreater(lower, 0)
            self.assertLessEqual(lower, exact)

    def test_falling_factorial_lower_factors(self):
        for population in (20, 50, 100):
            for k in range(1, 12):
                exact = Fraction(1)
                for i in range(k):
                    exact *= 1-Fraction(i, population)
                self.assertGreaterEqual(exact, 1-Fraction(k*(k-1), 2*population))

    def test_top_one_bucket_obstruction(self):
        result = exact_excess_event_lower(1 << 22, 32*(1 << 22), 64, 64)
        lower = Fraction(result['probability_lower_exact'])
        self.assertGreater(lower, Fraction(1, 1 << 62))
        self.assertTrue(result['exceeds_2_minus_64'])
        self.assertEqual(result['witnessed_total_excess'], 65)

    def test_lower_formula_rejects_unsupported_domain(self):
        for args in ((0, 4, 2, 1), (4, 8, 2, 1), (3, 3, 4, 2), (4, 4, 4, 1)):
            with self.assertRaises(ValueError):
                exact_excess_event_lower(*args)


if __name__ == '__main__':
    unittest.main()
