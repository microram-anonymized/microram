"""Checks for analysis/residual_occupancy_certificate.py (balls-in-bins excess bounds
with outward-rounded arithmetic): exact finite oracles for each inequality it certifies."""

from collections import Counter
from decimal import Decimal
from fractions import Fraction
import importlib.util
from itertools import product
from math import comb
from pathlib import Path
import sys
import unittest


ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location(
    "occupancy_certificate", ROOT / "analysis/residual_occupancy_certificate.py")
cert = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = cert
spec.loader.exec_module(cert)


class OccupancyCertificateTest(unittest.TestCase):
    def test_interval_operations_enclose_exact_rationals(self):
        a, b = cert.interval(1) / 3, cert.interval(7) / 11
        for value, exact in (
                (a + b, Fraction(1, 3) + Fraction(7, 11)),
                (a - b, Fraction(1, 3) - Fraction(7, 11)),
                (a * b, Fraction(7, 33)),
                (a / b, Fraction(11, 21)),
                (a ** 137, Fraction(1, 3) ** 137)):
            self.assertLessEqual(Fraction(value.low), exact)
            self.assertGreaterEqual(Fraction(value.high), exact)

    def test_binomial_points_and_tails(self):
        for n in range(12):
            for bins in range(1, 6):
                for threshold in range(n + 2):
                    point = (Fraction(comb(n, threshold) *
                                      (bins - 1) ** (n - threshold), bins**n)
                             if threshold <= n else Fraction(0))
                    enclosed = cert.binomial_point(n, bins, threshold)
                    self.assertLessEqual(Fraction(enclosed.low), point)
                    self.assertGreaterEqual(Fraction(enclosed.high), point)
                    tail = sum(Fraction(comb(n, k) * (bins - 1) ** (n-k), bins**n)
                               for k in range(threshold, n + 1))
                    bound = cert.binomial_tail_upper(n, bins, threshold)
                    self.assertGreaterEqual(Fraction(bound), tail)

    def test_bounds_against_enumeration_not_independent_bins(self):
        for records, buckets, cap in ((5, 2, 2), (7, 3, 2), (8, 4, 2),
                                      (6, 2, 3), (6, 1, 2)):
            counts = Counter()
            for destinations in product(range(buckets), repeat=records):
                loads = Counter(destinations)
                excess = sum(max(load - cap, 0) for load in loads.values())
                counts[excess] += 1
            for slots in range(4):
                exact = Fraction(sum(count for excess, count in counts.items()
                                     if excess > slots), buckets**records)
                lower = cert.excess_lower(records, buckets, slots, cap)
                upper = cert.excess_upper(records, buckets, slots, cap,
                                          z=cert.interval(3) / 2)
                self.assertLessEqual(Fraction(lower), exact)
                self.assertGreaterEqual(Fraction(upper), exact)

    def test_weighted_tail_is_not_truncated(self):
        records, buckets, cap, slots = 300, 20, 2, 60
        z = Fraction(3, 2)
        mgf = sum(Fraction(comb(records, k) * (buckets - 1)**(records-k),
                           buckets**records) * z**max(k-cap, 0)
                  for k in range(records + 1))
        exact_chernoff = min(Fraction(1), mgf / z**(slots+1))
        upper = cert.excess_upper(records, buckets, slots, cap, outputs=1,
                                  z=cert.interval(3) / 2)
        self.assertGreaterEqual(Fraction(upper), exact_chernoff)

    def test_binary_stage_union_against_exhaustive_tags(self):
        # Four one-record input buckets, capacity one. At each level route
        # through the actual capped network and count that level's sheds.
        # The checked event is any stage spilling more than the stash holds.
        for slots in (0, 1, 2):
            failures = 0
            for tags in product(range(4), repeat=4):
                state = [[tag] for tag in tags]
                failed = False
                for bit in range(2):
                    shed = 0
                    for low in range(4):
                        high = low | (1 << bit)
                        if low == high:
                            continue
                        records = state[low] + state[high]
                        left = [tag for tag in records if not (tag & (1 << bit))]
                        right = [tag for tag in records if tag & (1 << bit)]
                        shed += max(len(left)-1, 0) + max(len(right)-1, 0)
                        state[low], state[high] = left[:1], right[:1]
                    failed |= shed > slots
                failures += failed
            exact = Fraction(failures, 4**4)
            upper = cert.binary_initialization_stash_upper(4, slots, load=1, cap=1)
            self.assertGreaterEqual(Fraction(upper), exact)
        self.assertEqual(cert.binary_initialization_stash_upper(8, 0, load=0), 0)

    def test_one_tier_bucket_counterexample(self):
        buckets = 1 << 22
        records = 32 * buckets
        lower = cert.excess_lower(records, buckets, 64)
        corrected = cert.DOWN.subtract(lower, cert.permutation_distance(records))
        self.assertGreater(corrected, (cert.interval(1) / (1 << 64)).high)
        self.assertGreater(corrected, Decimal("2.43e-19"))
        self.assertLess(corrected, Decimal("2.44e-19"))
        # A larger tier removes this particular occupancy obstruction; this
        # does not certify the intermediate range route or the whole engine.
        two_bucket = cert.excess_upper(records, buckets, 128)
        self.assertLess(two_bucket, (cert.interval(1) / (1 << 120)).low)


if __name__ == "__main__":
    unittest.main()
