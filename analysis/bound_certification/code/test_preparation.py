#!/usr/bin/env python3
"""Independent finite checks for the uncapped-arrival subset-witness proof."""
from collections import defaultdict
from fractions import Fraction
import itertools
import math
import unittest

from certify_preparation import stage_bound


class PreparationChecks(unittest.TestCase):
    def test_main_only_deletion_needs_no_exchangeable_retention(self):
        # Exact original-home law, followed by positive first-stage tests.
        # The asymmetric deletion deliberately violates retained symmetry.
        for asymmetric in (False, True):
            for subset in range(1, 16):
                for z in (Fraction(3, 2), Fraction(2), Fraction(3)):
                    g = [1 + Fraction(sum((subset >> j) & 1 for j in
                         (i & ~1, (i & ~1) | 1)), 2) * (z - 1) for i in range(4)]
                    retained = original = Fraction(0)
                    for homes in itertools.product(range(4), repeat=4):
                        x = [homes.count(i) for i in range(4)]
                        a = [min(n, 2) if not asymmetric or i else 0
                             for i, n in enumerate(x)]
                        left = math.prod(w**n for w, n in zip(g, a))
                        right = math.prod(w**n for w, n in zip(g, x))
                        self.assertLessEqual(left, right)
                        retained += left / 256
                        original += right / 256
                    self.assertEqual(original, (sum(g) / 4)**4)
                    self.assertLessEqual(retained, original)

    def test_capped_route_is_bounded_by_original_uncapped_arrivals(self):
        # Four physical source buckets, capacity two, up to half load. Route
        # actual records and remove sheds permanently after each bit stage.
        # Compute the comparison from ORIGINAL source/tag pairs independently.
        checked = 0
        for counts in itertools.product(range(3), repeat=4):
            if sum(counts) > 4:
                continue
            sources = [i for i, count in enumerate(counts) for _ in range(count)]
            for tags in itertools.product(range(4), repeat=len(sources)):
                original = list(zip(sources, tags))
                buckets = [[record for record in original if record[0] == i]
                           for i in range(4)]
                cumulative = 0
                for bit in range(2):
                    next_buckets = [[] for _ in range(4)]
                    actual_shed = 0
                    for low in range(4):
                        if low & (1 << bit):
                            continue
                        high = low | (1 << bit)
                        pair = buckets[low] + buckets[high]
                        for target, direction in ((low, 0), (high, 1)):
                            arriving = [r for r in pair if (r[1] >> bit) & 1 == direction]
                            next_buckets[target] = arriving[:2]
                            actual_shed += max(len(arriving) - 2, 0)
                    routed_bits = (1 << (bit + 1)) - 1
                    ideal = [0] * 4
                    for source, tag in original:
                        ideal[(source & ~routed_bits) | (tag & routed_bits)] += 1
                    excess = sum(max(z - 2, 0) for z in ideal)
                    self.assertLessEqual(actual_shed, excess)
                    cumulative += actual_shed
                    self.assertEqual(sum(map(len, next_buckets)) + cumulative, len(original))
                    buckets = next_buckets
                    checked += 1
        self.assertGreater(checked, 1000)

    def test_overflow_has_a_nonempty_subset_witness(self):
        for loads in itertools.product(range(6), repeat=4):
            loss = sum(max(z - 2, 0) for z in loads)
            for slots in range(6):
                if loss <= slots:
                    continue
                witnesses = [subset for bits in range(1, 16)
                             if (subset := [i for i in range(4) if bits >> i & 1])
                             and sum(loads[i] for i in subset) >= 2 * len(subset) + slots + 1]
                self.assertTrue(witnesses)

    def test_retained_first_stage_without_bucket_independence(self):
        retained = defaultdict(Fraction)
        for homes in itertools.product(range(4), repeat=4):
            counts = tuple(homes.count(i) for i in range(4))
            retained[tuple(min(n, 2) for n in counts)] += Fraction(1, 4**4)
        arrivals = defaultdict(Fraction)
        for counts, weight in retained.items():
            sources = [i for i, count in enumerate(counts) for _ in range(count)]
            for bits in itertools.product((0, 1), repeat=len(sources)):
                loads = [0] * 4
                for source, bit in zip(sources, bits):
                    loads[(source & ~1) | bit] += 1
                arrivals[tuple(loads)] += weight / 2**len(sources)
        self.assertEqual(sum(arrivals.values()), 1)
        # Verify each subset's Chernoff step against the exact joint law.
        # The finite-total MGF envelope is rational and stronger than the
        # exponential/Poisson envelope used by the production-size certificate.
        for subset_bits in range(1, 16):
            subset = [i for i in range(4) if subset_bits >> i & 1]
            for z in (Fraction(3, 2), Fraction(2), Fraction(3)):
                exact_mgf = sum(p * z**sum(loads[i] for i in subset)
                                for loads, p in arrivals.items())
                envelope = (1 + Fraction(len(subset), 4) * (z - 1))**4
                self.assertLessEqual(exact_mgf, envelope)
                for slots in range(4):
                    threshold = 2 * len(subset) + slots + 1
                    tail = sum(p for loads, p in arrivals.items()
                               if sum(loads[i] for i in subset) >= threshold)
                    self.assertLessEqual(tail, envelope / z**threshold)
        for slots in range(4):
            actual = sum(p for loads, p in arrivals.items()
                         if sum(max(z - 2, 0) for z in loads) > slots)
            # Exercise both the explicit sum and the independently bounded
            # omitted-subset tail, including cutoff below the number of nodes.
            for cutoff in (1, 2, 4):
                bound, _, tail = stage_bound(4, slots, cutoff, 2, Fraction(1))
                self.assertLessEqual(actual, Fraction(bound))
                self.assertEqual(tail == 0, cutoff >= 4)


if __name__ == '__main__':
    unittest.main()
