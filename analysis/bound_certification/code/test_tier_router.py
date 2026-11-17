#!/usr/bin/env python3
"""Exact small joint-family laws, physical witnesses and production coverage."""
from collections import Counter
from fractions import Fraction
import itertools
import json
from pathlib import Path
import unittest

from certify_oram import certificate, upper_fraction
from certify_preparation import stage_bound
from certify_tier_router import series_cutoff, validate_carry, positive_excess_bound

HERE = Path(__file__).resolve().parent


def excess(homes, nodes, capacity):
    return sum(max(homes.count(i)-capacity, 0) for i in range(nodes))


def excess_law(nodes, count, capacity):
    return Counter(excess(h, nodes, capacity)
                   for h in itertools.product(range(nodes), repeat=count))


class TierRouterTests(unittest.TestCase):
    def test_independent_families_with_shared_keys(self):
        # All four keys occur in both populations. Retain the first two
        # arrivals at each home; selection may depend on the whole word.
        keys = range(4)
        law = excess_law(2, 4, 2)
        joint = Counter()
        shared_tier_copies = 0
        for old in itertools.product(range(2), repeat=4):
            a_tier = {k for i in range(2) for k in
                      [k for k in keys if old[k] == i][2:]}
            for new in itertools.product(range(2), repeat=4):
                b_tier = {k for i in range(2) for k in
                          [k for k in keys if new[k] == i][2:]}
                ta, tb = excess(old, 2, 2), excess(new, 2, 2)
                self.assertEqual((len(a_tier), len(b_tier)), (ta, tb))
                joint[ta, tb] += 1
                shared_tier_copies += len(a_tier & b_tier)
                # New marks of shared physical copies agree. Charge both;
                # a dedup here would need the native prologue, not this proof.
                for pattern in range(2):
                    physical = sum(new[k] == pattern for k in a_tier)
                    physical += sum(new[k] == pattern for k in b_tier)
                    self.assertLessEqual(physical, ta+tb)
        self.assertGreater(shared_tier_copies, 0)
        self.assertEqual(joint, Counter({(a, b): na*nb
                         for a, na in law.items() for b, nb in law.items()}))

    def test_same_family_cannot_multiply_count_laws(self):
        law = excess_law(2, 4, 2)
        same = Fraction(sum(n for t, n in law.items() if 2*t > 3), 2**4)
        independent = Fraction(sum(na*nb for a, na in law.items()
                                   for b, nb in law.items() if a+b > 3), 2**8)
        self.assertEqual(same, Fraction(1, 8))
        self.assertEqual(independent, Fraction(1, 64))
        self.assertGreater(same, independent)

    def test_selected_incoming_marks_are_not_fresh(self):
        # Two keys, two homes, capacity one: a tier key exists precisely
        # when both homes agree. Given key 0's word, the selected key's
        # word is then determined. Joint tier counts need no contrary law.
        selected = []
        for h in itertools.product(range(2), repeat=2):
            if h[0] == 0 and excess(h, 2, 1):
                selected.append(h[1])
        self.assertEqual(selected, [0])

    def test_one_shared_capacity_and_physical_copies(self):
        # Each marginal fits capacity two, but their physical sum does not.
        a, b = {0, 1}, {0, 1}
        self.assertEqual(len(a | b), 2)
        self.assertGreater(len(a)+len(b), 2)
        self.assertTrue(len(a) <= 2 and len(b) <= 2)

    def test_subset_bound_for_two_multinomials(self):
        for ma, na, mb, nb, capacity in ((2, 4, 3, 6, 2), (3, 3, 2, 2, 1)):
            a, b = excess_law(ma, na, capacity), excess_law(mb, nb, capacity)
            for slots in range(na+nb+1):
                exact = Fraction(sum(x*y for i, x in a.items() for j, y in b.items()
                                     if i+j > slots), ma**na * mb**nb)
                bound, finite, tail = stage_bound(ma+mb, slots, capacity=capacity,
                    mean=max(Fraction(na, ma), Fraction(nb, mb)))
                self.assertGreaterEqual(Fraction(bound), exact)
                self.assertGreaterEqual(Fraction(bound), Fraction(finite)+Fraction(tail))

    def test_positive_series_bounds_exact_joint_stoploss(self):
        # Compare expectations (stronger than tail probabilities), including
        # different means and a full overlap in key identities across families.
        for ma, na, mb, nb, capacity in ((2, 4, 3, 6, 2), (3, 3, 2, 2, 1),
                                        (2, 3, 3, 3, 2)):
            a, b = excess_law(ma, na, capacity), excess_law(mb, nb, capacity)
            for slots in range(na+nb+1):
                exact = Fraction(sum(max(i+j-slots, 0)*x*y
                    for i, x in a.items() for j, y in b.items()), ma**na * mb**nb)
                bound = positive_excess_bound(ma+mb, slots, capacity=capacity,
                    mean=max(Fraction(na, ma), Fraction(nb, mb)))
                self.assertGreaterEqual(Fraction(bound), exact)

    def test_stoploss_has_increasing_differences(self):
        def f(vector, slots):
            return max(sum(max(x-2, 0) for x in vector)-slots, 0)
        increments = list(itertools.product(range(2), repeat=2))
        for x in itertools.product(range(5), repeat=2):
            for a, b in itertools.product(increments, repeat=2):
                xa = tuple(v+w for v, w in zip(x, a))
                xb = tuple(v+w for v, w in zip(x, b))
                xab = tuple(v+w for v, w in zip(xa, b))
                for slots in range(4):
                    self.assertGreaterEqual(f(xab, slots)+f(x, slots),
                                            f(xa, slots)+f(xb, slots))

    def test_series_majorizes_exact_polynomial_stoploss(self):
        # An independent exact-rational polynomial check of the reused
        # positive-series recurrence; do not assume its output is a PMF.
        weights = [Fraction(0)]*17
        weights[1], weights[3] = Fraction(1, 3), Fraction(1, 7)
        polynomial = [Fraction(1)]
        for _ in range(4):
            following = [Fraction(0)]*(len(polynomial)+3)
            for i, mass in enumerate(polynomial):
                following[i] += mass
                following[i+1] += mass*weights[1]
                following[i+3] += mass*weights[3]
            polynomial = following
        at_two = sum(w*2**i for i, w in enumerate(weights))
        for slots in (0, 2, 5, 11):
            exact = sum(max(i-slots, 0)*p for i, p in enumerate(polynomial))
            upper = certificate([upper_fraction(w) for w in weights],
                                upper_fraction(at_two), 4, slots)
            self.assertGreaterEqual(Fraction(upper), exact)

    def test_largest_count_bound_and_invalid_parameters(self):
        self.assertLess(Fraction(positive_excess_bound(524288, 64)), Fraction(1, 1 << 78))
        for kwargs in ({'nodes': 0}, {'slots': 256, 'cutoff': 256}, {'capacity': 0},
                       {'mean': Fraction(65)}):
            values = dict(nodes=16, slots=64)
            values.update(kwargs)
            with self.assertRaises(ValueError):
                positive_excess_bound(**values)

    def test_series_cutoff_rule(self):
        # The automatic cutoff is the fixed 256 wherever that already leaves
        # an omitted tail of at most 2^-128, so those values are unchanged.
        for nodes, slots in ((1 << 18, 64), (1 << 22, 128), (1 << 24, 128), (16, 64)):
            self.assertEqual(series_cutoff(nodes, slots), 256)
            self.assertEqual(positive_excess_bound(nodes, slots),
                             positive_excess_bound(nodes, slots, cutoff=256))
        # It grows where 256 does not suffice, and a capacity at or above 256
        # slots gets a cutoff above it; a larger cutoff never loosens the bound.
        self.assertEqual(series_cutoff(1 << 25, 192), 512)
        self.assertGreater(series_cutoff(16, 256), 256)
        self.assertLessEqual(positive_excess_bound(1 << 25, 192),
                             positive_excess_bound(1 << 25, 192, cutoff=256))
        self.assertLess(Fraction(positive_excess_bound(1 << 25, 192)), Fraction(1, 1 << 115))

    def test_old_map_bias_transfers_through_joint_counts(self):
        # A biased three-home map paired with an independent uniform B map.
        masses = (Fraction(1, 2), Fraction(1, 4), Fraction(1, 4))
        weighted, uniform = Counter(), Counter()
        for a in itertools.product(range(3), repeat=3):
            probability = masses[a[0]]*masses[a[1]]*masses[a[2]]
            for b in itertools.product(range(2), repeat=2):
                value = excess(a, 3, 1)+excess(b, 2, 1)
                weighted[value] += probability/4
                uniform[value] += Fraction(1, 3**3 * 4)
        density = (3*max(masses))**3
        self.assertEqual(sum(weighted.values()), 1)
        for value, mass in weighted.items():
            self.assertLessEqual(mass, density*uniform[value])

    def test_incoming_carry_must_be_the_full_binary_table(self):
        ordinary = json.loads((HERE/'ordinary_range_audit.json').read_text())
        shapes = {(r['level'], r['digit']): r for r in ordinary['passes']}
        validate_carry(shapes[2, 2], shapes)
        broken = dict(shapes)
        broken[1, 8] = dict(shapes[1, 8], radix=3)
        with self.assertRaisesRegex(ValueError, 'full binary carry'):
            validate_carry(shapes[2, 2], broken)

if __name__ == '__main__':
    unittest.main()
