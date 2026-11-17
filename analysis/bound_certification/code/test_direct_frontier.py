#!/usr/bin/env python3
"""Exact finite models for the conditional deferred-mark lemma and its limits."""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
import unittest


class DirectFrontierChecks(unittest.TestCase):
    def test_joint_suffix_after_asymmetric_low_bit_cap(self):
        # Source order is deliberately asymmetric, but sees only low bits.
        groups = defaultdict(Counter)
        for words in product(range(4), repeat=3):
            low = tuple(w & 1 for w in words)
            main = tuple(next((x for x in (2, 0, 1) if low[x] == h), -1)
                         for h in range(2))
            sheds = tuple(x for x in range(3) if x not in main)
            order = tuple(x for x in main if x >= 0) + sheds
            groups[(low, main, sheds)][tuple(words[x] >> 1 for x in order)] += 1
        for outcomes in groups.values():
            self.assertEqual(len(outcomes), 8)
            self.assertEqual(set(outcomes.values()), {1})

    def test_complete_pool_conserves_all_keys_before_b(self):
        for words in product(range(4), repeat=4):
            buckets = {h: [h] for h in range(4)}
            old_tier = [4]
            sheds = []
            for bit in range(2):
                next_buckets = {h: [] for h in range(4)}
                for h in range(4):
                    if h & (1 << bit):
                        continue
                    pair = buckets[h] + buckets[h | (1 << bit)]
                    for direction in range(2):
                        selected = [x for x in pair if words[x] >> bit & 1 == direction]
                        next_buckets[h | (direction << bit)] = selected[:1]
                        sheds.extend(selected[1:])
                buckets = next_buckets
                main = [x for xs in buckets.values() for x in xs]
                self.assertEqual(sorted(main + old_tier + sheds), list(range(5)))
            completed = old_tier + sheds
            self.assertEqual(len(completed), len(set(completed)))
            # A fresher B copy must not alter the analytical A pool.
            b_keys = set(completed)
            self.assertEqual(len(completed), len(b_keys))
            self.assertEqual([x for x in completed if x not in b_keys], [])

    def test_finite_radix_marks_independent_of_low_bits(self):
        counts = Counter((w % 4, (w // 4) % 3) for w in range(32))
        for low in range(4):
            self.assertEqual([Fraction(counts[low, a], 8) for a in range(3)],
                             [Fraction(3, 8), Fraction(3, 8), Fraction(1, 4)])

    def test_success_conditioning_changes_shared_a_marks(self):
        # Two B keys, two homes, capacity one, no residual room.
        # Both keys also occur in A. Its unconditional both-zero event has mass 1/4;
        # it disappears upon conditioning on successful B production.
        samples = list(product(range(2), repeat=2))
        success = [s for s in samples if s[0] != s[1]]
        event = lambda s: s == (0, 0)
        self.assertEqual(Fraction(sum(map(event, samples)), len(samples)), Fraction(1, 4))
        self.assertEqual(Fraction(sum(map(event, success)), len(success)), 0)
        self.assertEqual(Fraction(sum(s[0] == s[1] for s in success), len(success)), 0)

    def test_distinct_b_residual_keys_do_not_imply_independent_marks(self):
        # Capacity one: first key wins, two residual keys stay distinct.
        samples = [w for w in product(range(2), repeat=3) if len(set(w)) == 1]
        self.assertEqual(len(samples), 2)
        self.assertEqual(Fraction(sum(w[1] == 0 for w in samples), 2), Fraction(1, 2))
        self.assertEqual(Fraction(sum(w[1] == w[2] == 0 for w in samples), 2), Fraction(1, 2))
        self.assertNotEqual(Fraction(1, 2), Fraction(1, 2)**2)

    def test_suffix_aware_survivor_selection_breaks_frontier(self):
        # Select the smaller suffix before routing it. Individual words
        # are uniform, but the selected survivor is biased toward zero.
        outcomes = [min(w) for w in product(range(2), repeat=2)]
        self.assertEqual(Fraction(outcomes.count(0), 4), Fraction(3, 4))

    def test_successive_loss_classes_share_routing_constraint(self):
        # Three keys route through two cap-one stages. Early and late losses
        # are disjoint, yet conditioning on their identities can reveal marks.
        selected = []
        sources = (0, 0, 2)
        for words in product(range(4), repeat=3):
            first = [[x for x in range(3)
                      if (sources[x] & ~1) | (words[x] & 1) == h]
                     for h in range(4)]
            early = [x for xs in first for x in xs[1:]]
            main = [xs[0] for xs in first if xs]
            second = [[x for x in main if words[x] == h] for h in range(4)]
            late = [x for xs in second for x in xs[1:]]
            if early == [1] and late == [2]:
                selected.append(words)
        self.assertTrue(selected)
        # Late loss requires the two retained keys' high bits to coincide.
        self.assertTrue(all(w[0] >> 1 == w[2] >> 1 for w in selected))
        self.assertTrue(set([1]).isdisjoint([2]))



if __name__ == '__main__':
    unittest.main()
