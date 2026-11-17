"""Finite checks for REPORT.tex's completed-A comparison.

These check topology and the terminal joint-state law, not Poissonization,
finite-precision certificates, or native C++ memory/scheduler correctness.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
from math import comb
import random
import unittest


def terminal_law(states, probability, capacity):
    """Exact joint-state thinning, addition, then the one terminal cap."""
    law = {(0, 0): Q(1)}
    for main, shadow in states:
        next_law = defaultdict(Q)
        for (u, v), mass in law.items():
            for m in range(main + 1):
                for s in range(shadow + 1):
                    weight = (comb(main, m) * comb(shadow, s)
                              * probability ** (m + s)
                              * (1 - probability) ** (main + shadow - m - s))
                    next_law[u + m, v + s] += mass * weight
        law = next_law
    result = defaultdict(Q)
    for (u, v), mass in law.items():
        result[min(u, capacity), v + max(u - capacity, 0)] += mass
    return dict(result)


def route(positions, homes, carry, digit, capacity, scheduled):
    """Compare the native public block schedule with the expanded network."""
    radix, power = digit, 0
    while radix % 2 == 0:
        radix //= 2
        power += 1
    k = carry.bit_length() - 1
    b = k + power
    block = 1 << b
    buckets = [[] for _ in range(digit * carry)]
    losses = [set() for _ in range(b + (radix > 1))]
    for key, old in enumerate(positions):
        buckets[carry + old].append(key)

    def stage(start, width, bit):
        half = 1 << bit
        for base in range(start, start + width, 2 * half):
            for offset in range(half):
                lo, hi = base + offset, base + offset + half
                keys = buckets[lo] + buckets[hi]
                for side, dest in enumerate((lo, hi)):
                    selected = [x for x in keys if (homes[x] >> bit) & 1 == side]
                    buckets[dest] = selected[:capacity]
                    losses[bit].update(selected[capacity:])

    if scheduled:
        spans = [(j * block, block) for j in range(1, radix)]
        spans += [(1 << (k + u), 1 << (k + u)) for u in reversed(range(power))]
        for start, width in spans:
            for bit in range(width.bit_length() - 1):
                stage(start, width, bit)
        for bit in range(k, b):
            before = len(losses[bit])
            stage(0, 1 << (bit + 1), bit)
            if bit == k:
                # First continuation pairs empty buckets with <= C records.
                assert len(losses[bit]) == before
    else:
        for bit in range(b):
            stage(0, digit * carry, bit)
    if radix > 1:
        for low in range(block):
            keys = sum((buckets[j * block + low] for j in range(radix)), [])
            for j in range(radix):
                selected = [x for x in keys if homes[x] // block == j]
                buckets[j * block + low] = selected[:capacity]
                losses[b].update(selected[capacity:])
    return buckets, losses


class CompletedAShadowTests(unittest.TestCase):
    def test_terminal_joint_law_against_labelled_records(self):
        for states in (((1, 1),), ((1, 1), (2, 0)), ((1, 0),) * 3):
            labels = [kind for m, s in states for kind in [0] * m + [1] * s]
            for p in (Q(1, 3), Q(2, 5), Q(1)):
                expected = defaultdict(Q)
                for marks in product((0, 1), repeat=len(labels)):
                    m = sum(hit for kind, hit in zip(labels, marks) if kind == 0)
                    s = sum(hit for kind, hit in zip(labels, marks) if kind == 1)
                    hits = sum(marks)
                    expected[min(m, 1), s + max(m - 1, 0)] += p**hits * (1-p)**(len(labels)-hits)
                actual = terminal_law(states, p, 1)
                self.assertEqual({k: v for k, v in actual.items() if v},
                                 {k: v for k, v in expected.items() if v})
                self.assertEqual(sum(actual.values()), 1)

    def test_terminal_main_loss_cannot_be_omitted(self):
        law = terminal_law(((1, 0),) * 3, Q(1, 3), 1)
        self.assertEqual(sum(p for (_, r), p in law.items() if r), Q(7, 27))
        # All input shadow marginals are zero, but the terminal loss is not.

    def test_exact_finite_word_radix_is_biased(self):
        words, radix = 8, 3
        masses = [Q(sum(h % radix == a for h in range(words)), words)
                  for a in range(radix)]
        self.assertEqual(masses, [Q(3, 8), Q(3, 8), Q(1, 4)])
        self.assertGreater(masses[0], Q(1, radix))

    def check_route(self, positions, homes, digit):
        actual = route(positions, homes, 2, digit, 1, True)
        self.assertEqual(actual, route(positions, homes, 2, digit, 1, False))
        buckets, losses = actual
        survivors = [x for bucket in buckets for x in bucket]
        residuals = [x for loss in losses for x in loss]
        self.assertEqual(sorted(survivors + residuals), list(range(len(homes))))
        for bucket, keys in enumerate(buckets):
            self.assertTrue(all(homes[x] == bucket for x in keys))

    def test_block_schedule_equals_completed_blank_network(self):
        for digit in (2, 3, 4):
            count = min(3, 2 * (digit - 1))
            for positions in combinations(range(2 * (digit - 1)), count):
                for homes in product(range(2 * digit), repeat=count):
                    self.check_route(positions, homes, digit)
        rng = random.Random(20260929)
        for digit in (5, 6, 7, 8):
            for _ in range(100):
                positions = rng.sample(range(2 * (digit - 1)), 6)
                homes = [rng.randrange(2 * digit) for _ in positions]
                self.check_route(positions, homes, digit)


if __name__ == '__main__':
    unittest.main()
