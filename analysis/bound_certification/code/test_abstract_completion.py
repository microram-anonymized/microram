#!/usr/bin/env python3
"""Finite checks of the new top laws and public ordinal exposure formulas.

These enumerate ideal words, not native engine histories, and do not certify
the production top range distributors or the numerical deployment target.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
import unittest

from certify_preparation import stage_bound
from certify_tier_router import positive_excess_bound


def top_home(word, carry, digit):
    if digit & (digit - 1) == 0:
        return word % (carry * digit)
    return word % carry + carry * ((word // carry) % digit)


class AbstractCompletionTests(unittest.TestCase):
    def test_exact_top_laws_and_independent_old_new_stage_envelopes(self):
        words, carry = 64, 4
        for digit in range(1, 9):
            homes = carry * digit
            law = Counter(top_home(word, carry, digit) for word in range(words))
            binary = digit & (digit - 1) == 0
            maximum = (words // homes if binary else
                       (words // carry + digit - 1) // digit)
            self.assertEqual(max(law.values()), maximum)
            self.assertEqual(set(law), set(range(homes)))
            if not binary:
                quotient, remainder = divmod(words // carry, digit)
                for home in range(homes):
                    self.assertEqual(law[home], quotient + (home // carry < remainder))
            block = homes if binary else carry
            for bits in range(1, block.bit_length()):
                width = 1 << bits
                raw = Counter(
                    (top_home(old, carry, digit) // width) * width + new % width
                    for old, new in product(range(words), repeat=2))
                self.assertEqual(sum(raw.values()), words * words)
                self.assertLessEqual(max(raw.values()), maximum * words)

    def test_exact_biased_excess_tails_are_below_both_bounds(self):
        # Deliberately short words make modulo bias substantial. Include
        # whole-digit six, and populations smaller than the public capacity.
        words, carry, public_keys, capacity = 16, 2, 4, 2
        for digit in (2, 3, 6):
            homes = carry * digit
            law = Counter(top_home(word, carry, digit) for word in range(words))
            p_max = Fraction(max(law.values()), words)
            density = (homes * p_max) ** public_keys
            exact = []
            for count in range(public_keys + 1):
                excess_law = Counter()
                for assignment in product(range(homes), repeat=count):
                    occupancy = Counter(assignment)
                    excess = sum(max(n - capacity, 0) for n in occupancy.values())
                    mass = 1
                    for home in assignment:
                        mass *= law[home]
                    excess_law[excess] += mass
                self.assertEqual(sum(excess_law.values()), words ** count)
                exact.append((excess_law, words ** count))
            for slots in range(3):
                subset = Fraction(stage_bound(
                    homes, slots, capacity=capacity, mean=public_keys * p_max)[0])
                series = density * Fraction(positive_excess_bound(
                    homes, slots, capacity=capacity,
                    mean=Fraction(public_keys, homes), cutoff=32))
                for excess_law, denominator in exact:
                    tail = Fraction(sum(mass for excess, mass in excess_law.items()
                                        if excess > slots), denominator)
                    self.assertLessEqual(tail, min(Fraction(1), subset, series))

    def test_fixed_scatter_raw_means_for_all_top_maps(self):
        words, carry, per_home = 64, 4, 1
        for digit in range(1, 9):
            homes = carry * digit
            block = homes if digit & (digit - 1) == 0 else carry
            for bits in range(1, block.bit_length()):
                width = 1 << bits
                raw = Counter((source // width) * width + word % width
                              for source in range(homes)
                              for _ in range(per_home)
                              for word in range(words))
                self.assertTrue(all(count <= per_home * words
                                    for count in raw.values()))

    def test_digit_counts_include_exact_boundary_speculation(self):
        for fanout, period in product((2, 4, 8), (1, 2, 7, 32)):
            for seed in (0, 1, fanout, 3 * fanout):
                for horizon in range(65):
                    potential = horizon // period + 1
                    explicit = Counter(1 + ((v - 1) % fanout)
                                       for v in range(seed + 1, seed + potential + 1))
                    total = 0
                    for digit in range(1, fanout + 1):
                        count = ((seed + potential - digit) // fanout
                                 - (seed - digit) // fanout)
                        self.assertEqual(count, explicit[digit])
                        total += count
                    self.assertEqual(total, potential)
                    if horizon % period == 0:
                        self.assertGreater(potential, (horizon + period - 1) // period)


if __name__ == '__main__':
    unittest.main()
