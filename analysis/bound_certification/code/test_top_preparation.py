#!/usr/bin/env python3
"""Finite categorical laws, A-only conservation, native boundary checks."""
from collections import Counter
from fractions import Fraction
import itertools
import random
import unittest

from certify_tier_router import positive_excess_bound
from certify_top_preparation import evaluate_shape, native_checks, sorted_range_bound
from test_sorted_range import test_deferred_selection, test_finite_distribution


class TopPreparationTests(unittest.TestCase):
    def test_binary_raw_stage_is_uniform_with_independent_old_new_words(self):
        # Every uncapped destination combines old high and new low bits.
        # Check its full joint law, not just equal expected bucket loads.
        for bits in (1, 2):
            low = (1 << bits)-1
            destinations = Counter((old & ~low) | (new & low)
                                   for old in range(4) for new in range(4))
            self.assertEqual(destinations, Counter({v: 4 for v in range(4)}))
            raw_law = Counter()
            for old in itertools.product(range(4), repeat=3):
                for new in itertools.product(range(4), repeat=3):
                    counts = Counter((o & ~low) | (n & low) for o, n in zip(old, new))
                    raw_law[tuple(counts[v] for v in range(4))] += 1
            multinomial = Counter(tuple(homes.count(v) for v in range(4))
                                  for homes in itertools.product(range(4), repeat=3))
            self.assertEqual(raw_law, Counter({key: 64*n for key, n in multinomial.items()}))

    def test_old_new_independence_is_needed_for_raw_arrivals(self):
        # Individually uniform families need not have independent high/low
        # coordinates: swapping the old bits makes both stage bits equal.
        counts = Counter((old & 2) | ((old >> 1) & 1) for old in range(4))
        self.assertEqual(counts, Counter({0: 2, 3: 2}))

    def test_initial_fixed_scatter_categorical_excess_comparison(self):
        # One record at each source, C=2. Stage one is deterministically safe;
        # stage two is multinomial. Intermediate destinations are independent
        # but need not be identically distributed across records.
        for bits in (1, 2):
            low = (1 << bits)-1
            law = Counter()
            for tags in itertools.product(range(4), repeat=4):
                counts = Counter((source & ~low) | (tag & low)
                                 for source, tag in enumerate(tags))
                law[sum(max(n-2, 0) for n in counts.values())] += 1
            if bits == 1:
                self.assertEqual(law, Counter({0: 256}))
            for slots in range(5):
                exact = Fraction(sum(n*max(excess-slots, 0) for excess, n in law.items()), 256)
                upper = positive_excess_bound(4, slots, capacity=2, mean=Fraction(1), cutoff=32)
                self.assertGreaterEqual(Fraction(upper), exact)

    def test_a_only_routing_offers_and_each_drain_prefix(self):
        rng = random.Random(20260928)
        had_early = had_final = had_absorption = 0
        for _ in range(2000):
            buckets, capacity = 4, 2
            homes = {key: rng.randrange(buckets) for key in range(rng.randrange(1, 12))}
            shuffled = list(homes)
            rng.shuffle(shuffled)
            main = [[] for _ in range(buckets)]
            pool = []
            # Arbitrary distinct old main/tier partition; numerical source law
            # is tested separately. Some main records may already be deleted.
            for key in shuffled:
                source = rng.randrange(buckets)
                if len(main[source]) < capacity and rng.randrange(3):
                    main[source].append(key)
                else:
                    pool.append(key)
            old_sources = {key: b for b, keys in enumerate(main) for key in keys}
            final = []
            for bit in range(2):
                next_main = [[] for _ in range(buckets)]
                sheds = []
                for source, keys in enumerate(main):
                    for key in keys:
                        destination = (source & ~(1 << bit)) | (homes[key] & (1 << bit))
                        next_main[destination].append(key)
                for b in range(buckets):
                    rng.shuffle(next_main[b])
                    sheds += next_main[b][capacity:]
                    next_main[b] = next_main[b][:capacity]
                # Earlier deletions cannot increase the raw stage witness.
                low = (1 << (bit+1))-1
                raw = Counter((b & ~low) | (homes[key] & low) for key, b in old_sources.items())
                self.assertLessEqual(len(sheds), sum(max(n-capacity, 0) for n in raw.values()))
                main = next_main
                if bit == 0:
                    pool += sheds
                    had_early += bool(sheds)
                else:
                    final = sheds  # Native final stage is drain-only.
                    had_final += bool(sheds)
            rng.shuffle(pool)
            leftovers = []
            for key in pool:
                home = homes[key]
                if len(main[home]) < capacity:
                    main[home].append(key)
                    had_absorption += 1
                else:
                    leftovers.append(key)
            excess = sum(max(list(homes.values()).count(b)-capacity, 0) for b in range(buckets))
            self.assertEqual(len(leftovers)+len(final), excess)
            self.assertEqual(sorted(sum(main, [])+leftovers+final), sorted(homes))
            for key in leftovers+final:
                self.assertEqual(len(main[homes[key]]), capacity)
            for prefix in range(len(final)+1):
                self.assertLessEqual(len(leftovers)+prefix, excess)
        self.assertTrue(had_early and had_final and had_absorption)

    def test_general_sorted_formula_reproduces_existing_top_certificate(self):
        self.assertGreater(test_deferred_selection(), 0)
        self.assertGreater(test_finite_distribution(), 0)

    def test_unsupported_shapes_rejected(self):
        row = dict(kind='top_prepare', main_bits=10, block_bits=10, radix=1,
            out_buckets=1024, stash_buckets=1, tier_buckets=1, pool_buckets=10,
            dense_bits=0, groups=1, scatter_per_bucket=8, range_bits=7,
            index_bits=3, range_buckets=128, carry_bits=7)
        for override in ({'kind': 'top_finish'}, {'radix': 3}, {'pool_buckets': 11}):
            with self.subTest(override=override), self.assertRaises(ValueError):
                evaluate_shape(row | override)
        with self.assertRaises(ValueError):
            sorted_range_bound(4, 3, 64, 64, False)

    def test_wide_top_capacities_do_not_set_shadow_cutoff(self):
        for bits, buckets, tier in ((26, 4, 3), (27, 5, 5), (28, 8, 8)):
            pool = (bits-1)*buckets+tier
            range_bits = (8*pool-1).bit_length()
            row = dict(kind='top_prepare', main_bits=bits, block_bits=bits,
                radix=1, out_buckets=1 << bits, stash_buckets=buckets,
                tier_buckets=tier, pool_buckets=pool, dense_bits=0,
                groups=1, scatter_per_bucket=8, range_bits=range_bits,
                index_bits=bits-range_bits, range_buckets=1 << range_bits,
                carry_bits=bits-3)
            for initialization in (False, True):
                result = evaluate_shape(row, initialization)
                self.assertIsNotNone(result['sorted_ranges'])
                self.assertEqual(result['sorted_ranges']['early_population_cap'],
                    64*(buckets*row['index_bits']+tier*int(not initialization)))
                for part in ('stages', 'packing', 'sorted_ranges'):
                    self.assertLess(Fraction(result[part]['probability_upper_decimal']),
                                    Fraction(1, 1 << 64))

    def test_native_packing_boundaries_and_initial_scatter(self):
        rows, hashes = native_checks()
        self.assertEqual(len(rows), 41)
        self.assertTrue(hashes)
        packing = [r for r in rows if r['kind'] == 'packing']
        for capacity in (64, 128):
            for delta in (0, 1):
                row = next(r for r in packing if r['tier_slots'] == capacity and
                           not r['earlier_pool'] and r['witness_excess'] == capacity+delta)
                self.assertEqual(row['drain_succeeded'], delta == 0)
        for row in rows:
            if row['kind'] == 'final_stage':
                self.assertEqual(row['succeeded'], row['excess'] <= row['capacity'])


if __name__ == '__main__':
    unittest.main()
