#!/usr/bin/env python3
"""Finite complete-union witnesses and outward-rounded tail checks."""
from collections import Counter
from fractions import Fraction
import itertools
import json
from pathlib import Path
import random
import unittest

from audit_preparation_contract import home_mass_bound
from certify_preparation import stage_bound

HERE = Path(__file__).resolve().parent


class PooledFinishTests(unittest.TestCase):
    def test_full_union_offer_and_drain_witness(self):
        # Main retention may depend on ALL marks. Shared keys carry a common
        # home, while A/B physical copies remain until each actual dedup.
        rng = random.Random(20260928)
        duplicate_leftovers = replacements = 0
        for _ in range(6000):
            a = set(range(rng.randrange(1, 13)))
            b = set(rng.sample(sorted(a), rng.randrange(min(len(a), 6)+1)))
            b.update(range(20, 20+rng.randrange(7)))
            raw = a | b
            homes = {key: rng.randrange(4) for key in raw}
            a_main = {key for key in a if rng.randrange(2)}
            b_main = {key for key in b if rng.randrange(2)}
            # Prologue swept-pool dedup: B copy wins before scatter, while
            # remaining copies meeting in final main dedup at that kernel.
            fresh = b-b_main
            stale = (a-a_main)-fresh
            main_inputs = a_main | b_main
            main, fused = set(), set()
            for home in range(4):
                arriving = sorted(key for key in main_inputs if homes[key] == home)
                rng.shuffle(arriving)
                main.update(arriving[:2])
                fused.update(arriving[2:])
            excess = sum(max(sum(homes[key] == h for key in raw)-2, 0) for h in range(4))
            self.assertLessEqual(len(fused), excess)
            leftovers = set()
            for home in range(4):
                m = {key for key in main if homes[key] == home}
                old = sorted(key for key in stale-main if homes[key] == home)
                new = sorted(key for key in fresh if homes[key] == home)
                rng.shuffle(old)
                rng.shuffle(new)
                before = len(m)
                take_old = old[:2-before]
                clear = m & set(new)
                replacements += bool(clear)
                m -= clear
                m.update(take_old)
                take_new = new[:2-len(m)]
                m.update(take_new)
                leftovers.update(set(old)-set(take_old))
                leftovers.update(set(new)-set(take_new))
                main = {key for key in main if homes[key] != home} | m
                self.assertGreaterEqual(len(m), before)
            # The epilogue's drain-only pool dedup reads the original fresh
            # stash, including candidates already absorbed into main. It
            # must clear these shed copies BEFORE checking disjointness.
            fused -= fresh
            self.assertFalse(main & (leftovers | fused))
            self.assertEqual(main | leftovers | fused, raw)
            for key in leftovers | fused:
                self.assertEqual(sum(homes[k] == homes[key] for k in main), 2)
            # First tier drain is before leftover dedup, yet already fits E.
            self.assertLessEqual(len(leftovers), excess)
            duplicate_leftovers += bool(leftovers & fused)
            # Production's class resolution can clear either physical side;
            # neither side is charged an independent full tier capacity.
            drained = leftovers-((leftovers & fused)-fresh)
            pending = fused-(leftovers & fresh)
            self.assertFalse(drained & pending)
            self.assertEqual(len(drained)+len(pending), excess)
            for count in range(len(pending)+1):
                self.assertLessEqual(len(drained)+count, excess)
        self.assertGreater(duplicate_leftovers, 0)
        self.assertGreater(replacements, 0)

    def test_cannot_deduplicate_before_the_test(self):
        # Physical copies can exceed a range capacity while their logical
        # union fits. This theorem deliberately begins at later native dedup.
        swept, fused = {0, 1}, {0, 1}
        self.assertGreater(len(swept)+len(fused), 2)
        self.assertEqual(len(swept | fused), 2)

    def test_subset_envelope_against_exact_multinomial(self):
        for nodes, count, capacity in ((2, 4, 2), (3, 4, 2), (3, 6, 3)):
            tails = Counter()
            for homes in itertools.product(range(nodes), repeat=count):
                excess = sum(max(homes.count(h)-capacity, 0) for h in range(nodes))
                tails[excess] += 1
            for slots in range(count+1):
                exact = Fraction(sum(n for e, n in tails.items() if e > slots), nodes**count)
                bound, finite, tail = stage_bound(nodes, slots, capacity=capacity,
                                                 mean=Fraction(count, nodes))
                self.assertGreaterEqual(Fraction(bound), exact)
                self.assertGreaterEqual(Fraction(bound), Fraction(finite)+Fraction(tail))

    def test_current_map_density(self):
        audit = json.loads((HERE/'ordinary_range_audit.json').read_text())
        biased = 0
        for row in audit['passes']:
            bits = row['block_bits'] if row['radix'] > 1 else row['main_bits']
            law = home_mass_bound(bits, row['radix'], 32*row['out_buckets'])
            density = Fraction(law['joint_density_upper_bound'])
            self.assertGreaterEqual(density, 1)
            self.assertLess(density, Fraction(1000001, 1000000))
            biased += not law['exactly_uniform']
        self.assertEqual(len(audit['passes']), 36)
        self.assertEqual(biased, 20)


if __name__ == '__main__':
    unittest.main()
