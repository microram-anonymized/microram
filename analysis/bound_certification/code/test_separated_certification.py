"""Separated-job event coverage, native matching, and raw-excess witnesses."""
from collections import Counter
import copy
from fractions import Fraction as Q
from itertools import combinations, product
import json
import random
import tempfile
import unittest

from check_configuration import (DEFAULT, HALF_FANOUT_SELECTED, Certificates, compile_probe, probe,
    normalize, ordinary_obligations, evaluate, assemble, digit_exposures)
from certify_separated_sources import check_shape, expected_domain, storage_bounds, HERE
from test_completed_a_shadow import route
from certify_tier_router import positive_excess_bound


class SeparatedProofTests(unittest.TestCase):
    def test_shifted_old_home_reference_is_categorical_with_bounded_mass(self):
        # The expanded blank-B stage need not be uniform. Its complete keys
        # nevertheless have independent destinations with mass <= 1/M.
        for digit in range(2, 9):
            carry = 2
            old_homes, homes = (digit-1)*carry, digit*carry
            radix = digit
            while radix % 2 == 0:
                radix //= 2
            bits = (homes//radix).bit_length()-1
            for stage in range(1, bits+1):
                width = 1 << stage
                destinations = Counter((old+carry)//width*width+low
                    for old in range(old_homes) for low in range(width))
                self.assertEqual(sum(destinations.values()), old_homes*width)
                self.assertTrue(all(0 <= v < homes for v in destinations))
                self.assertLessEqual(max(destinations.values()), width)
                # Two distinct keys have the product categorical law.
                pairs = Counter((a, b) for a in destinations.elements()
                                for b in destinations.elements())
                self.assertEqual(pairs, Counter({(a,b): na*nb
                    for a,na in destinations.items() for b,nb in destinations.items()}))

    def test_large_output_positive_series_removes_subset_obstacle(self):
        # At 2^24 homes even two pages suffice; at 2^25 the planner's
        # three-page width is needed for a small stage bound.
        for homes, slots in ((1 << 24, 128), (1 << 25, 192)):
            self.assertLess(Q(positive_excess_bound(homes, slots)), Q(1, 1 << 80))

    def test_whole_binary_stage_sheds_bounded_by_uncapped_arrivals(self):
        rng = random.Random(20260930)
        checks = 0
        for digit in range(2,9):
            carry, capacity = 2, 1
            radix = digit
            while radix % 2 == 0:
                radix //= 2
            bits = (digit*carry//radix).bit_length()-1
            for _ in range(150):
                n = rng.randrange(2*(digit-1)+1)
                positions = rng.sample(range(2*(digit-1)),n)
                homes = [rng.randrange(digit*carry) for _ in positions]
                _, losses = route(positions,homes,carry,digit,capacity,True)
                for bit in range(bits):
                    width = 1 << (bit+1)
                    raw = Counter(((old+carry)//width)*width+home%width
                                  for old,home in zip(positions,homes))
                    self.assertLessEqual(len(losses[bit]), sum(max(v-capacity,0) for v in raw.values()))
                    checks += 1
                if radix > 1:
                    counts = Counter(homes)
                    self.assertLessEqual(len(losses[bits]),sum(max(v-capacity,0) for v in counts.values()))
        self.assertGreater(checks,1000)

    def test_insertion_and_publication_use_one_union_excess(self):
        # Include arbitrary selected A/B subsets and shared keys. Dedup happens
        # before capacity; offers can change survivors but cannot lower fill.
        keys = set(range(4))
        for homes in product(range(2),repeat=4):
            excess = sum(max(sum(h == v for h in homes)-1,0) for v in range(2))
            for aa in range(16):
                for bb in range(16):
                    a = {key for key in keys if aa >> key & 1}
                    b = {key for key in keys if bb >> key & 1}
                    insertion = 0
                    published = set()
                    for v in range(2):
                        selected = {key for key in a|b if homes[key] == v}
                        insertion += max(len(selected)-1,0)
                        all_home = {key for key in keys if homes[key] == v}
                        published.update(sorted(all_home)[1:])
                    self.assertLessEqual(insertion, excess)
                    self.assertEqual(len(published),excess)

    def test_digit_counts_match_explicit_lists(self):
        for period,fanout,seed in product((1,7,512),(2,4,8),(0,1,16)):
            for horizon in range(32):
                end = horizon//period+1
                expected = Counter((v-1)%fanout+1 for v in range(seed+1,seed+end+1))
                actual = {d:digit_exposures(horizon,period,fanout,d,seed) for d in range(1,fanout+1)}
                self.assertEqual(actual, {d:expected[d] for d in actual})
                self.assertEqual(sum(actual.values()),end)


class SeparatedNativeCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix='separated-certificate-test-')
        cls.exe,_ = compile_probe(cls.temp.name)
        cls.config = DEFAULT|{'separated_sources':True}
        cls.certs = Certificates()
        cls.rows = [r for r in probe(cls.config,cls.exe) if r['kind'] == 'ordinary' and r['level'] > 1 and r.get('separated_sources')]

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def test_complete_selected_event_coverage_and_small_subtotal(self):
        self.assertIn('separated_sources_certificates',self.certs.data,
                      self.certs.errors.get('separated_sources_certificates'))
        artifact = self.certs.data['separated_sources_certificates']
        self.assertEqual(len(self.rows),28)
        for row in self.rows:
            obligations = ordinary_obligations(self.config,row,self.certs)
            self.assertTrue(all(o['conditional_upper_exact'] is not None for o in obligations))
            shared = next(o for o in obligations if o['name']=='insertion_and_published_tier')
            self.assertEqual(shared['capacity_slots'],64*min(row['stash_buckets'],row['tier_buckets']))
            self.assertTrue(shared['shared_witness_charged_once'])
            reuse = next(o for o in obligations if o['name']=='B_producer_tier_reuse')
            self.assertEqual(reuse['conditional_upper_exact'],'0')
        result = evaluate(self.config,self.exe,self.certs,True)
        selected = [p for p in result['passes'] if p['name'].startswith('ordinary_L')
                    and int(p['name'].split('_L')[1].split('_')[0]) in range(2,6)]
        subtotal = assemble(selected, self.config['target_exact'])
        self.assertEqual(Q(subtotal['conditional_lifetime_upper_exact']),Q(artifact['lifetime_subtotal_exact']))
        self.assertLess(Q(artifact['lifetime_subtotal_exact']),Q(1,1 << 64))
        self.assertFalse(result['complete_configuration_certified'])
        # The library's routing prepares the top through the certified
        # one-page DFS, so the top has no gap either, and the deterministic
        # inventory audit discharges the inventory line: the conditional
        # bound is the selected subtotal. Premises keep it unconditional one.
        self.assertEqual(result['coverage_gaps'], [])
        self.assertEqual(result['conditional_lifetime_upper_exact'],
                         result['covered_obligations_subtotal_exact'])
        self.assertLess(Q(result['conditional_lifetime_upper_exact']), Q(1, 1 << 64))
        self.assertEqual(result['unconditional_capacity_upper_exact'], '1')

    def test_shape_and_missing_certificate_fail_closed(self):
        row = self.rows[0]
        missing = copy.deepcopy(self.certs)
        missing.data.pop('separated_sources_certificates',None)
        for changed in (row|{'index_bits':row['index_bits']+1},
                        row|{'older_tier_buckets':row['older_tier_buckets']+1},
                        row|{'stash_buckets':row['stash_buckets']+1}):
            self.assertIsNone(self.certs.separated_case(self.config,changed))
        self.assertIsNone(self.certs.separated_case(self.config|{'branching':4},row))
        obligations = ordinary_obligations(self.config,row,missing)
        self.assertEqual(sum(o['conditional_upper_exact'] is None for o in obligations),3)
        with self.assertRaises(ValueError): check_shape(row|{'pool_buckets':row['pool_buckets']-1})
        with self.assertRaises(ValueError): check_shape(row|{'index_bits':row['carry_bits']})

    def test_per_digit_counts_preserve_speculation(self):
        result = evaluate(self.config,self.exe,self.certs,True)
        for level in range(1,6):
            clocks = [c for name,c in result['clocks'].items() if name.startswith(f'ordinary_L{level}_d')]
            expected = (1 << 32)//(512*8**(level-1))+1
            self.assertEqual(sum(c['exposures'] for c in clocks),expected)
            self.assertEqual(result['clocks'][f'ordinary_L{level}_d1']['exposures'],(expected-1)//8+1)
        self.assertEqual(result['clocks']['initialization']['exposures'],1)

class HalfFanoutSeparatedTests(unittest.TestCase):
    """The default ladder's 27 sparse jobs: fanout four at levels two and three."""
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix='separated-half-test-')
        cls.exe,_ = compile_probe(cls.temp.name)
        cls.config = normalize(HALF_FANOUT_SELECTED)
        cls.certs = Certificates()
        cls.native = probe(cls.config,cls.exe)
        cls.rows = [r for r in cls.native if r['kind'] == 'ordinary' and r['level'] > 1 and r.get('separated_sources')]
        artifact = cls.certs.data['separated_sources_certificates']
        cls.section, = [s for s in artifact['additional_configurations'] if s['ladder'] == 'half_fanout']

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def test_every_sparse_digit_at_each_levels_fanout(self):
        self.assertEqual(len(self.rows),27)
        self.assertEqual({(r['level'],r['digit']) for r in self.rows}, expected_domain(self.native))
        self.assertEqual({r['digit'] for r in self.rows if r['level'] in (2,3)}, {2,3,4})
        self.assertEqual(self.section['configuration_gate']['level_fanouts'],[4,4,4,8,8,8])
        for row in self.rows:
            check_shape(row)
            obligations = ordinary_obligations(self.config,row,self.certs)
            self.assertTrue(all(o['conditional_upper_exact'] is not None for o in obligations))

    def test_subtotal_matches_checker_assembly(self):
        result = evaluate(self.config,self.exe,self.certs,True)
        selected = [p for p in result['passes'] if p['name'].startswith('ordinary_L')
                    and int(p['name'].split('_L')[1].split('_')[0]) in range(2,7)]
        subtotal = assemble(selected, self.config['target_exact'])
        self.assertEqual(Q(subtotal['conditional_lifetime_upper_exact']),Q(self.section['lifetime_subtotal_exact']))
        self.assertLess(Q(self.section['lifetime_subtotal_exact']),Q(1,1 << 64))

    def test_fanout_eight_levels_reuse_uniform_per_job_bounds(self):
        # Half-fanout levels four to six have exactly the shapes of uniform
        # levels three to five (same carry widths, stashes, tiers and plans);
        # their per-job bounds must agree, and only the level label differs.
        uniform = {tuple(sorted((k,v) for k,v in c['shape'].items() if k != 'level')): c
                   for c in self.certs.data['separated_sources_certificates']['cases']}
        matched = 0
        for case in self.section['cases']:
            if case['shape']['level'] < 4:
                continue
            key = tuple(sorted((k,v) for k,v in case['shape'].items() if k != 'level'))
            self.assertEqual(case['per_job_upper_exact'], uniform[key]['per_job_upper_exact'])
            self.assertEqual(case['shape']['level']-1, uniform[key]['shape']['level'])
            matched += 1
        self.assertEqual(matched,21)

    def test_gate_refuses_other_ladders(self):
        row = next(r for r in self.rows if r['level'] == 2)
        self.assertIsNotNone(self.certs.separated_case(self.config,row))
        for other in (DEFAULT, self.config|{'level_fanouts':[4,4,8,8,8,8]}, self.config|{'levels':6}):
            self.assertIsNone(self.certs.separated_case(other,row))


if __name__ == '__main__':
    unittest.main()
