"""The separated binary top finish: native shape, A-only DFS ranges and the shared witness."""
from fractions import Fraction as Q
import tempfile
import unittest

from certify_tier_router import positive_excess_bound
from check_configuration import DEFAULT, HALF_FANOUT_SELECTED, Certificates, compile_probe, normalize, probe, top_obligations
from evaluate_top_finish import evaluate


class TopFinishProofTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix='top-finish-test-')
        cls.exe, _ = compile_probe(cls.temp.name)
        cls.row = next(r for r in probe(DEFAULT, cls.exe) if r['kind'] == 'top_finish')
        cls.certs = Certificates()

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def test_native_row_is_a_separated_dfs_finish(self):
        # A = the retained carry (two stash pages) through a one-page DFS
        # leaf per coarse range of the finish plan; B = the carry tier, direct.
        row = self.row
        self.assertTrue(row['separated_sources'] and row['dfs'])
        self.assertEqual((row['pool_buckets'], row['stash_buckets'], row['direct_buckets'],
                          row['carry_tier_buckets'], row['older_tier_buckets']), (4, 2, 2, 2, 0))
        self.assertEqual((row['range_bits'], row['index_bits'], row['range_buckets'],
                          row['groups'], row['scatter_per_bucket']), (4, 18, 16, 1, 64))

    def test_ranges_are_the_leaf_marginal_only(self):
        case = evaluate(self.row, 257)
        per_range = Q(positive_excess_bound(1 << 18, 64))
        self.assertEqual(Q(case['ranges']['per_range_upper']), per_range)
        self.assertGreaterEqual(Q(case['ranges']['probability_upper_decimal']), 16*per_range)
        self.assertEqual(case['ranges']['coarse_ranges'], 16)
        self.assertEqual(case['direct_B_pages']['probability_upper_decimal'], '0')
        self.assertEqual(case['packing']['capacity_slots'], 128)
        self.assertEqual(Q(case['packing']['probability_upper_decimal']),
                         Q(positive_excess_bound(1 << 22, 128)))
        self.assertLess(Q(case['ranges']['probability_upper_decimal']), Q(1, 1 << 78))
        self.assertTrue(case['meets_2_minus_64'])

    def test_one_page_retained_carry_is_deterministic(self):
        row = self.row | dict(stash_buckets=1, pool_buckets=3, range_bits=3, index_bits=19,
                              range_buckets=8)
        case = evaluate(row, 1)
        self.assertEqual(case['ranges']['probability_upper_decimal'], '0')
        self.assertEqual(case['packing']['capacity_slots'], 64)
        direct = self.row | dict(dfs=False, range_bits=0, index_bits=22, groups=2, range_buckets=2)
        self.assertEqual(evaluate(direct, 1)['ranges']['name'], 'direct_A_pool')

    def test_rejects_other_contracts(self):
        for changes in ({'separated_sources': False}, {'direct_buckets': 0},
                        {'pool_buckets': 5}, {'radix': 3}, {'index_bits': 17},
                        {'groups': 2},
                        {'older_tier_buckets': 2}, {'kind': 'top_prepare'}):
            with self.assertRaises(ValueError, msg=changes):
                evaluate(self.row | changes, 1)
        # A deeper top (four-bucket stashes, 256 slots) is inside the contract:
        # the positive series picks its own cutoff, so it evaluates.
        deeper = evaluate(self.row | {'stash_buckets': 4, 'tier_buckets': 4,
                                      'pool_buckets': 6}, 1)
        self.assertTrue(deeper['meets_2_minus_64'])

    def test_native_obligations_are_the_separated_finishs(self):
        self.assertIn('top_finish_evaluation', self.certs.data, self.certs.errors.get('top_finish_evaluation'))
        case = self.certs.data['top_finish_evaluation']['case']
        self.assertTrue(case['meets_2_minus_64'])
        self.assertLess(Q(case['lifetime']['probability_upper_decimal']), Q(1, 1 << 70))
        obligations = top_obligations(DEFAULT, self.row, self.certs)
        self.assertEqual([o['name'] for o in obligations],
                         ['A_only_range_router', 'B_producer_tier_reuse', 'insertion_and_published_tier'])
        self.assertTrue(all(o['conditional_upper_exact'] is not None for o in obligations))
        self.assertTrue(obligations[0]['dfs_containment'])
        self.assertEqual(obligations[1]['conditional_upper_exact'], '0')
        self.assertTrue(obligations[2]['shared_witness_charged_once'])
        wrong = top_obligations(DEFAULT, self.row | {'tier_buckets': 1}, self.certs)
        self.assertIsNone(wrong[0]['conditional_upper_exact'])
        self.assertIsNone(wrong[2]['conditional_upper_exact'])

    def test_half_fanout_top_is_the_uniform_top(self):
        # At the same capacity the default ladder ends in the same top (same
        # carry width, stash and tier), one level higher: the same per-finish
        # bound and exposure count, admitted only by its own gated section.
        data = self.certs.data['top_finish_evaluation']
        half, = [s for s in data['additional_configurations'] if s['ladder'] == 'half_fanout']
        self.assertEqual(half['case']['shape'] | {'level': 6}, data['case']['shape'])
        for part in ('ranges', 'packing', 'lifetime'):
            self.assertEqual(half['case'][part]['probability_upper_decimal'],
                             data['case'][part]['probability_upper_decimal'])
        config = normalize(HALF_FANOUT_SELECTED)
        row = next(r for r in probe(config, self.exe) if r['kind'] == 'top_finish')
        self.assertTrue(all(o['conditional_upper_exact'] is not None
                            for o in top_obligations(config, row, self.certs)))
        self.assertTrue(any(o['conditional_upper_exact'] is None
                            for o in top_obligations(DEFAULT, row, self.certs)))


if __name__ == '__main__':
    unittest.main()
