"""Native separated selection, numerical coverage and source-contract guards."""
import tempfile
import unittest
from check_configuration import (DEFAULT, HALF_FANOUT_SELECTED, Certificates, compile_probe, evaluate,
                                 normalize, ordinary_obligations, probe)

class SeparatedSourcesTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix='separated-checker-')
        cls.exe, _ = compile_probe(cls.temp.name)
    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()
    def test_schema(self):
        self.assertTrue(normalize({'separated_sources': True})['separated_sources'])
        with self.assertRaises(ValueError): normalize({'separated_sources': 1})
    def test_native_selection_and_fail_closed_ledger(self):
        config = DEFAULT | {'separated_sources': True}
        rows = probe(config, self.exe)
        selected = [r for r in rows if r['kind'] == 'ordinary' and r['level'] > 1 and r.get('separated_sources')]
        self.assertEqual(len(selected), 28)
        for row in selected:
            self.assertEqual(row['groups'], 1)
            self.assertEqual(row['direct_buckets'], row['carry_tier_buckets'])
            obligations = ordinary_obligations(config, row, Certificates())
            leaf = next(o for o in obligations if o['name'] == 'A_only_range_router')
            self.assertIsNotNone(leaf['conditional_upper_exact'])
            self.assertTrue(leaf['includes_final_A_route_sheds'])
            self.assertEqual(sum(o['name'] == 'B_producer_tier_reuse' for o in obligations), 1)
        for row in rows:
            if row['kind'] == 'top_prepare':
                self.assertFalse(row.get('separated_sources', False))
            if row['kind'] == 'ordinary' and row['level'] == 1:
                self.assertEqual(row['separated_sources'], row['digit'] > 1)
        # The top merge is a separated finish too: the retained carry
        # through a one-page DFS leaf, B's carry tier offered directly.
        top, = [r for r in rows if r['kind'] == 'top_finish']
        self.assertTrue(top['separated_sources'] and top['dfs'])
        self.assertEqual((top['direct_buckets'], top['groups']), (top['carry_tier_buckets'], 1))
        result = evaluate(config, self.exe, Certificates())
        self.assertFalse(result['complete_configuration_certified'])
        # No coverage gap is left (the deterministic inventory audit
        # discharges the inventory line); the premises keep it uncertified.
        self.assertEqual(result['coverage_gaps'], [])
        self.assertEqual(result['unconditional_capacity_upper_exact'], '1')
    def test_rejects_wrong_source_contract(self):
        config = DEFAULT | {'separated_sources': True}
        row = next(r for r in probe(config, self.exe)
                   if r['kind'] == 'ordinary' and r['level'] > 1 and r.get('separated_sources'))
        for changes in ({'dense_bits': 1}, {'groups': 2}, {'direct_buckets': 0}):
            with self.assertRaises(ValueError): ordinary_obligations(config, row | changes, Certificates())
    def test_half_fanout_selection(self):
        # The default ladder selects separated sources at every sparse digit
        # above one of levels two to six, fanout four at levels two and three.
        rows = probe(normalize(HALF_FANOUT_SELECTED), self.exe)
        selected = [r for r in rows if r['kind'] == 'ordinary' and r['level'] > 1 and r.get('separated_sources')]
        self.assertEqual(len(selected), 27)
        self.assertEqual(sorted({(r['level'], r['digit']) for r in selected if r['level'] < 4}),
                         [(l, d) for l in (2, 3) for d in (2, 3, 4)])
        for row in rows:
            if row['kind'] == 'ordinary' and row['level'] == 1:
                self.assertEqual(row['separated_sources'], row['digit'] > 1)

if __name__ == '__main__': unittest.main()
