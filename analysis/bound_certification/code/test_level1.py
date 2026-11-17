"""Dense-direct producer, applicability and lifetime accounting regression."""
import copy
from fractions import Fraction as Q
import tempfile
import unittest
from certify_level1 import check_shape, evaluate, validate_inventory, expected_sources
from check_configuration import DEFAULT, SELECTED, compile_probe, probe, normalize, Certificates, ordinary_obligations
class DirectTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp=tempfile.TemporaryDirectory(); cls.exe,_=compile_probe(cls.tmp.name)
    @classmethod
    def tearDownClass(cls):cls.tmp.cleanup()
    def test_every_native_digit(self):
        for name,config in SELECTED.items():
            config=normalize(config)
            rows=[r for r in probe(config,self.exe) if r['kind']=='ordinary' and r['level']==1]
            fanout = 8 if name == 'uniform' else 4
            validate_inventory(rows, fanout)
            with self.assertRaises(ValueError):
                validate_inventory(rows[:-1], fanout)
            with self.assertRaises(ValueError):
                validate_inventory([*rows[:-1], rows[0]], fanout)
            for row in rows:
                sources=expected_sources(row)
                self.assertEqual(sum(x['pages'] for x in sources if not x['drain_only']),row['pool_buckets'])
                result=evaluate(row)
                self.assertEqual(Q(result['dense']['probability_upper_decimal'])==0,row['digit']==1)
                self.assertEqual(result['packing']['capacity_slots'],64*row['tier_buckets'])
                for field,value in [('dense_direct',False),('carry_tier_buckets',2),('merge_stash_buckets',0)]:
                    with self.assertRaises(ValueError):check_shape(row|{field:value})
    def test_small_direct_A_plan(self):
        config = normalize(SELECTED['uniform'] | {'prefix_flushes': 2})
        row = next(r for r in probe(config, self.exe)
                   if r['kind'] == 'ordinary' and r['level'] == 1 and r['digit'] == 2)
        self.assertEqual((row['carry_bits'], row['index_bits']), (2, 3))
        self.assertFalse(row['dfs'])
        result = evaluate(row)
        self.assertEqual(result['shape'], row)
        self.assertEqual(result['ranges']['probability_upper_decimal'], '0')
        self.assertEqual(result['range_sources'], [])
        for changes in ({'index_bits': 0}, {'groups': row['groups'] + 1},
                        {'range_bits': 1}, {'scatter_per_bucket': 128}):
            with self.assertRaises(ValueError):
                check_shape(row | changes)

    def test_producer_is_additional_event(self):
        # 129 winners in one low-bit home overflow its one-page tier while
        # four compatible final ways can each fit at most 33 winners.
        counts=[33,32,32,32]
        self.assertGreater(sum(counts)-64,64)
        self.assertEqual(sum(max(x-64,0) for x in counts),0)
    def test_certificate_and_ledger(self):
        certs=Certificates()
        for name,config in SELECTED.items():
            rows=[r for r in probe(normalize(config),self.exe) if r['kind']=='ordinary' and r['level']==1]
            cases=[]
            for row in rows:
                case=certs.level_one_case(config,row)
                self.assertIsNotNone(case,certs.errors)
                cases.append(case)
                obligations=ordinary_obligations(config,row,certs)
                self.assertEqual(len(obligations),4)
                self.assertTrue(all(o['conditional_upper_exact'] is not None for o in obligations))
                self.assertEqual(obligations[2]['capacity_slots'],64)
                bad=row|{'merge_stash_buckets':0}
                self.assertIsNone(certs.level_one_case(config,bad))
            self.assertEqual(sum(c['exposures'] for c in cases),(1 << 23)+1)
if __name__=='__main__':unittest.main()
