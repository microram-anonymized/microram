"""Mutation checks for untrusted numerical registry proposals."""
import copy
from fractions import Fraction
import importlib.util
import json
from pathlib import Path
import unittest

import configuration_family_numerics as numerics


def load_range_generator():
    path = Path(__file__).resolve().parents[3] / 'lean/RebuildBound/Proofs/NumericsFamilyRange/gen.py'
    spec = importlib.util.spec_from_file_location('family_range_test_generator', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class NumericalRegistryTests(unittest.TestCase):
    def test_rounding_is_upward(self):
        for value in [Fraction(1, 2**70), Fraction(3, 2**72), Fraction(9, 2**74),
                      Fraction(7, 10**50)]:
            exponent = numerics.dyadic_exponent(value)
            self.assertLessEqual(value, Fraction(1, 2**exponent))
            self.assertLess(Fraction(1, 2**(exponent+1)), value)

    def test_nonpositive_budget_rejected(self):
        for value in [0, -1]:
            with self.assertRaises(ValueError):
                numerics.dyadic_exponent(value)

    @staticmethod
    def fixture():
        key = dict(role='top_finish', carry_bits=3, block_bits=6, range_bits=3,
                   index_bits=3, dfs=True, stash_buckets=1, carry_tier_buckets=1,
                   merge_stash_buckets=1, tier_buckets=1)
        manifest = dict(jobs={'id': dict(key=key, per_job_upper_exact='1/1024')})
        table = dict(entries=[dict(key_id='id', key=copy.deepcopy(key),
                                   case=dict(per_job_upper_exact='1/1024'))])
        return manifest, table

    def test_full_key_mismatch_rejected(self):
        manifest, table = self.fixture()
        table['entries'][0]['key']['carry_tier_buckets'] = 2
        with self.assertRaisesRegex(ValueError, 'complete job key'):
            numerics.registries(manifest, table)

    def test_stale_budget_rejected(self):
        manifest, table = self.fixture()
        table['entries'][0]['case']['per_job_upper_exact'] = '1/2048'
        with self.assertRaisesRegex(ValueError, 'bound mismatch'):
            numerics.registries(manifest, table)

    def test_duplicate_geometry_rejected(self):
        manifest, table = self.fixture()
        manifest['jobs']['other'] = copy.deepcopy(manifest['jobs']['id'])
        duplicate = copy.deepcopy(table['entries'][0]);duplicate['key_id'] = 'other'
        table['entries'].append(duplicate)
        with self.assertRaisesRegex(ValueError, 'Duplicate complete semantic shape'):
            numerics.registries(manifest, table)

    def test_unrecognized_statement_format_rejected(self):
        with self.assertRaisesRegex(ValueError, 'exactly one'):
            numerics.replace_rows('def altered := []', 'topBudgets', [])


class RangeRegistryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.generator = load_range_generator()
        manifest = json.loads((Path(__file__).resolve().parent / 'configuration_family.json').read_text())
        cls.manifest = dict(jobs={key: value for key, value in manifest['jobs'].items()
                                 if value['key']['role'] == 'separated_ordinary'})

    def test_full_shapes_have_distinct_final_certificate_names(self):
        rows = self.generator.rows_of(self.manifest)
        self.assertEqual(len(rows), 133)
        self.assertEqual(len({row['tag'] for row in rows}), len(rows))
        transition = [row for row in rows if (row['level'], row['digit']) == (12, 2)]
        self.assertEqual(len(transition), 2)
        self.assertNotEqual(transition[0]['geom'], transition[1]['geom'])
        self.assertNotEqual(transition[0]['tag'], transition[1]['tag'])

    def test_duplicate_complete_shape_is_rejected(self):
        manifest = copy.deepcopy(self.manifest)
        first_key, first = next(iter(manifest['jobs'].items()))
        manifest['jobs'][first_key + '_mutant'] = copy.deepcopy(first)
        with self.assertRaises((AssertionError, ValueError)):
            self.generator.rows_of(manifest)

    def test_reuse_checks_exact_reduced_mass_depth_and_radix(self):
        lower = dict(t=6, r=7, nb=61, qc=2**61 // 7)
        same = dict(t=6, r=7, nb=60, qc=2**60 // 7)
        self.assertEqual(self.generator.chain_key(lower), self.generator.chain_key(same))
        upper = dict(lower, qc=lower['qc'] + 1)
        other_upper = dict(same, qc=same['qc'] + 1)
        self.assertNotEqual(self.generator.chain_key(upper), self.generator.chain_key(other_upper))
        self.assertNotEqual(self.generator.chain_key(lower), self.generator.chain_key(dict(lower, r=3)))
        self.assertNotEqual(self.generator.chain_key(lower), self.generator.chain_key(dict(lower, t=7)))


if __name__ == '__main__':
    unittest.main()
