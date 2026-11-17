#!/usr/bin/env python3
"""The shape-keyed bound table: exact reproduction of the selected ledgers,
key completeness, fail-closed composition and the configuration-space
artifact's internal consistency.  Reads retained artifacts only; no probe."""
import copy
from fractions import Fraction as Q
import json
from pathlib import Path
import unittest

import bound_table as bt
from certify_tier_router import positive_excess_bound
import check_configuration as cc

HERE = Path(__file__).resolve().parent
CHECKS = {'uniform': 'selected_configuration_check.json',
          'half_fanout': 'selected_configuration_half_fanout_check.json'}
SPACE = HERE/'configuration_space_2p27.json'


def load(name):
    return json.loads((HERE/name).read_text())


def stored(name):
    data = load(name)
    return data['configurations'][0] if 'configurations' in data else data


def strip_evidence(passes):
    result = copy.deepcopy(passes)
    for p in result:
        for o in p['obligations']:
            o.pop('evidence', None)
    return result


class Recording(dict):
    """A row that records which fields a bound function reads."""
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.read = set()

    def __getitem__(self, key):
        self.read.add(key)
        return super().__getitem__(key)

    def get(self, key, default=None):
        self.read.add(key)
        return super().get(key, default)


TABLE = bt.BoundTable()


@unittest.skipIf(TABLE.errors or not TABLE.entries, f'bound_table.json missing or stale: {TABLE.errors[:2]}')
class ReproductionTests(unittest.TestCase):
    """Any difference between a table-composed ledger and the retained
    checker output is a bug in the table."""

    def test_selected_ledgers_are_reproduced_exactly(self):
        for name, file in CHECKS.items():
            with self.subTest(configuration=name):
                check = stored(file)
                certs = bt.TableCertificates(TABLE)
                passes = cc.native_passes(check['configuration'], check['native_inventory'], certs)
                retained = [p for p in check['passes'] if p['name'] != 'integrated_inventory']
                self.assertEqual(strip_evidence(passes), strip_evidence(retained))
                inventory = [p for p in check['passes'] if p['name'] == 'integrated_inventory']
                result = cc.assemble(passes + inventory, check['configuration']['target_exact'],
                                     check['undischarged_premises'])
                for field in ('conditional_lifetime_upper_exact',
                              'covered_obligations_subtotal_exact', 'clocks', 'coverage_gaps'):
                    self.assertEqual(result[field], check[field], field)
                for p in passes:
                    for o in p['obligations']:
                        if o['evidence'] and o['conditional_upper_exact'] not in (None, '0') \
                                and 'producer' not in o['evidence']:
                            self.assertTrue(o['evidence'].startswith(bt.TABLE.name), o['evidence'])

    def test_component_certificate_cases_are_reproduced(self):
        separated = load('separated_sources_certificates.json')
        for section in [separated, *separated['additional_configurations']]:
            for case in section['cases']:
                entry = TABLE.lookup(bt.shape_key(case['shape']))
                self.assertIsNotNone(entry)
                for part in ('stages', 'ranges', 'packing'):
                    self.assertEqual(entry[part], case[part])
                self.assertEqual(entry['per_job_upper_exact'], case['per_job_upper_exact'])
        level1 = load('level1_certificates.json')
        for section in [level1, *level1['additional_configurations']]:
            for case in section['cases']:
                entry = TABLE.lookup(bt.shape_key(case['shape']))
                for part in ('dense', 'stages', 'ranges', 'packing', 'range_sources'):
                    self.assertEqual(entry[part], case[part])
                self.assertEqual(entry['per_job_upper_exact'], case['per_job_upper_exact'])
        finish = load('top_finish_evaluation.json')
        for section in [finish, *finish['additional_configurations']]:
            entry = TABLE.lookup(bt.shape_key(section['case']['shape']))
            for part in ('ranges', 'direct_B_pages', 'packing'):
                self.assertEqual(entry[part], section['case'][part])

    def test_shared_shapes_are_one_entry(self):
        # The default ladder's levels 4-6 and top repeat the uniform levels
        # 3-5 and top: one key each, one computation.
        uniform, half = (stored(f)['native_inventory'] for f in CHECKS.values())
        keys = lambda rows: {bt.key_id(bt.shape_key(r)) for r in rows if r['kind'] == 'ordinary'}
        shared = keys(uniform) & keys(half)
        self.assertGreaterEqual(len(shared), 3*7 + 4)


class KeyTests(unittest.TestCase):
    def rows(self):
        return [r for f in CHECKS.values() for r in stored(f)['native_inventory']
                if r['kind'] in ('ordinary', 'top_prepare', 'top_finish')]

    def test_key_is_the_whole_row_less_the_level(self):
        for row in self.rows():
            key = bt.shape_key(row)
            self.assertEqual(set(key), set(row) - set(bt.NON_KEY_FIELDS) | {'role'})
            self.assertEqual(bt.representative_row(key, row['level']), row)
        self.assertEqual(bt.NON_KEY_FIELDS, ('level',))

    def test_roles(self):
        rows = self.rows()
        self.assertEqual({bt.role_of(r) for r in rows if r['kind'] == 'ordinary' and r['level'] == 1},
                         {'dense_level_one'})
        self.assertEqual({bt.role_of(r) for r in rows if r['kind'] == 'ordinary' and r['level'] > 1},
                         {'separated_ordinary'})
        top = next(r for r in rows if r['kind'] == 'top_prepare')
        self.assertNotEqual(bt.key_id(bt.shape_key(top)), bt.key_id(bt.shape_key(top, True)))
        with self.assertRaises(ValueError):
            bt.role_of(dict(kind='adoption', level=2, digit=1))

    def test_bounds_read_only_key_fields_and_not_the_level(self):
        """Every field the per-job functions read is in the key; the level is
        read only by the role/domain test, and moving a separated job to
        another level leaves its storage bounds unchanged."""
        import certify_separated_sources as css
        import certify_top_preparation as ctp
        import evaluate_top_finish as etf
        rows = self.rows()
        sep = next(r for r in rows if bt.role_of(r) == 'separated_ordinary' and r['radix'] > 1)
        rec = Recording(sep)
        bounds = css.storage_bounds(rec)
        self.assertLessEqual(rec.read, set(sep))
        css.old_law(rec)
        for level in (2, 9, 30):
            self.assertEqual(css.storage_bounds(dict(sep, level=level)), bounds)
        with self.assertRaises(ValueError):
            css.storage_bounds(dict(sep, level=1))
        top = next(r for r in rows if r['kind'] == 'top_prepare')
        from audit_ordinary_ranges import PLAN_KEYS, expected_plan
        partition = Recording(top | dict(zip(PLAN_KEYS, expected_plan(top['pool_buckets'], top['main_bits']))))
        ctp.validate_binary(partition)
        self.assertNotIn('level', partition.read)
        finish = next(r for r in rows if r['kind'] == 'top_finish')
        rec = Recording(finish)
        etf.evaluate(rec, 1)
        self.assertLessEqual(rec.read - {'level'}, set(finish) - {'level'})

    def test_level_one_shape_check_reads_key_fields(self):
        import certify_level1 as cl1
        row = next(r for r in self.rows() if bt.role_of(r) == 'dense_level_one' and r['digit'] == 3)
        rec = Recording(row)
        cl1.check_shape(rec)
        cl1.expected_sources(rec)
        self.assertLessEqual(rec.read, set(row))


class FailClosedTests(unittest.TestCase):
    def test_untabled_shape_is_a_gap_charged_one(self):
        check = stored(CHECKS['uniform'])
        table = bt.BoundTable.__new__(bt.BoundTable)
        table.path, table.errors, table.source_sha256 = bt.TABLE, [], {}
        table.entries = dict(TABLE.entries)
        victim = next(r for r in check['native_inventory']
                      if r['kind'] == 'ordinary' and r['level'] == 3 and r['digit'] == 5)
        table.entries.pop(bt.key_id(bt.shape_key(victim)), None)
        passes = cc.native_passes(check['configuration'], check['native_inventory'],
                                  bt.TableCertificates(table))
        gap = next(p for p in passes if p['name'] == 'ordinary_L3_d5')
        self.assertTrue(any(o['conditional_upper_exact'] is None for o in gap['obligations']))
        result = cc.assemble(passes, check['configuration']['target_exact'])
        self.assertEqual(result['conditional_lifetime_upper_exact'], '1')
        self.assertIn('ordinary_L3_d5/completed_A_route_stashes', result['coverage_gaps'])

    def test_empty_or_stale_table_covers_nothing(self):
        check = stored(CHECKS['half_fanout'])
        table = bt.BoundTable(HERE/'no_such_table.json')
        passes = cc.native_passes(check['configuration'], check['native_inventory'],
                                  bt.TableCertificates(table))
        result = cc.assemble(passes, check['configuration']['target_exact'])
        self.assertEqual(result['conditional_lifetime_upper_exact'], '1')
        self.assertGreater(len(result['coverage_gaps']), 50)

    def test_changed_key_field_misses(self):
        if not TABLE.entries:
            self.skipTest('no table')
        row = next(r for r in stored(CHECKS['uniform'])['native_inventory']
                   if r['kind'] == 'ordinary' and r['level'] == 4)
        self.assertIsNotNone(TABLE.lookup(bt.shape_key(row)))
        for field, value in (('stash_buckets', row['stash_buckets']+1),
                             ('tier_buckets', row['tier_buckets']+1),
                             ('index_bits', row['index_bits']+1)):
            self.assertIsNone(TABLE.lookup(bt.shape_key(dict(row, **{field: value}))))

    def test_level_one_needs_its_native_inventory(self):
        import certify_configuration_space as space
        check = stored(CHECKS['uniform'])
        certs = space.CandidateCertificates(TABLE, level_one_ok=False)
        passes = cc.native_passes(check['configuration'], check['native_inventory'], certs)
        self.assertTrue(all(o['conditional_upper_exact'] is None
                            for p in passes if p['name'].startswith('ordinary_L1_')
                            for o in p['obligations']))


@unittest.skipUnless(SPACE.exists() and not TABLE.errors and TABLE.entries,
                     'configuration_space_2p27.json not generated')
class GeneralizedAdapterTests(unittest.TestCase):
    """Generalized direct level-one shapes and separated top finish at every D."""

    @classmethod
    def setUpClass(cls):
        data = json.loads(SPACE.read_text())
        cls.rows = [r for c in data['candidates'] for r in c['native_inventory']]

    def test_direct_level_one_shapes(self):
        import certify_level1 as cl1
        rows = [r for r in self.rows if r['kind'] == 'ordinary' and r['level'] == 1]
        self.assertEqual({r['carry_bits'] for r in rows}, {2, 3, 4})
        for row in rows:
            with self.subTest(shape=row):
                cl1.check_shape(row)
                case = TABLE.lookup(bt.shape_key(row))
                self.assertIsNotNone(case)
                if row['digit'] == 1:
                    self.assertFalse(row['dfs'])
                    self.assertEqual(case['dense']['probability_upper_decimal'], '0')
                    self.assertEqual(case['range_sources'], [])
                else:
                    self.assertEqual(row['direct_buckets'], 1)
                    self.assertEqual(case['dense']['capacity_slots'], 64)
                if row['dfs']:
                    self.assertEqual(row['scatter_per_bucket'], 64)
                    self.assertEqual(row['range_buckets'], 1 << row['range_bits'])
                else:
                    self.assertEqual(case['ranges']['probability_upper_decimal'], '0')
                    self.assertEqual(case['range_sources'], [])
                for field, value in (('dense_direct', False), ('carry_tier_buckets', 2)):
                    with self.subTest(field=field), self.assertRaises(ValueError):
                        cl1.check_shape(row | {field: value})

    def test_top_finish_every_top_digit(self):
        finishes = {r['digit']: r for r in self.rows if r['kind'] == 'top_finish'}
        self.assertEqual(set(finishes), {1, 2, 4, 8})
        for digit, row in finishes.items():
            case = TABLE.lookup(bt.shape_key(row))
            self.assertLessEqual(Q(case['per_job_upper_exact']), 1)
            # The separated form at every D: the A-only leaf marginal alone
            # (it does not depend on D), no event for B's direct pages.
            self.assertTrue(row['separated_sources'])
            self.assertEqual(case['direct_B_pages']['probability_upper_decimal'], '0')
            if row['dfs'] and row['stash_buckets'] > 1:
                self.assertEqual(Q(case['ranges']['per_range_upper']),
                                 Q(positive_excess_bound(1 << row['index_bits'], 64)))
            self.assertLess(Q(case['per_job_upper_exact']), Q(1, 1 << 78))


@unittest.skipUnless(SPACE.exists() and not TABLE.errors and TABLE.entries,
                     'configuration_space_2p27.json not generated')
class SpaceArtifactTests(unittest.TestCase):
    def test_recomposition_and_theorem(self):
        import certify_configuration_space as space
        data = json.loads(SPACE.read_text())
        # It depends on the table entries it used, each still as recorded.
        self.assertTrue(data['bound_table_entries'])
        self.assertEqual(TABLE.stale_entries(data['bound_table_entries']), [])
        names = set()
        for c in data['candidates']:
            with self.subTest(candidate=c['name']):
                names.add(c['name'])
                self.assertEqual(c['configuration']['levels'], c['levels'])
                self.assertEqual(c['geometry']['capacity_entries'], data['capacity_entries'])
                certs = space.CandidateCertificates(TABLE, c['level_one_native']['passed'])
                passes = cc.native_passes(c['configuration'], c['native_inventory'], certs)
                self.assertEqual(cc.passes_sha256(passes), c['inventory']['ledger_obligations_sha256'])
                passes += [dict(name='integrated_inventory', clock='integrated_inventory',
                                exposures=1, obligations=[c['inventory_line']]),
                           dict(name='native_applicability', clock='native_applicability',
                                exposures=1, obligations=[c['native_applicability_line']])]
                result = cc.assemble(passes, data['target_exact'])
                self.assertEqual(result['conditional_lifetime_upper_exact'],
                                 c['conditional_lifetime_upper_exact'])
                self.assertEqual(c['meets_target'],
                                 Q(result['conditional_lifetime_upper_exact']) <= Q(data['target_exact'])
                                 and not result['coverage_gaps'])
        theorem = data['theorem']
        self.assertEqual(len(names), theorem['candidates'])
        self.assertEqual(theorem['proved'], all(c['meets_target'] for c in data['candidates']))
        floor = theorem['planner_default_top_digit_floor']
        self.assertEqual(floor['proved'], all(c['meets_target'] for c in data['candidates']
                                               if c['top_digit'] >= floor['min_top_digit']))
        self.assertEqual(set(theorem['failing']),
                         {c['name'] for c in data['candidates'] if not c['meets_target']})
        self.assertIn(theorem['planner_default']['name'], names)
        for r in data['planner_counts']:
            self.assertEqual(r['planner_candidates'], r['enumerated'])

    def test_candidate_space_is_the_arithmetic_one(self):
        """At B = 8, s = 1 the exact-capacity geometries are the solutions of
        log2 r0 + log2 D + sum(log2 b_l) = log2(N / 64) over the two ladders."""
        data = json.loads(SPACE.read_text())
        bits = data['capacity_entries'].bit_length()-1-6
        expected = set()
        for r0 in (2, 4, 8):
            for d in (1, 2, 4, 8):
                rest = bits-(r0.bit_length()-1)-(d.bit_length()-1)
                for levels in range(2, 40):
                    for a in (1, 2, 3):
                        f = [4]*a+[8]*(levels-1-a) if a <= levels-1 else None
                        if f and sum(x.bit_length()-1 for x in f) == rest:
                            expected.add((levels, r0, d, tuple(f)))
                    for b in (2, 4, 8):
                        f = [b]+[8]*(levels-2)
                        if sum(x.bit_length()-1 for x in f) == rest:
                            expected.add((levels, r0, d, tuple(f)))
        found = {(c['levels'], c['prefix_flushes'], c['top_digit'], tuple(c['level_fanouts']))
                 for c in data['candidates']}
        self.assertEqual(found, expected)


if __name__ == '__main__':
    unittest.main()
