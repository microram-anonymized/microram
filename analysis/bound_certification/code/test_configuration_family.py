#!/usr/bin/env python3
"""Family manifest regressions and mutation checks (no numerical recomputation)."""
import copy
from fractions import Fraction as Q
import json
import unittest

import bound_table as bt
import configuration_family as family


class FamilyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(family.OUTPUT.read_text())

    def test_complete_domain_and_accounting(self):
        data = self.data
        self.assertEqual(data['summary']['candidates'], 94)
        self.assertEqual(data['summary']['unique_job_keys'], 220)
        self.assertEqual([len(c['candidate_names']) for c in data['capacities'][:4]], [1, 2, 3, 4])
        self.assertEqual({m['capacity_entries'] for m in data['members']},
                         {1 << k for k in range(11, 32)})
        for m in data['members']:
            family.validate_member(m, data['jobs'])
            self.assertLessEqual(Q(m['ledger']['initialized_upper_exact']), family.space.TARGET)
            self.assertLessEqual(Q(m['ledger']['empty_upper_exact']),
                                 Q(m['ledger']['initialized_upper_exact']))
            self.assertTrue(m['inventory']['complete'])
            self.assertTrue(m['families']['passed'])

    def test_structural_transitions_are_represented(self):
        members, jobs = self.data['members'], self.data['jobs']
        self.assertEqual({m['configuration']['prefix_flushes'] for m in members}, {2, 4, 8})
        small = [m for m in members if m['capacity_entries'] <= 1 << 13]
        self.assertEqual({m['configuration']['levels'] for m in small}, {2})
        self.assertTrue(any(e['key']['role'] == 'dense_level_one' and
                            e['key']['digit'] > 1 and not e['key']['dfs']
                            for e in jobs.values()))
        self.assertTrue(any(e['key']['role'] == 'initialization' and
                            e['native_initialization']['drain_pages'] != e['key']['stash_buckets']
                            for e in jobs.values()))

    def test_missing_row_and_exposure_undercount_rejected(self):
        member = self.data['members'][0]
        for mutation in ('missing', 'duplicate', 'exposure', 'total', 'empty'):
            with self.subTest(mutation=mutation):
                bad = copy.deepcopy(member)
                if mutation == 'missing':
                    bad['jobs'].pop()
                elif mutation == 'duplicate':
                    bad['jobs'].append(bad['jobs'][0])
                elif mutation == 'exposure':
                    bad['jobs'][0]['exposures'] -= 1
                elif mutation == 'total':
                    bad['ledger']['initialized_upper_exact'] = '0'
                else:
                    bad['ledger']['empty_upper_exact'] = bad['ledger']['initialized_upper_exact']
                with self.assertRaises(ValueError):
                    family.validate_member(bad, self.data['jobs'])

    def test_mutated_semantic_key_rejected(self):
        member = self.data['members'][0]
        for field in ('out_buckets', 'radix', 'older_tier_buckets'):
            with self.subTest(field=field):
                registry = copy.deepcopy(self.data['jobs'])
                registry[member['jobs'][0]['key_id']]['key'][field] += 1
                with self.assertRaisesRegex(ValueError, 'certificate key'):
                    family.validate_member(member, registry)

    def test_swapped_clock_labels_rejected(self):
        member = copy.deepcopy(self.data['members'][0])
        a, b = member['jobs'][:2]
        a['clock'], b['clock'] = b['clock'], a['clock']
        with self.assertRaisesRegex(ValueError, 'clock differs'):
            family.validate_member(member, self.data['jobs'])

    def test_registry_has_exact_keys_and_no_unused_entries(self):
        self.assertEqual(set(self.data['jobs']),
                         {j['key_id'] for m in self.data['members'] for j in m['jobs']})
        for kid, e in self.data['jobs'].items():
            self.assertEqual(kid, bt.key_id(e['key']))
            self.assertEqual(e['lean']['status'], 'certified')
            self.assertIn(e['lean']['prior_status'], ('existing', 'adaptable', 'new'))


if __name__ == '__main__':
    unittest.main()
