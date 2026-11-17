#!/usr/bin/env python3
"""Reject broken manifest linkage before emitting the Lean structural fixtures."""
import copy
import json
import unittest

import configuration_family_structure as structure


class StructuralFixtureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = json.loads(structure.family.OUTPUT.read_text())
        cls.fixture = json.loads(structure.OUTPUT.read_text())

    def inputs(self, index=0):
        member = copy.deepcopy(self.manifest['members'][index])
        registry = self.manifest['jobs']
        rows = copy.deepcopy(member['native_metadata']) + [
            structure.bt.representative_row(registry[j['key_id']]['key'], j['level'])
            for j in member['jobs'] if j['clock'] != 'initialization']
        job, = [j for j in member['jobs'] if j['clock'] == 'initialization']
        initialization = copy.deepcopy(registry[job['key_id']]['native_initialization'])
        return member, registry, rows, initialization

    def test_all_members_link_to_manifest_and_compact_parameters(self):
        structure.validate_members(self.manifest)
        self.assertEqual([m['name'] for m in self.fixture['members']],
                         [m['name'] for m in self.manifest['members']])
        for i, want in enumerate(self.fixture['members']):
            self.assertEqual(structure.extract_member(*self.inputs(i)), want)
        self.assertEqual(structure.LEAN.read_text(), structure.lean_source(self.fixture['members']))

    def test_uniform_fanouts_expand_in_compact_parameters(self):
        count = 0
        for original, emitted in zip(self.manifest['members'], self.fixture['members']):
            cfg = original['configuration']
            if not cfg['level_fanouts']:
                count += 1
                self.assertEqual(emitted['level_fanouts'], [8]*(cfg['levels']-1))
        self.assertEqual(count, 19)

    def test_missing_and_duplicate_members_rejected(self):
        for duplicate in (False, True):
            bad = copy.deepcopy(self.manifest)
            if duplicate:
                bad['members'][-1] = bad['members'][0]
            else:
                bad['members'].pop()
            with self.assertRaisesRegex(ValueError, 'family member'):
                structure.validate_members(bad)

    def test_missing_row_wrong_shape_and_exposure_rejected(self):
        for mutation in ('missing', 'direct', 'exposure', 'key'):
            with self.subTest(mutation=mutation):
                member, registry, rows, initialization = self.inputs()
                if mutation == 'missing':
                    rows = [r for r in rows if not (r['kind'] == 'ordinary' and r['digit'] == 2)]
                elif mutation == 'direct':
                    next(r for r in rows if r['kind'] == 'ordinary')['tier_buckets'] += 1
                elif mutation == 'exposure':
                    member['jobs'][0]['exposures'] -= 1
                else:
                    member['jobs'][0]['key_id'] = member['jobs'][1]['key_id']
                with self.assertRaisesRegex(ValueError, 'jobs, keys or exposures'):
                    structure.extract_member(member, registry, rows, initialization)

    def test_initialization_drain_and_seed_changes_rejected(self):
        for mutation in ('drain', 'seed'):
            member, registry, rows, initialization = self.inputs()
            if mutation == 'drain':
                initialization['drain_pages'] += 1
            else:
                next(r for r in rows if r['kind'] == 'ordinal_seed')['seeded_carries'] += 1
            with self.assertRaises(ValueError):
                structure.extract_member(member, registry, rows, initialization)

    def test_preparation_pool_is_not_projected_from_initialization(self):
        member, original, rows, initialization = self.inputs()
        registry = copy.deepcopy(original)
        prep = next(r for r in rows if r['kind'] == 'top_prepare')
        prep['pool_buckets'] += 1
        # Keep the synthetic registry consistent so the test reaches shape
        # extraction. The native field must survive for Lean to reject it.
        for job in member['jobs']:
            if job['clock'] in ('top_prepare', 'initialization'):
                entry = copy.deepcopy(registry[job['key_id']])
                entry['key'] = structure.bt.shape_key(prep, job['clock'] == 'initialization')
                job['key_id'] = structure.bt.key_id(entry['key'])
                registry[job['key_id']] = entry
        result = structure.extract_member(member, registry, rows, initialization)
        self.assertEqual(result['shapes']['prep']['a_tier_pages'], 2)
        self.assertEqual(result['shapes']['init']['a_tier_pages'], 1)

    def test_nonstandard_configuration_rejected(self):
        member, registry, rows, initialization = self.inputs()
        member['configuration']['dense_prefixes'] = 1
        with self.assertRaisesRegex(ValueError, 'fixed structural family'):
            structure.extract_member(member, registry, rows, initialization)


if __name__ == '__main__':
    unittest.main()
