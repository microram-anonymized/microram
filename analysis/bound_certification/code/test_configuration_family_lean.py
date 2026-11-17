#!/usr/bin/env python3
"""Certificate classification must not confuse Python values with Lean evidence."""
import copy
import json
import unittest
from unittest.mock import patch

import configuration_family_lean as evidence


class LeanInventoryTests(unittest.TestCase):
    def setUp(self):
        self.validation = patch.object(evidence, '_validated', True)
        self.validation.start()
        self.addCleanup(self.validation.stop)
        self.family = patch.object(evidence, '_family_keys', {})
        self.family.start()
        self.addCleanup(self.family.stop)
        self.current, self.legacy = evidence.inventories()

    def test_requires_fresh_shape_validation(self):
        with patch.object(evidence, '_validated', False):
            with self.assertRaises(ValueError):
                evidence.classify(next(iter(self.current.values()))[0])

    def test_current_full_keys_have_role_specific_theorems(self):
        self.assertEqual(len(self.current), 45)
        for key, _ in self.current.values():
            result = evidence.classify(key)
            self.assertEqual(result['status'], 'existing')
            self.assertIn(evidence.CHECK, result['evidence'])
            self.assertTrue(all((evidence.ROOT/p).is_file() for p in result['evidence']))

    def test_legacy_values_are_not_current_certificates(self):
        keys = [v[0] for k, v in self.legacy.items() if k not in self.current]
        self.assertTrue(keys)
        for key in keys:
            self.assertEqual(evidence.classify(key)['status'], 'adaptable')

    def test_changed_semantic_field_is_not_reused(self):
        key = copy.deepcopy(next(iter(self.current.values()))[0])
        key['tier_buckets'] = 999
        self.assertEqual(evidence.classify(key)['status'], 'new')

    def test_native_rows_cannot_disagree_with_checked_shapes(self):
        fixture = json.loads(evidence.FIXTURE31.read_text())
        evidence.validate_projection(fixture)
        row = next(r for r in fixture['native_inventory']
                   if r['kind'] == 'ordinary' and r['level'] == 1)
        row['tier_buckets'] += 1
        with self.assertRaisesRegex(ValueError, 'shape projection'):
            evidence.validate_projection(fixture)

    def test_unmatched_direct_a_pool_is_not_silently_covered(self):
        key = copy.deepcopy(next(v[0] for v in self.current.values()
                                 if v[0]['role'] == 'dense_level_one' and v[0]['digit'] == 2))
        key.update(carry_bits=2, out_buckets=8, dfs=False)
        result = evidence.classify(key)
        self.assertEqual(result['status'], 'new')

    def test_family_requires_exact_freshly_validated_key(self):
        key = copy.deepcopy(next(iter(self.current.values()))[0])
        with patch.object(evidence, '_family_keys', {evidence.bt.key_id(key): key}):
            result = evidence.classify(key)
            self.assertEqual(result['status'], 'certified')
            self.assertEqual(result['prior_status'], 'existing')
            self.assertIn(evidence.FAMILY_CHECK, result['evidence'])
            bad = dict(key, tier_buckets=999)
            self.assertEqual(evidence.classify(bad)['status'], 'new')


if __name__ == '__main__':
    unittest.main()
