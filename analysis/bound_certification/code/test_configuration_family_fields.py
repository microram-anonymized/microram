#!/usr/bin/env python3
"""Field coverage and shape changes must fail closed; direct routing is not DFS."""
import copy
import unittest

import configuration_family_fields as fields
from lean_configuration_inventory import direct_shape


class FieldAuditTests(unittest.TestCase):
    def test_all_current_fields_have_a_classification(self):
        actual = fields.checked_classifications()
        self.assertEqual(len(actual['LevelArenaCapacityRequest']), 23)
        self.assertEqual(len(actual['Options']), 51)

    def test_changed_shape_is_rejected_even_when_bill_changes_are_allowed(self):
        variants = {
            'baseline': dict(bill_bytes=100, rows=[dict(kind='initialization', drain_pages=1)]),
            'bank_off': dict(bill_bytes=150, rows=[dict(kind='initialization', drain_pages=1)]),
        }
        fields.compare_variations(variants)
        wrong = copy.deepcopy(variants)
        wrong['bank_off']['rows'][0]['drain_pages'] = 2
        with self.assertRaisesRegex(ValueError, 'bank_off changed'):
            fields.compare_variations(wrong)

    def test_direct_digit_two_preserves_nonempty_a_tier(self):
        row = dict(digit=2, dfs=False, carry_bits=2, out_buckets=8, tier_buckets=1,
                   older_tier_buckets=1, stash_buckets=2, merge_stash_buckets=3,
                   pool_buckets=7, direct_buckets=0, index_bits=0, range_bits=3)
        shape = direct_shape(row)
        self.assertEqual(shape['ranges'], dict(kind='direct'))
        self.assertEqual(shape['a_tier_capacity'], 64)
        self.assertEqual(shape['output_homes'], 8)
        self.assertEqual(shape['insertion_capacity'], 192)

    def test_dfs_keeps_its_exact_pool_and_range_widths(self):
        row = dict(digit=3, dfs=True, carry_bits=4, out_buckets=48, tier_buckets=2,
                   older_tier_buckets=2, stash_buckets=3, merge_stash_buckets=4,
                   pool_buckets=23, direct_buckets=2, index_bits=2, range_bits=4)
        self.assertEqual(direct_shape(row)['ranges'], dict(
            kind='dfs', index_bits=2, range_bits=4, pool_capacity=64*21))


if __name__ == '__main__':
    unittest.main()
