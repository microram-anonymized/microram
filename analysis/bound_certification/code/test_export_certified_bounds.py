#!/usr/bin/env python3
"""The planner table's exporter: exact upward rounding, stale refusal and the
hash-cycle guard (python3 -m unittest test_export_certified_bounds)."""
from fractions import Fraction as Q
import json
from pathlib import Path
import tempfile
import unittest

import export_certified_bounds as ecb
from source_scope import provenance


class RoundingTests(unittest.TestCase):
    def test_exact_powers(self):
        self.assertEqual(ecb.ceil_log2_millis(Q(1, 1 << 64)), -64000)
        self.assertEqual(ecb.ceil_log2_millis(Q(1, 2)), -1000)
        self.assertEqual(ecb.ceil_log2_millis(1), 0)

    def test_rounds_up(self):
        # Just above 2^-64 must not round to -64000.
        self.assertEqual(ecb.ceil_log2_millis(Q(1, 1 << 64) * Q(10**30 + 1, 10**30)), -63999)
        self.assertEqual(ecb.ceil_log2_millis(Q(3, 4)), -415)  # log2 0.75 = -0.41504
        for value in (Q(7, 1000), Q(123456789, 10**40), Q(1, 3**50)):
            m = ecb.ceil_log2_millis(value)
            self.assertLessEqual(value**1000, Q(2)**m)
            self.assertGreater(value**1000, Q(2)**(m - 1))

    def test_zero_is_refused(self):
        with self.assertRaises(ValueError):
            ecb.ceil_log2_millis(0)


class StaleTests(unittest.TestCase):
    def test_mismatched_source_is_stale(self):
        artifact = dict(input_sha256={'bound_table.json': '0'*64},
                        source_sha256=provenance(
                            {'analysis/bound_certification/code/manifest.py': '0'*64}))
        reasons = ecb.stale_reasons(artifact, 'x.json')
        self.assertEqual(len(reasons), 2)

    def test_other_scope_lists_are_stale(self):
        name = 'analysis/bound_certification/code/manifest.py'
        artifact = dict(input_sha256={'manifest.py': ecb.sha(ecb.HERE/'manifest.py')},
                        source_sha256={name: ecb.sha(ecb.ROOT/name)})
        self.assertEqual(len(ecb.stale_reasons(artifact, 'x.json')), 1)

    def test_matching_source_is_current(self):
        name = 'analysis/bound_certification/code/manifest.py'
        artifact = dict(input_sha256={'manifest.py': ecb.sha(ecb.HERE/'manifest.py')},
                        source_sha256=provenance({name: ecb.sha(ecb.ROOT/name)}))
        self.assertEqual(ecb.stale_reasons(artifact, 'x.json'), [])


class GuardTests(unittest.TestCase):
    def test_probes_do_not_reach_the_table(self):
        self.assertEqual(ecb.include_closure_violations(), [])

    def test_a_planted_include_is_caught(self):
        with tempfile.TemporaryDirectory() as tmp:
            planted = Path(tmp)/'planted.cpp'
            planted.write_text(f'#include "{ecb.GUARDED[0]}"\nint main() {{}}\n')
            self.assertTrue(ecb.include_closure_violations([planted]))


class OutputTests(unittest.TestCase):
    def test_render_is_deterministic_and_marks_staleness(self):
        text, records, _ = ecb.build(allow_stale=True)
        again, _, _ = ecb.build(allow_stale=True)
        self.assertEqual(text, again)
        self.assertIn(f'kCertifiedBoundRecordCount = {len(records)};', text)
        for r in records:
            self.assertEqual(r['meets'], r['millis'] <= -64000)


if __name__ == '__main__':
    unittest.main()
