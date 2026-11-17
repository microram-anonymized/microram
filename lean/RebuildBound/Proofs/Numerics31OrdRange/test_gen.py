#!/usr/bin/env python3
"""Small metadata regressions; arithmetic is independently checked in Lean."""
import copy
import importlib.util
import json
import os
from fractions import Fraction
from pathlib import Path
import unittest
import tempfile

HERE = Path(__file__).resolve().parent
SOURCE = Path(os.environ.get('NUMERICS31_SOURCE_ROOT') or HERE / '../../..').resolve()
spec = importlib.util.spec_from_file_location('ordinary_generator', HERE / 'gen.py')
gen = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gen)


class GeneratorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.pilot = gen.helper(SOURCE)
        cls.inventory = json.loads((SOURCE.parent / 'analysis/bound_certification/code/lean_configuration_2p31.json').read_text())
        cls.pilot_spec = (SOURCE / 'RebuildBound/Spec/Numerics31Pilot.lean').read_text()
        cls.spec = (SOURCE / 'RebuildBound/Spec/Numerics31Ordinary.lean').read_text()

    def rows(self, inventory=None):
        return gen.all_rows(inventory or self.inventory, self.pilot_spec, self.spec, self.pilot)

    def test_complete_inventory(self):
        rows = self.rows()
        self.assertEqual(len(rows), len(self.inventory['shapes']['sep']))
        self.assertEqual(sum(r['pilot'] for r in rows), 4)
        self.assertEqual(sum(r['selected'] for r in rows), 6)
        self.assertEqual(sum(not r['pilot'] and not r['selected'] for r in rows), 28)

    def test_allocation(self):
        costs = []
        for r in self.rows():
            n = self.inventory['clocks'][f'ordinary_L{r["level"]}_d{r["digit"]}']['exposures']
            cost = n * Fraction(r['bn'], r['bd'])
            if (r['level'], r['digit']) == (7, 6):
                self.assertEqual(cost, Fraction(1, 2**71))
            costs.append(cost)
        self.assertEqual(sum(costs) * 2**65, Fraction(891, 1024))

    def test_duplicate_row_rejected(self):
        inventory = copy.deepcopy(self.inventory)
        inventory['shapes']['sep'].append(inventory['shapes']['sep'][0])
        with self.assertRaises(AssertionError):
            self.rows(inventory)

    def test_exact_reuse_key(self):
        registry = gen.chain_registry(str(SOURCE))
        self.assertIn((5, 3, Fraction(12009599006321323, 2**55)), registry)
        self.assertFalse((5, 3, Fraction(12009599006321330, 2**55)) in registry)
        self.assertFalse((6, 3, Fraction(12009599006321323, 2**55)) in registry)

    def test_reuse_workload(self):
        reused = saved = 0
        for row in self.rows():
            if row['pilot'] or row['selected']:
                continue
            for job in self.pilot.class_jobs(row):
                if gen.known_chain(str(SOURCE), job):
                    reused += 1
                    saved += job['r']
        self.assertEqual((reused, saved), (20, 88))

    def test_output_protection(self):
        selected = SOURCE / 'RebuildBound/Proofs/SelRange3/Numerics31OrdRange'
        with self.assertRaises(ValueError):
            gen.validate_output(selected, 'RebuildBound.Proofs.Numerics31OrdRange', SOURCE)
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / 'Numerics31OrdRange'
            output.with_suffix('.lean').symlink_to(SOURCE / 'RebuildBound/Spec/Numerics31Ordinary.lean')
            with self.assertRaises(ValueError):
                gen.validate_output(output, 'RebuildBound.Proofs.Numerics31OrdRange', SOURCE)

    def test_mixed_source_rejected(self):
        with self.assertRaises(ValueError):
            gen.helper(SOURCE.parent)


if __name__ == '__main__':
    unittest.main()
