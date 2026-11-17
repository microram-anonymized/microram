"""Small regressions for geometry-driven pilot generation; no Lean build needed."""
import copy
import importlib.util
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
from types import SimpleNamespace

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('range_pilot_generator', HERE / 'gen.py')
gen = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gen)
ROOT = HERE.parents[2]


class PilotGeneratorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.inventory = json.loads((ROOT.parent / 'analysis/bound_certification/code/lean_configuration_2p31.json').read_text())
        cls.spec = (ROOT / 'RebuildBound/Spec/Numerics31Pilot.lean').read_text()

    def test_finite_word_histograms_and_actual_multiplicities(self):
        for bits in range(1, 9):
            for radix in [1, 3, 5, 7]:
                histogram = Counter(value % radix for value in range(2 ** bits))
                expected = Counter({a: count for a, count in histogram.items()})
                quotient, remainder = divmod(2 ** bits, radix)
                self.assertEqual([expected[a] for a in range(radix)],
                                 [quotient + (a < remainder) for a in range(radix)])
                masses = gen.class_masses(bits, radix)
                self.assertEqual(Counter({mass: count for mass, count in masses if count}),
                                 Counter(expected[a] for a in range(radix)))
                self.assertEqual(sum(mass * count for mass, count in masses), 2 ** bits)
        for row in self.inventory['shapes']['sep']:
            if row['r'] == 7:
                nb = 64 - row['K'] - row['e']
                self.assertEqual([n for _, n in gen.class_masses(nb, 7)], [4, 3])
        self.assertEqual([n for _, n in gen.class_masses(50, 5)], [4, 1])
        self.assertEqual([n for _, n in gen.class_masses(44, 5)], [1, 4])

    def test_missing_pilot_geometry_is_rejected(self):
        changed = copy.deepcopy(self.inventory)
        selected = gen.parse_rows(self.spec)[0][:2]
        changed['shapes']['sep'] = [r for r in changed['shapes']['sep']
                                   if (r['level'], r['digit']) != selected]
        with self.assertRaisesRegex(ValueError, 'exactly one inventory geometry'):
            gen.inventory_jobs(changed, self.spec)

    def test_geometry_changes_alter_law_and_drain_does_not(self):
        rows, prep = gen.inventory_jobs(self.inventory, self.spec)
        selected = (rows[0]['level'], rows[0]['digit'])
        for field in ['I', 'stash_pages']:
            changed = copy.deepcopy(self.inventory)
            geometry = next(r for r in changed['shapes']['sep']
                            if (r['level'], r['digit']) == selected)
            geometry[field] += 1
            new_rows, _ = gen.inventory_jobs(changed, self.spec)
            self.assertNotEqual((rows[0]['t'], rows[0]['p']),
                                (new_rows[0]['t'], new_rows[0]['p']))
        changed = copy.deepcopy(self.inventory)
        changed['shapes']['init']['drain_pages'] += 1
        self.assertEqual(prep, gen.inventory_jobs(changed, self.spec)[1])

    def test_empty_chain_uses_thin_table_and_trivial_chain_proof(self):
        with tempfile.TemporaryDirectory() as directory:
            emitter = gen.Emitter(Path(directory) / 'Pilot', 'RebuildBound.Proofs.Pilot', 2)
            data = dict(job=dict(label='TP', t=9, i=17, p=4288, kind='half', qc=1, nb=1, r=1),
                        final=dict(wf=648, rr=1, fuel=18), thin=[[1]], width=637,
                        qc=1, nb=1, steps=[])
            certificate = emitter.class_certificate(data, 1, 10 ** 30, 0)
            imports, checks = emitter.lanes[0]
            self.assertIn('(steps := [])', certificate)
            self.assertIn('(by trivial)', certificate)
            self.assertIn('[NCA5.rootMarg 64 Tab.TPth]', checks[-1])
            self.assertNotIn('_s1', checks[-1])
            self.assertEqual(imports[-1], 'RebuildBound.Proofs.Pilot.TabTPth')
            self.assertTrue(all(p.parent == Path(directory) / 'Pilot' for p in emitter.files))
            self.assertFalse(list(Path(directory).rglob('*.lean')))

    def test_protected_output_and_entrypoint_are_rejected(self):
        for name in ['SelRange3', 'SelRange5', 'TPNum', 'NCA1']:
            with self.assertRaisesRegex(ValueError, 'protected proof source'):
                gen.validate_output(ROOT / 'RebuildBound/Proofs' / name,
                                    'RebuildBound.Proofs.' + name, ROOT)
        self.assertEqual(gen.validate_output(HERE, 'RebuildBound.Proofs.Numerics31Range', ROOT), HERE)
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'Fresh'
            self.assertEqual(gen.validate_output(output, 'RebuildBound.Proofs.Fresh', ROOT), output)

    def test_cross_source_arithmetic_import_is_rejected(self):
        with patch.object(gen, '_ARITHMETIC_ROOT', Path('/tmp/first-source')):
            with self.assertRaisesRegex(ValueError, 'only one source root'):
                gen.validate_arithmetic_source(ROOT)
        with patch.object(gen, '_ARITHMETIC_ROOT', None):
            with patch.dict(sys.modules, {'gen': SimpleNamespace(__file__='/tmp/other/NCA1/gen.py')}):
                with self.assertRaisesRegex(ValueError, 'another NCA1 source root'):
                    gen.validate_arithmetic_source(ROOT)

    def test_chain_reuse_depends_on_full_law_not_row_coordinates(self):
        rows, _ = gen.inventory_jobs(self.inventory, self.spec)
        row = next(r for r in rows if (r['level'], r['digit']) == (5, 5))
        job = gen.class_jobs(row)[0]
        reuse = gen.known_chain(ROOT, job)
        self.assertEqual(reuse['reuse'], 'NCA5A')
        self.assertEqual(Fraction(reuse['qc'], 2 ** reuse['nb']), Fraction(job['qc'], 2 ** job['nb']))
        altered = dict(job, p=job['p'] + 1, i=job['i'] + 1, qc=job['qc'] * 2, nb=job['nb'] + 1)
        self.assertEqual(gen.known_chain(ROOT, altered), reuse)
        for field in ['t', 'r', 'qc']:
            altered = dict(job); altered[field] += 1
            self.assertIsNone(gen.known_chain(ROOT, altered))

    def test_targets_enclose_without_float_rounding(self):
        for value in [Fraction(1, 10 ** 38), Fraction(999999, 10 ** 40),
                      Fraction(2512513217365977, 10 ** 49)]:
            numerator, denominator = gen.target(value)
            self.assertLessEqual(value, Fraction(numerator, denominator))
            self.assertGreater(value, Fraction(numerator - 1, denominator))


if __name__ == '__main__':
    unittest.main()
