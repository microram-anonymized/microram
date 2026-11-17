#!/usr/bin/env python3
"""Fail-closed inventory and known-refusal checks for the d = 2 generator."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import regen_d2 as generator


def result(name, status=0, stderr=''):
    sub, filename = name.split('/')
    return {'sub': sub, 'name': filename,
            'args': generator.decode(sub, filename), 'status': status, 'stderr': stderr}


def refusal(name):
    return result(name, 2, generator.EXPECTED_REFUSAL_STDERR)


class RefusalTests(unittest.TestCase):
    def setUp(self):
        self.names = generator.battery_names()
        self.known = sorted(generator.EXPECTED_CARRY_REFUSALS)[0]
        self.normal = next(name for name in self.names if name not in generator.EXPECTED_CARRY_REFUSALS)

    def test_known_refusals_are_exactly_fifteen_canonical_cases(self):
        self.assertEqual(len(self.names), 1964)
        self.assertEqual(len(set(self.names)), 1964)
        self.assertEqual(len(generator.EXPECTED_CARRY_REFUSALS), 15)
        self.assertTrue(generator.EXPECTED_CARRY_REFUSALS.issubset(self.names))
        self.assertEqual(sum(n.startswith('fx/') for n in generator.EXPECTED_CARRY_REFUSALS), 3)
        self.assertEqual(sum(n.startswith('fy/') for n in generator.EXPECTED_CARRY_REFUSALS), 12)
        for name in generator.EXPECTED_CARRY_REFUSALS:
            generator.decode(*name.split('/'))

    def test_complete_inventory_retains_every_disposition(self):
        rows = [refusal(name) if name in generator.EXPECTED_CARRY_REFUSALS else result(name)
                for name in self.names]
        self.assertEqual(generator.validate_results(rows, self.names), [])
        self.assertEqual(sum(row['expected_refusal'] for row in rows), 15)
        self.assertEqual(sum(row['status'] == 0 for row in rows), 1949)
        for row in rows:
            if row['expected_refusal']:
                self.assertEqual(row['status'], 2)
                self.assertEqual(row['stderr'], generator.EXPECTED_REFUSAL_STDERR)

    def test_unknown_refusal_is_not_accepted_by_matching_message(self):
        rows = [refusal(self.normal)]
        self.assertTrue(generator.validate_results(rows, [self.normal]))
        self.assertFalse(rows[0]['expected_refusal'])

    def test_changed_known_status_is_rejected_even_if_successful(self):
        for status in (0, 1, 3, -9):
            with self.subTest(status=status):
                rows = [result(self.known, status, generator.EXPECTED_REFUSAL_STDERR)]
                self.assertTrue(generator.validate_results(rows, [self.known]))
                self.assertFalse(rows[0]['expected_refusal'])

    def test_known_refusal_requires_exact_diagnostic(self):
        for diagnostic in ('', 'a different harness failure', generator.EXPECTED_REFUSAL_STDERR + ' extra'):
            with self.subTest(diagnostic=diagnostic):
                rows = [result(self.known, 2, diagnostic)]
                self.assertTrue(generator.validate_results(rows, [self.known]))
                self.assertFalse(rows[0]['expected_refusal'])

    def test_missing_selected_result_is_rejected(self):
        self.assertTrue(generator.validate_results([result(self.normal)], [self.normal, self.known]))
        self.assertTrue(generator.validate_results([refusal(self.known)], [self.normal, self.known]))

    def test_duplicate_or_unselected_results_are_rejected(self):
        self.assertTrue(generator.validate_results([refusal(self.known), refusal(self.known)], [self.known]))
        self.assertTrue(generator.validate_results([refusal(self.known), result(self.normal)], [self.known]))
        self.assertTrue(generator.validate_results([refusal(self.known)], [self.known, self.known]))

    def test_subsets_validate_only_selected_known_refusals(self):
        self.assertEqual(generator.validate_results([result(self.normal)], [self.normal]), [])
        self.assertEqual(generator.validate_results([refusal(self.known)], [self.known]), [])
        custom = 'fx/f_F00D_0_0.json'
        self.assertNotIn(custom, self.names)
        self.assertEqual(generator.validate_results([result(custom)], [custom]), [])

    def test_cli_rejects_stale_refusal_and_missing_success_fixture(self):
        for label, name, diagnostic in [
                ('stale', self.known, 'known refusal has a stale fixture'),
                ('missing', self.normal, 'successful run has no fixture')]:
            with self.subTest(label=label), tempfile.TemporaryDirectory() as directory:
                work = Path(directory)
                source = work / 'previous' / name
                source.parent.mkdir(parents=True)
                source.write_text('{}')
                output = work / 'out'
                if label == 'stale':
                    stale = output / name
                    stale.parent.mkdir(parents=True)
                    stale.write_text('{}')
                dumper = work / 'dumper.py'
                dumper.write_text('#!' + sys.executable + '\nimport sys\n' +
                                  ('print(' + repr(generator.EXPECTED_REFUSAL_STDERR) +
                                   ',file=sys.stderr)\nsys.exit(2)\n' if label == 'stale' else 'sys.exit(0)\n'))
                dumper.chmod(0o755)
                command = [sys.executable, str(Path(generator.__file__).resolve()),
                           str(output), '--from', str(work / 'previous'),
                           '--exe', str(dumper), '--jobs', '1']
                run = subprocess.run(command, capture_output=True, text=True)
                self.assertNotEqual(run.returncode, 0)
                self.assertIn(diagnostic, run.stdout)

    def test_from_and_subsets_keep_known_refusal_checks(self):
        # Exercise the real CLI against a tiny fake dumper: no C++ build or model.
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            source = work / 'previous'
            for name in [self.known, 'fy/f_1_16_0_0_0_0.json']:
                path = source / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('{}')
            dumper = work / 'dumper.py'
            dumper.write_text('#!' + sys.executable + '\n'
                              'import pathlib,sys\n'
                              'p=pathlib.Path(sys.argv[1])\n'
                              'if p.name == ' + repr(self.known.split('/')[1]) + ':\n'
                              ' print(' + repr(generator.EXPECTED_REFUSAL_STDERR) + ',file=sys.stderr)\n'
                              ' sys.exit(2)\n'
                              'p.write_text("{}")\n')
            dumper.chmod(0o755)
            script = Path(generator.__file__).resolve()
            command = [sys.executable, str(script), str(work / 'out'), 'fx',
                       '--from', str(source), '--exe', str(dumper), '--jobs', '1']
            run = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
            self.assertIn('0 fixtures produced; 1 expected carry-construction refusals; 1 knob sets attempted', run.stdout)
            # The same known name changing to success must fail the real CLI.
            dumper.write_text('#!' + sys.executable + '\nimport pathlib,sys\npathlib.Path(sys.argv[1]).write_text("{}")\n')
            command[2] = str(work / 'changed')
            run = subprocess.run(command, capture_output=True, text=True)
            self.assertNotEqual(run.returncode, 0)
            self.assertIn('known carry refusal changed', run.stdout)


if __name__ == '__main__':
    unittest.main()
