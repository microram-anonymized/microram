#!/usr/bin/env python3
"""Fast inventory/CLI regressions; the Lean and mutation suites test geometry."""
import contextlib
import importlib.util
import io
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('hierarchy_replay_tests', HERE / 'hierarchy_replay_tests.py')
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)
manifest = driver.MANIFEST


class ManifestTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name)
        for case in manifest['FIXTURES']:
            (self.directory / (case['name'] + '.json')).write_text('{}')

    def test_complete_inventory(self):
        names, ignored, notes = manifest['inventory'](self.directory)
        self.assertEqual(len(names), 64)
        self.assertEqual((ignored, notes), ([], []))
        self.assertEqual(len(manifest['PAIRS']), 5)

    def test_missing_top_finish_fails_before_replay(self):
        (self.directory / 'i_force_topfinish.json').unlink()
        report = {}
        with patch.object(driver, 'run_parallel') as replay, contextlib.redirect_stdout(io.StringIO()):
            self.assertFalse(driver.battery(str(self.directory), 1, report))
        replay.assert_not_called()
        self.assertIn('missing fixture: i_force_topfinish', report['inventory']['notes'])

    def test_missing_default_policy_pairs_fail(self):
        for path in self.directory.glob('s2_share*.json'):
            path.unlink()
        _, _, notes = manifest['inventory'](self.directory)
        self.assertEqual(len(notes), 6)
        self.assertTrue(all('s2_share' in note for note in notes))

    def test_unexpected_fixture_fails(self):
        (self.directory / 'renamed_topfinish.json').write_text('{}')
        self.assertIn('unexpected fixture: renamed_topfinish', manifest['inventory'](self.directory)[2])

    def test_no_selected_accepts_fresh_or_stale_selected_files(self):
        names, ignored, notes = manifest['inventory'](self.directory, False)
        self.assertEqual(len(names), 60)
        self.assertEqual(set(ignored), set(driver.SELECTED))
        self.assertEqual(notes, [])
        self.assertTrue(set(names).isdisjoint(driver.SELECTED))
        for name in driver.SELECTED:
            (self.directory / (name + '.json')).unlink()
        self.assertEqual(manifest['inventory'](self.directory, False), (names, [], []))

    def test_no_selected_cli_reaches_all_checks_consistently(self):
        report = self.directory / 'report.txt'
        def battery(directory, jobs, out, include_selected=True):
            self.assertFalse(include_selected)
            out['inventory'] = {'ok': True}
            return True
        with patch.object(sys, 'argv', ['hierarchy_replay_tests.py', '--no-generate', '--no-selected',
                                      '--report', str(report)]), \
             patch.object(driver, 'git', return_value='test'), \
             patch.object(driver.subprocess, 'run') as run, \
             patch.object(driver, 'battery', side_effect=battery), \
             patch.object(driver, 'mutations', return_value=True) as mutations, \
             patch.object(driver, 'two_secret', return_value=True), \
             patch.object(driver, 'shapes') as shapes, \
             contextlib.redirect_stdout(io.StringIO()):
            run.return_value.returncode = 0
            self.assertEqual(driver.main(), 0)
        self.assertFalse(mutations.call_args.args[3])
        shapes.assert_not_called()


if __name__ == '__main__':
    unittest.main()
