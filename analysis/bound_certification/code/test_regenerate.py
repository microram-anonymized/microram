#!/usr/bin/env python3
"""Incremental regeneration must validate edits outside numerical provenance."""
from pathlib import Path
import json
import tempfile
import unittest
from unittest.mock import patch

import manifest
import regenerate as r


class RegenerationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.here = self.root/'code'
        self.here.mkdir()
        self.patch = patch.object(r, 'HERE', self.here)
        self.patch.start()
        self.addCleanup(self.patch.stop)
        for name in ('test_example.py', 'regenerate.py', 'build_report.py'):
            (self.here/name).write_text('original')
        for name in ('REPORT.tex', 'REPORT.pdf'):
            (self.root/name).write_text('original')
        self.recorded = {name: r.sha(self.here/name) for name in (
            'test_example.py', 'regenerate.py', 'build_report.py',
            '../REPORT.tex', '../REPORT.pdf')}

    def test_current_tests_and_report_do_not_need_work(self):
        self.assertFalse(r.tests_changed(self.recorded))
        self.assertFalse(r.report_changed(self.recorded))

    def test_test_edit_addition_and_removal_trigger_validation(self):
        for operation in ('edit', 'add', 'remove'):
            with self.subTest(operation=operation):
                path = self.here/'test_example.py'
                path.write_text('original')
                extra = self.here/'test_new.py'
                extra.unlink(missing_ok=True)
                if operation == 'edit':
                    path.write_text('changed')
                elif operation == 'add':
                    extra.write_text('new')
                else:
                    path.unlink()
                self.assertTrue(r.tests_changed(self.recorded))

    def test_driver_edit_triggers_validation(self):
        (self.here/'regenerate.py').write_text('changed')
        self.assertTrue(r.tests_changed(self.recorded))

    def test_missing_or_changed_report_is_rebuilt(self):
        for name in ('REPORT.tex', 'REPORT.pdf'):
            path = self.root/name
            path.write_text('changed')
            self.assertTrue(r.report_changed(self.recorded))
            path.write_text('original')
        (self.root/'REPORT.pdf').unlink()
        self.assertTrue(r.report_changed(self.recorded))

    def test_test_only_edit_marks_runner_dirty_with_current_producers(self):
        (self.here/'test_example.py').write_text('changed')
        with patch.object(r, 'recorded_manifest', return_value=self.recorded), \
             patch.object(r, 'anything_stale', return_value=False):
            self.assertTrue(r.Runner(False, False).dirty)

    def test_manifest_includes_new_argument_documents(self):
        (self.root/'.gitignore').write_text('')
        (self.root/'FRONTIER.md').write_text('premises')
        with patch.object(manifest, 'HERE', self.here):
            self.assertIn('../FRONTIER.md', manifest.current_hashes())

    def test_family_checks_planner_sources_outside_numerical_scope(self):
        header = self.root/'planner.hpp'
        header.write_text('original')
        artifact = dict(source_sha256=r.source_scope.provenance({}),
                        strict_source_sha256={'planner.hpp': r.sha(header)})
        (self.here/'family.json').write_text(json.dumps(artifact))
        with patch.object(r, 'ROOT', self.root):
            self.assertTrue(r.current('family.json'))
            header.write_text('changed')
            self.assertFalse(r.current('family.json'))

    def test_shape_fixture_tracks_ledger_and_native_sources(self):
        ledger = self.root/'ledger.json'
        header = self.root/'planner.hpp'
        for p in (ledger, header):
            p.write_text('original')
        data = dict(format='lean-configuration-inventory/1',
                    source_sha256={p.name: r.sha(p) for p in (ledger, header)})
        fixture = self.here/'fixture.json'
        fixture.write_text(json.dumps(data))
        with patch.object(r, 'ROOT', self.root):
            self.assertTrue(r.current('fixture.json'))
            for p in (ledger, header):
                p.write_text('changed')
                self.assertFalse(r.current('fixture.json'))
                p.write_text('original')
            data['source_sha256'] = {}
            fixture.write_text(json.dumps(data))
            self.assertFalse(r.current('fixture.json'))

    def test_family_structure_tracks_generated_lean_and_checker_sources(self):
        source = self.root/'checker.lean'
        generated = self.root/'data.lean'
        for p in (source, generated):
            p.write_text('original')
        data = dict(format='configuration-family-structure/1',
                    source_sha256={source.name: r.sha(source)},
                    generated_sha256={generated.name: r.sha(generated)})
        fixture = self.here/'fixture.json'
        fixture.write_text(json.dumps(data))
        with patch.object(r, 'ROOT', self.root):
            self.assertTrue(r.current('fixture.json'))
            for p in (source, generated):
                p.write_text('changed')
                self.assertFalse(r.current('fixture.json'))
                p.write_text('original')
            generated.unlink()
            self.assertFalse(r.current('fixture.json'))
            data['generated_sha256'] = {}
            fixture.write_text(json.dumps(data))
            self.assertFalse(r.current('fixture.json'))


if __name__ == '__main__':
    unittest.main()
