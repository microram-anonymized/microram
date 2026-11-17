#!/usr/bin/env python3
"""The read-only checks rebuild only missing, recorded tree caches."""
import json
from pathlib import Path
import tempfile
import unittest

import tree_caches


class TreeCacheTests(unittest.TestCase):
    def test_shipped_artifacts_record_the_expected_depths(self):
        depths = tree_caches.recorded_depths()
        self.assertTrue(depths)
        self.assertEqual(depths, set(range(2, max(depths) + 1)))

    def test_rebuilds_only_missing_recorded_caches(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            (directory/'a.json').write_text(json.dumps(
                {'tree_cache_sha256': {'tree_2.json': 'x', 'tree_4.json': 'y'}}))
            (directory/'b.json').write_text(json.dumps({'tree_cache_sha256': {'tree_3.json': 'z'}}))
            (directory/'c.json').write_text(json.dumps([1, 2]))
            (directory/'tree_3.json').write_text('{}')
            built = []

            def build(depth):
                # Like tree_at_depth: fill every depth from the last existing cache.
                for d in range(2, depth + 1):
                    path = directory/f'tree_{d}.json'
                    if not path.exists():
                        path.write_text('{}')
                        built.append(d)

            self.assertEqual(tree_caches.ensure_recorded(directory, build), [2, 4])
            self.assertEqual(built, [2, 4])
            self.assertEqual((directory/'tree_3.json').read_text(), '{}')
            self.assertEqual(tree_caches.ensure_recorded(directory, build), [])

    def test_rejects_unexpected_cache_names(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            (directory/'a.json').write_text(json.dumps({'tree_cache_sha256': {'../x.json': 'x'}}))
            with self.assertRaises(ValueError):
                tree_caches.recorded_depths(directory)


if __name__ == '__main__':
    unittest.main()
