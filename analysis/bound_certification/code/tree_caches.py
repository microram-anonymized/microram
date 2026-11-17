"""Rebuild missing shadow-loss tree caches before a check reads them.

The caches code/tree_<d>.json are gitignored: each is a deterministic output
of certify_sorted_range.tree_at_depth(d), and every artifact that used one
records its SHA-256 under `tree_cache_sha256`.  A fresh checkout has none, so
without this step every check would report those artifacts stale.
ensure_recorded() recomputes each recorded cache that is missing (about two
minutes for depths 2..10 in pure Python, seconds with code/libgmp_square.so).
The callers then compare the caches with the recorded hashes exactly as
before, so a wrong rebuild still fails closed.  An existing cache is never
rewritten; delete a corrupted one to have it rebuilt.

This module is tooling: no artifact records its hash, and none of the
certifiers imports it.
"""
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
NAME = re.compile(r'tree_([1-9][0-9]*)\.json')


def recorded_depths(directory=HERE):
    """Depths of every tree cache that some artifact in `directory` recorded."""
    depths = set()
    for path in sorted(directory.glob('*.json')):
        if NAME.fullmatch(path.name):
            continue
        text = path.read_text()
        if 'tree_cache_sha256' not in text:
            continue
        data = json.loads(text)
        if not isinstance(data, dict):
            continue
        for name in data.get('tree_cache_sha256', {}):
            match = NAME.fullmatch(name)
            if not match:
                raise ValueError(f'{path.name}: unexpected tree cache name {name!r}')
            depths.add(int(match.group(1)))
    return depths


def ensure_recorded(directory=HERE, build=None):
    """Rebuild the recorded caches that are missing; return their depths."""
    missing = sorted(d for d in recorded_depths(directory)
                     if not (directory/f'tree_{d}.json').exists())
    if not missing:
        return []
    print('Rebuilding missing shadow-loss tree caches '
          + ', '.join(f'tree_{d}.json' for d in missing)
          + ' (deterministic; checked against the recorded hashes)',
          file=sys.stderr, flush=True)
    if build is None:
        from certify_sorted_range import tree_at_depth as build
    for depth in missing:
        # tree_at_depth extends the deepest existing cache below `depth`, so
        # one call may also fill later entries of `missing`.
        if not (directory/f'tree_{depth}.json').exists():
            build(depth)
    return missing
