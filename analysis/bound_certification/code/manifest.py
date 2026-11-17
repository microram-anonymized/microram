#!/usr/bin/env python3
"""Write or check hashes of active report artifacts, excluding tree caches."""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def current_hashes():
    names = ['../REPORT.tex', '../REPORT.pdf', '../.gitignore']
    names += ['../' + p.name for p in HERE.parent.glob('*.md')]
    names += [p.name for p in HERE.iterdir()
              if p.suffix in {'.py', '.cpp', '.md', '.json', '.jsonl'}
              and p.name != 'SHA256SUMS.json' and not p.name.startswith('tree_')]
    return {name: hashlib.sha256((HERE/name).read_bytes()).hexdigest()
            for name in sorted(names)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    current = current_hashes()
    path = HERE/'SHA256SUMS.json'
    if args.check:
        if not path.exists() or current != json.loads(path.read_text()):
            raise SystemExit('Active artifact manifest mismatch; regenerate after reviewing changes.')
        print('Verified', len(current), 'active artifact hashes.')
    else:
        path.write_text(json.dumps(current, indent=2)+'\n')
        print('Wrote', len(current), 'active artifact hashes.')


if __name__ == '__main__':
    main()
