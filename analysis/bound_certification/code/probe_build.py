"""Compiled native probes, cached by content.

Compiling a probe is most of a configuration-space run (about 9 of 11 s), and
the same probes are rebuilt by every capacity and setting.  `build` reuses a
binary while every file of its include closure (g++ -MMD) is byte-identical
to what it was compiled from, under the same compiler and flags.  That is the
binary's own dependency set -- every header, not only the ones
source_scope.py tracks for provenance.  The cache lives in .probe_cache/
(ignored by git) and is safe to delete.
"""
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
CACHE = HERE/'.probe_cache'
_COMPILER = []


def _sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _compiler():
    if not _COMPILER:
        cxx = shlex.split(os.environ.get('CXX', 'g++'))
        version = subprocess.run([*cxx, '--version'], check=True, text=True,
                                 capture_output=True).stdout.splitlines()[0]
        _COMPILER.append((cxx, version))
    return _COMPILER[0]


def build(source, optimization='-O2'):
    """The probe compiled from `source`, and its include closure as paths
    relative to the repository root."""
    source = Path(source).resolve()
    cxx, version = _compiler()
    flags = [optimization, '-std=c++17', '-march=native', '-I.', '-pthread']
    key = hashlib.sha256(json.dumps(
        [cxx, version, flags, source.relative_to(ROOT).as_posix()]).encode()).hexdigest()[:24]
    entry = CACHE/key
    exe, meta = entry/'probe', entry/'closure.json'
    if exe.exists() and meta.exists():
        closure = json.loads(meta.read_text())
        if all((ROOT/name).exists() and _sha(ROOT/name) == digest
               for name, digest in closure.items()):
            return exe, list(closure)
    entry.mkdir(parents=True, exist_ok=True)
    deps, partial = entry/'probe.d', entry/'probe.partial'
    subprocess.run([*cxx, *flags, '-MMD', '-MF', str(deps), str(source), '-o', str(partial)],
                   cwd=ROOT, check=True)
    names = shlex.split(deps.read_text().replace('\\\n', ' ').split(':', 1)[1])
    closure = {(ROOT/n).resolve().relative_to(ROOT).as_posix(): _sha(ROOT/n) for n in names}
    partial.replace(exe)
    meta.write_text(json.dumps(closure, indent=1, sort_keys=True))
    return exe, list(closure)
