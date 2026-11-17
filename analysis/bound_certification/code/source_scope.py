"""Which engine sources a certificate depends on.

A certificate is a function of the jobs' public shapes and the stash and
tier sizes, and of the analysis code that computes it.  So artifacts record,
and checkers compare, the hashes of exactly those engine files, every file
under analysis/ and lean/ (the probes, the Python modules and the Lean
sources), and the test helper a probe compiles.  Every other file -- the
kernels, scheduling, publication, the planner's byte bill, the public
adapters, the tests -- can change without staling a certificate.

A file belongs here when its content decides which merges run and at what
size (the odometer and merge shapes), the residual passes' pools, range and
DFS plans and their capacities, the planned stages, or a stash or tier
depth.  Moving such code into a header outside this list hides its edits
from every staleness check; add the header here instead.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]

CERTIFIED_SOURCES = frozenset({
    # Levels, digits, carry plans, tier widths.
    'src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp',
    # Stash depths, tier resolution, stash slot offsets.
    'src/oram/levelarena/cpu_byteslice_level_arena_stash.hpp',
    'src/oram/rebuild/cpu_byteslice_stash_capacity_table.hpp',
    'src/oram/rebuild/cpu_byteslice_residual_tier_bound.hpp',
    # Merge shapes and the phase plans.
    'src/oram/levelarena/cpu_byteslice_level_arena_merge.hpp',
    'src/oram/scheduler/cpu_byteslice_subtask.hpp',
    'src/oram/scheduler/cpu_byteslice_subtask_plan.hpp',
    # Residual passes: pools, range and DFS plans and their capacities.
    'src/oram/levelarena/cpu_byteslice_level_arena_pass_shape.hpp',
    'src/oram/scheduler/cpu_byteslice_residual_pass.hpp',
    'src/oram/rebuild/cpu_byteslice_residual_range.hpp',
    'src/oram/rebuild/cpu_byteslice_dfs_residual.hpp',
})


def relative(name):
    """`name` as the repository-relative path artifacts record."""
    path = Path(name)
    if path.is_absolute():
        path = path.resolve().relative_to(ROOT)
    return path.as_posix()


# Code outside analysis/ that a native probe compiles and runs.
PROBE_HELPERS = frozenset({
    'tests/oram/cpu_byteslice_level_arena_test_support.hpp',
    'tests/oram/cpu_byteslice_rebuild_test_support.hpp',
})

SELF_NAME = Path(__file__).resolve().relative_to(ROOT).as_posix()

# What artifacts record under SELF_NAME: the lists above and the rule below,
# not this file's bytes, so a comment here stales nothing while a change to
# which files count stales everything.  Bump RULE when tracked() changes.
RULE = 2


def scope_id():
    import hashlib
    import json
    return hashlib.sha256(json.dumps(
        [RULE, sorted(CERTIFIED_SOURCES), sorted(PROBE_HELPERS)]).encode()).hexdigest()


def tracked(name):
    """Whether a recorded source hash is part of a certificate's provenance:
    a listed engine file, a probe helper, or analysis or Lean code -- but not a test
    script (test_*.py checks results and computes none) and not this file
    (its entry is the scope identifier)."""
    rel = relative(name)
    if rel == SELF_NAME:
        return False
    # lean/ sat under analysis/ when RULE 2 was set; counting both keeps the
    # same files tracked.
    if rel.startswith(('analysis/', 'lean/')):
        return not Path(rel).name.startswith('test_')
    return rel in CERTIFIED_SOURCES or rel in PROBE_HELPERS


def scoped(hashes):
    """The tracked entries of a recorded {path: sha256} map: what a checker
    compares."""
    return {name: digest for name, digest in hashes.items() if tracked(name)}


def scope_current(hashes):
    """Whether a recorded map was written under today's lists."""
    return hashes.get(SELF_NAME) == scope_id()


def provenance(hashes):
    """What a producer records: the tracked entries plus the scope identifier
    (regenerate.py and the exporter treat an artifact without today's as
    stale)."""
    out = scoped(hashes)
    out[SELF_NAME] = scope_id()
    return out
