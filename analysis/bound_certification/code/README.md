# Conditional capacity certification tools

This directory computes the numerical capacity certificates described in
[REPORT.pdf](../REPORT.pdf) and exports them to the library planner. Level one
uses the dense-direct builder. Every result here is **conditional** on the
report's source-law and execution premises (status `unproved_applicability`,
unconditional upper bound one); [../README.md](../README.md) explains how this
relates to the kernel-checked Lean family proof.

## Pipeline

1. **Native probes** (`*_probe.cpp`) compile against the production headers
   and print public job shapes, pools, range maps, tier and stash widths
   without allocating record tables. `probe_build.py` compiles and caches them
   by content; `source_scope.py` lists the engine headers whose edits stale a
   certificate.
2. **Per-job bounds.** `bound_table.py` memoizes one exact bound per distinct
   native shape (key = job role plus every probe field except the level index;
   see [CONFIGURATION_SPACE.md](../CONFIGURATION_SPACE.md#scope-and-exact-keys)).
   It draws on the job-specific certifiers below.
3. **Composition.** `check_configuration.py` composes conditional component
   bounds with exact exposure counts for one configuration (missing evidence
   is charged one). `certify_configuration_space.py` composes every planner
   candidate per capacity and stash setting into
   `configuration_space_2p{n}.json` (`s=1`) and
   `configuration_space_s{s}_q2_2p{n}.json` (`s=2,4`).
4. **Export.** `export_certified_bounds.py` writes the gap-free candidates to
   `src/oram/levelarena/cpu_byteslice_level_arena_certified_bounds.inc` and
   fails closed on stale provenance.

## Files

Job-specific certifiers and numerical kernels:

| File | Covers |
| --- | --- |
| `certify_level1.py` | Direct level one: the producer's global positive excess for digits above one, completed-A routing and unfiltered A ranges, and a shared output-excess witness for the merge stash and both drain phases. Digit one has only its output-tier event. A and B share the current word family; no independent carry-selection law or conditioning on producer success is used. |
| `certify_separated_sources.py` | Higher ordinary (separated) levels. |
| `certify_top_preparation.py`, `evaluate_top_finish.py` | Binary top preparation, initialization and finish. |
| `certify_completed_a.py`, `certify_preparation.py`, `certify_tier_router.py`, `certify_sorted_range.py`, `certify_oram.py`, `loss_tree.py` | Reusable outward-rounded numerical bounds (completed-A joint state, A-only preparation by coordinatewise deletion, positive-series stop-loss for complete-home excess, sorted final ranges, ORAM overflow series, shadow-loss tree). `gmp_square.cpp` is an optional accelerator for one exact convolution. |
| `analyze_tier_sizes.py` | The finite-multinomial lower witness against a single top tier bucket. |

Native audits (each writes a JSON artifact; the ordinary-range and deterministic-inventory audits are inputs of `check_configuration.py`, the other two are fail-closed consistency checks):

| File | Checks |
| --- | --- |
| `audit_ordinary_ranges.py` | Ordinary range maps and dependencies. |
| `audit_preparation_contract.py` | Completed non-top preparation inputs, old-home bias and families ([PREPARATION_CONTRACT.md](PREPARATION_CONTRACT.md)). |
| `audit_separated_sources.py` | Complete A routing and direct B offers in separated jobs. |
| `audit_deterministic_inventory.py` | Maps every native capacity test and fixed extent to a matching witness or deterministic bound (REPORT, "Deterministic inventory"). |

Reference ledgers: `selected_configuration_check.json` and
`selected_configuration_half_fanout_check.json` are full ledgers for two
capacity-`2^27` configurations (`r0=8`, `D=8`, `s=1`, `q=2`; uniform fanout
eight and the planner's half-fanout ladder), produced by
`check_configuration.py --details`.

Lean family inventory (inputs to the Lean proof in the repository's top-level `lean/`):

| File | Role |
| --- | --- |
| `lean_configuration_inventory.py` → `lean_configuration_2p31.json` | Shape-only inventory of the `geometry31` candidate: all shapes (including the distinct initialization drain), exact exposures, certificate reuse and finite-word class multiplicities. It certifies no probability bound; `lean/spec_tests/Configuration31.lean` compares every field with `Configuration31` and rejects geometry/accounting mutations. |
| `configuration_family.py` → `configuration_family.json` | The standard unpinned-top candidate domain at `2^11..2^31`: 220 full keys stored once, each of the 94 members' exposures, and initialized/empty conditional totals. |
| `configuration_family_lean.py` | Links native family shapes to the Lean certificate inventory; its labels are not certificates. |
| `configuration_family_fields.py` (+ `configuration_family_fields_probe.cpp`) | Classifies every planner request and public option field and checks that fixed-geometry layout/pricing variations do not change job keys. |
| `configuration_family_structure.py` | Reruns all 94 native shape probes and generates the compact Lean member parameters; `lean/spec_tests/ConfigurationFamily.lean` instantiates the structural proofs from both starts. |
| `configuration_family_numerics.py` | Proposes compact budgets for the Lean kernel checks and audits the generated Lean data without recomputing convolutions. |

Wide-key error reports (see [../ERROR_ACCOUNTING.md](../ERROR_ACCOUNTING.md)):

| File | Role |
| --- | --- |
| `linear_wide_key_components.py` → `linear_wide_key_components.json` | Exact-comparison and routing-pair coefficients `A(g)`, `B(g)` for all 94 geometries and both starts; the normalization allowance is `min(1, (A + q*B)/2^128)` for `q` charged lanes. Reports exact capacity/matching budgets and their margin to `2^-64`. |
| `long_key_live_collision.py` → `long_key_live_collision.{json,csv}`, `*_summary.csv`, `*_controls.csv` | Per-member tightened allocations and normalization totals for the `NativeMatchTight*` and `NativeMatchLive*` Lean endpoints, in units of `2^-64`. The Lean statements, not this report, prove validity. |

Infrastructure: `regenerate.py` (incremental driver), `manifest.py`
(`SHA256SUMS.json`, hashes of the report and active artifacts),
`build_report.py` (builds `../REPORT.pdf`, keeping TeX auxiliaries in
`../.build/`), `test_*.py` (regressions; they check results and compute none).

## Provenance

Every producer records the SHA-256 of the analysis and Lean code, probe
sources and tracked engine headers it read (`source_sha256`), of its input artifacts
(`input_sha256`) and of the gitignored shadow-loss tree caches
(`tree_cache_sha256`). The caches are deterministic; `tree_caches.py` rebuilds
the recorded ones that are missing (a fresh checkout has none) before
`regenerate.py` and `export_certified_bounds.py` check them. An artifact is
stale when any recorded hash differs from the current tree. Stale artifacts are regenerated, never re-pinned by editing
hashes: updating a recorded hash alone does not validate an old computation.
The family artifacts additionally record the full probe source closure,
including planner headers outside `source_scope.py`'s numerical scope.

## Commands

From this directory:

```sh
python3 regenerate.py --dry-run          # list stale steps
python3 regenerate.py                    # recompute stale artifacts, test, export, report, manifest
python3 export_certified_bounds.py --check
python3 manifest.py --check
```

The driver also handles test-only and report-only edits. Manual report
rebuilds use `python3 build_report.py` and `python3 manifest.py`.

Regenerate only the standard family and its Lean fixtures:

```sh
python3 regenerate.py --configuration-family
python3 configuration_family.py --check
python3 configuration_family_fields.py --check
python3 configuration_family_structure.py --check
cd ../../../lean
lake test
lake env lean --run spec_tests/ConfigurationFamilyNative.lean
```

Reproduce and check the `geometry31` inventory:

```sh
python3 lean_configuration_inventory.py
python3 lean_configuration_inventory.py --check
cd ../../../lean
lake env lean --run spec_tests/Configuration31.lean ../analysis/bound_certification/code/lean_configuration_2p31.json
```

Wide-key reports: `python3 linear_wide_key_components.py [--check]` and
`python3 long_key_live_collision.py [--check]`.
