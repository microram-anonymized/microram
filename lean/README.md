# RebuildBound: Lean formalization of the capacity and obliviousness bounds

This Lean 4 project (with Mathlib) formalizes the capacity certificate and the
online obliviousness argument of the level-arena hierarchical ORAM
(`src/oram/levelarena/`). It models the rebuild jobs and the online probe
cascade at record level, proves that a capacity failure is rare for every
certified geometry, and proves that the adversary's view (the buckets each
access touches) can be simulated from public information off that failure
event. The mathematics follows [REPORT.pdf](../analysis/bound_certification/REPORT.pdf); the claim-by-claim
map with every premise is [LEAN_CLAIMS.md](../analysis/bound_certification/LEAN_CLAIMS.md); the terms
(level, digit, carry, A/B, family, tier, window, start) are defined in
[analysis/bound_certification/README.md](../analysis/bound_certification/README.md#terms).

## What is proved

All headline statements quantify over the 94 standard planner geometries of
[`Spec/ConfigurationFamilyData.lean`](RebuildBound/Spec/ConfigurationFamilyData.lean)
(`ConfigurationFamily.members`: top digit `D = 8` (the top level's ways), capacities `2^11 .. 2^31`,
bucket capacity 64, load 32), from an initialized or an empty start, and over
every horizon of `h ≥ 1` windows of `2^32` accesses. Keys are arbitrary byte
strings and requests may be chosen adaptively from what the client has
observed. The probability space is the ideal tape: one independent uniform
64-bit word per (hash family, key) and an independent uniform dummy tape
(`IdealKey.tapeLaw`).

| Theorem | Statement (file) | In words |
| --- | --- | --- |
| `IdealApiFamily` | [`Spec/IdealOblivious.lean`](RebuildBound/Spec/IdealOblivious.lean) | For every legal sequence of public API requests that respects logical live capacity: every request is answered correctly by the reference execution (latest value, scalar and batch replies, probe addresses); the transcript of touched buckets has exactly the law of a simulator that reads only public data; and the reference capacity-failure event has probability at most `h · 2^-64`. |
| `IdealApiOblivious`, `IdealSeedOblivious` | [`Spec/IdealOblivious.lean`](RebuildBound/Spec/IdealOblivious.lean) | Any measurable observation that agrees with (an encoding of) the reference transcript off failure is within `h · 2^-64` of the simulator; the seed form allows client coins with unbounded support, independent of the tapes. |
| `IdealCapacity`, `IdealSeedCapacity` | [`Spec/IdealCapacity.lean`](RebuildBound/Spec/IdealCapacity.lean) | The capacity-failure bound `h · 2^-64` alone, for adaptive legal clients and for independent seeds. |
| `IdealCapacityTight`, `NativeMatchTightOverflow` | [`Spec/NativeMatch/TightOverflow.lean`](RebuildBound/Spec/NativeMatch/TightOverflow.lean) | Under the premises of `IdealCapacity`, the capacity-failure probability is at most `h` times an exact per-member rational budget, and that budget is below `2^-65.5` for all 94 members. |
| `IdealApiSeedExact`, `IdealApiExact` | [`Spec/IdealProbe.lean`](RebuildBound/Spec/IdealProbe.lean) | The exact simulation law, at any geometry meeting the structural premises (no numerical certificate). |
| `IdealApiFresh` | [`Spec/IdealFresh.lean`](RebuildBound/Spec/IdealFresh.lean) | The freshness behind that law: for every adaptive client with arbitrary byte keys and every choice of the words and the dummy tape, two different real probes never have the same hash family and key (structural premises, no numerical certificate). |
| `IdealApiBounded`, `IdealSeedBounded` | [`Spec/IdealBounded.lean`](RebuildBound/Spec/IdealBounded.lean) | Incorrect *actual* API results have outer measure at most `h · 2^-64`, for an adapter that agrees with the reference off failure. |
| `ConfigurationFamilyStructural`, `ConfigurationFamilyAnalytic`, `ConfigurationFamilyNumerics` | [`Spec/ConfigurationFamily.lean`](RebuildBound/Spec/ConfigurationFamily.lean), [`Spec/ConfigurationFamilyBound.lean`](RebuildBound/Spec/ConfigurationFamilyBound.lean) | The three ingredients: every member meets the decidable structural contract from either start; the first-failure probability is at most the horizon multiplier times the exposure sum of the per-job analytic bounds; and every initialized member's exact class-weighted budget is at most `2^-64` (kernel-checked rational arithmetic; the empty start removes exactly the initialization term). |
| `NativeMatchBestCodedFailure`, `NativeMatchBestCodedObservation`, `NativeMatchPublic*` | [`Spec/NativeMatch/`](RebuildBound/Spec/NativeMatch/) | Conditional native error composition: the operational model of the native key matcher, routing encoding and stored-key normalization adds an explicit allowance to the ideal bound. |
| `NativeMatchSixteenWindowError` | [`Spec/NativeMatch/SixteenWindow.lean`](RebuildBound/Spec/NativeMatch/SixteenWindow.lean) | For sixteen-byte keys the error term of `NativeMatchTightPublicFailure` and `NativeMatchTightPublicObservation` is below `h · 2^-65` for every `h ≥ 1`. |

Each `<Name>` is a theorem `RebuildBound.<Name> : RebuildBound.Spec.<Name>_statement`
(registered in [`scripts/packages.txt`](scripts/packages.txt)); its proof is in
`RebuildBound/Proofs/`. The library also exports fixed-geometry statements
(`*31`, for the single capacity-`2^31` geometry `geometry31`) and
fixed-key-universe statements (`Generic*31`, `ConfigurationFamilyCausal`,
`ConfigurationFamilyWindows`, `ConfigurationFamilyOblivious`). They keep their
own, stronger premises; the canonical `Ideal*` endpoints above do not depend on
them. [LEAN_CLAIMS.md](../analysis/bound_certification/LEAN_CLAIMS.md#configuration-family-capacity-and-privacy)
lists every export.

**Premises.** The theorems are about the Lean model on the ideal tape. What
connects them to the C++ engine is stated, not proved: the engine executes the
model (supported by the differential tests below and by component refinement
proofs), its observation agrees with the model's view off failure, its probe
schedule does not depend on the hash words, the rebuild jobs' memory traces
depend only on public geometry, and AES is replaced by the ideal tape (the
cryptographic distance is accounted in [ERROR_ACCOUNTING.md](../analysis/bound_certification/ERROR_ACCOUNTING.md)).
[LEAN_CLAIMS.md, "Premises and their evidence"](../analysis/bound_certification/LEAN_CLAIMS.md#premises-and-their-evidence)
lists each premise with its Lean name and evidence;
["Out of scope"](../analysis/bound_certification/LEAN_CLAIMS.md#out-of-scope) lists what is not covered
(threaded execution, timing, compiled-code refinement).

## Layout

| Path | Contents |
| --- | --- |
| `RebuildBound/Spec/` | The trusted base: every statement (`*_statement : Prop`) and the definitions it uses. A reviewer reads this tree. |
| `RebuildBound/Spec/Model/` | The record-level models of the rebuild jobs (d = 2 merge, general-digit merge, direct level one, top preparation and finish), the serialised hierarchy (`Hierarchy.lean`), the online probe cascade and the adversary's view (`Online.lean`, `OnlineBatch.lean`), adaptive clients (`Adaptive.lean`) and the public API. Core Lean only (no Mathlib). The `ENGINE_*.md` and `DIRECT_JOB_CONTRACT.md` notes beside them record the engine semantics each model was extracted from, with source anchors. |
| `RebuildBound/Proofs/` | The proofs, one *package* per file `<ID>.lean` or directory `<ID>/`. A package proves the theorems that `scripts/packages.txt` registers for `<ID>`, each with exactly its Spec statement as its type; packages without registered theorems hold lemmas or conditional forms (`X_of : premises → X`) that a later package assembles. Proofs need not be read to trust the results. |
| `RebuildBound/Proofs/*/gen.py` | Generators of the numerical certificate modules (marked "Generated by"); they propose integers that Lean checks (see below). |
| `RebuildBound/Util/` | Proof helpers shared by several packages. |
| `RebuildBound/Oracle/` | Library code of the differential-test executable `lake exe oracle`. |
| `RebuildBound.lean` | The library root: imports the Spec and Proofs modules of the results; `lake build` builds every module under `RebuildBound/` (the `RebuildBound.*` glob in `lakefile.toml`). |
| `spec_tests/` | Regression and non-vacuity tests (`lake test`): concrete runs that discharge every premise of the headline statements and show that the failure events are nonempty, plus checks that the definitions compute what they claim. The `*.py` files cross-check selected statements numerically on small instances. |
| `oracle/` | C++ fixture dumpers and drivers for the differential tests ([oracle/README.md](oracle/README.md)). |
| `scripts/` | Dependency installation, audits and their regression tests. |

Package and module IDs (`X1`, `P5a`, `P11`, `Phase0`, `NCA1`, ...) are opaque
labels; [`scripts/packages.txt`](scripts/packages.txt) lists what each proves.
They are unrelated to the premises P1–P11 of [LEAN_CLAIMS.md](../analysis/bound_certification/LEAN_CLAIMS.md).
In proof comments and script identifiers, *legacy* denotes the bounded
numeric-key forms (keys below a numeric bound or in one fixed finite universe,
finite family tapes, the selected `*31` geometry), as opposed to the canonical
arbitrary-byte-key `Ideal*` forms.

## Trusted base

A reader must trust the Spec tree, Lean's kernel and Mathlib's definitions.
The audits below establish the rest:

- every registered theorem has exactly its Spec statement as its type;
- the library's axioms are only `propext`, `Classical.choice` and
  `Quot.sound` (Lean's standard axioms; `Classical.choice` enters through
  Mathlib), and no library module declares an axiom;
- outside `RebuildBound/Oracle/` (the fixture reader, which uses Lean's JSON
  library), the library uses no `sorry`, `admit`, `native_decide`,
  `implemented_by`, `extern`, `unsafe`, metaprogramming, `Lean` namespace or
  `debug.` kernel options. Numerical certificates are checked with
  `decide +kernel`, which evaluates in the kernel itself; the kernel's
  GMP-accelerated natural-number arithmetic is part of the trusted kernel. The
  oracle, a few spec tests and the audit scripts use `import Lean` or compiled
  code; no theorem imports them.

Mathlib's and core's `.olean` files come from the pinned binary cache and are
trusted with the toolchain; `leanchecker` replays the RebuildBound modules,
not Mathlib's.

## Build

Requirements: Linux x86-64 (Ubuntu or Debian for `install_deps.sh`), `git`,
`curl`, a C toolchain and Python 3. The audit scripts also need GNU time at
`/usr/bin/time` (package `time`). The toolchain is pinned in
[`lean-toolchain`](lean-toolchain) (`leanprover/lean4:v4.34.1`) and Mathlib in
[`lakefile.toml`](lakefile.toml) and [`lake-manifest.json`](lake-manifest.json)
(tag `v4.34.1`).

```sh
cd lean
scripts/install_deps.sh --no-build        # elan (checksum-pinned) + the pinned toolchain
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NAT_MAX_SIZE=1000000000       # the kernel must accept the checkers' packed big integers
lake exe cache get                        # Mathlib's prebuilt .olean cache (about 8 GB in .lake/)
lake build                                # the library and the spec tests (default targets)
lake test                                 # the spec tests alone
lake build oracle                         # the differential-test executable
```

`scripts/install_deps.sh` without `--no-build` also runs `lake exe cache get`
and `lake build`.
The library has about 1,700 modules; most build quickly, but the generated
numerical certificate modules dominate: individual kernel checks take tens of
seconds and some modules peak at about 20 GB of memory each (per-module costs
are in the docstrings of `Proofs/NCA1.lean`, `Proofs/SelRange*.lean` and
similar). Lake builds modules in parallel, so a full build wants a many-core
machine with a few hundred GB of RAM; a smaller machine can build individual
modules and their imports, for example
`lake build RebuildBound.Spec.IdealOblivious` (a statement and its trusted
definitions).

## Audit

Run from this directory, after `lake build`. The audits identify sources
through git (`git ls-files`, `git ls-tree`, `git rev-parse`), so run them in a
git checkout; from an archive without `.git`, first run
`git init && git add -A && git -c user.name=r -c user.email=r@localhost commit -qm snapshot`
at the repository root.

```sh
scripts/audit_axioms.sh     # registry types + from-scratch axiom walk over every module (about a minute)
scripts/audit_spec.sh       # build and kernel-replay every Spec module with leanchecker
python3 scripts/lean_forbidden.py RebuildBound.lean \
  $(find RebuildBound -name '*.lean' -not -path 'RebuildBound/Oracle/*')   # forbidden-construct scan
lake env leanchecker RebuildBound.Proofs.IdealOblivious                 # kernel replay of any module
```

- `audit_axioms.sh` walks the type and value of every constant of every
  `RebuildBound` module from scratch (not the per-module axiom lists stored in
  `.olean` files) and fails on any axiom other than the three above. It also
  checks every entry of `scripts/packages.txt` and that every imported module
  is visible to git.
- `audit_spec.sh` replays the trusted base (`RebuildBound.Spec`) in the kernel
  and names it by a git tree hash (`scripts/spec_tree.sh`); one replay takes
  about 6 minutes and about 180 GB peak memory on a 64-thread host.
- `lake env leanchecker RebuildBound` replays the whole library in the kernel.
  It is the most expensive check: about 26 minutes and about 660 GB peak
  memory on a 64-thread host.
- `python3 scripts/review_surface.py --output-dir DIR` lists, for the headline
  statements, every declaration and source span they depend on (types and
  definitions, not proofs): the part of the Spec tree a reviewer must read.
- The audit scripts have their own regression tests:
  `scripts/test_audit_spec.sh`, `scripts/test_spec_target.sh`,
  `python3 scripts/test_review_surface.py` and
  `python3 scripts/test_semantic_imports.py` (the last checks that the semantic
  endpoints do not import numerical certificate modules).

## Numerical certificates

The probability bounds reduce to finite rational arithmetic: stop-loss sums of
Poisson and binomial laws through the shadow tree, the positive series `Φ_K`,
and exposure-weighted budgets per geometry. Executable checkers written in
Lean (`Proofs/NTop`, `Proofs/NCA1`, `Proofs/NCA5` and the `Numerics*` packages)
are proved sound once; the generated modules then apply them to concrete
integers with `decide +kernel`. The generators (`Proofs/*/gen.py`, with
`registry.json` files recording which certificate covers which shape) only
propose numbers; a wrong number makes a check fail, never a false claim. The
same certificates are computed independently in Python by
[`analysis/bound_certification/code/`](../analysis/bound_certification/code/README.md), which is not part of the Lean trust base.

## Differential tests against the C++ engine

`lake exe oracle` reads JSON fixtures written by C++ dumpers that drive the
real engine headers, reruns the fixture's inputs through the trusted Lean
model, and compares verdicts and lane-exact table contents. The batteries
cover each rebuild job on its own (d = 2 merge, radix digits 2–8, top finish,
top preparation and initialization, direct level one), whole-hierarchy runs
compared table by table (`--hierarchy`), the adversary's view of every scalar
and batch access against `Model.Online` and `Model.OnlineBatch` (`--view`),
two-secret runs that must have identical public schedules, the public API
(`--api`), and wide-key normalization. Every driver also mutates fixtures and
requires the oracle to reject them. This is finite evidence for the
native-correspondence premises, not a proof; [oracle/README.md](oracle/README.md)
gives the commands, schemas and coverage.
