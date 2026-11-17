# Bound certification

This directory bounds the probability that the hierarchical ORAM's rebuild
runs out of space ("capacity failure") and connects that bound to the
library's obliviousness and correctness claims. It has three parts; the Lean
formalization lives in the repository's top-level `lean/` directory:

| Part | What it is | Trusted for |
| --- | --- | --- |
| [REPORT.tex](REPORT.tex) / [REPORT.pdf](REPORT.pdf) | The mathematics: conditional composition of per-job capacity events, the direct level-one, completed-A, binary-top and top-finish bounds, exposure accounting and the cryptographic error ledger. | Human-checked arguments |
| [code/](code/README.md) | Python certifiers and allocation-free native C++ probes. They read the engine's public job shapes, compute exact rational per-job bounds, compose them per planner configuration, and export the table the library's planner reads. | Exact arithmetic over native shapes; conditional on the report's premises |
| [lean/](../../lean/README.md) (repository root) | A Lean 4 / Mathlib formalization of the reference model, its capacity bound, exact probe simulation, API correctness and the stored-key/routing error terms. | Kernel-checked theorems with explicit premises |

[LEAN_CLAIMS.md](LEAN_CLAIMS.md) maps every proved claim to its theorem and
premises. [ERROR_ACCOUNTING.md](ERROR_ACCOUNTING.md) separates cryptographic,
stored-key normalization, matching, routing and stop errors from the capacity
term. [CONFIGURATION_SPACE.md](CONFIGURATION_SPACE.md) summarizes the numerical
results over the planner's configuration space.
[COMPLETED_A_FRONTIER.md](COMPLETED_A_FRONTIER.md) proves the deferred-mark
lemma used by the completed-A comparison. The engine itself is described in
[src/oram/levelarena/DESIGN.md](../../src/oram/levelarena/DESIGN.md) and
[src/oram/rebuild/DESIGN.md](../../src/oram/rebuild/DESIGN.md).

## Terms

- **Level, digit, fanout.** The hierarchy has `L` levels. Each level merges a
  fixed number of carries from the level below (its *fanout*) before its own
  table moves up as a carry; the position of a merge within that cycle is its
  *digit*. The top level has `D` ways (`D` a power of two; the certified
  family uses `D=8`).
- **Carry, A and B.** A merge combines the table the level built so far
  (**A**, routed under its old hash family and the new one) with the newly
  arrived carry from the level below (**B**, routed under the new family only).
- **Family.** One hash function (AES-keyed in the engine, an ideal random tape
  in the model) per `(level, ordinal)` coordinate. A table is placed and
  probed under its family; forwarding lets a level reuse its consumer's family.
- **Bucket, main, tier, stash, residual.** Tables are arrays of 64-slot
  buckets (*main*). Records that do not fit their home bucket are *residuals*;
  they go to a public-size per-level *tier* (published with the table) or to a
  temporary *stash* during a merge. A capacity failure is an overflow of any
  such public capacity.
- **Prefix, unit, `r0`, `s`, `q`.** Online writes go to a dense *prefix* of
  `r0` flush units of `64 s` slots; `q` dense prefixes are kept. Level one
  consumes one prefix per *ordinal*.
- **Geometry.** All public sizes of one configuration: capacity, levels,
  fanouts, `D`, `r0`, `s`, `q`, tier and stash widths.
- **Start.** *Initialized* (a direct initialization fills the top) or *empty*
  (no initialization job, empty top).
- **Window.** `2^32` consecutive accesses. Budgets are stated per window.

## What is certified

The target is a capacity-failure probability of at most `2^-64` per window,
i.e. at most `h * 2^-64` over the first `h ≥ 1` windows. Two artifacts carry
that target, with different strength.

**Kernel-checked (Lean).** For each of the **94 standard planner geometries**
(branching factor `B=8`, `D=8`, `s=1`, `q=2`, load 32, bucket capacity 64, automatic tier and
stash sizing) at capacities `2^11..2^31`, from initialized and empty starts,
`IdealApiFamily` proves in the ideal reference model:

- reference correctness of the public API for arbitrary byte-string keys
  (every logical prefix, every reply, and the exact list of probed addresses);
- an exact simulator for the probe view (bucket addresses and publication
  events), depending only on public shape and schedule;
- capacity failure at most `h * 2^-64` over `h` windows, for adaptive clients
  that keep at most capacity-many live keys on every legal branch.

`IdealApiOblivious` turns this into simulator distance at most `h * 2^-64` for
any observation that agrees with the reference off capacity failure;
`IdealApiBounded` bounds incorrect actual API results by the same amount under
explicit agreement. Seeded (randomized-client) forms are included. The
stored-key matching, normalization and routing terms are bounded by the
`NativeMatch*` endpoints (see [ERROR_ACCOUNTING.md](ERROR_ACCOUNTING.md)).
[LEAN_CLAIMS.md](LEAN_CLAIMS.md#configuration-family-capacity-and-privacy)
lists each export with its premises.

**Conditional numerical certificate (Python).** `code/` evaluates every
candidate the planner can choose at capacities `2^15..2^31` and online stash
settings `s=1,2,4`, composing exact per-job bounds with exact exposure counts.
Its results are in `code/configuration_space_*.json` and summarized in
[CONFIGURATION_SPACE.md](CONFIGURATION_SPACE.md). These ledgers are
conditional on the report's source-law and execution premises; the checker
records status `unproved_applicability` and an unconditional upper bound of
one. The Lean family covers the `s=1` standard subset of this space; the
`s=2,4` settings and pinned-tier options are covered only by the conditional
ledgers.

## How the certificate reaches the library

1. Native probes in `code/*.cpp` compile against the engine headers that
   decide job shapes and stash sizes (listed in
   [code/source_scope.py](code/source_scope.py)) and print each job's public
   shape without allocating tables.
2. `code/bound_table.py` computes one exact bound per distinct shape;
   `code/certify_configuration_space.py` composes them per candidate and
   capacity. Every artifact records the SHA-256 of the sources and inputs it
   read.
3. `code/export_certified_bounds.py` refuses stale artifacts, then writes
   [src/oram/levelarena/cpu_byteslice_level_arena_certified_bounds.inc](../../src/oram/levelarena/cpu_byteslice_level_arena_certified_bounds.inc):
   one record per gap-free candidate with its exact public shape and
   `ceil(1000 log2 bound)`.
4. [cpu_byteslice_level_arena_certification.hpp](../../src/oram/levelarena/cpu_byteslice_level_arena_certification.hpp)
   looks the resolved geometry up in that table and reports it through the
   resolved plan's `certification` field and `ByteMap<true>::certification()`:
   *certified* (a record matches and its **conditional** bound meets the
   target), *above target*, or *not covered*. The lookup never refuses a
   configuration; it only reports.

No native probe may include the generated table (it would make the table an
input of the certificates it is built from); the exporter and
`cpu_byteslice_level_arena_certification_test` both enforce this.

## What is proved and what is assumed

Proved in Lean, in the serialized reference model on ideal tapes: the per-job
capacity laws (direct level one, separated ordinary merges, top preparation,
initialization and finish), their causal composition over first failures,
exact probe simulation, API correctness, and the finite instruction semantics
of the stored-key matchers and routing-message encoding.

Assumed, and stated as explicit premises
([LEAN_CLAIMS.md, "Premises and their evidence"](LEAN_CLAIMS.md#premises-and-their-evidence)):

- **Ideal hashing.** Routing words and dummy words are independent uniform
  tapes; AES is replaced by them through the reductions in
  [ERROR_ACCOUNTING.md](ERROR_ACCOUNTING.md), whose AES advantages are not
  bounded numerically.
- **Public schedule and shape.** The rebuild schedule, which operations probe,
  and batch widths do not depend on secret data; rebuild memory traces depend
  only on public geometry (supported by the engine's instruction-census and
  protected-page tests, not proved).
- **Native correspondence.** The C++ engine executes the model: same job
  inputs, families, order and selected records, and its observation equals
  the model's view off failure. Finite differential replays
  ([lean/oracle/README.md](../../lean/oracle/README.md)) compare engine and model
  state on many runs but do not prove this.
- **Planner membership.** That every plan the native planner selects is one of
  the listed family members is checked by enumeration for the standard
  options, not proved for arbitrary inputs.
- **Lifetime budgets.** Query counts for the AES reductions, and the
  probability of a resource stop, are charged separately (see
  [ERROR_ACCOUNTING.md](ERROR_ACCOUNTING.md#outstanding-native-obligations)).

Out of scope: owner/helper thread scheduling, timing, tree/hybrid payload
execution, callback side effects, and stored-key APIs (`StoredKey`, `*Stored`)
that let a client choose stored keys.

## Level-one and top contracts

Level one deduplicates the incoming prefix, then builds B's main table
directly. Its residual occupancy is exactly `sum_i max(X_i - 64, 0)` over home
loads `X_i`, including excess spread across many homes. Digit one drains
directly into the output tier. Above digit one, one standalone 64-slot B tier
has its own producer event; A completes its route with B's region blank and
distributes all A residuals through one-page DFS leaves (very small A pools
use a direct plan with no distributor event). B production and final
insertion use the same current family, so A's coarse-range bound is evaluated
before selection against B and is never conditioned on B's success. The
insertion stash and its lane copies are at least as wide as the output tier,
so the output event dominates both.

Higher ordinary levels use the completed-A argument
([COMPLETED_A_FRONTIER.md](COMPLETED_A_FRONTIER.md)). The top is binary
(`D` a power of two): its preparation and a direct initialization distribute
through one-page DFS leaves, whose final-range event is certified only for a
binary top's population map. The top finish resolves versions and tombstones
before testing capacity and is bounded by the separated-carry and
resolved-live-set excess arguments (REPORT, "Resolve before compression and
top excess").

## Why the family stops at `2^31`

At `2^32` and `2^33` the planner's geometries have complete conditional
exposure sums above the target, dominated by top preparation and finish.
Raising the series cutoff does not help: every admissible cutoff of the
positive-series bound includes its first coefficient above the top's slot
count, and that single term already exceeds `2^-64` at both capacities.
Extending the family needs a sharper probability analysis or larger top
tiers. This is a limit of the bound, not a lower bound on actual failure, and
no artifact in this directory covers those capacities.

## Regenerate and verify

To confirm that the shipped artifacts match the current sources without
recomputing anything, run the read-only checks from the repository root:

```sh
python3 analysis/bound_certification/code/regenerate.py --dry-run   # lists the steps that would run; none means current
python3 analysis/bound_certification/code/manifest.py --check
python3 analysis/bound_certification/code/export_certified_bounds.py --check
```

`--dry-run` lists a step when any hash its artifact recorded differs from the
current tree (see [code/README.md](code/README.md#provenance)). On a fresh
checkout, `regenerate.py` and `export_certified_bounds.py` first rebuild the
gitignored shadow-loss tree caches (`code/tree_*.json`) that the artifacts
recorded: they are deterministic, take about two minutes in pure Python (or
seconds with the optional GMP accelerator below), and are then checked against
the recorded hashes like every other input. Nothing else is written.
`manifest.py --check` compares the report, docs and artifacts with
`code/SHA256SUMS.json`, and `export_certified_bounds.py --check` fails when
the planner's generated bound table is out of date or its inputs are stale.

A full regeneration needs Python 3, a C++17 compiler (`g++`, or `CXX`) on an
x86-64 host with AVX-512 (the native probes are compiled with
`-march=native` and run the engine's own planner and job-shape code), and
`pdflatex` for the report. The optional GMP accelerator for one exact
convolution is built by hand, from this directory:
`g++ -O3 -shared -fPIC code/gmp_square.cpp -lgmp -o code/libgmp_square.so`;
without it that step runs in pure Python and can take hours. Expect a full
regeneration to take hours rather than minutes:

```sh
python3 analysis/bound_certification/code/regenerate.py
```

The driver recomputes only stale artifacts (an artifact is stale when a
recorded source or input hash no longer matches), runs the regression tests,
re-exports the planner table, rebuilds the report and refreshes
`code/SHA256SUMS.json`. Report-only edits rebuild the PDF without recomputing
certificates. The equivalent manual commands, from this directory:

```sh
python3 code/build_report.py
python3 code/manifest.py
python3 code/manifest.py --check
python3 code/export_certified_bounds.py --check
```

To build and audit the Lean proofs, see [lean/README.md](../../lean/README.md).
Native regression targets in `tests/oram/` cover dense selection and drain,
complete jobs, initialization, top resolution and DFS offers, including
pauses, helpers and lanes. They validate the implementation's concrete
contracts; they do not discharge the source-distribution premises.
