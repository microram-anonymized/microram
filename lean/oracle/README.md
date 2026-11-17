# Differential-test oracle

This directory checks the trusted Lean models of `RebuildBound/Spec/Model/`
against the C++ engine in `src/oram/`. C++ dumpers run the real engine and
write JSON fixtures; `lake exe oracle` reruns each fixture's inputs through
the Lean model and compares. Agreement on finite fixtures is evidence for the
native-correspondence premises of the Lean theorems, not a proof of them.

`lake exe oracle` runs the Lean model on fixtures written by the C++ engine
and compares the two: O1 (the semantic spec, on both outputs), O2 (verdict
and failing test) and O3 (lane-exact contents). Its default mode handles two
fixture formats: `rebuild-fixture/0` (the d = 2 separated-sources merge, model
`RebuildBound.Model.job`) and `top-finish-fixture/0` (the top finish, model
`RebuildBound.Model.topJob`).

    oracle/roundtrip.sh                  # build both sides, dump, check, mutation-test
    oracle/check_fixtures.sh <dir>...    # the differential test over fixture directories

`--tp` mode (`RebuildBound/Oracle/TPDiff.lean`): the top preparation and the
initialization route, `top-prep-fixture/0` and `top-init-fixture/0` (source
dumpers and generators in [fixtures-tp/](fixtures-tp/README.md); generated
fixtures under `.lake/oracle/fixtures-tp/`, gitignored). The model is
`tpJob` (preparation) or `initJob` (initialization) under `engineRule`; O2
compares the verdict and the failure kind, O3 the lane-exact main and drain
target (`R` or the published tier). An initialization also compares the
scatter when the fixture records it: the 800 job-level fixtures report
`scatter: pass`, while the 120 public-engine fixtures omit the intermediate
observation and report `scatter: skipped`.
O1 is light (permutation of the input minus flagged tombstones, home of every
main record). Run
`ORACLE_ARGS=--tp oracle/check_fixtures.sh .lake/oracle/fixtures-tp/fx .lake/oracle/fixtures-tp/fx-engine`.
The `T = 4096` fixtures take the model several seconds each, so the whole
battery is best run in parallel: set `ORACLE_JOBS=16` (any `check_fixtures.sh`
run takes it).
The source README includes the complete regeneration commands; no cached
fixture or cached source file is needed.

Pieces:

| file | role |
| --- | --- |
| `fixture_dump.cpp` | the round trip's d = 2 dumper: runs the job on the real engine, self-checks it in C++, writes the fixture |
| `build_dumper.sh` | compiles it into `.lake/oracle-build/fixture_dump` (gitignored; skipped when up to date; `--asserts` builds with `-UNDEBUG`) |
| `roundtrip.sh` | the driver: build, dump, `lake exe oracle`, failure fixture, mutation tests |
| `check_fixtures.sh` | runs `lake exe oracle` over directories (`ORACLE_ARGS` for the mode, `ORACLE_JOBS` for parallel processes; skips the generators' `manifest.json`, `summary.json`, `results.json`) and prints the O1/O2/O3 summary; fails on a missing or empty directory |
| `top_mutations.sh` | mutation tests of the top-finish oracle: invalid and aliased coordinates, swapped, dropped and corrupted records, and out-of-range input pages must be rejected |
| `../RebuildBound/Oracle/{Fixture,Check,Diff,Main}.lean` | the d = 2 reader, the O1 checker, the model run and comparison, the `oracle` executable |
| `../RebuildBound/Oracle/TopDiff.lean` | the top finish's reader, O1 (with the `TopShape` premise check), model run and comparison |
| `../RebuildBound/Oracle/SepDiff.lean`, `TPDiff.lean` | the general-digit (`--sep`) and top-preparation (`--tp`) modes |

The ordinary oracle executable imports core `Lean`, `Std` and the model only, never Mathlib.

## Fixture batteries

Every per-job battery's source machinery (dumper, build script, generator,
Python model, comparison script) is tracked in a directory of `oracle/`,
whose README gives the complete commands to build the dumpers outside CMake,
regenerate the battery, compare it with an earlier one and check it with the
Lean oracle. Generated dumpers and fixtures go to a work directory under the
gitignored `.lake/oracle/`, overridable per battery (`ORACLE_D2_WORK`,
`ORACLE_RADIX_WORK`, `ORACLE_TOP_WORK`, `ORACLE_TP_WORK`) so that a fresh run
can be compared with an existing battery without overwriting it. No cached
source file is needed. The direct-job modes and native exporter are described
below.

| battery | sources | dumper | generator | Python model | fixtures | Lean |
| --- | --- | --- | --- | --- | --- | --- |
| d = 2 merge | [fixtures-d2/](fixtures-d2/README.md) | `fd2.cpp` (`build_fd2.sh`) | `regen_d2.py` (knobs in the file names; `names.txt`) | `model.py` | 1949 (of 1964 knob sets; 15 checked input refusals) | default mode |
| radix digits 2–8 | [fixtures-radix/](fixtures-radix/README.md) | `fd3.cpp` (`build_fd3.sh`) | `gen.py OUTDIR 500 --keep` | `model3.py` | 8592 (of 9000 knob sets; 408 harness refusals) | `--sep` |
| top finish | [fixtures-top/](fixtures-top/README.md) | `fdtop.cpp` (`build_fdtop.sh`) | `gen_top.py` (fixed seed) | `model_top.py` | 1000 | default mode |
| top preparation, initialization | [fixtures-tp/](fixtures-tp/README.md) | `fdtp.cpp`, `fdtp_engine.cpp` (`build_fdtp.sh`, `build_fdtp_engine.sh`) | `gen_tp.py`, `gen_engine_tp.py` (fixed seeds) | `model_tp.py` (`run_tp.py`, `mutate_tp.py`) | 2399 + 120 | `--tp` |

The d = 2 generator retains all 1964 knob sets: 1949 produce fixtures (1132
engine successes and 817 capacity failures), and 15 have exactly checked
carry-construction refusals before the merge job starts. Two-block CBC routing
changed the seeded filler keys; these inputs no longer fit the incoming B main.
The generator rejects any new refusal or changed known disposition. Refused
inputs are recorded separately and are not counted as Lean comparisons. See the
d = 2 README for the exact acceptance checks. The table lists the current
expected counts; each battery's checks determine whether a run passes.

Current radix generation attempts all 9000 knob sets and produces 8592 fixtures
(3902 engine successes and 4690 capacity failures). The other 408 inputs fail
construction of the incoming B source under two-block CBC routing: 401 shed
while routing and 7 overflow the carry route. Their diagnostics remain in
`results.json`; these refusals are not Lean comparisons. The Lean oracle must
compare all 8592 produced fixtures without mismatches.

The engine semantics each model follows are in
`../RebuildBound/Spec/Model/ENGINE_{D2,RADIX,TOP,TOPPREP}.md`.

**After an engine change**, rebuild every dumper (`build_dumper.sh` and the
build script of each battery directory; an API removal breaks them, and
nothing else compiles them), regenerate each battery into a new work
directory, compare it with the current one (`fixtures-d2/cmp_d2.py`,
`fixtures-radix/cmp_radix.py`, or a byte comparison for the top finish and
the top preparation), run the Python model and the Lean oracle on it as each
README says (`check_fixtures.sh`, with `ORACLE_ARGS=--sep` for the radix
battery and `--tp` for the top preparation), and run `roundtrip.sh`.

By hand:

    oracle/build_dumper.sh
    .lake/oracle-build/fixture_dump .lake/oracle/fixture_d2.json   # no argument: run + self-check only
    lake build oracle
    lake exe oracle .lake/oracle/fixture_d2.json                   # exit 0 pass / 1 fail / 2 malformed

The dumper is kept out of `tests/oram` on purpose: the top-level CMake globs
`tests/oram/*.cpp`, so a file there would enter every ctest build. It includes
the engine headers and `tests/oram/cpu_byteslice_level_arena_test_support.hpp`
read-only and touches nothing else.

## The job

The d = 2 separated-sources ordinary merge that `RunCase` in
`tests/oram/cpu_byteslice_level_arena_job_test.cpp` runs for its "binary" case
(branching 2, levels 3, level 2, digit 2, forced_older 60, forced_fresh 0, no
tombstones, no produced carry); `dfs_pages` reports the actual completed-A
leaf width from `FinishDfsPages(pool)` (1; the d = 2 and radix batteries'
dumpers write the constant 2), a field no model consumes. The dumper replicates that setup minimally (same helpers,
same call sequence, same RNG stream), then runs
`Begin; PrepareOlder; InstallCarry; FinishMerge` with the whole-phase budget.
Source A (older, source byte 1) is level 2's odd bank, with 16 records in each
of 8 buckets plus a 12-record tier; source B (fresher, source byte 2) is level
2's inbox 0 in the same shape, routed under the merge family's nonce, a third of
its keys shadowing A. The output goes to level 3's inbox 0 (16 buckets, one tier
bucket). `forced_older` keys are all homed at output bucket 0, so it overflows
and the excess is shed into the tier.

Dumper options: `--seed HEX` (the instance's AES key seed), `--forced-older N`,
`--forced-fresh N`. `--forced-older 128` overloads the tier and gives a
*failure* fixture (`fixture_d2_fail.json`): the engine throws
"the finish phase ran out of room at residual-dfs-partition".

Exit status of the dumper: 0 ran and self-check passed (a capacity failure is a
legitimate result), 1 self-check violation, 2 usage/harness error.

## Fixture schema (`rebuild-fixture/0`)

Keys, routing words, nonces, seeds and values are hex strings; everything else
is a JSON number or boolean. A record is
`{"bucket":b,"lane":l,"key":"<16 hex>","value":"<value_bytes hex>","tombstone":bool}`:
bucket capacity is 64 lanes; `value` is all `value_bytes` stored bytes, byte 0 =
source (1 = A, 2 = B) and the LAST byte the meta byte with the engine's scratch
bit `kMetaResidualClass` (0x40) cleared; `tombstone` is bit 0x80 of that byte.

```
{"format":"rebuild-fixture/0",
 "job":{"kind":"ordinary_merge","digit":2,"level":2,"separated_sources":true,
        "shape":"dfs","seed":"<AES key seed>","forced_older":60,"forced_fresh":0,
        "aes_round_keys":["<11 x 16-byte hex>"]},
 "geometry":{"bucket_capacity":64,"key_bytes":8,"value_bytes":8,"tag_bytes":4,
   "branching":2,"levels":3,"level":2,"digit":2,"odd_part":1,"power":1,
   "U":8,"K":3,"block_bits":4,"block_buckets":16,"out_buckets":16,
   "older_buckets":8,"older_tier_buckets":1,"carry_tier_buckets":1,
   "out_tier_buckets":1,"stage_stash_buckets":1,"prefix_flushes":2,
   "stash_buckets":1,"routed_prefix_buckets":4,
   "pool_swept_buckets":..,"pool_main_levels":..,"pool_fused":..,
   "pool_direct_buckets":..,"range_bits":..,"range_index_bits":..,
   "range_groups":..,"range_buckets":..,"range_scatter_per_bucket":..,
   "separated_sources":1,"dfs_pages":1,"max_accesses_log2":32},
 "families":{"merge":{"level":3,"ordinal":1,"nonce_lo":"..","nonce_hi":".."}},
 "inputs":{"A_main":[rec..],"A_tier":[rec..],"B_main":[rec..],"B_tier":[rec..]},
 "words":[{"family":"merge","key":"..","word":".."}, ...],   // one per key of A u B
 "outputs":{"verdict":"success"|"failure","message":"..",
            "main":[rec..],"tier":[rec..]}}
```

`word` is `crypto::AesCtrTagU128WordsHost(nonce_lo, nonce_hi, key, 0, rk)`: the
low 64 bits of the merge family's PRF. For d = 2 the index map is the identity,
so a key's home is `word & (out_buckets - 1)`. The dumper recomputes the home
of every key both ways (this word, and the test's own
`ComputeRoutingTags`-based `DestinationBuckets`) and refuses to write a fixture
where they differ. The Lean side reads `words` as trusted input (it does not
implement AES); `aes_round_keys` is informational.
`verdict:"failure"` fixtures carry empty `main` / `tier`.
The Lean side reads only the geometry fields it uses (`bucket_capacity`,
`key_bytes`, `value_bytes`, `U`, `K`, `block_bits`, `out_buckets`,
`older_buckets`, `older_tier_buckets`, `carry_tier_buckets`, `out_tier_buckets`,
`stage_stash_buckets`); the others are informational and may be extended.

## O1-only check of a d = 2 fixture (`--phase0`)

1. conservation: output main + tier hold exactly one record per key of
   `A_main u A_tier u B_main u B_tier`, the newest version (B beats A) with
   identical value bytes and tombstone flag (tombstones are live records);
2. placement: every output main record is in bucket
   `word(merge,key) & (out_buckets-1)`;
3. counts: with `X_v` the winners homed at `v`, main bucket `v` holds
   `min(X_v,64)` records, the tier holds `sum_v (X_v-64)+`, and each tier
   record names a home with `X_v >= 64` and a full main bucket;
4. input structure: positions in range and distinct, at most 64 records per
   bucket, key/value widths, A's keys distinct across A_main u A_tier, B's
   across B_main u B_tier; geometry consistency (`out_buckets` a power of two,
   `U = 2^K`, ...).

One line of JSON on stdout: `{"o1":"pass","records":N,"homes":16,"tier":T,...}`,
`{"o1":"fail","violation_count":n,"violations":[..first 20..]}` (exit 1),
`{"o1":"malformed","error":..}` (exit 2), or, for an engine `failure` fixture,
`{"o1":"skipped","engine":"failure","message":..}` (exit 0; only check 4 runs.
O1 does not apply to a failure; the default mode below compares the model's
verdict instead).

## Mutation tests (in `roundtrip.sh`)

Copies of the real fixture, each of which must be rejected: (a) move a main
record to another bucket, (b) delete a tier record, (c) replace a winner's value
by its losing A version; plus extras (flip a tombstone, flip a routing word,
duplicate an output record, repeat a B key in the input, move a tier record into
main), an unmodified control that must pass, and a truncated file that must be
malformed (exit 2).

## Differential mode (model vs engine, the default)

`lake exe oracle <fixture.json>...` runs the model and compares it with the
engine: O2 verdict (and failing-test kind; for a DFS failure not the node,
since the models' DFS traces are abstract, see `Job.lean`), O3 lane-exact
main and tier, O1 on the engine's and on the model's output. One JSON line
per fixture; `--phase0`
keeps the O1-only mode for d = 2 fixtures. A d = 2 fixture runs
`RebuildBound.Model.job engineRule` (`RebuildBound/Oracle/Diff.lean`). A
top-finish fixture runs `RebuildBound.Model.topJob` with the engine's
unshadowed flag, bit `0x20` of the value's meta byte
(`RebuildBound/Oracle/TopDiff.lean`). Its O1 applies only when the inputs meet
`TopShape`: fixtures that break it on purpose report `"o1":"premise"` with the
broken clauses, and are still compared by O2 and O3. Every coordinate of a top
fixture is checked against its store (in range, no position used twice) before
it is compared: an input fault makes the input malformed, an output fault fails
O3 and O1, and the tier is compared by (page, lane). `oracle/check_fixtures.sh <dir>...` runs it over directories and prints
the summary. Geometry choices: pool = (`pool_swept_buckets` -
`pool_direct_buckets`)*C slots, leaf capacity C, stage/insertion stash
`stage_stash_buckets`*C, output tier `out_tier_buckets`*C.

## Direct-job reference (`--direct`)

`lake exe oracle --direct <fixture.json>...` runs the complete scalar digit-one
reference against original-input fixtures. See [DIRECT_JOB_SCHEMA.md](DIRECT_JOB_SCHEMA.md)
for the schema and `python3 oracle/direct_job_tests.py` for the independent
expected-result and mutation suite. This mode provides reference regression
evidence; native direct-job export is available through the native format below.
This mode covers the scalar digit-one job; it rejects a whole job at a later digit
with the status `requiresLaterPhases`. Digits 2–8 are covered by `--direct-a` below
and `--direct-finish`.

`lake exe oracle --direct-a <fixture.json>...` runs A preparation and operational
direct/DFS distribution at digits 2–8. It compares analytical full lanes, ordered
sheds, B-tier freshness filtering, leaves, check traces and bounded phase failure
priority. Success is `phases-completed`, with no publication. The shared schema
also documents this mode; `python3 oracle/direct_job_a_tests.py` runs its 125
independent reference regressions. These fixtures do not establish native phase correspondence.

`lake exe oracle --direct-finish <fixture.json>...` runs the complete bounded
reference at digits 1–8 and compares lane-preserving publication or the first
logical failure. It also recomputes analytical insertion, ordered offers, ranked
leftovers, drain lanes and their checks after earlier failures. Run
`python3 oracle/direct_job_finish_tests.py` for independent original-input
regressions and expected-result mutations. Successful cases are also checked
against a separate newest-full-record union, placement, saturation and exact
excess. Formal finish correctness and all-digit publication correctness are
proved separately in the `DirectJobFinishCorrectness`/`DirectJobPublication`
packages. Native differential fixtures are supplied separately by the exporter below. The `--direct`
mode is the digit-one API and rejects later phases.

`DirectJobFailure` proves whole-job analytical/bounded agreement and
unconditional deterministic failure containment. The `--direct-finish` mode
also compares the analytical job's first failure or successful output with
the fixture's independently expected bounded result, including after earlier
phase overflow. JSON reports include `analytical_result`; fixture inputs are
unchanged. `DirectJobExposure` separately proves ordered routing transcript
noninterference. Shared probability adapters are implemented; native
correspondence and probability-law applicability are not established here.


Native direct-job observations use the same `--direct-finish` mode through
`direct-job-native/0`. `direct_native_dump.cpp` exports original inputs and AES
routing words from the real `LevelMergeJob`, exact full publication lanes,
successful A/B phase boundaries and normalized failure classes.
`python3 oracle/direct_native_tests.py --keep .lake/oracle/direct-native`
compiles the assertions-enabled exporter and runs the selected K=4 digits 1–8,
capacity controls and mutations. See the native section of
[DIRECT_JOB_SCHEMA.md](DIRECT_JOB_SCHEMA.md) for complete payload encoding and
the deliberate phase/check-class failure projection. The reference recomputes
its answer from original inputs; native snapshots never define its states.
Finite differential evidence does not discharge universal native correspondence,
exact logical failure identity, resume/progress or probability applicability.


The whole-job `--direct-finish` checks also execute `DirectJobResume` with
segmented fuel (including a zero-fuel pause) and report `resumed_result`.
Reference fixtures require exact equality with the independently expected
bounded result. Native fixtures require full equality with the atomic reference
before native failure-class normalization. Fuel uses analytical trace length
plus phase-boundary slack solely as a regression allowance; this does not
establish native interruption or timing behavior.

## Hierarchy replay (`--hierarchy`)

The native identification of the hierarchy model (the model runs jobs
serialised in dependency order; the engine pauses and interleaves them, so
their identification is checked here rather than proved): the real public
engine runs a whole access trace, and the oracle rebuilds the same run from the
trusted `RebuildBound.Model.Hierarchy` and compares every published table lane
by lane, plus the first capacity failure. It also checks the theorems'
premises on the observed trace: `TracePremises` (distinct keys per unit, the
per-ordinal load, keys and initialization keys below `N = config.key_bound`)
and `UnshPromise` at every evaluated top finish, exactly at the run's words
and in a word-independent sufficient form, with counts of the flagged
tombstones examined. Schema, identification rule, failure rules and the
premise report: [HIERARCHY_REPLAY_SCHEMA.md](HIERARCHY_REPLAY_SCHEMA.md).

*The adversary's view* (`--view`, `OnlineDiff.lean`; schema section "The
adversary's view"): on every small scalar fixture the dumper also records, per
access, the probe plan's hashed tables, the bucket the engine touched in each,
whether that probe was real and the dummy word, all read from the engine (its
composed plan at the access's reader-epoch pause point, its probe scratch, its
dummy counter and the probe audit), for the arena and the synchronous engine;
the oracle compares them with the trusted online model's `touched` and
`isReal` (`RebuildBound.Model.Online`) on the run rebuilt from the fixture, and
checks that `traceOf` reproduces the captured units, the schedule premises on
the recorded plans, `OnlineFresh`'s one real probe per (family, key), and the
synchronous plans against `syncSchedule`.

*The batch path* (`--view` with `--batch`, `OnlineBatchDiff.lean`; schema
section "The batch path"): on every batch fixture (`k_batch_*`) the dumper
records the view of every `AccessBatch` lane, engine chunk by engine chunk: the
chunk's composed plan (one reader epoch per chunk, checked), and per lane and
hashed main the touched bucket, the real flag and the dummy word, read from the
batch tiles' probe scratch, found bits and dedup and from a shadow of the
cascade on the engine's own data (its address pass, matcher and plan storage),
checked against the engine's scratch, found bits, dedup, audit counts and sets;
both the chunked (`RunBatchChunk`) and the parallel-tile (`RunBatchJob`,
`--batch-tiles`, `--batch-bucket-scan`) shapes. The oracle rebuilds the
`BatchRun` (a recorded chunk is one `.batch` operation, the slots between
calls scalar operations) and compares with the trusted batch model's `touched`
and `isReal` (`RebuildBound.Model.OnlineBatch`), with the same checks over
slots (`syncSchedule` at each operation's first slot) and `chunks` (the
recorded chunks are the fixture's `AccessBatch` operations, one plan per
chunk, no `write_np` lane, both engines cut the same chunks). On a scalar view
it also runs the batch model (`online_batch`, `BatchScalar`), which must agree.

The [committed replay summary](hierarchy_battery_summary.txt) records a run
at the preceding artifact commit: 64 runs, 6,993 compared tables and
5,298,876 probes, with no mismatch and all 89 mutation checks passing
(including 54 vacuity probes). Fresh fixtures were generated serially at
that same clean commit before the recorded four-worker `--no-generate`
replay. Its timing excludes fixture generation. The summary's commit line
identifies the source tree used.

    python3 -I oracle/hierarchy_replay_tests.py -j 16    # build, generate, compare, mutate (~10 min)
    python3 -I oracle/hierarchy_replay_tests.py -j 16 --summary .lake/oracle/hierarchy-summary.txt
    python3 -I oracle/hierarchy_replay_tests.py --no-selected  # 60 runs; ignores stale selected JSON
    python3 -I oracle/test_hierarchy_manifest.py        # fast inventory/CLI regressions
    oracle/build_hierarchy_dump.sh [--asserts]           # .lake/oracle-build/hierarchy_dump
    oracle/gen_hierarchy_fixtures.sh                     # the battery into .lake/oracle/hierarchy/
    lake exe oracle --hierarchy F.json...                # with the view replay when F has a view (batch model for a batch view)
    lake exe oracle --online F.json...                   # the view replay alone
    lake env lean --run spec_tests/HierarchyReplayShapes.lean .lake/oracle/hierarchy/j_selected_uniform.json

| file | role |
| --- | --- |
| `hierarchy_dump.cpp` | drives a `LevelArenaEngine` (inline executor, `kHandOver` or with `--policy auto` the engine's default `kAuto`, which resolves to `kShare`; a fixed secret unless `--secret` is given) on a seeded trace; captures each dense prefix before level one consumes it, every table at every publication (pause hook `kAfterPlanInstall`, read only), the engine's per-job shapes and the AES words; names the failing job; self-checks families, windows, homes, prefix immutability, and (`--sync-check`) equality with the synchronous engine; with `--view` the adversary's view (compiled with the probe audit; the engine headers are included with `private` spelled `public` to read the probe scratch, the dummy counter and the audit's sets, no engine edit), self-checked against the audit's counts and sets, `LastProbeTables`/`LastProbeBuckets`, the dummy counter's advance and the AES words; with `--batch` the view per chunk and lane (the tiles' scratch against a shadow cascade on the engine's own data; `--batch-vary`, `--batch-scalar`, `--batch-lanes`, `--batch-tiles`, `--batch-bucket-scan` shape the calls and chunks) |
| `hierarchy_fixture_manifest.py` | the single source of fixture names, dumper arguments, expected failures and the five required two-secret pairs; used by both generator and replay driver |
| `gen_hierarchy_fixtures.sh` | builds the dumper and runs the manifest battery: 64 runs (35 small scalar, 15 batch `k_batch_*`, both selected configurations scalar and batch `j_selected_*`, five two-secret pairs `s2_*_a/_b`) over B, L, D, r0, s, per-level fanouts, D = 1, initialization, value widths, eager and lazy drive, the engine's default inline policy (`--policy auto`, `kShare`), forced failures at level one, a separated level, the top preparation and finish, the unshadowed promise (`u_*`: forced erases and reads of fresh keys and erases of keys written earlier, overflowing a top carry's bucket into its tier; erase- and read-heavy traces), and the batch path (`k_batch_*`: fanouts 2/4/8, both drives, chunk widths 5 to 64, the parallel-tile shape with and without the bucket scan, repeated keys inside chunks, calls spanning unit and prefix ends (internal chunks end at unit boundaries), scalar operations between calls, initialized, forced tiers, the unshadowed promise, a forced level-one failure). Every run records both engines' views (`--sync-check --view`); `-j N` runs the dumpers in parallel. The forced top overflows (`i_force_top*`, `i_force_topfinish`, `n_tiers_*`, `k_batch_tiers_*`, 9 runs) use keys past `N = 32 T` and fail `trace_premises.keys` by construction, as the driver expects |
| `../RebuildBound/Oracle/HierarchyDiff.lean` | the reader and the memoised evaluation: tables in serialised order through the model's `base` and `step` (`table_eq`, `Env.evalTable_sound`); job results through the model's functions on memo tables (`levelOneResultOf_eq` … `ordinaryFailsOf_eq`); level one's producer through `buildBFast`, proved equal to the trusted `buildB` (the trusted definition recomputes the prefix winners per index and takes minutes per ordinal); the premises: `tracePremises` (each conjunct decided literally), the promise's exact instance `unshInstance` on `finishInputsOf` (`finishInputsOf_eq`, `unshInstance_iff`, `unshInstance_model`) and the sufficient form (`UnshSufficient.instance`) |
| `../RebuildBound/Oracle/OnlineBatchDiff.lean` | the batch view replay: the run (`BatchRun`: recorded chunks as `.batch` operations), the schedule by slot, read through the trusted `slots`, `widths`, `slotSchedule` and `chunkStart`; the requester state advanced per operation (`stateAt_succ`), the duplicate test on the slot's operation (`duplicateWith_eq`), key sets on `traceOf` (`keySet_table`, `traceWith_eq`), and `isRealB_eq`, `touchedB_eq` lifting them to the trusted `isReal` and `touched`; the chunk checks; the combined `--hierarchy` line (`runCombined`) |
| `../RebuildBound/Oracle/OnlineDiff.lean` | the view replay: the run (`OnlineRun`, records from the captured units), the schedule (the recorded plans), the words and dummy words from the fixture; the requester state advanced per operation (`stateAt_succ`), key sets from the memoised tables on `traceOf` (`keySet_table`, `traceWith_eq`), and `isRealWith_eq`, `touchedWith_eq` lifting them to the trusted `isReal` and `touched`; the schedule premises decided field by field (`tilesB_iff`) |
| `../spec_tests/HierarchyReplayShapes.lean` | at a selected configuration, the engine's config and every job shape equal the theorem's `hierarchyShapes cfg rows` |
| `hierarchy_replay_tests.py` | the driver, the forced-failure expectations, the trace premises recomputed independently (a fixture passes when the oracle's failure reasons are exactly those, and keys past `N` are forced ones), the battery's unshadowed-promise totals (fails if the exact form is vacuous), and the mutations, each with the failure reasons it must report (tables; nodup, load, keys, init_nodup; an unshadowed bit set on a carry tombstone that shadows a live older copy, in the tier and in the main; the view: a touched bucket, a real flag, a dummy word, a plan entry dropped or reordered, a synchronous plan's consumption mark, an operation's kind, a unit record's lane; the batch view: a lane's touched bucket, a duplicate lane claimed real, a duplicate lane's dummy word, a lane recording another plan than its chunk, a chunk's plan with an entry dropped, a synchronous chunk's consumption mark, a chunk record removed, a chunk lane turned into `write_np`, a superseded lane given a record in a captured frozen unit), and the BatchScalar cross-check on every scalar view; fail closed: the oracle's `evidence.*` checks and the driver's own (compared = tables − skipped top tables, `checks.failures` empty, `init_shape_differs` agrees with the emitted shapes, both views complete), vacuity probes (gutted fixtures and false selected labels) that must be rejected, and the two-secret comparison (identical plan schedules, counters, real/dummy patterns, units, outcome and table record sets under two secrets, with different words and touched buckets); writes `.lake/oracle/hierarchy-report.json` |
| `hierarchy_battery_summary.py` | writes a plain-text summary of that report (`--summary FILE`) |

The driver requires every fixture and secret pair in the manifest; missing or
unexpected JSON files fail before replay. `--no-selected` expects exactly the
60 non-selected cases, skips selected-only mutations and shape runs, and never
reads leftover selected fixtures. The report lists any such ignored filenames.

A selected label is validated before it can exempt top evidence: it must name
`uniform` or `half`, match the configuration and native geometry, and match all
direct, separated, top, preparation and initialization shapes. The executable
uses core-only snapshots in `Oracle/SelectedShapes.lean`; the default SpecTests
build checks their exact equality to the canonical Spec definitions in
`spec_tests/SelectedReplay.lean`, and exercises both selected configurations
with scalar and batch metadata. The mutation battery also rejects unknown and
falsely applied labels through both hierarchy and online replay entry points.

Selected-configuration fixtures (`T = 2^22`) skip the top's table contents and
compare every table below it (levels 1–3 at uniform, 1–4 at half-fanout in
70,000 accesses); their view replay compares every plan entry, the top's
included, without evaluating the top (each plan's top entry is its last). The
dumper needs about 15 GB there. Missing evidence is an error
([schema](HIERARCHY_REPLAY_SCHEMA.md), "Completeness"). `--summary` writes
the counts of a run. Finite differential evidence: it does not establish the identification for every
trace.

What of the evaluator is proved: the per-step equations (`table_eq`,
`levelOneResultOf_eq` … `ordinaryFailsOf_eq`, `finishInputsOf_eq`,
`buildBFast_eq`, the view's `isRealWith_eq`, `touchedWith_eq`,
`isRealB_eq`, `touchedB_eq` and their helpers) and the soundness of each memo
entry (`Env.evalTable_sound`). What is argued, not proved: the loop
invariants of `evaluate` and `checkView` (that the memo holds the right
entries when each step reads them), that `tracePremises` decides
`TracePremises`, and that each native table is compared with the right memo
entry. So the replay is not a Lean proof that the evaluator computes the
trusted `table` and job results; it computes them by proved steps glued by
unverified loop code.

## Current geometry and public API replay

`current_api_tests.py` adds native runs of the capacity-`2^31` configuration
and the public `ByteMap::Access` callbacks and `access_batch` API. Run from
this Lean directory:

```sh
python3 oracle/current_api_tests.py --small-only  # four small API runs
python3 oracle/current_api_tests.py             # includes three full geometry31 allocations
```

The full run needs roughly 120 GiB RAM per native geometry31 engine; the
script generates at most two simultaneously (`-j 1` makes this sequential).
It rebuilds both native exporters and the Lean oracle, generates seven runs,
checks state and responses, then rejects corrupted evidence. Results and
source hashes, and a `summary.json` of the counts, are written to
`.lake/oracle/current-api/`. `--no-build` and
`--no-generate` are intended for replaying freshly generated local evidence.

The geometry31 scalar and batch runs each execute 70,000 accesses. They
compare all published tables below the top (reaching levels 1–4), plus probe
plans and addresses. `SelectedReplay.lean` checks that the exported geometry
and job-shape constants equal the canonical capacity-`2^31` Spec constants,
including the distinct initialization/preparation drain counts (3 versus 4).

Unlike the selected-configuration runs of the hierarchy replay, these runs
also compare top contents.
The exporter scans **all** `2^26` native main occupancy masks and all tier
lanes at empty publication, initialized publication, and the end. Only empty
main buckets are omitted from the JSON. `PublicApiDiff.lean` computes expected
occupied buckets and lane positions using the model's split operation. This
restricted sparse evaluator accepts 1–32 initialization records and no top
replacement. `PublicApiReplay.lean` checks its agreement with the original
dense initializer on 112 smaller cases. There is no general proof of the
sparse evaluator, and these runs do not exercise a geometry31 top rebuild,
large initialization, or top overflow.

The public API runs use batch widths 1, 5, 16, and 64 on small configurations
and width 5 on geometry31. Original calls independently drive the existing
`Api`, `ApiAccess`, `PublicApi`, and `Requester` models. Checks cover callback
input/presence, invocation count, return/exception behavior, renames to the
same/occupied/new key, batch output/presence, mixed blind/probing operations,
exchange insertion policies, duplicate keys, and width/unit boundaries.
After **every public call**, native current-unit and partial-prefix contents
are compared lane by lane; completed units and published tables are also
compared. Reader-epoch chunk boundaries are observed from the native engine.
The exporter records normalized primitive descriptors for comparison with
the model's lowering. Internal groups also end at the next requester-unit
boundary; the oracle derives this limit from the unit size and public
primitive position, including positions consumed by suppressed lanes. This coverage uses one-byte payloads, 64-bit keys, the
inline executor, and stops before top replacement.

Use `oracle --api FILE` or `oracle --geometry31 FILE`; `--hierarchy` also
automatically performs these additional checks when their metadata is
present. Sparse-top success is reported separately under
`extension.exact_sparse_top_snapshots`: the `skipped_top` counter
counts tops omitted by the *dense* evaluator. These are finite state
comparisons, not a universal proof of native/model correspondence. Logical
records and occupancy are compared, with scratch bit `0x40` removed; unused
lane bytes and cached tag bytes are not compared as raw memory.

## Complete top rebuilds and full initialization

The geometry31 runs above stop before a top rebuild. For complete rebuild
coverage (21 runs, 52 top rebuilds, about a thousand table comparisons, and
eight corruptions that must be rejected; one run has only the expected
numeric-premise failure described below), run:

```sh
python3 oracle/complete_cycle_tests.py
```

This suite uses 4-byte keys and 4-byte payloads. Eight hierarchy cases use
32,768-entry configurations with fanouts `[4,8]` or `[4,4,2]`, empty or fully
initialized starts, and scalar or batch access. Each executes 8,320 accesses:
two complete top carries (4,096 accesses each), then another prefix. The
recorder and driver require the two top publications and complete contents
for every table; the **original dense Lean hierarchy evaluator** checks them,
with no sparse top evaluator and no skipped tables. Both arena and synchronous
probe views are also checked.

Eight further hierarchy cases use two levels with fanouts `[2]`, at `r0=2`
(capacity 2,048) or `r0=4` (capacity 4,096). Each combines an empty/full start
with scalar/batch access. Their 640/1,280 accesses cover two top rebuilds plus
one prefix. Names include `hierarchy-2-r2` or `hierarchy-2-r4`; the same full
table, view and schedule checks apply. `spec_tests/HierarchyGeometry.lean`
can also compare the scalar fixtures against the checked Lean pilot shapes.

Four public API cases use 4,096-entry configurations with fanouts `[4,2]`,
empty or full initialization, and widths 5/64. Their 896 calls per run execute
2,544/7,264 primitives and finish two/seven top rebuilds. For these cases the
native engine hands over flushed prefixes and drains after each public call.
The two-prefix queue accommodates the largest call. The API oracle checks the
observed top ordinal against the access count and discards consumed-prefix
tombstones from its independently generated history after each top rebuild:
retain its latest live winners, then append the unconsumed suffix. Complete
top tables are independently checked by the dense hierarchy replay. The
small API cases of the previous section keep the inline-share schedule and
stop before a top rebuild.

A separate case fully initializes 32,768 entries using **only nonzero keys,
1 through 32,768**, then completes two top rebuilds. The library accepts this;
capacity bounds the record count, not the numeric key value. The harness's
default generator samples `1 .. key_bound-1`, with `key_bound` equal to
capacity, which leaves only capacity-minus-one keys. `--sequential-keys` adds zero-inclusive coverage, but zero is not necessary
for full initialization: the nonzero case uses `--key-bound 32769` instead.

For that nonzero case, the oracle's numeric premise `key_bound <= capacity`
is deliberately false. The driver requires **exactly** `trace_premises.N` to
fail and every state/view comparison to pass; it does not silently waive a
state mismatch or claim the numeric-key theorem applies. The remaining
cases require the entire oracle report to pass. This distinction is recorded
per run in the `summary.json` that the script writes, with the reports, source
hashes and eight corruption checks, under `.lake/oracle/complete-cycle/`. These are smaller complete-cycle tests, not
an assertion that geometry31's top rebuild has been replayed.

## Wide-key fallback replay

`fallback_wide_tests.py` builds on the ordinary byte-key hierarchy/API/view
oracle. The native recorders accept `--K 9` through `--K 64` in addition to
the ordinary widths 4 and 8. Keys are supplied to the native byte API at
that actual width. The recorder reads the complete stored key from every
occupied lane and rejects unknown stored bytes or an ambiguous codec.

Wide native fixtures use trace IDs only as serialization handles. **Run them
through `fallback_wide_tests.py`; do not interpret those IDs as logical keys.**
Raw exports use `hierarchy-replay-wide/1`, which the ordinary oracle
rejects until the verified decoder produces `hierarchy-replay/0`. The driver
also accepts raw exports without the `hierarchy-replay-wide/1` guard.
The driver checks every exported normalization independently using
`/usr/bin/openssl`: verbatim bytes below width 16, the labeled AES permutation
at 16, and length-prefixed CBC-MAC above 16. It checks a lossless finite codec
and rewrites every logical key with the exact length-sensitive
`LogicalKey.toNat` encoding before running Lean. Shared low stored words at
widths 9–15 and shared 16-byte user prefixes above width 16 are required in the
corpus; the all-zero key is included.

The ordinary oracle's numeric-universe check cannot hold for those byte
encodings. Following the nonzero-key complete-cycle convention, the driver
requires **exactly** `trace_premises.N` to fail, while every table, API, view,
capacity/failure and other premise/evidence check passes. Every wide-key top
table is compared. This does not establish the numeric-key theorem's premise.

From the Lean directory, with a fresh output directory (the driver refuses
an existing output directory so a failed rerun cannot leave a stale success
summary):

```sh
campaign="$PWD/.lake/oracle/fallback-wide-new"
mkdir -p "$campaign/bin"
ORACLE_BUILD="$campaign/bin" oracle/build_hierarchy_dump.sh
ORACLE_BUILD="$campaign/bin" oracle/build_api_dump.sh
lake build oracle spec_tests.PublicApiReplay RebuildBound.Spec.NativeMatch.Api
cp .lake/build/bin/oracle "$campaign/bin/oracle"
python3 oracle/fallback_wide_tests.py --core-only --hours 6 -j 4 --bin "$campaign/bin" --out "$campaign/full"
python3 oracle/fallback_dispatch_tests.py --hours 2 --campaign "$campaign/full"
```

Both native build scripts disable VP2INTERSECT unless `ORACLE_VP2INTERSECT=1`
is set, which leaves the choice to `-march=native`. The first driver
has 148 core cases selected by `--core-only`: every width 9–64, boundary-width API cycles at two batch
widths, empty/full scalar/batch hierarchy cycles at capacity 32,768, and
alternate-secret API cases. Omitting `--core-only` adds six supplemental full-initialization cases covering
capacities 65,536, 131,072 and 262,144 with 17-byte scalar and 64-byte batch
keys. `--quick` selects 12 smaller cases. Fifteen mutations check full high key
bytes, normalization, callback evidence, current units, rebuilt tops and
retirement. Initialization uniqueness uses the existing quadratic oracle
check, so the largest cases can be expensive.

`fallback_dispatch_tests.py` separately runs
`WideFallbackReference.lean`, importing the current
`RebuildBound.Spec.NativeMatch.Api`. The runner uses the actual
`NativeMatchDispatch.requesterStep` with VP2 disabled: exact stored-key scalar
clear, fallback batch clear and full stored-key supersession. Original public
inputs independently drive API lowering and history; native current/frozen
states and API responses are compared. Eight corrupted fixtures must fail.
The ordinary executable retains its Core/Std-only imports and default
`Requester.run`; only the standalone additional runner imports the extended
model. This is not execution of the complete `NativeMatchCoded` experiment.

Each campaign retains immutable binaries, a source archive and manifest,
native commands/logs, per-case reports and verified compressed native/decoded
fixtures. Sources and binaries must remain unchanged during a run. A successful
`summary.json` is written only after every planned case and final gate passes;
`status.json` preserves completed cases if a deadline or another error stops
it. Do not treat an incomplete campaign as all-pass. Without
`ORACLE_VP2INTERSECT=1` this replay does not execute VP2INTERSECT; in no
configuration does it prove compiled refinement, establish cryptographic
security, or perform a geometry31 top rebuild.

### With VP2INTERSECT

`ORACLE_VP2INTERSECT=1` builds both recorders with VP2INTERSECT on a host that
has it; `fallback_wide_tests.py` then records the instruction-site count in
its summary. `fallback_dispatch_tests.py --vp2` runs the requester replay with
the production dense branch (`batchCross` enabled) on every batch page at
stored width 16, the approximate half match, which must still agree with
native; narrower stored keys stay exact, as natively. The core corpus never
reaches the native dense cross-match gate (>= 16 dense buckets in a plan), so
exercising it needs additional lazy-drive `r0 = 8` runs, which the scripted
corpus does not include; counting executed VP2INTERSECT instructions per
kernel (for example under gdb) confirms that the branch ran.
