# Hierarchy replay fixtures (`hierarchy-replay/0`)

The native identification of the hierarchy model (which runs jobs serialised
in dependency order, while the engine pauses and interleaves them): the real
public engine
runs a whole access trace, and the Lean oracle rebuilds the same run from the
trusted model `RebuildBound.Model.Hierarchy` (`table`, `step`, the bounded
`*Result` functions) and compares every table the engine published, lane by
lane, and the first capacity failure.

The fixture's probed `Write` operation calls the public `ReadThenWrite`; its
`WriteWithoutProbe` operation calls the alias of the public default `Write`.

    oracle/build_hierarchy_dump.sh [--asserts]      # .lake/oracle-build/hierarchy_dump
    .lake/oracle-build/hierarchy_dump OUT.json [options]   # CLI: header of hierarchy_dump.cpp
    oracle/gen_hierarchy_fixtures.sh [--no-selected] [-j N] # the battery, .lake/oracle/hierarchy/
    lake exe oracle --hierarchy OUT.json...
    python3 oracle/hierarchy_replay_tests.py        # battery + mutations + two-secret pairs
    python3 oracle/hierarchy_battery_summary.py REPORT.json OUT.txt   # a plain-text summary of a report

## What the dumper does

1. Builds a `LevelArenaEngine` (8-byte keys, user value width `V`, inline executor,
   no owner threads, `FlushPolicy::kHandOver`, fixed secret seed (`--secret`),
   the requested geometry and `max_accesses`; optionally `Initialize` with an
   input list). `--policy auto` builds it with the engine's default
   `FlushPolicy::kAuto`, which the inline executor resolves to `kShare` (one
   budgeted rebuild share after every flush); with `--drive lazy` this is the
   engine's default inline behaviour exactly.
2. Runs a seeded random operation sequence (`Write`, `Read`, `Erase`,
   `WriteWithoutProbe`, optionally `AccessBatch`) over a key universe, plus
   optional *forced* keys whose word under a chosen family coordinate homes to
   one bucket (to provoke capacity failures at a chosen job). A forced
   key set can be issued as erases or reads (`--force L:V:C:F:OP[:LAST]`, OP
   `w`/`e`/`r`, over level-one ordinals `F..LAST`) and issued again with
   another op (`--force-again I:OP:F[:LAST]`), so that forced tombstones
   overflow a top carry's bucket into its tier (forcing at level `L - 1`,
   ordinal `v b_(L-1)`, homes to bucket 0 of the carry top finish `v`
   consumes; `32 D` keys below `N` home there). Forced keys are searched
   upward from 1 and pass `N = 32 T` when they must (every forced top
   overflow does).
3. After every access that completes a dense prefix `p`, reads the prefix with
   `dense().PrefixView(p)` **before** any rebuild step runs, records it as the
   units of level-one ordinal `p + 1`, then drives the executor with
   `StepOnce()` until it stops (`--drive eager`, the default). *Snapshots
   (changed from the first draft):* `publisher().LiveTables()` is read at
   **every publication**, through the engine's deterministic pause point
   `ArenaPause::kAfterPlanInstall` (compiled in by the dumper; the hook only
   reads), as well as after construction, after `Initialize` and after every
   step. Snapshots between steps alone miss tables: one inline sweep steps
   levels `1..L` in order, so a level-`ℓ` forward is published and consumed by
   level `ℓ + 1` inside one `StepOnce()` (at `B = 2, L = 2` every second
   level-one table). Every table id seen is recorded once, with its contents
   read at first sight; adoption keeps the table id, so an adopted carry is one
   record. `--drive lazy` never steps: the requester runs rebuild shares only
   under backpressure (paused phases, deadline order); the prefix is still
   read when its access completes it, before any share can consume it.
   Prefixes are also captured from the publication hooks (after the
   seed): under `--policy auto` the flush that completes a prefix runs a share
   inside the access, which can consume the prefix and publish level one's
   table before the access returns; the hook reads the prefix first
   (`kBeforePlanInstall`).
4. Stops at the requested access count or at the first exception (a capacity
   failure latches the engine). Records the outcome.
5. Emits the ideal words: for every terminal family coordinate
   `CanonicalFamily(ℓ, v)` with `s_ℓ < v ≤ ⌊t / P(ℓ)⌋ + 1` (`t` the last
   complete level-one ordinal, `P(ℓ) = b_1 ⋯ b_(ℓ-1)`), plus level one's
   `CanonicalFamily(1, s_1)` and the top's `(L, s_L)`, and every key that
   appears anywhere in the run (units, init input, ops, tables),
   `AesCtrTagU128WordsHost(nonce.real_lo, nonce.real_hi, key, 0, round_keys)`
   with `nonce = FamilyNonce(Family{ℓ, v})`. From an empty start `s_1 = 0` and
   the model's `familyOf 1 0 = (L, 0)`: the family `(L, 0)` is emitted with the
   engine's empty-top nonce `EmptyTopNonce(L)` (`real_lo = L`, `real_hi = 0`);
   no job routes under it (digit one has no A).

Self-checks in the dumper (exit 1 on violation; the fixture is still written
and `checks.failures` says why): every published table's `family` equals
`CanonicalFamily(g, ℓ, v)` of the coordinate the identification rule below
assigns, its window and main size are that coordinate's, and its tier is
`TierBucketsOf(ℓ)` pages; no recorded table changes contents (or descriptor)
while live; every main record of every table sits at its home under the
emitted words (`home_checks`); every captured prefix is unchanged until it is
reclaimed, and level one's publication of ordinal `v` holds the prefix's
newest version of every key (byte-exact, `level_one_checks`); the initialized
top holds exactly the init records, as emitted; with `--sync-check`, a
synchronous engine with the same secret runs the trace in lockstep and every
live table, matched by (window, family), has the same occupied entries after
every drained prefix and at the end (lazy drive: the end only, the
unshadowed bit masked, see below). Harness errors exit 2.

## Schema

Numbers are JSON numbers (keys and words are below `2^64`; a value is below
`2^(8 value_bytes)`, which exceeds `2^64` at user width 8; Lean reads them as
`Nat`). `config.value_bytes` is the **stored** width
`user_value_bytes + 1` (`LevelArenaStoredLayout` appends the meta byte); the
user width is `config.user_value_bytes`. A record is
`{"key":K,"value":V,"tombstone":B}`: `key` the 8 key bytes little-endian;
`value` all `value_bytes` stored value bytes little-endian, the **last** byte
the meta byte with the scratch bit `kMetaResidualClass` (0x40) cleared;
`tombstone` bit `kMetaErased` (0x80) of the meta byte. The unshadowed flag is
meta bit 0x20, i.e. bit `8 (value_bytes - 1) + 5` of `value`. An init record's
meta byte is 0 (checked against the initialized top). A lane array is a JSON
array of exactly 64 entries per bucket, `null` for a free lane.

```
{"format":"hierarchy-replay/0",
 "config":{"fanouts":[b_1,...,b_(L-1)],"carry1":U_1,"top_digit":D,"load":32,
           "horizon":max_accesses,"initialized":bool,
           "prefix_flushes":r0,"stash_buckets":s,"key_bytes":8,"value_bytes":V+1,
           "user_value_bytes":V,"branching":B,"secret_seed":"<hex>",
           "selected":"uniform"|"half"|null,
           // informative: "T","address_space" (32 T),"key_bound","trace_seed",
           // "drive":"eager"|"lazy","batch","skip_top_contents",
           // added, read by the completeness checks: "flush_policy":"handover"|"auto",
           // "accesses_requested","view":bool,"sync_check":bool,"view_limit":n|null,
           // "batch_vary","batch_scalar","batch_width" (MaxCombinedBatchLanes()),
           // "tier_widths":[TierBucketsOf(l), l = 1..L],"stash_widths":[sizing.Buckets(l)]
          },
 "shapes":{
   "direct":[{"digit":d, <the direct-job-native/0 "geometry" object>}, ... d = 1..b_1],
   "sep":[{"level":l,"digit":d,"C":..,"K":..,"e":..,"r":..,"range_bits":..,"I":..,
           "stash_pages":..,"a_tier_pages":..,"b_tier_pages":..,"tier_pages":..,
           // informative: "dfs":bool,"merge_pages","pool_swept_buckets","pool_direct_buckets"
          }, ... every 2 <= l < L, 2 <= d <= b_l],
   "top":{"C":..,"k":..,"e":..,"rho":..,"I":..,"dfs":bool,"r_pages":..,"b_pages":..,
          "merge_pages":..,"tier_pages":..},
   "prep":{"C":..,"k":..,"stash_pages":..,"a_tier_pages":..,"drain_pages":..,
           "range_bits":..,"I":..,"dfs":bool,"pool_swept_buckets":..},
   "init":{ the same fields, drain_pages = TierBucketsOf(L) }},   // added
 "init":[rec, ...],                       // the initialization input, in input order
 "units":[{"ordinal":v,"units":[[64 s lanes], ... r0 flush units]}, ...],
 "tables":[{"id":table_id,"owner":o,"slot_kind":"odd"|"inbox"|"top"|"run",
            "family":[l,v],"window":[begin,end],"main_buckets":n,"tier_buckets":t,
            "main":[[64 lanes], ... n buckets] | null,"tier":[64 t lanes, page-major] | null,
            // informative: "slot":index,"ident":[l,v] (the rule below, as the dumper
            // applied it),"seen":{"access":i,"level_one_ordinal":t} (first sight)
           }, ...],                  // in order of first sight; null contents: top
                                     // tables under --skip-top-contents (selected runs)
 "words":{"families":[[l,v], ...],"keys":[k, ...],"table":[[w per key] per family]},
 "view":{"arena":VIEW,"sync":VIEW|null},   // added, --view only (section "The adversary's view")
 "ops":[{"op":"write"|"read"|"erase"|"write_np","key":k,"value":v
         // value: the user bytes LE (no meta byte); 0 for read and erase.
         // optional "forced":true, "batch":n (AccessBatch number)
        }, ...],               // every op issued, the failing one included
 "outcome":{"accesses":n,      // ops completed
            "prefixes":p,      // prefixes completed in the run (seed excluded)
            "last_level_one_ordinal":t,"seed_prefixes":H,   // added
            "levels":[{"level":l,"published":v,             // added: state at the stop:
                       "job":null|{"ordinal":v,"prepared":b,"installed":b}}, ...],
            "failure":null | {"access":i,"message":"...","level":l|null,"ordinal":v|null,
                              // added: "during":"initialize"|"access"|"step",
                              // "phase":"prepare-older"|"install-carry"|"finish",
                              // "job":"level_one"|"separated"|"adopt"|"top_prepare"|
                              //       "top_finish"|"initialization","stepped_levels":[..]
                             }},
 "checks":{...}}               // added: the dumper's self-check report
```

Shape fields use the model structures' names (`DirectJob.Geometry`,
`SepGeom`, `TopGeom`, `TPGeom`) and are computed from the engine geometry and
stash sizing exactly as the existing per-job dumpers do
(`oracle/direct_native_dump.cpp`; `fd3.cpp`, `fdtop.cpp` under
`.lake/oracle/`; `oracle/fixtures-tp/fdtp.cpp`) and as the per-job oracle
readers map them (`Oracle/DirectJob.lean`, `SepDiff.lean`, `TopDiff.lean`,
`TPDiff.lean`). `units[i].units` lists the prefix's `r0` flush units in unit
order, each the `64 s` lanes of its `s` buckets in bucket-then-lane order (the
direct-job-native `inputs.units` encoding); ordinals run `s_1 + 1, …, t`
consecutively.

Every value is the engine's at the run's resolved geometry (automatic tier
widths at `horizon`): `direct` from `TierBucketsOf(1)`, `OlderTierBuckets(1, d)`,
`sizing.Buckets(1)`, `MergeStashBuckets` and `FinishPoolShapeAt` /
`LevelFinishRangePlan` (`pool_capacity` = DFS pool pages · 64); `sep` from
`FinishPoolShapeAt(g, sizing.Buckets(l), l, MakeMergeShape(U_l, d, r))`,
`OlderTierBuckets(l, d)`, `FinishCarryTierBuckets(l)`, `TierBucketsOf(l)`;
`top` from `TopMergePoolShapeOf`, `r_pages = merge_pages = sizing.Buckets(L)`
(the job's retained-carry and merge stashes: `SetStashWidths`),
`b_pages = CarryTierBuckets(L)`, `tier_pages = TierBucketsOf(L)`; `prep` from
`TopPreparePoolShapeOf(shape, S, OlderTierBuckets(L, D))` and
`TopPrepareRangePlan`, `drain_pages` the retained carry R
(`sizing.Buckets(L)`). `init` is `prep` with `drain_pages =
TierBucketsOf(L)`: the initialization's route drains into the published tier,
not into R (fdtp's init mode; TPDiff reads `out_tier_pages` there). The
model's `initOutput` and `initResult` use the explicit `sh.init` geometry.
Initialization may have a different drain from preparation. An initialized
run requires `shapes.init` (MALFORMED if absent), and evaluated initialization
geometry must satisfy `TPGeom.Valid`. `init_shape_differs` reports whether the
two emitted shapes differ; the battery checks that report against the fixture.
The shapes test still compares initialization with `selectedTP` at both selected
configurations. At the selected configurations the emitted
`sep` rows equal `Spec/Selected.lean` (28 uniform, 27 half-fanout rows), `top`
equals `selectedTop`, `prep` equals `selectedTP`, and `direct` equals
`selectedDirectGeometry`.

## How the Lean side identifies a table

With `cp(ℓ) = load · U_ℓ` (`Config.carryPositions`): a table in an `inbox` of
owner `o` is level `o - 1`'s (an even partial under the forwarding lease, a
forwarded full table, or a carry the receiver adopted, which the model makes
the same table); any other slot is level `o`'s. Its ordinal is
`v = window.end / cp(ℓ)` (exact division), and it is compared with
`table cfg sh tr words ℓ v`. Checks: `family = familyOf cfg ℓ v`; below the top
`window.begin = window.end - digitOf(b_ℓ, v) · cp(ℓ)` and
`main_buckets = digitOf(b_ℓ, v) · U_ℓ`; at the top `window.begin = 0` and
`main_buckets = T`. *Exception (engine fact):* the empty top an uninitialized
engine publishes at construction (`DescribeEmptyTop`) has family `(L, 0)` and
window `[0, 1)`, so `window.end / cp(L)` is not exact; it is top ordinal 0
(the model's base table). `window.end` is the engine's
`FamilyWindowEnd(family)`, which is invariant along forwarding, so the rule
agrees with the terminal family for forwards. Every table of the battery
satisfies these checks (slot kinds `odd`, `run`, `inbox`, `top`; a binary
level's digit-one plain copy is a new table in the odd bank of level `ℓ`,
identified as `(ℓ, v)`, same family as the carry). Main buckets are compared
lane-exactly; tiers are compared lane-exactly after dropping trailing free
lanes on both sides.

## Completeness (fail closed)

Missing evidence is an error, not a
vacuous pass. The oracle (`HierarchyDiff.evidenceFaults`; failures
`evidence.*`, `dumper_checks`; MALFORMED, exit 2, for an absent
required object):

| reason | check |
| --- | --- |
| `evidence.ops` | `ops` lists every issued operation: without a failure exactly `outcome.accesses` of them, as many as `config.accesses_requested`; with one at least `outcome.accesses` |
| `evidence.units` | the captured prefixes are exactly the ordinals `s_1 + 1 … s_1 + outcome.prefixes`; `outcome.prefixes = ⌊accesses / 64 r0 s⌋`; `last_level_one_ordinal = s_1 + prefixes`; `seed_prefixes = s_1` |
| `evidence.levels` | `outcome.levels` lists every level; without a failure level `ℓ` published `⌊t / P(ℓ)⌋` (the dumper settles at the end, lazy drive included), with one at most that |
| `evidence.contents` | a table without contents only at a selected configuration, only at the top, only under `config.skip_top_contents` |
| `evidence.tables` | every job that completed natively (the failure comparison's rule) has a recorded table at its coordinate, except a digit-one adoption at a level of fanout above 2 (its table is the carry); the top's seed table `(L, s_L)` is recorded |
| `dumper_checks` | `checks.failures` is empty |

MALFORMED: `ops`, `checks` (with `failures`), `outcome.levels`,
`outcome.seed_prefixes`, `outcome.last_level_one_ordinal` absent; with
`config.view` the `view` object and its `arena` view absent, and its `sync`
view absent with `config.sync_check` (or present without); a view's
`audit_violations`, `recorded`, a plan's `size` or an access's counter
absent; batch-tagged operations or chunks with `config.batch = 0`; no
batch-tagged operation or no `chunks` array with `config.batch` nonzero.

A non-null `config.selected` must be `uniform` or `half` and match that
configuration (up to the run's horizon), `prefix_flushes = 8`,
`stash_buckets = 1`, `T = 2^22`, `branching = 8`, and `key_bytes = 8`.
Every direct digit and separated row, and the top, preparation and
initialization shapes, must match the selected Spec data. Unknown names,
mislabelled small runs, missing shapes and changed shapes are MALFORMED
(`config.selected` or `shapes.selected`, exit 2). This common parser validation
runs for the hierarchy, scalar view and batch view, before any top skip.

The battery driver uses `hierarchy_fixture_manifest.py` for both generation
and required presence: all 64 fixtures and all five two-secret pairs, or the
60 non-selected fixtures under `--no-selected`. In the latter mode existing
selected files are explicitly ignored, including by the mutation suite; other
unexpected JSON files and any missing required fixture fail the inventory.

The only skip: at a selected configuration the top's tables
(`skipped_top`, with or without contents); a table compared is never one
without contents, so a passing line has `compared = tables - skipped_top`.

In the view replay (`OnlineDiff`, `OnlineBatchDiff`): `online.E.recorded`
(each engine's view records every completed operation: the arena
`outcome.accesses`, the synchronous engine up to its own failure
`checks.sync.sync_failure.access`, both capped by `config.view_limit`; and
`recorded` equals the record's length), `online.E.counters` (the dummy
counters form one chain: the first probing access starts at 1, each probing
access, or chunk, starts where the previous one's `size` (`lanes · size`)
counters end, a chunk's lane `g` at `dummy_base + g · size`; a recorded access
removed or nulled breaks it), and `online.units` also requires every
observed unit lane to agree with its operation (an erase inserted a
tombstone, a write its value; a read inserts the value found or a
tombstone).

The battery driver checks besides, per fixture: compared = tables −
skipped_top, with skipped_top the number of top tables at a selected run
and 0 elsewhere; `checks.failures` empty; `init_shape_differs` agrees with the emitted shapes; the
view of both engines present (`config.view`, `config.sync_check` on every
fixture) and complete; `key_bound` the address space. Its vacuity probes
(gutted fixtures) must each be rejected.

## Failure comparison

Natively a job may start its preparation of the older table speculatively,
before its carry arrives, so the engine can fail during the drain after
level-one ordinal `t` in a job whose `jobTime` is later than `t`. The dumper
therefore names the failing job (`outcome.failure.level`/`ordinal`, the top's
preparation and finish distinguished by the message's phase) whenever the
engine state lets it.

*How the dumper names it (engine facts).* The message carries no level
(`"level arena: the <phase> phase ran out of room at <site>; ..."`, phase
`prepare-older`, `install-carry` or `finish`). An inline sweep steps levels
`1..L` in order, each `LevelState::Step` counts itself first, and the sweep
stops at the throw; so the failing level is the highest level whose step count
moved, and its job is still bound after the throw (`job().ordinal()`, checked
to be the level's next ordinal and `job().family()` canonical). The top's
`prepare-older` is the preparation (`job: "top_prepare"`), anything else at the
top the finish; level one's install and finish are one job (`"level_one"`).
Observed: a top preparation failure of ordinal `o + 1` is raised in the drain
right after finish `o`, i.e. at `t = o P(L)` with `jobTime = (o + 1) P(L) > t`
(`i_force_top*`). A failed `Initialize` is `job: "initialization"`, level `L`,
ordinal `D`, `during: "initialize"`. Under `--drive lazy` steps run in deadline
order inside an access; the job named is the unique stepped level with a bound
job (otherwise `level`/`ordinal` are null; `stepped_levels` lists candidates).

The oracle checks:

1. every table published before the failure equals the model's (as above);
2. every potential job with `jobTime < t` succeeds in the model (they all
   completed natively), where `t` is the last level-one ordinal whose prefix
   was complete when the failure occurred (`outcome.last_level_one_ordinal`).
   *Eager drive only:* under `--drive lazy` the rebuild lags the requester, so
   jobs with `jobTime < t` may be unfinished or the failing one
   (`i_force_l1_lazy_b8`: job `(1, 3)` fails at `t = 4`); use
   `outcome.levels[ℓ].published` instead (level `ℓ`'s ordinals up to it
   completed natively);
3. the named job fails in the model (its bounded result on its reference
   inputs is not a publication), and the failure class agrees with the
   message's phase where the model distinguishes it;
4. a run without a native failure has no failing model job with
   `jobTime ≤ t` for the last completed level-one ordinal `t`, other than
   jobs whose native execution had not started (eager: at the end every job
   with `jobTime ≤ t` has published; `outcome.levels` shows any speculative
   preparation still bound).

## The theorems' premises (`trace_premises`, `unsh_promise`)

`HierarchyUniform` and `HierarchyChunk` assume `TracePremises cfg N tr`
and `UnshPromise cfg sh tr` (`Spec/Hierarchy.lean`; the chunk theorem at
`chunkConfig cfg (k + 1)`, same load, carry and model). Every replay checks
both on the observed trace; a violation fails the fixture (the line's
`failures` names it: `trace_premises.nodup|load|keys|init_nodup|init_keys`,
`unsh_promise.exact|sufficient`, next to `tables` and `failure_check`).

* `trace_premises`: each conjunct decided literally at every captured ordinal
  (the model's trace is `[]` elsewhere, where all hold) and on `init`. `N` is
  `config.key_bound` (default the engine's `CapacityEntries = 32 T`), else
  `config.address_space`; `N_le_2^27` is reported (the theorems need it; it
  holds at the selected configurations, `32 T = 2^27`). Reported: the
  ordinals and records checked, `load.max_records` against `load.bound = a U_1`
  (with the schema's `r0` units of `64 s` lanes and `64 r0 s = a U_1`, the
  bound cannot be exceeded by a well-formed fixture), `keys.max_key`, the
  first violations, and whether every key `≥ N` is a forced one
  (`keys.all_forced`). The battery's forced top overflows (`i_force_top*`,
  `i_force_topfinish`, `n_tiers_*`) violate `keys` by construction: a top
  bucket's share of the address space is about `32` keys.
* `unsh_promise` (`n/a` at a selected configuration, whose top is not
  evaluated): at every evaluated top finish `o`, (a) `exact`, the premise's
  instance at the fixture's words, `finishInputsAt` computed from the memo
  tables (`finishInputsOf_eq`, `unshInstance_iff`): every flagged tombstone of
  B's tier has no live copy in C's main; (b) `sufficient`, word-independent:
  every flagged tombstone of the carry (main and tier) has no live record
  with its key in the preparation's output (C and R) or the previous top
  table. (b) implies (a)'s instance at every tape whose finish inputs hold the
  same records (`UnshSufficient.instance`); with the model's word-independent
  record sets (`JobContracts.finishRecsA/B`, which need the promise only at
  earlier finishes) it implies `UnshPromise` by induction over the top
  ordinals (argued in `HierarchyDiff.lean`, not proved). Counts, so that a
  vacuous pass shows: `unsh_checked` (flagged carry tombstones),
  `exact.flagged_in_b_tier`, `exact.unflagged_shadowing_in_b_tier` (unflagged
  tier tombstones with a live copy in C: where a wrongly set flag would be
  caught), `sufficient.flagged_key_in_older`, `unflagged_shadowing`,
  `older_tombstones` (natively 0: the top publishes no tombstones). A
  violation lists the finish, the key, the tombstone, the live copy, where it
  is, and the key's operation history (`ops` indices).

## The unshadowed flag depends on the rebuild schedule (engine fact)

The online path sets meta bit 0x20 when the probe found nothing or found an
unshadowed tombstone. What the probe finds depends on how far the rebuild has
got: the top drops every carry tombstone, so a synchronous (or eagerly drained)
run can find nothing where a lagging arena still finds the shadowing tombstone
below the top. The lazy and the synchronous runs of one access sequence
therefore record different units in this bit alone (observed with
`--drive lazy --sync-check`; keys, values and tombstone bits agree, and the
eager arena equals the synchronous engine exactly). So the hierarchy model's fixed
logical trace (`Trace`) is a function of the access sequence and, in this one bit, of the
rebuild schedule; the replay is unaffected because `units` are the observed
bytes. The lazy `--sync-check` masks the bit, and so does the eager one
once an `AccessBatch` call completed a prefix before its last lane
(`checks.sync.straddling_calls`): the eager drive steps only between calls,
so the call's later chunks probe a lagging arena (observed: `--batch 100`,
meta `0xa0` synchronous against `0x80` in the arena, nothing else differs).

## The adversary's view (`--view`, `view`)

The native side of the online obliviousness replay (the trusted model
`Spec/Model/Online.lean`, the engine facts `Spec/Model/ENGINE_ONLINE.md`). With
`--view` the dumper records, for every scalar operation (`--view-limit n`: the
first `n`), what the adversary sees of it: for a probing operation (Read,
Write, Erase) the hashed main tables of its probe plan in cascade order and the
bucket the engine touched in each; nothing for `WriteWithoutProbe`, which opens
no reader epoch. It records the same for the synchronous engine of
`--sync-check`. Batches are recorded too (section "The batch path"
below). The selected configurations are in scope. The oracle does not evaluate their top (`T = 2^22`), and needs
not: `isReal` of entry `i` reads only the tables before it (`tables.take i`),
the top's entry is its plan's last (`SchedulePremises.tile` forces it, and the
oracle checks it: `online.E.top_order`), and `touched` of the top's entry
reads the words and the real flag only. So every entry, the top's included,
is compared; only the top's key sets are never computed.

```
VIEW = {"engine":"arena"|"sync","drive":"eager"|"lazy"|"sync",
        "recorded":n,                  // operations recorded (ops[0..n))
        // informative: "probing","entries","real","dummy","max_hashed",
        // "word_checks","audit_checks","audit_unobservable","audit_real_probes"
        "audit_violations":v,          // ProbeAuditViolations() at the end
        "batch":null | {...},          // added: the batch path's shape and counts (below)
        "plans":[{"consumed":c,        // the plan's heads_consumed (level-one ordinals
                                       // consumed into hashed tables, seeded ones included)
                  "tables":[[l,v],...],// its hashed mains in cascade order, as coordinates
                  "ids":[table_id,...],"families":[[fl,fo],...],  // the engine's nonce family
                  "windows":[[b,e],...],"epoch":e,"size":plan.tables.size(),
                  "first_live":f}, ...],      // distinct plans, in order of first use
        "chunks":[[first,lanes,p,dummy_base,call], ...],  // added: engine chunks (below)
        "accesses":[null                           // an unprobed write
                   | [p,                           // index into plans
                      [bucket per table],          // the bucket the engine touched
                      [1 real | 0 dummy per table],
                      [dummy word per table],      // the AES tag of its dummy block
                      dummy_base], ...]}           // the access's first dummy counter
```

**What is read from the engine.** Nothing in the view is recomputed from a
model. (1) The plan: the access's own composed plan, taken at its reader-epoch
pause point (`ArenaPause::kInsideReaderEpoch`, raised in `Probe`'s
`AccessEpoch` after `BeginAccess`), by calling the engine's `ComposedPlan()`,
which the access calls next and which then returns the same object unchanged
(inline executor: nothing publishes inside a reader epoch). Hashed entries are
identified by table id: in the arena through the table record of this fixture
(the identification rule above, so `tables` agree with `tables[].ident`); in
the synchronous engine, which publishes every table with `owner` = its level,
as `(owner, window_end / cp(owner))`, the empty top `(L, 0)`. (2) After the
access returns, the probe scratch `probe_` it filled (ProbeScratch,
`cpu_byteslice_probe_addresses.hpp`): per hashed main, at its AES slot `j`
and cascade index `i`, the tags `tags[2j]` (real block) and `tags[2j+1]`
(dummy block) and the candidate pointers `bucket[2i]`, `bucket[2i+1]`,
converted to bucket indices of the entry's storage. (3) Which one was touched:
the audit's real-probe count moved by `r`, and the cascade's `found` is
monotone (a dummy-gated main never hits, `ENGINE_ONLINE.md` 4), so the first
`r` hashed mains were probed for real and the rest got their dummy candidate.
The private members (`probe_`, `dummy_counter_`, `ComposedPlan`, the audit's
sets) are read by compiling the engine headers with `private` spelled `public`
in the dumper; no engine source changes. The dumper is compiled with
`MICRORAM_BYTESLICE_PROBE_AUDIT` (counting only).

**Self-checks** (each a `checks.failures` entry, prefixed `view:` or
`view (sync):`): exactly one reader epoch per probing access and none per
unprobed write; the dummy counter advanced by `plan.tables.size()`;
`LastProbeTables()` and `LastProbeBuckets()` equal the plan's live length and
bucket count; every candidate pointer is a bucket boundary of its table (and
its mask pointer that bucket's); the audit's per-family sets gained the key in
exactly the first `r` families (read at the access's first publication after
its probe, before any family can retire, or when the access returns; a
family the synchronous engine retired inside the access, which it does without
a pause point, is counted in `audit_unobservable`); no audit violation; the
real tag equals the emitted word of `(family, key)` (`words`, computed
independently with `AesCtrTagU128WordsHost` under `FamilyNonce` /
`EmptyTopNonce`); the dummy tag equals `AesCtrTagU128WordsHost(dummy_lo,
dummy_hi, dummy_base + i, 0)` of the family's dummy nonce (`ENGINE_ONLINE.md`
3); every entry's family is `CanonicalFamily` of its coordinate. A failing
access (an exception) ends the record before it.

**The oracle** (`OnlineDiff.lean`; with `--hierarchy` its report is the
line's `online` object and its failures join `failures`; `--online` runs it
alone). It builds the model's inputs: the run (`OnlineRun`: operation `j` is
`blind` for `write_np`, else `probe`, inserting the record at position `j` of
the captured units, i.e. unit `j / 64 s`, lane `j mod 64 s` of ordinal
`s_1 + 1 + ⌊j / 64 s r0⌋`; an empty lane or an uncaptured prefix gives the
operation's key with a placeholder value, counted as `records_unobserved`;
`init` and the unshadowed flag as above), `OnlineGeom ⟨64 s, r0⟩`, the schedule
(the recorded plans; an unprobed write gets the previous probing access's
plan), the words matrix and the recorded dummy words. Over the recorded
operations of each engine it computes the model's `isReal` and `touched` for
every plan entry (requester state advanced per operation, table key sets from
the memoised tables on `traceOf`; equal to the trusted definitions by
`stateAt_succ`, `denseKeysWith_eq`, `keySet_table`, `isRealWith_eq`,
`touchedWith_eq`) and compares them with the engine's real flag and bucket.
Failure reasons:

| reason | check |
| --- | --- |
| `online.units` | `traceOf` of the rebuilt run reproduces every captured prefix complete within the recorded operations, unit by unit and lane by lane (the Requester model's slot and clearing discipline), and every observed lane holds its operation's key |
| `online.E.view` | a touched bucket differs from the model's `touched` (`E` = `arena` or `sync`) |
| `online.E.real` | a real flag differs from the model's `isReal` |
| `online.E.kinds` | an operation's kind (probe or not) disagrees with the record (an access for a `write_np`, none for a probing op) |
| `online.E.schedule` | a field of `SchedulePremises` (consumed, length, coords, one_top, tile) fails on the recorded schedule; `first` names the operation, the plan and its windows |
| `online.E.plans` | an entry's engine family is not the model's `familyOf` of its coordinate, or (arena) its table id is not a recorded table with that coordinate |
| `online.E.fresh` | `OnlineFresh` on this run: a `(familyOf c, key)` is real-probed twice; also reported: real probes whose family is outside `Config.coordinates` or whose key is `≥ N` (not failures: forced keys pass `N` by construction) |
| `online.E.words` | a real probe's `(family, key)` word is missing from `words` |
| `online.sync.sync_schedule` | the synchronous engine's plan at a probing access is not `syncSchedule cfg j` (consumption mark and tables) |
| `online.E.audit` | the engine's probe audit counted a violation |
| `online.E.recorded` | the view does not record every completed operation (section "Completeness") |
| `online.E.counters` | the dummy counters do not form one chain (section "Completeness") |
| `online.E.top_order` | at a selected configuration, a top entry that is not its plan's last (the entries after it would read the top's contents, which are not evaluated) |

The battery (`gen_hierarchy_fixtures.sh`) records the view on every fixture
(eager and lazy drive, kShare, initialized, forced failures and tier
overflows, batches, both selected configurations scalar and batch) for both
engines; `hierarchy_replay_tests.py` requires the online replay to pass on each
and mutates the view (see its header).

## The batch path (`--view` with `--batch`)

The view of `AccessBatch` (the trusted model
`Spec/Model/OnlineBatch.lean`, the engine facts `ENGINE_ONLINE.md` 7). The
harness's `--batch k` hands `k` requests to one `AccessBatch` call
(`--batch-vary`: a size uniform in `[1, k]` per call; `--batch-scalar q`: `q`
scalar operations, `WriteWithoutProbe` included, after every call); the
engine cuts a call into chunks of at most `MaxCombinedBatchLanes()` lanes (public:
`--batch-lanes w`, default 16, in the chunked shape `RunBatchChunk`;
`w · P` with `--batch-tiles P` in the parallel shape `RunBatchJob`, optionally
`--batch-bucket-scan`), further capped at the next requester-unit boundary.
A chunk is one operation of the model. A batch
has no `WriteWithoutProbe` lane (`BatchOp` is read, write, erase, exchange), so
the harness keeps turning a drawn `write_np` into a `write` inside a call (as
before); scalar operations between calls keep theirs. Every lane is inserted
at one access position, so the record stays one entry per operation, i.e. per
**slot**: `accesses[t]` is slot `t`'s `[p, touched, real, dummy, counter]` with
`p` its chunk's plan and `counter` the lane's first dummy counter
`dummy_base + g · size` (lane `g` of the chunk). The chunks:

```
"chunks":[[first,                // the chunk's first slot (= op index)
           lanes,                // m, its lane count
           p,                    // index into plans: the plan the chunk probes
           dummy_base,           // dummy_counter_ + 1 when the chunk claimed its m · size counters
           call], ...]           // ops[].batch: the harness's AccessBatch number
"batch":{"width":MaxCombinedBatchLanes(),"shape":"chunked"|"tiles","lanes":w,"participants":P,
         "bucket_scan":b,        // informative from here on:
         "chunks","batch_lanes","duplicate_lanes","straddle_prefix","straddle_unit",
         "scratch_checks","found_checks","dedup_checks","shadow_real"}
```

The `straddle_unit` and `straddle_prefix` counters are zero under
unit-aligned lowering. A public call may still span many units and prefixes.
The Lean batch replay independently rejects a chunk that crosses a unit boundary,
even when both recorded engines agree on that chunk.

**What is read from the engine, per chunk.** (1) At the chunk's reader-epoch
pause point (`AccessEpoch` in `RunBatchChunk`/`RunBatchJob`, after the lanes
were loaded and, chunked, deduplicated): the plan, exactly as for a scalar
access (`ComposedPlan()`, which the chunk calls next; one plan per chunk),
the counters, the lanes' keys as the tiles hold them, the chunked shape's
dedup (`tile.dedup`), the tiles' lane counts (`BatchPartition`), the audit's
sets before the probe, and a **shadow** of the probe on the engine's own data:
the engine's address pass (`ResolveHashedProbeAddressesBatch` on the plan's
addressing with the engine's AES keys and the dummy base the chunk will
claim) into a private scratch, and the cascade's found bits with the engine's
matcher (`MatchMaskByteSlicedTree`) on the plan's storage (every bucket of a
dense entry; the real candidate of a hashed main while not found; a duplicate
lane starts found), which says which hashed mains each lane probes for real.
(2) When the next chunk's pause point is reached or the call returns (nothing
in between rewrites a tile's probe scratch, found bits or job metadata): the
tiles' own `BatchProbeScratch` of every lane (the parallel shape's tile and
local lane by `BatchPartition`), whose AES tags and candidate pointers must
equal the shadow's exactly; each lane's final `found` bit, which must equal
the shadow's; the parallel shape's job dedup (`metadata.duplicates`,
`superseded`) against the lanes' keys. The touched bucket is the engine's
candidate the shadow's real flag selects. The audit cannot attribute real
probes to lanes by itself (its count is per chunk), hence the shadow; it
cross-checks it.

**Self-checks** (prefix `view:` / `view (sync):`): one reader epoch for every
chunk independently predicted from the public call length, maximum width,
starting position and unit size; the counter advanced by `m · size` per
chunk; `LastProbeTables()`/`LastProbeBuckets()` the plan's; the audit's real
probes moved by the shadow's number of real probes, with no violation; the
audit's per-family sets gained exactly the shadow's real (family, key) pairs
(observable families; the synchronous engine retires some inside the call,
counted in `audit_unobservable`); no duplicate lane probed for real; the
engine's scratch, found bits and dedup equal the shadow's and the keys'; the
real tag is the family's word of the key, the dummy tag
`AesCtrTagU128WordsHost(dummy_lo, dummy_hi, dummy_base + g · size + i, 0)` of
the family's dummy nonce (`i` the entry's index in `plan.tables`); every
candidate a bucket of its table. A failing call ends the record before it.

**The oracle** (`OnlineBatchDiff.lean`; `--hierarchy` uses it for a fixture
whose `config.batch` is nonzero, its report the line's `online` object with
`"model":"OnlineBatch"`). The run `BatchRun`: walking the slots, a slot that
starts a recorded chunk (of the longest record; the other engine's chunks
must be the same cut) opens `.batch lanes` over the chunk's slots, every other
slot is a scalar `.probe` (`.blind` for `write_np`); each lane's record is the
captured unit lane at its position, as above (a superseded lane, inserted
non-real, gets a placeholder). The schedule `S` by slot (a lane: its chunk's
plan), read by the model at operations' first slots through the trusted
`slotSchedule` and `chunkStart`. Per slot and plan entry it compares the
model's `isReal` and `touched` (requester state at the slot's operation,
`stateAt_succ`; the duplicate test on the operation's lanes,
`duplicateWith_eq`; table key sets on `traceOf`, `keySet_table`;
`isRealB_eq`, `touchedB_eq`). Failure reasons: those of the scalar table
(`online.units`, `online.E.view|real|kinds|schedule|plans|fresh|words|audit`,
`online.sync.sync_schedule`, at each operation's first slot:
`syncSchedule cfg (chunkStart ws t)`), and

| reason | check |
| --- | --- |
| `online.E.chunks` | a slot is in a recorded chunk iff its operation went to `AccessBatch` (`ops[].batch`), with the chunk's call; no chunk lane is a `write_np`; every lane records its chunk's plan; the two engines cut the same chunks (first slot, lanes, call) |

On a scalar view `--hierarchy` also runs this replay (no chunks: every slot a
scalar operation, the batch model's `BatchScalar` case) under `online_batch`,
its failures named `online_batch.*`; the driver requires it to pass with the
scalar replay's counts.


## Two secrets: the schedule does not depend on the words

The fixtures `s2_*_a` and `s2_*_b`
run one operation sequence under two engine secrets (`--secret 5eed0c0de`,
`1234abcd9`; no forced keys, whose search reads the words): `kHandOver` eager
and lazy, and the engine's default inline policy (`--policy auto`, `kShare`)
scalar, initialized and batch, each with both engines' views.
`hierarchy_replay_tests.py` requires, per pair: the configurations equal but
for the secret; `ops`, `init`, `units` (the unshadowed bits included) and
`outcome` identical; every table's descriptor (id, owner, slot, family,
window, first sight) and record set identical; for both engines, every
recorded operation's plan (dereferenced: coordinates, ids, families,
windows, consumption mark, epoch, size), first dummy counter and real/dummy
pattern identical, and the chunks identical; and, so that the pair is not
vacuous, the words and some touched buckets different. Each fixture also
passes the replay on its own.

## Geometry31 sparse top and public API extensions

`--selected geometry31` is validated against the canonical geometry31
configuration, horizon `2^32`, all job shapes, and `T=2^26`. It emits the
ordinary hierarchy schema plus `sparse_top`, an array of exactly three
snapshots: the empty and initialized top publications and the initialized
top at the end. Each has `id`, `family`, `phase` (`publish` or `final`),
`scanned_buckets`, `main`, and `tier`. `main` is an ascending list of
`[bucket_index, [64 lane records/nulls]]`; every occupied bucket is present.
The exporter reads every occupancy mask, so an omitted bucket represents
an empty mask, not an unexamined bucket. The tier is a full lane list.

`PublicApiDiff.checkSparseTop` compares these against the restricted sparse
model initializer, rejecting missing/duplicate snapshots, wrong identities,
insufficient scan coverage, and any differing bucket, lane, record, or tier.
It requires 1–32 initial records and no top replacement; its exact split
steps are those of `engineRule`, with executable small-case checks against
the dense initializer, not a general refinement proof.

`api_native_dump` adds `api: {format: "public-api/0", width, calls}`. Calls
contain original write/callback/batch descriptors and observed responses,
`position` (primitive access count), `current` (a full dense unit), `partial`
(frozen units of the unfinished prefix), and `groups` (native reader-epoch
`[starting_position, lane_count]` pairs). Callback descriptors specify the
fixed test transform `(old + delta + (found ? 17 : 31)) mod 256`, optional
key replacement, and whether the callback throws after modifying its
buffers. Responses include callback input/presence/count and return or
exception, and each batch lane's optional value/presence. Normalized `ops`
add `exchange` with an `insert` boolean. The independent API model predicts
responses, lowering, chunk boundaries, and every inserted record from the
original descriptors; it does not use native returned values as its inputs.
Internal probing groups stop at the next requester-unit boundary, as well as
at the public width or a blind-write separator. Their expected width uses
`64 * config.stash_buckets` and the public primitive position modulo that unit
size, with a full unit normalized before the next group. This is an execution
rule for the existing schema; fixtures recorded under another grouping rule
fail it.

`--api` requires and checks API evidence. `--geometry31` requires geometry31
and checks its sparse tops. `--hierarchy` automatically enables the API
extension when `api` is present and the sparse extension for geometry31.
Missing extension evidence or an internal-state mismatch fails the run,
even if the ordinary hierarchy check passes. Reports retain the original
fields and add `extension` with `result`, `api_calls`, `api_probe_groups`,
and `exact_sparse_top_snapshots` (or an `error`). A dense top counted in
`skipped_top` is covered separately by the sparse extension; consumers must
check both results. `--online` remains the view-only checker.

### Complete-cycle API scheduling and key domains

`api.settle_after_call = true` selects the complete-cycle API driver. It uses
4-byte payloads (5 stored bytes including metadata) and 4-byte keys, the
handover policy, two dense-prefix queue slots, and a drain after each call.
Each call emits `top_ordinal`. The oracle requires it to equal
`cfg.seed L + position / cfg.carryPositions L`. At a new top ordinal it keeps
only the latest live winners of the consumed reference-history prefix and
retains the later suffix. This models top garbage collection before the next
call while preserving all requester units for their separate comparisons.
Missing/false retirement metadata cannot permit a trace past a top rebuild.
The lazy schedule requires a trace that ends before top replacement.

The hierarchy exporter accepts `--K 4|8` and `--sequential-keys` (universe
`[0, keys)`). Default sampling remains `[1, key_bound)`. Neither sampling rule
is a library restriction. The capacity count and the numeric-key premise
are separate: the nonzero full-capacity regression sets `key_bound` one above
capacity, expects only `trace_premises.N` to fail, and requires exact state
and view equality throughout. It does not claim to check the generic
universe-cardinality probability theorem.
