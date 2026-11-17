import Std.Data.HashMap
import Std.Data.HashSet
import RebuildBound.Oracle.DirectJob
import RebuildBound.Oracle.SepDiff
import RebuildBound.Oracle.TopDiff
import RebuildBound.Oracle.TPDiff
import RebuildBound.Spec.Model.Hierarchy
import RebuildBound.Oracle.SelectedShapes

/-!
# Trace replay of the whole level hierarchy (`--hierarchy`)

Reads a `hierarchy-replay/0` fixture (`oracle/HIERARCHY_REPLAY_SCHEMA.md`,
written by `oracle/hierarchy_dump.cpp`): one run of the real public engine on
an access trace, with every table it published, the units each level-one
ordinal consumed, the initialization input, the ideal words and the outcome.
It rebuilds the same run from the trusted model
`RebuildBound.Model.Hierarchy` and compares:

* every published table, identified as `(ℓ, v)` (an `inbox` of owner `o` is
  level `o - 1`'s, any other slot level `o`'s; `v = window.end / cp(ℓ)`),
  against `table cfg sh tr words ℓ v`: its family against `familyOf`, its
  window and main width, its main buckets lane by lane, and its tier lane by
  lane after dropping trailing free lanes on both sides;
* the first capacity failure against the potential jobs' bounded results
  (the schema's "Failure comparison"): the jobs that completed natively (time
  `< t`, or `≤ t` without a failure; under `--drive lazy` every ordinal up to
  its level's `outcome.levels` publication) succeed in the model, and the job
  the engine names (`outcome.failure.job`, level, ordinal) fails in the model
  with the same coarse failure class as the message's site;
* the theorems' premises on the observed trace ("The theorems' trace
  premises" below): `TracePremises` at `N = config.key_bound`, and
  `UnshPromise` at every evaluated top finish, exactly at the run's words and
  in a word-independent sufficient form. A violation fails the fixture; the
  line's `failures` lists every failed check.

The empty top every engine publishes at construction (family `(L, 0)`,
window `[0, 1)`) is top ordinal 0 of an empty start; before an
initialization it is compared with the empty start's base table.

**Fail closed.** Missing evidence is a failure, not a vacuous pass
(`evidenceFaults`, failures `evidence.*` and `dumper_checks`): every issued
operation listed, every completed prefix captured, every natively completed job
with a recorded table, contents omitted only for the top's tables of a selected
run (`config.skip_top_contents`), and the dumper's `checks.failures` empty.
`shapes.init` is required on an initialized run (malformed if absent); the
model routes initialization with that shape. `init_shape_differs` reports
whether it differs from preparation, which is permitted.

**The evaluator follows the model's defining equation.** `table` is
well-founded recursion without sharing, exponential if called per table, so
the oracle evaluates the tables in serialised order (level-one ordinal by
level-one ordinal, each level whose ordinal it completes in increasing level)
into a memo `(ℓ, v) ↦ Output`, each entry computed by `Env.evalTable` with the
model's own `base` and `step` on memo entries: the right-hand side of
`table_eq`. `evalTable_sound` proves that a memo of model tables only ever
receives model tables. Each potential job's bounded result is the model's
function with the memo tables substituted for its `table`/`carryOf` calls
(`levelOneResultOf` … `finishResultOf`, each proved equal to the model's
function by `rfl`). Job semantics are not reimplemented anywhere here.

At a validated selected configuration (`config.selected` names `uniform` or
`half`, with matching configuration and every job shape, `T = 2^22`) the top
is never evaluated: `table ℓ v` for `ℓ < L` does not read the top, and the top
tables and top jobs are reported as skipped (`skipped_top`, the only skip: a
table compared is never one without contents, so `compared = tables -
skipped_top` on a passing run).

Core `Lean` and `Std` and the core-only model only, as every oracle module.
-/

open Lean Std

namespace RebuildBound.Oracle.HierarchyDiff

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.DirectJob
open RebuildBound.Oracle (P natField strField boolField arrField objField)

abbrev MRec := RebuildBound.Model.Rec
abbrev DGeom := RebuildBound.Model.DirectJob.Geometry

/-! ### The fixture -/

/-- One table the engine published. -/
structure NativeTable where
  id : Nat
  owner : Nat
  slotKind : String
  family : Nat × Nat
  window : Nat × Nat
  mainBuckets : Nat
  tierBuckets : Nat
  /-- The main buckets and the tier's lanes; `none` for a top table whose
  contents the dumper skipped (`--skip-top-contents`). -/
  contents : Option (List Bucket × List (Option MRec))

/-- The engine's first failure. -/
structure NativeFailure where
  access : Nat
  message : String
  level : Option Nat
  ordinal : Option Nat
  /-- The dumper's name of the failing job's kind (`level_one`, `separated`,
  `adopt`, `top_prepare`, `top_finish`, `initialization`), if given. -/
  job : Option String

/-- One issued operation (`ops[i]`): its kind, key and whether it is a forced key. -/
structure NativeOp where
  kind : String
  key : Nat
  forced : Bool

structure Replay where
  cfg : Config
  selected : Option String
  valueBytes : Nat
  prefixFlushes : Nat
  stashBuckets : Nat
  direct : HashMap Nat DGeom
  sep : HashMap (Nat × Nat) SepGeom
  top : Option TopGeom
  prep : Option TPGeom
  init : List MRec
  /-- Level-one ordinal ↦ its flush units. -/
  units : HashMap Nat (List Bucket)
  tables : Array NativeTable
  /-- Family coordinate ↦ key ↦ word. -/
  words : HashMap (Nat × Nat) (HashMap Nat Nat)
  accesses : Nat
  prefixes : Nat
  failure : Option NativeFailure
  /-- `eager` (the executor drained after every prefix) or `lazy`. -/
  drive : String
  /-- `outcome.last_level_one_ordinal`. -/
  lastOrdinal : Option Nat
  /-- `outcome.levels`: each level's last published ordinal. -/
  published : HashMap Nat Nat
  /-- `shapes.init` (the initialization's route, draining into the published tier). -/
  initShape : Option TPGeom
  /-- `config.key_bound` (the dumper's universe bound, default `32 T`) and
  `config.address_space` (the engine's `CapacityEntries`, `32 T`). -/
  keyBound : Option Nat
  addressSpace : Option Nat
  /-- The issued operations (kind, key, forced), for key histories in reports. -/
  ops : Array NativeOp
  /-- `config.skip_top_contents`: the dumper omitted the top tables' contents
  (only at a selected configuration may a table have no contents). -/
  skipTopContents : Bool
  /-- `outcome.seed_prefixes`: the prefixes the initialization seeded. -/
  seedPrefixes : Nat
  /-- `config.accesses_requested`: the operations the dumper was asked to issue. -/
  accessesRequested : Option Nat
  /-- `checks.failures`: the dumper's self-check failures (must be empty). -/
  dumperChecks : List String
  /-- `checks.sync.sync_failure.access`: where the synchronous engine of
  `--sync-check` failed, if it did (its view ends before that access). -/
  syncFailureAccess : Option Nat
  /-- `config.view`, `config.sync_check`, `config.view_limit`, `config.batch`. -/
  viewRequested : Bool
  syncCheck : Bool
  viewLimit : Option Nat
  batch : Nat

def pairField (j : Json) (ctx k : String) : P (Nat × Nat) := do
  let a ← arrField j ctx k
  match a.toList with
  | [x, y] =>
    match x.getNat?, y.getNat? with
    | .ok x, .ok y => pure (x, y)
    | _, _ => throw s!"{ctx}.{k}: expected two natural numbers"
  | _ => throw s!"{ctx}.{k}: expected a pair"

def optNatField (j : Json) (ctx k : String) : P (Option Nat) :=
  match j.getObjVal? k with
  | .ok Json.null => pure none
  | .ok v => match v.getNat? with
    | .ok n => pure (some n)
    | .error _ => throw s!"{ctx}.{k}: expected a natural number or null"
  | .error _ => pure none

/-- A lane array of exactly `n` lanes. -/
def parseLanes (ctx : String) (n : Nat) (j : Json) : P Bucket := do
  let b ← DirectJob.parseBucket ctx j
  if b.length != n then throw s!"{ctx}: expected {n} lanes, got {b.length}"
  return b

def parseConfig (j : Json) : P (Config × Option String × Nat × Nat × Nat) := do
  let ctx := "config"
  let fanouts ← (← arrField j ctx "fanouts").toList.mapM fun x =>
    match x.getNat? with
    | .ok n => pure n
    | .error _ => throw "config.fanouts: expected natural numbers"
  let cfg : Config := {
    fanouts, carry1 := ← natField j ctx "carry1", topDigit := ← natField j ctx "top_digit"
    load := ← natField j ctx "load", horizon := ← natField j ctx "horizon"
    initialized := ← boolField j ctx "initialized" }
  let selected ← match j.getObjVal? "selected" with
    | .ok Json.null => pure none
    | .ok (Json.str s) => pure (some s)
    | .ok _ => throw "config.selected: expected a string or null"
    | .error _ => pure none
  return (cfg, selected, ← natField j ctx "value_bytes", ← natField j ctx "prefix_flushes",
    ← natField j ctx "stash_buckets")

def parseSep (j : Json) : P ((Nat × Nat) × SepGeom) := do
  let ctx := "shapes.sep"
  return ((← natField j ctx "level", ← natField j ctx "digit"),
    { C := ← natField j ctx "C", K := ← natField j ctx "K", e := ← natField j ctx "e"
      r := ← natField j ctx "r", rangeBits := ← natField j ctx "range_bits", I := ← natField j ctx "I"
      stashPages := ← natField j ctx "stash_pages", aTierPages := ← natField j ctx "a_tier_pages"
      bTierPages := ← natField j ctx "b_tier_pages", tierPages := ← natField j ctx "tier_pages" })

def parseTop (j : Json) : P TopGeom := do
  let ctx := "shapes.top"
  return { C := ← natField j ctx "C", k := ← natField j ctx "k", e := ← natField j ctx "e"
           rho := ← natField j ctx "rho", I := ← natField j ctx "I", dfs := ← boolField j ctx "dfs"
           rPages := ← natField j ctx "r_pages", bPages := ← natField j ctx "b_pages"
           mergePages := ← natField j ctx "merge_pages", tierPages := ← natField j ctx "tier_pages" }

def parsePrep (j : Json) : P TPGeom := do
  let ctx := "shapes.prep"
  return { C := ← natField j ctx "C", k := ← natField j ctx "k"
           stashPages := ← natField j ctx "stash_pages", aTierPages := ← natField j ctx "a_tier_pages"
           drainPages := ← natField j ctx "drain_pages", rangeBits := ← natField j ctx "range_bits"
           I := ← natField j ctx "I", dfs := ← boolField j ctx "dfs" }

/-- An optional shape object (`null` or absent is `none`). -/
def optObj (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok Json.null => none
  | .ok v => some v
  | .error _ => none

def parseTable (i : Nat) (j : Json) : P NativeTable := do
  let ctx := s!"tables[{i}]"
  let n ← natField j ctx "main_buckets"
  let t ← natField j ctx "tier_buckets"
  let contents ← match ← objField j ctx "main", ← objField j ctx "tier" with
    | Json.null, Json.null => pure none
    | mj, tj => do
      let main ← match mj.getArr? with
        | .ok a => a.toList.mapM (parseLanes s!"{ctx}.main" 64)
        | .error _ => throw s!"{ctx}.main: expected an array of buckets"
      if main.length != n then throw s!"{ctx}.main: expected {n} buckets, got {main.length}"
      pure (some (main, ← parseLanes s!"{ctx}.tier" (64 * t) tj))
  return { id := ← natField j ctx "id", owner := ← natField j ctx "owner"
           slotKind := ← strField j ctx "slot_kind", family := ← pairField j ctx "family"
           window := ← pairField j ctx "window", mainBuckets := n, tierBuckets := t, contents }

def parseWords (j : Json) : P (HashMap (Nat × Nat) (HashMap Nat Nat)) := do
  let ctx := "words"
  let fams ← arrField j ctx "families"
  let keys ← (← arrField j ctx "keys").mapM fun x =>
    match x.getNat? with
    | .ok n => pure n
    | .error _ => throw "words.keys: expected natural numbers"
  let rows ← arrField j ctx "table"
  if rows.size != fams.size then throw "words.table: one row per family expected"
  let mut out : HashMap (Nat × Nat) (HashMap Nat Nat) := {}
  for h : i in [0:fams.size] do
    let f ← match fams[i].getArr? with
      | .ok #[x, y] => match x.getNat?, y.getNat? with
        | .ok x, .ok y => pure (x, y)
        | _, _ => throw s!"words.families[{i}]: expected [level, ordinal]"
      | _ => throw s!"words.families[{i}]: expected [level, ordinal]"
    let row ← match rows[i]!.getArr? with
      | .ok a => pure a
      | .error _ => throw s!"words.table[{i}]: expected an array"
    if row.size != keys.size then throw s!"words.table[{i}]: one word per key expected"
    let mut m : HashMap Nat Nat := {}
    for h : k in [0:keys.size] do
      match row[k]!.getNat? with
      | .ok w => m := m.insert keys[k] w
      | .error _ => throw s!"words.table[{i}][{k}]: expected a natural number"
    out := out.insert f m
  return out

/-- The `shapes` object as emitted: rows by digit and by `(level, digit)`. -/
structure EmittedShapes where
  direct : HashMap Nat DGeom
  sep : HashMap (Nat × Nat) SepGeom
  top : Option TopGeom
  prep : Option TPGeom
  init : Option TPGeom

def parseShapes (shapes : Json) : P EmittedShapes := do
  let mut direct : HashMap Nat DGeom := {}
  for x in (← arrField shapes "shapes" "direct") do
    let d ← natField x "shapes.direct" "digit"
    if direct.contains d then throw s!"shapes.direct: digit {d} listed twice"
    direct := direct.insert d (← DirectJob.parseGeometry x)
  let mut sep : HashMap (Nat × Nat) SepGeom := {}
  for x in (← arrField shapes "shapes" "sep") do
    let (c, g) ← parseSep x
    if sep.contains c then throw s!"shapes.sep: row {c} listed twice"
    sep := sep.insert c g
  return { direct, sep, top := ← (optObj shapes "top").mapM parseTop
           prep := ← (optObj shapes "prep").mapM parsePrep
           init := ← (optObj shapes "init").mapM parsePrep }

/-- A selected label is an assertion to check, never permission by itself to
omit evidence. The core-only snapshots equal the canonical Spec data (checked
by `spec_tests/SelectedReplay.lean`). Every scalar and batch replay uses this
validator before the selected top-skipping path can be reached. -/
def validateSelected (config : Json) (cfg : Config) (selected : Option String)
    (r0 s : Nat) (em : EmittedShapes) : P Unit := do
  let some name := selected | return ()
  let (want, rows) ← match name with
    | "uniform" => pure (SelectedShapes.uniformConfig, SelectedShapes.uniformSeparated)
    | "half" => pure (SelectedShapes.halfFanoutConfig, SelectedShapes.halfFanoutSeparated)
    | "geometry31" => pure (SelectedShapes.config31, SelectedShapes.separated31)
    | _ => throw "config.selected: expected \"uniform\" or \"half\", or \"geometry31\""
  if (name == "geometry31" && cfg.horizon != want.horizon) ||
      { cfg with horizon := want.horizon } != want || r0 != 8 || s != 1 then
    throw s!"config.selected: {name} does not match the selected configuration"
  if (← natField config "config" "T") != (if name == "geometry31" then 2 ^ 26 else 2 ^ 22) ||
      (← natField config "config" "branching") != 8 ||
      (← natField config "config" "key_bytes") != 8 then
    throw s!"config.selected: {name} does not match the selected native geometry"
  for d in List.range' 1 (want.fanout 1) do
    if em.direct[d]? != some (SelectedShapes.selectedDirectGeometry d) then
      throw s!"shapes.selected: direct digit {d} does not match"
  if em.direct.size != want.fanout 1 then throw "shapes.selected: unexpected direct digit"
  let classes := SelectedShapes.separatedClasses want
  for (ℓ, d) in classes do
    if em.sep[(ℓ, d)]? != SelectedShapes.sepRow want rows ℓ d then
      throw s!"shapes.selected: separated row ({ℓ}, {d}) does not match"
  if em.sep.size != classes.length then throw "shapes.selected: unexpected separated row"
  if em.top != some (if name == "geometry31" then SelectedShapes.top31 else SelectedShapes.selectedTop) then throw "shapes.selected: top does not match"
  if em.prep != some (if name == "geometry31" then SelectedShapes.prep31 else SelectedShapes.selectedTP) then throw "shapes.selected: preparation does not match"
  if em.init != some (if name == "geometry31" then SelectedShapes.init31 else SelectedShapes.selectedTP) then throw "shapes.selected: initialization does not match"

/-- A parsed fixture's replay inputs (`parseReplay` on the parsed JSON). -/
def parseReplayJson (j : Json) : P Replay := do
  let fmt ← strField j "fixture" "format"
  if fmt != "hierarchy-replay/0" then
    throw s!"unsupported fixture format \"{fmt}\" (want \"hierarchy-replay/0\")"
  let (cfg, selected, valueBytes, r0, s) ← parseConfig (← objField j "fixture" "config")
  if valueBytes == 0 then throw "config.value_bytes: expected a positive number"
  let sh ← parseShapes (← objField j "fixture" "shapes")
  validateSelected (← objField j "fixture" "config") cfg selected r0 s sh
  let init ← (← arrField j "fixture" "init").toList.mapM (DirectJob.parseRecord "init")
  let mut units : HashMap Nat (List Bucket) := {}
  for x in (← arrField j "fixture" "units") do
    let o ← natField x "units" "ordinal"
    if units.contains o then throw s!"units: ordinal {o} listed twice"
    let us ← (← arrField x "units" "units").toList.mapM (parseLanes s!"units[{o}]" (64 * s))
    if us.length != r0 then throw s!"units[{o}]: expected {r0} flush units"
    units := units.insert o us
  let tablesJ ← arrField j "fixture" "tables"
  let mut tables := #[]
  for h : i in [0:tablesJ.size] do
    tables := tables.push (← parseTable i tablesJ[i])
  let outcome ← objField j "fixture" "outcome"
  let failure ← match outcome.getObjVal? "failure" with
    | .ok Json.null => pure none
    | .ok f => pure (some {
        access := ← natField f "outcome.failure" "access"
        message := ← strField f "outcome.failure" "message"
        level := ← optNatField f "outcome.failure" "level"
        ordinal := ← optNatField f "outcome.failure" "ordinal"
        job := match f.getObjValAs? String "job" with
          | .ok s => some s
          | .error _ => none })
    | .error _ => throw "outcome.failure: missing"
  let configJ ← objField j "fixture" "config"
  let drive := match configJ.getObjValAs? String "drive" with
    | .ok d => d
    | .error _ => "eager"
  let mut ops : Array NativeOp := #[]
  for x in ← arrField j "fixture" "ops" do
    ops := ops.push { kind := ← strField x "ops" "op", key := ← natField x "ops" "key"
                      forced := match x.getObjValAs? Bool "forced" with
                        | .ok b => b
                        | .error _ => false }
  -- the dumper's self-check report and the synchronous engine's failure
  let checksJ ← objField j "fixture" "checks"
  let dumperChecks ← (← arrField checksJ "checks" "failures").toList.mapM fun x =>
    match x.getStr? with
    | .ok s => pure s
    | .error _ => throw "checks.failures: expected strings"
  let syncFailureAccess ← match checksJ.getObjVal? "sync" with
    | .ok sj@(Json.obj _) =>
      match sj.getObjVal? "sync_failure" with
      | .ok Json.null => pure none
      | .ok f => some <$> natField f "checks.sync.sync_failure" "access"
      | .error _ => pure none
    | _ => pure none
  let optBool (k : String) : P Bool := match configJ.getObjVal? k with
    | .ok (Json.bool b) => pure b
    | .ok Json.null => pure false
    | .ok _ => throw s!"config.{k}: expected a boolean"
    | .error _ => pure false
  let mut published : HashMap Nat Nat := {}
  for x in ← arrField outcome "outcome" "levels" do
    let ℓ ← natField x "outcome.levels" "level"
    if published.contains ℓ then throw s!"outcome.levels: level {ℓ} listed twice"
    published := published.insert ℓ (← natField x "outcome.levels" "published")
  return { cfg, selected, valueBytes, prefixFlushes := r0, stashBuckets := s,
           drive, lastOrdinal := some (← natField outcome "outcome" "last_level_one_ordinal"), published,
           initShape := sh.init, ops, dumperChecks, syncFailureAccess
           skipTopContents := ← optBool "skip_top_contents"
           seedPrefixes := ← natField outcome "outcome" "seed_prefixes"
           accessesRequested := ← optNatField configJ "config" "accesses_requested"
           viewRequested := ← optBool "view", syncCheck := ← optBool "sync_check"
           viewLimit := ← optNatField configJ "config" "view_limit"
           batch := (← optNatField configJ "config" "batch").getD 0
           keyBound := ← optNatField configJ "config" "key_bound"
           addressSpace := ← optNatField configJ "config" "address_space"
           direct := sh.direct, sep := sh.sep, top := sh.top, prep := sh.prep,
           init, units, tables, words := ← parseWords (← objField j "fixture" "words")
           accesses := ← natField outcome "outcome" "accesses"
           prefixes := ← natField outcome "outcome" "prefixes", failure }

def parseReplay (text : String) : P Replay := do
  parseReplayJson (← Json.parse text)

/-! ### The model's inputs -/

/-- The model's inputs built from a fixture. -/
structure Env where
  cfg : Config
  sh : Shapes
  tr : Trace
  words : Words

/-- A placeholder shape for rows the fixture does not list; `Replay.missingShapes`
reports every such row the run needs before anything is evaluated. -/
def noDirect : DGeom := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, .direct⟩
def noSep : SepGeom := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
def noTop : TopGeom := ⟨0, 0, 0, 0, 0, false, 0, 0, 0, 0⟩
def noPrep : TPGeom := ⟨0, 0, 0, 0, 0, 0, 0, false⟩

/-- The engine's unshadowed flag: meta bit `0x20`, bit `8 (V - 1) + 5` of the value. -/
def unshOf (valueBytes : Nat) (r : MRec) : Bool := r.val.testBit (8 * (valueBytes - 1) + 5)

def Replay.env (rp : Replay) : Env :=
  let cfg := rp.cfg
  { cfg
    sh := ⟨fun d => rp.direct.getD d noDirect, fun ℓ d => rp.sep.getD (ℓ, d) noSep,
           rp.top.getD noTop, rp.prep.getD noPrep, rp.initShape.getD noPrep⟩
    tr := ⟨fun i => rp.units.getD (cfg.seed 1 + 1 + i) [], rp.init, unshOf rp.valueBytes⟩
    words := fun ℓ v k => ((rp.words.get? (ℓ, v)).bind (·.get? (LogicalKey.toNat k))).getD 0 }

/-! ### An evaluation-order twin of level one's producer

The trusted `buildB` reads every winner through `DirectRecords.record rs i =
(winners rs)[i]!`, which recomputes the quadratic `winners` at every index
and every home, and `bRemaining` recomputes `bHomes` per chunk: a full
level-one ordinal (512 records) takes minutes. `buildBFast` is the same
definition with the winners and the homes computed once; `buildBFast_eq`
proves it equal to `buildB`, and `runJobFast_eq`, `levelOneStepFast_eq` and
`stepFast_eq` lift the equation to `runJob`, `levelOneStep` and `step`. The
evaluator runs the twins; what it computes is the model's value by these
theorems. -/

theorem record_eq (rs : List MRec) :
    DirectRecords.record rs = fun i => (DirectPrefix.winners rs).toArray[i]! := by
  funext i
  simp only [DirectRecords.record, List.getElem!_toArray]

theorem home_eq (rs : List MRec) (word : LogicalKey → Nat) (U : Nat) :
    DirectRecords.home rs word U = fun i => DirectPrefix.cachedHome word U (DirectPrefix.winners rs).toArray[i]! := by
  funext i
  simp only [DirectRecords.home, record_eq]

/-- `buildB` with the winners and the homes computed once. -/
def buildBFast (g : DGeom) (word : LogicalKey → Nat) (inp : DirectJob.Inputs) : Except CheckEvent Table :=
  let ws := (DirectPrefix.winners inp.bRecords).toArray
  let homes := DirectGroups.groups g.U (fun i => DirectPrefix.cachedHome word g.U ws[i]!)
    (bChunks inp).flatten
  match drainBounded .produceB (bSite g) g.bCapacity 0 []
      ((bChunks inp).map fun source => DirectRemaining.run 64 source homes) with
  | .error e => .error e
  | .ok tier => .ok ⟨(DirectB.main 64 homes).map (List.map fun i => ws[i]!), tier.map fun i => ws[i]!⟩

theorem buildBFast_eq (g : DGeom) (word : LogicalKey → Nat) (inp : DirectJob.Inputs) :
    buildBFast g word inp = buildB g word inp := by
  simp only [buildBFast, buildB, bRemaining, bHomes, DirectRecords.restore, home_eq, record_eq]
  split <;> simp_all

/-- `runJob` with `buildBFast`. -/
def runJobFast (g : DGeom) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs) : LaneResult :=
  if ¬ g.Valid then .rejected .geometry
  else if ¬ inp.Valid g oldWord then .rejected .inputs
  else if g.digit = 1 then
    match buildBFast g word inp with
    | .error e => .failed e
    | .ok b => .published (finishOutput g b.bLanes (b.tier.map some))
  else match prepareA g word inp.aMain with
    | .error e => .failed e
    | .ok a => match buildBFast g word inp with
      | .error e => .failed e
      | .ok b => match distributeABounded g word (aOperational a inp.aTier b.tier) with
        | .error e => .failed e
        | .ok leaves => match finishBounded g word b a.main leaves with
          | .error e => .failed e
          | .ok out => .published out

theorem runJobFast_eq (g : DGeom) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs) :
    runJobFast g oldWord word inp = runJob g oldWord word inp := by
  simp only [runJobFast, runJob, buildBFast_eq]
  repeat' (first | rfl | (split <;> simp_all))

/-- `levelOneStep` with `runJobFast`. -/
def levelOneStepFast (g : DGeom) (oldWord word : LogicalKey → Nat) (prev : Output) (units : List Bucket) :
    Output :=
  match runJobFast g oldWord word (adopt prev units) with
  | .published out => out
  | _ => (referenceFallback g (adopt prev units)).toOutput

theorem levelOneStepFast_eq (g : DGeom) (oldWord word : LogicalKey → Nat) (prev : Output)
    (units : List Bucket) :
    levelOneStepFast g oldWord word prev units = levelOneStep g oldWord word prev units := by
  simp only [levelOneStepFast, levelOneStep, runJobFast_eq]
  split <;> simp_all

/-- `step` with `levelOneStepFast`. -/
def stepFast (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (ℓ v : Nat)
    (prev carry : Output) : Output :=
  let d := Config.digitOf (cfg.fanout ℓ) v
  if ℓ = cfg.levels then
    (topReference sh.top tr.unsh (jobWord cfg words ℓ v)
      (finishInputs (prepOutput cfg sh tr words v prev) carry)).output
  else if ℓ = 1 then
    levelOneStepFast (sh.direct d) (jobWord cfg words 1 (v - 1)) (jobWord cfg words 1 v)
      (if d = 1 then emptyOutput else prev) (tr.units (v - cfg.seed 1 - 1))
  else if d = 1 then carry
  else (sReference engineRule (sh.sep ℓ d) (jobWord cfg words ℓ v) (sepInputs (sh.sep ℓ d) prev carry)).output

theorem stepFast_eq (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (ℓ v : Nat)
    (prev carry : Output) :
    stepFast cfg sh tr words ℓ v prev carry = step cfg sh tr words ℓ v prev carry := by
  simp only [stepFast, step, levelOneStepFast_eq]

/-! ### Memoised evaluation of `table` -/

/-- The defining equation of `table`, which `Env.evalTable` follows. -/
theorem table_eq (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (ℓ v : Nat) :
    table cfg sh tr words ℓ v =
      if ℓ = 0 ∨ cfg.levels < ℓ ∨ v ≤ cfg.seed ℓ then base cfg sh tr words ℓ
      else step cfg sh tr words ℓ v (table cfg sh tr words ℓ (v - 1))
        (if ℓ = 1 then emptyOutput else table cfg sh tr words (ℓ - 1) (v * cfg.fanout (ℓ - 1))) := by
  rw [table]

abbrev Memo := HashMap (Nat × Nat) Output

/-- Every memo entry `(ℓ, v)` is the model's `table ℓ v`. -/
def Env.Sound (e : Env) (m : Memo) : Prop :=
  ∀ ℓ v o, m[(ℓ, v)]? = some o → o = table e.cfg e.sh e.tr e.words ℓ v

/-- Whether `(ℓ, v)` is at or below its level's base (the first branch of `table`). -/
abbrev Env.IsBase (e : Env) (ℓ v : Nat) : Prop := ℓ = 0 ∨ e.cfg.levels < ℓ ∨ v ≤ e.cfg.seed ℓ

/-- A table from the memo, or the base table at and below the seeded counter. -/
def Env.lookup (e : Env) (m : Memo) (ℓ v : Nat) : Option Output :=
  match m[(ℓ, v)]? with
  | some o => some o
  | none => if e.IsBase ℓ v then some (base e.cfg e.sh e.tr e.words ℓ) else none

/-- The carry a job reads: nothing at level one, else the memo's table of the
level below. -/
def Env.carryFor (e : Env) (m : Memo) (ℓ v : Nat) : Option Output :=
  if ℓ = 1 then some emptyOutput else e.lookup m (ℓ - 1) (v * e.cfg.fanout (ℓ - 1))

/-- One table from the memo: the right-hand side of `table_eq` with the memo's
entries for the level's previous table and the carry (and `stepFast` for
`step`). -/
def Env.evalTable (e : Env) (m : Memo) (ℓ v : Nat) : Option Output :=
  if e.IsBase ℓ v then some (base e.cfg e.sh e.tr e.words ℓ)
  else match e.lookup m ℓ (v - 1), e.carryFor m ℓ v with
    | some prev, some carry => some (stepFast e.cfg e.sh e.tr e.words ℓ v prev carry)
    | _, _ => none

theorem Env.sound_empty (e : Env) : e.Sound {} := by
  intro ℓ v o h
  simp at h

theorem Env.lookup_sound {e : Env} {m : Memo} (h : e.Sound m) {ℓ v : Nat} {o : Output}
    (hl : e.lookup m ℓ v = some o) : o = table e.cfg e.sh e.tr e.words ℓ v := by
  unfold Env.lookup at hl
  split at hl
  · rename_i o' hm
    cases hl
    exact h _ _ _ hm
  · split at hl
    · rename_i hb
      cases hl
      rw [table_eq, ite_eq_left hb]
    · cases hl

theorem Env.carryFor_sound {e : Env} {m : Memo} (h : e.Sound m) {ℓ v : Nat} {c : Output}
    (hc : e.carryFor m ℓ v = some c) :
    c = if ℓ = 1 then emptyOutput else table e.cfg e.sh e.tr e.words (ℓ - 1) (v * e.cfg.fanout (ℓ - 1)) := by
  unfold Env.carryFor at hc
  split at hc
  · rename_i h1
    cases hc
    rw [ite_eq_left h1]
  · rename_i h1
    rw [ite_eq_right h1]
    exact lookup_sound h hc

theorem Env.evalTable_sound {e : Env} {m : Memo} (h : e.Sound m) {ℓ v : Nat} {o : Output}
    (he : e.evalTable m ℓ v = some o) : o = table e.cfg e.sh e.tr e.words ℓ v := by
  unfold Env.evalTable at he
  rw [table_eq]
  split at he
  · rename_i hb
    cases he
    rw [ite_eq_left hb]
  · rename_i hb
    rw [ite_eq_right hb]
    split at he
    · rename_i prev carry hp hc
      cases he
      rw [stepFast_eq, ← lookup_sound h hp, ← carryFor_sound h hc]
    · cases he

theorem Env.Sound.insert {e : Env} {m : Memo} (h : e.Sound m) {ℓ v : Nat} {o : Output}
    (ho : o = table e.cfg e.sh e.tr e.words ℓ v) : e.Sound (m.insert (ℓ, v) o) := by
  intro ℓ' v' o' h'
  rw [HashMap.getElem?_insert] at h'
  split at h'
  · rename_i hk
    simp only [beq_iff_eq, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    cases h'
    exact ho
  · exact h _ _ _ h'

theorem Env.Sound.erase {e : Env} {m : Memo} (h : e.Sound m) (k : Nat × Nat) :
    e.Sound (m.erase k) := by
  intro ℓ v o h'
  rw [HashMap.getElem?_erase] at h'
  split at h'
  · cases h'
  · exact h _ _ _ h'

/-! ### The potential jobs' bounded results on memo tables -/

/-- `levelOneResult` with the previous partial supplied. -/
def levelOneResultOf (e : Env) (v : Nat) (prev : Output) : LaneResult :=
  runJobFast (e.sh.direct (Config.digitOf (e.cfg.fanout 1) v)) (jobWord e.cfg e.words 1 (v - 1))
    (jobWord e.cfg e.words 1 v)
    (adopt (if Config.digitOf (e.cfg.fanout 1) v = 1 then emptyOutput else prev)
      (e.tr.units (v - e.cfg.seed 1 - 1)))

theorem levelOneResultOf_eq (e : Env) (v : Nat) :
    levelOneResultOf e v (table e.cfg e.sh e.tr e.words 1 (v - 1)) =
      levelOneResult e.cfg e.sh e.tr e.words v := by
  simp only [levelOneResultOf, levelOneResult, levelOneInputs, runJobFast_eq]

/-- `sepResult` with the previous partial and the carry supplied. -/
def sepResultOf (e : Env) (ℓ v : Nat) (prev carry : Output) : Except STest Output :=
  sJob engineRule (e.sh.sep ℓ (Config.digitOf (e.cfg.fanout ℓ) v)) (jobWord e.cfg e.words ℓ v)
    (sepInputs (e.sh.sep ℓ (Config.digitOf (e.cfg.fanout ℓ) v)) prev carry)

theorem sepResultOf_eq (e : Env) (ℓ v : Nat) :
    sepResultOf e ℓ v (table e.cfg e.sh e.tr e.words ℓ (v - 1)) (carryOf e.cfg e.sh e.tr e.words ℓ v) =
      sepResult e.cfg e.sh e.tr e.words ℓ v := rfl

/-- `prepResult` with the previous top table supplied. -/
def prepResultOf (e : Env) (v : Nat) (prevTop : Output) : Except TPTest Output :=
  tpJob engineRule e.sh.prep e.tr.unsh (jobWord e.cfg e.words e.cfg.levels v) (prepInputs prevTop)

theorem prepResultOf_eq (e : Env) (v : Nat) :
    prepResultOf e v (table e.cfg e.sh e.tr e.words e.cfg.levels (v - 1)) =
      prepResult e.cfg e.sh e.tr e.words v := rfl

/-- `finishResult` with the previous top table and the carry supplied. -/
def finishResultOf (e : Env) (v : Nat) (prevTop carry : Output) : Except Test Output :=
  topJob e.sh.top e.tr.unsh (jobWord e.cfg e.words e.cfg.levels v)
    (finishInputs (prepOutput e.cfg e.sh e.tr e.words v prevTop) carry)

theorem finishResultOf_eq (e : Env) (v : Nat) :
    finishResultOf e v (table e.cfg e.sh e.tr e.words e.cfg.levels (v - 1))
        (carryOf e.cfg e.sh e.tr e.words e.cfg.levels v) =
      finishResult e.cfg e.sh e.tr e.words v := rfl

/-- `jobFails` on an ordinary job, with the previous partial and the carry supplied. -/
def ordinaryFailsOf (e : Env) (ℓ o : Nat) (prev carry : Output) : Bool :=
  if ℓ = 1 then
    match levelOneResultOf e o prev with
    | .published _ => false
    | _ => true
  else if Config.digitOf (e.cfg.fanout ℓ) o = 1 then false
  else !(sepResultOf e ℓ o prev carry).toBool

theorem ordinaryFailsOf_eq (e : Env) (ℓ o : Nat) :
    ordinaryFailsOf e ℓ o (table e.cfg e.sh e.tr e.words ℓ (o - 1)) (carryOf e.cfg e.sh e.tr e.words ℓ o) =
      jobFails e.cfg e.sh e.tr e.words (.ordinary ℓ o) := by
  by_cases h1 : ℓ = 1
  · subst h1
    simp only [ordinaryFailsOf, jobFails, ite_true, levelOneResultOf_eq]
    generalize levelOneResult e.cfg e.sh e.tr e.words o = r
    cases r <;> rfl
  · simp only [ordinaryFailsOf, jobFails, h1, ite_false, sepResultOf_eq]

/-! ### Selected-geometry replay premises

This replay checks the trace premises used by the selected
geometries: `TracePremises cfg N tr` and `UnshPromise cfg sh tr` (at a chunk
horizon the load, carry and model are unchanged). Both are properties of the
logical trace, so every replayed run checks them on the trace it observed.
The certified geometry is `geometry31`; fixtures of other configurations keep
their own scope and do not establish a separate capacity or adaptive-security endpoint.

**`TracePremises`.** The env's trace `e.tr` returns the captured units at the
captured ordinals and `[]` everywhere else, where every conjunct holds
vacuously; so checking each conjunct at every captured ordinal (and on the
initialization input) checks `TracePremises cfg N e.tr` exactly. Each conjunct
is decided literally (`List.Nodup` by `decide`, the length bound, `key < N`);
first violations are located separately for the report. `N` is
`config.key_bound` (the dumper's bound on universe keys, default the engine's
`CapacityEntries = 32 T`), else `config.address_space`. The two selected
configurations and every other non-`geometry31` configuration use `N ≤ 2^27`;
`geometry31` checks `N ≤ 2^31`; both also require `N ≤ address_space`.
The `N_le_2^27` field is informational for geometry31; `N_check` and
`key_capacity_limit` report the applicable check. The dumper's forced keys are searched upward from 1 and pass `32 T`
when a bucket must hold more than its share of the address space (every
forced top overflow): such traces violate `keys`, by construction, and the
report says whether every violating key is a forced one.

**`UnshPromise`, exact form at the run's words.** For every top finish `o`
the run evaluates (not at a selected configuration, whose top is never
evaluated), the instance of the promise at the fixture's words:
`unshInstance e.tr.unsh (finishInputsOf e o prevTop carry)`, which is
`UnshInstance … (finishInputsAt cfg sh tr words o)` by `finishInputsOf_eq` and
`unshInstance_iff` when `prevTop` and `carry` are the model's tables (memo
entries, `Env.evalTable_sound`).

**`UnshPromise`, word-independent sufficient form.** The premise quantifies
over every tape, and the run sees one. The sufficient form checks, at every
evaluated finish, that every flagged tombstone of the carry B (main *and*
tier) has no live record with its key anywhere in the preparation's whole
output (C *and* R) nor in the previous top table. On the preparation's output
this is `UnshSufficient unsh inp` (`inp.bAll` is the carry's records,
`inp.aAll` the preparation output's records), and `UnshSufficient.instance`
proves that it implies the exact instance at every input `inp'` whose A and B
records are among `inp`'s. That covers every tape `w'` once the finish's input
*record sets* are word-independent (`JobContracts.finishRecsA/B`; only the
positions, main against tier and C against R, move with the words). Those
contracts are proved under the promise itself, but only at earlier finishes:
the record sets of finish `o`'s inputs are built from top table `o - 1` and
the carry, and with the promise at finishes `< o` (under every tape) each
earlier finish's output keeps each key's newest live version, whatever the
placement. So, by induction over the top ordinals, the sufficient form at
every potential finish under one tape implies `UnshPromise`: this is
`UnshReductionProof.unshPromise_of_sufficient` (`Proofs/UnshReduction.lean`,
kernel-checked, not a registered statement). The replay evaluates only the
finishes its run reaches, so it checks the lemma's hypothesis only at those.
(Natively the top publishes no tombstones, so C and R are live; a flagged
tombstone whose key is anywhere in them is a violation.)

The report counts the flagged tombstones examined (in B's tier for the exact
form, in all of B for the sufficient one), how many have their key in the
older tables at all, and the carry's *unflagged* tombstones that do shadow a
live older copy (where a wrongly set flag would be caught), so that a vacuous
pass is visible.
-/

/-- `finishInputsAt` with the previous top table and the carry supplied. -/
def finishInputsOf (e : Env) (v : Nat) (prevTop carry : Output) : TopInputs :=
  finishInputs (prepOutput e.cfg e.sh e.tr e.words v prevTop) carry

theorem finishInputsOf_eq (e : Env) (v : Nat) :
    finishInputsOf e v (table e.cfg e.sh e.tr e.words e.cfg.levels (v - 1))
        (carryOf e.cfg e.sh e.tr e.words e.cfg.levels v) =
      finishInputsAt e.cfg e.sh e.tr e.words v := rfl

/-- The finish's bounded result on the supplied inputs (computed once). -/
theorem finishResultOf_inputs (e : Env) (v : Nat) (prevTop carry : Output) :
    finishResultOf e v prevTop carry =
      topJob e.sh.top e.tr.unsh (jobWord e.cfg e.words e.cfg.levels v) (finishInputsOf e v prevTop carry) :=
  rfl

/-- The body of `UnshPromise` at one finish's inputs (after `words` and `o`). -/
def UnshInstance (unsh : MRec → Bool) (inp : TopInputs) : Prop :=
  ∀ r ∈ inp.bTier, earlyDrop unsh r = true →
    ∀ c ∈ inp.cMain.flatMap Bucket.recs, c.key = r.key → c.tomb = true

/-- `UnshInstance`, decided. -/
def unshInstance (unsh : MRec → Bool) (inp : TopInputs) : Bool :=
  let cs := inp.cMain.flatMap Bucket.recs
  inp.bTier.all fun r => !earlyDrop unsh r || cs.all fun c => c.key != r.key || c.tomb

theorem unshInstance_iff (unsh : MRec → Bool) (inp : TopInputs) :
    unshInstance unsh inp = true ↔ UnshInstance unsh inp := by
  simp only [unshInstance, UnshInstance, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    bne_iff_ne, ne_eq]
  constructor
  · intro h r hr hd c hc hk
    rcases h r hr with h1 | h1
    · rw [hd] at h1
      cases h1
    · rcases h1 c hc with h2 | h2
      · exact absurd hk h2
      · exact h2
  · intro h r hr
    by_cases hd : earlyDrop unsh r = true
    · refine Or.inr fun c hc => ?_
      by_cases hk : c.key = r.key
      · exact Or.inr (h r hr hd c hc hk)
      · exact Or.inl hk
    · exact Or.inl (by simpa using hd)

/-- The exact check at a finish evaluated on the model's tables is the
premise's instance at the run's words. -/
theorem unshInstance_model (e : Env) (v : Nat) :
    unshInstance e.tr.unsh (finishInputsOf e v (table e.cfg e.sh e.tr e.words e.cfg.levels (v - 1))
        (carryOf e.cfg e.sh e.tr e.words e.cfg.levels v)) = true ↔
      UnshInstance e.tr.unsh (finishInputsAt e.cfg e.sh e.tr e.words v) := by
  rw [finishInputsOf_eq, unshInstance_iff]

/-- The sufficient form on one finish's inputs: no flagged tombstone of B
(main or tier) has a live record with its key in A (C or R). -/
def UnshSufficient (unsh : MRec → Bool) (inp : TopInputs) : Prop :=
  ∀ r ∈ inp.bAll, earlyDrop unsh r = true → ∀ c ∈ inp.aAll, c.key = r.key → c.tomb = true

/-- The sufficient form implies the exact instance at any inputs whose A and
B records are among the checked inputs' (another tape's placement of the same
records). -/
theorem UnshSufficient.instance {unsh : MRec → Bool} {inp inp' : TopInputs}
    (hA : ∀ x ∈ inp'.aAll, x ∈ inp.aAll) (hB : ∀ x ∈ inp'.bAll, x ∈ inp.bAll)
    (h : UnshSufficient unsh inp) : UnshInstance unsh inp' := by
  intro r hr hd c hc hk
  exact h r (hB r (List.mem_append_right _ hr)) hd c (hA c (List.mem_append_left _ hc)) hk

/-- The preparation output's records are A's, the carry's records are B's. -/
theorem finishInputs_all (prepOut carry : Output) :
    (finishInputs prepOut carry).aAll = prepOut.records ∧
      (finishInputs prepOut carry).bAll = carry.records := ⟨rfl, rfl⟩

/-- The key history of a reported key: its operations (index, kind, forced), the last `n`. -/
def keyHistory (ops : Array NativeOp) (k : Nat) (n : Nat := 12) : Json := Id.run do
  let mut out : Array Json := #[]
  for h : i in [0:ops.size] do
    let o := ops[i]
    if o.key == k then
      out := out.push (Json.arr (#[toJson i, toJson o.kind] ++ (if o.forced then #[toJson "forced"] else #[])))
  return Json.mkObj [("ops", toJson out.size), ("last", Json.arr (out.extract (out.size - min n out.size) out.size))]

/-- The trace premises: the failed conjuncts' names and the report. -/
def tracePremises (rp : Replay) (e : Env) (N : Nat) (limit : Nat := 5) : List String × Json := Id.run do
  let cfg := e.cfg
  let bound := cfg.load * cfg.carry1
  let ords := (rp.units.toArray.map (·.1)).qsort (· < ·)
  let forced : HashSet Nat := rp.ops.foldl (fun s o => if o.forced then s.insert o.key else s) {}
  let mut nodupBad := 0
  let mut nodupShown : List Json := []
  let mut loadBad := 0
  let mut loadShown : List Json := []
  let mut maxLoad := 0
  let mut maxLoadAt := 0
  let mut keysBad := 0
  let mut keysAllForced := true
  let mut keysShown : List Json := []
  let mut maxKey := 0
  let mut recs := 0
  let mut checkedOrds := 0
  for o in ords do
    if o ≤ cfg.seed 1 then continue
    checkedOrds := checkedOrds + 1
    let us := e.tr.units (o - cfg.seed 1 - 1)
    let mut j := 0
    for u in us do
      if !decide ((u.recs.map RebuildBound.Model.Rec.key).Nodup) then
        nodupBad := nodupBad + 1
        if nodupShown.length < limit then
          -- locate a repeated key
          let mut seen : HashSet LogicalKey := {}
          let mut dup := none
          for r in u.recs do
            if dup.isNone then
              if seen.contains r.key then dup := some r.key
              seen := seen.insert r.key
          nodupShown := nodupShown ++ [Json.mkObj [("ordinal", toJson o), ("unit", toJson j),
            ("key", toJson (dup.map LogicalKey.toNat))]]
      j := j + 1
    let rs := DirectMasks.records us
    recs := recs + rs.length
    if rs.length > maxLoad then
      maxLoad := rs.length
      maxLoadAt := o
    if !decide (rs.length ≤ bound) then
      loadBad := loadBad + 1
      if loadShown.length < limit then
        loadShown := loadShown ++ [Json.mkObj [("ordinal", toJson o), ("records", toJson rs.length)]]
    for x in rs do
      maxKey := max maxKey (LogicalKey.toNat x.key)
      if !decide (LogicalKey.toNat x.key < N) then
        keysBad := keysBad + 1
        if !forced.contains (LogicalKey.toNat x.key) then keysAllForced := false
        if keysShown.length < limit then
          keysShown := keysShown ++ [Json.mkObj [("ordinal", toJson o), ("key", toJson (LogicalKey.toNat x.key)),
            ("forced", toJson (forced.contains (LogicalKey.toNat x.key)))]]
  let initNodup := decide ((e.tr.init.map RebuildBound.Model.Rec.key).Nodup)
  let initBad := (e.tr.init.filter fun x => !decide (LogicalKey.toNat x.key < N))
  -- the selected configurations use `N ≤ 2^27`; `N` must not exceed the engine's address
  -- space `32 T` (a larger `key_bound` would weaken the `keys` conjunct)
  let keyCapacity := if rp.selected == some "geometry31" then 2 ^ 31 else 2 ^ 27
  let nOk := decide (N ≤ keyCapacity) && rp.addressSpace.all (N ≤ ·)
  let mut fails := []
  if !nOk then fails := fails ++ ["trace_premises.N"]
  if nodupBad != 0 then fails := fails ++ ["trace_premises.nodup"]
  if loadBad != 0 then fails := fails ++ ["trace_premises.load"]
  if keysBad != 0 then fails := fails ++ ["trace_premises.keys"]
  if !initNodup then fails := fails ++ ["trace_premises.init_nodup"]
  if !initBad.isEmpty then fails := fails ++ ["trace_premises.init_keys"]
  let verdict (b : Bool) : Json := toJson (if b then "pass" else "fail")
  let out := Json.mkObj [
    ("result", verdict fails.isEmpty),
    ("N", toJson N), ("N_source", toJson (if rp.keyBound.isSome then "key_bound" else "address_space")),
    ("address_space", toJson rp.addressSpace), ("N_le_2^27", toJson (decide (N ≤ 2 ^ 27))),
    ("N_check", verdict nOk), ("key_capacity_limit", toJson keyCapacity),
    ("ordinals", toJson checkedOrds), ("records", toJson recs),
    ("nodup", Json.mkObj [("result", verdict (nodupBad == 0)), ("violations", toJson nodupBad),
      ("first", toJson nodupShown)]),
    ("load", Json.mkObj [("result", verdict (loadBad == 0)), ("bound", toJson bound),
      ("max_records", toJson maxLoad), ("max_at_ordinal", toJson maxLoadAt), ("violations", toJson loadBad),
      ("first", toJson loadShown)]),
    ("keys", Json.mkObj ([("result", verdict (keysBad == 0)), ("max_key", toJson maxKey),
      ("violations", toJson keysBad)] ++
      (if keysBad == 0 then [] else [("all_forced", toJson keysAllForced), ("first", toJson keysShown)]))),
    ("init_nodup", verdict initNodup),
    ("init_keys", Json.mkObj [("result", verdict initBad.isEmpty), ("records", toJson e.tr.init.length),
      ("violations", toJson initBad.length)])]
  return (fails, out)

/-- The promise's counts over the evaluated top finishes. -/
structure UnshAcc where
  finishes : Nat := 0
  /-- Finishes whose exact instance (`unshInstance`) fails. -/
  exactFailed : List Nat := []
  bTierFlagged : Nat := 0
  exactViolations : Nat := 0
  exactShown : List Json := []
  carryFlagged : Nat := 0
  carryFlaggedTier : Nat := 0
  flaggedKeyOlder : Nat := 0
  suffViolations : Nat := 0
  suffShown : List Json := []
  unflaggedShadowing : Nat := 0
  /-- Unflagged tombstones of B's tier with a live copy in C's main: where the
  exact form would catch a wrongly set flag. -/
  unflaggedShadowingTier : Nat := 0
  /-- Tombstones in C or R (natively none: the top publishes no tombstones). -/
  olderTombs : Nat := 0

/-- Both forms of the promise at the finish `v`, on its inputs `inp =
finishInputsOf e v prevTop carry`. -/
def UnshAcc.check (acc : UnshAcc) (e : Env) (ops : Array NativeOp) (v : Nat) (prevTop : Output)
    (inp : TopInputs) (limit : Nat := 5) : UnshAcc := Id.run do
  let unsh := e.tr.unsh
  let cRecs := inp.cMain.flatMap Bucket.recs
  let mut acc := { acc with finishes := acc.finishes + 1 }
  if !unshInstance unsh inp then acc := { acc with exactFailed := acc.exactFailed ++ [v] }
  -- the older live records by key, most specific last: the previous top, R, C
  let mut olderLive : HashMap LogicalKey (String × MRec) := {}
  let mut olderAny : HashSet LogicalKey := {}
  for (part, rs) in [("prev_top", prevTop.records), ("r", inp.carry), ("c_main", cRecs)] do
    for c in rs do
      olderAny := olderAny.insert c.key
      if c.tomb then
        if part != "prev_top" then acc := { acc with olderTombs := acc.olderTombs + 1 }
      else olderLive := olderLive.insert c.key (part, c)
  let mut cLive : HashMap LogicalKey MRec := {}
  for c in cRecs do
    if !c.tomb then cLive := cLive.insert c.key c
  let viol (part : String) (r : MRec) (w : String) (c : MRec) : Json :=
    Json.mkObj [("finish", toJson v), ("key", toJson (LogicalKey.toNat r.key)), ("part", toJson part),
      ("tombstone", DirectJob.recordJson r), ("live", DirectJob.recordJson c), ("in", toJson w),
      ("history", keyHistory ops (LogicalKey.toNat r.key))]
  -- the exact form: B's tier against C's main
  for r in inp.bTier do
    if earlyDrop unsh r then
      acc := { acc with bTierFlagged := acc.bTierFlagged + 1 }
      if let some c := cLive.get? r.key then
        acc := { acc with exactViolations := acc.exactViolations + 1 }
        if acc.exactShown.length < limit then
          acc := { acc with exactShown := acc.exactShown ++ [viol "b_tier" r "c_main" c] }
    else if r.tomb && cLive.contains r.key then
      acc := { acc with unflaggedShadowingTier := acc.unflaggedShadowingTier + 1 }
  -- the sufficient form: all of B against everything older
  for (part, rs) in [("b_main", inp.bMain.flatMap Bucket.recs), ("b_tier", inp.bTier)] do
    for r in rs do
      if !r.tomb then continue
      if unsh r then
        acc := { acc with carryFlagged := acc.carryFlagged + 1 }
        if part == "b_tier" then acc := { acc with carryFlaggedTier := acc.carryFlaggedTier + 1 }
        if olderAny.contains r.key then acc := { acc with flaggedKeyOlder := acc.flaggedKeyOlder + 1 }
        if let some (w, c) := olderLive.get? r.key then
          acc := { acc with suffViolations := acc.suffViolations + 1 }
          if acc.suffShown.length < limit then
            acc := { acc with suffShown := acc.suffShown ++ [viol part r w c] }
      else if olderLive.contains r.key then
        acc := { acc with unflaggedShadowing := acc.unflaggedShadowing + 1 }
  return acc

/-- The promise's failed forms and its report (`none`: the top was not evaluated). -/
def UnshAcc.report (acc : Option UnshAcc) : List String × Json :=
  match acc with
  | none => ([], Json.mkObj [("result", "n/a"),
      ("reason", "top not evaluated (selected configuration)")])
  | some a =>
    let exactOk := a.exactFailed.isEmpty
    let suffOk := a.suffViolations == 0
    let fails := (if exactOk then [] else ["unsh_promise.exact"]) ++
      (if suffOk then [] else ["unsh_promise.sufficient"])
    -- the located exact violations agree with the decided instance
    let agree := (a.exactViolations == 0) == exactOk
    let fails := if agree then fails else fails ++ ["unsh_promise.internal"]
    (fails, Json.mkObj [
      ("result", toJson (if fails.isEmpty then "pass" else "fail")),
      ("finishes", toJson a.finishes),
      ("unsh_checked", toJson a.carryFlagged),
      ("exact", Json.mkObj [("result", toJson (if exactOk then "pass" else "fail")),
        ("flagged_in_b_tier", toJson a.bTierFlagged),
        ("unflagged_shadowing_in_b_tier", toJson a.unflaggedShadowingTier),
        ("violations", toJson a.exactViolations),
        ("failed_finishes", toJson (a.exactFailed.take 10)), ("first", toJson a.exactShown)]),
      ("sufficient", Json.mkObj [("result", toJson (if suffOk then "pass" else "fail")),
        ("flagged_in_b", toJson a.carryFlagged), ("flagged_in_b_tier", toJson a.carryFlaggedTier),
        ("flagged_key_in_older", toJson a.flaggedKeyOlder), ("violations", toJson a.suffViolations),
        ("first", toJson a.suffShown)]),
      ("unflagged_shadowing", toJson a.unflaggedShadowing),
      ("older_tombstones", toJson a.olderTombs)])

/-! ### Failure classes -/

/-- A coarse failure class shared by the engine's messages and the four models'
tests: `route` (a butterfly or route stash), `radix`, `dfs`, `insertion`
(the merge stash), `drain` (an output or B tier). -/
def nativeClass (msg : String) : String :=
  let tok := match msg.splitOn "ran out of room at " with
    | _ :: rest :: _ => (rest.splitOn ";").headD ""
    | _ => ""
  let has (s : String) := (tok.splitOn s).length > 1
  if tok.isEmpty then "unknown"
  else if has "dfs" then "dfs"
  else if has "radix" then "radix"
  else if has "drain" then "drain"
  else if has "fixed-merge" then "insertion"
  else if has "butterfly" || has "route-level" || has "cross-level" then "route"
  else "unknown"

/-- The native kind token of a failure message (`… ran out of room at <kind>;`). -/
def nativeKind (msg : String) : String :=
  match msg.splitOn "ran out of room at " with
  | _ :: rest :: _ => (rest.splitOn ";").headD ""
  | _ => ""

def levelOneClass : RebuildBound.Model.DirectJob.Site → String
  | .route _ _ => "route" | .radix => "radix" | .dfs _ _ => "dfs"
  | .bTier => "drain" | .outputTier => "drain" | .insertion => "insertion"

def sepClass : STest → String
  | .stash _ _ => "route" | .radix => "radix" | .dfs _ _ => "dfs"
  | .insertion => "insertion" | .drain => "drain"

def topClass : Test → String
  | .stash _ => "route" | .dfs _ _ => "dfs" | .insertion => "insertion" | .drain => "drain"

def tpClass : TPTest → String
  | .stash _ => "route" | .dfs _ _ => "dfs" | .drain => "drain"

/-! ### Evaluated jobs -/

/-- A potential job evaluated on the memo: its time, whether its bounded result
is not a publication, and on failure the model's test and class. -/
structure JobOutcome where
  job : JobId
  time : Nat
  fails : Bool
  test : String := ""
  cls : String := ""
  /-- Evaluated with an empty carry because its carry completes after the run
  (a speculative native start; only an A-side failure is conclusive). -/
  speculative : Bool := false

def jobJson : JobId → List (String × Json)
  | .ordinary ℓ o => [("job", "ordinary"), ("level", toJson ℓ), ("ordinal", toJson o)]
  | .topPrepare o => [("job", "top_prepare"), ("ordinal", toJson o)]
  | .topFinish o => [("job", "top_finish"), ("ordinal", toJson o)]
  | .initialization => [("job", "initialization")]

def JobOutcome.toJson (j : JobOutcome) : Json :=
  Json.mkObj (jobJson j.job ++ [("time", Lean.toJson j.time), ("fails", Lean.toJson j.fails)] ++
    (if j.fails then [("test", Lean.toJson j.test), ("class", Lean.toJson j.cls)] else []) ++
    (if j.speculative then [("speculative", Lean.toJson true)] else []))

def levelOneOutcome (e : Env) (v : Nat) (prev : Output) : JobOutcome :=
  let job := JobId.ordinary 1 v
  let fails := ordinaryFailsOf e 1 v prev emptyOutput
  match levelOneResultOf e v prev with
  | .published _ => { job, time := jobTime e.cfg job, fails }
  | .failed ev =>
    { job, time := jobTime e.cfg job, fails,
      test := (DirectJob.eventJson ev).compress, cls := levelOneClass ev.id.site }
  | .rejected r =>
    { job, time := jobTime e.cfg job, fails, test := s!"rejected {repr r}", cls := "rejected" }

def sepOutcome (e : Env) (ℓ v : Nat) (prev carry : Output) : JobOutcome :=
  let job := JobId.ordinary ℓ v
  let fails := ordinaryFailsOf e ℓ v prev carry
  if Config.digitOf (e.cfg.fanout ℓ) v = 1 then { job, time := jobTime e.cfg job, fails }
  else match sepResultOf e ℓ v prev carry with
    | .ok _ => { job, time := jobTime e.cfg job, fails }
    | .error t => { job, time := jobTime e.cfg job, fails, test := Sep.testDetail t, cls := sepClass t }

def prepOutcome (e : Env) (v : Nat) (prevTop : Output) : JobOutcome :=
  let job := JobId.topPrepare v
  match prepResultOf e v prevTop with
  | .ok _ => { job, time := jobTime e.cfg job, fails := false }
  | .error t => { job, time := jobTime e.cfg job, fails := true, test := TP.testDetail t, cls := tpClass t }

/-- On `inp = finishInputsOf e v prevTop carry`: `finishResultOf e v prevTop
carry` (`finishResultOf_inputs`), with the preparation computed once. -/
def finishOutcome (e : Env) (v : Nat) (inp : TopInputs) : JobOutcome :=
  let job := JobId.topFinish v
  match topJob e.sh.top e.tr.unsh (jobWord e.cfg e.words e.cfg.levels v) inp with
  | .ok _ => { job, time := jobTime e.cfg job, fails := false }
  | .error t => { job, time := jobTime e.cfg job, fails := true, test := Top.testDetail t, cls := topClass t }

def initOutcome (e : Env) : JobOutcome :=
  match initResult e.cfg e.sh e.tr e.words with
  | .ok _ => { job := .initialization, time := 0, fails := false }
  | .error t => { job := .initialization, time := 0, fails := true, test := TP.testDetail t, cls := tpClass t }

/-! ### Identification and comparison of native tables -/

/-- The product `b_1 ⋯ b_(ℓ-1)`: level `ℓ`'s ordinal `v` has time `v · period ℓ`. -/
def period (cfg : Config) (ℓ : Nat) : Nat := (cfg.fanouts.take (ℓ - 1)).foldr (· * ·) 1

/-- The coordinate the schema assigns to a native table. -/
def coordOf (cfg : Config) (t : NativeTable) : Nat × Nat :=
  let ℓ := if t.slotKind == "inbox" then t.owner - 1 else t.owner
  (ℓ, t.window.2 / cfg.carryPositions ℓ)

/-- The empty top every engine publishes at construction (`DescribeEmptyTop`):
family `(L, 0)`, window `[0, 1)`. Uninitialized, it is top ordinal 0, the
model's base table (schema, "Exception"); initialized, it precedes
`Initialize` and is compared with the empty start's base table (the model's
initialized base is the initialization's output at `(L, s_L)`). -/
def isEmptyTop (cfg : Config) (t : NativeTable) : Bool :=
  t.slotKind != "inbox" && t.owner == cfg.levels &&
    t.family == (cfg.levels, 0) && t.window == (0, 1)

def lj (l : List (String × Json)) : List (String × Json) := l

def recJson : Option MRec → Json
  | none => Json.null
  | some r => DirectJob.recordJson r

def stripTrailing (l : List (Option MRec)) : List (Option MRec) :=
  (l.reverse.dropWhile Option.isNone).reverse

/-- Lane-level differences between two lane lists, as `(index, native, model)`. -/
def laneDiffs (nat model : List (Option MRec)) : List (Nat × Option MRec × Option MRec) :=
  let n := max nat.length model.length
  (List.range n).filterMap fun i =>
    let a := nat.getD i none
    let b := model.getD i none
    if a == b then none else some (i, a, b)

/-- The structural checks of a native table against its coordinate (family,
window, main width; the window's exact division). -/
def structuralFaults (cfg : Config) (t : NativeTable) : List (String × Json) := Id.run do
  let (ℓ, v) := coordOf cfg t
  let L := cfg.levels
  let cp := cfg.carryPositions ℓ
  let mut out := []
  if ℓ == 0 || L < ℓ then
    return [("level", Json.mkObj [("native", toJson ℓ), ("levels", toJson L)])]
  if isEmptyTop cfg t then
    if t.mainBuckets != cfg.carry ℓ * cfg.topDigit then
      out := out ++ [("main_buckets", Json.mkObj [("native", toJson t.mainBuckets),
        ("model", toJson (cfg.carry ℓ * cfg.topDigit))])]
    return out
  if cp == 0 || t.window.2 % cp != 0 then
    out := out ++ [("window", Json.mkObj [("native", toJson [t.window.1, t.window.2]),
      ("carry_positions", toJson cp)])]
  let fam := familyOf cfg ℓ v
  if t.family != fam then
    out := out ++ [("family", Json.mkObj [("native", toJson [t.family.1, t.family.2]),
      ("model", toJson [fam.1, fam.2])])]
  if ℓ < L then
    let d := Config.digitOf (cfg.fanout ℓ) v
    if t.window.1 + d * cp != t.window.2 then
      out := out ++ [("window", Json.mkObj [("native", toJson [t.window.1, t.window.2]),
        ("model", toJson [t.window.2 - d * cp, t.window.2])])]
    if t.mainBuckets != d * cfg.carry ℓ then
      out := out ++ [("main_buckets", Json.mkObj [("native", toJson t.mainBuckets),
        ("model", toJson (d * cfg.carry ℓ))])]
  else
    if t.window.1 != 0 then
      out := out ++ [("window", Json.mkObj [("native", toJson [t.window.1, t.window.2]),
        ("model", toJson [0, t.window.2])])]
    let T := cfg.carry ℓ * cfg.topDigit
    if t.mainBuckets != T then
      out := out ++ [("main_buckets", Json.mkObj [("native", toJson t.mainBuckets), ("model", toJson T)])]
  return out

/-- The lane differences of a native table against the model's table, in
JSON, at most `limit`, with their total count. -/
def compareTable (t : NativeTable) (ℓ v : Nat) (o : Output) (limit : Nat) : Nat × List Json := Id.run do
  let hdr : List (String × Json) := [("table", toJson [ℓ, v]), ("id", toJson t.id)]
  let some (tmain, ttier) := t.contents | return (0, [])
  let mut n := 0
  let mut shown : List Json := []
  if tmain.length != o.main.length then
    n := n + 1
    shown := shown ++ [Json.mkObj (hdr ++ lj [("part", "main_count"), ("native", toJson tmain.length),
      ("model", toJson o.main.length)])]
  let buckets := max tmain.length o.main.length
  for b in [0:buckets] do
    let nb := tmain.getD b []
    let mb := o.main.getD b []
    if nb != mb then
      for (i, a, c) in laneDiffs nb mb do
        n := n + 1
        if shown.length < limit then
          shown := shown ++ [Json.mkObj (hdr ++ lj [("part", "main"), ("bucket", toJson b), ("lane", toJson i),
            ("native", recJson a), ("model", recJson c)])]
  let nt := stripTrailing ttier
  let mt := stripTrailing o.tier
  if nt != mt then
    for (i, a, c) in laneDiffs nt mt do
      n := n + 1
      if shown.length < limit then
        shown := shown ++ [Json.mkObj (hdr ++ lj [("part", "tier"), ("lane", toJson i),
          ("native", recJson a), ("model", recJson c)])]
  return (n, shown)

/-! ### The run -/

/-- The jobs and family coordinates of the serialised order up to level-one
ordinal `tEnd`, without evaluating anything: for the shape and word checks. -/
def plannedCoords (cfg : Config) (evalTop : Bool) (tEnd : Nat) : List (Nat × Nat) := Id.run do
  let L := cfg.levels
  let top := if evalTop then L else L - 1
  let mut out := []
  for t in [cfg.seed 1 + 1 : tEnd + 1] do
    for ℓ in [1 : top + 1] do
      let p := period cfg ℓ
      if t % p == 0 then
        out := (ℓ, t / p) :: out
  return out.reverse

/-- Shape rows the run needs that the fixture does not list. -/
def missingShapes (rp : Replay) (evalTop : Bool) (coords : List (Nat × Nat)) : List String := Id.run do
  let cfg := rp.cfg
  let L := cfg.levels
  let mut out := []
  for (ℓ, v) in coords do
    let d := Config.digitOf (cfg.fanout ℓ) v
    if ℓ == 1 && !rp.direct.contains d then out := out ++ [s!"direct digit {d}"]
    if 1 < ℓ && ℓ < L && 1 < d && !rp.sep.contains (ℓ, d) then out := out ++ [s!"sep ({ℓ}, {d})"]
  if evalTop then
    if rp.top.isNone then out := out ++ ["top"]
    if rp.prep.isNone then out := out ++ ["prep"]
    if rp.cfg.initialized && rp.initShape.isNone then out := out ++ ["init"]
  return out.eraseDups

/-- Family coordinates and keys the run reads words at whose words the
fixture lacks (an over-approximation: every family of every evaluated job,
level one's old family, and every key of the units and the initialization). -/
def missingWords (rp : Replay) (evalTop : Bool) (coords : List (Nat × Nat)) :
    List (Nat × Nat) × Nat := Id.run do
  let cfg := rp.cfg
  let L := cfg.levels
  let mut fams : HashSet (Nat × Nat) := {}
  for (ℓ, v) in coords do
    fams := fams.insert (familyOf cfg ℓ v)
    -- level one reads its old family only to place A, which is empty at digit one
    if ℓ == 1 && Config.digitOf (cfg.fanout 1) v != 1 then fams := fams.insert (familyOf cfg 1 (v - 1))
    if ℓ == L then fams := fams.insert (familyOf cfg L (v + 1))
  if evalTop then
    if cfg.initialized then fams := fams.insert (familyOf cfg L (cfg.seed L))
    fams := fams.insert (familyOf cfg L (cfg.seed L + 1))
  let mut keys : HashSet Nat := {}
  for r in rp.init do keys := keys.insert (LogicalKey.toNat r.key)
  for (_, us) in rp.units.toList do
    for r in DirectMasks.records us do keys := keys.insert (LogicalKey.toNat r.key)
  let mut missingFams := []
  let mut missingPairs := 0
  for f in fams.toList do
    match rp.words.get? f with
    | none => missingFams := f :: missingFams
    | some m =>
      let miss := keys.toList.filter (fun k => !m.contains k)
      if !miss.isEmpty then
        missingFams := f :: missingFams
        missingPairs := missingPairs + miss.length
  return (missingFams, missingPairs)

structure State where
  memo : Memo := {}
  jobs : Array JobOutcome := #[]
  tables : Nat := 0
  compared : Nat := 0
  skipped : Nat := 0
  mismatches : Nat := 0
  shown : List Json := []
  /-- The unshadowed promise over the evaluated top finishes. -/
  unsh : UnshAcc := {}

def mismatchLimit : Nat := 5

def State.addFaults (st : State) (t : NativeTable) (ℓ v : Nat) (faults : List (String × Json)) : State :=
  { st with mismatches := st.mismatches + faults.length,
            shown := st.shown ++ (faults.map fun (part, j) =>
              Json.mkObj [("table", toJson [ℓ, v]), ("id", toJson t.id), ("part", toJson part),
                ("detail", j)]).take (mismatchLimit - min mismatchLimit st.shown.length) }

def lookupE (e : Env) (m : Memo) (ℓ v : Nat) : Except String Output :=
  match e.lookup m ℓ v with
  | some o => .ok o
  | none => .error s!"internal: table ({ℓ}, {v}) was not evaluated"

/-- Evaluate the serialised order up to level-one ordinal `tEnd`: every table,
compared with the native tables of its coordinate as soon as it is computed,
and every potential job's bounded result. Tables are dropped from the memo
when the level's next table is computed (`Env.Sound.erase`). -/
def evaluate (e : Env) (evalTop : Bool) (tEnd : Nat)
    (natives : HashMap (Nat × Nat) (Array NativeTable)) (ops : Array NativeOp) : Except String State := do
  let cfg := e.cfg
  let L := cfg.levels
  let top := if evalTop then L else L - 1
  let mut st : State := {}
  if evalTop then
    if cfg.initialized then st := { st with jobs := st.jobs.push (initOutcome e) }
    let base0 ← (e.evalTable st.memo L (cfg.seed L)).elim (.error "internal: top base") pure
    st := { st with memo := st.memo.insert (L, cfg.seed L) base0 }
    st := { st with jobs := st.jobs.push (prepOutcome e (cfg.seed L + 1) base0) }
  for t in [cfg.seed 1 + 1 : tEnd + 1] do
    for ℓ in [1 : top + 1] do
      let p := period cfg ℓ
      if t % p != 0 then continue
      let v := t / p
      let prev ← lookupE e st.memo ℓ (v - 1)
      let carry ← if ℓ = 1 then pure emptyOutput else lookupE e st.memo (ℓ - 1) (v * cfg.fanout (ℓ - 1))
      let job ←
        if ℓ = L then
          -- the finish's inputs once: its bounded result and the unshadowed promise
          let inp := finishInputsOf e v prev carry
          st := { st with unsh := st.unsh.check e ops v prev inp }
          pure (finishOutcome e v inp)
        else if ℓ = 1 then pure (levelOneOutcome e v prev)
        else pure (sepOutcome e ℓ v prev carry)
      st := { st with jobs := st.jobs.push job }
      let some o := e.evalTable st.memo ℓ v | throw s!"internal: table ({ℓ}, {v})"
      for nt in natives.getD (ℓ, v) #[] do
        let (n, shown) := compareTable nt ℓ v o (mismatchLimit - min mismatchLimit st.shown.length)
        st := { st with compared := st.compared + 1, mismatches := st.mismatches + n,
                        shown := st.shown ++ shown }
      st := { st with memo := (st.memo.insert (ℓ, v) o).erase (ℓ, v - 1) }
      if ℓ = L then
        st := { st with jobs := st.jobs.push (prepOutcome e (v + 1) o) }
  return st

/-- The named job of a native failure, from the dumper's level and ordinal and
the message's phase (the top's preparation and finish). -/
def namedJob (cfg : Config) (f : NativeFailure) : Option JobId := do
  if f.job == some "initialization" then return .initialization
  let ℓ ← f.level
  let o ← f.ordinal
  match f.job with
  | some "top_prepare" => return .topPrepare o
  | some "top_finish" => return .topFinish o
  | _ =>
    if ℓ < cfg.levels then return .ordinary ℓ o
    -- older fixtures: the top's preparation is the `prepare-older` phase
    if (f.message.splitOn "prepare-older").length > 1 then return .topPrepare o
    return .topFinish o

/-- Under `--drive lazy`, whether a job completed natively by the run's end:
its level's ordinal is at most the level's published ordinal
(`outcome.levels`); a top preparation precedes its finish's publication. -/
def publishedJob (cfg : Config) (published : HashMap Nat Nat) : JobId → Bool
  | .ordinary ℓ o => o ≤ published.getD ℓ 0
  | .topPrepare o => o ≤ published.getD cfg.levels 0
  | .topFinish o => o ≤ published.getD cfg.levels 0
  | .initialization => cfg.initialized

/-- A named job whose carry completes after the run: its bounded result with
an empty carry (and empty units at level one). Natively it failed while
preparing A, before its carry existed, so only an A-side failure is
conclusive. -/
def speculativeOutcome (e : Env) (m : Memo) (j : JobId) : Option JobOutcome := do
  match j with
  | .ordinary ℓ v =>
    let prev ← e.lookup m ℓ (v - 1)
    if ℓ = 1 then
      return { levelOneOutcome e v prev with speculative := true }
    else return { sepOutcome e ℓ v prev emptyOutput with speculative := true }
  | _ => none

/-! ### The evidence's completeness (fail closed)

A fixture with evidence removed must not pass. Every check below is an
invariant of the dumper's output (`HIERARCHY_REPLAY_SCHEMA.md`, "Completeness");
a violation is a failure `evidence.*` (or `dumper_checks`), so that a gutted,
truncated or partially written fixture is rejected rather than compared
vacuously. -/

/-- A coordinate that has no table of its own: below the top, a digit-one job
of a level with fanout above 2 adopts its carry, the level below's table (an
`inbox` table identified as the level below's; schema, "How the Lean side
identifies a table"). A binary level's digit one publishes a plain copy. -/
def adoptsCarry (cfg : Config) (ℓ v : Nat) : Bool :=
  1 < ℓ && ℓ < cfg.levels && Config.digitOf (cfg.fanout ℓ) v == 1 && 2 < cfg.fanout ℓ

/-- The completeness checks: the failed ones' names and the report.

* `evidence.ops`: `ops` lists every issued operation (without a failure exactly
  `outcome.accesses` of them, as many as `config.accesses_requested`);
* `evidence.levels`: `outcome.levels` lists every level; without a failure
  each level published `⌊t / P(ℓ)⌋` (the dumper settles at the end, lazy drive
  included), with one at most that;
* `evidence.units`: the captured prefixes are exactly the level-one ordinals
  `s_1 + 1 … s_1 + outcome.prefixes`, `outcome.prefixes = ⌊accesses / 64 r0 s⌋`
  (one position per operation), `last_level_one_ordinal = s_1 + prefixes` and
  `seed_prefixes = s_1`;
* `evidence.contents`: a table without contents (`main`, `tier` null) only at a
  selected configuration, only at the top, and only under
  `config.skip_top_contents`;
* `evidence.tables`: every job that completed natively (the failure
  comparison's rule: eager, time `≤ t` (`< t` after a failure); lazy, up to the
  level's published ordinal) has a recorded table at its coordinate, except a
  digit-one adoption (`adoptsCarry`); the top's seed table `(L, s_L)` (the
  empty top `(L, 0)` uninitialized) is recorded;
* `dumper_checks`: `checks.failures` is empty. -/
def evidenceFaults (rp : Replay) (tLast : Nat) (lazy : Bool) (limit : Nat := 5) :
    List String × Json := Id.run do
  let cfg := rp.cfg
  let L := cfg.levels
  let sel := rp.selected.isSome
  let failed := rp.failure.isSome
  let mut fails : List String := []
  -- operations
  let opsOk := if failed then decide (rp.accesses ≤ rp.ops.size) else rp.ops.size == rp.accesses
  let reqOk := failed || rp.accessesRequested.all (· == rp.accesses)
  if !(opsOk && reqOk) then fails := fails ++ ["evidence.ops"]
  -- units
  let perPrefix := 64 * rp.stashBuckets * rp.prefixFlushes
  let seed1 := cfg.seed 1
  let unitOrds := ((rp.units.toArray.map (·.1)).qsort (· < ·)).toList
  let want := (List.range rp.prefixes).map (seed1 + 1 + ·)
  let unitsOk := rp.seedPrefixes == seed1 && tLast == seed1 + rp.prefixes && unitOrds == want &&
    perPrefix != 0 && rp.prefixes == rp.accesses / perPrefix
  if !unitsOk then fails := fails ++ ["evidence.units"]
  -- the levels' state at the stop: every level listed; without a failure the
  -- final settle (lazy drive too) publishes every due ordinal, `⌊t / P(ℓ)⌋`
  let levelsOk := (List.range L).all fun i =>
    let ℓ := i + 1
    match rp.published.get? ℓ with
    | none => false
    | some p => if failed then decide (p ≤ tLast / period cfg ℓ) else p == tLast / period cfg ℓ
  let levelsOk := levelsOk && rp.published.size == L
  if !levelsOk then fails := fails ++ ["evidence.levels"]
  -- contents
  let mut nullBad := 0
  let mut present : HashSet (Nat × Nat) := {}
  for nt in rp.tables do
    let (ℓ, v) := coordOf cfg nt
    present := present.insert (ℓ, v)
    if nt.contents.isNone && !(sel && rp.skipTopContents && ℓ == L) then nullBad := nullBad + 1
  if nullBad != 0 then fails := fails ++ ["evidence.contents"]
  -- coverage
  let completed (ℓ v : Nat) : Bool :=
    if lazy then decide (v ≤ rp.published.getD ℓ 0)
    else if failed then decide (v * period cfg ℓ < tLast) else decide (v * period cfg ℓ ≤ tLast)
  let mut done := 0
  let mut adopted := 0
  let mut missing : List (Nat × Nat) := []
  let mut nMissing := 0
  for (ℓ, v) in (L, cfg.seed L) :: plannedCoords cfg true tLast do
    if v > cfg.seed ℓ && !completed ℓ v then continue
    done := done + 1
    if present.contains (ℓ, v) then continue
    if adoptsCarry cfg ℓ v then
      adopted := adopted + 1
    else
      nMissing := nMissing + 1
      if missing.length < limit then missing := missing ++ [(ℓ, v)]
  if nMissing != 0 then fails := fails ++ ["evidence.tables"]
  if !rp.dumperChecks.isEmpty then fails := fails ++ ["dumper_checks"]
  let verdict (b : Bool) : Json := toJson (if b then "pass" else "fail")
  return (fails, Json.mkObj [
    ("result", verdict fails.isEmpty),
    ("ops", Json.mkObj [("result", verdict (opsOk && reqOk)), ("issued", toJson rp.ops.size),
      ("completed", toJson rp.accesses), ("requested", toJson rp.accessesRequested)]),
    ("units", Json.mkObj [("result", verdict unitsOk), ("ordinals", toJson unitOrds.length),
      ("prefixes", toJson rp.prefixes), ("seed_prefixes", toJson rp.seedPrefixes)]),
    ("levels", Json.mkObj [("result", verdict levelsOk),
      ("rule", toJson (if failed then "published ordinal <= t / P(l) at every level"
        else "published ordinal = t / P(l) at every level (the final settle)"))]),
    ("contents", Json.mkObj [("result", verdict (nullBad == 0)), ("omitted_outside_rule", toJson nullBad),
      ("rule", toJson "only the top's tables of a selected run under skip_top_contents")]),
    ("coverage", Json.mkObj [("result", verdict (nMissing == 0)), ("completed_coordinates", toJson done),
      ("adoptions_without_table", toJson adopted), ("missing", toJson nMissing),
      ("first", toJson (missing.map fun c => [c.1, c.2]))]),
    ("dumper_checks", Json.mkObj [("result", verdict rp.dumperChecks.isEmpty),
      ("failures", toJson (rp.dumperChecks.take limit))])])

/-- The replay of a parsed fixture. -/
def runJson (path : String) (fixture : Json) : P (Json × UInt32) := do
  let rp ← parseReplayJson fixture
  let cfg := rp.cfg
  let L := cfg.levels
  if L < 2 then throw "config.fanouts: at least one level below the top expected"
  let sel := rp.selected.isSome
  let evalTop := !sel
  let e := rp.env
  -- the last level-one ordinal whose prefix completed
  let tLast := rp.lastOrdinal.getD (rp.units.fold (fun acc o _ => max acc o) (cfg.seed 1))
  let lazy := rp.drive == "lazy"
  -- identify the native tables
  let mut natives : HashMap (Nat × Nat) (Array NativeTable) := {}
  let mut pre : State := {}
  let mut tMaxNative := cfg.seed 1
  let mut preInit : Array NativeTable := #[]
  let mut unread := 0
  for nt in rp.tables do
    let (ℓ, v) := coordOf cfg nt
    let faults := structuralFaults cfg nt
    pre := { pre.addFaults nt ℓ v faults with tables := pre.tables + 1 }
    -- the one legitimate skip: the top's tables at a selected configuration,
    -- whose top the replay does not evaluate (with or without contents)
    if ℓ == L && sel then
      pre := { pre with skipped := pre.skipped + 1 }
    else if nt.contents.isNone then
      -- contents omitted outside the rule: not compared, `evidence.contents` fails
      unread := unread + 1
    else if cfg.initialized && isEmptyTop cfg nt then
      preInit := preInit.push nt
    else if 1 ≤ ℓ && ℓ ≤ L && v > cfg.seed ℓ then
      natives := natives.insert (ℓ, v) ((natives.getD (ℓ, v) #[]).push nt)
      tMaxNative := max tMaxNative (v * period cfg ℓ)
    else if 1 ≤ ℓ && ℓ ≤ L then
      -- a base table: compare it with the base directly
      natives := natives.insert (ℓ, v) ((natives.getD (ℓ, v) #[]).push nt)
  let tEnd := max tLast tMaxNative
  let coords := plannedCoords cfg evalTop tEnd
  let ms := missingShapes rp evalTop coords
  if !ms.isEmpty then throw s!"shapes: rows the run needs are missing: {ms}"
  for (ℓ, v) in coords do
    let d := Config.digitOf (cfg.fanout ℓ) v
    if ℓ == 1 && !decide (e.sh.direct d).Valid then throw s!"shapes.direct: digit {d} violates Geometry.Valid"
    if 1 < ℓ && ℓ < L && 1 < d && !decide (e.sh.sep ℓ d).Valid then
      throw s!"shapes.sep: ({ℓ}, {d}) violates SepGeom.Valid"
  if evalTop && !decide e.sh.prep.Valid then throw "shapes.prep: violates TPGeom.Valid"
  if evalTop && cfg.initialized && !decide e.sh.init.Valid then
    throw "shapes.init: violates TPGeom.Valid"
  if evalTop && !decide e.sh.top.Valid then throw "shapes.top: violates TopGeom.Valid"
  let (mf, mp) := missingWords rp evalTop coords
  if !mf.isEmpty then
    throw s!"words-missing: {mf.length} families ({mp} family/key pairs), e.g. {mf.take 5}"
  -- base tables listed natively (at or below the seeded counter)
  let N ← match rp.keyBound <|> rp.addressSpace with
    | some n => pure n
    | none => throw "config.key_bound / config.address_space: missing (the trace premises' N)"
  let mut st ← match evaluate e evalTop tEnd natives rp.ops with
    | .ok st => pure st
    | .error err => throw err
  for ((ℓ, v), nts) in natives.toList do
    if v ≤ cfg.seed ℓ then
      let o := base cfg e.sh e.tr e.words ℓ
      for nt in nts do
        let (n, shown) := compareTable nt ℓ v o (mismatchLimit - min mismatchLimit st.shown.length)
        st := { st with compared := st.compared + 1, mismatches := st.mismatches + n,
                        shown := st.shown ++ shown }
  for nt in preInit do
    let o := base { cfg with initialized := false } e.sh e.tr e.words L
    let (n, shown) := compareTable nt L 0 o (mismatchLimit - min mismatchLimit st.shown.length)
    st := { st with compared := st.compared + 1, mismatches := st.mismatches + n,
                    shown := st.shown ++ shown }
  st := { st with tables := pre.tables, skipped := pre.skipped,
                  mismatches := st.mismatches + pre.mismatches, shown := (pre.shown ++ st.shown).take mismatchLimit }
  -- the failure comparison
  let failing := st.jobs.toList.filter (·.fails)
  -- jobs that completed natively: eager, every job with time < t (time ≤ t
  -- without a failure); lazy, every job up to its level's published ordinal
  let completed (jo : JobOutcome) : Bool :=
    if lazy then publishedJob cfg rp.published jo.job
    else if rp.failure.isSome then jo.time < tLast else jo.time ≤ tLast
  let early := failing.filter completed
  let rule := if lazy then "jobs up to each level's published ordinal succeed"
    else if rp.failure.isSome then "jobs with time < t succeed" else "jobs with time <= t succeed"
  let base : List (String × Json) := [("t", toJson tLast), ("drive", toJson rp.drive),
    ("rule", toJson rule), ("completed_failures", toJson ((early.take 5).map (·.toJson)))]
  let (fcheck, fdetail) : String × List (String × Json) :=
    match rp.failure with
    | none => (if early.isEmpty then "pass" else "fail", base)
    | some f =>
      let c2 := early.isEmpty
      match namedJob cfg f with
      | none => (if c2 then "n/a" else "fail", base ++ lj [("named", "unnamed")])
      | some j =>
        let topJobN := match j with
          | .ordinary ℓ _ => ℓ == L | _ => true
        if topJobN && sel then
          (if c2 then "n/a" else "fail", base ++ [("named", Json.mkObj (jobJson j)),
            ("named_result", toJson "not evaluated (top at a selected configuration)")])
        else
          let found := (st.jobs.toList.find? (·.job == j)).orElse fun _ => speculativeOutcome e st.memo j
          match found with
          | none => ("fail", base ++ [("named", Json.mkObj (jobJson j)), ("named_result", toJson "not evaluated")])
          | some jo =>
            let ncls := nativeClass f.message
            let clsOk := ncls == "unknown" || jo.cls == ncls
            (if c2 && jo.fails && clsOk then "pass" else "fail",
              base ++ [("named", jo.toJson), ("native_class", toJson ncls),
                ("native_kind", toJson (nativeKind f.message))])
  let tablesOk := st.mismatches == 0
  -- the theorems' premises on the observed trace
  let (tpFails, tpJson) := tracePremises rp e N
  let (unFails, unJson) := UnshAcc.report (if evalTop then some st.unsh else none)
  -- the evidence's completeness
  let (evFails, evJson) := evidenceFaults rp tLast lazy
  -- Initialization uses its own emitted shape; retain the difference as
  -- diagnostic information, with missing evidence still a failure.
  let initDiffers : Option Bool := match rp.initShape, rp.prep with
    | some i, some p => some (i != p)
    | _, _ => none
  let failures := (if tablesOk then [] else ["tables"]) ++ (if fcheck == "fail" then ["failure_check"] else []) ++
    tpFails ++ unFails ++ evFails
  let pass := failures.isEmpty
  let nativeFailure : Json := match rp.failure with
    | none => Json.null
    | some f => Json.mkObj [("access", toJson f.access), ("message", toJson f.message),
        ("level", toJson f.level), ("ordinal", toJson f.ordinal), ("job", toJson f.job)]
  let out := Json.mkObj [
    ("file", toJson path), ("mode", "hierarchy"), ("selected", toJson rp.selected),
    ("accesses", toJson rp.accesses), ("t", toJson tLast),
    ("tables", toJson st.tables), ("compared", toJson st.compared), ("skipped_top", toJson st.skipped),
    ("skip_rule", toJson (if sel then "the top's tables (selected configuration: the top is not evaluated)"
      else "none")), ("unread", toJson unread),
    ("mismatches", toJson st.mismatches), ("first_mismatches", toJson st.shown),
    ("jobs_evaluated", toJson st.jobs.size),
    ("model_failures", toJson ((failing.take 5).map (·.toJson))),
    ("native_failure", nativeFailure), ("init_shape_differs", toJson initDiffers),
    ("failure_check", toJson fcheck),
    ("failure_detail", Json.mkObj fdetail),
    ("trace_premises", tpJson), ("unsh_promise", unJson), ("evidence", evJson),
    ("failures", toJson failures),
    ("result", if pass then "pass" else "fail")]
  return (out, if pass then 0 else 1)

def run (path text : String) : P (Json × UInt32) := do
  runJson path (← Json.parse text)

end RebuildBound.Oracle.HierarchyDiff
