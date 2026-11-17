import RebuildBound.Oracle.PublicApiDiff
import RebuildBound.Oracle.Check
import RebuildBound.Oracle.Diff
import RebuildBound.Oracle.TopDiff
import RebuildBound.Oracle.SepDiff
import RebuildBound.Oracle.DirectJob
import RebuildBound.Oracle.DirectJobA
import RebuildBound.Oracle.DirectJobFinish
import RebuildBound.Oracle.TPDiff
import RebuildBound.Oracle.HierarchyDiff
import RebuildBound.Oracle.OnlineDiff
import RebuildBound.Oracle.OnlineBatchDiff

/-!
# Command-line entry of the differential-test oracle

    lake exe oracle [--phase0 | --sep | --tp | --direct | --direct-a | --direct-finish | --hierarchy | --online | --api | --geometry31] <fixture.json>...

Default mode: runs the Lean model on each fixture and compares it with the
engine (O2 verdict, O3 lane-exact output, O1 on both outputs): the d = 2 job
(`Diff.lean`) for a `rebuild-fixture/0` and the top finish (`TopDiff.lean`) for
a `top-finish-fixture/0`; one JSON
line per fixture with `o1`, `o1_model`, `o2`, `o3`, `kind`, `diff` fields. With
`--phase0`: only the engine's O1 check, as below. Several files: one line each,
exit code the maximum (0 pass / 1 fail / 2 malformed). `--direct` instead
runs hand/model `direct-job-reference/0` reference regressions: exact logical
result, normalized first failure event, and full compact publication. This
mode supplies no native differential evidence; see `oracle/DIRECT_JOB_SCHEMA.md`.
`--hierarchy` replays a whole engine run (`hierarchy-replay/0`,
`HierarchyDiff.lean`, `oracle/HIERARCHY_REPLAY_SCHEMA.md`) against the trusted
hierarchy model: every published table lane by lane and the first capacity
failure; one line with `mode`, `tables`, `compared`, `mismatches`,
`failure_check` and `result` per fixture. A fixture with a `view`
(`hierarchy_dump --view`) also gets the adversary's-view replay under
`online`, its failures added to the line's `failures`: the scalar model's
(`OnlineDiff.lean`) on a scalar view, plus the same view through the batch
model under `online_batch` (`BatchScalar`); the batch model's
(`OnlineBatchDiff.lean`) on a view of a `--batch` run. `--online` runs that
replay alone. `--api` also checks original public API requests, callback and
batch responses, current/frozen dense units, and probe chunks. `--geometry31`
requires the current selected geometry and exact sparse top snapshots.
`--hierarchy` automatically enables these checks for API/geometry31 fixtures.

The `--phase0` mode reads a `rebuild-fixture/0` fixture (written by `oracle/fixture_dump.cpp`),
checks the O1 semantic spec of an ordinary merge (`Check.lean`) and prints ONE
line of JSON:

* `{"o1":"pass","records":N,"homes":H,"tier":T,...}`   exit 0
* `{"o1":"fail","violation_count":n,"violations":[...]}`   exit 1
* `{"o1":"skipped","engine":"failure","message":"..."}`   exit 0: the engine
  reported a capacity failure; O1 does not apply and only the structure of the
  inputs is checked (the default mode compares the model's verdict)
* `{"o1":"malformed","error":"..."}`   exit 2: unreadable or ill-formed file
-/

open Lean
open RebuildBound.Oracle

def emit (fields : List (String × Json)) : IO Unit :=
  IO.println (Json.mkObj fields).compress

def failJson (r : Report) : List (String × Json) :=
  [("o1", "fail"), ("violation_count", toJson r.total),
   ("violations", toJson r.shown)]

def malformed (msg : String) : IO UInt32 := do
  emit [("o1", "malformed"), ("error", toJson msg)]
  IO.eprintln s!"oracle: malformed fixture: {msg}"
  return 2

/-- A malformed fixture in a mode whose lines carry `file`, `mode` and `result`. -/
def malformedIn (mode path msg : String) : IO UInt32 := do
  emit [("file", toJson path), ("mode", toJson mode), ("result", "malformed"), ("error", toJson msg)]
  IO.eprintln s!"oracle: malformed fixture {path}: {msg}"
  return 2

def runPhase0 (path : String) : IO UInt32 := do
  let text ← try pure (some (← IO.FS.readFile path)) catch _ => pure none
  let some text := text | malformed s!"cannot read {path}"
  match parseFixture text with
  | .error e => malformed e
  | .ok fx =>
    if fx.outputs.verdict == "failure" then
      let r := checkFailureInputs fx
      if r.total != 0 then
        emit (failJson r)
        return 1
      emit [("o1", "skipped"), ("engine", "failure"),
            ("message", toJson fx.outputs.message), ("inputs", "ok")]
      return 0
    else
      let (s, r) := checkSuccess fx
      if r.total != 0 then
        emit (failJson r)
        return 1
      emit [("o1", "pass"), ("records", toJson s.records),
            ("homes", toJson s.homes), ("tier", toJson s.tierRecords),
            ("main", toJson s.mainRecords), ("full_homes", toJson s.fullHomes),
            ("shadowed", toJson s.shadowed)]
      return 0

def lj (l : List (String × Json)) : List (String × Json) := l

def statsJson (s : Stats) : List (String × Json) :=
  [("records", toJson s.records), ("homes", toJson s.homes),
   ("tier", toJson s.tierRecords), ("main", toJson s.mainRecords),
   ("full_homes", toJson s.fullHomes), ("shadowed", toJson s.shadowed)]

/-- Differential mode for a top-finish fixture. -/
def runTopDiff (path text : String) : IO UInt32 := do
  match Top.parseFixture text with
  | .error e => malformed e
  | .ok fx =>
    let (fields, ok) := Top.run fx
    emit ([("file", toJson path), ("job", "top_finish"), ("engine", toJson fx.verdict)] ++ fields)
    return if ok then 0 else 1

/-- Differential mode: model against engine. -/
def runDiff (path : String) : IO UInt32 := do
  let text ← try pure (some (← IO.FS.readFile path)) catch _ => pure none
  let some text := text | malformed s!"cannot read {path}"
  if (text.splitOn "\"top-finish-fixture/0\"").length > 1 then
    return ← runTopDiff path text
  match parseFixture text with
  | .error e => malformed e
  | .ok fx =>
    let file : List (String × Json) := [("file", toJson path)]
    let inputsBad := checkFailureInputs fx
    if inputsBad.total != 0 then
      -- ill-formed inputs: O1 (check 4) fails, the model does not run
      let r := if fx.outputs.verdict == "failure" then inputsBad else (checkSuccess fx).2
      emit (file ++ failJson r ++ lj [("o2", "skipped"), ("o3", "skipped")])
      return 1
    let res := runModel fx
    if fx.outputs.verdict == "failure" then
      let ek := engineKind fx.outputs.message
      let base := file ++ lj [("o1", "skipped"), ("engine", "failure"),
        ("message", toJson fx.outputs.message), ("engine_kind", toJson ek)]
      match res with
      | .ok _ =>
        emit (base ++ lj [("o2", "fail"), ("model", "success"), ("o3", "skipped")])
        return 1
      | .badInput =>
        emit (base ++ lj [("o2", "fail"), ("model", "bad-input"), ("o3", "skipped")])
        return 1
      | .fail t =>
        let km := testKind t == ek
        emit (base ++ lj [("o2", "pass"), ("model", "failure"),
          ("model_kind", toJson (testKind t)), ("model_test", toJson (testDetail t)),
          ("kind", if km then "match" else "mismatch"), ("o3", "skipped")])
        return if km then 0 else 1
    else
      let (s, r) := checkSuccess fx
      let o1 : List (String × Json) :=
        if r.total != 0 then
          [("o1", "fail"), ("violation_count", toJson r.total), ("violations", toJson r.shown)]
        else lj [("o1", "pass")] ++ statsJson s
      let o1bad := r.total != 0
      match res with
      | .badInput =>
        emit (file ++ o1 ++ lj [("o2", "fail"), ("model", "bad-input"), ("o3", "skipped")])
        return 1
      | .fail t =>
        emit (file ++ o1 ++ lj [("o2", "fail"), ("model", "failure"),
          ("model_kind", toJson (testKind t)), ("model_test", toJson (testDetail t)),
          ("o3", "skipped")])
        return 1
      | .ok o =>
        let (m1, mr) := checkSuccess (modelFixture fx o)
        let (nd, diffs) := compareOutputs fx o
        let o1m : List (String × Json) :=
          if mr.total != 0 then
            [("o1_model", "fail"), ("model_violation_count", toJson mr.total),
             ("model_violations", toJson mr.shown)]
          else [("o1_model", "pass"), ("model_tier", toJson m1.tierRecords)]
        let o3 : List (String × Json) :=
          if nd == 0 then [("o3", "pass")]
          else [("o3", "fail"), ("diff_count", toJson nd), ("diff", toJson diffs)]
        emit (file ++ o1 ++ o1m ++ lj [("o2", "pass"), ("model", "success")] ++ o3)
        return if o1bad || mr.total != 0 || nd != 0 then 1 else 0

/-- Differential mode for the general-digit model: any
`rebuild-fixture/0` fixture, through `RebuildBound.Model.sJob`. -/
def runSepDiff (path : String) : IO UInt32 := do
  let text ← try pure (some (← IO.FS.readFile path)) catch _ => pure none
  let some text := text | malformed s!"cannot read {path}"
  match parseFixture text with
  | .error e => malformed e
  | .ok fx =>
    let (fields, ok) := Sep.run text fx
    emit ([("file", toJson path), ("job", "separated"), ("engine", toJson fx.outputs.verdict)] ++ fields)
    return if fields.any (fun f => f.1 == "o1" && f.2 == "malformed") then 2 else if ok then 0 else 1

/-- Differential mode for the top preparation and the initialization route
(`TPDiff.lean`): `top-prep-fixture/0` and `top-init-fixture/0`. -/
def runTPDiff (path : String) : IO UInt32 := do
  let text ← try pure (some (← IO.FS.readFile path)) catch _ => pure none
  let some text := text | malformed s!"cannot read {path}"
  match TP.run path text with
  | .error e => malformed e
  | .ok (fields, ok) =>
    emit fields
    return if ok then 0 else 1

/-- Hand/model direct-job reference regression, with exact result comparison. -/
def runDirect (path : String) (mode : String := "direct") : IO UInt32 := do
  let text ← try pure (some (← IO.FS.readFile path)) catch _ => pure none
  let some text := text | malformed s!"cannot read {path}"
  match (if mode == "direct-finish" then DirectJobFinish.run path text
    else if mode == "direct-a" then DirectJobA.run path text else DirectJob.run path text) with
  | .error e => malformed e
  | .ok (result, ok) =>
    IO.println result.compress
    return if ok then 0 else 1

/-- Trace replay of the whole hierarchy (`HierarchyDiff.lean`). -/
def runHierarchy (path : String) : IO UInt32 := do
  let text ← try pure (some (← IO.FS.readFile path)) catch _ => pure none
  let some text := text | malformedIn "hierarchy" path s!"cannot read {path}"
  let parsed := Json.parse text
  let hasApi := (parsed.bind (fun j => j.getObjVal? "api")).isOk
  let selected := parsed.bind (fun j => do
    let c ← j.getObjVal? "config"
    (← c.getObjVal? "selected").getStr?)
  let replay := if hasApi || selected.toOption == some "geometry31" then
      PublicApiDiff.run path text hasApi
    else OnlineBatchDiff.runCombined path text
  match replay with
  | .error e => malformedIn "hierarchy" path e
  | .ok (result, code) =>
    IO.println result.compress
    return code

/-- The adversary's view alone (`OnlineDiff.lean`, `OnlineBatchDiff.lean`): a fixture with a `view`. -/
def runOnline (path : String) : IO UInt32 := do
  let text ← try pure (some (← IO.FS.readFile path)) catch _ => pure none
  let some text := text | malformedIn "online" path s!"cannot read {path}"
  match OnlineBatchDiff.runOnline path text with
  | .error e => malformedIn "online" path e
  | .ok (result, code) =>
    IO.println result.compress
    return code

def runPublicApi (path : String) (api : Bool) : IO UInt32 := do
  let text ← try IO.FS.readFile path catch _ => return ← malformedIn "api" path s!"cannot read {path}"
  match PublicApiDiff.run path text api with
  | .error e => malformedIn (if api then "api" else "geometry31") path e
  | .ok (result, code) => IO.println result.compress; return code

def main (args : List String) : IO UInt32 := do
  if args.head? == some "--l1" then
    IO.eprintln "unsupported mode: --l1"
    return 2
  let (mode, files) := match args with
    | "--phase0" :: rest => ("phase0", rest)
    | "--sep" :: rest => ("sep", rest)
    | "--tp" :: rest => ("tp", rest)
    | "--direct" :: rest => ("direct", rest)
    | "--direct-a" :: rest => ("direct-a", rest)
    | "--direct-finish" :: rest => ("direct-finish", rest)
    | "--hierarchy" :: rest => ("hierarchy", rest)
    | "--online" :: rest => ("online", rest)
    | "--api" :: rest => ("api", rest)
    | "--geometry31" :: rest => ("geometry31", rest)
    | _ => ("diff", args)
  if files.isEmpty then
    IO.eprintln "usage: lake exe oracle [--phase0 | --sep | --tp | --direct | --direct-a | --direct-finish | --hierarchy | --online | --api | --geometry31] <fixture.json>..."
    return 2
  let mut code : UInt32 := 0
  for f in files do
    let c ← match mode with
      | "phase0" => runPhase0 f
      | "sep" => runSepDiff f
      | "tp" => runTPDiff f
      | "direct" => runDirect f
      | "direct-a" => runDirect f "direct-a"
      | "direct-finish" => runDirect f "direct-finish"
      | "hierarchy" => runHierarchy f
      | "online" => runOnline f
      | "api" => runPublicApi f true
      | "geometry31" => runPublicApi f false
      | _ => runDiff f
    code := max code c
  return code
