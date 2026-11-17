import RebuildBound.Oracle.DirectJobA
import RebuildBound.Spec.Model.DirectJobFailure
import RebuildBound.Spec.Model.DirectJobResume

/-! Whole-job reference regressions from original inputs. Analytical observations
remain available after failure; only runJob determines publication. -/
namespace RebuildBound.Oracle.DirectJobFinish
open Lean RebuildBound.Model RebuildBound.Oracle.DirectJob
open RebuildBound.Oracle.DirectJobA (recordsJson bucketsJson)

def bucketJson (b : Bucket) : Json :=
  Json.arr ((b.map fun x => x.elim Json.null recordJson).toArray)

def laneResultJson : Model.DirectJob.LaneResult → Json
  | .rejected r => resultJson (.rejected r)
  | .failed e => resultJson (.failed e)
  | .published out => Json.mkObj [("kind", "published"),
      ("main", bucketsJson out.main), ("tier", bucketJson out.tier)]

def observe (f : Sources) : Json := Id.run do
  let g := f.geometry
  let inp := f.inputs
  let w := wordFor f.words "current"
  let b := Model.DirectJob.analyticalBTable g w inp
  let job := Model.DirectJob.analyticalJob g w inp
  let bounded := laneResultJson (Model.DirectJob.runJob g (wordFor f.words "old") w inp)
  if g.digit = 1 then
    return Json.mkObj [("finish_main", bucketsJson job.main), ("insertion", recordsJson []),
      ("remaining_leaves", toJson (#[] : Array Json)),
      ("remaining_b_tier", toJson (#[] : Array Json)),
      ("raw_tier", bucketJson job.tier),
      ("finish_trace", toJson (#[] : Array Json)), ("bounded", bounded)]
  let a := Model.DirectJob.analyticalA g w inp.aMain
  let d := Model.DirectJob.distributeA g w (Model.DirectJob.aOperational a.state inp.aTier b.tier)
  let fin := Model.DirectJob.analyticalFinish g w b a.state.main d.leaves
  return Json.mkObj [("finish_main", bucketsJson job.main),
    ("insertion", recordsJson fin.state.ins),
    ("remaining_leaves", Json.arr ((fin.state.leaves.map recordsJson).toArray)),
    ("remaining_b_tier", Json.arr ((fin.state.bcopy.map recordsJson).toArray)),
    ("raw_tier", bucketJson job.tier),
    ("finish_trace", Json.arr ((fin.trace.map eventJson).toArray)), ("bounded", bounded)]

/-- Parsed sources already satisfy the structural contract. Compare the
unconditional analytical trace with the independently expected bounded result. -/
def analyticalResultJson (f : Sources) : Json :=
  let job := Model.DirectJob.analyticalJob f.geometry (wordFor f.words "current") f.inputs
  laneResultJson (match Model.DirectJob.firstFailure job.trace with
    | some e => .failed e
    | none => .published (Model.DirectJob.finishOutput f.geometry job.main job.tier))

/-- Exercise the compiled logical cursor with pauses, including zero fuel.
The analytical trace supplies a regression fuel allowance, not production fuel.
Phase boundaries need at most six extra transitions. -/
def resumedResultJson (f : Sources) : Json := Id.run do
  let g := f.geometry
  let w := wordFor f.words "current"
  let fuel := (Model.DirectJob.analyticalJob g w f.inputs).trace.length + 6
  let mut cursor := Model.DirectJob.startJob g (wordFor f.words "old") w f.inputs
  for segment in [0, 1, fuel / 2, fuel - fuel / 2] do
    cursor := Model.DirectJob.resumeJob g w f.inputs segment cursor
  match cursor with
  | .done result => return laneResultJson result
  | _ => return Json.mkObj [("kind", "unfinished-cursor")]

/-- Native observations are read independently of original inputs. Failure
identity is deliberately projected to phase/check class: native batching does
not establish the reference ordinal, occupancy, or DFS node. -/
def nativeResultJson (j : Json) : P Json := do
  match ← strField j "result" "kind" with
  | "published" => return j
  | "failed" =>
    let e ← objField j "result" "event"
    let phase ← strField e "event" "phase"
    let site ← objField e "event" "site"
    let kind ← strField site "site" "kind"
    return Json.mkObj [("kind", "failed"), ("phase", toJson phase),
      ("site", Json.mkObj [("kind", toJson kind)])]
  | _ => throw "native result: expected published or failed"

def runNative (path text : String) : P (Json × Bool) := do
  let f ← parseSources text "direct-job-native/0" "native-differential"
  let j ← Json.parse text
  let expected ← objField j "fixture" "expected"
  let actualFull := laneResultJson (Model.DirectJob.runJob f.geometry
    (wordFor f.words "old") (wordFor f.words "current") f.inputs)
  let actual ← nativeResultJson actualFull
  let analytical ← nativeResultJson (analyticalResultJson f)
  let resumedFull := resumedResultJson f
  let resumed ← nativeResultJson resumedFull
  let observations ← objField j "fixture" "observations"
  let fields ← observations.getObj?.mapError (fun _ => "observations: expected object")
  let a := Model.DirectJob.analyticalA f.geometry (wordFor f.words "current") f.inputs.aMain
  let b := Model.DirectJob.analyticalBTable f.geometry (wordFor f.words "current") f.inputs
  let available := Json.mkObj [("a_main", bucketsJson a.state.main),
    ("a_stashes", Json.arr ((a.state.stash.map recordsJson).toArray)),
    ("a_radix", recordsJson a.state.radix), ("b_tier", recordsJson b.tier)]
  let mut snapshotsOk := true
  for (name, value) in fields.toList do
    if name != "a_main" && name != "a_stashes" && name != "a_radix" && name != "b_tier" then
      throw s!"observations: unsupported native boundary {name}"
    let reference ← objField available "observations" name
    snapshotsOk := snapshotsOk && value == reference
  let ok := actual == expected && analytical == expected && resumedFull == actualFull && snapshotsOk
  return (Json.mkObj [("file", toJson path), ("job", "direct-finish"),
    ("evidence", "native-differential"), ("comparison", if ok then "pass" else "fail"),
    ("actual", actualFull), ("expected", expected), ("analytical_result", analytical),
    ("resumed_result", resumed),
    ("snapshots", if snapshotsOk then "pass" else "fail"),
    ("reference_boundaries", available)], ok)

def run (path text : String) : P (Json × Bool) := do
  let root ← Json.parse text
  if (← strField root "fixture" "format") == "direct-job-native/0" then
    return ← runNative path text
  let f ← parseSources text "direct-job-finish-reference/0"
  let j ← Json.parse text
  let expected ← objField j "fixture" "expected"
  let actual := observe f
  let analytical := analyticalResultJson f
  let resumed := resumedResultJson f
  let expectedBounded ← objField expected "expected" "bounded"
  let ok := actual == expected && analytical == expectedBounded && resumed == expectedBounded
  return (Json.mkObj [("file", toJson path), ("job", "direct-finish"),
    ("evidence", "reference-regression"), ("comparison", if ok then "pass" else "fail"),
    ("actual", actual), ("expected", expected), ("analytical_result", analytical),
    ("resumed_result", resumed)], ok)

end RebuildBound.Oracle.DirectJobFinish
