import RebuildBound.Oracle.DirectJob
import RebuildBound.Spec.Model.DirectJobA

/-! Original-input A-phase regressions. Analytical snapshots are recomputed even
on failure, while the bounded observation respects prepare-A, B, distribution.
No successful phase result is a published complete job. -/
namespace RebuildBound.Oracle.DirectJobA
open Lean RebuildBound.Model
open RebuildBound.Oracle.DirectJob

def recordsJson (rs : List Model.Rec) : Json := Json.arr ((rs.map recordJson).toArray)
def bucketsJson (bs : List Bucket) : Json :=
  Json.arr ((bs.map fun b => Json.arr ((b.map fun x => x.elim Json.null recordJson).toArray)).toArray)

def observe (f : Sources) : Json := Id.run do
  let g := f.geometry
  let inp := f.inputs
  let w := wordFor f.words "current"
  let a := Model.DirectJob.analyticalA g w inp.aMain
  let tierIndices := (Model.DirectJob.analyticalB g w inp).records
  let bTier := (DirectRecords.restore inp.bRecords ([], tierIndices)).2
  let pool := Model.DirectJob.aOperational a.state inp.aTier bTier
  let d := Model.DirectJob.distributeA g w pool
  let bounded := match Model.DirectJob.prepareA g w inp.aMain with
    | .error e => resultJson (.failed e)
    | .ok _ => match Model.DirectJob.buildB g w inp with
      | .error e => resultJson (.failed e)
      | .ok _ => match Model.DirectJob.distributeABounded g w pool with
        | .error e => resultJson (.failed e)
        | .ok _ => Json.mkObj [("kind", "phases-completed")]
  return Json.mkObj [
    ("a_main", bucketsJson a.state.main),
    ("a_stashes", Json.arr ((a.state.stash.map recordsJson).toArray)),
    ("a_radix", recordsJson a.state.radix),
    ("a_trace", Json.arr ((a.trace.map eventJson).toArray)),
    ("unfiltered_pool", recordsJson (Model.DirectJob.aResidual a.state inp.aTier)),
    ("b_tier", recordsJson bTier), ("operational_pool", recordsJson pool),
    ("leaves", Json.arr ((d.leaves.map recordsJson).toArray)),
    ("distribution_trace", Json.arr ((d.trace.map eventJson).toArray)),
    ("bounded", bounded)]

def run (path text : String) : P (Json × Bool) := do
  let f ← parseSources text "direct-job-a-reference/0"
  if f.geometry.digit < 2 then throw "geometry: A phase requires a later digit"
  let j ← Json.parse text
  let expected ← objField j "fixture" "expected"
  let actual := observe f
  let ok := actual == expected
  return (Json.mkObj [("file", toJson path), ("job", "direct-a-phases"),
    ("evidence", "reference-regression"), ("comparison", if ok then "pass" else "fail"),
    ("actual", actual), ("expected", expected)], ok)

end RebuildBound.Oracle.DirectJobA
