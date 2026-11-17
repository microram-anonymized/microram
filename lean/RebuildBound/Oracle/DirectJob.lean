import RebuildBound.Oracle.Fixture
import RebuildBound.Spec.Model.DirectJobB

/-! Core-only digit-one reference regression runner. These fixtures are
hand/model evidence; no native exporter or native correspondence is claimed. -/
namespace RebuildBound.Oracle.DirectJob
open Lean
open RebuildBound.Model

structure Word where
  family : String
  key : Nat
  word : Nat

structure Fixture where
  geometry : RebuildBound.Model.DirectJob.Geometry
  inputs : RebuildBound.Model.DirectJob.Inputs
  words : List Word
  expected : RebuildBound.Model.DirectJob.Result

def wordFor (ws : List Word) (family : String) (key : Model.LogicalKey) : Nat :=
  ((ws.find? (fun w => w.family == family && w.key == Model.LogicalKey.toNat key)).map Word.word).getD 0

def parseRecord (ctx : String) (j : Json) : P RebuildBound.Model.Rec := do
  return ⟨Model.LogicalKey.ofNat (← natField j ctx "key"), ← natField j ctx "value", ← boolField j ctx "tombstone"⟩

def parseRecords (ctx : String) (j : Json) : P (List RebuildBound.Model.Rec) := do
  let a ← j.getArr?.mapError (fun _ => s!"{ctx}: expected an array")
  a.toList.mapM (parseRecord ctx)

def parseBucket (ctx : String) (j : Json) : P Bucket := do
  let a ← j.getArr?.mapError (fun _ => s!"{ctx}: expected a lane array")
  a.toList.mapM fun x => if x == Json.null then pure none else some <$> parseRecord ctx x

def parseGeometry (j : Json) : P RebuildBound.Model.DirectJob.Geometry := do
  let r ← objField j "geometry" "ranges"
  let ranges ← match ← strField r "geometry.ranges" "kind" with
    | "direct" => pure RebuildBound.Model.DirectJob.RangePlan.direct
    | "dfs" => do
      pure (RebuildBound.Model.DirectJob.RangePlan.dfs (← natField r "geometry.ranges" "index_bits")
        (← natField r "geometry.ranges" "range_bits") (← natField r "geometry.ranges" "pool_capacity"))
    | _ => throw "geometry.ranges.kind: expected direct or dfs"
  return {
    K := ← natField j "geometry" "K"
    digit := ← natField j "geometry" "digit"
    outputHomes := ← natField j "geometry" "output_homes"
    outputCapacity := ← natField j "geometry" "output_capacity"
    aTierCapacity := ← natField j "geometry" "a_tier_capacity"
    routeCapacity := ← natField j "geometry" "route_capacity"
    radixCapacity := ← natField j "geometry" "radix_capacity"
    insertionCapacity := ← natField j "geometry" "insertion_capacity"
    copyCapacity := ← natField j "geometry" "copy_capacity"
    ranges := ranges }

def parseInputs (j : Json) : P RebuildBound.Model.DirectJob.Inputs := do
  return {
    aMain := ← (← arrField j "inputs" "a_main").toList.mapM (parseBucket "inputs.a_main")
    aTier := ← parseRecords "inputs.a_tier" (← objField j "inputs" "a_tier")
    units := ← (← arrField j "inputs" "units").toList.mapM (parseBucket "inputs.units") }

def parsePhase (s : String) : P RebuildBound.Model.DirectJob.Phase :=
  match s with
  | "prepareA" => pure .prepareA | "produceB" => pure .produceB
  | "distributeA" => pure .distributeA | "finish" => pure .finish
  | "drain" => pure .drain | "publish" => pure .publish
  | _ => throw "event.phase: unrecognized phase"

def parseSite (j : Json) : P RebuildBound.Model.DirectJob.Site := do
  match ← strField j "event.site" "kind" with
  | "route" => return .route (← natField j "event.site" "bit") (← boolField j "event.site" "continuation")
  | "radix" => pure .radix | "bTier" => pure .bTier | "outputTier" => pure .outputTier
  | "dfs" => return .dfs (← natField j "event.site" "depth") (← natField j "event.site" "pre")
  | "insertion" => pure .insertion
  | _ => throw "event.site.kind: unrecognized site"

def parseResult (g : RebuildBound.Model.DirectJob.Geometry) (j : Json) : P RebuildBound.Model.DirectJob.Result := do
  match ← strField j "expected" "kind" with
  | "rejected" =>
    match ← strField j "expected" "reason" with
    | "geometry" => pure (.rejected .geometry)
    | "inputs" => pure (.rejected .inputs)
    | "requiresLaterPhases" => pure (.rejected .requiresLaterPhases)
    | _ => throw "expected.reason: unrecognized rejection"
  | "failed" =>
    let e ← objField j "expected" "event"
    return .failed ⟨⟨← parsePhase (← strField e "event" "phase"),
      ← parseSite (← objField e "event" "site"), ← natField e "event" "ordinal"⟩,
      ← natField e "event" "occupancy", ← natField e "event" "capacity"⟩
  | "published" =>
    let main ← (← arrField j "expected" "main").toList.mapM (parseRecords "expected.main")
    if main.length != g.outputHomes || main.any (fun b => b.length > 64) then
      throw "expected.main: wrong home count or home longer than 64 records"
    return .published ⟨main, ← parseRecords "expected.tier" (← objField j "expected" "tier")⟩
  | _ => throw "expected.kind: expected rejected, failed, or published"

structure Sources where
  geometry : RebuildBound.Model.DirectJob.Geometry
  inputs : RebuildBound.Model.DirectJob.Inputs
  words : List Word

def parseSources (text : String) (format : String := "direct-job-reference/0")
    (evidence : String := "reference-regression") : P Sources := do
  let j ← Json.parse text
  if (← strField j "fixture" "format") != format then
    throw s!"fixture.format: expected {format}"
  if (← strField j "fixture" "evidence") != evidence then
    throw s!"fixture.evidence: expected {evidence}"
  let g ← parseGeometry (← objField j "fixture" "geometry")
  if !decide g.Valid then throw "geometry: violates DirectJob.Geometry.Valid"
  let inp ← parseInputs (← objField j "fixture" "inputs")
  let mut ws : List Word := []
  for e in (← arrField j "fixture" "words").toList do
    let w : Word := ⟨← strField e "words" "family", ← natField e "words" "key", ← natField e "words" "word"⟩
    if w.family != "current" && w.family != "old" then throw "words.family: expected current or old"
    if ws.any (fun x => x.family == w.family && x.key == w.key && x.word != w.word) then
      throw "words: inconsistent repeated family/key assignment"
    ws := ws ++ [w]
  for r in inp.aRecords ++ inp.bRecords do
    if !(ws.any (fun w => w.family == "current" && w.key == Model.LogicalKey.toNat r.key)) then
      throw s!"words: missing current assignment for key {r.key}"
  for r in inp.aRecords do
    if !(ws.any (fun w => w.family == "old" && w.key == Model.LogicalKey.toNat r.key)) then
      throw s!"words: missing old assignment for A key {r.key}"
  if !decide (inp.Valid g (wordFor ws "old")) then
    throw "inputs: violates DirectJob.Inputs.Valid (shape, duplicate key, or old placement)"
  return ⟨g, inp, ws⟩

def parseFixture (text : String) : P Fixture := do
  let f ← parseSources text
  let j ← Json.parse text
  return ⟨f.geometry, f.inputs, f.words,
    ← parseResult f.geometry (← objField j "fixture" "expected")⟩

def recordJson (r : RebuildBound.Model.Rec) : Json :=
  Json.mkObj [("key", toJson (Model.LogicalKey.toNat r.key)), ("value", toJson r.val), ("tombstone", toJson r.tomb)]

def phaseName : RebuildBound.Model.DirectJob.Phase → String
  | .prepareA => "prepareA" | .produceB => "produceB" | .distributeA => "distributeA"
  | .finish => "finish" | .drain => "drain" | .publish => "publish"

def siteJson : RebuildBound.Model.DirectJob.Site → Json
  | .route b c => Json.mkObj [("kind", "route"), ("bit", toJson b), ("continuation", toJson c)]
  | .dfs d p => Json.mkObj [("kind", "dfs"), ("depth", toJson d), ("pre", toJson p)]
  | .radix => Json.mkObj [("kind", "radix")]
  | .bTier => Json.mkObj [("kind", "bTier")]
  | .outputTier => Json.mkObj [("kind", "outputTier")]
  | .insertion => Json.mkObj [("kind", "insertion")]

def eventJson (e : RebuildBound.Model.DirectJob.CheckEvent) : Json :=
  Json.mkObj [("phase", toJson (phaseName e.id.phase)), ("site", siteJson e.id.site),
    ("ordinal", toJson e.id.ordinal), ("occupancy", toJson e.occupancy), ("capacity", toJson e.capacity)]

def resultJson : RebuildBound.Model.DirectJob.Result → Json
  | .rejected reason => Json.mkObj [("kind", "rejected"), ("reason", toJson (match reason with
      | .geometry => "geometry" | .inputs => "inputs" | .requiresLaterPhases => "requiresLaterPhases"))]
  | .failed e => Json.mkObj [("kind", "failed"), ("event", eventJson e)]
  | .published t => Json.mkObj [("kind", "published"),
      ("main", Json.arr ((t.main.map (fun b => Json.arr ((b.map recordJson).toArray))).toArray)),
      ("tier", Json.arr ((t.tier.map recordJson).toArray))]

def run (path text : String) : P (Json × Bool) := do
  let f ← parseFixture text
  let actual := RebuildBound.Model.DirectJob.runDigitOne f.geometry (wordFor f.words "old") (wordFor f.words "current") f.inputs
  let ok := actual == f.expected
  return (Json.mkObj [("file", toJson path), ("job", "direct-digit-one"),
    ("evidence", "reference-regression"), ("comparison", if ok then "pass" else "fail"),
    ("actual", resultJson actual), ("expected", resultJson f.expected)], ok)

end RebuildBound.Oracle.DirectJob
