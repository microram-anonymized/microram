import RebuildBound.Oracle.Diff
import RebuildBound.Oracle.TopDiff
import RebuildBound.Spec.Model.Sep

/-!
# Differential test of the general-digit model against the engine

`lake exe oracle --sep <fixture.json>...` runs `RebuildBound.Model.sJob
engineRule` on a `rebuild-fixture/0` fixture of any digit (`fd3`, and the d = 2
dumper `fd2`) and compares it with the engine:

* O2: verdict and, on failure, the failing test kind (`butterfly`,
  `route-level`, `radix-route`, `residual-dfs-partition`,
  `fixed-merge-offers`, `residual-drain`) against the engine's message;
* O3: lane-exact output (main: bucket, lane, key, value, tombstone; tier: by
  (page, lane), the model's tier index being `page · C + lane`);
* O1, the semantic spec of a successful merge, on the engine's output and on
  the model's: conservation (the newest version of every key, once), placement
  at the home `H = (w mod 2^k) + 2^k ((w / 2^k) mod r)`, `min(X_v, C)` main
  records per home, `(X_v - C)₊` tier records per home, each naming a full
  home. O1 applies when the inputs meet the engine's input contract
  (`ENGINE_RADIX.md`, section 7): distinct keys within A and within B, and B's
  main records at their carry buckets; otherwise it reports `premise`.

Geometry (`sepGeom`): every field of `SepGeom` is a fixture field. The
fixture's derived fields (U, digit, block bits, buckets, the DFS pool) are
checked against the model's; a mismatch makes the fixture malformed.
-/

open Lean Std
open RebuildBound.Model (engineRule)

namespace RebuildBound.Oracle.Sep

/-- The general-digit geometry fields that `Fixture.lean` does not read. -/
structure Extra where
  digit : Nat
  oddPart : Nat
  power : Nat
  rangeBits : Nat

def parseExtra (text : String) : P Extra := do
  let j ← Json.parse text
  let g ← objField j "fixture" "geometry"
  return {
    digit := ← natField g "geometry" "digit"
    oddPart := ← natField g "geometry" "odd_part"
    power := ← natField g "geometry" "power"
    rangeBits := ← natField g "geometry" "range_bits" }

def sepGeom (fx : Fixture) (x : Extra) : Model.SepGeom :=
  let g := fx.geometry
  { C := g.bucketCapacity, K := g.k, e := x.power, r := x.oddPart, rangeBits := x.rangeBits
    I := g.rangeIndexBits, stashPages := g.stageStashBuckets, aTierPages := g.olderTierBuckets
    bTierPages := g.carryTierBuckets, tierPages := g.outTierBuckets }

/-- The fixture's derived geometry against the model's. -/
def geomFaults (fx : Fixture) (x : Extra) (sg : Model.SepGeom) : Array String := Id.run do
  let g := fx.geometry
  let mut out := #[]
  if g.u != sg.U then out := out.push s!"U {g.u} != 2^K = {sg.U}"
  if x.digit != sg.d then out := out.push s!"digit {x.digit} != odd_part * 2^power = {sg.d}"
  if g.blockBits != sg.k then out := out.push s!"block_bits {g.blockBits} != K + power = {sg.k}"
  if g.outBuckets != sg.N then out := out.push s!"out_buckets {g.outBuckets} != d U = {sg.N}"
  if g.olderBuckets != (sg.d - 1) * sg.U then
    out := out.push s!"older_buckets {g.olderBuckets} != (d - 1) U"
  if g.poolSweptBuckets - g.poolDirectBuckets != sg.poolPages then
    out := out.push s!"DFS pool {g.poolSweptBuckets - g.poolDirectBuckets} buckets != model {sg.poolPages}"
  if g.poolDirectBuckets != g.carryTierBuckets then
    out := out.push s!"pool_direct_buckets {g.poolDirectBuckets} != carry_tier_buckets"
  if !(decide sg.Valid) then out := out.push "the geometry is outside SepGeom.Valid"
  if g.bucketCapacity == 0 then out := out.push "bucket_capacity is 0"
  return out

/-- Pages of a tier: page `p` lists the records of bucket `p` in lane order. -/
def toPages (n c : Nat) (recs : Array Rec) : Option (List (List Model.Rec)) := do
  let b ← toBuckets n c recs
  return b.map Model.Bucket.recs

def sepInputs (fx : Fixture) : Option Model.SInputs := do
  let g := fx.geometry
  let i := fx.inputs
  if !(Top.positionFaults "A_tier" g.olderTierBuckets g.bucketCapacity i.aTier).isEmpty then failure
  return { aMain := ← toBuckets g.olderBuckets g.bucketCapacity i.aMain
           aTier := sortedRecs i.aTier
           bMain := ← toBuckets g.u g.bucketCapacity i.bMain
           bTier := ← toPages g.carryTierBuckets g.bucketCapacity i.bTier }

inductive Result where
  | ok (out : Model.Output)
  | fail (t : Model.STest)
  | badInput

def runModel (fx : Fixture) (sg : Model.SepGeom) : Result :=
  match sepInputs fx with
  | none => .badInput
  | some inp =>
    let ws := modelWords fx
    match Model.sJob engineRule sg (fun k => ws.getD (Model.LogicalKey.toNat k) 0) inp with
    | .ok o => .ok o
    | .error t => .fail t

def testKind : Model.STest → String
  | .stash _ false => "butterfly"
  | .stash _ true => "route-level"
  | .radix => "radix-route"
  | .dfs _ _ => "residual-dfs-partition"
  | .insertion => "fixed-merge-offers"
  | .drain => "residual-drain"

def testDetail : Model.STest → String
  | .stash j c => s!"stash(bit {j}{if c then ", continuation" else ""})"
  | .radix => "radix"
  | .dfs d p => s!"dfs(depth {d}, pre {p})"
  | .insertion => "insertion"
  | .drain => "drain"

/-- The engine's failing test kind, read off its message (`... at <kind>;`). -/
def engineKind (msg : String) : String :=
  match ["butterfly", "route-level", "radix-route", "residual-dfs-partition",
      "fixed-merge-offers", "residual-drain"].find? (fun k => (msg.splitOn s!"at {k};").length > 1) with
  | some k => k
  | none => "unknown"

/-! ### The input contract and O1 -/

/-- Structural faults of the inputs (positions, distinct keys): a fixture with
any is malformed for the model. -/
def inputFaults (fx : Fixture) : Array String :=
  let g := fx.geometry
  let i := fx.inputs
  Top.positionFaults "A_main" g.olderBuckets g.bucketCapacity i.aMain ++
    Top.positionFaults "A_tier" g.olderTierBuckets g.bucketCapacity i.aTier ++
    Top.positionFaults "B_main" g.u g.bucketCapacity i.bMain ++
    Top.positionFaults "B_tier" g.carryTierBuckets g.bucketCapacity i.bTier

/-- Breaks of the engine's input contract that O1 relies on. -/
def premiseFaults (fx : Fixture) (words : HashMap Nat Nat) : Array String := Id.run do
  let i := fx.inputs
  let mut out := #[]
  let dup (name : String) (recs : Array Rec) : Array String := Id.run do
    let mut seen : HashSet Nat := {}
    let mut o := #[]
    for r in recs do
      if seen.contains r.key then o := o.push s!"{name}: key {hex16 r.key} occurs twice"
      seen := seen.insert r.key
    return o
  out := out ++ dup "A" (i.aMain ++ i.aTier) ++ dup "B" (i.bMain ++ i.bTier)
  for r in i.bMain do
    match words.get? r.key with
    | none => out := out.push s!"B_main key {hex16 r.key} has no merge word"
    | some t =>
      if t % fx.geometry.u != r.bucket then
        out := out.push s!"B_main key {hex16 r.key} sits in bucket {r.bucket}, its carry bucket is {t % fx.geometry.u}"
  for r in i.aMain ++ i.aTier ++ i.bTier do
    if !(words.contains r.key) then out := out.push s!"key {hex16 r.key} has no merge word"
  return out

/-- O1 on an output (main buckets and tier pages): the first `limit` violations
and their number. -/
def checkO1 (fx : Fixture) (sg : Model.SepGeom) (words : HashMap Nat Nat) (main tier : Array Rec)
    (limit : Nat := 8) : Nat × Array String := Id.run do
  let c := sg.C
  let mut n := 0
  let mut out : Array String := #[]
  let note (n : Nat) (out : Array String) (s : String) : Nat × Array String :=
    (n + 1, if out.size < limit then out.push s else out)
  for f in Top.positionFaults "main" sg.N c main ++ Top.positionFaults "tier" sg.tierPages c tier do
    (n, out) := note n out f
  let i := fx.inputs
  -- winners: B beats A
  let mut winners : HashMap Nat Rec := {}
  for r in i.aMain ++ i.aTier do winners := winners.insert r.key r
  for r in i.bMain ++ i.bTier do winners := winners.insert r.key r
  let homeOf (key : Nat) : Nat := sg.homeOf (words.getD key 0)
  -- conservation
  let mut count : HashMap Nat Nat := {}
  for r in main ++ tier do
    count := count.insert r.key (count.getD r.key 0 + 1)
    match winners.get? r.key with
    | none => (n, out) := note n out s!"conservation: output key {hex16 r.key} is in no input"
    | some w =>
      if w.value != r.value || w.tombstone != r.tombstone then
        (n, out) := note n out s!"conservation: key {hex16 r.key} is not the newest version"
  for (key, _) in winners.toList do
    match count.get? key with
    | some 1 => pure ()
    | some m => (n, out) := note n out s!"conservation: key {hex16 key} occurs {m} times"
    | none => (n, out) := note n out s!"conservation: winner {hex16 key} is missing"
  -- placement and counts
  let mut x : Array Nat := Array.replicate sg.N 0
  for (key, _) in winners.toList do
    let h := homeOf key
    if h < sg.N then x := x.modify h (· + 1)
  let mut mainN : Array Nat := Array.replicate sg.N 0
  for r in main do
    if homeOf r.key != r.bucket then
      (n, out) := note n out s!"placement: key {hex16 r.key} in bucket {r.bucket}, home {homeOf r.key}"
    if r.bucket < sg.N then mainN := mainN.modify r.bucket (· + 1)
  let mut tierN : Array Nat := Array.replicate sg.N 0
  for r in tier do
    let h := homeOf r.key
    if h < sg.N then
      tierN := tierN.modify h (· + 1)
      if mainN[h]! != c then
        (n, out) := note n out s!"counts: tier key {hex16 r.key} names home {h}, which holds {mainN[h]!} < {c}"
  for v in [0:sg.N] do
    if mainN[v]! != min x[v]! c then
      (n, out) := note n out s!"counts: home {v} holds {mainN[v]!}, want min({x[v]!}, {c})"
    if tierN[v]! != x[v]! - c then
      (n, out) := note n out s!"counts: tier holds {tierN[v]!} records of home {v}, want {x[v]! - c}"
  return (n, out)

/-! ### O3 -/

def compareOutputs (fx : Fixture) (mm mt : Array Rec) (limit : Nat := 8) : Nat × Array String :=
  Id.run do
  let show_ (r : Rec) := s!"key {hex16 r.key} val {r.value}{if r.tombstone then " tomb" else ""}"
  let mut n := 0
  let mut out : Array String := #[]
  let note (n : Nat) (out : Array String) (s : String) : Nat × Array String :=
    (n + 1, if out.size < limit then out.push s else out)
  let cmp (name : String) (eng mod : Array Rec) (n : Nat) (out : Array String) :
      Nat × Array String := Id.run do
    let mut n := n
    let mut out := out
    let mut em : HashMap (Nat × Nat) Rec := {}
    for r in eng do em := em.insert (r.bucket, r.lane) r
    let mut mo : HashMap (Nat × Nat) Rec := {}
    for r in mod do mo := mo.insert (r.bucket, r.lane) r
    for r in eng do
      match mo.get? (r.bucket, r.lane) with
      | none => (n, out) := note n out s!"{name} ({r.bucket},{r.lane}): engine {show_ r}, model empty"
      | some q =>
        if q.key != r.key || q.value != r.value || q.tombstone != r.tombstone then
          (n, out) := note n out s!"{name} ({r.bucket},{r.lane}): engine {show_ r}, model {show_ q}"
    for q in mod do
      if !(em.contains (q.bucket, q.lane)) then
        (n, out) := note n out s!"{name} ({q.bucket},{q.lane}): engine empty, model {show_ q}"
    return (n, out)
  (n, out) := cmp "main" fx.outputs.main mm n out
  (n, out) := cmp "tier" fx.outputs.tier mt n out
  return (n, out)

/-! ### One fixture -/

/-- A report line, typed so that string literals become `Json`. -/
def F (l : List (String × Json)) : List (String × Json) := l

/-- The report line of one fixture and whether everything passed. -/
def run (text : String) (fx : Fixture) : List (String × Json) × Bool :=
  match parseExtra text with
  | .error e => (F [("o1", "malformed"), ("error", toJson e)], false)
  | .ok x =>
  let sg := sepGeom fx x
  let gf := geomFaults fx x sg
  if !gf.isEmpty then (F [("o1", "malformed"), ("error", toJson gf.toList)], false) else
  let inf := inputFaults fx
  if !inf.isEmpty then (F [("o1", "malformed"), ("error", toJson (inf.toList.take 8))], false) else
  let words := modelWords fx
  let prem := premiseFaults fx words
  let digit : List (String × Json) := F [("digit", toJson sg.d)]
  match runModel fx sg with
  | .badInput => (digit ++ F [("o2", "fail"), ("model", "bad-input")], false)
  | .fail t =>
    let base := digit ++ F [("o1", "skipped"), ("engine", toJson fx.outputs.verdict)]
    if fx.outputs.verdict == "failure" then
      let ek := engineKind fx.outputs.message
      let km := testKind t == ek
      (base ++ F [("o2", "pass"), ("model", "failure"), ("engine_kind", toJson ek),
        ("model_kind", toJson (testKind t)), ("model_test", toJson (testDetail t)),
        ("kind", if km then "match" else "mismatch"), ("o3", "skipped")], km)
    else
      (base ++ F [("o2", "fail"), ("model", "failure"), ("model_kind", toJson (testKind t)),
        ("model_test", toJson (testDetail t)), ("o3", "skipped")], false)
  | .ok o =>
    if fx.outputs.verdict == "failure" then
      (digit ++ F [("o1", "skipped"), ("engine", "failure"), ("o2", "fail"), ("model", "success"),
        ("engine_kind", toJson (engineKind fx.outputs.message)), ("o3", "skipped")], false)
    else
      let (mm, mt) := outRecs fx.geometry.valueBytes sg.C o
      let (nd, diffs) := compareOutputs fx mm mt
      let o3 : List (String × Json) :=
        if nd == 0 then F [("o3", "pass")] else F [("o3", "fail"), ("diff_count", toJson nd), ("diff", toJson diffs)]
      if !prem.isEmpty then
        (digit ++ F [("o1", "premise"), ("premise", toJson (prem.toList.take 4)), ("o2", "pass"),
          ("model", "success")] ++ o3, nd == 0)
      else
        let (ne, ve) := checkO1 fx sg words fx.outputs.main fx.outputs.tier
        let (nm, vm) := checkO1 fx sg words mm mt
        let o1 : List (String × Json) :=
          if ne == 0 then F [("o1", "pass")] else F [("o1", "fail"), ("violations", toJson ve)]
        let o1m : List (String × Json) :=
          if nm == 0 then F [("o1_model", "pass")] else F [("o1_model", "fail"), ("model_violations", toJson vm)]
        (digit ++ o1 ++ o1m ++ F [("o2", "pass"), ("model", "success")] ++ o3,
          ne == 0 && nm == 0 && nd == 0)

end RebuildBound.Oracle.Sep
