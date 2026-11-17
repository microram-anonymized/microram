import RebuildBound.Oracle.Check
import RebuildBound.Spec.Model.Job

/-!
# Differential test: the Lean model against the engine

Builds the model's `Inputs`, `Geom`, `Caps` and word function from a fixture,
runs `RebuildBound.Model.job RebuildBound.Model.engineRule`, and compares:

* O2: verdict (and, on failure, the failing test kind against the engine's
  message);
* O3: lane-exact output (main: bucket, lane, key, value, tombstone; tier: index
  = bucket * C + lane of the engine's tier record);
* O1 on the model's output is run by `Main` through `checkSuccess`, on a
  fixture whose outputs are replaced by `modelFixture`.

Choices where the fixture is ambiguous (see `Spec/Model/ENGINE_D2.md`, section 0):
the pool is `pool_swept_buckets - pool_direct_buckets` buckets (5, i.e. 320
slots), because the swept pool includes the direct B-tier copy; the leaf
capacity is one page (`C`), since the job ignores `dfs_pages`; every stage
stash and the insertion stash hold `stage_stash_buckets * C`; the output tier
`out_tier_buckets * C`.
-/

open Std
open RebuildBound.Model (engineRule)

namespace RebuildBound.Oracle

/-- Model value: the value hex read as a number. -/
def toModelRec (r : Rec) : Model.Rec :=
  { key := Model.LogicalKey.ofNat r.key, val := (parseHex r.value).toOption.getD 0, tomb := r.tombstone }

/-- Lane arrays of `n` buckets of `c` lanes; `none` if a record is out of range
or two records share a position. -/
def toBuckets (n c : Nat) (recs : Array Rec) : Option (List Model.Bucket) := do
  let mut arr : Array (Array (Option Model.Rec)) := Array.replicate n (Array.replicate c none)
  for r in recs do
    if r.bucket ≥ n || r.lane ≥ c then failure
    if (arr[r.bucket]!)[r.lane]!.isSome then failure
    arr := arr.modify r.bucket fun b => b.set! r.lane (some (toModelRec r))
  return arr.toList.map (·.toList)

/-- Records in (bucket, lane) order. -/
def sortedRecs (recs : Array Rec) : List Model.Rec :=
  (recs.qsort fun a b => a.bucket < b.bucket || (a.bucket == b.bucket && a.lane < b.lane)).toList.map toModelRec

def modelGeom (fx : Fixture) : Model.Geom :=
  let g := fx.geometry
  { C := g.bucketCapacity, k := g.k, lo := g.rangeIndexBits
    poolSlots := (g.poolSweptBuckets - g.poolDirectBuckets) * g.bucketCapacity }

def modelCaps (fx : Fixture) : Model.Caps :=
  let g := fx.geometry
  let s := g.stageStashBuckets * g.bucketCapacity
  { stash := fun _ => some s, leaf := some g.bucketCapacity, ins := some s
    out := some (g.outTierBuckets * g.bucketCapacity) }

def modelInputs (fx : Fixture) : Option Model.Inputs := do
  let g := fx.geometry
  let i := fx.inputs
  return { aMain := ← toBuckets g.olderBuckets g.bucketCapacity i.aMain
           aTier := sortedRecs i.aTier
           bMain := ← toBuckets g.u g.bucketCapacity i.bMain
           bTier := sortedRecs i.bTier }

def modelWords (fx : Fixture) : HashMap Nat Nat := Id.run do
  let mut m : HashMap Nat Nat := {}
  for w in fx.words do
    if w.family == "merge" then m := m.insert w.key w.word
  return m

/-- Result of the model on a fixture. -/
inductive ModelResult where
  | ok (out : Model.Output)
  | fail (t : Model.Test)
  | badInput

def runModel (fx : Fixture) : ModelResult :=
  match modelInputs fx with
  | none => .badInput
  | some inp =>
    let ws := modelWords fx
    match Model.job engineRule (modelGeom fx) (modelCaps fx) (fun k => ws.getD (Model.LogicalKey.toNat k) 0) inp with
    | .ok o => .ok o
    | .error t => .fail t

def testKind : Model.Test → String
  | .stash _ => "butterfly"
  | .dfs _ _ => "residual-dfs-partition"
  | .insertion => "fixed-merge-offers"
  | .drain => "residual-drain"

def testDetail : Model.Test → String
  | .stash j => s!"stash(bit {j})"
  | .dfs d p => s!"dfs(depth {d}, pre {p})"
  | .insertion => "insertion"
  | .drain => "drain"

/-- The engine's failing test kind, read off its message. -/
def engineKind (msg : String) : String :=
  match ["butterfly", "residual-dfs-partition", "fixed-merge-offers", "residual-drain"].find?
      (fun k => (msg.splitOn k).length > 1) with
  | some k => k
  | none => "unknown"

/-- Model output as records in a fixture's format (value as padded hex). -/
def outRecs (valueBytes : Nat) (c : Nat) (o : Model.Output) : Array Rec × Array Rec := Id.run do
  let mk (b l : Nat) (r : Model.Rec) : Rec :=
    let s := String.ofList (Nat.toDigits 16 r.val)
    { bucket := b, lane := l, key := Model.LogicalKey.toNat r.key, tombstone := r.tomb
      value := "".pushn '0' (2 * valueBytes - s.length) ++ s }
  let mut main := #[]
  for b in o.main, bi in [0:o.main.length] do
    for s in b, li in [0:b.length] do
      if let some r := s then main := main.push (mk bi li r)
  let mut tier := #[]
  for s in o.tier, ti in [0:o.tier.length] do
    if let some r := s then tier := tier.push (mk (ti / c) (ti % c) r)
  return (main, tier)

def modelFixture (fx : Fixture) (o : Model.Output) : Fixture :=
  let (m, t) := outRecs fx.geometry.valueBytes fx.geometry.bucketCapacity o
  { fx with outputs := { fx.outputs with verdict := "success", main := m, tier := t } }

/-- Lane-exact comparison of the engine's outputs with the model's; the first
`limit` differences. Total number of differences first. -/
def compareOutputs (fx : Fixture) (o : Model.Output) (limit : Nat := 8) : Nat × Array String := Id.run do
  let c := fx.geometry.bucketCapacity
  let (mm, mt) := outRecs fx.geometry.valueBytes c o
  let show_ (r : Rec) := s!"key {hex16 r.key} val {r.value}{if r.tombstone then " tomb" else ""}"
  let mut n := 0
  let mut out : Array String := #[]
  let note (n : Nat) (out : Array String) (s : String) : Nat × Array String :=
    (n + 1, if out.size < limit then out.push s else out)
  -- main, keyed by (bucket, lane)
  let mut em : HashMap (Nat × Nat) Rec := {}
  for r in fx.outputs.main do em := em.insert (r.bucket, r.lane) r
  let mut mo : HashMap (Nat × Nat) Rec := {}
  for r in mm do mo := mo.insert (r.bucket, r.lane) r
  for r in fx.outputs.main do
    match mo.get? (r.bucket, r.lane) with
    | none => (n, out) := note n out s!"main (b{r.bucket},l{r.lane}): engine {show_ r}, model empty"
    | some q =>
      if q.key != r.key || q.value != r.value || q.tombstone != r.tombstone then
        (n, out) := note n out s!"main (b{r.bucket},l{r.lane}): engine {show_ r}, model {show_ q}"
  for q in mm do
    if !(em.contains (q.bucket, q.lane)) then
      (n, out) := note n out s!"main (b{q.bucket},l{q.lane}): engine empty, model {show_ q}"
  let mut et : HashMap Nat Rec := {}
  for r in fx.outputs.tier do et := et.insert (r.bucket * c + r.lane) r
  let mut mot : HashMap Nat Rec := {}
  for r in mt do mot := mot.insert (r.bucket * c + r.lane) r
  for r in fx.outputs.tier do
    let i := r.bucket * c + r.lane
    match mot.get? i with
    | none => (n, out) := note n out s!"tier [{i}]: engine {show_ r}, model empty"
    | some q =>
      if q.key != r.key || q.value != r.value || q.tombstone != r.tombstone then
        (n, out) := note n out s!"tier [{i}]: engine {show_ r}, model {show_ q}"
  for q in mt do
    let i := q.bucket * c + q.lane
    if !(et.contains i) then
      (n, out) := note n out s!"tier [{i}]: engine empty, model {show_ q}"
  return (n, out)

end RebuildBound.Oracle
