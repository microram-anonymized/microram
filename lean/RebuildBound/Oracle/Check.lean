import RebuildBound.Oracle.Fixture
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# The O1 semantic spec, as a checker over a fixture

For a successful ordinary merge (tombstones are kept as live records):

1. conservation: the output main and tier together hold exactly one record per
   key of the complete population `A_main ∪ A_tier ∪ B_main ∪ B_tier`, namely
   the newest version (B beats A), with identical value bytes and tombstone
   flag;
2. placement: every output main record sits in bucket
   `word(merge, key) &&& (out_buckets - 1)`;
3. counts: with `X_v` the number of winners whose home is `v`, main bucket `v`
   holds exactly `min (X_v, 64)` records, the tier holds `∑_v (X_v - 64)⁺`
   records, and every tier record's home `v` has `X_v ≥ 64` and a full main
   bucket;
4. structural sanity of the inputs: `A`'s keys are distinct across
   `A_main ∪ A_tier`, `B`'s across `B_main ∪ B_tier`, positions are in range
   and distinct, every bucket holds at most 64 records.

Nothing here decides *whether the engine should fail*; a failure fixture only
gets check 4. The differential mode (`Diff.lean`) compares the model's verdict.
-/

open Std

namespace RebuildBound.Oracle

/-- Violations: every one is counted, the first `maxShown` are kept. -/
structure Report where
  total : Nat := 0
  shown : Array String := #[]

def maxShown : Nat := 20

abbrev M := StateM Report

def viol (msg : String) : M Unit :=
  modify fun r =>
    { total := r.total + 1
      shown := if r.shown.size < maxShown then r.shown.push msg else r.shown }

/-- Sixteen hex digits, zero padded. -/
def hex16 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  "".pushn '0' (16 - s.length) ++ s

def isPow2 (n : Nat) : Bool := n != 0 && (n &&& (n - 1)) == 0

/-- What the checker learned about a passing fixture. -/
structure Stats where
  /-- Number of winners (distinct keys of the population). -/
  records : Nat := 0
  homes : Nat := 0
  tierRecords : Nat := 0
  mainRecords : Nat := 0
  fullHomes : Nat := 0
  /-- Keys present in both A and B. -/
  shadowed : Nat := 0

/-! ### Check 4: structure of a store and of a source -/

/-- Positions in range and distinct, at most `cap` records per bucket, value
and key widths as the geometry says. -/
def checkStore (name : String) (g : Geometry) (recs : Array Rec)
    (buckets : Nat) : M Unit := do
  let cap := g.bucketCapacity
  let mut seen : HashSet (Nat × Nat) := {}
  let mut counts : HashMap Nat Nat := {}
  for r in recs do
    let who := s!"{name}[key {hex16 r.key}]"
    if r.bucket ≥ buckets then
      viol s!"{who}: bucket {r.bucket} out of range (store has {buckets})"
    if r.lane ≥ cap then
      viol s!"{who}: lane {r.lane} out of range (capacity {cap})"
    if seen.contains (r.bucket, r.lane) then
      viol s!"{who}: position (bucket {r.bucket}, lane {r.lane}) occupied twice"
    seen := seen.insert (r.bucket, r.lane)
    counts := counts.insert r.bucket (counts.getD r.bucket 0 + 1)
    if r.value.length != 2 * g.valueBytes then
      viol s!"{who}: value has {r.value.length / 2} bytes, want {g.valueBytes}"
    if r.key ≥ 256 ^ g.keyBytes then
      viol s!"{who}: key wider than {g.keyBytes} bytes"
  for (b, c) in counts.toList do
    if c > cap then viol s!"{name}: bucket {b} holds {c} records (capacity {cap})"

/-- One source's keys are distinct across its main and its tier. -/
def checkDistinct (name : String) (main tier : Array Rec) : M Unit := do
  let mut seen : HashSet Nat := {}
  for r in main ++ tier do
    if seen.contains r.key then
      viol s!"{name}: key {hex16 r.key} occurs twice"
    seen := seen.insert r.key

def checkGeometry (fx : Fixture) : M Unit := do
  let g := fx.geometry
  if !isPow2 g.outBuckets then
    viol s!"geometry: out_buckets {g.outBuckets} is not a power of two"
  if g.u != 2 ^ g.k then viol s!"geometry: U {g.u} != 2^K (K = {g.k})"
  if g.bucketCapacity == 0 then viol "geometry: bucket_capacity is 0"
  if isPow2 fx.job.digit then
    if g.outBuckets != fx.job.digit * g.u then
      viol s!"geometry: out_buckets {g.outBuckets} != digit * U"
    if g.outBuckets != 2 ^ g.blockBits then
      viol s!"geometry: out_buckets {g.outBuckets} != 2^block_bits"

def checkInputs (fx : Fixture) : M Unit := do
  let g := fx.geometry
  let i := fx.inputs
  checkGeometry fx
  checkStore "A_main" g i.aMain g.olderBuckets
  checkStore "A_tier" g i.aTier (g.olderTierBuckets)
  checkStore "B_main" g i.bMain g.u
  checkStore "B_tier" g i.bTier g.carryTierBuckets
  checkDistinct "A" i.aMain i.aTier
  checkDistinct "B" i.bMain i.bTier

/-! ### Checks 1-3: the merge's output -/

/-- The routing word of every key, for the merge family. -/
def wordMap (fx : Fixture) : M (HashMap Nat Nat) := do
  let mut m : HashMap Nat Nat := {}
  for w in fx.words do
    if w.family == "merge" then
      match m.get? w.key with
      | some old =>
        if old != w.word then
          viol s!"words: key {hex16 w.key} has two different merge words"
      | none => m := m.insert w.key w.word
  return m

def checkOutput (fx : Fixture) : M Stats := do
  let g := fx.geometry
  let i := fx.inputs
  let o := fx.outputs
  let cap := g.bucketCapacity
  let words ← wordMap fx
  -- Structure of the output, positions included.
  checkStore "out_main" g o.main g.outBuckets
  checkStore "out_tier" g o.tier g.outTierBuckets

  -- The winners: B beats A.  (record, source)
  let mut winners : HashMap Nat (Rec × Nat) := {}
  for r in i.aMain ++ i.aTier do winners := winners.insert r.key (r, 1)
  let mut shadowed := 0
  for r in i.bMain ++ i.bTier do
    if winners.contains r.key then shadowed := shadowed + 1
    winners := winners.insert r.key (r, 2)

  -- 1. conservation.
  let mut count : HashMap Nat Nat := {}
  for r in o.main ++ o.tier do
    count := count.insert r.key (count.getD r.key 0 + 1)
    match winners.get? r.key with
    | none => viol s!"conservation: output key {hex16 r.key} is in no input"
    | some (w, src) =>
      if w.value != r.value || w.tombstone != r.tombstone then
        viol s!"conservation: output key {hex16 r.key} is not the newest version (source {src}: value {w.value} tombstone {w.tombstone}; output: value {r.value} tombstone {r.tombstone})"
  for (k, (_, src)) in winners.toList do
    match count.get? k with
    | none => viol s!"conservation: winner {hex16 k} (source {src}) is missing from the output"
    | some 1 => pure ()
    | some n => viol s!"conservation: key {hex16 k} occurs {n} times in the output"

  -- 2. placement, and the population's homes.
  let mask := g.outBuckets - 1
  let homeOf (k : Nat) : Option Nat := (words.get? k).map (· &&& mask)
  for r in o.main do
    match homeOf r.key with
    | none => viol s!"placement: output key {hex16 r.key} has no merge word"
    | some h =>
      if h != r.bucket then
        viol s!"placement: key {hex16 r.key} is in bucket {r.bucket}, its home is {h}"

  -- 3. counts.
  let mut x : Array Nat := Array.replicate g.outBuckets 0
  for (k, _) in winners.toList do
    match homeOf k with
    | none => viol s!"counts: winner {hex16 k} has no merge word"
    | some h => if h < x.size then x := x.modify h (· + 1)
  let mut mainN : Array Nat := Array.replicate g.outBuckets 0
  for r in o.main do
    if r.bucket < mainN.size then mainN := mainN.modify r.bucket (· + 1)
  let mut tierN : Array Nat := Array.replicate g.outBuckets 0
  let mut tierExpected := 0
  for r in o.tier do
    match homeOf r.key with
    | none => viol s!"counts: tier key {hex16 r.key} has no merge word"
    | some h =>
      if h < tierN.size then tierN := tierN.modify h (· + 1)
      if x[h]! < cap then
        viol s!"counts: tier key {hex16 r.key} names home {h}, which has only {x[h]!} < {cap} winners"
      if mainN[h]! != cap then
        viol s!"counts: tier key {hex16 r.key} names home {h}, whose main bucket holds {mainN[h]!} < {cap}"
  let mut fullHomes := 0
  for v in [0:g.outBuckets] do
    let want := min x[v]! cap
    let excess := x[v]! - cap
    tierExpected := tierExpected + excess
    if x[v]! ≥ cap then fullHomes := fullHomes + 1
    if mainN[v]! != want then
      viol s!"counts: main bucket {v} holds {mainN[v]!}, want min(X={x[v]!}, {cap}) = {want}"
    if tierN[v]! != excess then
      viol s!"counts: tier holds {tierN[v]!} records of home {v}, want (X={x[v]!} - {cap})+ = {excess}"
  if o.tier.size != tierExpected then
    viol s!"counts: tier holds {o.tier.size} records, want sum (X_v - {cap})+ = {tierExpected}"

  return { records := winners.size, homes := g.outBuckets,
           tierRecords := o.tier.size, mainRecords := o.main.size,
           fullHomes := fullHomes, shadowed := shadowed }

/-- Everything O1 asks of a fixture whose engine verdict is `success`. -/
def checkSuccess (fx : Fixture) : Stats × Report :=
  let (stats, report) := (do checkInputs fx; checkOutput fx : M Stats).run {}
  (stats, report)

/-- A failure fixture: only the input structure (check 4) applies. -/
def checkFailureInputs (fx : Fixture) : Report :=
  ((checkInputs fx : M Unit).run {}).2

end RebuildBound.Oracle
