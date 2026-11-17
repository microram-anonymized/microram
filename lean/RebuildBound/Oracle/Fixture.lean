import Lean.Data.Json

/-!
# Fixture reader of the differential-test oracle

Parses a `rebuild-fixture/0` JSON file written by `oracle/fixture_dump.cpp`
into plain structures.  Only core `Lean` is imported (no Mathlib), so that the
`oracle` executable links quickly.

Keys, routing words and seeds are hex strings in the file and `Nat` here.  A
record's value stays a lower-case hex string: the checker only ever compares
values for equality.  Every problem found here is a `malformed` fixture (the
oracle's exit code 2), as opposed to a spec violation in a well-formed one.
-/

open Lean

namespace RebuildBound.Oracle

/-- One stored record of a published table or tier: where it sits, its key, its
value (all value bytes, meta byte last, as hex) and the tombstone flag. -/
structure Rec where
  bucket : Nat
  lane : Nat
  key : Nat
  value : String
  tombstone : Bool
  deriving Repr, BEq, Inhabited

structure Job where
  kind : String
  digit : Nat
  level : Nat
  separatedSources : Bool
  shape : String
  seed : Nat
  deriving Repr

/-- The public geometry of the job: the fields the checker reads. -/
structure Geometry where
  bucketCapacity : Nat
  keyBytes : Nat
  valueBytes : Nat
  /-- U, the carry's bucket count. -/
  u : Nat
  /-- K = log2 U. -/
  k : Nat
  blockBits : Nat
  outBuckets : Nat
  olderBuckets : Nat
  olderTierBuckets : Nat
  carryTierBuckets : Nat
  outTierBuckets : Nat
  stageStashBuckets : Nat
  /-- log2 of the homes per coarse DFS range (`range_index_bits`). -/
  rangeIndexBits : Nat
  /-- Swept pool buckets and the direct B-tier copy (`pool_swept_buckets`,
  `pool_direct_buckets`); the DFS pool is their difference. -/
  poolSweptBuckets : Nat
  poolDirectBuckets : Nat
  deriving Repr

structure Family where
  level : Nat
  ordinal : Nat
  nonceLo : Nat
  nonceHi : Nat
  deriving Repr

structure Inputs where
  aMain : Array Rec
  aTier : Array Rec
  bMain : Array Rec
  bTier : Array Rec

structure WordEntry where
  family : String
  key : Nat
  word : Nat
  deriving Repr

structure Outputs where
  verdict : String
  message : String
  main : Array Rec
  tier : Array Rec

structure Fixture where
  format : String
  job : Job
  geometry : Geometry
  /-- The merge family (the only one this fixture kind has). -/
  merge : Family
  inputs : Inputs
  words : Array WordEntry
  outputs : Outputs

/-! ### Small parsing combinators -/

abbrev P := Except String

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Big-endian hex digits to a number; rejects the empty string and any
non-hex character. -/
def parseHex (s : String) : P Nat := do
  if s.isEmpty then throw "empty hex string"
  let mut acc := 0
  for c in s.toList do
    match hexDigit? c with
    | some d => acc := acc * 16 + d
    | none => throw s!"bad hex digit '{c}' in \"{s}\""
  return acc

def isHexString (s : String) : Bool :=
  s.toList.all fun c => (hexDigit? c).isSome

def objField (j : Json) (ctx k : String) : P Json :=
  match j.getObjVal? k with
  | .ok v => pure v
  | .error _ => throw s!"{ctx}: missing field \"{k}\""

def natField (j : Json) (ctx k : String) : P Nat := do
  match (← objField j ctx k).getNat? with
  | .ok n => pure n
  | .error _ => throw s!"{ctx}.{k}: expected a natural number"

def strField (j : Json) (ctx k : String) : P String := do
  match (← objField j ctx k).getStr? with
  | .ok s => pure s
  | .error _ => throw s!"{ctx}.{k}: expected a string"

def boolField (j : Json) (ctx k : String) : P Bool := do
  match (← objField j ctx k).getBool? with
  | .ok b => pure b
  | .error _ => throw s!"{ctx}.{k}: expected a boolean"

def arrField (j : Json) (ctx k : String) : P (Array Json) := do
  match (← objField j ctx k).getArr? with
  | .ok a => pure a
  | .error _ => throw s!"{ctx}.{k}: expected an array"

def hexField (j : Json) (ctx k : String) : P Nat := do
  match parseHex (← strField j ctx k) with
  | .ok n => pure n
  | .error e => throw s!"{ctx}.{k}: {e}"

/-! ### Structures -/

def parseRec (ctx : String) (j : Json) : P Rec := do
  let value := (← strField j ctx "value").toLower
  if !(isHexString value) || value.length % 2 != 0 || value.isEmpty then
    throw s!"{ctx}.value: expected a non-empty even-length hex string"
  return {
    bucket := ← natField j ctx "bucket"
    lane := ← natField j ctx "lane"
    key := ← hexField j ctx "key"
    value := value
    tombstone := ← boolField j ctx "tombstone" }

def parseRecs (ctx : String) (j : Json) (k : String) : P (Array Rec) := do
  let arr ← arrField j ctx k
  let mut out := #[]
  for h : i in [0:arr.size] do
    out := out.push (← parseRec s!"{ctx}.{k}[{i}]" arr[i])
  return out

def parseJob (j : Json) : P Job := do
  let ctx := "job"
  return {
    kind := ← strField j ctx "kind"
    digit := ← natField j ctx "digit"
    level := ← natField j ctx "level"
    separatedSources := ← boolField j ctx "separated_sources"
    shape := ← strField j ctx "shape"
    seed := ← hexField j ctx "seed" }

def parseGeometry (j : Json) : P Geometry := do
  let ctx := "geometry"
  return {
    bucketCapacity := ← natField j ctx "bucket_capacity"
    keyBytes := ← natField j ctx "key_bytes"
    valueBytes := ← natField j ctx "value_bytes"
    u := ← natField j ctx "U"
    k := ← natField j ctx "K"
    blockBits := ← natField j ctx "block_bits"
    outBuckets := ← natField j ctx "out_buckets"
    olderBuckets := ← natField j ctx "older_buckets"
    olderTierBuckets := ← natField j ctx "older_tier_buckets"
    carryTierBuckets := ← natField j ctx "carry_tier_buckets"
    outTierBuckets := ← natField j ctx "out_tier_buckets"
    stageStashBuckets := ← natField j ctx "stage_stash_buckets"
    rangeIndexBits := ← natField j ctx "range_index_bits"
    poolSweptBuckets := ← natField j ctx "pool_swept_buckets"
    poolDirectBuckets := ← natField j ctx "pool_direct_buckets" }

def parseFamily (j : Json) : P Family := do
  let ctx := "families.merge"
  return {
    level := ← natField j ctx "level"
    ordinal := ← natField j ctx "ordinal"
    nonceLo := ← hexField j ctx "nonce_lo"
    nonceHi := ← hexField j ctx "nonce_hi" }

def parseInputs (j : Json) : P Inputs := do
  let ctx := "inputs"
  return {
    aMain := ← parseRecs ctx j "A_main"
    aTier := ← parseRecs ctx j "A_tier"
    bMain := ← parseRecs ctx j "B_main"
    bTier := ← parseRecs ctx j "B_tier" }

def parseWords (j : Json) : P (Array WordEntry) := do
  let arr ← arrField j "fixture" "words"
  let mut out := #[]
  for h : i in [0:arr.size] do
    let ctx := s!"words[{i}]"
    let e := arr[i]
    out := out.push {
      family := ← strField e ctx "family"
      key := ← hexField e ctx "key"
      word := ← hexField e ctx "word" }
  return out

def parseOutputs (j : Json) : P Outputs := do
  let ctx := "outputs"
  let verdict ← strField j ctx "verdict"
  if verdict != "success" && verdict != "failure" then
    throw s!"outputs.verdict: expected \"success\" or \"failure\", got \"{verdict}\""
  return {
    verdict := verdict
    message := ← strField j ctx "message"
    main := ← parseRecs ctx j "main"
    tier := ← parseRecs ctx j "tier" }

/-- Parse a whole fixture from JSON text. -/
def parseFixture (text : String) : P Fixture := do
  let j ← Json.parse text
  let format ← strField j "fixture" "format"
  if format != "rebuild-fixture/0" then
    throw s!"unsupported fixture format \"{format}\" (want \"rebuild-fixture/0\")"
  let families ← objField j "fixture" "families"
  return {
    format := format
    job := ← parseJob (← objField j "fixture" "job")
    geometry := ← parseGeometry (← objField j "fixture" "geometry")
    merge := ← parseFamily (← objField families "families" "merge")
    inputs := ← parseInputs (← objField j "fixture" "inputs")
    words := ← parseWords j
    outputs := ← parseOutputs (← objField j "fixture" "outputs") }

end RebuildBound.Oracle
