import RebuildBound.Oracle.OnlineBatchDiff
import RebuildBound.Spec.Model.ApiLowering
import RebuildBound.Spec.Model.ApiAccess

/-! Native public API replay. Original descriptors drive the existing Api,
ApiAccess, PublicApi and Requester models. Native responses never define model
records. Full current units, frozen prefix units, chunk boundaries and all
published tables are compared. The lazy-schedule runs stop before top replacement.
Complete-cycle runs use handover and drain after every public call. Once a top
is rebuilt, the reference history retains only the live winners of the consumed
prefix, followed by the unconsumed suffix. The full dense hierarchy replay also
checks that publication, including every removed tombstone.

For geometry31 the separate sparse initialization check scans all native masks
and checks exact occupied lanes, including the initial and final top. It supports
at most 32 initial records (one half-full input bucket), with no top replacement.
The sparse evaluator calls the model's engineRule.split, omitting empty pairs.
Its executable agreement with dense initReference is checked in SpecTests;
this evaluator is regression tooling, not a new trusted Spec or refinement proof.
-/
namespace RebuildBound.Oracle.PublicApiDiff
open Lean RebuildBound.Model HierarchyDiff

private def boolField (j : Json) (ctx key : String) : P Bool := do
  (← objField j ctx key).getBool?.mapError (fun _ => s!"{ctx}.{key}: expected bool")

/-- A lossless logical payload/flag codec; bytes are converted separately. -/
def codec : Api.Codec where
  pack v b := 2 * v + b.toNat
  payload n := n / 2
  flag n := n % 2 == 1
  payload_pack := by intro v b; cases b <;> simp; omega
  flag_pack := by intro v b; cases b <;> simp

def logicalFor (bits : Nat) (r : MRec) : MRec :=
  { r with val := codec.pack (r.val % 2^bits) (r.val.testBit (bits+5)) }
def logical := logicalFor 8

def storedFor (bits : Nat) (r : MRec) : MRec :=
  { r with val := codec.payload r.val + (if codec.flag r.val then 2^(bits+5) else 0) +
      (if r.tomb then 2^(bits+7) else 0) }
def stored := storedFor 8

def storedBucket (b : Bucket) : Bucket := b.map (Option.map stored)

def parseLane (j : Json) : P PublicApi.Lane := do
  let kind ← match ← strField j "lane" "kind" with
    | "write" => pure PublicApi.Kind.write
    | "read" => pure .read
    | "erase" => pure .erase
    | "exchange" => pure .exchange
    | "readThenWrite" => pure .readThenWrite
    | _ => throw "lane.kind: unknown"
  return ⟨LogicalKey.ofNat (← natField j "lane" "key"), ← natField j "lane" "value",
    ⟨kind, ← boolField j "lane" "value_output", ← boolField j "lane" "insert"⟩⟩

structure ApiState where
  history : List MRec
  requester : Requester.State := ⟨[], []⟩
  requests : List Api.Request := []
  position : Nat := 0
  retired : Nat := 0
  baseLength : Nat := 0

/-- Alternate executable requester semantics can be checked against the same
independently lowered API calls without changing the ordinary Core-only oracle. -/
abbrev RequesterRun := Nat → Requester.State → List Requester.Op → Requester.State

/-- Original public API requests independently produce the expected records. -/
def applyGroupUsing (requesterRun : RequesterRun) (entries : Nat) (batch : Bool) (qs : List Api.Request) (s : ApiState) : ApiState :=
  let rs := Api.referenceRecords codec s.history qs
  let ops := if batch then [Requester.Op.batch rs] else rs.map (fun r => .access r true)
  { s with
    history := s.history ++ rs,
    requester := requesterRun entries s.requester ops,
    requests := s.requests ++ qs, position := s.position + qs.length }

def applyGroup : Nat → Bool → List Api.Request → ApiState → ApiState :=
  applyGroupUsing Requester.run

def checkApiUsing (requesterRun : RequesterRun) (rp : Replay) (j : Json) : P (Nat × Nat) := do
  if rp.valueBytes != 2 && rp.valueBytes != 5 then throw "API replay requires one or four payload bytes"
  let bits := 8 * (rp.valueBytes - 1)
  let storeBucket := fun (b : Bucket) => b.map (Option.map (storedFor bits))
  let a ← objField j "fixture" "api"
  if (← strField a "api" "format") != "public-api/0" then throw "api.format"
  let width ← natField a "api" "width"
  if width == 0 || width > 64 then throw "api.width"
  unless width == (← natField (← objField j "fixture" "config") "config" "batch_width") do
    throw "api.width.native"
  let calls ← arrField a "api" "calls"
  if calls.isEmpty then throw "api.calls: empty evidence"
  let settle := (a.getObjValAs? Bool "settle_after_call").toOption.getD false
  let period := rp.cfg.carryPositions rp.cfg.levels
  if period == 0 then throw "API top carry period is zero"
  if !settle && rp.accesses ≥ period then throw "API top replacement requires settle_after_call"
  if settle && (rp.drive != "eager" || rp.prefixFlushes != 2) then throw "API cycle scheduling metadata"
  let E := 64 * rp.stashBuckets
  let mut s : ApiState := { history := rp.init.map (logicalFor bits), baseLength := rp.init.length }
  let mut groupCount := 0
  for call in calls do
    let mut expectedGroups : List (Nat × Nat) := []
    match ← strField call "call" "kind" with
    | "write" =>
      let key := LogicalKey.ofNat (← natField call "call" "key")
      let value ← natField call "call" "value"
      s := applyGroupUsing requesterRun E false [⟨key, .blindWrite value⟩] s
    | "callback" =>
      let key := LogicalKey.ofNat (← natField call "call" "key")
      let mutableKey ← boolField call "call" "mutable_key"
      let destination ← natField call "call" "destination"
      let delta ← natField call "call" "delta"
      let throws ← boolField call "call" "throws"
      let q : ApiAccess.Request := ⟨key, if mutableKey then .mutableKey else .valueOnly,
        fun v f => if throws then .exception else
          .success (LogicalKey.ofNat destination) ((v + delta + if f then 17 else 31) % 2^bits)⟩
      let old := Api.value codec (DirectPrefix.latest key s.history)
      unless (← natField call "call" "input") == Api.output old &&
          (← boolField call "call" "found") == Api.present old &&
          (← natField call "call" "invocations") == 1 do throw "api.callback.input"
      unless (← boolField call "call" "exception") == throws do throw "api.callback.exception"
      let response := if throws then Json.null else toJson (Api.present old)
      unless (← objField call "call" "returned") == response do throw "api.callback.response"
      expectedGroups := [(s.position, 1)]
      s := applyGroupUsing requesterRun E false (ApiAccess.lower q old) s
    | "batch" =>
      let found ← boolField call "call" "found_output"
      let lanes ← (← arrField call "call" "lanes").toList.mapM parseLane
      let responses ← arrField call "call" "responses"
      if responses.size != lanes.length then throw "api.batch.responses.length"
      let mut h := s.history
      for (lane, response) in lanes.zip responses.toList do
        let old := Api.value codec (DirectPrefix.latest lane.key h)
        let want := PublicApi.response found lane old
        unless (← objField response "response" "value") == toJson want.value &&
            (← objField response "response" "found") == toJson want.found do throw "api.batch.response"
        h := h ++ Api.referenceRecords codec h [PublicApi.request found lane]
      for group in PublicApi.groups width E s.position found lanes do
        match group with
        | .blind lane => s := applyGroupUsing requesterRun E false [PublicApi.request found lane] s
        | .chunk lanes =>
          expectedGroups := expectedGroups ++ [(s.position, lanes.length)]
          s := applyGroupUsing requesterRun E true (lanes.map (PublicApi.request found)) s
    | _ => throw "api.call.kind"
    let nativeGroups ← (← arrField call "call" "groups").toList.mapM fun g => do
      let pair ← g.getArr?
      if pair.size != 2 then throw "api.group: pair required"
      return (← pair[0]!.getNat?, ← pair[1]!.getNat?)
    unless nativeGroups == expectedGroups do throw "api.groups"
    groupCount := groupCount + nativeGroups.length
    unless (← natField call "call" "position") == s.position do throw "api.position"
    let current ← parseLanes "api.current" E (← objField call "call" "current")
    let want := storeBucket (s.requester.current ++ List.replicate (E - s.requester.current.length) none)
    unless current == want do throw s!"api.current at {s.position}"
    let prefixTail := (s.requester.frozen.drop
      (s.requester.frozen.length / rp.prefixFlushes * rp.prefixFlushes)).flatten
    let actual ← parseLanes "api.partial" prefixTail.length (← objField call "call" "partial")
    unless actual == storeBucket prefixTail do throw s!"api.partial at {s.position}"
    if settle then
      let retired := s.position / period * period
      unless (← natField call "call" "top_ordinal") == rp.cfg.seed rp.cfg.levels + s.position / period do
        throw "api.top_ordinal"
      -- The native driver drains only between calls. The two-prefix queue
      -- accommodates its largest call; no top retirement occurs inside a call.
      -- Keep live winners of the consumed prefix, not old versions hidden by
      -- tombstones. All records here came from the API model, not native tables.
      if retired > s.retired then
        let cut := s.baseLength + retired - s.retired
        let base := (DirectPrefix.winners (s.history.take cut)).filter (fun r => !r.tomb)
        s := { s with history := base ++ s.history.drop cut, baseLength := base.length, retired }
  unless s.position == rp.accesses && s.requests.length == rp.ops.size do throw "api.ops.coverage"
  let nativeOps ← arrField j "fixture" "ops"
  for (q, op) in s.requests.zip nativeOps.toList do
    let name ← strField op "op" "op"
    let value ← natField op "op" "value"
    let action ← match name with
      | "read" => pure Api.Action.read
      | "erase" => pure .erase
      | "write" => pure (.write value)
      | "write_np" => pure (.blindWrite value)
      | "exchange" => pure (.exchange value (← boolField op "op" "insert"))
      | _ => throw "api.ops.kind"
    unless LogicalKey.toNat q.key == (← natField op "op" "key") && q.action == action do throw "api.ops.lowering"
  for (ordinal, units) in rp.units.toList do
    let start := (ordinal - rp.cfg.seed 1 - 1) * rp.prefixFlushes
    let want := (s.requester.frozen.drop start).take rp.prefixFlushes |>.map storeBucket
    unless units == want do throw s!"api.units at {ordinal}"
  return (calls.size, groupCount)

def checkApi : Replay → Json → P (Nat × Nat) := checkApiUsing Requester.run

abbrev Sparse := List (Nat × Bucket)

def putBucket (m : Sparse) (i : Nat) (b : Bucket) : Sparse :=
  let rest := m.filter (fun p => p.1 != i)
  if occupied b == 0 then rest else (i,b) :: rest

/-- The one-input-bucket initializer, executing the existing split operation
on occupied pairs. The small-input restriction excludes every spill. -/
def sparseInit (k : Nat) (w : LogicalKey → Nat) (input : List MRec) : Sparse := Id.run do
  let mut m : Sparse := if input.isEmpty then [] else
    [(0, input.map some ++ List.replicate (64 - input.length) none)]
  for bit in [0:k] do
    let pairs := ((m.map fun p => p.1 - if p.1.testBit bit then 2 ^ bit else 0).eraseDups.toArray.qsort (· < ·)).toList
    for i in pairs do
      let a := (m.find? (fun p => p.1 == i)).map (·.2) |>.getD (Bucket.empty 64)
      let b := (m.find? (fun p => p.1 == i + 2 ^ bit)).map (·.2) |>.getD (Bucket.empty 64)
      let p := engineRule.split 64 (dirBit w bit) a b
      m := putBucket (putBucket m i p.1) (i + 2 ^ bit) p.2.1
  return (m.toArray.qsort (fun a b => a.1 < b.1)).toList

def checkSparseTop (rp : Replay) (j : Json) : P Nat := do
  if rp.selected != some "geometry31" then return 0
  if rp.init.isEmpty || rp.init.length > 32 then throw "sparse_top.init: requires 1..32 records"
  let cfg := rp.cfg
  let top := cfg.levels
  if rp.accesses ≥ cfg.carryPositions top then throw "sparse_top: top replacement unsupported"
  let natives := rp.tables.toList.filter (fun t => (coordOf cfg t).1 == top)
  if natives.length != 2 then throw "sparse_top: exactly empty and initialized publication required"
  let snaps ← arrField j "fixture" "sparse_top"
  if snaps.size != 3 then throw "sparse_top: two publications and a final snapshot required"
  let mut seen : List (Nat × String) := []
  for snap in snaps do
    let id ← natField snap "sparse_top" "id"
    let phase ← strField snap "sparse_top" "phase"
    if phase != "publish" && phase != "final" then throw "sparse_top.phase"
    if seen.contains (id,phase) then throw "sparse_top.duplicate"
    seen := (id,phase) :: seen
    let some nt := natives.find? (fun t => t.id == id) | throw "sparse_top.id"
    unless (← pairField snap "sparse_top" "family") == nt.family do throw "sparse_top.family"
    let T := 2 ^ 26
    unless nt.mainBuckets == T && (← natField snap "sparse_top" "scanned_buckets") == T do
      throw "sparse_top.coverage"
    let source := if nt.family.2 == 0 then [] else rp.init
    let words := rp.words.getD nt.family {}
    for r in source do if !words.contains (LogicalKey.toNat r.key) then throw "sparse_top.words"
    let expected := sparseInit 26 (fun k => words.getD (LogicalKey.toNat k) 0) source
    let actual ← (← arrField snap "sparse_top" "main").toList.mapM fun x => do
      let p ← x.getArr?
      if p.size != 2 then throw "sparse_top.main: bucket/lane pair required"
      return (← p[0]!.getNat?, ← parseLanes "sparse_top.bucket" 64 p[1]!)
    unless actual == expected do throw "sparse_top.main"
    let tier ← parseLanes "sparse_top.tier" (64 * nt.tierBuckets) (← objField snap "sparse_top" "tier")
    unless tier.all Option.isNone do throw "sparse_top.tier"
  for nt in natives do
    unless seen.contains (nt.id,"publish") do throw "sparse_top.publication.missing"
    if nt.family.2 != 0 && !seen.contains (nt.id,"final") then throw "sparse_top.final.missing"
  return snaps.size

def run (path text : String) (requireApi : Bool) : P (Json × UInt32) := do
  let j ← Json.parse text
  let rp ← parseReplayJson j
  let (base, code) ← OnlineBatchDiff.runCombined path text
  let extension : P (Nat × Nat × Nat) := do
    let tops ← checkSparseTop rp j
    if !requireApi && rp.selected != some "geometry31" then throw "geometry31 configuration required"
    let (calls, groups) ← if requireApi then checkApi rp j else pure (0,0)
    return (tops,calls,groups)
  match extension with
  | .error e => return (base.setObjVal! "result" "fail" |>.setObjVal! "extension"
      (Json.mkObj [("result","fail"),("error",toJson e)]), max code 1)
  | .ok (tops,calls,groups) =>
    return (base.setObjVal! "extension" (Json.mkObj [
      ("api_calls",toJson calls), ("api_probe_groups",toJson groups),
      ("exact_sparse_top_snapshots",toJson tops), ("result","pass")]), code)
end RebuildBound.Oracle.PublicApiDiff
