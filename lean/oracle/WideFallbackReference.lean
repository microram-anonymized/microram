import RebuildBound.Oracle.PublicApiDiff
import RebuildBound.Spec.NativeMatch.Api

/-!
Additional finite replay of the updated NativeMatchDispatch.requesterStep.
The ordinary hierarchy/API/view oracle remains Core/Std-only. This standalone
runner imports the extended model and substitutes its actual fallback requester
step into the same independent public-call lowering and lane/state comparisons.
Stored keys are the complete native bytes, independently verified by OpenSSL
by fallback_wide_tests.py. No probability theorem or C++ refinement is asserted.
With `--vp2` (recorders built with VP2INTERSECT), fixtures with 16-byte stored
keys (user keys of 16+ bytes) use the production dense branch on EVERY batch
page: the approximate half match, wider than native's own selection (>= 64
lanes, >= 16 dense buckets), which must still agree with native. Narrower
stored keys never take that branch natively and stay exact.
-/
open Lean Std RebuildBound.Model RebuildBound.Oracle
open RebuildBound.Oracle.HierarchyDiff RebuildBound.Oracle.PublicApiDiff
open RebuildBound.Spec

private def check (vp2 : Bool) (j : Json) : P (Nat × Nat) := do
  let rp ← parseReplayJson j
  let wide ← objField j "fixture" "wide_key_replay"
  let entries ← arrField wide "wide_key_replay" "stored_keys"
  if entries.isEmpty then throw "stored keys: empty evidence"
  let mut keys : HashMap Nat (Fin (2^128)) := {}
  for e in entries do
    let k ← natField e "stored key" "key"
    let v ← natField e "stored key" "stored"
    if keys.contains k then throw "stored keys: duplicate logical key"
    if h : v < 2^128 then keys := keys.insert k ⟨v,h⟩
    else throw "stored keys: out of range"
  for op in rp.ops do
    unless keys.contains op.key do throw "stored keys: missing operation"
  for r in rp.init do
    unless keys.contains r.key.toNat do throw "stored keys: missing initializer"
  let stored := fun (k : LogicalKey) => keys.getD k.toNat 0
  let cfg ← objField j "fixture" "config"
  let cross := vp2 && 16 ≤ (← natField cfg "config" "key_bytes")
  let run : RequesterRun := fun entries st ops =>
    ops.foldl (NativeMatchDispatch.requesterStep
      (fun _ => .tile cross 64 [32]) stored entries) st
  checkApiUsing run rp j

def main (args : List String) : IO UInt32 := do
  let vp2 := args.head? == some "--vp2"
  let args := if vp2 then args.tail else args
  if args.isEmpty then
    IO.eprintln "usage: lake env lean --run oracle/WideFallbackReference.lean [--vp2] FIXTURE.json ..."
    return 2
  let mut exitCode : UInt32 := 0
  for path in args do
    let text ← IO.FS.readFile path
    let result := do check vp2 (← Json.parse text)
    match result with
    | .ok (calls,groups) =>
      IO.println (Json.mkObj [("file",toJson path),("result","pass"),
        ("model",toJson (if vp2 then "NativeMatchDispatch.requesterStep, VP2 enabled at stored width 16"
          else "NativeMatchDispatch.requesterStep, VP2 disabled")),
        ("api_calls",toJson calls),("probe_groups",toJson groups)]).compress
    | .error error =>
      IO.println (Json.mkObj [("file",toJson path),("result","fail"),("error",toJson error)]).compress
      exitCode := 1
  return exitCode
