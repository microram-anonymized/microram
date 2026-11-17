import RebuildBound.Proofs.Inventory31
import RebuildBound.Proofs.Geometry31
import RebuildBound.Oracle.HierarchyDiff

/-!
Compare every shape and exposure with the source-hashed, allocation-free
native fixture. Deliberate mutations must be rejected. This is geometry
correspondence evidence, not a native execution or probability proof.

  lake env lean --run spec_tests/Configuration31.lean ../analysis/bound_certification/code/lean_configuration_2p31.json
-/

open Lean RebuildBound.Model RebuildBound.Spec
open RebuildBound.Oracle (natField strField arrField objField)
open RebuildBound.Oracle.HierarchyDiff (parseSep parseTop parsePrep)

namespace Configuration31Test

def passName : JobClass → String
  | .ordinary ℓ d => s!"ordinary_L{ℓ}_d{d}"
  | .topPrepare => "top_prepare"
  | .topFinish => "top_finish"
  | .initialization => "initialization"

def check (j : Json) : Except String Unit := do
  let sh ← objField j "fixture" "shapes"
  let direct ← (← arrField sh "shapes" "direct").toList.mapM
    RebuildBound.Oracle.DirectJob.parseGeometry
  let wantDirect := (List.range' 1 (config31.fanout 1)).map geometry31.shapes.direct
  unless direct == wantDirect do throw "direct shapes"
  let sep ← (← arrField sh "shapes" "sep").toList.mapM parseSep
  unless sep == config31.separatedClasses.zip (separated31.map Prod.fst) do
    throw "separated shapes or coverage"
  unless (← parseTop (← objField sh "shapes" "top")) == geometry31.shapes.top do throw "top shape"
  unless (← parsePrep (← objField sh "shapes" "prep")) == geometry31.shapes.prep do throw "preparation shape"
  unless (← parsePrep (← objField sh "shapes" "init")) == geometry31.shapes.init do throw "initialization shape"
  let fanouts ← (← arrField j "fixture" "level_fanouts").toList.mapM Json.getNat?
  unless fanouts == config31.fanouts do throw "fanouts"
  let carries ← (← arrField j "fixture" "carry_buckets").toList.mapM Json.getNat?
  unless carries == (List.range' 1 config31.levels).map config31.carry do throw "carry widths"
  let tiers ← (← arrField j "fixture" "level_tier_buckets").toList.mapM Json.getNat?
  unless tiers == (List.range' 1 config31.levels).map tierPages31 do throw "tier schedule"
  let stashes ← (← arrField j "fixture" "stash_buckets").toList.mapM Json.getNat?
  unless stashes == (List.range' 1 config31.levels).map stashPages31 do throw "stash schedule"
  let cfg ← objField j "fixture" "configuration"
  unless (← natField cfg "configuration" "horizon_accesses") == config31.horizon do throw "horizon"
  unless (← natField j "fixture" "top_digit") == config31.topDigit do throw "top digit"
  let clocks ← (← objField j "fixture" "clocks").getObj?
  unless clocks.size == config31.exposures.length do throw "exposure coverage"
  for (cl, n) in config31.exposures do
    let entry ← match clocks.get? (passName cl) with
      | some x => pure x
      | none => throw s!"missing exposure {passName cl}"
    unless (← natField entry "clock" "exposures") == n do throw s!"exposure {passName cl}"
  let obligations ← arrField j "fixture" "certificate_inventory"
  let wantNames := (config31.exposures.filter fun p => match p.1 with
    | .ordinary ℓ d => ℓ == 1 || d != 1
    | _ => true).map (fun p => passName p.1)
  let names ← obligations.toList.mapM (fun r => strField r "obligation" "name")
  unless names == wantNames do throw "certificate coverage"
  for row in obligations do
    let name ← strField row "obligation" "name"
    let some (cl, n) := config31.exposures.find? (fun p => passName p.1 == name)
      | throw "unknown certificate"
    unless (← natField row "obligation" "exposures") == n do throw "certificate exposure"
    let reused := match cl with
      | .ordinary ℓ d => ℓ == 1 || reusedClasses31.contains (ℓ, d)
      | _ => false
    unless (← strField row "obligation" "numerics") == (if reused then "reused" else "new") do
      throw "certificate reuse"
    match cl with
    | .ordinary ℓ d =>
      let K := (config31.carry ℓ).log2 + val2 d
      let r := d / 2 ^ val2 d
      let heavy := 2 ^ (64 - K) % r
      unless (← natField row "obligation" "heavy_classes") == heavy &&
          (← natField row "obligation" "light_classes") == r - heavy do
        throw "finite-word class multiplicities"
    | _ => pure ()
  let law ← objField j "fixture" "law_parameters"
  unless (← natField law "law" "word_bits") == 64 &&
      (← natField law "law" "load") == config31.load do throw "law parameters"
  let cuts ← (← arrField law "law" "ordinary_cutoffs").toList.mapM Json.getNat?
  unless cuts == [256, 256] do throw "ordinary cutoffs"

/-- Change one object field along a fixed JSON path. -/
def change (j : Json) : List String → (Json → Json) → Json
  | [], f => f j
  | k :: ks, f => j.setObjVal! k (change ((j.getObjVal? k).toOption.getD Json.null) ks f)

def mutations (j : Json) : List (String × Json) :=
  let num (n : Nat) : Json := toJson n
  let firstField (k : String) (v : Json) (a : Json) : Json :=
    toJson ((a.getArr?.toOption.getD #[]).modify 0 fun r => r.setObjVal! k v)
  [ ("missing row", change j ["shapes", "sep"] fun a =>
        toJson ((a.getArr?.toOption.getD #[]).extract 1)),
    ("carry width", change j ["carry_buckets"] fun a =>
        toJson ((a.getArr?.toOption.getD #[]).set! 0 (num 32))),
    ("tier capacity", change j ["shapes", "sep"] (firstField "b_tier_pages" (num 9))),
    ("direct capacity", change j ["shapes", "direct"] (firstField "copy_capacity" (num 128))),
    ("initialization drain", change j ["shapes", "init", "drain_pages"] fun _ => num 4),
    ("preparation drain", change j ["shapes", "prep", "drain_pages"] fun _ => num 3),
    ("exposure count", change j ["clocks", "ordinary_L1_d1", "exposures"] fun _ => num 0),
    ("class multiplicity", change j ["certificate_inventory"] fun a =>
        toJson ((a.getArr?.toOption.getD #[]).map fun row =>
          if (row.getObjValAs? String "name").toOption == some "ordinary_L3_d7" then
            (row.setObjVal! "heavy_classes" (num 1)).setObjVal! "light_classes" (num 6)
          else row)),
    ("reuse classification", change j ["certificate_inventory"] (firstField "numerics" (toJson "new"))) ]

end Configuration31Test

def main (args : List String) : IO UInt32 := do
  let path := args.headD "../analysis/bound_certification/code/lean_configuration_2p31.json"
  let text ← IO.FS.readFile path
  match Json.parse text with
  | .error e => IO.eprintln e; return 2
  | .ok j =>
    match Configuration31Test.check j with
    | .error e => IO.eprintln s!"FAIL: {e}"; return 1
    | .ok () =>
      let mutants := Configuration31Test.mutations j
      for (label, bad) in mutants do
        if (Configuration31Test.check bad).isOk then
          IO.eprintln s!"FAIL: accepted mutation {label}"
          return 1
      IO.println s!"PASS: 4 direct, 38 separated, top/prep/init; 51 exposures; {mutants.length} mutations rejected"
      return 0
