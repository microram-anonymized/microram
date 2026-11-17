import spec_tests.ConfigurationFamilyData
import RebuildBound.Oracle.HierarchyDiff

/-! Compare every derived family geometry with fresh allocation-free native
probes. This is finite implementation evidence; the structural proofs are in
`ConfigurationFamily.lean`. No numerical probability certificate is checked.

  lake env lean --run spec_tests/ConfigurationFamilyNative.lean
-/

open Lean RebuildBound.Model RebuildBound.Spec
open RebuildBound.Oracle (natField strField arrField objField)
open RebuildBound.Oracle.HierarchyDiff (parseSep parseTop parsePrep)

namespace ConfigurationFamilyTest.Native

def passName : JobClass → String
  | .ordinary ℓ d => s!"ordinary_L{ℓ}_d{d}"
  | .topPrepare => "top_prepare"
  | .topFinish => "top_finish"
  | .initialization => "initialization"

def naturals (j : Json) (key : String) : Except String (List Nat) := do
  (← arrField j "member" key).toList.mapM Json.getNat?

def checkMember (m : Member) (j : Json) : Except String Unit := do
  let g := m.geometry true
  let cfg := g.cfg
  unless (← strField j "member" "name") == m.name do throw "member name/order"
  unless (← natField j "member" "r0") == m.r0 do throw "r0"
  unless (← natField j "member" "capacity_entries") == g.keyCapacity do throw "capacity"
  unless (← natField j "member" "top_digit") == cfg.topDigit do throw "top digit"
  unless (← natField j "member" "horizon_accesses") == cfg.horizon do throw "horizon"
  unless (← natField j "member" "load") == cfg.load do throw "load"
  unless (← naturals j "level_fanouts") == cfg.fanouts do throw "fanouts"
  let levels := List.range' 1 cfg.levels
  unless (← naturals j "carry_buckets") == levels.map cfg.carry do throw "carry widths"
  unless (← naturals j "level_tier_buckets") == levels.map m.tierPages do throw "tier schedule"
  unless (← naturals j "stash_buckets") == levels.map m.stashPages do throw "stash schedule"
  unless (← naturals j "seeded_carries") == levels.map cfg.seed do throw "initialization seeds"
  let sh ← objField j "member" "shapes"
  let direct ← (← arrField sh "shapes" "direct").toList.mapM
    RebuildBound.Oracle.DirectJob.parseGeometry
  unless direct == (List.range' 1 (cfg.fanout 1)).map g.shapes.direct do
    throw "direct shapes or coverage"
  let sep ← (← arrField sh "shapes" "sep").toList.mapM parseSep
  unless sep == cfg.separatedClasses.zip (g.rows.map Prod.fst) do
    throw "separated shapes or coverage"
  unless (← parseTop (← objField sh "shapes" "top")) == g.shapes.top do throw "top shape"
  unless (← parsePrep (← objField sh "shapes" "prep")) == g.shapes.prep do
    throw "preparation shape"
  unless (← parsePrep (← objField sh "shapes" "init")) == g.shapes.init do
    throw "initialization shape"
  let clocks ← (← arrField j "member" "clocks").toList.mapM fun row => do
    return (← strField row "clock" "name", ← natField row "clock" "exposures")
  unless clocks == cfg.exposures.map (fun (cl, n) => (passName cl, n)) do
    throw "exposure counts or coverage"

def check (j : Json) : Except String Unit := do
  unless (← strField j "fixture" "format") == "configuration-family-structure/1" do
    throw "fixture format"
  let rows ← arrField j "fixture" "members"
  unless rows.size == members.length do throw "member coverage"
  for (m, row) in members.zip rows.toList do
    (checkMember m row).mapError fun e => s!"{m.name}: {e}"

/-- Change one field along a fixed mutation path. -/
def change (j : Json) : List String → (Json → Json) → Json
  | [], f => f j
  | key :: keys, f =>
    j.setObjVal! key (change ((j.getObjVal? key).toOption.getD Json.null) keys f)

def array (f : Array Json → Array Json) (j : Json) : Json :=
  toJson (f (j.getArr?.toOption.getD #[]))

def bump (j : Json) : Json := toJson (j.getNat?.toOption.getD 0 + 1)

def first (path : List String) (f : Json → Json) (j : Json) : Json :=
  change j ["members"] (array fun a => a.modify 0 fun row => change row path f)

def mutations (j : Json) : List (String × Json) :=
  [ ("missing member", change j ["members"] (array fun a => a.extract 1)),
    ("duplicate member", change j ["members"] (array fun a => a.set! 1 (a[0]!))),
    ("member name", first ["name"] (fun _ => toJson "unknown") j),
    ("r0", first ["r0"] bump j),
    ("capacity", first ["capacity_entries"] bump j),
    ("fanout", first ["level_fanouts"] (array fun a => a.modify 0 bump) j),
    ("carry width", first ["carry_buckets"] (array fun a => a.modify 0 bump) j),
    ("tier schedule", first ["level_tier_buckets"] (array fun a => a.modify 0 bump) j),
    ("stash schedule", first ["stash_buckets"] (array fun a => a.modify 0 bump) j),
    ("initialization seed", first ["seeded_carries"] (array fun a => a.modify 0 bump) j),
    ("top digit", first ["top_digit"] bump j),
    ("horizon", first ["horizon_accesses"] bump j),
    ("load", first ["load"] bump j),
    ("missing clock", first ["clocks"] (array fun a => a.extract 1) j),
    ("exposure undercount", first ["clocks"] (array fun a => a.modify 0 fun row =>
      change row ["exposures"] fun n => toJson (n.getNat?.toOption.getD 0 - 1)) j),
    ("missing direct shape", first ["shapes", "direct"] (array fun a => a.extract 1) j),
    ("direct capacity", first ["shapes", "direct"]
      (array fun a => a.modify 0 fun row => change row ["copy_capacity"] bump) j),
    ("direct routing", first ["shapes", "direct"]
      (array fun a => a.modify 1 fun row => change row ["ranges"] fun _ =>
        Json.mkObj [("kind", toJson "dfs"), ("index_bits", toJson (0 : Nat)),
          ("range_bits", toJson (3 : Nat)), ("pool_capacity", toJson (64 : Nat))]) j),
    ("missing separated shape", change j ["members"] (array fun a => a.map fun row =>
      change row ["shapes", "sep"] (array fun rows => rows.extract 1))),
    ("top tier link", first ["shapes", "top", "b_pages"] bump j),
    ("preparation drain", first ["shapes", "prep", "drain_pages"] bump j),
    ("initialization drain", first ["shapes", "init", "drain_pages"] bump j) ]

end ConfigurationFamilyTest.Native

def main (args : List String) : IO UInt32 := do
  let path := args.headD "../analysis/bound_certification/code/configuration_family_structure.json"
  let text ← IO.FS.readFile path
  match Json.parse text with
  | .error e => IO.eprintln e; return 2
  | .ok j =>
    match ConfigurationFamilyTest.Native.check j with
    | .error e => IO.eprintln s!"FAIL: {e}"; return 1
    | .ok () =>
      let mutants := ConfigurationFamilyTest.Native.mutations j
      for (label, bad) in mutants do
        if (ConfigurationFamilyTest.Native.check bad).isOk then
          IO.eprintln s!"FAIL: accepted mutation {label}"
          return 1
      IO.println s!"PASS: {ConfigurationFamilyTest.members.length} native family geometries; {mutants.length} mutations rejected"
      return 0
