import Lean.Data.Json
import RebuildBound.Spec.Model.Config

/-!
# The exposure count against the configuration-space ledger (S8's oracle)

For every candidate of `analysis/bound_certification/code/configuration_space_*.json`, build its `Config`
from the probe's fields and compare:
* `Config.exposures` with the ledger's `clocks` (every pass name but the two
  audit lines `integrated_inventory` and `native_applicability`, which carry
  no exposure);
* `Config.carry ℓ` with `carry_buckets`, `Config.carryPositions ℓ` and
  `Config.seed ℓ` with the probe's `level` and `ordinal_seed` rows.

    lake env lean --run spec_tests/Exposures.lean ../analysis/bound_certification/code

Prints one line per file and a total; exit 1 on any mismatch.
-/

open Lean RebuildBound.Model

def passName : JobClass → String
  | .ordinary ℓ d => s!"ordinary_L{ℓ}_d{d}"
  | .topPrepare => "top_prepare"
  | .topFinish => "top_finish"
  | .initialization => "initialization"

def getNat (j : Json) (k : String) : Except String Nat := do
  let v ← j.getObjVal? k
  v.getNat?

def natList (j : Json) (k : String) : Except String (List Nat) := do
  let a ← (← j.getObjVal? k).getArr?
  a.toList.mapM fun v => v.getNat?

/-- Check one candidate; returns the list of mismatches. -/
def checkCandidate (c : Json) : Except String (List String) := do
  let name ← (← c.getObjVal? "name").getStr?
  let fanouts ← natList c "level_fanouts"
  let carries ← natList c "carry_buckets"
  let D ← getNat c "top_digit"
  let H ← getNat (← c.getObjVal? "configuration") "horizon_accesses"
  let clocks ← (← c.getObjVal? "clocks").getObj?
  let init := (clocks.get? "initialization").isSome
  let cfg : Config := { fanouts, carry1 := carries.headD 0, topDigit := D, load := 32,
                        horizon := H, initialized := init }
  let mut bad : List String := []
  -- exposures against clocks
  let mut seen : List String := []
  for (cl, n) in cfg.exposures do
    let p := passName cl
    seen := p :: seen
    match clocks.get? p with
    | none => bad := s!"{name}: {p} not in clocks" :: bad
    | some v =>
      let e ← getNat v "exposures"
      if e != n then bad := s!"{name}: {p} ledger {e}, Lean {n}" :: bad
  for (k, _) in clocks.toArray do
    if k != "integrated_inventory" && k != "native_applicability" && !seen.contains k then
      bad := s!"{name}: clock {k} not in Lean's exposures" :: bad
  -- geometry rows
  if carries.length != cfg.levels then
    bad := s!"{name}: {carries.length} carry widths for {cfg.levels} levels" :: bad
  for i in [0:carries.length] do
    if cfg.carry (i + 1) != carries.getD i 0 then
      bad := s!"{name}: carry {i + 1} ledger {carries.getD i 0}, Lean {cfg.carry (i + 1)}" :: bad
  let inv ← (← c.getObjVal? "native_inventory").getArr?
  for r in inv do
    let kind ← (← r.getObjVal? "kind").getStr?
    if kind == "level" then
      let ℓ ← getNat r "level"
      let pos ← getNat r "carry_positions"
      if pos != cfg.carryPositions ℓ then
        bad := s!"{name}: level {ℓ} positions ledger {pos}, Lean {cfg.carryPositions ℓ}" :: bad
    if kind == "ordinal_seed" then
      let ℓ ← getNat r "level"
      let s ← getNat r "seeded_carries"
      if s != cfg.seed ℓ then
        bad := s!"{name}: level {ℓ} seed ledger {s}, Lean {cfg.seed ℓ}" :: bad
  return bad

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "../analysis/bound_certification/code"
  let entries ← System.FilePath.readDir dir
  let files := (entries.map (·.path)).filter fun p =>
    p.fileName.any fun n => n.startsWith "configuration_space_" && n.endsWith ".json"
  let files := files.qsort (·.toString < ·.toString)
  let mut total := 0
  let mut failed := 0
  for f in files do
    let s ← IO.FS.readFile f
    match Json.parse s with
    | .error e => IO.println s!"{f}: parse error {e}"; failed := failed + 1
    | .ok j =>
      match j.getObjVal? "candidates" >>= Json.getArr? with
      | .error e => IO.println s!"{f}: {e}"; failed := failed + 1
      | .ok cs =>
        let mut nbad := 0
        for c in cs do
          total := total + 1
          match checkCandidate c with
          | .error e => IO.println s!"{f}: {e}"; nbad := nbad + 1
          | .ok [] => pure ()
          | .ok bad =>
            nbad := nbad + 1
            for b in bad.reverse.take 5 do IO.println s!"  {b}"
        IO.println s!"{f.fileName.getD ""}: {cs.size} candidates, {nbad} mismatched"
        failed := failed + nbad
  IO.println s!"total {total} candidates, {failed} mismatched"
  return if failed == 0 && total > 0 then 0 else 1
