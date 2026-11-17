import RebuildBound.Spec.Hierarchy

/-!
# The hierarchy model on a tiny instance (smoke test)

Evaluates `Spec/Model/Hierarchy.lean` on a two-level configuration (level one
with the selected direct geometries, a top of 32 homes) and a trace of two
eight-record units per level-one ordinal, and prints the families, the
tables' sizes and the potential jobs' results. A regression check that the
recursion evaluates and composes the four job models:

    lake env lean --run spec_tests/Hierarchy.lean
-/

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Spec

def tinyCfg : Config :=
  { fanouts := [2], carry1 := 16, topDigit := 1, load := 32, horizon := 2048, initialized := false }
def tinyTop : TopGeom :=
  { C := 64, k := 5, e := 0, rho := 0, I := 5, dfs := false, rPages := 1, bPages := 1,
    mergePages := 1, tierPages := 1 }
def tinyPrep : TPGeom :=
  { C := 64, k := 5, stashPages := 1, aTierPages := 1, drainPages := 1, rangeBits := 0, I := 5,
    dfs := false }
def tinySh : Shapes := ⟨selectedDirectGeometry, fun _ _ => selectedDirectSep 2, tinyTop, tinyPrep, tinyPrep⟩
def unit (i : Nat) : Bucket := (List.range 8).map fun j => some ⟨LogicalKey.ofNat (i * 100 + j), j, false⟩
def tinyTr : Trace := ⟨fun i => [unit i, unit (i + 1)], [], fun _ => false⟩
def wds : Words := fun ℓ v k => (LogicalKey.toNat k * 2654435761 + ℓ * 97 + v * 7919) % 2 ^ 40

def main : IO Unit := do
  IO.println s!"levels {tinyCfg.levels}, potential jobs {tinyCfg.potentialJobs.length}"
  IO.println s!"families {(familyOf tinyCfg 1 2, familyOf tinyCfg 1 3, familyOf tinyCfg 2 1)}"
  for v in [1, 2, 3, 4] do
    let t := table tinyCfg tinySh tinyTr wds 1 v
    IO.println s!"level one ordinal {v}: {t.main.length} buckets, {t.records.length} records"
  for v in [1, 2] do
    let t := table tinyCfg tinySh tinyTr wds 2 v
    IO.println s!"top ordinal {v}: {t.main.length} buckets, {t.records.length} records"
  let fails := tinyCfg.potentialJobs.map (jobFails tinyCfg tinySh tinyTr wds)
  IO.println s!"jobFails {fails}"
  if fails.any id then
    IO.println "FAIL: a potential job of the tiny instance fails"
    IO.Process.exit 1
  IO.println "OK"
