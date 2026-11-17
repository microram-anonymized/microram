import RebuildBound.Proofs.Geometry31
import RebuildBound.Proofs.HierarchyHorizonFree
import RebuildBound.Proofs.HierarchyTopLaw.Init

/-! Separate initialization drains affect bounded failure, and the selected
instances retain their original initialization and reference execution. -/

namespace HierarchyInitializationTest
open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Spec

example (cfg : Config) (rows : List (SepGeom × Nat)) :
    hierarchyShapes cfg rows =
      ⟨selectedDirectGeometry, fun ℓ d => (cfg.sepRow rows ℓ d).getD (selectedDirectSep 2),
        selectedTop, selectedTP, selectedTP⟩ := rfl

example (cfg : Config) (rows : List (SepGeom × Nat)) (tr : Trace) (words : Words) :
    initOutput cfg (hierarchyShapes cfg rows) tr words =
      (tpReference engineRule selectedTP (fun _ => false)
        (jobWord cfg words cfg.levels (cfg.seed cfg.levels))
        ⟨initMain selectedTP tr.init, []⟩).output := rfl

example (cfg : Config) (rows : List (SepGeom × Nat)) (tr : Trace) (words : Words) :
    initResult cfg (hierarchyShapes cfg rows) tr words =
      initJob engineRule selectedTP (jobWord cfg words cfg.levels (cfg.seed cfg.levels))
        tr.init := rfl

-- The selected execution and failure event agree with using prep for initialization.
example (cfg : Config) (rows : List (SepGeom × Nat)) (tr : Trace) (words : Words) :
    let sh := hierarchyShapes cfg rows
    (table cfg sh tr words = table cfg {sh with init := sh.prep} tr words) ∧
    (Fails cfg sh tr words ↔ Fails cfg {sh with init := sh.prep} tr words) :=
  ⟨rfl, Iff.rfl⟩

def cfg : Config := ⟨[2], 1, 1, 1, 0, true⟩
def prep : TPGeom := ⟨2, 3, 4, 2, 2, 0, 3, false⟩
def initial : TPGeom := { prep with drainPages := 1 }
def sh : Shapes :=
  hierarchyShapesWith cfg [] selectedTop prep initial

def tr : Trace := ⟨fun _ => [], (List.range 5).map fun k => ⟨LogicalKey.ofNat (k), k, false⟩, fun _ => false⟩
def words : Words := fun _ _ _ => 0

example : prep.Valid ∧ initial.Valid := by decide +kernel

-- Three residual records fit prep's four slots but overflow init's two.
example : initResult cfg sh tr words = .error .drain := by decide +kernel
example : (initResult cfg {sh with init := prep} tr words).toBool = true := by decide +kernel
example : (initOutput cfg sh tr words).records.length = 5 := by decide +kernel

-- The real geometry is linked symbolically; never evaluate its full table.
example : geometry31.shapes.init = init31 ∧ geometry31.shapes.prep = prep31 := ⟨rfl, rfl⟩
example : geometry31.TopCompatible := RebuildBound.Geometry31.1
example (tr : Trace) (words : Words) :
    initResult config31 geometry31.shapes tr words =
      initJob engineRule init31
        (jobWord config31 words config31.levels (config31.seed config31.levels)) tr.init := rfl

-- Word locality / event containment of initialization needs no selected shape.
example (N : Nat) (tr : Trace) (hT : TracePremises config31 N tr)
    (hcount : tr.init.length ≤ init31.C / 2 * init31.T) (pc : Coord config31) :
    InitLaw (RebuildBound.HierarchyTopLawProof.initLawFor config31 tr N init31 pc) tr.init :=
  RebuildBound.HierarchyTopLawProof.initLawFor_initLaw hT hcount (by decide +kernel) pc

end HierarchyInitializationTest
