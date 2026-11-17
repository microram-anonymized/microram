import RebuildBound.Spec.HierarchyBase

/-!
# Geometry for hierarchy instances

Data only: numerical budgets belong to composition. Direct level-one shapes
are explicit, alongside the separated and top shapes.
-/

namespace RebuildBound.Spec
open Model Model.Hierarchy

/-- A hierarchy instance's geometry and key-universe capacity. -/
structure HierarchyGeometry where
  cfg : Config
  rows : List (SepGeom × Nat)
  top : TopGeom
  prep : TPGeom
  init : TPGeom
  keyCapacity : Nat
  direct : Nat → DirectJob.Geometry

namespace HierarchyGeometry

/-- Selected-configuration geometry used by shared proof helpers and numerical
certificates.
Public certification uses `geometry31` and the standard configuration family. -/
def selected (cfg : Config) (rows : List (SepGeom × Nat)) : HierarchyGeometry :=
  ⟨cfg, rows, selectedTop, selectedTP, selectedTP, 2 ^ 27, selectedDirectGeometry⟩

def shapes (g : HierarchyGeometry) : Shapes :=
  hierarchyShapesWith g.cfg g.rows g.top g.prep g.init g.direct

/-- Finite agreement of the actual first-level jobs with the configuration.
Validity includes output capacities and direct/DFS routing constraints. -/
def DirectCompatible (cfg : Config) (direct : Nat → DirectJob.Geometry) : Prop :=
  ∀ d < cfg.fanout 1 + 1, 1 ≤ d →
    (direct d).Valid ∧ (direct d).U = cfg.carry 1 ∧ (direct d).digit = d

instance (cfg : Config) (direct : Nat → DirectJob.Geometry) :
    Decidable (DirectCompatible cfg direct) := by
  unfold DirectCompatible
  infer_instance

/-- Capacity of the tier published into the top. Two-level hierarchies use
level one's direct publication; deeper hierarchies require an actual separated
row. A missing row never acquires a capacity from the execution placeholder. -/
def incomingTopCapacity (g : HierarchyGeometry) : Option Nat :=
  if g.cfg.levels = 2 then some (g.direct (g.cfg.fanout 1)).outputCapacity
  else (g.cfg.sepRow g.rows (g.cfg.levels - 1)
    (g.cfg.fanout (g.cfg.levels - 1))).map fun row => row.tierPages * row.C

/-- Shared top dimensions and tier links. Equal table sizes also give the
same word-home interpretation (`word key % T`); the drains may differ.
This does not assert the hierarchy invariant or any probability bound. -/
def TopCompatible (g : HierarchyGeometry) : Prop :=
  g.top.Valid ∧ g.prep.Valid ∧ g.init.Valid ∧
  g.top.C = 64 ∧ g.prep.C = g.top.C ∧ g.init.C = g.top.C ∧
  g.prep.T = g.top.T ∧ g.init.T = g.top.T ∧
  g.cfg.load = 32 ∧ g.cfg.carry g.cfg.levels = g.top.U ∧
  g.cfg.topDigit = g.top.D ∧ g.keyCapacity ≤ g.cfg.load * g.top.T ∧
  g.init.drainPages ≤ g.prep.aTierPages ∧
  g.top.tierPages ≤ g.prep.aTierPages ∧
  g.prep.drainPages ≤ g.top.rPages ∧
  (g.incomingTopCapacity.any fun capacity => decide (capacity ≤ g.top.SB)) = true

instance (g : HierarchyGeometry) : Decidable g.TopCompatible := by
  unfold TopCompatible
  infer_instance

end HierarchyGeometry
end RebuildBound.Spec
