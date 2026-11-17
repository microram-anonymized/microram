import RebuildBound.Spec.HierarchyGeometry

/-! Finite structural conditions for generic reference semantics. These are
arithmetic and actual-shape checks, independent of run, schedule, tape law,
numerical budgets and membership in a planner family. -/

namespace RebuildBound.Spec.HierarchyGeometry
open Model Model.Hierarchy

/-- A required separated row must exist and match its level and digit.
Positive carry-tier pages suffice for the structural induction. -/
def SeparatedRowCompatible (cfg : Config) (ℓ d : Nat) : Option SepGeom → Prop
  | some row => row.d = d ∧ row.U = cfg.carry ℓ ∧ row.Valid ∧
      row.C = 64 ∧ 0 < row.bTierPages ∧ val2 row.d = row.e
  | none => False

instance (cfg : Config) (ℓ d : Nat) (row : Option SepGeom) :
    Decidable (SeparatedRowCompatible cfg ℓ d row) := by
  cases row <;> unfold SeparatedRowCompatible <;> infer_instance

/-- Finite lower geometry checks; neither initialization mode nor horizon is
restricted. The algorithmic restrictions (load 32, lanes 64, power-of-two
fanouts in 2..8 and carry widths) remain explicit. -/
def LowerCompatible (g : HierarchyGeometry) : Prop :=
  (2 ≤ g.cfg.levels ∧ g.cfg.load = 32) ∧ DirectCompatible g.cfg g.direct ∧
  (∀ ℓ < g.cfg.levels, 1 ≤ ℓ →
    (2 ≤ g.cfg.fanout ℓ ∧ g.cfg.fanout ℓ ≤ 8 ∧
      2 ^ val2 (g.cfg.fanout ℓ) = g.cfg.fanout ℓ) ∧
    g.cfg.seed ℓ = g.cfg.fanout ℓ * g.cfg.seed (ℓ + 1) ∧
    g.cfg.carry (ℓ + 1) = g.cfg.fanout ℓ * g.cfg.carry ℓ) ∧
  (∀ ℓ < g.cfg.levels + 1, 1 ≤ ℓ → 2 ^ val2 (g.cfg.carry ℓ) = g.cfg.carry ℓ) ∧
  (∀ ℓ < g.cfg.levels, ∀ d < g.cfg.fanout ℓ + 1, 2 ≤ ℓ → 2 ≤ d →
    SeparatedRowCompatible g.cfg ℓ d (g.cfg.sepRow g.rows ℓ d))

instance (g : HierarchyGeometry) : Decidable g.LowerCompatible := by
  unfold LowerCompatible
  infer_instance

/-- The public structural contract combines lower checks with top dimensions,
initialization/preparation drains and the incoming tier link. It assumes no
correctness, transcript-law or capacity-failure conclusion. -/
def Structural (g : HierarchyGeometry) : Prop := g.LowerCompatible ∧ g.TopCompatible

instance (g : HierarchyGeometry) : Decidable g.Structural := by
  unfold Structural
  infer_instance

end RebuildBound.Spec.HierarchyGeometry
