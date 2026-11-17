import RebuildBound.Spec.ConfigurationFamilyData
import RebuildBound.Spec.TopBound

/-! Shared top-finish budgets for all family geometries. Each row retains the
whole semantic shape; membership is checked by equality, independently of any
Python job-key hash. The cutoff is 576 and the load is 32. -/

namespace RebuildBound.Spec.ConfigurationFamily
open Model

def topBudgets : List (TopGeom × Nat) := [
  (⟨64, 3, 3, 3, 3, true, 1, 1, 1, 1⟩, 114),
  (⟨64, 4, 3, 3, 4, true, 1, 1, 1, 1⟩, 112),
  (⟨64, 5, 3, 3, 5, true, 1, 1, 1, 1⟩, 110),
  (⟨64, 6, 3, 3, 6, true, 1, 1, 1, 1⟩, 108),
  (⟨64, 7, 3, 3, 7, true, 1, 1, 1, 1⟩, 106),
  (⟨64, 8, 3, 3, 8, true, 1, 1, 1, 1⟩, 103),
  (⟨64, 9, 3, 3, 9, true, 1, 1, 1, 1⟩, 101),
  (⟨64, 10, 3, 3, 10, true, 1, 1, 1, 1⟩, 99),
  (⟨64, 11, 3, 3, 11, true, 1, 1, 1, 1⟩, 96),
  (⟨64, 12, 3, 3, 12, true, 1, 1, 1, 1⟩, 93),
  (⟨64, 13, 3, 4, 12, true, 2, 1, 2, 1⟩, 90),
  (⟨64, 14, 3, 4, 13, true, 2, 1, 2, 2⟩, 95),
  (⟨64, 15, 3, 4, 14, true, 2, 1, 2, 2⟩, 92),
  (⟨64, 16, 3, 4, 15, true, 2, 1, 2, 2⟩, 89),
  (⟨64, 17, 3, 4, 16, true, 2, 2, 2, 2⟩, 86),
  (⟨64, 18, 3, 4, 17, true, 2, 2, 2, 2⟩, 82),
  (⟨64, 19, 3, 4, 18, true, 2, 2, 2, 2⟩, 78),
  (⟨64, 20, 3, 5, 18, true, 2, 2, 2, 2⟩, 77),
  (⟨64, 21, 3, 6, 18, true, 2, 2, 2, 2⟩, 76),
  (⟨64, 22, 3, 7, 18, true, 3, 2, 3, 3⟩, 75),
  (⟨64, 23, 3, 8, 18, true, 4, 2, 4, 3⟩, 70)]

end RebuildBound.Spec.ConfigurationFamily

namespace RebuildBound.Spec
open Model ConfigurationFamily

/-- One certificate per unique complete top shape. -/
def ConfigurationFamilyTopNumerics_statement : Prop :=
  ∀ x ∈ topBudgets,
    topFinishBound x.1.C x.1.SR x.1.rho x.1.I x.1.T
      (min x.1.SMerge x.1.STier) 576 576 32 ≤ 1 / (2 : ℝ) ^ x.2

/-- The exact shape is covered from either start, with a checked exposure
budget. This certifies the top contribution only. -/
def ConfigurationFamilyTopCoverage_statement : Prop :=
  ∀ (m : Member), m ∈ members → ∀ initialized : Bool,
    ∃ x ∈ topBudgets,
      (m.geometry initialized).top = x.1 ∧
      ((m.config initialized).ordinals (m.config initialized).levels : ℚ) /
        2 ^ x.2 ≤ 1 / 2 ^ 65

end RebuildBound.Spec
