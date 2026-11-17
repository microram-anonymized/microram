import RebuildBound.Spec.DirectJobSelected

open scoped ENNReal NNReal

namespace RebuildBound.Spec

/-- Selected B and union excess budgets, with the completed-A budget explicit.
The union budget allows a density factor of two over the checked Phi bound.
No native source/history law is asserted by choosing these numbers. -/
noncomputable def selectedDirectBound (aBudget : Nat → ℝ≥0∞) (d : Nat) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (2 : ℝ) ^ 117) + aBudget d +
    ENNReal.ofReal (1 / (2 : ℝ) ^ 111)

end RebuildBound.Spec
