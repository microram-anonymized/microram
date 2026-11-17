import RebuildBound.Spec.ConfigurationFamilyDirect

/-! Shared direct B, union and A bounds for every family member. The finite
shape registry and numerical width checks belong to the proof modules. -/
open scoped ENNReal
namespace RebuildBound.Spec
open ConfigurationFamily

def ConfigurationFamilyDirectBUNumerics_statement : Prop :=
  ∀ m ∈ members, ∀ d, 1 ≤ d → d ≤ (m.config true).fanout 1 →
    directBBound m d ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 117) ∧
    directUBound m d ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 111)

/-- A-history bounds reuse the complete-shape separated arithmetic registry. -/
def ConfigurationFamilyDirectANumerics_statement : Prop :=
  ∀ m ∈ members, ∀ d, 2 ≤ d → d ≤ (m.config true).fanout 1 →
    directABound m d ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 99)

/-- One conservatively rounded direct-job budget serves the whole family. -/
def ConfigurationFamilyDirectNumerics_statement : Prop :=
  ∀ m ∈ members, ∀ d, 1 ≤ d → d ≤ (m.config true).fanout 1 →
    directBound m d ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 98)

end RebuildBound.Spec
