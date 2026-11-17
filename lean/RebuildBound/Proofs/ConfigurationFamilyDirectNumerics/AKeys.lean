import RebuildBound.Spec.ConfigurationFamilyDirectNumerics
import RebuildBound.Proofs.ConfigurationFamilyDirectNumerics.Data
import RebuildBound.Spec.ConfigurationFamilyRest
import RebuildBound.Spec.ConfigurationFamilyRange
import RebuildBound.Spec.ConfigurationFamilyDirectRange

/-! Full-shape coverage is checked independently of the arithmetic matrices. -/
namespace RebuildBound.ConfigurationFamilyDirectNumericsProof
open Model Spec Spec.ConfigurationFamily

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem aCoverage : ∀ x ∈ directShapes, 2 ≤ x.1.digit →
    restBudgets.any (fun y => decide (y.1 = x.2 ∧ 100 ≤ y.2)) = true ∧
    (x.1.ranges ≠ .direct →
      (rangeBudgets ++ directRangeBudgets).any
        (fun y => decide (y.1 = x.2 ∧ 100 ≤ y.2)) = true) := by
  decide +kernel

end RebuildBound.ConfigurationFamilyDirectNumericsProof
