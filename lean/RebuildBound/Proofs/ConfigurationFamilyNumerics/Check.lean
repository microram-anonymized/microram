import RebuildBound.Proofs.ConfigurationFamilyNumerics.Budget

/-! Kernel evaluation checks coverage of complete shapes and the exact rational
sum, independently of the analytic local bounds. -/
namespace RebuildBound.ConfigurationFamilyNumericsProof
open Model Spec Spec.ConfigurationFamily

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem covered : ∀ m ∈ members, ∀ p ∈ (m.config true).exposures,
    classCovered m p.1 := by decide +kernel

theorem checked : ∀ m ∈ members, exposureBudget m ≤ dyadic 64 := by decide +kernel

end RebuildBound.ConfigurationFamilyNumericsProof
