import RebuildBound.Spec.ConfigurationFamilyDirectNumerics
import RebuildBound.Proofs.ConfigurationFamilyDirectNumerics.Data
import RebuildBound.Proofs.NumericalPhi
import RebuildBound.Proofs.SelRest.Sound

namespace RebuildBound.ConfigurationFamilyDirectNumericsProof
open Model Spec Spec.ConfigurationFamily

set_option exponentiation.threshold 512
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Each exact Phi key is checked once, independently of its occurrences. -/
theorem producerCheck : ∀ n ∈ producerWidths,
    2 ^ 117 * NTop.phiNum (2 ^ 400) 100 32 256 n 64 64 32 1 ≤ 2 ^ 400 := by decide +kernel

theorem outputCheck : ∀ n ∈ outputWidths,
    2 ^ 112 * NTop.phiNum (2 ^ 400) 100 32 256 n 64 64 32 1 ≤ 2 ^ 400 := by decide +kernel

theorem densityCheck : ∀ x ∈ directShapes,
    1 ≤ x.2.r ∧ 32 * x.2.N < 2 ^ 64 ∧
    SelRest.dens 64 (x.2.r * ((2 ^ (64 - x.2.k) + x.2.r - 1) / x.2.r))
      (64 - x.2.k) (32 * x.2.N) ≤ 2 * 2 ^ 64 := by decide +kernel

theorem dimensions : ∀ x ∈ directShapes,
    x.1.U ∈ producerWidths ∧ x.1.outputHomes ∈ outputWidths ∧
    x.1.bCapacity = 64 ∧ x.1.outputCapacity = 64 := by decide +kernel

theorem coverage : ∀ m ∈ members,
    ∀ d ∈ List.range' 1 ((m.config true).fanout 1),
      (m.direct d, m.directSep d) ∈ directShapes := by decide +kernel

end RebuildBound.ConfigurationFamilyDirectNumericsProof
