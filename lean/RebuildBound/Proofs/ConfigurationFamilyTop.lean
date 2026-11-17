import RebuildBound.Spec.ConfigurationFamilyTop
import RebuildBound.Proofs.ConfigurationFamilyTop.C0
import RebuildBound.Proofs.ConfigurationFamilyTop.C1
import RebuildBound.Proofs.ConfigurationFamilyTop.C2
import RebuildBound.Proofs.ConfigurationFamilyTop.C3
import RebuildBound.Proofs.ConfigurationFamilyTop.C4
import RebuildBound.Proofs.ConfigurationFamilyTop.C5
import RebuildBound.Proofs.ConfigurationFamilyTop.C6

/-! Complete top-finish certificates for the family, sharing one checker
soundness proof and certifying each distinct shape exactly once. -/

namespace RebuildBound.ConfigurationFamilyTopProof
open Spec Model Spec.ConfigurationFamily

theorem checked : topBudgets.all check = true := by
  have h : topBudgets = chunk 0 ++ chunk 1 ++ chunk 2 ++ chunk 3 ++ chunk 4 ++ chunk 5 ++ chunk 6 := by
    decide +kernel
  rw [h]
  simp only [List.all_append, checked0, checked1, checked2, checked3, checked4, checked5,
    checked6, Bool.and_self]

end RebuildBound.ConfigurationFamilyTopProof

namespace RebuildBound
open Spec Model Spec.ConfigurationFamily

theorem ConfigurationFamilyTopNumerics : ConfigurationFamilyTopNumerics_statement := by
  intro x hx
  have hc := List.all_eq_true.mp ConfigurationFamilyTopProof.checked x hx
  simp only [ConfigurationFamilyTopProof.check, decide_eq_true_eq] at hc
  simpa only [Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] using
    NumericalPhi.top_le x.1 576 576 1 (2 ^ x.2) (by positivity)
    (by simpa only [one_mul] using hc)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ConfigurationFamilyTopCoverage : ConfigurationFamilyTopCoverage_statement := by
  intro m hm initialized
  have h : ∀ m ∈ members, ∀ initialized ∈ [false, true],
      ∃ x ∈ topBudgets, (m.geometry initialized).top = x.1 ∧
        ((m.config initialized).ordinals (m.config initialized).levels : ℚ) /
          2 ^ x.2 ≤ 1 / 2 ^ 65 := by decide +kernel
  exact h m hm initialized (by cases initialized <;> simp)

end RebuildBound
