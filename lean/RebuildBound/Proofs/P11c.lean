import RebuildBound.Proofs.X1
import RebuildBound.Proofs.P6
import RebuildBound.Spec.P11
import RebuildBound.Proofs.ShadowNet.Class

/-!
# P11c: class membership of the first-arrival test

No obstacle. The terminal test is a binomial mixture (`P6_mix`) of convex nondecreasing
functions of a partial shadow sum; the backward stages are thinAll ∘ capAll ∘ sumAlong.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.P11cProof

open RebuildBound.Spec RebuildBound.X1Proof RebuildBound.P6Proof

variable {b : ℕ}

lemma capAll_bound (K : ℝ≥0∞) (C : ℕ) (l : List (Bits b)) :
    ∀ ψ : States (Bits b) → ℝ≥0∞, CountBounded K ψ → CountBounded K (ψ ∘ capAll l C) := by
  induction l with
  | nil => exact fun ψ h => h
  | cons a l ih =>
    intro ψ h
    exact ih (ψ ∘ capAt a C) (RebuildBound.P6_bound.1 K ψ a C h)

lemma thinAll_bound (K : ℝ≥0∞) (l : List (Bits b)) (p : Bits b → I) :
    ∀ ψ : States (Bits b) → ℝ≥0∞, CountBounded K ψ → CountBounded K (thinAll l p ψ) := by
  induction l with
  | nil => exact fun ψ h => h
  | cons a l ih =>
    intro ψ h
    exact RebuildBound.P6_bound.2.1 K _ a (p a) (ih ψ h)

lemma backStage_class (C : ℕ) (R : Bits b) (j : ℕ) (K : ℝ≥0∞) (ψ : States (Bits b) → ℝ≥0∞)
    (h : ClassT (fun _ : Bits b => (⊤ : ℕ∞)) ψ) (hK : CountBounded K ψ) :
    ClassT (fun _ : Bits b => (⊤ : ℕ∞)) (backStage C R j ψ) ∧ CountBounded K (backStage C R j ψ) := by
  unfold backStage
  split_ifs with hj
  · have h1 := RebuildBound.P6_capAll ψ (allNodes b) C h
    have h2 := RebuildBound.X1_add (fun V : Bits b => Function.update V ⟨j, hj⟩ (R ⟨j, hj⟩))
      _ h1
    have k1 := capAll_bound K C (allNodes b) ψ hK
    have k2 := RebuildBound.P6_bound.2.2.1 K (fun V : Bits b => Function.update V ⟨j, hj⟩ (R ⟨j, hj⟩))
      _ k1
    exact ⟨RebuildBound.P6_thinAll _ _ (allNodes b) _ h2, thinAll_bound K _ _ _ k2⟩
  · exact ⟨h, hK⟩

lemma forest_class (C : ℕ) (R : Bits b) (K : ℝ≥0∞) (φ : States (Bits b) → ℝ≥0∞)
    (h : ClassT (fun _ : Bits b => (⊤ : ℕ∞)) φ) (hK : CountBounded K φ) (j : ℕ) :
    ClassT (fun _ : Bits b => (⊤ : ℕ∞)) (forestTest C R φ j) ∧ CountBounded K (forestTest C R φ j) := by
  unfold forestTest
  generalize List.range (b - j) = l
  induction l with
  | nil => exact ⟨h, hK⟩
  | cons i l ih => exact backStage_class C R (j + i) K _ ih.1 ih.2

end RebuildBound.P11cProof

open RebuildBound.Spec RebuildBound.P11cProof in
theorem RebuildBound.P11c_class : RebuildBound.Spec.P11c_class_statement := by
  intro b C P L lo R
  obtain ⟨h0, k0⟩ := termTest_class P (halfPow (b - lo)) L lo R
  obtain ⟨h1, k1⟩ := forest_class C R P _ h0 k0 (lo + 1)
  have h2 := RebuildBound.P6_capAll _ (allNodes b) C h1
  have k2 := capAll_bound P C (allNodes b) _ k1
  exact RebuildBound.P6_embed _ P h2 k2
