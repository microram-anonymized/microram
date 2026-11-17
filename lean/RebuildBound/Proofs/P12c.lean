import RebuildBound.Proofs.ShadowNet.Class
import RebuildBound.Spec.P12

/-!
# P12c: class membership of the radix first-arrival test

No obstacle. `radixTermTest` is `thinAll ∘ (termTest ∘ capAll ∘ sumAlong)`, in `𝒯(⊤)` by P6/X1
with the P11c terminal lemma; each `rBackStage` is `thinAll ∘ capAll ∘ sumAlong`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.P12cProof

open RebuildBound.Spec RebuildBound.X1Proof RebuildBound.P6Proof RebuildBound.P11cProof

section Gen

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma capAll_bound' (K : ℝ≥0∞) (C : ℕ) (l : List ι) :
    ∀ ψ : States ι → ℝ≥0∞, CountBounded K ψ → CountBounded K (ψ ∘ capAll l C) := by
  induction l with
  | nil => exact fun ψ h => h
  | cons a l ih =>
    intro ψ h
    exact ih (ψ ∘ capAt a C) (RebuildBound.P6_bound.1 K ψ a C h)

lemma thinAll_bound' (K : ℝ≥0∞) (l : List ι) (p : ι → I) :
    ∀ ψ : States ι → ℝ≥0∞, CountBounded K ψ → CountBounded K (thinAll l p ψ) := by
  induction l with
  | nil => exact fun ψ h => h
  | cons a l ih =>
    intro ψ h
    exact RebuildBound.P6_bound.2.1 K _ a (p a) (ih ψ h)

end Gen

variable {r b : ℕ}

lemma radixTerm_class (C P L lo : ℕ) (pe q : I) (R : Bits b) :
    ClassT (fun _ : RNode r b => (⊤ : ℕ∞)) (radixTermTest (r := r) C P pe q L lo R) ∧
      CountBounded (P : ℝ≥0∞) (radixTermTest (r := r) C P pe q L lo R) := by
  obtain ⟨h0, k0⟩ := termTest_class P pe L lo R
  have h1 := RebuildBound.P6_capAll _ (allNodes b) C h0
  have h2 := RebuildBound.X1_add (fun V : RNode r b => V.2) _ h1
  have k1 := capAll_bound' _ C (allNodes b) _ k0
  have k2 := RebuildBound.P6_bound.2.2.1 (P : ℝ≥0∞) (fun V : RNode r b => V.2) _ k1
  exact ⟨RebuildBound.P6_thinAll _ _ (allRNodes r b) _ h2, thinAll_bound' _ _ _ _ k2⟩

lemma rBackStage_class (C : ℕ) (R : Bits b) (j : ℕ) (K : ℝ≥0∞) (ψ : States (RNode r b) → ℝ≥0∞)
    (h : ClassT (fun _ : RNode r b => (⊤ : ℕ∞)) ψ) (hK : CountBounded K ψ) :
    ClassT (fun _ : RNode r b => (⊤ : ℕ∞)) (rBackStage C R j ψ) ∧
      CountBounded K (rBackStage C R j ψ) := by
  unfold rBackStage
  split_ifs with hj
  · have h1 := RebuildBound.P6_capAll ψ (allRNodes r b) C h
    have h2 := RebuildBound.X1_add
      (fun V : RNode r b => (V.1, Function.update V.2 ⟨j, hj⟩ (R ⟨j, hj⟩))) _ h1
    have k1 := capAll_bound' K C (allRNodes r b) ψ hK
    have k2 := RebuildBound.P6_bound.2.2.1 K
      (fun V : RNode r b => (V.1, Function.update V.2 ⟨j, hj⟩ (R ⟨j, hj⟩))) _ k1
    exact ⟨RebuildBound.P6_thinAll _ _ (allRNodes r b) _ h2, thinAll_bound' K _ _ _ k2⟩
  · exact ⟨h, hK⟩

lemma rForest_class (C : ℕ) (R : Bits b) (K : ℝ≥0∞) (φ : States (RNode r b) → ℝ≥0∞)
    (h : ClassT (fun _ : RNode r b => (⊤ : ℕ∞)) φ) (hK : CountBounded K φ) (j : ℕ) :
    ClassT (fun _ : RNode r b => (⊤ : ℕ∞)) (rForestTest C R φ j) ∧
      CountBounded K (rForestTest C R φ j) := by
  unfold rForestTest
  generalize List.range (b - j) = l
  induction l with
  | nil => exact ⟨h, hK⟩
  | cons i l ih => exact rBackStage_class C R (j + i) K _ ih.1 ih.2

end RebuildBound.P12cProof

open RebuildBound.Spec RebuildBound.P12cProof in
theorem RebuildBound.P12c : RebuildBound.Spec.P12c_statement := by
  intro r b C P L lo R q
  obtain ⟨h0, k0⟩ := radixTerm_class (r := r) C P L lo (q * halfPow (b - lo)) q R
  obtain ⟨h1, k1⟩ := rForest_class C R P _ h0 k0 (lo + 1)
  have h2 := RebuildBound.P6_capAll _ (allRNodes r b) C h1
  have k2 := capAll_bound' P C (allRNodes r b) _ k1
  exact RebuildBound.P6_embed _ P h2 k2
