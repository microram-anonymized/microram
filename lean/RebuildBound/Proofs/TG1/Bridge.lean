import RebuildBound.Proofs.TG1.Init1
import RebuildBound.Proofs.P8c
import RebuildBound.Proofs.P7fin

/-!
# IG1: the bridge for independent, non-identical uniform destinations

`bridgeV`: the average over `Fin n → A` of a function of `Σ_i e_{d_i (g i)}` is the integral
against the convolution of the `n` laws of `d_i a` for a uniform `a`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.TG1Proof

open RebuildBound.Model RebuildBound.Spec RebuildBound.P11dProof

variable {κ : Type} [Fintype κ] [DecidableEq κ] {A : Type} [Fintype A] [Nonempty A]

lemma conv_ofFn_prob (n : ℕ) (d : Fin n → A → κ) :
    IsProbabilityMeasure (convList (List.ofFn fun i => unitLaw (law (d i)))) := by
  induction n with
  | zero => simp only [List.ofFn_zero, convList]; infer_instance
  | succ n ih =>
    have hU := unitLaw_prob (law (d 0)) (sum_law (d 0))
    have hT := ih (fun i => d i.succ)
    rw [List.ofFn_succ, convList]
    infer_instance

lemma bridgeV (n : ℕ) : ∀ (d : Fin n → A → κ) (F : (κ → ℕ) → ℝ≥0∞),
    ∫⁻ v, F v ∂(convList (List.ofFn fun i => unitLaw (law (d i)))) =
      ((Fintype.card A : ℝ≥0∞) ^ n)⁻¹ * ∑ g : Fin n → A, F (∑ i, unitVec (d i (g i))) := by
  induction n with
  | zero => intro d F; simp [convList, lintegral_dirac]
  | succ n ih =>
    intro d F
    have hU := unitLaw_prob (law (d 0)) (sum_law (d 0))
    have hT := conv_ofFn_prob n (fun i => d i.succ)
    rw [List.ofFn_succ, convList, Measure.lintegral_conv Measurable.of_discrete,
      lintegral_unitLaw_law]
    simp_rw [ih (fun i => d i.succ)]
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => A)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [pow_succ', ENNReal.mul_inv (by simp) (by simp), mul_assoc]
    simp only [Finset.mul_sum]

end RebuildBound.TG1Proof
