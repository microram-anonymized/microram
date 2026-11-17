import RebuildBound.Proofs.NetworkAverage
import RebuildBound.Proofs.P5a
import RebuildBound.Proofs.P5b
import RebuildBound.Proofs.ShadowNet.Class
import RebuildBound.Spec.P11de

/-!
# ShadowLaw: unit laws and the Poisson bridge (from P11d)

Moved from the d = 2 chain (`P11d`); namespace `RebuildBound.P11dProof` kept.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace RebuildBound.P11dProof
open RebuildBound.Spec
section Bridge
variable {κ : Type} [Fintype κ] [DecidableEq κ]
lemma lintegral_unitLaw (p : κ → ℝ≥0) (G : (κ → ℕ) → ℝ≥0∞) :
    ∫⁻ v, G v ∂(unitLaw p) = ∑ k, (p k : ℝ≥0∞) * G (unitVec k) := by
  unfold unitLaw
  rw [lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

lemma unitLaw_prob (p : κ → ℝ≥0) (hp : ∑ k, p k = 1) : IsProbabilityMeasure (unitLaw p) := by
  refine ⟨?_⟩
  have := lintegral_unitLaw p (fun _ => 1)
  simp only [lintegral_const, mul_one, one_mul] at this
  rw [this]
  exact_mod_cast hp

omit [DecidableEq κ] in
lemma convList_replicate_prob (μ : Measure (κ → ℕ)) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (convList (List.replicate n μ)) := by
  induction n with
  | zero => simp only [List.replicate, convList]; infer_instance
  | succ n ih => simp only [List.replicate, convList]; infer_instance

variable {A : Type} [Fintype A]
/-- The law of `d a` for a uniform `a : A`. -/
noncomputable def law (d : A → κ) : κ → ℝ≥0 :=
  fun v => ((Finset.univ.filter (fun a => d a = v)).card : ℝ≥0) / (Fintype.card A : ℝ≥0)

lemma sum_law [Nonempty A] (d : A → κ) : ∑ v, law d v = 1 := by
  unfold law
  rw [← Finset.sum_div, ← Nat.cast_sum,
    ← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _), Finset.card_univ]
  exact div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

lemma lintegral_unitLaw_law [Nonempty A] (d : A → κ) (G : (κ → ℕ) → ℝ≥0∞) :
    ∫⁻ v, G v ∂(unitLaw (law d)) = (Fintype.card A : ℝ≥0∞)⁻¹ * ∑ a, G (unitVec (d a)) := by
  have hfib := Finset.sum_fiberwise' Finset.univ d (fun v => G (unitVec v))
  rw [lintegral_unitLaw, ← hfib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul, law,
    ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), ENNReal.coe_natCast,
    ENNReal.coe_natCast, div_eq_mul_inv]
  ring

/-- **Bridge.** The uniform average over `Fin n → A` of `F (Σ_i e_{d (g i)})` is the
integral of `F` against the `n`-fold convolution of `unitLaw (law d)`. -/
lemma bridge [Nonempty A] (d : A → κ) (n : ℕ) (F : (κ → ℕ) → ℝ≥0∞) :
    ∫⁻ v, F v ∂(convList (List.replicate n (unitLaw (law d)))) =
      ((Fintype.card A : ℝ≥0∞) ^ n)⁻¹ * ∑ g : Fin n → A, F (∑ i, unitVec (d (g i))) := by
  have hU := unitLaw_prob (law d) (sum_law d)
  induction n generalizing F with
  | zero => simp [convList, lintegral_dirac]
  | succ n ih =>
    have hT := convList_replicate_prob (unitLaw (law d)) n
    rw [List.replicate_succ, convList, Measure.lintegral_conv Measurable.of_discrete,
      lintegral_unitLaw_law]
    simp_rw [ih]
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => A)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [pow_succ', ENNReal.mul_inv (by simp) (by simp), mul_assoc]
    simp only [Finset.mul_sum]

end Bridge
section Poisson
variable {κ : Type} [Fintype κ]
lemma convList_replicate_poissonVec (ν : κ → ℝ≥0) (n : ℕ) :
    convList (List.replicate (n + 1) (poissonVec ν)) = poissonVec ((n + 1) • ν) := by
  induction n with
  | zero =>
    simp only [List.replicate, convList, zero_add, one_smul]
    exact Measure.conv_dirac_zero _
  | succ n ih =>
    rw [List.replicate_succ, convList, ih, RebuildBound.P5b_conv, ← succ_nsmul']

lemma poisson_chain (f : (κ → ℕ) → ℝ≥0∞) (hf : Monotone f) (ν : κ → ℝ≥0) (n : ℕ)
    (lam : ℝ≥0) (h : n • ν ≤ fun _ => lam) :
    ∫⁻ v, f v ∂(convList (List.replicate n (poissonVec ν))) ≤
      ∫⁻ v, f v ∂(poissonVec (fun _ => lam)) := by
  cases n with
  | zero =>
    simp only [List.replicate, convList]
    rw [lintegral_dirac]
    calc f 0 = ∫⁻ _, f 0 ∂(poissonVec (fun _ => lam)) := by simp
      _ ≤ ∫⁻ v, f v ∂(poissonVec (fun _ => lam)) :=
          lintegral_mono fun y => hf fun i => Nat.zero_le (y i)
  | succ n =>
    rw [convList_replicate_poissonVec]
    exact RebuildBound.P5b_pad f hf _ _ h

end Poisson
end RebuildBound.P11dProof
