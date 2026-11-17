import RebuildBound.Proofs.P10
import RebuildBound.Spec.P10r

/-!
# P10r: sums of thinned trees and their truncation

* `truncPairConvPow_eq`: restricting every partial sum to `lowTotal H` is restricting
  the final sum, since partial sums are coordinatewise at most the final sum.
* `pairConvPow_map_tot`, `natConvPow_poisson`, `radix_tot`: the total of the radix
  node's sum is `Po(r λ_t q)`, with `λ_t = λ` for `t ≥ 1` and `λ_0 = 0`.
* `truncTree_high`, `bind_thinPair_high`: a truncated tree, thinned or not, puts no
  mass above `H`.
* `one_le_pow_add`: Bernoulli's inequality `1 ≤ a^n + n b` from `1 ≤ a + b`, `a ≤ 1`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.P10rProof

open RebuildBound.Spec RebuildBound.P10Proof RebuildBound.P11eProof RebuildBound.X1Proof

/-! ### Sums of independent node states -/

instance isFinite_pairConvPow (μ : Measure (ℕ × ℕ)) [IsFiniteMeasure μ] :
    ∀ n, IsFiniteMeasure (pairConvPow μ n)
  | 0 => by rw [pairConvPow]; infer_instance
  | n + 1 => by
    have := isFinite_pairConvPow μ n
    rw [pairConvPow]
    infer_instance

lemma isProb_pairConvPow (μ : Measure (ℕ × ℕ)) [IsProbabilityMeasure μ] :
    ∀ n, IsProbabilityMeasure (pairConvPow μ n)
  | 0 => by rw [pairConvPow]; infer_instance
  | n + 1 => by
    have := isProb_pairConvPow μ n
    rw [pairConvPow]
    infer_instance

lemma pairConvPow_mono {μ ν : Measure (ℕ × ℕ)} [IsFiniteMeasure ν] (h : μ ≤ ν) :
    ∀ n, pairConvPow μ n ≤ pairConvPow ν n
  | 0 => le_rfl
  | n + 1 => by
    rw [pairConvPow, pairConvPow]
    exact conv_mono' (pairConvPow_mono h n) h

lemma pairConvPow_univ (μ : Measure (ℕ × ℕ)) [IsFiniteMeasure μ] :
    ∀ n, pairConvPow μ n Set.univ = μ Set.univ ^ n
  | 0 => by simp [pairConvPow]
  | n + 1 => by rw [pairConvPow, conv_univ, pairConvPow_univ μ n, pow_succ]

lemma mem_lowTotal_of_add {x y : ℕ × ℕ} {H : ℕ} (h : x + y ∈ lowTotal H) : x ∈ lowTotal H := by
  simp only [lowTotal, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add] at h ⊢
  omega

lemma zero_mem_lowTotal (H : ℕ) : ((0, 0) : ℕ × ℕ) ∈ lowTotal H := by
  simp [lowTotal]

/-- Mass of a sum that is already above `H` stays above `H`. -/
lemma restrict_conv_restrict (H : ℕ) (ν μ : Measure (ℕ × ℕ)) [IsFiniteMeasure ν]
    [IsFiniteMeasure μ] :
    (ν.restrict (lowTotal H) ∗ μ).restrict (lowTotal H) = (ν ∗ μ).restrict (lowTotal H) := by
  have hA : MeasurableSet (lowTotal H) := MeasurableSet.of_discrete
  conv_rhs => rw [← Measure.restrict_add_restrict_compl (μ := ν) hA]
  rw [Measure.add_conv, Measure.restrict_add]
  suffices h : (ν.restrict (lowTotal H)ᶜ ∗ μ).restrict (lowTotal H) = 0 by rw [h, add_zero]
  rw [Measure.restrict_eq_zero, Measure.conv, Measure.map_apply Measurable.of_discrete hA]
  refine measure_mono_null (t := lowTotal H ×ˢ Set.univ) ?_ ?_
  · intro p hp
    exact ⟨mem_lowTotal_of_add hp, Set.mem_univ _⟩
  · rw [Measure.prod_prod, Measure.restrict_apply hA, Set.inter_compl_self, measure_empty,
      zero_mul]

/-- Restricting every partial sum is restricting the final sum. -/
lemma truncPairConvPow_eq (H : ℕ) (μ : Measure (ℕ × ℕ)) [IsFiniteMeasure μ] :
    ∀ n, truncPairConvPow H μ n = (pairConvPow μ n).restrict (lowTotal H)
  | 0 => by
    rw [truncPairConvPow, pairConvPow, Measure.restrict_eq_self_of_ae_mem]
    exact (ae_dirac_iff MeasurableSet.of_discrete).2 (zero_mem_lowTotal H)
  | n + 1 => by
    rw [truncPairConvPow, pairConvPow, truncPairConvPow_eq H μ n, restrict_conv_restrict]

/-! ### Totals -/

lemma pairConvPow_map_tot (μ : Measure (ℕ × ℕ)) [IsFiniteMeasure μ] :
    ∀ n, (pairConvPow μ n).map tot = natConvPow (μ.map tot) n
  | 0 => by
    rw [pairConvPow, natConvPow, Measure.map_dirac]
    rfl
  | n + 1 => by rw [pairConvPow, natConvPow, conv_map_tot, pairConvPow_map_tot μ n]

lemma poissonMeasure_zero : poissonMeasure 0 = Measure.dirac 0 := by
  refine Measure.ext_of_singleton fun k => ?_
  rw [poissonMeasure_singleton, Measure.dirac_apply' _ (measurableSet_singleton k)]
  rcases k with _ | k
  · simp
  · simp

lemma natConvPow_poisson (x : ℝ≥0) : ∀ n, natConvPow (poissonMeasure x) n = poissonMeasure (n * x)
  | 0 => by rw [natConvPow, Nat.cast_zero, zero_mul, poissonMeasure_zero]
  | n + 1 => by
    rw [natConvPow, natConvPow_poisson x n, poissonMeasure_conv_poissonMeasure]
    congr 1
    push_cast
    ring

/-- The depth's effective rate: `λ` for `t ≥ 1`, `0` at `t = 0`. -/
noncomputable def lamAt (lam : ℝ≥0) (t : ℕ) : ℝ≥0 := if t = 0 then 0 else lam

lemma lamAt_le (lam : ℝ≥0) (t : ℕ) : lamAt lam t ≤ lam := by
  unfold lamAt
  split_ifs <;> simp

lemma shadowTree_tot' (C : ℕ) (lam : ℝ≥0) (t : ℕ) :
    (shadowTree C lam t).map tot = poissonMeasure (lamAt lam t) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp only [lamAt, ↓reduceIte]
    rw [poissonMeasure_zero, shadowTree, Measure.map_dirac]
    rfl
  · have h0 : t ≠ 0 := by omega
    simp only [lamAt, h0, ↓reduceIte]
    exact shadowTree_tot C lam t ht

/-- The total of the radix node's sum is `Po(r λ_t q)`. -/
lemma radix_tot (C : ℕ) (lam : ℝ≥0) (t r : ℕ) (q : I) :
    (pairConvPow ((shadowTree C lam t).bind (thinPair q)) r).map tot =
      poissonMeasure (r * (lamAt lam t * pNN q)) := by
  have := isProb_shadowTree C lam t
  rw [pairConvPow_map_tot, thin_tot _ _ (shadowTree_tot' C lam t), natConvPow_poisson]

lemma lowTotal_compl (H : ℕ) : (lowTotal H)ᶜ = tot ⁻¹' {n | H < n} := by
  ext s
  simp [lowTotal, tot]

lemma map_tot_high (μ : Measure (ℕ × ℕ)) (H : ℕ) :
    μ (lowTotal H)ᶜ = (μ.map tot) {n | H < n} := by
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete, lowTotal_compl]

/-! ### Truncated trees put no mass above `H` -/

lemma truncTree_high (C : ℕ) (lam : ℝ≥0) (H : ℕ) :
    ∀ t, truncTree C lam H t (lowTotal H)ᶜ = 0
  | 0 => by
    rw [truncTree, Measure.dirac_apply' _ MeasurableSet.of_discrete]
    exact Set.indicator_of_notMem (fun h => absurd (zero_mem_lowTotal H) h) _
  | 1 => by
    rw [truncTree, Measure.restrict_apply MeasurableSet.of_discrete, Set.compl_inter_self,
      measure_empty]
  | t + 2 => by
    rw [truncTree]
    rw [Measure.restrict_apply MeasurableSet.of_discrete, Set.compl_inter_self, measure_empty]

lemma binomial_high {n H : ℕ} (h : n ≤ H) (p : I) : binomial n p {k | H < k} = 0 := by
  have := ae_iff.1 (ae_le_binomial n p)
  refine measure_mono_null (fun k hk => ?_) this
  simp only [Set.mem_ofPred_eq] at hk ⊢
  omega

lemma bind_thinPair_high (μ : Measure (ℕ × ℕ)) (H : ℕ) (p : I) (h : μ (lowTotal H)ᶜ = 0) :
    (μ.bind (thinPair p)) (lowTotal H)ᶜ = 0 := by
  rw [Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  have hae : ∀ᵐ s ∂μ, s ∈ lowTotal H := ae_iff.2 h
  rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
  filter_upwards [hae] with s hs
  rw [map_tot_high, thinPair_map_tot]
  exact binomial_high hs p

/-! ### Bernoulli's inequality -/

lemma one_le_pow_add {a b : ℝ≥0∞} (ha : a ≤ 1) (h : 1 ≤ a + b) :
    ∀ n : ℕ, 1 ≤ a ^ n + n * b
  | 0 => by simp
  | n + 1 => by
    have ih := one_le_pow_add ha h n
    calc (1 : ℝ≥0∞) ≤ a ^ n + n * b := ih
      _ ≤ a ^ n * (a + b) + n * b := by
          gcongr
          exact le_mul_of_one_le_right' h
      _ = a ^ (n + 1) + a ^ n * b + n * b := by ring
      _ ≤ a ^ (n + 1) + 1 * b + n * b := by
          gcongr
          exact pow_le_one₀ zero_le ha
      _ = a ^ (n + 1) + ((n + 1 : ℕ) : ℝ≥0∞) * b := by
          push_cast
          ring

end RebuildBound.P10rProof
