import RebuildBound.Spec.P5

/-!
# P5b: Poisson splitting, sums and padding

* `poissonVec_conv` (sums): `poissonVec ν = Π_k Po(ν k)`, so `poissonVec ν ∗ poissonVec ν'`
  is the image of `Π_k (Po(ν k) ⊗ Po(ν' k))` (`measurePreserving_arrowProdEquivProdArrow`)
  under coordinatewise addition, which is `Π_k Po(ν k + ν' k)` by `measurePreserving_pi`
  and `poissonMeasure_conv_poissonMeasure`.
* `poissonVec_pad` (padding): `poissonVec ν' = poissonVec ν ∗ poissonVec (ν' - ν)`, then
  `Measure.lintegral_conv` and `f y ≤ f (y + z)`.
* `split` (splitting): both sides are compared on singletons
  (`Measure.ext_of_singleton`). By induction on `m`, using
  `(μ ∗ unitLaw p) {n} = Σ_k p_k μ {x | x + e_k = n}`,
  `convPow (unitLaw p) m {n} = [Σ n = m] m! Π_k p_k^{n_k} / n_k!`.
  Summing against `Po(r)` and using `Σ p = 1` gives `Π_k Po(r p_k){n_k}`.

The measure-based API sufficed. The point-mass arithmetic is done in `ℝ` under
`ENNReal.ofReal`, which keeps `field_simp`/`ring` available; the multinomial API
(`Nat.multinomial`, `Finset.piAntidiag`) was not needed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RebuildBound.P5bProof

open RebuildBound.Spec

variable {κ : Type} [Fintype κ]

instance isProbabilityMeasure_poissonVec (ν : κ → ℝ≥0) :
    IsProbabilityMeasure (poissonVec ν) := by
  unfold poissonVec
  infer_instance

/-! ### Sums of Poisson vectors -/

/-- Adding two independent `Po(a)`, `Po(b)` counts gives `Po(a + b)`, as a
measure-preserving map. -/
lemma mp_add (a b : ℝ≥0) :
    MeasurePreserving (fun x : ℕ × ℕ => x.1 + x.2)
      ((poissonMeasure a).prod (poissonMeasure b)) (poissonMeasure (a + b)) where
  measurable := measurable_add
  map_eq := poissonMeasure_conv_poissonMeasure a b

lemma poissonVec_conv (ν ν' : κ → ℝ≥0) :
    poissonVec ν ∗ poissonVec ν' = poissonVec (ν + ν') := by
  have h1 := (measurePreserving_arrowProdEquivProdArrow ℕ ℕ κ
    (fun k => poissonMeasure (ν k)) (fun k => poissonMeasure (ν' k))).symm
  have h2 := measurePreserving_pi (fun k => (poissonMeasure (ν k)).prod (poissonMeasure (ν' k)))
    (fun k => poissonMeasure (ν k + ν' k)) (fun k => mp_add (ν k) (ν' k))
  have h3 := h2.comp h1
  exact h3.map_eq

/-! ### Padding of means -/

lemma poissonVec_pad (f : (κ → ℕ) → ℝ≥0∞) (hf : Monotone f) (ν ν' : κ → ℝ≥0)
    (h : ν ≤ ν') : ∫⁻ y, f y ∂(poissonVec ν) ≤ ∫⁻ y, f y ∂(poissonVec ν') := by
  have hν : ν' = ν + (ν' - ν) := by
    funext k
    exact (add_tsub_cancel_of_le (h k)).symm
  rw [hν, ← poissonVec_conv, Measure.lintegral_conv Measurable.of_discrete]
  refine lintegral_mono fun y => ?_
  calc f y = ∫⁻ _, f y ∂(poissonVec (ν' - ν)) := by simp [lintegral_const]
    _ ≤ ∫⁻ z, f (y + z) ∂(poissonVec (ν' - ν)) :=
        lintegral_mono fun z => hf fun k => Nat.le_add_right _ _

/-! ### Poisson splitting -/

section Split

variable [DecidableEq κ]

/-- The multinomial weight `∏ₖ p_k^{n_k} / n_k!`. -/
noncomputable def wt (p : κ → ℝ≥0) (n : κ → ℕ) : ℝ :=
  ∏ k, ((p k : ℝ) ^ n k / (n k).factorial)

omit [DecidableEq κ] in
lemma wt_nonneg (p : κ → ℝ≥0) (n : κ → ℕ) : 0 ≤ wt p n :=
  Finset.prod_nonneg fun _ _ => by positivity

lemma wt_add_unit (p : κ → ℝ≥0) (n : κ → ℕ) (k : κ) :
    wt p (n + unitVec k) * ((n k : ℝ) + 1) = p k * wt p n := by
  unfold wt
  rw [Fintype.prod_eq_mul_prod_compl k, Fintype.prod_eq_mul_prod_compl k]
  have hrest : ∏ j ∈ {k}ᶜ, ((p j : ℝ) ^ (n + unitVec k) j / ((n + unitVec k) j).factorial)
      = ∏ j ∈ {k}ᶜ, ((p j : ℝ) ^ n j / (n j).factorial) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjk : j ≠ k := by simpa using hj
    simp [unitVec, Pi.single_eq_of_ne hjk]
  rw [hrest]
  simp only [Pi.add_apply, unitVec, Pi.single_eq_same]
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma sum_add_unit (n : κ → ℕ) (k : κ) : ∑ j, (n + unitVec k) j = ∑ j, n j + 1 := by
  simp [unitVec, Finset.sum_add_distrib]

omit [Fintype κ] in
lemma preimage_add_unit (k : κ) (n : κ → ℕ) :
    (· + unitVec k) ⁻¹' {n + unitVec k} = {n} := by
  ext x
  simp

omit [Fintype κ] in
lemma preimage_add_unit_empty (k : κ) (n : κ → ℕ) (h : n k = 0) :
    (· + unitVec k) ⁻¹' {n} = ∅ := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  intro hx
  have := congrFun hx k
  simp [unitVec] at this
  omega

/-- One more unit vector, evaluated at a point. -/
lemma conv_unitLaw_apply (μ : Measure (κ → ℕ)) (p : κ → ℝ≥0) (n : κ → ℕ) :
    (μ ∗ unitLaw p) {n} = ∑ k, (p k : ℝ≥0∞) * μ ((· + unitVec k) ⁻¹' {n}) := by
  rw [← lintegral_indicator_one (measurableSet_singleton n),
    Measure.lintegral_conv Measurable.of_discrete]
  simp only [unitLaw, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac,
    smul_eq_mul]
  rw [lintegral_finsetSum _ (fun _ _ => Measurable.of_discrete)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [lintegral_const_mul _ Measurable.of_discrete,
    ← lintegral_indicator_one (MeasurableSet.of_discrete)]
  rfl

/-- The point masses of `convPow (unitLaw p) m`: multinomial weights. -/
lemma convPow_unitLaw_apply (p : κ → ℝ≥0) (m : ℕ) (n : κ → ℕ) :
    convPow (unitLaw p) m {n} =
      if ∑ k, n k = m then ENNReal.ofReal (m.factorial * wt p n) else 0 := by
  induction m generalizing n with
  | zero =>
    simp only [convPow]
    rw [Measure.dirac_apply]
    by_cases hn : n = 0
    · subst hn
      simp [wt]
    · have : ∑ k, n k ≠ 0 := by
        intro h
        apply hn
        funext k
        exact (Finset.sum_eq_zero_iff.1 h) k (Finset.mem_univ k)
      simp [this, Ne.symm hn]
  | succ m ih =>
    change (convPow (unitLaw p) m ∗ unitLaw p) {n} = _
    rw [conv_unitLaw_apply]
    have key : ∀ k, (p k : ℝ≥0∞) * convPow (unitLaw p) m ((· + unitVec k) ⁻¹' {n}) =
        if ∑ j, n j = m + 1 then ENNReal.ofReal (m.factorial * n k * wt p n) else 0 := by
      intro k
      by_cases hk : n k = 0
      · rw [preimage_add_unit_empty k n hk]
        simp [hk]
      · obtain ⟨n', rfl⟩ : ∃ n', n = n' + unitVec k := by
          refine ⟨n - unitVec k, ?_⟩
          funext j
          by_cases hj : j = k
          · subst hj
            simp [unitVec]
            omega
          · simp [unitVec, Pi.single_eq_of_ne hj]
        rw [preimage_add_unit, ih, sum_add_unit]
        by_cases hs : ∑ j, n' j = m
        · simp only [hs, ite_true]
          rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have hw := wt_add_unit p n' k
          have hnk : ((n' + unitVec k) k : ℝ) = (n' k : ℝ) + 1 := by
            simp [unitVec]
          rw [hnk]
          linear_combination (-(m.factorial : ℝ)) * hw
        · simp [hs]
    rw [Finset.sum_congr rfl fun k _ => key k]
    by_cases h : ∑ j, n j = m + 1
    · simp only [h, ite_true]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by have := wt_nonneg p n; positivity)]
      congr 1
      rw [← Finset.sum_mul, ← Finset.mul_sum, ← Nat.cast_sum, h, Nat.factorial_succ]
      push_cast
      ring
    · simp [h]

lemma compoundPoisson_unitLaw_apply (r : ℝ≥0) (p : κ → ℝ≥0) (n : κ → ℕ) :
    compoundPoisson r (unitLaw p) {n} =
      ENNReal.ofReal (Real.exp (-r) * r ^ (∑ k, n k) * wt p n) := by
  rw [compoundPoisson, Measure.sum_apply _ (measurableSet_singleton n)]
  simp only [Measure.smul_apply, smul_eq_mul, convPow_unitLaw_apply]
  rw [tsum_eq_single (∑ k, n k)]
  · simp only [ite_true]
    rw [poissonMeasure_singleton, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : ((∑ k, n k).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  · intro m hm
    simp [Ne.symm hm]

omit [DecidableEq κ] in
lemma poissonVec_apply (ν : κ → ℝ≥0) (n : κ → ℕ) :
    poissonVec ν {n} =
      ENNReal.ofReal (∏ k, (Real.exp (-(ν k)) * (ν k) ^ n k / (n k).factorial)) := by
  rw [poissonVec, Measure.pi_singleton]
  simp only [poissonMeasure_singleton]
  rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity)]

lemma split (r : ℝ≥0) (p : κ → ℝ≥0) (hp : ∑ k, p k = 1) :
    compoundPoisson r (unitLaw p) = poissonVec (fun k => r * p k) := by
  refine Measure.ext_of_singleton fun n => ?_
  rw [compoundPoisson_unitLaw_apply, poissonVec_apply]
  congr 1
  have hp' : ∑ k, (p k : ℝ) = 1 := by exact_mod_cast hp
  have hk : ∀ k, Real.exp (-((r * p k : ℝ≥0) : ℝ)) * ((r * p k : ℝ≥0) : ℝ) ^ n k / (n k).factorial
      = Real.exp (-((r : ℝ) * p k)) * ((r : ℝ) ^ n k * ((p k : ℝ) ^ n k / (n k).factorial)) := by
    intro k
    rw [NNReal.coe_mul, mul_pow]
    ring
  rw [Finset.prod_congr rfl fun k _ => hk k, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    ← Real.exp_sum, Finset.prod_pow_eq_pow_sum, wt,
    show ∑ k, -((r : ℝ) * p k) = -(r : ℝ) by
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum, hp', mul_one]]
  ring

end Split

end RebuildBound.P5bProof

theorem RebuildBound.P5b_split : RebuildBound.Spec.P5b_split_statement := by
  intro κ _ _ r p hp
  exact RebuildBound.P5bProof.split r p hp

theorem RebuildBound.P5b_conv : RebuildBound.Spec.P5b_conv_statement := by
  intro κ _ ν ν'
  exact RebuildBound.P5bProof.poissonVec_conv ν ν'

theorem RebuildBound.P5b_pad : RebuildBound.Spec.P5b_pad_statement := by
  intro κ _ f hf ν ν' h
  exact RebuildBound.P5bProof.poissonVec_pad f hf ν ν' h
