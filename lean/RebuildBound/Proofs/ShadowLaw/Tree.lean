import RebuildBound.Proofs.ShadowLaw.Stage

/-!
# ShadowLaw: the shadow tree law (from P11e)

Moved from the d = 2 chain (`P11e`); namespace `RebuildBound.P11eProof` kept.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval
set_option linter.unusedSectionVars false
namespace RebuildBound.P11eProof
open RebuildBound.Spec
lemma isProb_shadowTree (C : ℕ) (lam : ℝ≥0) :
    ∀ t, IsProbabilityMeasure (shadowTree C lam t)
  | 0 => by rw [shadowTree]; infer_instance
  | 1 => by rw [shadowTree]; infer_instance
  | t + 2 => by
    have := isProb_shadowTree C lam (t + 1)
    rw [shadowTree]
    infer_instance

variable {b : ℕ}
/-- The law of the node pairs after stage `j`: a depth-`(j - lo)` shadow tree at the
nodes that agree with `R` on bits `lo + 1, …, j - 1`, empty elsewhere. -/
noncomputable def lawAt (C : ℕ) (lam : ℝ≥0) (lo : ℕ) (R : Bits b) (j : ℕ) (W : Bits b) :
    Measure (ℕ × ℕ) :=
  if ∀ i : Fin b, lo < i.val → i.val < j → W i = R i then shadowTree C lam (j - lo)
  else Measure.dirac (0, 0)

/-- The initial product law, before any forest stage. -/
lemma poissonVec_map_capPair {ι : Type*} [Fintype ι] (C : ℕ) (lam : ℝ≥0) :
    (poissonVec (fun _ : ι => lam)).map (fun N v => capPair C (N v, 0)) =
      Measure.pi (fun _ : ι => shadowTree C lam 1) := by
  unfold poissonVec
  rw [Measure.pi_map_pi (f := fun _ n => capPair C (n, 0))
    (fun _ => Measurable.of_discrete.aemeasurable)]
  rfl

lemma lawAt_initial (C : ℕ) (lam : ℝ≥0) (lo : ℕ) (R : Bits b) :
    lawAt C lam lo R (lo + 1) = fun _ => shadowTree C lam 1 := by
  funext W
  unfold lawAt
  rw [ite_eq_left (fun i h1 h2 => absurd h2 (by omega))]
  simp

lemma isProb_lawAt (C : ℕ) (lam : ℝ≥0) (lo : ℕ) (R : Bits b) (j : ℕ) (W : Bits b) :
    IsProbabilityMeasure (lawAt C lam lo R j W) := by
  unfold lawAt
  split_ifs
  · exact isProb_shadowTree C lam _
  · infer_instance

lemma stepLaw_lawAt (C : ℕ) (lam : ℝ≥0) (lo : ℕ) (R : Bits b) (j : ℕ) (hj : j < b)
    (hlo : lo < j) :
    stepLaw C ⟨j, hj⟩ (R ⟨j, hj⟩) (lawAt C lam lo R j) = lawAt C lam lo R (j + 1) := by
  funext W
  set j' : Fin b := ⟨j, hj⟩ with hj'
  have hgood : ∀ W : Bits b, (∀ i : Fin b, lo < i.val → i.val < j + 1 → W i = R i) ↔
      ((∀ i : Fin b, lo < i.val → i.val < j → W i = R i) ∧ W j' = R j') := by
    intro W
    constructor
    · intro h
      exact ⟨fun i h1 h2 => h i h1 (by omega), h j' (by simp [j']; omega) (by simp [j'])⟩
    · rintro ⟨h, hW⟩ i h1 h2
      by_cases hi : i.val < j
      · exact h i h1 hi
      · have : i = j' := Fin.ext (by simp [j']; omega)
        rw [this]
        exact hW
  have hflip : ∀ W : Bits b,
      (∀ i : Fin b, lo < i.val → i.val < j → Function.update W j' (!R j') i = R i) ↔
        (∀ i : Fin b, lo < i.val → i.val < j → W i = R i) := by
    intro W
    have hne : ∀ i : Fin b, i.val < j → i ≠ j' := fun i hi h => by
      rw [h] at hi
      simp [j'] at hi
    constructor
    · intro h i h1 h2
      rw [← h i h1 h2, Function.update_of_ne (hne i h2)]
    · intro h i h1 h2
      rw [Function.update_of_ne (hne i h2)]
      exact h i h1 h2
  simp only [stepLaw, combLaw]
  by_cases hW : W j' = R j'
  · rw [ite_eq_left hW]
    by_cases hg : ∀ i : Fin b, lo < i.val → i.val < j → W i = R i
    · unfold lawAt
      rw [ite_eq_left hg, ite_eq_left ((hflip W).2 hg), ite_eq_left ((hgood W).2 ⟨hg, hW⟩)]
      obtain ⟨t, ht⟩ : ∃ t, j - lo = t + 1 := ⟨j - lo - 1, by omega⟩
      rw [ht, show j + 1 - lo = t + 2 by omega, shadowTree]
    · unfold lawAt
      rw [ite_eq_right hg, ite_eq_right (mt (hflip W).1 hg),
        ite_eq_right (fun h => hg ((hgood W).1 h).1),
        Measure.dirac_bind Measurable.of_discrete]
      simp [thinPair, binomial_zero, Measure.dirac_prod_dirac, Measure.dirac_conv_dirac,
        Measure.map_dirac, capPair]
  · rw [ite_eq_right hW]
    unfold lawAt
    rw [ite_eq_right (fun h => hW ((hgood W).1 h).2)]

/-- The shadow sum over `S` of independent nodes with law `μ` has law
`natConvPow (μ.map Prod.snd) |S|`. -/
lemma lintegral_sum_snd {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : Measure (ℕ × ℕ))
    [IsProbabilityMeasure μ] (ν : ι → Measure (ℕ × ℕ)) (hν : ∀ i, IsProbabilityMeasure (ν i))
    (S : Finset ι) (hS : ∀ v ∈ S, ν v = μ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ y, F (∑ v ∈ S, (y v).2) ∂(Measure.pi ν) =
      ∫⁻ s, F s ∂(natConvPow (μ.map Prod.snd) S.card) := by
  induction S using Finset.induction_on generalizing F with
  | empty => simp [natConvPow, lintegral_dirac]
  | insert a S ha ih =>
    rw [lintegral_pi_resample ν a]
    have hS' : ∀ (y : ι → ℕ × ℕ) z, ∑ v ∈ S, (Function.update y a z v).2 = ∑ v ∈ S, (y v).2 :=
      fun y z => Finset.sum_congr rfl fun v hv => by
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hv ha)]
    simp_rw [Finset.sum_insert ha, Function.update_self, hS']
    rw [hS a (Finset.mem_insert_self a S)]
    have ih' := ih (fun v hv => hS v (Finset.mem_insert_of_mem hv))
      (fun s => ∫⁻ z, F (z.2 + s) ∂μ)
    rw [ih', Finset.card_insert_of_notMem ha, natConvPow,
      Measure.lintegral_conv Measurable.of_discrete]
    refine lintegral_congr fun s => ?_
    rw [lintegral_map Measurable.of_discrete measurable_snd]
    simp_rw [add_comm]

lemma card_rangeHomes (lo : ℕ) (R : Bits b) (hlo : lo ≤ b) :
    (rangeHomes lo R).card = 2 ^ lo := by
  unfold rangeHomes
  rw [← Fintype.card_subtype]
  let e : {v : Bits b // InRange lo R v} ≃ (Fin lo → Bool) :=
    { toFun := fun v k => v.1 ⟨k.val, by omega⟩
      invFun := fun w => ⟨fun i => if h : i.val < lo then w ⟨i.val, h⟩ else R i,
        fun i hi => by simp [not_lt.2 hi]⟩
      left_inv := fun v => by
        apply Subtype.ext
        funext i
        by_cases h : i.val < lo
        · simp [h]
        · simp [h, v.2 i (not_lt.1 h)]
      right_inv := fun w => by
        funext k
        simp [k.2] }
  rw [Fintype.card_congr e]
  simp

lemma lintegral_termTest (P : ℕ) (p : I) (L lo : ℕ) (R : Bits b) (ν : Bits b → Measure (ℕ × ℕ))
    (hν : ∀ i, IsProbabilityMeasure (ν i)) (μ : Measure (ℕ × ℕ)) [IsProbabilityMeasure μ]
    (hS : ∀ v ∈ rangeHomes lo R, ν v = μ) :
    ∫⁻ y, termTest P p L lo R (toS y) ∂(Measure.pi ν) =
      stopLoss (binomial P p ∗ natConvPow (μ.map Prod.snd) (rangeHomes lo R).card) L := by
  unfold termTest stopLoss
  rw [lintegral_lintegral_swap Measurable.of_discrete.aemeasurable,
    Measure.lintegral_conv Measurable.of_discrete]
  refine lintegral_congr fun e => ?_
  exact lintegral_sum_snd μ ν hν _ hS (fun s => ((e + s - L : ℕ) : ℝ≥0∞))

end RebuildBound.P11eProof
