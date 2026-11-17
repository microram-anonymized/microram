import RebuildBound.Proofs.P12e
import RebuildBound.Spec.P13

/-!
# P13e: the forest identity with a drain-only terminal node

As P12e (`Proofs/P12e.lean`), but the terminal radix node has no cap, so the range's
shadow total is the sum over its `2^lo` buckets and `r` blocks of the thinned root
shadow counts: `lintegral_radixTermTest0` reads it through P11e's `lintegral_sum_snd`
over the node set `univ ×ˢ rangeHomes`. At radix one, `radixRoot C λ t 1 q` is the shadow
marginal of the thinned tree because the main count of `shadowTree` is at most `C`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

set_option linter.unusedSectionVars false

namespace RebuildBound.P13eProof

open RebuildBound.Spec RebuildBound.P11eProof RebuildBound.P12eProof

variable {r b : ℕ}

lemma ae_main_le (C : ℕ) (lam : ℝ≥0) (t : ℕ) : ∀ᵐ s ∂(shadowTree C lam t), s.1 ≤ C := by
  rcases t with _ | _ | t
  · rw [shadowTree]; simp
  · rw [shadowTree, ae_map_iff Measurable.of_discrete.aemeasurable (by measurability)]
    exact Filter.Eventually.of_forall fun n => by simp [capPair]
  · rw [shadowTree, ae_map_iff Measurable.of_discrete.aemeasurable (by measurability)]
    exact Filter.Eventually.of_forall fun n => by simp [capPair]

lemma ae_thinPair_le (q : I) (a : ℕ × ℕ) : ∀ᵐ s ∂(thinPair q a), s.1 ≤ a.1 := by
  unfold thinPair
  have h : ∀ᵐ x ∂(binomial a.1 q), x ≤ a.1 :=
    ae_le_of_hasLaw_binomial (HasLaw.id (μ := binomial a.1 q))
  exact (Measure.quasiMeasurePreserving_fst).ae h

lemma ae_bind_thin_le (C : ℕ) (lam : ℝ≥0) (t : ℕ) (q : I) :
    ∀ᵐ s ∂((shadowTree C lam t).bind (thinPair q)), s.1 ≤ C := by
  rw [ae_iff, Measure.bind_apply (by measurability) Measurable.of_discrete.aemeasurable]
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [ae_main_le C lam t] with a ha
  have h := ae_thinPair_le q a
  rw [ae_iff] at h
  refine measure_mono_null (fun s hs => ?_) h
  simp only [Set.mem_ofPred_eq, not_le] at hs ⊢
  omega

lemma pairConvPow_one (μ : Measure (ℕ × ℕ)) [SFinite μ] : pairConvPow μ 1 = μ := by
  rw [pairConvPow, pairConvPow, Measure.conv_comm, Measure.conv_dirac]
  have : (fun y : ℕ × ℕ => y + (0, 0)) = id := by funext y; simp
  rw [this, Measure.map_id]

/-- At radix one the radix root is the shadow marginal of the thinned tree. -/
lemma radixRoot_one (C : ℕ) (lam : ℝ≥0) (t : ℕ) (q : I) :
    radixRoot C lam t 1 q = ((shadowTree C lam t).bind (thinPair q)).map Prod.snd := by
  have := isProb_shadowTree C lam t
  unfold radixRoot
  rw [pairConvPow_one]
  refine Measure.map_congr ?_
  filter_upwards [ae_bind_thin_le C lam t q] with s hs
  simp [Nat.sub_eq_zero_of_le hs]

lemma lintegral_radixTermTest0 (P : ℕ) (pe q : I) (L lo : ℕ) (R : Bits b) (hlo : lo ≤ b)
    (κ : Bits b → Measure (ℕ × ℕ)) (hκ : ∀ W, IsProbabilityMeasure (κ W))
    (μ : Measure (ℕ × ℕ)) [IsProbabilityMeasure μ] (hS : ∀ W ∈ rangeHomes lo R, κ W = μ) :
    ∫⁻ y, radixTermTest0 P pe q L lo R (toS y) ∂(Measure.pi (fun v : RNode r b => κ v.2)) =
      stopLoss (binomial P pe ∗ natConvPow ((μ.bind (thinPair q)).map Prod.snd)
        (2 ^ lo * r)) L := by
  have hth : ∀ v : RNode r b, IsProbabilityMeasure ((κ v.2).bind (thinPair q)) :=
    fun _ => inferInstance
  unfold radixTermTest0
  rw [lintegral_thinAll q _ (allRNodes r b) (Finset.nodup_toList _) _ (fun _ => inferInstance)]
  simp only [mem_allRNodes, ite_true, Function.comp_apply, sumAlong_snd_toS]
  unfold termTest stopLoss
  rw [lintegral_lintegral_swap Measurable.of_discrete.aemeasurable,
    Measure.lintegral_conv Measurable.of_discrete]
  refine lintegral_congr fun e => ?_
  have hsum : ∀ y : RNode r b → ℕ × ℕ,
      ∑ v ∈ rangeHomes lo R, toS (fun W => ∑ i, y (i, W)) (v, .shadow) =
        ∑ p ∈ (Finset.univ : Finset (Fin r)) ×ˢ rangeHomes lo R, (y p).2 := by
    intro y
    rw [Finset.sum_product_right]
    simp [Prod.snd_sum]
  simp_rw [hsum]
  have hcard : ((Finset.univ : Finset (Fin r)) ×ˢ rangeHomes lo R).card = 2 ^ lo * r := by
    rw [Finset.card_product, card_rangeHomes lo R hlo]
    simp [mul_comm]
  have := lintegral_sum_snd (μ.bind (thinPair q)) (fun v : RNode r b => (κ v.2).bind (thinPair q))
    hth ((Finset.univ : Finset (Fin r)) ×ˢ rangeHomes lo R)
    (fun v hv => by
      have := (Finset.mem_product.1 hv).2
      simp only [hS _ this])
    (fun s => ((e + s - L : ℕ) : ℝ≥0∞))
  rw [this, hcard]

end RebuildBound.P13eProof

open RebuildBound.Spec RebuildBound.P11eProof RebuildBound.P12eProof RebuildBound.P13eProof in
theorem RebuildBound.P13e : RebuildBound.Spec.P13e_statement := by
  intro r b C P L lo R q lam hlo _hr
  unfold rFirstArrivalTest0
  have h0 : ∀ N : RNode r b → ℕ,
      capAll (allRNodes r b) C (mainEmbed N) = toS (fun v => capPair C (N v, 0)) :=
    fun N => capAll_mainEmbed C _ (by intro v; simp [allRNodes]) N
  simp_rw [h0]
  rw [← lintegral_map (f := fun y => rForestTest C R
    (radixTermTest0 P (q * halfPow (b - lo)) q L lo R) (lo + 1) (toS y))
    Measurable.of_discrete Measurable.of_discrete]
  have h1 : (poissonVec (fun _ : RNode r b => lam)).map (fun N v => capPair C (N v, 0)) =
      Measure.pi (lawAtR C lam lo R (lo + 1)) := by
    rw [poissonVec_map_capPair]
    congr 1
    funext v
    exact (congrFun (lawAt_initial C lam lo R) v.2).symm
  have hS : ∀ v ∈ rangeHomes lo R, lawAt C lam lo R b v = shadowTree C lam (b - lo) := by
    intro v hv
    unfold lawAt
    rw [ite_eq_left]
    intro i h1 _
    exact (Finset.mem_filter.1 hv).2 i h1.le
  have := isProb_shadowTree C lam (b - lo)
  rw [h1, lintegral_rForestTest C lam lo R _ (b - (lo + 1)) (lo + 1) (by omega) (by omega)]
  unfold rangeLawR
  rw [radixRoot_one]
  exact lintegral_radixTermTest0 P _ q L lo R hlo.le (lawAt C lam lo R b)
    (isProb_lawAt C lam lo R b) _ hS
