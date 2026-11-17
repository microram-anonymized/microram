import RebuildBound.Proofs.ShadowLaw.Pi
import RebuildBound.Proofs.ShadowLaw.Stage

/-!
# P11e: one backward stage against a product law of node pairs

`toS y` reads a vector of node pairs `y v = (main, shadow)` as node states. Under a
product law `Measure.pi ν` of node pairs:

* `lintegral_thinAll`: thinning every node of a nodup list replaces each node's law
  by its bind with `thinPair`;
* `capAll_sumAlong_toS`: the stage-`j` addition and cap act on pairs by
  `stageMap`, which adds each node with bit `j` of `R` and its sibling and caps;
* `lintegral_backStage`: one backward stage integrates to the next product law
  `stepLaw`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

set_option linter.unusedSectionVars false

namespace RebuildBound.P11eProof

open RebuildBound.Spec

/-! ### The binary stage -/

section Bits

variable {b : ℕ}

lemma capAll_sumAlong_toS (C : ℕ) (j : Fin b) (r : Bool) (y : Bits b → ℕ × ℕ) :
    capAll (allNodes b) C (sumAlong (fun V => Function.update V j r) (toS y)) =
      toS (stageMap C j r y) := by
  rw [sumAlong_toS, capAll_toS]
  congr 1
  funext W
  simp only [allNodes, Finset.mem_toList, Finset.mem_univ, ite_true, stageMap,
    sum_filter_update]

lemma isProb_stepLaw (C : ℕ) (j : Fin b) (r : Bool) (ν : Bits b → Measure (ℕ × ℕ))
    (hν : ∀ i, IsProbabilityMeasure (ν i)) (W : Bits b) :
    IsProbabilityMeasure (stepLaw C j r ν W) :=
  isProb_combLaw C j r _ (fun _ => inferInstance) W

lemma map_stageMap (C : ℕ) (j : Fin b) (r : Bool) (μ : Bits b → Measure (ℕ × ℕ))
    (hμ : ∀ i, IsProbabilityMeasure (μ i)) :
    (Measure.pi μ).map (stageMap C j r) = Measure.pi (combLaw C j r μ) := by
  have := isProb_combLaw C j r μ hμ
  refine map_pairMap μ (flipEquiv j r) (fun q => capPair C (q.1 + q.2)) (0, 0) _ ?_ ?_ _ ?_ ?_
  · intro y t
    simp [stageMap, t.2]
  · intro y t
    simp [stageMap, capPair]
  · intro t
    simp only [flipEquiv_inl, flipEquiv_inr, combLaw, t.2, ite_true]
    rw [Measure.conv, Measure.map_map Measurable.of_discrete Measurable.of_discrete]
    rfl
  · intro t
    simp [combLaw]

/-- One backward stage against a product law of node pairs. -/
lemma lintegral_backStage (C : ℕ) (R : Bits b) (j : ℕ) (hj : j < b)
    (ν : Bits b → Measure (ℕ × ℕ)) (hν : ∀ i, IsProbabilityMeasure (ν i))
    (ψ : States (Bits b) → ℝ≥0∞) :
    ∫⁻ y, backStage C R j ψ (toS y) ∂(Measure.pi ν) =
      ∫⁻ y, ψ (toS y) ∂(Measure.pi (stepLaw C ⟨j, hj⟩ (R ⟨j, hj⟩) ν)) := by
  have hth : ∀ i, IsProbabilityMeasure ((ν i).bind (thinPair half)) := fun _ => inferInstance
  simp only [backStage, hj, dite_true]
  rw [lintegral_thinAll half _ (allNodes b) (Finset.nodup_toList _) ν hν]
  have hfam : (fun v => if v ∈ allNodes b then (ν v).bind (thinPair half) else ν v) =
      fun v => (ν v).bind (thinPair half) := by
    funext v
    simp [allNodes]
  rw [hfam]
  simp only [Function.comp_apply, capAll_sumAlong_toS]
  rw [← lintegral_map (f := fun w => ψ (toS w)) Measurable.of_discrete Measurable.of_discrete,
    map_stageMap C _ _ _ hth]
  rfl

end Bits

end RebuildBound.P11eProof
