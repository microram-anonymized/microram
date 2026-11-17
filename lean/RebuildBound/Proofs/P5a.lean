import RebuildBound.Proofs.X2
import RebuildBound.Spec.P5

/-!
# P5a: key-by-key Pois(1) replacement

Induction on the list of laws, generalized over the base point `x`.  For the head
law `μ` and tail `T = convList μs`: swap to `T ∗ μ`, apply X2 to `f` itself at
the base point `x + t` for each fixed tail value `t` (replacing `μ` by its
compound Poisson law `P`), integrate, swap to `P ∗ T`, and apply the induction
hypothesis at base point `x + w`.  X2 is never applied to an averaged function.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open RebuildBound.Spec

namespace RebuildBound.P5aProof

variable {κ : Type} [Fintype κ] [DecidableEq κ]

private lemma convPow_prob (μ : Measure (κ → ℕ)) [IsProbabilityMeasure μ] (k : ℕ) :
    IsProbabilityMeasure (convPow μ k) := by
  induction k with
  | zero => simp only [convPow]; infer_instance
  | succ k ih => simp only [convPow]; infer_instance

private lemma compound_prob (μ : Measure (κ → ℕ)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (compoundPoisson 1 μ) := by
  refine ⟨?_⟩
  unfold compoundPoisson
  rw [Measure.sum_apply _ MeasurableSet.univ]
  have : ∀ k, (poissonMeasure 1 {k} • convPow μ k) Set.univ = poissonMeasure 1 {k} := by
    intro k
    have := convPow_prob μ k
    simp
  simp_rw [this]
  exact X2Proof.tsum_poisson_one

private lemma convList_prob (μs : List (Measure (κ → ℕ)))
    (h : ∀ μ ∈ μs, IsProbabilityMeasure μ) : IsProbabilityMeasure (convList μs) := by
  induction μs with
  | nil => simp only [convList]; infer_instance
  | cons μ μs ih =>
    have := h μ (by simp)
    have := ih (fun ν hν => h ν (by simp [hν]))
    simp only [convList]; infer_instance

private lemma main (f : (κ → ℕ) → ℝ≥0∞) (hc : DirConvex f) (hfin : ∀ y, f y ≠ ∞) :
    ∀ (μs : List (Measure (κ → ℕ))), (∀ μ ∈ μs, IsProbabilityMeasure μ) →
    ∀ (x : κ → ℕ),
      ∫⁻ v, f (x + v) ∂(convList μs) ≤
        ∫⁻ v, f (x + v) ∂(convList (μs.map (compoundPoisson 1))) := by
  intro μs
  induction μs with
  | nil => intro _ x; simp [convList]
  | cons μ μs ih =>
    intro h x
    have hμ := h μ (by simp)
    have h' : ∀ ν ∈ μs, IsProbabilityMeasure ν := fun ν hν => h ν (by simp [hν])
    have hT := convList_prob μs h'
    have hP := compound_prob μ
    have hT' := convList_prob (μs.map (compoundPoisson 1)) (by
      intro ν hν
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hν
      have := h' a ha
      exact compound_prob a)
    have hm : ∀ g : (κ → ℕ) → ℝ≥0∞, Measurable g := fun g => Measurable.of_discrete
    simp only [List.map_cons, convList]
    calc ∫⁻ v, f (x + v) ∂(μ ∗ convList μs)
        = ∫⁻ v, f (x + v) ∂(convList μs ∗ μ) := by rw [Measure.conv_comm]
      _ = ∫⁻ t, ∫⁻ w, f (x + (t + w)) ∂μ ∂(convList μs) := Measure.lintegral_conv (hm _)
      _ ≤ ∫⁻ t, ∫⁻ w, f (x + (t + w)) ∂(compoundPoisson 1 μ) ∂(convList μs) := by
          refine lintegral_mono fun t => ?_
          have := (RebuildBound.X2 (κ := κ)) f hc hfin μ (x + t)
          simpa [add_assoc] using this
      _ = ∫⁻ v, f (x + v) ∂(convList μs ∗ compoundPoisson 1 μ) :=
          (Measure.lintegral_conv (f := fun v => f (x + v)) (hm _)).symm
      _ = ∫⁻ v, f (x + v) ∂(compoundPoisson 1 μ ∗ convList μs) := by rw [Measure.conv_comm]
      _ = ∫⁻ w, ∫⁻ t, f (x + (w + t)) ∂(convList μs) ∂(compoundPoisson 1 μ) :=
          Measure.lintegral_conv (hm _)
      _ ≤ ∫⁻ w, ∫⁻ t, f (x + (w + t)) ∂(convList (μs.map (compoundPoisson 1)))
            ∂(compoundPoisson 1 μ) := by
          refine lintegral_mono fun w => ?_
          have := ih h' (x + w)
          simpa [add_assoc] using this
      _ = ∫⁻ v, f (x + v) ∂(compoundPoisson 1 μ ∗ convList (μs.map (compoundPoisson 1))) :=
          (Measure.lintegral_conv (f := fun v => f (x + v)) (hm _)).symm

end RebuildBound.P5aProof

theorem RebuildBound.P5a : RebuildBound.Spec.P5a_statement := by
  intro κ _ _ f hc hfin μs h x
  exact RebuildBound.P5aProof.main f hc hfin μs h x
