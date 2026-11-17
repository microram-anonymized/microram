import RebuildBound.Spec.P9
import Mathlib.Tactic

/-!
# P9: one capacity and arbitrarily dependent reference sources

The proof uses Mathlib's measure API throughout; there is no probability API
obstacle or finite-sum replacement. Counts and failure events need no
measurability premise because the conclusion follows from the outer-measure
union bound. Every marginal bound refers to the original measure, before
any success/failure conditioning. The allocation is a fixed public function.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound

open Spec

/-- A public allocation of the common capacity gives an unconditional bound. -/
theorem P9_alloc : Spec.P9_alloc_statement := by
  classical
  intro Ω ι _ _ μ _ T c S b F hmarg hfail a ha
  have hai (i : ι) : a i ≤ S := by
    rw [← ha]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
  have htail (i : ι) : μ {ω | a i < min (T i ω) (c i)} ≤
      cappedTail (c i) (b i) (a i) := by
    by_cases hc : c i ≤ a i
    · have he : {ω | a i < min (T i ω) (c i)} = (∅ : Set Ω) := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact not_lt.mpr ((min_le_right _ _).trans hc)
      rw [he]
      simp [cappedTail, hc]
    · rw [cappedTail, ite_eq_right hc]
      refine le_min prob_le_one ?_
      have hsub : {ω | a i < min (T i ω) (c i)} ⊆ {ω | a i < T i ω} := by
        intro ω hω
        change a i < T i ω
        change a i < min (T i ω) (c i) at hω
        exact lt_of_lt_of_le hω (min_le_left _ _)
      exact (measure_mono hsub).trans (hmarg i (a i) (hai i))
  have hcover : F ⊆ ⋃ i, {ω | a i < min (T i ω) (c i)} := by
    intro ω hω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    by_contra hnone
    push Not at hnone
    have hsum : (∑ i, min (T i ω) (c i)) ≤ S := by
      rw [← ha]
      exact Finset.sum_le_sum (fun i _ => hnone i)
    exact (not_lt_of_ge hsum) (hfail ω hω)
  apply le_min prob_le_one
  calc μ F ≤ μ (⋃ i, {ω | a i < min (T i ω) (c i)}) := measure_mono hcover
    _ ≤ ∑ i, μ {ω | a i < min (T i ω) (c i)} := measure_iUnion_fintype_le μ _
    _ ≤ ∑ i, cappedTail (c i) (b i) (a i) := Finset.sum_le_sum (fun i _ => htail i)

/-- Taking the best public allocation preserves the bound under all correlations. -/
theorem P9 : Spec.P9_statement := by
  intro Ω ι _ _ μ _ T c S b F hmarg hfail
  apply le_min prob_le_one
  apply le_iInf
  intro a
  exact (P9_alloc μ T c S b F hmarg hfail a.val a.property).trans (min_le_right _ _)

/-- The mixed-pool range bound sums range bounds, with no range independence. -/
theorem P9_ranges : Spec.P9_ranges_statement := by
  classical
  intro Ω ρ ι _ _ _ μ _ T c S b F hmarg hfail
  apply le_min prob_le_one
  have hcover : F ⊆ ⋃ q, {ω | S q < ∑ i, min (T q i ω) (c q i)} := by
    intro ω hω
    simpa only [Set.mem_iUnion, Set.mem_ofPred_eq] using hfail ω hω
  calc μ F ≤ μ (⋃ q, {ω | S q < ∑ i, min (T q i ω) (c q i)}) := measure_mono hcover
    _ ≤ ∑ q, μ {ω | S q < ∑ i, min (T q i ω) (c q i)} := measure_iUnion_fintype_le μ _
    _ ≤ ∑ q, mixedAllocationBound (S q) (c q) (b q) := by
      apply Finset.sum_le_sum
      intro q _
      exact P9 μ (T q) (c q) (S q) (b q) _ (hmarg q) (fun _ h => h)

namespace P9Proof

/-- Public source caps that fit one allocation give zero bound, even when the
uncapped marginal estimates are completely uninformative. -/
theorem publicCaps {ι : Type} [Fintype ι] (S : ℕ) (c : ι → ℕ)
    (b : ι → ℕ → ℝ≥0∞) (a : ι → ℕ) (ha : ∑ i, a i = S)
    (hcap : ∀ i, c i ≤ a i) : mixedAllocationBound S c b = 0 := by
  apply le_antisymm _ bot_le
  unfold mixedAllocationBound
  refine (min_le_right _ _).trans ?_
  calc _ ≤ ∑ i, cappedTail (c i) (b i) (a i) :=
      iInf_le _ (⟨a, ha⟩ : {a : ι → ℕ // ∑ i, a i = S})
    _ = 0 := by simp [cappedTail, hcap]

/-- A concrete non-vacuity witness for the public caps: two sources each
capped at two fit a shared capacity of four, regardless of their raw tails. -/
theorem twoPublicCaps :
    mixedAllocationBound (ι := Fin 2) 4 (fun _ => 2) (fun _ _ => ∞) = 0 := by
  exact publicCaps 4 (fun _ => 2) (fun _ _ => ∞) (fun _ => 2) (by simp)
    (fun _ => le_rfl)

/-- The report's identical-copy example. Each marginal is bounded by two,
yet both physical sources together overflow a shared capacity of two with
probability one. The valid allocation theorem returns exactly one. Thus the
failure premise is satisfiable and cannot be replaced by assigning the full
shared capacity independently to every source. -/
theorem correlatedCopies {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    let T : Fin 2 → Ω → ℕ := fun _ _ => 2
    μ {ω | 2 < ∑ i, min (T i ω) 2} = 1 ∧
      (∀ i, μ {ω | 2 < T i ω} = 0) ∧
      mixedAllocationBound (ι := Fin 2) 2 (fun _ => 2)
        (fun _ s => if s < 2 then 1 else 0) = 1 := by
  dsimp only
  refine ⟨by simp, (fun _ => by simp), ?_⟩
  apply le_antisymm (min_le_left _ _)
  have h := P9 μ (fun (_ : Fin 2) (_ : Ω) => 2) (fun _ => 2) 2
    (fun _ s => if s < 2 then 1 else 0) Set.univ ?_ ?_
  · simpa [mixedAllocationBound] using h
  · intro i s _
    by_cases hs : s < 2 <;> simp [hs]
  · intro ω _
    simp

end P9Proof

end RebuildBound
