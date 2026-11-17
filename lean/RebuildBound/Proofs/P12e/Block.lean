import RebuildBound.Proofs.ShadowLaw.Tree
import RebuildBound.Spec.P12

/-!
# P12e: sums of independent node pairs

* `lintegral_sum_pair`: the sum over `S` of independent node pairs with law `μ` has
  law `pairConvPow μ |S|`;
* `map_sum_pi`: its measure form over all coordinates;
* `map_curry`: a product law over `κ × ι` whose factors depend only on the `ι`
  coordinate is the product over `ι` of products over `κ`;
* `map_blockSum`: adding the `r` blocks of a node, `y ↦ (W ↦ Σ_i y (i, W))`, maps
  such a product law to the product of the `r`-fold pair convolutions.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

set_option linter.unusedSectionVars false

namespace RebuildBound.P12eProof

open RebuildBound.Spec RebuildBound.P11eProof

lemma isProb_pairConvPow (μ : Measure (ℕ × ℕ)) [IsProbabilityMeasure μ] :
    ∀ n, IsProbabilityMeasure (pairConvPow μ n)
  | 0 => by rw [pairConvPow]; infer_instance
  | n + 1 => by
    have := isProb_pairConvPow μ n
    rw [pairConvPow]
    infer_instance

instance (μ : Measure (ℕ × ℕ)) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (pairConvPow μ n) :=
  isProb_pairConvPow μ n

/-- The pair sum over `S` of independent nodes with law `μ` has law
`pairConvPow μ |S|`. -/
lemma lintegral_sum_pair {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : Measure (ℕ × ℕ))
    [IsProbabilityMeasure μ] (ν : ι → Measure (ℕ × ℕ)) (hν : ∀ i, IsProbabilityMeasure (ν i))
    (S : Finset ι) (hS : ∀ v ∈ S, ν v = μ) (F : ℕ × ℕ → ℝ≥0∞) :
    ∫⁻ y, F (∑ v ∈ S, y v) ∂(Measure.pi ν) = ∫⁻ s, F s ∂(pairConvPow μ S.card) := by
  induction S using Finset.induction_on generalizing F with
  | empty =>
    simp [pairConvPow]
    rfl
  | insert a S ha ih =>
    rw [lintegral_pi_resample ν a]
    have hS' : ∀ (y : ι → ℕ × ℕ) z, ∑ v ∈ S, Function.update y a z v = ∑ v ∈ S, y v :=
      fun y z => Finset.sum_congr rfl fun v hv => by
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hv ha)]
    simp_rw [Finset.sum_insert ha, Function.update_self, hS']
    rw [hS a (Finset.mem_insert_self a S)]
    have ih' := ih (fun v hv => hS v (Finset.mem_insert_of_mem hv))
      (fun s => ∫⁻ z, F (z + s) ∂μ)
    rw [ih', Finset.card_insert_of_notMem ha, pairConvPow,
      Measure.lintegral_conv Measurable.of_discrete]
    exact lintegral_congr fun s => lintegral_congr fun z => by rw [add_comm]

/-- The sum of all coordinates of i.i.d. node pairs. -/
lemma map_sum_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : Measure (ℕ × ℕ))
    [IsProbabilityMeasure μ] :
    (Measure.pi (fun _ : ι => μ)).map (fun z => ∑ i, z i) = pairConvPow μ (Fintype.card ι) := by
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  rw [lintegral_map hF Measurable.of_discrete, ← Finset.card_univ]
  exact lintegral_sum_pair μ _ (fun _ => inferInstance) Finset.univ (fun _ _ => rfl) F

/-- Currying a product law whose factors depend only on the second coordinate. -/
lemma map_curry {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (ν : ι → Measure (ℕ × ℕ)) [∀ W, IsProbabilityMeasure (ν W)] :
    (Measure.pi (fun v : κ × ι => ν v.2)).map (fun y W i => y (i, W)) =
      Measure.pi (fun W => Measure.pi (fun _ : κ => ν W)) := by
  refine Measure.ext_of_singleton fun z => ?_
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton z)]
  have hpre : (fun (y : κ × ι → ℕ × ℕ) W i => y (i, W)) ⁻¹' {z} = {fun v => z v.2 v.1} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro rfl
      rfl
    · rintro rfl
      rfl
  rw [hpre, Measure.pi_singleton, Measure.pi_singleton, Fintype.prod_prod_type,
    Finset.prod_comm]
  refine Finset.prod_congr rfl fun W _ => ?_
  rw [Measure.pi_singleton]

/-- Adding the `r` blocks of every node. -/
lemma map_blockSum {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (ν : ι → Measure (ℕ × ℕ)) [∀ W, IsProbabilityMeasure (ν W)] :
    (Measure.pi (fun v : Fin r × ι => ν v.2)).map (fun y W => ∑ i, y (i, W)) =
      Measure.pi (fun W => pairConvPow (ν W) r) := by
  have he : (fun (y : Fin r × ι → ℕ × ℕ) W => ∑ i, y (i, W)) =
      (fun Y W => ∑ i, Y W i) ∘ (fun y W i => y (i, W)) := rfl
  rw [he, ← Measure.map_map Measurable.of_discrete Measurable.of_discrete, map_curry,
    Measure.pi_map_pi (f := fun _ (z : Fin r → ℕ × ℕ) => ∑ i, z i) (fun _ => Measurable.of_discrete.aemeasurable)]
  congr 1
  funext W
  rw [map_sum_pi, Fintype.card_fin]

end RebuildBound.P12eProof
