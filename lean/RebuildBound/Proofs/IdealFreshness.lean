import RebuildBound.Spec.IdealFreshness
import RebuildBound.Proofs.IdealExposure
import RebuildBound.Proofs.IdealMeasurable
import RebuildBound.Proofs.IdealKeyLaw

/-! Factor the actual adaptive input prefix through the complete outside
environment. Canonical block independence then proves its independence from
every word of the fresh family simultaneously. -/
namespace RebuildBound
open Spec Model Model.Hierarchy Spec.IdealHierarchy MeasureTheory ProbabilityTheory

theorem IdealInputPrefixMeasurable : IdealInputPrefixMeasurable_statement := by
  let : MeasurableSpace (List (List Bucket)) := ⊤
  intro cfg sh g S m a cutoff
  apply IdealFiniteReadMeasurable
  exact (IdealAdaptiveFiniteRead cfg sh g S m a).comp fun result =>
    (List.range (cutoff - cfg.seed 1)).map fun i =>
      (OnlineBatch.traceOf g ⟨result.1, a.init, a.unsh⟩).units i

theorem IdealInputPrefixIndependent : IdealInputPrefixIndependent_statement := by
  let : MeasurableSpace (List (List Bucket)) := ⊤
  intro cfg sh g S m a hgeo hgeom hunit hS family
  classical
  let fresh := familyBlock family
  let fill : (↥(freshᶜ) → Word64) → IdealKey.Tape := fun outside coordinate =>
    if h : coordinate ∈ fresh then 0 else outside ⟨coordinate, h⟩
  have hfill : Measurable fill := by
    apply Measurable.of_eval
    intro coordinate
    by_cases h : coordinate ∈ fresh
    · simp only [fill, dite_eq_left h]
      exact measurable_const
    · simp only [fill, dite_eq_right h]
      exact measurable_pi_apply _
  let observe := inputPrefix cfg sh g S a (time cfg family.1 family.2)
  have hprefix : Measurable observe := IdealInputPrefixMeasurable cfg sh g S m a _
  have heq : observe = (observe ∘ fill) ∘ (freshᶜ).domRestrict := by
    funext tape
    apply List.map_congr_left
    intro i hi
    apply IdealAdaptiveFamilyFresh cfg sh g S m a hgeo hgeom hunit hS family
    · intro coordinate hc
      change coordinate ∉ fresh at hc
      simp only [fill, dite_eq_right hc, Set.domRestrict_apply]
    · have := List.mem_range.mp hi
      omega
  change IndepFun observe fresh.domRestrict IdealKey.tapeLaw
  rw [heq]
  exact (IdealKeyBlocks freshᶜ fresh disjoint_compl_left).1.comp
    (hprefix.comp hfill) measurable_id

end RebuildBound
