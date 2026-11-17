import RebuildBound.Spec.IdealSeed

/-! Independent client coins are integrated against the same canonical tape.
The seed may have infinite support and select its own initialization and keys.
These results transfer explicit slice laws; they do not establish hierarchy
freshness, a local failure estimate, or a simulator law by themselves. -/
namespace RebuildBound
open Spec Model MeasureTheory Spec.IdealKey
open scoped ENNReal

/-- Independent seed and tape laws preserve both original marginals. -/
theorem IdealSeedProbability : IdealSeedProbability_statement := by
  intro Seed _ μ _
  exact ⟨inferInstance, measurePreserving_fst.map_eq,
    measurePreserving_snd.map_eq⟩

/-- Countable seed sections suffice without discretizing the tape. -/
theorem IdealSeedMeasurable : IdealSeedMeasurable_statement := by
  intro Seed _ _ _ Value _ observe hmeas
  exact measurable_from_prod_countable_right hmeas

/-- Integrate the actual seed sections, allowing a different budget per seed. -/
theorem IdealSeedBound : IdealSeedBound_statement := by
  intro Seed _ μ _ event hevent bound hbound
  rw [Measure.prod_apply hevent]
  exact lintegral_mono hbound

namespace IdealSeedProof

/-- A uniform slice budget is unchanged by independent randomization. -/
theorem constant_bound {Seed : Type} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (event : Set (Seed × Tape)) (hevent : MeasurableSet event) (bound : ℝ≥0∞)
    (hbound : ∀ seed, tapeLaw (Prod.mk seed ⁻¹' event) ≤ bound) :
    (μ.prod tapeLaw) event ≤ bound := by
  simpa using IdealSeedBound Seed μ event hevent (fun _ => bound) hbound

end IdealSeedProof

/-- An identical public law in each seed slice gives the joint independent law. -/
theorem IdealSeedExact : IdealSeedExact_statement := by
  intro Seed _ μ _ Value _ simulator _ observe hmeas hslice
  have hjoint : MeasurePreserving (fun p : Seed × Tape => (p.1, observe p.1 p.2))
      (μ.prod tapeLaw) (μ.prod simulator) :=
    (MeasurePreserving.id μ).skew_product hmeas (Filter.Eventually.of_forall hslice)
  exact ⟨hjoint.map_eq, (measurePreserving_snd.comp hjoint).map_eq⟩

/-- Coupling is unconditional: seedwise failure bounds are mixed before the
agreement outside failure is transferred to measurable observation events. -/
theorem IdealSeedFailure : IdealSeedFailure_statement := by
  intro Seed _ μ _ Value _ simulator _ reference observed bad href _hobs hbad
    hslice hagree bound hbound event hevent
  have hmass := IdealSeedProof.constant_bound μ bad hbad bound hbound
  have hmap := (IdealSeedExact Seed μ Value simulator reference href hslice).2
  have hreference : simulator event =
      (μ.prod tapeLaw) (Function.uncurry reference ⁻¹' event) := by
    rw [← hmap, Measure.map_apply href hevent]
  rw [hreference]
  constructor
  · have hsubset : Function.uncurry observed ⁻¹' event ⊆
        (Function.uncurry reference ⁻¹' event) ∪ bad := by
      intro p hp
      by_cases h : p ∈ bad
      · exact Or.inr h
      · apply Or.inl
        change observed p.1 p.2 ∈ event at hp
        change reference p.1 p.2 ∈ event
        rwa [hagree p.1 p.2 h] at hp
    exact (measure_mono hsubset).trans
      ((measure_union_le _ _).trans (add_le_add le_rfl hmass))
  · have hsubset : Function.uncurry reference ⁻¹' event ⊆
        (Function.uncurry observed ⁻¹' event) ∪ bad := by
      intro p hp
      by_cases h : p ∈ bad
      · exact Or.inr h
      · apply Or.inl
        change reference p.1 p.2 ∈ event at hp
        change observed p.1 p.2 ∈ event
        rwa [hagree p.1 p.2 h]
    exact (measure_mono hsubset).trans
      ((measure_union_le _ _).trans (add_le_add le_rfl hmass))

end RebuildBound
