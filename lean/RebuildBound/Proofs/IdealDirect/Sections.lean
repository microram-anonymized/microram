import RebuildBound.Proofs.IdealKeyLaw

/-! Integrate a measurable event on the canonical tape by replacing one complete
coordinate block. Neither the outside environment nor the block is discretized. -/
namespace RebuildBound.IdealDirectProof
open Model Spec MeasureTheory
open scoped ENNReal

noncomputable def merge (fresh : Set IdealKey.Coord)
    (outside : (↥(freshᶜ) → Word64)) (inside : fresh → Word64) : IdealKey.Tape := by
  classical
  exact fun coordinate => if h : coordinate ∈ fresh then inside ⟨coordinate, h⟩
    else outside ⟨coordinate, h⟩

theorem merge_measurable (fresh : Set IdealKey.Coord) :
    Measurable (fun p : (↥(freshᶜ) → Word64) × (fresh → Word64) =>
      merge fresh p.1 p.2) := by
  classical
  apply Measurable.of_eval
  intro coordinate
  by_cases h : coordinate ∈ fresh
  · simp only [merge, dite_eq_left h]
    fun_prop
  · simp only [merge, dite_eq_right h]
    fun_prop

theorem merge_restrict (fresh : Set IdealKey.Coord) (tape : IdealKey.Tape) :
    merge fresh (freshᶜ.domRestrict tape) (fresh.domRestrict tape) = tape := by
  classical
  funext coordinate
  by_cases h : coordinate ∈ fresh <;> simp [merge, h]

theorem merge_outside (fresh : Set IdealKey.Coord)
    (outside : (↥(freshᶜ) → Word64)) (x y : fresh → Word64)
    (coordinate : IdealKey.Coord) (h : coordinate ∉ fresh) :
    merge fresh outside x coordinate = merge fresh outside y coordinate := by
  simp only [merge, dite_eq_right h]

theorem outside_bound (fresh : Set IdealKey.Coord) (event : Set IdealKey.Tape)
    (hevent : MeasurableSet event) (bound : ℝ≥0∞)
    (hsection : ∀ outside, (Measure.infinitePi (fun _ : fresh => IdealKey.wordLaw))
      {inside | merge fresh outside inside ∈ event} ≤ bound) :
    IdealKey.tapeLaw event ≤ bound := by
  let E := (fun p : (↥(freshᶜ) → Word64) × (fresh → Word64) =>
    merge fresh p.1 p.2) ⁻¹' event
  have h := IdealKeyOutsideSections fresh E (hevent.preimage (merge_measurable fresh))
    bound hsection
  have heq : ((fun tape => ((freshᶜ).domRestrict tape, fresh.domRestrict tape)) ⁻¹' E) =
      event := by
    ext tape
    simp only [E, Set.mem_preimage, merge_restrict]
  rwa [heq] at h

end RebuildBound.IdealDirectProof
