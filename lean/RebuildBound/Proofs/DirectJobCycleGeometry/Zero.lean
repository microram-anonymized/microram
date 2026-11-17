import RebuildBound.Proofs.DirectJobCycleGeometry
import RebuildBound.Spec.DirectJobCycleBounds

open MeasureTheory
open scoped ENNReal
namespace RebuildBound.DirectJobUniformCycleProof
open Model Model.DirectJob Spec
noncomputable section
variable {n : Nat} (units : Fin n → List Bucket)

def lawZero (h0 : 0 < n) : SJobLaw (selectedDirectSep 1) where
  KA := ∅
  KB := cycleKeys units ⟨0, h0⟩
  W := 64
  Hist := Unit
  weight _ := 1
  aIn _ := ([], [])
  wOld _ _ := 0
  bIn _ _ := ([], [])

def wordsZero (h0 : 0 < n) :
    Words units ⟨0, h0⟩ ≃ (lawZero units h0).toFinite.Outcome :=
  (keyCast (K := cycleKeys units ⟨0, h0⟩) (K' := ∅ ∪ cycleKeys units ⟨0, h0⟩)
    (Finset.empty_union _).symm (Fin (2 ^ 64))).trans
    (Equiv.uniqueProd ((∅ ∪ cycleKeys units ⟨0, h0⟩ : Finset Model.LogicalKey) → Fin (2 ^ 64)) Unit).symm

def splitZero (h0 : 0 < n) :
    CycleTape units ≃ (lawZero units h0).toFinite.Outcome ×
      (∀ j : {j : Fin n // j ≠ ⟨0, h0⟩}, Words units j) :=
  let e1 : (∀ j, Words units j) ≃ Words units ⟨0, h0⟩ ×
      (∀ j : {j : Fin n // j ≠ ⟨0, h0⟩}, Words units j) :=
    Equiv.piSplitAt (⟨0, h0⟩ : Fin n) (Words units)
  e1.trans (Equiv.prodCongr (wordsZero units h0) (Equiv.refl _))

theorem digitOneFor (capacity : Nat) [MeasurableSpace (CycleTape units)] [MeasurableSingletonClass (CycleTape units)]
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (π : Ω → CycleTape units) (hπ : Measurable π)
    (hμ : μ.map π = ProbabilityTheory.uniformOn (Set.univ : Set (CycleTape units)))
    (hcard : ∀ j, (unitKeys (units j)).card ≤ capacity)
    (native : Fin n → Ω → Model.LogicalKey → Nat)
    (hnative : ∀ j ω k (hk : k ∈ cycleKeys units j), native j ω k = π ω j ⟨k, hk⟩)
    (h0 : 0 < n) :
    DirectCycleDigitOneCoupled μ capacity (cycleStepsOn units native) := by
  refine ⟨_, lawZero units h0, fun _ _ => adopt emptyOutput (units ⟨0, h0⟩),
    fun ω => (splitZero units h0 (π ω)).1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [lawZero]
    rfl
  · rfl
  · intro _ _
    show unitKeys (units ⟨0, h0⟩) = cycleKeys units ⟨0, h0⟩
    exact (cycleKeys_zero units h0).symm
  · show (cycleKeys units ⟨0, h0⟩).card ≤ capacity
    rw [cycleKeys_zero]
    exact hcard _
  · exact FiniteCouplingProof.finite_uniform_image_coupling μ π hπ hμ (lawZero units h0).toFinite _
      (splitZero units h0) (fun _ => by simp [lawZero, SJobLaw.toFinite])
  · intro ω step hs
    simp only [cycleStepsOn, List.getElem?_ofFn, h0, dite_true, Option.some.injEq] at hs
    subst hs
    refine ⟨rfl, fun k hk => ?_⟩
    have hk' : k ∈ cycleKeys units ⟨0, h0⟩ := by simpa [lawZero] using hk
    show (if hx : k ∈ (lawZero units h0).KA ∪ (lawZero units h0).KB then
      (((splitZero units h0 (π ω)).1.2 ⟨k, hx⟩ : Fin (2 ^ 64)) : Nat) else 0) = native ⟨0, h0⟩ ω k
    simp only [hk, ↓reduceDIte]
    rw [hnative _ _ k hk']
    rfl

end
end RebuildBound.DirectJobUniformCycleProof

open RebuildBound.Spec RebuildBound.DirectJobUniformCycleProof in
theorem RebuildBound.DirectJobUniformCycleFirst : DirectJobUniformCycleFirst_statement := by
  intro n units capacity hcard _ _ Ω _ μ π hπ hμ native hnative h0
  exact digitOneFor units capacity μ π hπ hμ hcard native hnative h0
