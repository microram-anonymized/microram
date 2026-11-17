import RebuildBound.Proofs.HierarchyProbability
import RebuildBound.Proofs.HierarchyLevelOne.Uniform
import RebuildBound.Spec.HierarchyProbability

/-! A fixed trace is a constant causal trace. An empty dummy tape transports
its family-tape law into the same joint-tape interface, so fixed and adaptive
capacity bounds can share one probability assembly. -/
open MeasureTheory
open scoped ENNReal
namespace RebuildBound.HierarchyProbabilityProof
open Model Model.Hierarchy Spec

/-- Specialize any causal probability claim to a fixed trace, retaining the
original family-tape premises and introducing no extra randomness. -/
theorem fixed_of_causal (geo : HierarchyGeometry)
    (claim : ∀ {Ω : Type} [MeasurableSpace Ω], Measure Ω → (Ω → Trace) → (Ω → Words) → Prop)
    (hC : CausalBound geo claim)
    (N : Nat) (tr : Trace) (hN : N ≤ geo.keyCapacity)
    (hTr : TracePremises geo.cfg N tr) (hU : UnshPromise geo.cfg geo.shapes tr)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (tape : Ω → FamilyTape geo.cfg N) (words : Ω → Words)
    (ht : TapePremises geo.cfg N μ tape words) : claim μ (fun _ => tr) words := by
  let e := (Equiv.prodUnique (FamilyTape geo.cfg N) (DummyTape 0 0)).symm
  have hu : (ProbabilityTheory.uniformOn (Set.univ : Set (FamilyTape geo.cfg N))).map e =
      ProbabilityTheory.uniformOn (Set.univ : Set (FamilyTape geo.cfg N × DummyTape 0 0)) :=
    HierarchyLevelOneProof.map_uniform_of_split
      (e.trans (Equiv.prodPUnit (FamilyTape geo.cfg N × DummyTape 0 0)).symm) e (fun _ => rfl)
  have hOT : OnlineTapePremises geo.cfg N 0 0 μ tape (fun _ => default) words :=
    { measurable := ht.measurable.prodMk measurable_const
      uniform := by
        have he : (fun ω => (tape ω, (default : DummyTape 0 0))) = e ∘ tape := by
          funext ω
          apply Prod.ext
          · rfl
          · exact Subsingleton.elim _ _
        rw [he]
        rw [← Measure.map_map Measurable.of_discrete ht.measurable, ht.uniform]
        exact hu
      agree := ht.agree }
  have hs : CausalSetting geo N 0 0 (fun _ => tr) :=
    ⟨hN, ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ _ _ _ => rfl⟩, fun _ => ⟨hTr, hU⟩⟩
  exact hC N 0 0 (fun _ => tr) hs μ tape (fun _ => default) words hOT

/-- Fixed-run windows use the same class budgets and composition as causal runs. -/
theorem windows_of_causal (geo : HierarchyGeometry) (error : ℝ≥0∞)
    (hC : CausalWindowsFor geo error) : HierarchyWindowsFor geo error := by
  intro h N tr hh hN hTr hU Ω _ μ _ tape words ht
  exact fixed_of_causal (geo.chunk h) _ (hC h hh) N tr hN hTr hU μ tape words ht

end RebuildBound.HierarchyProbabilityProof
