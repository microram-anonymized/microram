import RebuildBound.Proofs.AdaptiveTop.Cell

/-! Initialization under a causal trace has a fixed input. Its unconditional
source law is independent of concrete numerical certificates. -/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.AdaptiveTopProof
open Model Model.Hierarchy Spec FiniteCouplingProof

/-- The initialization's first-failure event on a causal trace, at most the
initialization budget `i`. -/
theorem init_bound (geo : HierarchyGeometry) (hTopLaw : HierarchyTopLawFor geo)
    (hTP : TracePrefix_statement) (i : ℝ≥0∞)
    (hInit : ∀ (L : TPJobLaw geo.init) (input : List Rec), InitLaw L input →
      L.prob (tpFailEvent L engineRule fun _ => false) ≤ i)
    {N n m : Nat} {T : FamilyTape geo.cfg N × DummyTape n m → Trace}
    (hS : CausalSetting geo N n m T)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (tape : Ω → FamilyTape geo.cfg N) (dtape : Ω → DummyTape n m) (words : Ω → Words)
    (hOT : OnlineTapePremises geo.cfg N n m μ tape dtape words)
    (hj : JobId.initialization ∈ geo.cfg.potentialJobs) :
    μ {ω | JobFailsFirst geo.cfg geo.shapes (T (tape ω, dtape ω)) (words ω) .initialization} ≤ i := by
  let x0 : FamilyTape geo.cfg N × DummyTape n m := (fun _ _ => zeroWord, fun _ _ => zeroWord)
  obtain ⟨-, -, h3⟩ := hTopLaw N (T x0) hS.1 (hS.2.2 x0).1 (hS.2.2 x0).2 μ tape words
    (OnlineObliviousAssemblyProof.family_tape hOT)
  obtain ⟨L, input, sample, hL, hc, hsub⟩ := h3 hj
  refine le_trans (finite_transport_sub μ L.toFinite sample hc _ _ fun ω hω => hsub ?_)
    (hInit L input hL)
  exact init_event hTP geo.shapes hS.2.1 (tape ω, dtape ω) x0 (words ω) hj hω

end RebuildBound.AdaptiveTopProof

