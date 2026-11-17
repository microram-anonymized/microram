import RebuildBound.Spec.HierarchyGeometry.Interfaces
import RebuildBound.Spec.Oblivious
import RebuildBound.Proofs.HierarchyHorizonTransfer

/-!
# Generic numerical online obliviousness

Combine exact observation transfer with a geometry-specific window bound.
The family marginal of the joint ideal tape supplies `TapePremises`.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online

namespace OnlineObliviousAssemblyProof

/-- The family marginal of the joint ideal tape is a uniform family tape. -/
theorem family_tape {cfg : Config} {N n m : Nat} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} {tape : Ω → FamilyTape cfg N} {dtape : Ω → DummyTape n m}
    {words : Ω → Words} (hT : OnlineTapePremises cfg N n m μ tape dtape words) :
    TapePremises cfg N μ tape words := by
  classical
  refine ⟨measurable_fst.comp hT.measurable, ?_, hT.agree⟩
  have e : tape = Prod.fst ∘ (fun ω => (tape ω, dtape ω)) := rfl
  rw [e, ← Measure.map_map Measurable.of_discrete hT.measurable, hT.uniform]
  exact HierarchyLevelOneProof.map_uniform_of_split (Equiv.refl _) Prod.fst (fun _ => rfl)

/-- Natural chunk counts scale the real-valued power-of-two error budget. -/
theorem chunk_error_eq (h bits : Nat) :
    (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ bits) =
      ENNReal.ofReal ((h : ℝ) / 2 ^ bits) := by
  rw [div_eq_mul_one_div (h : ℝ), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_natCast]

/-- The failure probability at a chunk horizon for explicit geometry. -/
theorem fails_leFor (geo : HierarchyGeometry) (error : ℝ≥0∞)
    (hWin : HierarchyWindowsFor geo error) (h : Nat) (hh : 1 ≤ h) (N : Nat) (tr : Trace)
    (hN : N ≤ geo.keyCapacity) (hTr : TracePremises (chunkConfig geo.cfg h) N tr)
    (hUnsh : UnshPromise (chunkConfig geo.cfg h) (geo.chunk h).shapes tr)
    {n m : Nat} {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (tape : Ω → FamilyTape (chunkConfig geo.cfg h) N) (dtape : Ω → DummyTape n m)
    (words : Ω → Words)
    (hT : OnlineTapePremises (chunkConfig geo.cfg h) N n m μ tape dtape words) :
    μ {ω | Fails (chunkConfig geo.cfg h) (geo.chunk h).shapes tr (words ω)} ≤
      (h : ℝ≥0∞) * error :=
  hWin h N tr hh hN hTr hUnsh μ tape words (family_tape hT)

/-- Numerical obliviousness from exact observation transfer and a hierarchy window bound. -/
theorem obliviousFor (geo : HierarchyGeometry) (error : ℝ≥0∞)
    (hWin : HierarchyWindowsFor geo error)
    (hFail : ∀ h, 1 ≤ h → OnlineFailureFor (geo.chunk h)) :
    OnlineObliviousFor geo error := by
  intro h hh
  dsimp only
  intro N g run S n m hset Ω _ μ _ tape dtape words hT V _ obs ι hobs hι hagree A hA
  have hb := fails_leFor geo error hWin h hh N (traceOf g run) hset.1 hset.2.2.1.trace
    hset.2.2.1.unsh μ tape dtape words hT
  obtain ⟨h1, h2⟩ := hFail h hh N g run S n m hset μ tape dtape words hT obs ι hobs hι hagree A hA
  exact ⟨h1.trans (add_le_add le_rfl hb), h2.trans (add_le_add le_rfl hb)⟩

end OnlineObliviousAssemblyProof

end RebuildBound
