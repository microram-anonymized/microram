import RebuildBound.Spec.HierarchyProbability
import RebuildBound.Spec.AdaptiveStepsAssembly

/-! The existing causal realized-trace proof transports a geometry-parametric
window bound to clients whose future requests depend on observed buckets. -/
open MeasureTheory
open scoped ENNReal
namespace RebuildBound.AdaptiveAssembly
open Spec Model Model.Hierarchy Model.Online Model.Adaptive

/-- Capacity transfer from a causal trace to an adaptive client. Geometry and
semantic laws stay separate from the numerical error budget. -/
theorem numericFor (geo : HierarchyGeometry) (error : ℝ≥0∞)
    (hC : ∀ h, 1 ≤ h → AdaptiveCausalFor (geo.chunk h))
    (hW : CausalWindowsFor geo error) : AdaptiveNumericWindowsFor geo error := by
  intro h hh
  dsimp only
  intro N g m a S n hset Ω _ μ _ tape dtape words hT
  obtain ⟨T, hTs, hTeq⟩ := hC h hh N g m a S n hset
  have hb := hW h hh N n m T hTs μ tape dtape words hT
  refine le_trans (measure_mono ?_) hb
  intro ω hω
  have he := hTeq (words ω) (tape ω, dtape ω) (fun p k hk => hT.agree ω p k hk)
  change Fails (geo.chunk h).cfg (geo.chunk h).shapes
    (OnlineBatch.traceOf g (realized (geo.chunk h).cfg (geo.chunk h).shapes g S a
      (words ω) (dummyOf (dtape ω)))) (words ω) at hω
  rw [he] at hω
  exact hω

end RebuildBound.AdaptiveAssembly
