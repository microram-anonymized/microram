import RebuildBound.Spec.AdaptiveStepsJobs

/-! Geometry-parametric causal capacity interface. Local applicability and
numerical exposure budgets are established separately by its providers. -/
open MeasureTheory
open scoped ENNReal
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.Adaptive

/-- A realized adaptive trace is a causal function of the joint tape. -/
def AdaptiveCausalFor (geo : HierarchyGeometry) : Prop :=
  ∀ N g m (a : AdaptiveRun m) S n, AdaptiveNumericSetting geo N g a S n →
    ∃ T : FamilyTape geo.cfg N × DummyTape n m → Trace,
      CausalSetting geo N n m T ∧
      ∀ (words : Words) (x : FamilyTape geo.cfg N × DummyTape n m),
        (∀ (p : Coord geo.cfg) (k : LogicalKey) (hk : k.toNat < N), words p.1.1 p.1.2 k = x.1 p ⟨k, hk⟩) →
        OnlineBatch.traceOf g (realized geo.cfg geo.shapes g S a words (dummyOf x.2)) = T x

def CausalWindowsFor (geo : HierarchyGeometry) (error : ℝ≥0∞) : Prop :=
  ∀ h, 1 ≤ h → CausalBound (geo.chunk h) fun μ tr words =>
    μ {ω | Fails (geo.chunk h).cfg (geo.chunk h).shapes (tr ω) (words ω)} ≤
      (h : ℝ≥0∞) * error

end RebuildBound.Spec
