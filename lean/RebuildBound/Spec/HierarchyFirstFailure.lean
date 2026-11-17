import RebuildBound.Spec.HierarchyGeometry.Interfaces

/-! First-failure events and generic finite-window probability composition.
The event is unconditional; survival only locates its earliest failing job. -/

open MeasureTheory
open scoped ENNReal
namespace RebuildBound.Spec
open Model Model.Hierarchy

/-- A potential job's first-failure event: within the horizon, its input
tiers fit and it fails on its reference inputs; at level one, the earlier
ordinals of its cycle do not fail. Above level one it is `jobEvent`'s
condition. -/
def JobFailsFirst (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (j : JobId) : Prop :=
  WithinHorizon cfg j ∧ jobTiersFit cfg sh tr words j ∧ jobFails cfg sh tr words j = true ∧
    ∀ o, j = .ordinary 1 o → ∀ i, 0 < i → i < cfg.digitAt 1 o →
      jobFails cfg sh tr words (.ordinary 1 (o - i)) = false

/-- Pointwise first-failure covering at one geometry and horizon. -/
def HierarchyFirstFailureFor (geo : HierarchyGeometry) : Prop :=
  ∀ (tr : Trace) (words : Words), Fails geo.cfg geo.shapes tr words →
    ∃ j ∈ geo.cfg.potentialJobs, JobFailsFirst geo.cfg geo.shapes tr words j

/-- The first-failure covering at every positive chunk horizon. -/
def HierarchyFirstFailureChunksFor (geo : HierarchyGeometry) : Prop :=
  ∀ h, 1 ≤ h → HierarchyFirstFailureFor (geo.chunk h)

/-- Unconditional per-job first-failure estimates compose using the actual
class exposure counts. Traces may depend on the randomness; their probability
applicability must be established separately for fixed and adaptive clients. -/
def HierarchyProbabilityFor (geo : HierarchyGeometry) : Prop :=
  ∀ (b : JobClass → ℝ≥0∞) (h : Nat), 1 ≤ h →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tr : Ω → Trace) (words : Ω → Words),
      (∀ j ∈ (geo.chunk h).cfg.potentialJobs,
        μ {ω | JobFailsFirst (geo.chunk h).cfg (geo.chunk h).shapes (tr ω) (words ω) j} ≤
          b (geo.cfg.classOf j)) →
      μ {ω | Fails (geo.chunk h).cfg (geo.chunk h).shapes (tr ω) (words ω)} ≤
        (h : ℝ≥0∞) * geo.cfg.exposureSum b

end RebuildBound.Spec
