import RebuildBound.Spec.IdealDirect
import RebuildBound.Spec.ConfigurationFamilyDirect

/-! Canonical direct-job bounds for the certified geometry family. The early
A event uses two adjacent routing families and includes reference overflow
continuations. All local laws are derived from the actual adaptive execution;
neither a finite key universe nor a supplied probability bound is a premise. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy IdealHierarchy IdealDirect MeasureTheory
open scoped ENNReal

/-- Unconditional early-A witnesses, including the old-tier fit required by
the analytic range bound. No earlier-success or horizon-membership premise
restricts this event. Both direct and DFS range plans are covered. -/
def IdealDirectA_statement : Prop :=
  ∀ (initialized : Bool) (member : ConfigurationFamily.Member),
    member ∈ ConfigurationFamily.members → ∀ horizon,
    let geo := (member.geometry initialized).chunk horizon
    ∀ g S m (a : Adaptive.AdaptiveRun m),
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 → 0 < g.unitEntries →
    SchedulePremises geo.cfg S (Adaptive.slotCount a.shape) m →
    ∀ ordinal, geo.cfg.seed 1 < ordinal → 2 ≤ geo.cfg.digitAt 1 ordinal →
    IdealKey.tapeLaw {tape |
      levelOneA (geo.shapes.direct (geo.cfg.digitAt 1 ordinal))
        (jobWord geo.cfg (words tape) 1 ordinal)
        (inputs geo.cfg geo.shapes g S a ordinal tape)} ≤
      ConfigurationFamily.directABound member (geo.cfg.digitAt 1 ordinal)

/-- Complete direct first-failure bound on the actual canonical tape. Public
requester widths supply all populations; initialization, live capacity and
key-domain assumptions are unnecessary for these level-one jobs. -/
def IdealDirectFirstFailure_statement : Prop :=
  ∀ (initialized : Bool) (member : ConfigurationFamily.Member),
    member ∈ ConfigurationFamily.members → ∀ horizon,
    let geo := (member.geometry initialized).chunk horizon
    ∀ g S m (a : Adaptive.AdaptiveRun m),
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 → 0 < g.unitEntries →
    SchedulePremises geo.cfg S (Adaptive.slotCount a.shape) m →
    ∀ ordinal, JobId.ordinary 1 ordinal ∈ geo.cfg.potentialJobs →
    IdealKey.tapeLaw {tape |
      JobFailsFirst geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape)
        (words tape) (.ordinary 1 ordinal)} ≤
      ConfigurationFamily.directBound member (geo.cfg.digitAt 1 ordinal)

end RebuildBound.Spec
