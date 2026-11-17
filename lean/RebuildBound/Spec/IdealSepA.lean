import RebuildBound.Spec.IdealSepUnion

/-! Canonical separated early-A and complete first-failure bounds. Adjacent
routing families supply the old-home density; the same byte key uses one word
in each family, including forwarded families and reference continuations. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.DirectJob IdealHierarchy IdealDirect MeasureTheory
open scoped ENNReal

/-- Unconditional separated A route and range witnesses for every certified
row and both starts. Populations and joint old-home laws come from execution;
no key universe, live capacity, flag promise, or earlier-success premise is
required. The current B layout may still depend on the fresh family. -/
def IdealSepA_statement : Prop :=
  ∀ (initialized : Bool) (member : ConfigurationFamily.Member),
    member ∈ ConfigurationFamily.members → ∀ horizon,
    let geo := (member.geometry initialized).chunk horizon
    ∀ g S m (a : Adaptive.AdaptiveRun m),
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 → 0 < g.unitEntries →
    SchedulePremises geo.cfg S (Adaptive.slotCount a.shape) m →
    ∀ level ordinal (row : SepGeom),
    JobId.ordinary level ordinal ∈ geo.cfg.potentialJobs → 2 ≤ level →
    2 ≤ geo.cfg.digitAt level ordinal →
    geo.cfg.sepRow geo.rows level (geo.cfg.digitAt level ordinal) = some row →
    IdealKey.tapeLaw {tape |
      sharedARouteWitness row (jobWord geo.cfg (words tape) level (ordinal - 1))
          (jobWord geo.cfg (words tape) level ordinal)
          (sepInputsAt geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape)
            (words tape) level ordinal) ∨
        sharedARangeWitness row (jobWord geo.cfg (words tape) level ordinal)
          (sepInputsAt geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape)
            (words tape) level ordinal)} ≤ selSepABound row

/-- Complete separated first-failure bound on the actual adaptive tape.
The A and union sections reuse the existing analytic budget for each row. -/
def IdealSepFirstFailure_statement : Prop :=
  ∀ (initialized : Bool) (member : ConfigurationFamily.Member),
    member ∈ ConfigurationFamily.members → ∀ horizon,
    let geo := (member.geometry initialized).chunk horizon
    ∀ g S m (a : Adaptive.AdaptiveRun m),
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 → 0 < g.unitEntries →
    SchedulePremises geo.cfg S (Adaptive.slotCount a.shape) m →
    ∀ level ordinal (row : SepGeom),
    JobId.ordinary level ordinal ∈ geo.cfg.potentialJobs → 2 ≤ level →
    geo.cfg.sepRow geo.rows level (geo.cfg.digitAt level ordinal) = some row →
    IdealKey.tapeLaw {tape |
      JobFailsFirst geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape)
        (words tape) (.ordinary level ordinal)} ≤ selSepBound row

end RebuildBound.Spec
