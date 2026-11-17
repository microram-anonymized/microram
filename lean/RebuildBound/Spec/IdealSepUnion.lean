import RebuildBound.Spec.IdealDirectFresh
import RebuildBound.Spec.ConfigurationFamily
import RebuildBound.Spec.AdaptiveStepsJobs

/-! The separated current-home union term on the actual adaptive canonical
 tape. Only the finite key populations are fixed by the late outside section;
 the lower carry's physical layout may depend on the current family. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy IdealHierarchy IdealDirect MeasureTheory
open scoped ENNReal

/-- The unconditional union overflow witness for every certified separated
row, including reference continuations after earlier overflow. Public requester
widths supply the populations; no key universe, initialization bound, live
capacity, flag promise or supplied probability estimate is required. This is
the union term only; the early-A term remains a separate obligation. -/
def IdealSepUnion_statement : Prop :=
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
      min (row.stashPages * row.C) (row.tierPages * row.C) <
        sHomeExcess row (jobWord geo.cfg (words tape) level ordinal)
          (sepInputsAt geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape)
            (words tape) level ordinal)} ≤ selSepUBound row

end RebuildBound.Spec
