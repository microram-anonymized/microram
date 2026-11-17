import RebuildBound.Spec.ApiLegal
import RebuildBound.Spec.IdealDirect
import RebuildBound.Spec.G3
import RebuildBound.Spec.ConfigurationFamilyData
import RebuildBound.Spec.HierarchyFirstFailure

/-! Top finish on the canonical tape for legal adaptive API clients.
Logical prefix capacity supplies the population; the current routing family
remains fresh even when earlier observations determine new byte keys. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online IdealHierarchy IdealDirect MeasureTheory
open scoped ENNReal

/-- The actual top-finish contribution has its analytic bound. The event
includes input-tier fit, without conditioning the reference run on earlier success.
Storage admissibility concerns initialization and logical live capacity. -/
def IdealTopFinish_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.Structural →
    ∀ (c : Api.Codec) g S init m width batches,
    let fs := ApiAdaptive.frames width g.unitEntries batches
    ∀ choose : ApiLegal.Chooser geo.cfg (ApiAdaptive.shape fs) S m,
    let n := Adaptive.slotCount (ApiAdaptive.shape fs)
    let compiled := ApiLegal.adapt geo.cfg (ApiAdaptive.shape fs) S choose
    ApiCapacity.InitialStateValid geo.keyCapacity geo.cfg.initialized init →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → n ≤ geo.cfg.horizon → SchedulePremises geo.cfg S n m →
    (∀ t : ApiLegal.Prefix geo.cfg (ApiAdaptive.shape fs) S m n,
      ApiCapacity.LiveCapacity geo.keyCapacity (Api.stateOf c init) (init.map Rec.key)
        ((ApiAdaptive.requestGroups compiled (Adaptive.rowsOf (ApiLegal.erase t) n) fs).flatMap
          PublicApi.Group.lanes)) →
    ∀ K1 K2, geo.top.k + geo.top.e ≤ 64 →
    geo.top.C < K1 → min geo.top.SMerge geo.top.STier < K2 →
    ∀ ordinal, JobId.topFinish ordinal ∈ geo.cfg.potentialJobs →
    let a := ApiAdaptive.run c geo.cfg geo.shapes g S init fs compiled
    IdealKey.tapeLaw {tape |
      TopTiersFit geo.top (finishInputsAt geo.cfg geo.shapes
        (trace geo.cfg geo.shapes g S a tape) (words tape) ordinal) ∧
      (finishResult geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape)
        (words tape) ordinal).toBool = false} ≤
      ENNReal.ofReal (topFinishBound geo.top.C geo.top.SR geo.top.rho geo.top.I geo.top.T
        (min geo.top.SMerge geo.top.STier) K1 K2 32)

/-- Every certified geometry and both starts inherit the complete finish
first-failure bound. No supplied job load, key universe, numeric key encoding,
freshness law, or successful-execution premise occurs. -/
def IdealTopFinishFirstFailure_statement : Prop :=
  ∀ (initialized : Bool) (member : ConfigurationFamily.Member),
    member ∈ ConfigurationFamily.members → ∀ horizon,
    let geo := (member.geometry initialized).chunk horizon
    ∀ (c : Api.Codec) g S init m width batches,
    let fs := ApiAdaptive.frames width g.unitEntries batches
    ∀ choose : ApiLegal.Chooser geo.cfg (ApiAdaptive.shape fs) S m,
    let n := Adaptive.slotCount (ApiAdaptive.shape fs)
    let compiled := ApiLegal.adapt geo.cfg (ApiAdaptive.shape fs) S choose
    ApiCapacity.InitialStateValid geo.keyCapacity geo.cfg.initialized init →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → n ≤ geo.cfg.horizon → SchedulePremises geo.cfg S n m →
    (∀ t : ApiLegal.Prefix geo.cfg (ApiAdaptive.shape fs) S m n,
      ApiCapacity.LiveCapacity geo.keyCapacity (Api.stateOf c init) (init.map Rec.key)
        ((ApiAdaptive.requestGroups compiled (Adaptive.rowsOf (ApiLegal.erase t) n) fs).flatMap
          PublicApi.Group.lanes)) →
    ∀ ordinal, JobId.topFinish ordinal ∈ geo.cfg.potentialJobs →
    let a := ApiAdaptive.run c geo.cfg geo.shapes g S init fs compiled
    IdealKey.tapeLaw {tape | JobFailsFirst geo.cfg geo.shapes
      (trace geo.cfg geo.shapes g S a tape) (words tape) (.topFinish ordinal)} ≤
        ENNReal.ofReal (topFinishBound geo.top.C geo.top.SR geo.top.rho geo.top.I geo.top.T
          (min geo.top.SMerge geo.top.STier) 576 576 32)

end RebuildBound.Spec
