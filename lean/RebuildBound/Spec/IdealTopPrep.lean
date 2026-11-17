import RebuildBound.Spec.ApiLegal
import RebuildBound.Spec.IdealDirect
import RebuildBound.Spec.TopPrepG
import RebuildBound.Spec.ConfigurationFamilyData
import RebuildBound.Spec.HierarchyFirstFailure

/-! Top preparation on the canonical tape for legal adaptive API clients.
Logical prefix capacity supplies the population; the two routing families
remain independent even when earlier observations determine new byte keys. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online IdealHierarchy IdealDirect MeasureTheory
open scoped ENNReal

/-- The actual top-preparation contribution has its analytic bound. The event
includes old-tier fit, without conditioning the reference run on earlier success.
Storage admissibility concerns initialization and logical live capacity. -/
def IdealTopPreparation_statement : Prop :=
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
    ∀ K1 K2, geo.prep.k ≤ 64 → (geo.prep.dfs = true → geo.prep.I + 1 < geo.prep.k) →
    geo.prep.stashPages * geo.prep.C < K1 → geo.prep.drainPages * geo.prep.C < K2 →
    ∀ ordinal, JobId.topPrepare ordinal ∈ geo.cfg.potentialJobs →
    let a := ApiAdaptive.run c geo.cfg geo.shapes g S init fs compiled
    IdealKey.tapeLaw {tape |
      TPTiersFit geo.prep (prepInputsAt geo.cfg geo.shapes
        (trace geo.cfg geo.shapes g S a tape) (words tape) ordinal) ∧
      (prepResult geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape)
        (words tape) ordinal).toBool = false} ≤ tpBound geo.prep 32 1 K1 K2

/-- Every certified geometry and both starts inherit the complete preparation
first-failure bound. No supplied job load, key universe, numeric key encoding,
freshness law, or successful-execution premise occurs. -/
def IdealTopPreparationFirstFailure_statement : Prop :=
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
    ∀ ordinal, JobId.topPrepare ordinal ∈ geo.cfg.potentialJobs →
    let a := ApiAdaptive.run c geo.cfg geo.shapes g S init fs compiled
    IdealKey.tapeLaw {tape | JobFailsFirst geo.cfg geo.shapes
      (trace geo.cfg geo.shapes g S a tape) (words tape) (.topPrepare ordinal)} ≤
        tpBound geo.prep 32 1 576 576

end RebuildBound.Spec
