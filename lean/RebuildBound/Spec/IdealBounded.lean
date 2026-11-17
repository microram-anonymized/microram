import RebuildBound.Spec.ApiBounded
import RebuildBound.Spec.IdealCapacity

/-! Conditional bounded API correctness on the canonical tape for all certified
geometries and both starts. Concrete adapter agreement is explicit. These bounds
charge the actual reference capacity event without conditioning on success. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online IdealHierarchy IdealDirect MeasureTheory
open scoped ENNReal

/-- An agreeing adapter inherits correct logical prefixes, scalar/batch replies
and probing addresses, with incorrect-result outer measure at most h * 2^-64
over h ≥ 1 windows of 2^32 accesses. -/
def IdealApiBounded_statement : Prop :=
  ∀ (initialized : Bool) (member : ConfigurationFamily.Member),
    member ∈ ConfigurationFamily.members → ∀ h, 1 ≤ h →
    let geo := (member.geometry initialized).chunk h
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
    let a := ApiAdaptive.run c geo.cfg geo.shapes g S init fs compiled
    ∀ (runs : IdealKey.Tape → OnlineBatch.BatchRun)
      (requests : IdealKey.Tape → List Api.Request)
      (actual : IdealKey.Tape → Nat → Probe.Result),
    (∀ tape, ApiBoundedAgreement geo c g S m width batches init choose
      (words tape) (dummy tape) (runs tape) (requests tape) (actual tape)) →
    (∀ tape, ¬ Fails geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape) (words tape) →
      ApiResultsCorrect geo c g (runs tape) S n (words tape) (dummy tape)
        (requests tape) (actual tape)) ∧
    IdealKey.tapeLaw {tape | ¬ ApiResultsCorrect geo c g (runs tape) S n
      (words tape) (dummy tape) (requests tape) (actual tape)} ≤
        (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 64)

/-- The same bound for independent countable private seeds, including
seed-dependent initialization and no common dictionary across seeds. -/
def IdealSeedBounded_statement : Prop :=
  ∀ (Seed : Type) [MeasurableSpace Seed] [Countable Seed] [MeasurableSingletonClass Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (initialized : Bool) (member : ConfigurationFamily.Member),
    member ∈ ConfigurationFamily.members → ∀ h, 1 ≤ h →
    let geo := (member.geometry initialized).chunk h
    ∀ (c : Api.Codec) g S (init : Seed → List Rec) m width batches,
    let fs := ApiAdaptive.frames width g.unitEntries batches
    let n := Adaptive.slotCount (ApiAdaptive.shape fs)
    ∀ choose : Seed → ApiLegal.Chooser geo.cfg (ApiAdaptive.shape fs) S m,
    (∀ seed, ApiCapacity.InitialStateValid geo.keyCapacity geo.cfg.initialized (init seed)) →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → n ≤ geo.cfg.horizon → SchedulePremises geo.cfg S n m →
    (∀ seed (t : ApiLegal.Prefix geo.cfg (ApiAdaptive.shape fs) S m n),
      ApiCapacity.LiveCapacity geo.keyCapacity (Api.stateOf c (init seed)) ((init seed).map Rec.key)
        ((ApiAdaptive.requestGroups (ApiLegal.adapt geo.cfg (ApiAdaptive.shape fs) S (choose seed))
          (Adaptive.rowsOf (ApiLegal.erase t) n) fs).flatMap PublicApi.Group.lanes)) →
    ∀ (runs : Seed × IdealKey.Tape → OnlineBatch.BatchRun)
      (requests : Seed × IdealKey.Tape → List Api.Request)
      (actual : Seed × IdealKey.Tape → Nat → Probe.Result),
    (∀ p, ApiBoundedAgreement geo c g S m width batches (init p.1) (choose p.1)
      (words p.2) (dummy p.2) (runs p) (requests p) (actual p)) →
    let bad := ApiSeed.failure c geo.cfg geo.shapes g S init m width batches choose
    (∀ p, p ∉ bad → ApiResultsCorrect geo c g (runs p) S n
      (words p.2) (dummy p.2) (requests p) (actual p)) ∧
    (μ.prod IdealKey.tapeLaw) {p | ¬ ApiResultsCorrect geo c g (runs p) S n
      (words p.2) (dummy p.2) (requests p) (actual p)} ≤
        (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 64)

end RebuildBound.Spec
