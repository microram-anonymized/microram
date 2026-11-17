import RebuildBound.Spec.IdealProbe
import RebuildBound.Spec.IdealCapacity

/-! Reference correctness, exact simulation and the certified ideal capacity
budget share one arbitrary-key legal API execution. Observation transfer states
agreement off capacity failure explicitly; it does not assert native refinement. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online IdealHierarchy IdealDirect MeasureTheory
open scoped ENNReal

/-- One family endpoint exposes deterministic request correctness, exact probe
simulation and the finite-window capacity budget as separate conclusions. -/
def IdealApiFamily_statement : Prop :=
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
    let observe := fun tape => Adaptive.transcript geo.cfg geo.shapes g S a n
      (words tape) (dummy tape)
    (∀ tape, let qs := (ApiAdaptive.requestGroups compiled
        (Adaptive.rowsOf (observe tape) n) fs).flatMap PublicApi.Group.lanes
      ApiRunCorrect geo c g (Adaptive.realized geo.cfg geo.shapes g S a
        (words tape) (dummy tape)) S qs) ∧
    Measurable observe ∧
    IdealKey.tapeLaw.map observe =
      simLaw geo.cfg (OnlineBatch.slotSchedule (Adaptive.shapeWidths (ApiAdaptive.shape fs)) S)
        (Adaptive.shapePattern (ApiAdaptive.shape fs)) n m ∧
    IdealKey.tapeLaw {tape | Fails geo.cfg geo.shapes
      (trace geo.cfg geo.shapes g S a tape) (words tape)} ≤
      (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 64)

/-- Any measurable observation agreeing with an encoding of the reference
transcript off failure inherits the same eventwise simulator error. -/
def IdealApiOblivious_statement : Prop :=
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
    let reference := fun tape => Adaptive.transcript geo.cfg geo.shapes g S a n
      (words tape) (dummy tape)
    let simulator := simLaw geo.cfg
      (OnlineBatch.slotSchedule (Adaptive.shapeWidths (ApiAdaptive.shape fs)) S)
      (Adaptive.shapePattern (ApiAdaptive.shape fs)) n m
    ∀ (Value : Type) [MeasurableSpace Value]
      (observed : IdealKey.Tape → Value) (encode : (Fin n → Fin m → Nat) → Value),
    Measurable observed → Measurable encode →
    (∀ tape, ¬ Fails geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape) (words tape) →
      observed tape = encode (reference tape)) →
    ∀ event : Set Value, MeasurableSet event →
    IdealKey.tapeLaw (observed ⁻¹' event) ≤ simulator.map encode event +
        (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 64) ∧
      simulator.map encode event ≤ IdealKey.tapeLaw (observed ⁻¹' event) +
        (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 64)

/-- The same unconditional observation transfer after independent client
randomization. No common dictionary or supplied seedwise probability remains. -/
def IdealSeedOblivious_statement : Prop :=
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
    let reference := ApiSeed.transcript c geo.cfg geo.shapes g S init m width batches choose
    let bad := ApiSeed.failure c geo.cfg geo.shapes g S init m width batches choose
    let simulator := simLaw geo.cfg
      (OnlineBatch.slotSchedule (Adaptive.shapeWidths (ApiAdaptive.shape fs)) S)
      (Adaptive.shapePattern (ApiAdaptive.shape fs)) n m
    ∀ (Value : Type) [MeasurableSpace Value]
      (observed : Seed × IdealKey.Tape → Value) (encode : (Fin n → Fin m → Nat) → Value),
    Measurable observed → Measurable encode →
    (∀ p, p ∉ bad → observed p = encode (reference p.1 p.2)) →
    ∀ event : Set Value, MeasurableSet event →
    (μ.prod IdealKey.tapeLaw) (observed ⁻¹' event) ≤ simulator.map encode event +
        (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 64) ∧
      simulator.map encode event ≤ (μ.prod IdealKey.tapeLaw) (observed ⁻¹' event) +
        (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 64)

end RebuildBound.Spec
