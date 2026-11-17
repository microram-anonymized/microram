import RebuildBound.Spec.ApiSeed
import RebuildBound.Spec.HierarchyStructure

/-! Exact reference probe simulation on the canonical routing/dummy tape.
The public simulator uses only the schedule and batch shape. Neither logical
live capacity nor a common key dictionary is needed for the exact law. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online MeasureTheory IdealHierarchy

/-- A fixed supplied-record run has the public simulator law. Its flag promise
is explicit; the API endpoint below derives that promise from requests. -/
def IdealBatchExact_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.LowerCompatible →
    ∀ g (run : OnlineBatch.BatchRun) S n m,
    (run.init.map Rec.key).Nodup →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → (OnlineBatch.slots run).length ≤ geo.cfg.horizon →
    n ≤ (OnlineBatch.slots run).length →
    UnshPromise geo.cfg geo.shapes (OnlineBatch.traceOf g run) →
    SchedulePremises geo.cfg S n m →
    Measurable (fun tape => OnlineBatch.view geo.cfg geo.shapes g run S n m
      (words tape) (dummy tape)) ∧
    IdealKey.tapeLaw.map (fun tape => OnlineBatch.view geo.cfg geo.shapes g run S n m
      (words tape) (dummy tape)) =
      simLaw geo.cfg (OnlineBatch.slotSchedule (OnlineBatch.widths run) S)
        (OnlineBatch.probePattern run) n m

/-- Each replay branch may introduce entirely different arbitrary byte keys.
Only the supplied-record flag promise is quantified over those branches. -/
def IdealAdaptiveExact_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.LowerCompatible →
    ∀ g S m (a : Adaptive.AdaptiveRun m),
    let n := Adaptive.slotCount a.shape
    (a.init.map Rec.key).Nodup →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → n ≤ geo.cfg.horizon →
    (∀ t : Fin n → Fin m → Nat,
      UnshPromise geo.cfg geo.shapes (OnlineBatch.traceOf g (Adaptive.replay a t))) →
    SchedulePremises geo.cfg S n m →
    Measurable (fun tape => Adaptive.transcript geo.cfg geo.shapes g S a n
      (words tape) (dummy tape)) ∧
    IdealKey.tapeLaw.map (fun tape => Adaptive.transcript geo.cfg geo.shapes g S a n
      (words tape) (dummy tape)) =
      simLaw geo.cfg (OnlineBatch.slotSchedule (Adaptive.shapeWidths a.shape) S)
        (Adaptive.shapePattern a.shape) n m

/-- Legal API clients acquire exact simulation from initialization and public
execution validity. No probability, flag, live-capacity or success premise is supplied. -/
def IdealApiExact_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.Structural →
    ∀ (c : Api.Codec) g S init m width batches,
    let fs := ApiAdaptive.frames width g.unitEntries batches
    ∀ choose : ApiLegal.Chooser geo.cfg (ApiAdaptive.shape fs) S m,
    let n := Adaptive.slotCount (ApiAdaptive.shape fs)
    (geo.cfg.initialized = false → init = []) →
    (init.map Rec.key).Nodup → init.length ≤ geo.init.C / 2 * geo.init.T →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → n ≤ geo.cfg.horizon → SchedulePremises geo.cfg S n m →
    let a := ApiAdaptive.run c geo.cfg geo.shapes g S init fs
      (ApiLegal.adapt geo.cfg (ApiAdaptive.shape fs) S choose)
    Measurable (fun tape => Adaptive.transcript geo.cfg geo.shapes g S a n
      (words tape) (dummy tape)) ∧
    IdealKey.tapeLaw.map (fun tape => Adaptive.transcript geo.cfg geo.shapes g S a n
      (words tape) (dummy tape)) =
      simLaw geo.cfg (OnlineBatch.slotSchedule (Adaptive.shapeWidths (ApiAdaptive.shape fs)) S)
        (Adaptive.shapePattern (ApiAdaptive.shape fs)) n m

/-- Independent countable seeds with unbounded support preserve the exact law.
The joint conclusion makes the reference transcript independent of the seed. -/
def IdealApiSeedExact_statement : Prop :=
  ∀ (Seed : Type) [MeasurableSpace Seed] [Countable Seed] [MeasurableSingletonClass Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (geo : HierarchyGeometry), geo.Structural →
    ∀ (c : Api.Codec) g S (init : Seed → List Rec) m width batches,
    let fs := ApiAdaptive.frames width g.unitEntries batches
    ∀ choose : Seed → ApiLegal.Chooser geo.cfg (ApiAdaptive.shape fs) S m,
    let n := Adaptive.slotCount (ApiAdaptive.shape fs)
    (∀ seed, geo.cfg.initialized = false → init seed = []) →
    (∀ seed, ((init seed).map Rec.key).Nodup) →
    (∀ seed, (init seed).length ≤ geo.init.C / 2 * geo.init.T) →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → n ≤ geo.cfg.horizon → SchedulePremises geo.cfg S n m →
    let observe := ApiSeed.transcript c geo.cfg geo.shapes g S init m width batches choose
    let simulator := simLaw geo.cfg
      (OnlineBatch.slotSchedule (Adaptive.shapeWidths (ApiAdaptive.shape fs)) S)
      (Adaptive.shapePattern (ApiAdaptive.shape fs)) n m
    Measurable (Function.uncurry observe) ∧
    (μ.prod IdealKey.tapeLaw).map (fun p => (p.1, observe p.1 p.2)) = μ.prod simulator ∧
    (μ.prod IdealKey.tapeLaw).map (Function.uncurry observe) = simulator

end RebuildBound.Spec
