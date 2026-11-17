import RebuildBound.Spec.ApiLegal
import RebuildBound.Spec.IdealMeasurable
import RebuildBound.Spec.IdealSeed
import RebuildBound.Spec.IdealFailure

/-! Seeded legal API clients share public geometry, schedule and batch shape.
Their initial maps and arbitrary request choices can depend on the private
seed. Countable seeds may have unbounded support. The engine still stores
exact logical byte keys throughout records, requests and routing. -/
namespace RebuildBound.Spec.ApiSeed
open Model Model.Hierarchy Model.Online

/-- The existing request-derived engine, instantiated at one fixed seed. -/
def run {Seed : Type} (c : Api.Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (S : Schedule) (init : Seed → List Rec) (m width : Nat) (batches : List ApiAdaptive.Batch)
    (choose : Seed → ApiLegal.Chooser cfg
      (ApiAdaptive.shape (ApiAdaptive.frames width g.unitEntries batches)) S m)
    (seed : Seed) : Adaptive.AdaptiveRun m :=
  let fs := ApiAdaptive.frames width g.unitEntries batches
  ApiAdaptive.run c cfg sh g S (init seed) fs
    (ApiLegal.adapt cfg (ApiAdaptive.shape fs) S (choose seed))

def transcript {Seed : Type} (c : Api.Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (S : Schedule) (init : Seed → List Rec) (m width : Nat) (batches : List ApiAdaptive.Batch)
    (choose : Seed → ApiLegal.Chooser cfg
      (ApiAdaptive.shape (ApiAdaptive.frames width g.unitEntries batches)) S m)
    (seed : Seed) (tape : IdealKey.Tape) :
    Fin (Adaptive.slotCount (ApiAdaptive.shape (ApiAdaptive.frames width g.unitEntries batches))) →
      Fin m → Nat :=
  Adaptive.transcript cfg sh g S (run c cfg sh g S init m width batches choose seed)
    (Adaptive.slotCount (ApiAdaptive.shape (ApiAdaptive.frames width g.unitEntries batches)))
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)

/-- Capacity failure of the actual request-derived adaptive run, including its
unconditional reference inputs and the configured public horizon. -/
def failure {Seed : Type} (c : Api.Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (S : Schedule) (init : Seed → List Rec) (m width : Nat) (batches : List ApiAdaptive.Batch)
    (choose : Seed → ApiLegal.Chooser cfg
      (ApiAdaptive.shape (ApiAdaptive.frames width g.unitEntries batches)) S m) :
    Set (Seed × IdealKey.Tape) :=
  {p | Fails cfg sh (OnlineBatch.traceOf g (Adaptive.realized cfg sh g S
      (run c cfg sh g S init m width batches choose p.1)
      (IdealHierarchy.words p.2) (IdealHierarchy.dummy p.2))) (IdealHierarchy.words p.2)}

end RebuildBound.Spec.ApiSeed

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online MeasureTheory
open scoped ENNReal

/-- Measurability is derived for the actual seeded API execution, including
seed-dependent initialization. No measurable-execution premise is assumed. -/
def ApiSeedMeasurable_statement : Prop :=
  ∀ (Seed : Type) [MeasurableSpace Seed] [Countable Seed] [MeasurableSingletonClass Seed]
    c cfg sh g S (init : Seed → List Rec) m width batches choose,
    Measurable (Function.uncurry (ApiSeed.transcript c cfg sh g S init m width batches choose))

/-- Pointwise correctness and all top populations for a seeded legal client.
Admissibility quantifies separately over each seed and each legal transcript;
there is no common dictionary, and no event is conditioned on success. -/
def ApiSeedLive_statement : Prop :=
  ∀ (Seed : Type) (geo : HierarchyGeometry), geo.Structural →
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
    ∀ seed tape,
    let a := ApiSeed.run c geo.cfg geo.shapes g S init m width batches choose seed
    let t := ApiSeed.transcript c geo.cfg geo.shapes g S init m width batches choose seed tape
    let qs := (ApiAdaptive.requestGroups (ApiLegal.adapt geo.cfg (ApiAdaptive.shape fs) S (choose seed))
      (Adaptive.rowsOf t n) fs).flatMap PublicApi.Group.lanes
    let realized := Adaptive.realized geo.cfg geo.shapes g S a
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)
    ApiRunCorrect geo c g realized S qs ∧ ApiTopPopulations geo g realized ∧
      ApiLegal.erase (ApiLegal.normalizeTranscript geo.cfg (ApiAdaptive.shape fs) S t) = t

/-- A measurable event may inspect both the private seed and actual transcript.
Explicit seedwise bounds integrate with execution measurability discharged. -/
def ApiSeedEventBound_statement : Prop :=
  ∀ (Seed : Type) [MeasurableSpace Seed] [Countable Seed] [MeasurableSingletonClass Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    c cfg sh g S (init : Seed → List Rec) m width batches choose,
    let observe := ApiSeed.transcript c cfg sh g S init m width batches choose
    ∀ event : Set (Seed ×
      (Fin (Adaptive.slotCount (ApiAdaptive.shape (ApiAdaptive.frames width g.unitEntries batches))) →
        Fin m → Nat)),
    MeasurableSet event → ∀ bound : Seed → ℝ≥0∞,
    (∀ seed, IdealKey.tapeLaw ((fun tape => (seed, observe seed tape)) ⁻¹' event) ≤ bound seed) →
    (μ.prod IdealKey.tapeLaw) ((fun p => (p.1, observe p.1 p.2)) ⁻¹' event) ≤
      ∫⁻ seed, bound seed ∂μ

/-- Conditional mixture adapter for the actual engine. A seedwise exact-law
theorem is still required; this contract does not assert hierarchy freshness. -/
def ApiSeedExact_statement : Prop :=
  ∀ (Seed : Type) [MeasurableSpace Seed] [Countable Seed] [MeasurableSingletonClass Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    c cfg sh g S (init : Seed → List Rec) m width batches choose,
    let observe := ApiSeed.transcript c cfg sh g S init m width batches choose
    ∀ simulator : Measure
      (Fin (Adaptive.slotCount (ApiAdaptive.shape (ApiAdaptive.frames width g.unitEntries batches))) →
        Fin m → Nat),
    IsProbabilityMeasure simulator →
    (∀ seed, IdealKey.tapeLaw.map (observe seed) = simulator) →
    (μ.prod IdealKey.tapeLaw).map (fun p => (p.1, observe p.1 p.2)) = μ.prod simulator ∧
      (μ.prod IdealKey.tapeLaw).map (Function.uncurry observe) = simulator

/-- The actual seeded capacity-failure event is measurable. Any separately
proved uniform seedwise failure bound survives independent client randomization. -/
def ApiSeedFailure_statement : Prop :=
  ∀ (Seed : Type) [MeasurableSpace Seed] [Countable Seed] [MeasurableSingletonClass Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    c cfg sh g S (init : Seed → List Rec) m width batches choose,
    let bad := ApiSeed.failure c cfg sh g S init m width batches choose
    MeasurableSet bad ∧ ∀ bound : ℝ≥0∞,
      (∀ seed, IdealKey.tapeLaw (Prod.mk seed ⁻¹' bad) ≤ bound) →
      (μ.prod IdealKey.tapeLaw) bad ≤ bound

end RebuildBound.Spec
