import RebuildBound.Spec.Oblivious
import RebuildBound.Spec.Model.OnlineBatch

/-!
# Obliviousness with batch chunks (trusted statements)

The
statements of `Spec/Oblivious.lean` for runs that mix scalar operations with
batch chunks (`Model.OnlineBatch`), indexed by slot (one lane per access
position). The simulator reads the schedule at the operations' first slots
and which slots probe, both public (`widths`, `probePattern`). On a run without
chunks the model is the scalar one (`BatchScalar`).

**Premises.** `BatchRunPremises` are the scalar run premises over slots. The
schedule premises, the dummy tape, the tape premises and the simulator's law
are the scalar ones (`SchedulePremises`, `DummyTape`, `OnlineTapePremises`,
`simLaw`), the schedule indexed by slot; `syncSchedule` meets the premises
(`SyncSchedule`).

**Plan.** `BatchPattern`, `BatchFresh` (a chunk's real lanes have distinct
keys, and a chunk re-inserts every key at or after its first slot, so the
scalar window argument carries over), `BatchExact`, `BatchFailure`,
the generic numerical assembly, and `BatchOblivious31` for the supported
`geometry31` instance; `HierarchyChunkPartition` is reused. Selected
configuration specializations remain internal proof infrastructure.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.OnlineBatch

/-! ### Premises -/

/-- The run's premises over its slots: the geometry matches, the run fits
the horizon, every key lies below `N`, and the hierarchy's trace premises and
unshadowed promise hold for its trace. -/
structure BatchRunPremises (cfg : Config) (sh : Shapes) (N : Nat) (g : OnlineGeom) (run : BatchRun) :
    Prop where
  geom : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 ∧ 0 < g.unitEntries
  horizon : (slots run).length ≤ cfg.horizon
  keys : ∀ s ∈ slots run, s.record.key.toNat < N
  trace : TracePremises cfg N (Model.OnlineBatch.traceOf g run)
  unsh : UnshPromise cfg sh (Model.OnlineBatch.traceOf g run)

/-- Everything the batch statements assume at one configuration, for the
first `n` slots with plans of at most `m` tables. -/
def BatchSettingFor (geo : HierarchyGeometry) (N : Nat) (g : OnlineGeom) (run : BatchRun)
    (S : Schedule) (n m : Nat) : Prop :=
  N ≤ geo.keyCapacity ∧ n ≤ (slots run).length ∧
    BatchRunPremises geo.cfg geo.shapes N g run ∧ SchedulePremises geo.cfg S n m

/-- Original selected-geometry specialization. -/
def BatchSetting (cfg : Config) (rows : List (SepGeom × Nat)) (N : Nat) (g : OnlineGeom) (run : BatchRun)
    (S : Schedule) (n m : Nat) : Prop :=
  BatchSettingFor (HierarchyGeometry.selected cfg rows) N g run S n m

/-- The pattern does not depend on the words, at every entry of a plan. -/
def BatchPatternFor (geo : HierarchyGeometry) : Prop :=
  ∀ N g run S n m, BatchSettingFor geo N g run S n m →
    ∀ (words words' : Words) t i, t < n → i < (slotSchedule (widths run) S t).tables.length →
      Model.OnlineBatch.isReal geo.cfg geo.shapes g run S words t i =
        Model.OnlineBatch.isReal geo.cfg geo.shapes g run S words' t i

/-- Original selected-geometry specialization. -/
def BatchPatternAt (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  BatchPatternFor (HierarchyGeometry.selected cfg rows)

/-- **BatchPattern**: which plan entries get real buckets depends only on the
run and the schedule. -/
def BatchPattern_statement : Prop := SelectedOnline BatchPatternAt

/-- Every real probe at an entry of a plan reads a word of the family tape (a
coordinate of the horizon, a key below `N`), and no two real probes read the
same one. -/
def BatchFreshFor (geo : HierarchyGeometry) : Prop :=
  ∀ N g run S n m, BatchSettingFor geo N g run S n m → ∀ (words : Words),
    (∀ t i, t < n → i < (slotSchedule (widths run) S t).tables.length →
      Model.OnlineBatch.isReal geo.cfg geo.shapes g run S words t i = true →
      ∃ c s, (slotSchedule (widths run) S t).tables[i]? = some c ∧ (slots run)[t]? = some s ∧
        familyOf geo.cfg c.1 c.2 ∈ geo.cfg.coordinates ∧ s.record.key.toNat < N) ∧
    ∀ t i t' i' c c' s s', t < n → i < m → t' < n → i' < m → (t, i) ≠ (t', i') →
      Model.OnlineBatch.isReal geo.cfg geo.shapes g run S words t i = true →
      Model.OnlineBatch.isReal geo.cfg geo.shapes g run S words t' i' = true →
      (slotSchedule (widths run) S t).tables[i]? = some c →
      (slotSchedule (widths run) S t').tables[i']? = some c' →
      (slots run)[t]? = some s → (slots run)[t']? = some s' →
      (familyOf geo.cfg c.1 c.2, s.record.key) ≠ (familyOf geo.cfg c'.1 c'.2, s'.record.key)

/-- Original selected-geometry specialization. -/
def BatchFreshAt (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  BatchFreshFor (HierarchyGeometry.selected cfg rows)

/-- **BatchFresh**: at most one real probe per family and key. -/
def BatchFresh_statement : Prop := SelectedOnline BatchFreshAt

/-! ### The exact law -/

/-- The view's law is the simulator's. -/
def BatchExactFor (geo : HierarchyGeometry) : Prop :=
  ∀ N g run S n m, BatchSettingFor geo N g run S n m →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → FamilyTape geo.cfg N) (dtape : Ω → DummyTape n m) (words : Ω → Words),
      OnlineTapePremises geo.cfg N n m μ tape dtape words →
      μ.map (fun ω => Model.OnlineBatch.view geo.cfg geo.shapes g run S n m (words ω)
          (dummyOf (dtape ω))) =
        simLaw geo.cfg (slotSchedule (widths run) S) (Model.OnlineBatch.probePattern run) n m

/-- Original selected-geometry specialization. -/
def BatchExactAt (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  BatchExactFor (HierarchyGeometry.selected cfg rows)

/-- **BatchExact**: on the ideal tape the model's view is exactly the
simulator's, whatever the run. Conditional on the pattern and freshness
statements. -/
def BatchExact_statement : Prop :=
  BatchPattern_statement → BatchFresh_statement → SelectedOnline BatchExactAt

/-! ### Failures and the numerical bound -/

/-- Any observation that equals (an image of) the model's view on every
outcome without a capacity failure has, on every measurable set, the
simulator's probability up to the failure probability. -/
def BatchFailureFor (geo : HierarchyGeometry) : Prop :=
  ∀ N g run S n m, BatchSettingFor geo N g run S n m →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → FamilyTape geo.cfg N) (dtape : Ω → DummyTape n m) (words : Ω → Words),
      OnlineTapePremises geo.cfg N n m μ tape dtape words →
      ∀ {V : Type} [MeasurableSpace V] (obs : Ω → V) (ι : (Fin n → Fin m → Nat) → V),
        Measurable obs → Measurable ι →
        (∀ ω, ¬ Fails geo.cfg geo.shapes (Model.OnlineBatch.traceOf g run) (words ω) →
          obs ω = ι (Model.OnlineBatch.view geo.cfg geo.shapes g run S n m (words ω)
            (dummyOf (dtape ω)))) →
        ∀ A : Set V, MeasurableSet A →
          μ (obs ⁻¹' A) ≤
              (simLaw geo.cfg (slotSchedule (widths run) S) (Model.OnlineBatch.probePattern run) n m).map
                ι A +
              μ {ω | Fails geo.cfg geo.shapes (Model.OnlineBatch.traceOf g run) (words ω)} ∧
            (simLaw geo.cfg (slotSchedule (widths run) S) (Model.OnlineBatch.probePattern run) n m).map
                ι A ≤ μ (obs ⁻¹' A) +
              μ {ω | Fails geo.cfg geo.shapes (Model.OnlineBatch.traceOf g run) (words ω)}

/-- Original selected-geometry specialization. -/
def BatchFailureAt (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  BatchFailureFor (HierarchyGeometry.selected cfg rows)

/-- **BatchFailure**: every observation that agrees with the view off failure
is within the failure probability of the simulator. Conditional on
`BatchExact` and the two statements it uses. -/
def BatchFailure_statement : Prop :=
  BatchPattern_statement → BatchFresh_statement → BatchExact_statement →
    SelectedOnline BatchFailureAt

/-- The numerical form over `h` chunks of `2^32` accesses. -/
def BatchObliviousFor (geo : HierarchyGeometry) (error : ℝ≥0∞) : Prop :=
  ∀ (h : Nat), 1 ≤ h →
    let current := geo.chunk h
    let c := current.cfg
    ∀ N g run S n m, BatchSettingFor current N g run S n m →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (tape : Ω → FamilyTape c N) (dtape : Ω → DummyTape n m) (words : Ω → Words),
        OnlineTapePremises c N n m μ tape dtape words →
        ∀ {V : Type} [MeasurableSpace V] (obs : Ω → V) (ι : (Fin n → Fin m → Nat) → V),
          Measurable obs → Measurable ι →
          (∀ ω, ¬ Fails c current.shapes (Model.OnlineBatch.traceOf g run) (words ω) →
            obs ω = ι (Model.OnlineBatch.view c current.shapes g run S n m (words ω)
              (dummyOf (dtape ω)))) →
          ∀ A : Set V, MeasurableSet A →
            μ (obs ⁻¹' A) ≤
                (simLaw c (slotSchedule (widths run) S) (Model.OnlineBatch.probePattern run) n m).map
                  ι A + (h : ℝ≥0∞) * error ∧
              (simLaw c (slotSchedule (widths run) S) (Model.OnlineBatch.probePattern run) n m).map
                  ι A ≤ μ (obs ⁻¹' A) + (h : ℝ≥0∞) * error

/-! ### The scalar model is the batch model without chunks -/

/-- **BatchScalar**: on a run without chunks the batch model has the scalar
model's trace, plans, probe pattern and view. -/
def BatchScalar_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : OnlineRun) (S : Schedule) (n m : Nat)
    (words : Words) (dummy : Nat → Nat → Nat),
    Model.OnlineBatch.traceOf g (ofScalar run) = Model.Online.traceOf g run ∧
    slotSchedule (widths (ofScalar run)) S = S ∧
    Model.OnlineBatch.probePattern (ofScalar run) = Model.Online.probePattern run ∧
    Model.OnlineBatch.view cfg sh g (ofScalar run) S n m words dummy =
      Model.Online.view cfg sh g run S n m words dummy

end RebuildBound.Spec
