import RebuildBound.Spec.HierarchyStructure
import RebuildBound.Spec.Adaptive.Semantics
import RebuildBound.Spec.KeyRelabel.Semantics

/-! Public generic reference semantics, for either start. Run/schedule premises
and joint ideal-tape laws stay separate from the finite structural contract.
Lookup explicitly requires an empty supplied history when initialization is
disabled. The fixed-universe correctness predicates and all `*31` statements
are stated separately and are not modified by this generic form.
Observation transfer uses the actual failure probability, never a law
conditioned on success or an assumed numerical family bound. -/

open MeasureTheory

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.Adaptive

/-- Scalar reference answers and addresses, with consistent initial history. -/
def OnlineLookupFor (geo : HierarchyGeometry) : Prop :=
  ∀ N g run S n m, OnlineSettingFor geo N g run S n m →
    (geo.cfg.initialized = false → run.init = []) →
    ∀ (words : Words) (dummy : Nat → Nat → Nat) j o, j < n →
      run.ops[j]? = some o → o.probes = true →
      let result := Probe.scalar geo.cfg geo.shapes g run S words dummy j
      Probe.decode result.found =
          Probe.latestValue o.record.key (run.init ++ (run.ops.take j).map Op.record) ∧
        ∀ i, result.addresses.getD i 0 = touched geo.cfg geo.shapes g run S words dummy j i

/-- Batch reference answers include earlier lanes of the same chunk. -/
def BatchLookupFor (geo : HierarchyGeometry) : Prop :=
  ∀ N g run S n m, BatchSettingFor geo N g run S n m →
    (geo.cfg.initialized = false → run.init = []) →
    ∀ (words : Words) (dummy : Nat → Nat → Nat) t s, t < n →
      (OnlineBatch.slots run)[t]? = some s → s.probes = true →
      let result := Probe.batch geo.cfg geo.shapes g run S words dummy t
      Probe.decode result.found = Probe.latestValue s.record.key
          (run.init ++ ((OnlineBatch.slots run).take t).map OnlineBatch.Slot.record) ∧
        ∀ i, result.addresses.getD i 0 =
          OnlineBatch.touched geo.cfg geo.shapes g run S words dummy t i

/-- Scalar lookup for logical keys with 64-bit fixture identifiers in one fixed run-wide universe. -/
def UniverseOnlineLookupFor (geo : HierarchyGeometry) : Prop :=
  ∀ U g run S n m, UniverseOnlineSetting geo U g run S n m →
    (geo.cfg.initialized = false → run.init = []) →
    ∀ (words : Words) (dummy : Nat → Nat → Nat) j o, j < n →
      run.ops[j]? = some o → o.probes = true →
      let result := Probe.scalar geo.cfg geo.shapes g run S words dummy j
      Probe.decode result.found =
          Probe.latestValue o.record.key (run.init ++ (run.ops.take j).map Op.record) ∧
        ∀ i, result.addresses.getD i 0 = touched geo.cfg geo.shapes g run S words dummy j i

/-- Batch lookup for the same fixed universe and consistent initial history. -/
def UniverseBatchLookupFor (geo : HierarchyGeometry) : Prop :=
  ∀ U g run S n m, UniverseBatchSetting geo U g run S n m →
    (geo.cfg.initialized = false → run.init = []) →
    ∀ (words : Words) (dummy : Nat → Nat → Nat) t s, t < n →
      (OnlineBatch.slots run)[t]? = some s → s.probes = true →
      let result := Probe.batch geo.cfg geo.shapes g run S words dummy t
      Probe.decode result.found = Probe.latestValue s.record.key
          (run.init ++ ((OnlineBatch.slots run).take t).map OnlineBatch.Slot.record) ∧
        ∀ i, result.addresses.getD i 0 =
          OnlineBatch.touched geo.cfg geo.shapes g run S words dummy t i

/-- Adaptive observation transfer with error equal to the realized run's
actual failure probability. Every branch uses the same universe and schedule. -/
def AdaptiveFailureFor (geo : HierarchyGeometry) : Prop :=
  ∀ U g m (a : AdaptiveRun m) S n, AdaptiveSetting geo U g a S n →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → UniverseTape geo.cfg U) (dtape : Ω → DummyTape n m) (words : Ω → Words),
      UniverseOnlineTapePremises geo.cfg U n m μ tape dtape words →
      ∀ {V : Type} [MeasurableSpace V] (obs : Ω → V) (ι : (Fin n → Fin m → Nat) → V),
        Measurable obs → Measurable ι →
        (∀ ω, ¬ AdaptiveFails geo.cfg geo.shapes g S a (words ω) (dummyOf (dtape ω)) →
          obs ω = ι (transcript geo.cfg geo.shapes g S a n (words ω) (dummyOf (dtape ω)))) →
        ∀ A : Set V, MeasurableSet A →
          μ (obs ⁻¹' A) ≤
              (simLaw geo.cfg (OnlineBatch.slotSchedule (shapeWidths a.shape) S)
                (shapePattern a.shape) n m).map ι A +
                μ {ω | AdaptiveFails geo.cfg geo.shapes g S a (words ω) (dummyOf (dtape ω))} ∧
            (simLaw geo.cfg (OnlineBatch.slotSchedule (shapeWidths a.shape) S)
              (shapePattern a.shape) n m).map ι A ≤ μ (obs ⁻¹' A) +
                μ {ω | AdaptiveFails geo.cfg geo.shapes g S a (words ω) (dummyOf (dtape ω))}

/-- Both deterministic lookup interfaces follow from structural checks alone. -/
def HierarchyLookup_statement : Prop :=
  ∀ geo, geo.Structural → OnlineLookupFor geo ∧ BatchLookupFor geo

/-- Key relabelling preserves both-start lookup and its address agreement. -/
def HierarchyUniverseLookup_statement : Prop :=
  ∀ geo, geo.Structural → UniverseOnlineLookupFor geo ∧ UniverseBatchLookupFor geo

/-- Fixed-run pattern, freshness, exact law and observation transfer. -/
def HierarchyFixedSemantics_statement : Prop :=
  ∀ geo, geo.Structural →
    (OnlinePatternFor geo ∧ OnlineFreshFor geo ∧ OnlineExactFor geo ∧ OnlineFailureFor geo) ∧
    (BatchPatternFor geo ∧ BatchFreshFor geo ∧ BatchExactFor geo ∧ BatchFailureFor geo)

/-- The exact laws and observation transfer also use arbitrary fixed-universe keys. -/
def HierarchyUniverseSemantics_statement : Prop :=
  ∀ geo, geo.Structural →
    UniverseOnlineExactFor geo ∧ UniverseOnlineFailureFor geo ∧
    UniverseBatchExactFor geo ∧ UniverseBatchFailureFor geo

/-- Adaptive replay yields the exact law and actual-failure transfer. -/
def HierarchyAdaptiveSemantics_statement : Prop :=
  ∀ geo, geo.Structural → AdaptiveExactFor geo ∧ AdaptiveFailureFor geo

end RebuildBound.Spec
