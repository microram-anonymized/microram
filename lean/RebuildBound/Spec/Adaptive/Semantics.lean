import RebuildBound.Spec.KeyUniverse
import RebuildBound.Spec.Model.Adaptive

/-! Generic adaptive settings, exact laws and error-parametric interfaces. The public shape, schedule and universe are fixed across all client branches. -/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.Adaptive

/-- Everything the adaptive statements assume: the transcript covers every
slot of the shape (fixed length: every row the client sees is in the
transcript), and every run the client can issue, whatever rows it
reads, meets the fixed-run setting with one universe `U`. -/
def AdaptiveSetting (geo : HierarchyGeometry) (U : Finset LogicalKey) (g : OnlineGeom) {m : Nat}
    (a : AdaptiveRun m) (S : Schedule) (n : Nat) : Prop :=
  n = slotCount a.shape ∧
    ∀ t : Fin n → Fin m → Nat, UniverseBatchSetting geo U g (replay a t) S n m

/-- A capacity failure of the run the interaction issued. -/
def AdaptiveFails (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat}
    (a : AdaptiveRun m) (words : Words) (dummy : Nat → Nat → Nat) : Prop :=
  Fails cfg sh (OnlineBatch.traceOf g (realized cfg sh g S a words dummy)) words

/-- The transcript is measurable and its law is the simulator's for the
public shape. (Mathlib's image of a non-measurable map is a Dirac measure, so
the law alone would not give measurability.) -/
def AdaptiveExactFor (geo : HierarchyGeometry) : Prop :=
  ∀ U g m (a : AdaptiveRun m) S n, AdaptiveSetting geo U g a S n →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → UniverseTape geo.cfg U) (dtape : Ω → DummyTape n m) (words : Ω → Words),
      UniverseOnlineTapePremises geo.cfg U n m μ tape dtape words →
      Measurable (fun ω => transcript geo.cfg geo.shapes g S a n (words ω) (dummyOf (dtape ω))) ∧
        μ.map (fun ω => transcript geo.cfg geo.shapes g S a n (words ω) (dummyOf (dtape ω))) =
          simLaw geo.cfg (OnlineBatch.slotSchedule (shapeWidths a.shape) S)
            (shapePattern a.shape) n m

/-- The realized run's failure within `h` chunks has probability at most
`h · error`. -/
def AdaptiveWindowsFor (geo : HierarchyGeometry) (error : ℝ≥0∞) : Prop :=
  ∀ (h : Nat), 1 ≤ h →
    let current := geo.chunk h
    let c := current.cfg
    ∀ U g m (a : AdaptiveRun m) S n, AdaptiveSetting current U g a S n →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (tape : Ω → UniverseTape c U) (dtape : Ω → DummyTape n m) (words : Ω → Words),
        UniverseOnlineTapePremises c U n m μ tape dtape words →
        μ {ω | AdaptiveFails c current.shapes g S a (words ω) (dummyOf (dtape ω))} ≤
          (h : ℝ≥0∞) * error

/-- Every observation that agrees with the transcript off the adaptive failure
is within `h · error` of the simulator on every event. -/
def AdaptiveObliviousFor (geo : HierarchyGeometry) (error : ℝ≥0∞) : Prop :=
  ∀ (h : Nat), 1 ≤ h →
    let current := geo.chunk h
    let c := current.cfg
    ∀ U g m (a : AdaptiveRun m) S n, AdaptiveSetting current U g a S n →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (tape : Ω → UniverseTape c U) (dtape : Ω → DummyTape n m) (words : Ω → Words),
        UniverseOnlineTapePremises c U n m μ tape dtape words →
        ∀ {V : Type} [MeasurableSpace V] (obs : Ω → V) (ι : (Fin n → Fin m → Nat) → V),
          Measurable obs → Measurable ι →
          (∀ ω, ¬ AdaptiveFails c current.shapes g S a (words ω) (dummyOf (dtape ω)) →
            obs ω = ι (transcript c current.shapes g S a n (words ω) (dummyOf (dtape ω)))) →
          ∀ A : Set V, MeasurableSet A →
            μ (obs ⁻¹' A) ≤
                (simLaw c (OnlineBatch.slotSchedule (shapeWidths a.shape) S)
                  (shapePattern a.shape) n m).map ι A + (h : ℝ≥0∞) * error ∧
              (simLaw c (OnlineBatch.slotSchedule (shapeWidths a.shape) S)
                  (shapePattern a.shape) n m).map ι A ≤ μ (obs ⁻¹' A) + (h : ℝ≥0∞) * error

/-- **AdaptiveAdmissible**: every client whose records have keys in `U`, with
an initialization of distinct keys in `U` and no unshadowed flag, meets the
adaptive setting under a schedule that meets the premises. -/
def AdaptiveAdmissible_statement : Prop :=
  ∀ (geo : HierarchyGeometry) (U : Finset LogicalKey) (g : OnlineGeom) (m : Nat) (a : AdaptiveRun m)
    (S : Schedule),
    (∀ k ∈ U, k.toNat < 2 ^ 64) → U.card ≤ geo.keyCapacity →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 → 0 < g.unitEntries →
    slotCount a.shape ≤ geo.cfg.horizon →
    (a.init.map Rec.key).Nodup → (∀ x ∈ a.init, x.key ∈ U) →
    (∀ rows i, (a.client rows i).key ∈ U) → (∀ r, a.unsh r = false) →
    SchedulePremises geo.cfg S (slotCount a.shape) m →
    AdaptiveSetting geo U g a S (slotCount a.shape)

end RebuildBound.Spec
