import RebuildBound.Spec.HierarchySemantics
import RebuildBound.Spec.AdaptiveApi.Semantics

/-! Generic selected-record, flag and API semantics. Empty-start correctness
and flag soundness require a consistent empty initial history. Geometry,
run/schedule premises and local API construction remain separate; no numerical
failure bound or planner-family membership is assumed. -/

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.Adaptive

/-- Selected records, including tombstones and flags, are independent of tapes. -/
def BatchFoundFor (geo : HierarchyGeometry) : Prop :=
  ∀ U g run S n m, UniverseBatchSetting geo U g run S n m →
    ∀ (words words' : Words) (dummy dummy' : Nat → Nat → Nat) t, t < n →
      (Probe.batch geo.cfg geo.shapes g run S words dummy t).found =
        (Probe.batch geo.cfg geo.shapes g run S words' dummy' t).found

/-- The local flag rule implies the unshadowed promise, from either start. -/
def FlagSoundnessFor (geo : HierarchyGeometry) : Prop :=
  ∀ (U : Finset LogicalKey) (g : OnlineGeom) (run : OnlineBatch.BatchRun) (S : Schedule)
    (m : Nat) (words : Words),
    (geo.cfg.initialized = false → run.init = []) →
    (∀ k ∈ U, k.toNat < 2 ^ 64) → U.card ≤ geo.keyCapacity →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → (OnlineBatch.slots run).length ≤ geo.cfg.horizon →
    UniverseTracePremises geo.cfg U (OnlineBatch.traceOf g run) →
    SchedulePremises geo.cfg S (OnlineBatch.slots run).length m →
    FlagRule geo.cfg geo.shapes g run S words →
    UnshPromise geo.cfg geo.shapes (OnlineBatch.traceOf g run)

/-- Local post-record construction realizes every API prefix and reply. -/
def BatchApiCorrectnessFor (geo : HierarchyGeometry) : Prop :=
  ∀ U g run S m,
    UniverseBatchSetting geo U g run S (OnlineBatch.slots run).length m →
    (geo.cfg.initialized = false → run.init = []) →
    ∀ (c : Api.Codec) (words : Words) (dummy : Nat → Nat → Nat) (requests : List Api.Request),
      Api.Implements c geo.cfg geo.shapes
        g run S words dummy requests →
      ApiCorrect c geo.cfg geo.shapes
        g run S words dummy requests

/-- Local API construction derives the setting without assuming its unshadowed promise. -/
def ApiAdmissibleFor (geo : HierarchyGeometry) : Prop :=
  ∀ (U : Finset LogicalKey) (g : OnlineGeom) (run : OnlineBatch.BatchRun)
    (S : Schedule) (m : Nat) (c : Api.Codec) (words : Words)
    (dummy : Nat → Nat → Nat) (requests : List Api.Request),
    (geo.cfg.initialized = false → run.init = []) →
    (∀ k ∈ U, k.toNat < 2 ^ 64) → U.card ≤ geo.keyCapacity →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → (OnlineBatch.slots run).length ≤ geo.cfg.horizon →
    (run.init.map Rec.key).Nodup → (∀ r ∈ run.init, r.key ∈ U) →
    (∀ q ∈ requests, q.key ∈ U) →
    SchedulePremises geo.cfg S (OnlineBatch.slots run).length m →
    (∀ r, run.unsh r = c.flag r.val) →
    Api.Implements c geo.cfg geo.shapes
      g run S words dummy requests →
    UniverseBatchSetting geo U g run S (OnlineBatch.slots run).length m

/-- One fixed universe and the flag rule on every branch derive adaptive admissibility. -/
def AdaptiveFlagAdmissibleFor (geo : HierarchyGeometry) : Prop :=
  ∀ (U : Finset LogicalKey) (g : OnlineGeom) (m : Nat) (a : AdaptiveRun m) (S : Schedule),
    (geo.cfg.initialized = false → a.init = []) →
    (∀ k ∈ U, k.toNat < 2 ^ 64) → U.card ≤ geo.keyCapacity →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → slotCount a.shape ≤ geo.cfg.horizon →
    (a.init.map Rec.key).Nodup → (∀ x ∈ a.init, x.key ∈ U) →
    (∀ rows i, (a.client rows i).key ∈ U) →
    SchedulePremises geo.cfg S (slotCount a.shape) m →
    (∀ t : Fin (slotCount a.shape) → Fin m → Nat,
      FlagRule geo.cfg geo.shapes g (replay a t) S
        fun _ _ _ => 0) →
    AdaptiveSetting geo U g a S (slotCount a.shape)

/-- API correctness transfers to the actual adaptive run under arbitrary tapes. -/
def AdaptiveApiCorrectnessFor (geo : HierarchyGeometry) : Prop :=
  ∀ (U : Finset LogicalKey) (g : OnlineGeom) (m : Nat)
    (a : AdaptiveRun m) (S : Schedule) (n : Nat),
    AdaptiveSetting geo U g a S n →
    (geo.cfg.initialized = false → a.init = []) →
    ∀ (c : Api.Codec) (words : Words) (dummy : Nat → Nat → Nat)
      (requests : List Api.Request),
      let run := realized geo.cfg geo.shapes g S a words dummy
      Api.Implements c geo.cfg geo.shapes g run S words dummy requests →
      ApiCorrect c geo.cfg geo.shapes g run S words dummy requests

/-- Selected records, including tombstones and flags, are independent of tapes. -/
def HierarchyBatchFound_statement : Prop :=
  ∀ geo, geo.Structural → BatchFoundFor geo

/-- The local flag rule implies the unshadowed promise, from either start. -/
def HierarchyFlagSoundness_statement : Prop :=
  ∀ geo, geo.Structural → FlagSoundnessFor geo

/-- Local post-record construction realizes every API prefix and reply. -/
def HierarchyBatchApiCorrectness_statement : Prop :=
  ∀ geo, geo.Structural → BatchApiCorrectnessFor geo

/-- Local API construction derives the setting without assuming its unshadowed promise. -/
def HierarchyApiAdmissible_statement : Prop :=
  ∀ geo, geo.Structural → ApiAdmissibleFor geo

/-- One fixed universe and the flag rule on every branch derive adaptive admissibility. -/
def HierarchyAdaptiveFlagAdmissible_statement : Prop :=
  ∀ geo, geo.Structural → AdaptiveFlagAdmissibleFor geo

/-- API correctness transfers to the actual adaptive run under arbitrary tapes. -/
def HierarchyAdaptiveApiCorrectness_statement : Prop :=
  ∀ geo, geo.Structural → AdaptiveApiCorrectnessFor geo

end RebuildBound.Spec
