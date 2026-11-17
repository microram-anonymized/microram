import RebuildBound.Spec.HierarchySemantics

/-! Conditional correctness of bounded executions. The adapter supplies actual
probe results and agreement with the reference off capacity failure. Adaptive
agreement includes the issued run, since later requests may depend on earlier
observations. These are explicit refinement premises, not consequences of the
structural contract. No numerical bound or tape-distribution law is assumed.
-/

open MeasureTheory

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.Adaptive

/-- Actual scalar answers and addresses agree with the supplied logical history.
Only existing, probing operations within the stated prefix are constrained. -/
def OnlineResultsCorrect (geo : HierarchyGeometry) (g : OnlineGeom) (run : OnlineRun)
    (S : Schedule) (n : Nat) (words : Words) (dummy : Nat → Nat → Nat)
    (actual : Nat → Probe.Result) : Prop :=
  ∀ j o, j < n → run.ops[j]? = some o → o.probes = true →
    Probe.decode (actual j).found =
        Probe.latestValue o.record.key (run.init ++ (run.ops.take j).map Op.record) ∧
      ∀ i, (actual j).addresses.getD i 0 = touched geo.cfg geo.shapes g run S words dummy j i

/-- Batch answers include earlier lanes, including duplicate keys and tombstones. -/
def BatchResultsCorrect (geo : HierarchyGeometry) (g : OnlineGeom) (run : OnlineBatch.BatchRun)
    (S : Schedule) (n : Nat) (words : Words) (dummy : Nat → Nat → Nat)
    (actual : Nat → Probe.Result) : Prop :=
  ∀ t s, t < n → (OnlineBatch.slots run)[t]? = some s → s.probes = true →
    Probe.decode (actual t).found = Probe.latestValue s.record.key
        (run.init ++ ((OnlineBatch.slots run).take t).map OnlineBatch.Slot.record) ∧
      ∀ i, (actual t).addresses.getD i 0 =
        OnlineBatch.touched geo.cfg geo.shapes g run S words dummy t i

/-- Scalar agreement off failure gives pointwise correctness there and bounds
the incorrect-result event by the actual failure event, under any measure. -/
def HierarchyBoundedOnline_statement : Prop :=
  ∀ geo, geo.Structural → ∀ U g run S n m,
    UniverseOnlineSetting geo U g run S n m →
    (geo.cfg.initialized = false → run.init = []) →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
      (words : Ω → Words) (dummy : Ω → Nat → Nat → Nat) (actual : Ω → Nat → Probe.Result),
      (∀ ω, ¬ Fails geo.cfg geo.shapes (Online.traceOf g run) (words ω) →
        ∀ j < n, actual ω j = Probe.scalar geo.cfg geo.shapes g run S (words ω) (dummy ω) j) →
      (∀ ω, ¬ Fails geo.cfg geo.shapes (Online.traceOf g run) (words ω) →
        OnlineResultsCorrect geo g run S n (words ω) (dummy ω) (actual ω)) ∧
      μ {ω | ¬ OnlineResultsCorrect geo g run S n (words ω) (dummy ω) (actual ω)} ≤
        μ {ω | Fails geo.cfg geo.shapes (Online.traceOf g run) (words ω)}

/-- The same transfer for fixed mixed scalar/batch runs. -/
def HierarchyBoundedBatch_statement : Prop :=
  ∀ geo, geo.Structural → ∀ U g run S n m,
    UniverseBatchSetting geo U g run S n m →
    (geo.cfg.initialized = false → run.init = []) →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
      (words : Ω → Words) (dummy : Ω → Nat → Nat → Nat) (actual : Ω → Nat → Probe.Result),
      (∀ ω, ¬ Fails geo.cfg geo.shapes (OnlineBatch.traceOf g run) (words ω) →
        ∀ t < n, actual ω t = Probe.batch geo.cfg geo.shapes g run S (words ω) (dummy ω) t) →
      (∀ ω, ¬ Fails geo.cfg geo.shapes (OnlineBatch.traceOf g run) (words ω) →
        BatchResultsCorrect geo g run S n (words ω) (dummy ω) (actual ω)) ∧
      μ {ω | ¬ BatchResultsCorrect geo g run S n (words ω) (dummy ω) (actual ω)} ≤
        μ {ω | Fails geo.cfg geo.shapes (OnlineBatch.traceOf g run) (words ω)}

/-- Adaptive transfer uses one fixed universe across branches. The actual
operation history and probe results must agree off the reference failure event;
both may differ on failure. The conclusion uses the actual history. -/
def HierarchyBoundedAdaptive_statement : Prop :=
  ∀ geo, geo.Structural → ∀ U g m (a : AdaptiveRun m) S n,
    AdaptiveSetting geo U g a S n →
    (geo.cfg.initialized = false → a.init = []) →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
      (words : Ω → Words) (dummy : Ω → Nat → Nat → Nat)
      (runs : Ω → OnlineBatch.BatchRun) (actual : Ω → Nat → Probe.Result),
      (∀ ω, ¬ AdaptiveFails geo.cfg geo.shapes g S a (words ω) (dummy ω) →
        runs ω = realized geo.cfg geo.shapes g S a (words ω) (dummy ω) ∧
        ∀ t < n, actual ω t =
          Probe.batch geo.cfg geo.shapes g (runs ω) S (words ω) (dummy ω) t) →
      (∀ ω, ¬ AdaptiveFails geo.cfg geo.shapes g S a (words ω) (dummy ω) →
        BatchResultsCorrect geo g (runs ω) S n (words ω) (dummy ω) (actual ω)) ∧
      μ {ω | ¬ BatchResultsCorrect geo g (runs ω) S n (words ω) (dummy ω) (actual ω)} ≤
        μ {ω | AdaptiveFails geo.cfg geo.shapes g S a (words ω) (dummy ω)}

end RebuildBound.Spec
