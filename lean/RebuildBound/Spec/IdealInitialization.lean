import RebuildBound.Spec.IdealHierarchy
import RebuildBound.Spec.TopPrepG
import RebuildBound.Spec.Model.TopPrepCanonical
import RebuildBound.Spec.ApiCapacity

/-! Initialization failure on the actual canonical tape, using the existing
finite job bound at the input's own keys. Only the input record count is bounded;
neither the numeric encoding of keys nor the future adaptive dictionary is. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy IdealHierarchy MeasureTheory
open scoped ENNReal NNReal

/-- The actual initialization event is measurable even when later trace units
are arbitrary functions of the tape. No geometry or population premise is
needed for this event-space fact. -/
def IdealInitializationMeasurable_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (input : List Rec) (trace : IdealKey.Tape → Trace),
    (∀ tape, (trace tape).init = input) →
      MeasurableSet {tape | (initResult cfg sh (trace tape) (words tape)).toBool = false}

/-- The actual initialization job satisfies its analytic bound. Later trace
units may depend arbitrarily on the same tape; initialization uses only its
fixed input, including on reference continuations after overflow. -/
def IdealInitializationBound_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (input : List Rec) (K1 K2 : Nat),
    sh.init.Valid → sh.init.k ≤ 64 → (input.map Rec.key).Nodup →
    input.length ≤ sh.init.C / 2 * sh.init.T →
    (sh.init.dfs = true → sh.init.I + 1 < sh.init.k) →
    sh.init.stashPages * sh.init.C < K1 → sh.init.drainPages * sh.init.C < K2 →
    ∀ trace : IdealKey.Tape → Trace, (∀ tape, (trace tape).init = input) →
      IdealKey.tapeLaw {tape | (initResult cfg sh (trace tape) (words tape)).toBool = false} ≤
        tpBound sh.init ((sh.init.C / 2 : Nat) : NNReal) 1 K1 K2

/-- API initialization validity supplies the population premise for the raw
initialization test. Empty starts force an empty input; the separate public
job inventory omits initialization entirely at that start. -/
def IdealInitializationApi_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (capacity : Nat) (input : List Rec) (K1 K2 : Nat),
    sh.init.Valid → sh.init.k ≤ 64 →
    ApiCapacity.InitialStateValid capacity cfg.initialized input →
    capacity ≤ sh.init.C / 2 * sh.init.T →
    (sh.init.dfs = true → sh.init.I + 1 < sh.init.k) →
    sh.init.stashPages * sh.init.C < K1 → sh.init.drainPages * sh.init.C < K2 →
    ∀ trace : IdealKey.Tape → Trace, (∀ tape, (trace tape).init = input) →
      IdealKey.tapeLaw {tape | jobFails cfg sh (trace tape) (words tape) .initialization = true} ≤
        tpBound sh.init ((sh.init.C / 2 : Nat) : NNReal) 1 K1 K2

end RebuildBound.Spec
