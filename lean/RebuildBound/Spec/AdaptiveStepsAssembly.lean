import RebuildBound.Spec.AdaptiveStepsExact
import RebuildBound.Spec.AdaptiveStepsJobs

/-!
# Adaptive clients: assembly statements

Package statements outside the headline closure (see `Spec/AdaptiveSteps.lean`).

* `AdaptiveExactStep`: the exact law from the replay identity and the
  fixed-run exact law, by singletons on the countable transcript space; the
  transcript's fibres are the replayed runs' view fibres, which gives its
  measurability.
* `AdaptiveNumericWindows31`: the capacity bound with numeric keys, from the
  causal realized trace and the causal capacity bound.
* `AdaptiveWindowsUniverse`: numeric keys to a fixed run-wide universe, by
  the compression of `U` applied to the client's records.
* `AdaptiveObliviousAssembly`: the observation bound from the exact law and
  the capacity bound (`OnlineFailure.transfer`).
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.Adaptive

/-- The capacity bound with numeric keys below `N`. -/
def AdaptiveNumericWindowsFor (geo : HierarchyGeometry) (error : ℝ≥0∞) : Prop :=
  ∀ (h : Nat), 1 ≤ h →
    let current := geo.chunk h
    let c := current.cfg
    ∀ N g m (a : AdaptiveRun m) S n, AdaptiveNumericSetting current N g a S n →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (tape : Ω → FamilyTape c N) (dtape : Ω → DummyTape n m) (words : Ω → Words),
        OnlineTapePremises c N n m μ tape dtape words →
        μ {ω | AdaptiveFails c current.shapes g S a (words ω) (dummyOf (dtape ω))} ≤
          (h : ℝ≥0∞) * error

/-- **AdaptiveNumericWindows31**: the numeric capacity bound at `geometry31`. -/
def AdaptiveNumericWindows31_statement : Prop :=
  AdaptiveNumericWindowsFor geometry31 (ENNReal.ofReal (1 / (2 : ℝ) ^ 64))

/-- **AdaptiveWindowsUniverse**: a numeric capacity bound holds for keys in
any fixed universe. -/
def AdaptiveWindowsUniverse_statement : Prop :=
  ∀ (geo : HierarchyGeometry) (error : ℝ≥0∞),
    AdaptiveNumericWindowsFor geo error → AdaptiveWindowsFor geo error

/-- **AdaptiveObliviousAssembly**: the exact law and the capacity bound give
the observation bound. -/
def AdaptiveObliviousAssembly_statement : Prop :=
  ∀ (geo : HierarchyGeometry) (error : ℝ≥0∞),
    (∀ h, 1 ≤ h → AdaptiveExactFor (geo.chunk h)) → AdaptiveWindowsFor geo error →
      AdaptiveObliviousFor geo error

def AdaptiveNumericWindowsStep_statement : Prop :=
  AdaptiveCausal31_statement → CausalWindows31_statement → AdaptiveNumericWindows31_statement

end RebuildBound.Spec
