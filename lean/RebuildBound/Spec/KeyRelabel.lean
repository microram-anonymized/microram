import RebuildBound.Spec.Configuration31
import RebuildBound.Spec.KeyRelabel.Semantics
import RebuildBound.Spec.KeyUniverse

/-! Generic-key endpoint statements. The universe is fixed over the entire
run, contains every initialization/operation key, and has at most 2^31
members. The retained input-width premise bounds the numeric fixture encoding. All original schedule,
load, tombstone and observation-agreement premises remain explicit. -/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online

/-- Online exact for logical keys with 64-bit fixture identifiers in one fixed run-wide universe. -/
def GenericOnlineExact31_statement : Prop :=
  ∀ h, 1 ≤ h → UniverseOnlineExactFor (geometry31.chunk h)

/-- Online failure for logical keys with 64-bit fixture identifiers in one fixed run-wide universe. -/
def GenericOnlineFailure31_statement : Prop :=
  ∀ h, 1 ≤ h → UniverseOnlineFailureFor (geometry31.chunk h)

/-- Online correctness for logical keys with 64-bit fixture identifiers in one fixed run-wide universe. -/
def GenericOnlineCorrectness31_statement : Prop :=
  ∀ h, 1 ≤ h → UniverseOnlineCorrectnessFor (geometry31.chunk h)

/-- The original h · 2^-64 observation bound with 64-bit fixture identifiers. -/
def GenericOnlineOblivious31_statement : Prop :=
  UniverseOnlineObliviousFor geometry31 (ENNReal.ofReal (1 / (2 : ℝ) ^ 64))

/-- Batch exact for logical keys with 64-bit fixture identifiers in one fixed run-wide universe. -/
def GenericBatchExact31_statement : Prop :=
  ∀ h, 1 ≤ h → UniverseBatchExactFor (geometry31.chunk h)

/-- Batch failure for logical keys with 64-bit fixture identifiers in one fixed run-wide universe. -/
def GenericBatchFailure31_statement : Prop :=
  ∀ h, 1 ≤ h → UniverseBatchFailureFor (geometry31.chunk h)

/-- Batch correctness for logical keys with 64-bit fixture identifiers in one fixed run-wide universe. -/
def GenericBatchCorrectness31_statement : Prop :=
  ∀ h, 1 ≤ h → UniverseBatchCorrectnessFor (geometry31.chunk h)

/-- The original h · 2^-64 observation bound with 64-bit fixture identifiers. -/
def GenericBatchOblivious31_statement : Prop :=
  UniverseBatchObliviousFor geometry31 (ENNReal.ofReal (1 / (2 : ℝ) ^ 64))

/-- Failure within h chunks, with family words indexed by the fixed actual-key universe. -/
def GenericHierarchyWindows31_statement : Prop :=
  ∀ (h : Nat) (U : Finset LogicalKey) (tr : Trace), 1 ≤ h →
    (∀ k ∈ U, k.toNat < 2 ^ 64) → U.card ≤ keyCapacity31 →
    UniverseTracePremises (chunkConfig config31 h) U tr →
    UnshPromise (chunkConfig config31 h) (geometry31.chunk h).shapes tr →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → UniverseTape (chunkConfig config31 h) U) (words : Ω → Words),
      UniverseTapePremises (chunkConfig config31 h) U μ tape words →
      μ {ω | Fails (chunkConfig config31 h) (geometry31.chunk h).shapes tr (words ω)} ≤
        (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 64)

/-- The same permutation preserves the event that the first failure lies in chunk k. -/
def GenericHierarchyChunk31_statement : Prop :=
  ∀ (k : Nat) (U : Finset LogicalKey) (tr : Trace),
    (∀ x ∈ U, x.toNat < 2 ^ 64) → U.card ≤ keyCapacity31 →
    UniverseTracePremises (chunkConfig config31 (k + 1)) U tr →
    UnshPromise (chunkConfig config31 (k + 1)) (geometry31.chunk (k + 1)).shapes tr →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → UniverseTape (chunkConfig config31 (k + 1)) U) (words : Ω → Words),
      UniverseTapePremises (chunkConfig config31 (k + 1)) U μ tape words →
      μ {ω | ChunkFails config31 (geometry31.chunk (k + 1)).shapes tr (words ω) k} ≤
        ENNReal.ofReal (1 / (2 : ℝ) ^ 64)

end RebuildBound.Spec
