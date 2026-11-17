import RebuildBound.Spec.DirectJobReferenceCoverage
import RebuildBound.Spec.DirectJobLawTransport
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.UniformOn

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- A single uniform finite tape supplies an unconditional job law whenever it
splits into the complete history/current-word outcome and unused coordinates.
The split is a bijection of assignments, not a separate-marginal assumption.
Unused coordinates can include future families; no success event is selected. -/
def DirectJobUniformCoupling_statement : Prop :=
  ∀ {Ω : Type} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    {g : SepGeom} (L : SJobLaw g) (Unused : Type) [Fintype Unused] [Nonempty Unused]
    (split : Ω ≃ DirectJobOutcome L × Unused),
    (∀ hist, L.weight hist = (Fintype.card L.Hist : ℝ≥0∞)⁻¹) →
    DirectJobLawCoupling (ProbabilityTheory.uniformOn (Set.univ : Set Ω)) L
      (fun ω => (split ω).1)

/-- Digit one on the same uniform-tape construction. The only population
premises are the complete B key set and its load; no A input law is needed. -/
def DirectJobUniformDigitOneProbability_statement : Prop :=
  ∀ {Ω : Type} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    {g : SepGeom} (L : SJobLaw g) [Nonempty L.Hist]
    (direct : L.Hist → (LogicalKey → Nat) → DirectJob.Inputs)
    (Unused : Type) [Fintype Unused] [Nonempty Unused]
    (split : Ω ≃ DirectJobOutcome L × Unused),
    (∀ hist, L.weight hist = (Fintype.card L.Hist : ℝ≥0∞)⁻¹) →
    4 ≤ L.W →
    (∀ hist hw, ((direct hist (L.wordFn hw)).bRecords.map Rec.key).toFinset = L.KB) →
    L.KB.card ≤ 512 →
    ProbabilityTheory.uniformOn (Set.univ : Set Ω)
      {ω | ∃ e, runJob (selectedDirectGeometry 1) (L.wOld (split ω).1.1)
        (L.wordFn (split ω).1.2) (direct (split ω).1.1 (L.wordFn (split ω).1.2)) =
          .failed e} ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 117)

/-- Selected history bounds on a concrete uniform tape: uniform earlier base
assignments and a product split discharge the joint-coupling premise. The
source/chronology/load contract remains explicit in data.Valid. -/
def DirectJobUniformHistoryProbability_statement : Prop :=
  ∀ {Ω : Type} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (d : Nat), 2 ≤ d → d ≤ 8 →
    ∀ (data : DirectHistoryData), data.Valid d →
    (∀ base, data.weight base = (Fintype.card data.Base : ℝ≥0∞)⁻¹) →
    ∀ (Unused : Type) [Fintype Unused] [Nonempty Unused]
      (split : Ω ≃ DirectJobOutcome (data.law d) × Unused),
    ProbabilityTheory.uniformOn (Set.univ : Set Ω)
      {ω | ∃ e, runJob (selectedDirectGeometry d)
        ((data.law d).wOld (split ω).1.1) ((data.law d).wordFn (split ω).1.2)
        (data.direct d (split ω).1.1 ((data.law d).wordFn (split ω).1.2)) = .failed e} ≤
      selectedDirectBound selectedDirectABudget d

end RebuildBound.Spec
