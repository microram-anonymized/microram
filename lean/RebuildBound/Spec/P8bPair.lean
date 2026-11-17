import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# P8b's pairwise shared-rate comparison (trusted statement)

For an increasing-differences test, two copies of one count dominate two
independent identically distributed counts. In the star proof the common law
is Poisson(delta): this replaces two independent primitive rates by a shared
rate while keeping both marginal rates fixed. This lemma alone does NOT
establish the marked-Poisson star, its rate feasibility, the raw engine
witness, or the numerical positive series.
-/
open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec

/-- Supermodularity on two nonnegative integer coordinates. -/
def SharedIncreasingDifferences (f : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ a b c d : ℕ, a ≤ b → c ≤ d → f a d + f b c ≤ f a c + f b d

/-- One shared count dominates two independent equal-law counts. No
independence is asserted for the actual A/B copies in the job. -/
def P8bPair_statement : Prop :=
  ∀ (μ : Measure ℕ) [IsProbabilityMeasure μ] (f : ℕ → ℕ → ℝ≥0∞),
    SharedIncreasingDifferences f →
    (∫⁻ n, ∫⁻ m, f n m ∂μ ∂μ) ≤ ∫⁻ n, f n n ∂μ

end RebuildBound.Spec
