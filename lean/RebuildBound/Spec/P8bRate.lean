import RebuildBound.Spec.P8bPair
import Mathlib.Probability.Distributions.Poisson.Basic

/-! # Fixed-marginal shared Poisson rate

The two counts have marginal rates `a` and `b`. Their common Poisson primitive
has rate `gamma`; the remaining independent primitives have rates `a - gamma`
and `b - gamma`. Feasibility must be explicit because NNReal subtraction is
truncated. This is a reusable comparison step, not the full star bound.
-/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RebuildBound.Spec

noncomputable def sharedPoissonPair (a b gamma : ℝ≥0)
    (f : ℕ → ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ z, ∫⁻ x, ∫⁻ y, f (x + z) (y + z)
    ∂poissonMeasure (b - gamma) ∂poissonMeasure (a - gamma) ∂poissonMeasure gamma

/-- Increasing the shared primitive rate at fixed feasible marginal rates
increases every supermodular test, including tests with infinite expectation. -/
def P8bRate_statement : Prop :=
  ∀ (a b gamma gamma' : ℝ≥0) (f : ℕ → ℕ → ℝ≥0∞),
    gamma ≤ gamma' → gamma' ≤ a → gamma' ≤ b →
    SharedIncreasingDifferences f →
    sharedPoissonPair a b gamma f ≤ sharedPoissonPair a b gamma' f

end RebuildBound.Spec
