import RebuildBound.Spec.P8bPair
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic

/-!
# One shared-rate comparison for P8b

Probability API obstacles: none. The proof uses the measure-based Tonelli
symmetry directly. Every function on the countable discrete input space is
measurable. No finite-expectation hypothesis is needed: multiplication by
the finite positive scalar two can be cancelled in `ℝ≥0∞`, including when
one or both expectations are infinite.

This package proves only the pairwise comparison in its frozen statement;
it does not supply the marked-Poisson star or its engine coupling.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound

namespace P8bPairProof

/-- Increasing differences gives a symmetric rectangle inequality even when
the two arguments arrive in the opposite order. -/
theorem rectangle (f : ℕ → ℕ → ℝ≥0∞) (hf : Spec.SharedIncreasingDifferences f)
    (n m : ℕ) : f n m + f m n ≤ f n n + f m m := by
  rcases le_total n m with h | h
  · exact hf n m n m h h
  · simpa only [add_comm] using hf m n m n h h

end P8bPairProof

/-- A shared count dominates two independent equal-law counts for an
increasing-differences test. -/
theorem P8bPair : Spec.P8bPair_statement := by
  intro μ _ f hf
  have hadd (g h : ℕ → ℝ≥0∞) :
      (∫⁻ n, g n + h n ∂μ) = (∫⁻ n, g n ∂μ) + ∫⁻ n, h n ∂μ :=
    lintegral_add_left (measurable_of_countable g) h
  have hrectangle := lintegral_mono (μ := μ) (fun n =>
    lintegral_mono (μ := μ) (fun m => P8bPairProof.rectangle f hf n m))
  simp_rw [hadd, lintegral_const, measure_univ, mul_one] at hrectangle
  have hswap := lintegral_lintegral_swap (μ := μ) (ν := μ)
    (f := f) (measurable_of_countable (Function.uncurry f)).aemeasurable
  apply (ENNReal.mul_le_mul_iff_right (a := 2) (by simp) (by simp)).mp
  simpa only [two_mul, ← hswap] using hrectangle

namespace P8bPairProof

/-- The product test has genuine increasing differences. -/
theorem productTest :
    Spec.SharedIncreasingDifferences (fun n m => ((n * m : ℕ) : ℝ≥0∞)) := by
  intro a b c d hab hcd
  dsimp only
  exact_mod_cast (mul_add_mul_le_mul_add_mul hab hcd)

/-- A concrete count law with two equiprobable outcomes. -/
noncomputable def fairCount : Measure ℕ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac 1

instance fairCount_probability : IsProbabilityMeasure fairCount where
  measure_univ := by
    norm_num [fairCount]
    rw [← two_mul]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- A strict example: sharing the same nonconstant count doubles the product
expectation from one quarter to one half. This also witnesses that the
increasing-differences premise is inhabited by a nonconstant test. -/
theorem strictSharedExample :
    (∫⁻ n, ∫⁻ m, ((n * m : ℕ) : ℝ≥0∞) ∂fairCount ∂fairCount) = 1 / 4 ∧
      (∫⁻ n, ((n * n : ℕ) : ℝ≥0∞) ∂fairCount) = 1 / 2 := by
  constructor <;> norm_num [fairCount, lintegral_add_measure, lintegral_dirac,
    lintegral_smul_measure]
  rw [← ENNReal.mul_inv (by simp) (by simp)]
  norm_num

end P8bPairProof

end RebuildBound
