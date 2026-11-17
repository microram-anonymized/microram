import RebuildBound.Spec.P8bRate
import RebuildBound.Proofs.P8bPair
import RebuildBound.Proofs.P5b

/-!
# Increasing a shared Poisson rate at fixed marginal rates

The measure-based API suffices, including for infinite expectations. Independent
Poisson increments are expanded by convolution, reordered by Tonelli, and
replaced by a shared increment using P8bPair. No success conditioning appears.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RebuildBound.P8bRateProof

lemma poisson_add_integral (a b : ℝ≥0) (F : ℕ → ℝ≥0∞) :
    (∫⁻ s, F s ∂poissonMeasure (a + b)) =
      ∫⁻ x, ∫⁻ y, F (x + y) ∂poissonMeasure b ∂poissonMeasure a := by
  rw [← poissonMeasure_conv_poissonMeasure a b,
    Measure.lintegral_conv (measurable_of_countable F)]

lemma swap (a b : ℝ≥0) (F : ℕ → ℕ → ℝ≥0∞) :
    (∫⁻ x, ∫⁻ y, F x y ∂poissonMeasure b ∂poissonMeasure a) =
      ∫⁻ y, ∫⁻ x, F x y ∂poissonMeasure a ∂poissonMeasure b :=
  lintegral_lintegral_swap (measurable_of_countable (Function.uncurry F)).aemeasurable

lemma shifted (f : ℕ → ℕ → ℝ≥0∞) (hf : Spec.SharedIncreasingDifferences f)
    (x y z : ℕ) :
    Spec.SharedIncreasingDifferences (fun u v => f (x + u + z) (y + v + z)) := by
  intro a b c d hab hcd
  exact hf _ _ _ _ (by omega) (by omega)

end RebuildBound.P8bRateProof

namespace RebuildBound
open P8bRateProof

theorem P8bRate : Spec.P8bRate_statement := by
  intro a b gamma gamma' f hgg hga hgb hf
  let delta := gamma' - gamma
  have ha : a - gamma = (a - gamma') + delta := by
    dsimp [delta]
    exact (tsub_add_tsub_cancel hga hgg).symm
  have hb : b - gamma = (b - gamma') + delta := by
    dsimp [delta]
    exact (tsub_add_tsub_cancel hgb hgg).symm
  have hg : gamma + delta = gamma' := add_tsub_cancel_of_le hgg
  unfold Spec.sharedPoissonPair
  rw [ha, hb]
  calc
    _ = ∫⁻ z, ∫⁻ x, ∫⁻ y, ∫⁻ u, ∫⁻ v,
          f (x + u + z) (y + v + z)
          ∂poissonMeasure delta ∂poissonMeasure delta
          ∂poissonMeasure (b - gamma') ∂poissonMeasure (a - gamma')
          ∂poissonMeasure gamma := by
      apply lintegral_congr
      intro z
      rw [poisson_add_integral]
      apply lintegral_congr
      intro x
      simp_rw [poisson_add_integral]
      exact swap delta (b - gamma') _
    _ ≤ ∫⁻ z, ∫⁻ x, ∫⁻ y, ∫⁻ u, f (x + u + z) (y + u + z)
          ∂poissonMeasure delta ∂poissonMeasure (b - gamma')
          ∂poissonMeasure (a - gamma') ∂poissonMeasure gamma := by
      apply lintegral_mono
      intro z
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro y
      exact P8bPair (poissonMeasure delta) _ (shifted f hf x y z)
    _ = ∫⁻ z, ∫⁻ u, ∫⁻ x, ∫⁻ y, f (x + (z + u)) (y + (z + u))
          ∂poissonMeasure (b - gamma') ∂poissonMeasure (a - gamma')
          ∂poissonMeasure delta ∂poissonMeasure gamma := by
      apply lintegral_congr
      intro z
      simp_rw [swap (b - gamma') delta]
      rw [swap (a - gamma') delta]
      simp_rw [Nat.add_assoc, Nat.add_comm _ z]
    _ = ∫⁻ z, ∫⁻ x, ∫⁻ y, f (x + z) (y + z)
          ∂poissonMeasure (b - gamma') ∂poissonMeasure (a - gamma')
          ∂poissonMeasure gamma' := by
      simpa only [hg] using
        (poisson_add_integral gamma delta (fun z =>
          ∫⁻ x, ∫⁻ y, f (x + z) (y + z)
            ∂poissonMeasure (b - gamma') ∂poissonMeasure (a - gamma'))).symm

end RebuildBound
