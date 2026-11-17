import RebuildBound.Spec.P10

/-!
# P10: the stop-loss is 1-Lipschitz under a zero completion

For a root-loss law split as `μ = μg + μd` (good part and defect part), replace the
defect part by an atom at zero of the same mass, `μ' = μg + μd(ℕ) • δ₀`. Since
`(x + y - L)₊ ≤ (x - L)₊ + y`, one replacement raises the stop-loss of `ν ∗ μ` by at
most `∫ y dμd` (`stopLoss_step`); iterating over the `g` independent root losses
costs `g ∫ y dμd` (`stopLoss_iter`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.P10Proof

open RebuildBound.Spec

lemma isProb_natConvPow (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    ∀ g, IsProbabilityMeasure (natConvPow μ g)
  | 0 => by rw [natConvPow]; infer_instance
  | g + 1 => by
    have := isProb_natConvPow μ g
    rw [natConvPow]
    infer_instance

/-- The zero completion of the defect part. -/
noncomputable def zc (μg μd : Measure ℕ) : Measure ℕ := μg + μd Set.univ • Measure.dirac 0

lemma isProb_zc (μg μd : Measure ℕ) (h : IsProbabilityMeasure (μg + μd)) :
    IsProbabilityMeasure (zc μg μd) := by
  constructor
  rw [zc, Measure.add_apply, Measure.smul_apply, measure_univ (μ := Measure.dirac (0 : ℕ)),
    smul_eq_mul, mul_one,
    ← Measure.add_apply]
  exact h.measure_univ

lemma stopLoss_step (ν μg μd : Measure ℕ) [IsProbabilityMeasure ν] [IsFiniteMeasure μg]
    [IsFiniteMeasure μd] (L : ℕ) :
    stopLoss (ν ∗ (μg + μd)) L ≤ stopLoss (ν ∗ zc μg μd) L + ∫⁻ y, (y : ℝ≥0∞) ∂μd := by
  unfold stopLoss zc
  rw [Measure.lintegral_conv Measurable.of_discrete, Measure.lintegral_conv Measurable.of_discrete]
  calc ∫⁻ x, ∫⁻ y, ((x + y - L : ℕ) : ℝ≥0∞) ∂(μg + μd) ∂ν
      ≤ ∫⁻ x, (∫⁻ y, ((x + y - L : ℕ) : ℝ≥0∞) ∂(μg + μd Set.univ • Measure.dirac 0) +
          ∫⁻ y, (y : ℝ≥0∞) ∂μd) ∂ν := by
        refine lintegral_mono fun x => ?_
        rw [lintegral_add_measure, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac,
          add_assoc]
        gcongr
        calc ∫⁻ y, ((x + y - L : ℕ) : ℝ≥0∞) ∂μd
            ≤ ∫⁻ y, (((x - L : ℕ) : ℝ≥0∞) + (y : ℝ≥0∞)) ∂μd :=
              lintegral_mono fun y => by
                rw [← Nat.cast_add]
                exact Nat.cast_le.2 (by omega)
          _ = μd Set.univ • ((x + 0 - L : ℕ) : ℝ≥0∞) + ∫⁻ y, (y : ℝ≥0∞) ∂μd := by
              rw [lintegral_add_left measurable_const, lintegral_const, add_zero, smul_eq_mul,
                mul_comm]
    _ = ∫⁻ x, ∫⁻ y, ((x + y - L : ℕ) : ℝ≥0∞) ∂(μg + μd Set.univ • Measure.dirac 0) ∂ν +
          ∫⁻ y, (y : ℝ≥0∞) ∂μd := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ (μ := ν), mul_one]

lemma stopLoss_iter (μg μd : Measure ℕ) [IsFiniteMeasure μg] [IsFiniteMeasure μd]
    (hμ : IsProbabilityMeasure (μg + μd)) (L : ℕ) :
    ∀ (g : ℕ) (ν : Measure ℕ) [IsProbabilityMeasure ν],
      stopLoss (ν ∗ natConvPow (μg + μd) g) L ≤
        stopLoss (ν ∗ natConvPow (zc μg μd) g) L + g * ∫⁻ y, (y : ℝ≥0∞) ∂μd
  | 0, ν, _ => by simp [natConvPow]
  | g + 1, ν, _ => by
    have hz := isProb_zc μg μd hμ
    have h1 := isProb_natConvPow (μg + μd) g
    have h2 := isProb_natConvPow (zc μg μd) g
    have ih := stopLoss_iter μg μd hμ L g (ν ∗ zc μg μd)
    have hs := stopLoss_step (ν ∗ natConvPow (μg + μd) g) μg μd L
    rw [natConvPow, natConvPow, ← Measure.conv_assoc]
    have e1 : (ν ∗ natConvPow (μg + μd) g) ∗ zc μg μd =
        (ν ∗ zc μg μd) ∗ natConvPow (μg + μd) g := by
      rw [Measure.conv_assoc, Measure.conv_comm (natConvPow (μg + μd) g), ← Measure.conv_assoc]
    have e2 : (ν ∗ zc μg μd) ∗ natConvPow (zc μg μd) g =
        (ν ∗ natConvPow (zc μg μd) g) ∗ zc μg μd := by
      rw [Measure.conv_assoc, Measure.conv_comm (zc μg μd), ← Measure.conv_assoc]
    rw [e1] at hs
    rw [e2] at ih
    calc stopLoss ((ν ∗ natConvPow (μg + μd) g) ∗ (μg + μd)) L
        ≤ stopLoss ((ν ∗ zc μg μd) ∗ natConvPow (μg + μd) g) L + ∫⁻ y, (y : ℝ≥0∞) ∂μd := hs
      _ ≤ (stopLoss ((ν ∗ natConvPow (zc μg μd) g) ∗ zc μg μd) L +
            g * ∫⁻ y, (y : ℝ≥0∞) ∂μd) + ∫⁻ y, (y : ℝ≥0∞) ∂μd := by gcongr
      _ = stopLoss (ν ∗ (natConvPow (zc μg μd) g ∗ zc μg μd)) L +
            ((g + 1 : ℕ) : ℝ≥0∞) * ∫⁻ y, (y : ℝ≥0∞) ∂μd := by
          rw [Measure.conv_assoc]
          push_cast
          ring

end RebuildBound.P10Proof
