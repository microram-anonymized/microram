import RebuildBound.Spec.Phase0

/-!
# X1: Pascal's rule for the binomial law

Mathlib's `ProbabilityTheory.binomial` has no recurrence in `n`. We derive
`Bin(n + 1, p) = (1 - p) • Bin(n, p) + p • (Bin(n, p)).map (· + 1)` from
`binomial_singleton` and Pascal's rule, its `lintegral` form, stochastic
monotonicity in `n`, and the support bound `m ≤ n`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.X1Proof

/-- The success probability as an extended real. -/
noncomputable def pe (p : I) : ℝ≥0∞ := ENNReal.ofReal (p : ℝ)

/-- The failure probability as an extended real. -/
noncomputable def qe (p : I) : ℝ≥0∞ := ENNReal.ofReal (1 - (p : ℝ))

lemma qe_add_pe (p : I) : qe p + pe p = 1 := by
  rw [qe, pe, ← ENNReal.ofReal_add (by linarith [unitInterval.le_one p]) (unitInterval.nonneg p),
    sub_add_cancel, ENNReal.ofReal_one]

lemma binomial_succ (n : ℕ) (p : I) :
    binomial (n + 1) p = qe p • binomial n p + pe p • (binomial n p).map (· + 1) := by
  have hp := unitInterval.nonneg p
  have hq : (0 : ℝ) ≤ 1 - p := by linarith [unitInterval.le_one p]
  refine Measure.ext_of_singleton fun k => ?_
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton _), smul_eq_mul, smul_eq_mul]
  rcases k with _ | j
  · have : (fun k : ℕ => k + 1) ⁻¹' {0} = ∅ := by ext; simp
    rw [this, measure_empty, mul_zero, add_zero, binomial_singleton, binomial_singleton, qe,
      ← ENNReal.ofReal_mul hq]
    congr 1
    simp [pow_succ]
    ring
  · have : (fun k : ℕ => k + 1) ⁻¹' {j + 1} = {j} := by ext; simp
    rw [this, binomial_singleton, binomial_singleton, binomial_singleton, qe, pe,
      ← ENNReal.ofReal_mul hq, ← ENNReal.ofReal_mul hp,
      ← ENNReal.ofReal_add (mul_nonneg hq binomial_nonneg) (mul_nonneg hp binomial_nonneg)]
    congr 1
    rw [Nat.choose_succ_succ', Nat.add_sub_add_right]
    push_cast
    rcases lt_or_ge j n with h | h
    · obtain ⟨d, hd⟩ : ∃ d, n - j = d + 1 := ⟨n - j - 1, by omega⟩
      have hd' : n - (j + 1) = d := by omega
      rw [hd, hd']
      ring
    · rw [Nat.choose_eq_zero_of_lt (by omega : n < j + 1)]
      push_cast
      ring

lemma lintegral_binomial_succ (n : ℕ) (p : I) (g : ℕ → ℝ≥0∞) :
    ∫⁻ k, g k ∂(binomial (n + 1) p) =
      qe p * ∫⁻ k, g k ∂(binomial n p) + pe p * ∫⁻ k, g (k + 1) ∂(binomial n p) := by
  rw [binomial_succ, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_map Measurable.of_discrete Measurable.of_discrete, smul_eq_mul, smul_eq_mul]

/-- Stochastic monotonicity of `Bin(n, p)` in `n`. -/
lemma lintegral_binomial_mono (p : I) {g : ℕ → ℝ≥0∞} (hg : Monotone g) {n n' : ℕ}
    (h : n ≤ n') : ∫⁻ k, g k ∂(binomial n p) ≤ ∫⁻ k, g k ∂(binomial n' p) := by
  induction n', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n' _ ih =>
    refine ih.trans ?_
    rw [lintegral_binomial_succ]
    calc ∫⁻ k, g k ∂(binomial n' p)
        = (qe p + pe p) * ∫⁻ k, g k ∂(binomial n' p) := by rw [qe_add_pe, one_mul]
      _ = qe p * ∫⁻ k, g k ∂(binomial n' p) + pe p * ∫⁻ k, g k ∂(binomial n' p) := add_mul _ _ _
      _ ≤ qe p * ∫⁻ k, g k ∂(binomial n' p) + pe p * ∫⁻ k, g (k + 1) ∂(binomial n' p) := by
        gcongr with k
        exact hg (Nat.le_succ k)

/-- `Bin(n, p)` is supported on `{0, …, n}`. -/
lemma ae_le_binomial (n : ℕ) (p : I) : ∀ᵐ k ∂(binomial n p), k ≤ n := by
  rw [ae_iff_of_countable]
  intro k hk
  by_contra h
  apply hk
  rw [binomial_singleton, Nat.choose_eq_zero_of_lt (by omega)]
  simp

end RebuildBound.X1Proof
