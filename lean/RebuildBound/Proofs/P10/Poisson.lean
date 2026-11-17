import RebuildBound.Proofs.X1.Binomial
import RebuildBound.Spec.P10

/-!
# P10: binomial and Poisson facts

* `binomial_conv`: `Bin(a, p) ∗ Bin(b, p) = Bin(a + b, p)`, by induction on `b`
  with Pascal's rule (`X1Proof.binomial_succ`).
* `poisson_bind_binomial`: binomial thinning of `Po(r)` by `p` is `Po(r p)`.
* `lintegral_sq_poisson`: `E[N²] = r + r²` for `N ∼ Po(r)`.
* `poisson_tail_le`: `P(Po(ν) > H) ≤ τ_H(ν)` for `ν < H + 2`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Nat

namespace RebuildBound.P10Proof

open RebuildBound.X1Proof

/-- `Bin(a, p) ∗ Bin(b, p) = Bin(a + b, p)`. -/
lemma binomial_conv (a b : ℕ) (p : I) :
    binomial a p ∗ binomial b p = binomial (a + b) p := by
  induction b with
  | zero => simp [binomial_zero]
  | succ b ih =>
    rw [← add_assoc, binomial_succ, binomial_succ, Measure.conv_add, Measure.conv_smul_right,
      Measure.conv_smul_right, ih, ← Measure.conv_dirac (binomial b p), ← Measure.conv_assoc, ih,
      Measure.conv_dirac]

/-- The success probability as a nonnegative real. -/
noncomputable def pNN (p : I) : ℝ≥0 := ⟨(p : ℝ), unitInterval.nonneg p⟩

/-- Binomial thinning of a Poisson law: `Po(r)` thinned by `p` is `Po(r p)`. -/
lemma poisson_bind_binomial (r : ℝ≥0) (p : I) :
    (poissonMeasure r).bind (fun n => binomial n p) = poissonMeasure (r * pNN p) := by
  refine Measure.ext_of_singleton fun k => ?_
  rw [Measure.bind_apply (measurableSet_singleton k) Measurable.of_discrete.aemeasurable,
    lintegral_countable', poissonMeasure_singleton]
  have hp := unitInterval.nonneg p
  have hq : (0 : ℝ) ≤ 1 - p := by linarith [unitInterval.le_one p]
  set f : ℕ → ℝ := fun n => Real.exp (-r) * r ^ n / (n ! : ℝ) *
    ((n.choose k) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  have hsum : HasSum f (Real.exp (-((r : ℝ) * p)) * ((r : ℝ) * p) ^ k / (k ! : ℝ)) := by
    rw [← hasSum_nat_add_iff' k]
    have h0 : ∑ i ∈ Finset.range k, f i = 0 := Finset.sum_eq_zero fun i hi => by
      simp [f, Nat.choose_eq_zero_of_lt (Finset.mem_range.1 hi)]
    rw [h0, sub_zero]
    have he := (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * (1 - p))).mul_left
      (Real.exp (-r) * ((r : ℝ) * p) ^ k / (k ! : ℝ))
    rw [← Real.exp_eq_exp_ℝ] at he
    convert he using 1
    · funext m
      simp only [f]
      rw [show m + k = k + m from add_comm _ _, Nat.cast_add_choose, Nat.add_sub_cancel_left]
      have h1 : ((k + m)! : ℝ) ≠ 0 := by positivity
      have h2 : (k ! : ℝ) ≠ 0 := by positivity
      have h3 : (m ! : ℝ) ≠ 0 := by positivity
      simp only [mul_pow]
      field_simp
      ring
    · have : Real.exp (-((r : ℝ) * p)) = Real.exp (-r) * Real.exp ((r : ℝ) * (1 - p)) := by
        rw [← Real.exp_add]
        ring_nf
      rw [this]
      ring
  calc ∑' n, binomial n p {k} * poissonMeasure r {n}
      = ∑' n, ENNReal.ofReal (f n) := by
        refine tsum_congr fun n => ?_
        rw [binomial_singleton, poissonMeasure_singleton, mul_comm,
          ← ENNReal.ofReal_mul (by positivity)]
    _ = _ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hsum.summable, hsum.tsum_eq]
        rfl

/-! ### Moments -/

lemma poisson_succ_mul (r : ℝ≥0) (k : ℕ) :
    poissonMeasure r {k + 1} * ((k + 1 : ℕ) : ℝ≥0∞) = (r : ℝ≥0∞) * poissonMeasure r {k} := by
  rw [poissonMeasure_singleton, poissonMeasure_singleton, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  have : (k ! : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma tsum_poisson (r : ℝ≥0) : ∑' k, poissonMeasure r {k} = 1 := by
  have h := hasSum_one_poissonMeasure r
  simp_rw [poissonMeasure_singleton]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) h.summable, h.tsum_eq,
    ENNReal.ofReal_one]

lemma tsum_poisson_mul (r : ℝ≥0) :
    ∑' k, poissonMeasure r {k} * (k : ℝ≥0∞) = r := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, mul_zero, zero_add]
  simp_rw [poisson_succ_mul]
  rw [ENNReal.tsum_mul_left, tsum_poisson, mul_one]

lemma tsum_poisson_mul_sq (r : ℝ≥0) :
    ∑' k, poissonMeasure r {k} * (k : ℝ≥0∞) ^ 2 = r + r ^ 2 := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_add]
  have h : ∀ k : ℕ, poissonMeasure r {k + 1} * ((k + 1 : ℕ) : ℝ≥0∞) ^ 2 =
      (r : ℝ≥0∞) * (poissonMeasure r {k} * k + poissonMeasure r {k}) := by
    intro k
    rw [sq, ← mul_assoc, poisson_succ_mul, Nat.cast_succ]
    ring
  simp_rw [h]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, tsum_poisson_mul, tsum_poisson]
  ring

/-- `E[N²] = r + r²` for `N ∼ Po(r)`. -/
lemma lintegral_sq_poisson (r : ℝ≥0) :
    ∫⁻ n, (n : ℝ≥0∞) ^ 2 ∂(poissonMeasure r) = r + r ^ 2 := by
  rw [lintegral_countable', ← tsum_poisson_mul_sq r]
  exact tsum_congr fun n => mul_comm _ _

/-! ### The tail -/

lemma poissonTail_nonneg {H : ℕ} {ν : ℝ} (h0 : 0 ≤ ν) (h : ν < H + 2) :
    0 ≤ Spec.poissonTail H ν := by
  unfold Spec.poissonTail
  have : ν / (H + 2) < 1 := (div_lt_one (by positivity)).2 h
  have : 0 < 1 - ν / (H + 2) := by linarith
  positivity

/-- `P(Po(ν) > H) ≤ τ_H(ν)` for `ν < H + 2`: the terms after `H + 1` are dominated by a
geometric series of ratio `ν / (H + 2)`. -/
lemma poisson_tail_le (r : ℝ≥0) (H : ℕ) (hr : (r : ℝ) < H + 2) :
    poissonMeasure r {n | H < n} ≤ ENNReal.ofReal (Spec.poissonTail H r) := by
  have hset : {n : ℕ | H < n} = ⋃ m : ℕ, {m + (H + 1)} := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · intro h
      exact ⟨n - (H + 1), by omega⟩
    · rintro ⟨m, rfl⟩
      omega
  rw [hset, measure_iUnion (fun i j hij => Set.disjoint_singleton.2 (by omega))
    (fun _ => measurableSet_singleton _)]
  set a : ℝ := Real.exp (-r) * (r : ℝ) ^ (H + 1) / ((H + 1)! : ℝ) with ha
  set q : ℝ := (r : ℝ) / (H + 2) with hq
  have hr0 : (0 : ℝ) ≤ r := r.2
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := (div_lt_one (by positivity)).2 hr
  have hgeo := (hasSum_geometric_of_lt_one hq0 hq1).mul_left a
  have htail : Spec.poissonTail H r = a * (1 - q)⁻¹ := by
    simp only [Spec.poissonTail, ha, hq, div_eq_mul_inv]
  have hterm : ∀ m : ℕ, poissonMeasure r {m + (H + 1)} ≤ ENNReal.ofReal (a * q ^ m) := by
    intro m
    rw [poissonMeasure_singleton]
    refine ENNReal.ofReal_le_ofReal ?_
    have hfac : ((H + 1)! : ℝ) * ((H + 2 : ℕ) : ℝ) ^ m ≤ ((m + (H + 1))! : ℝ) := by
      have := @Nat.factorial_mul_pow_le_factorial (H + 1) m
      rw [show H + 1 + m = m + (H + 1) by omega] at this
      exact_mod_cast this
    have hpos : (0 : ℝ) < ((H + 1)! : ℝ) * ((H + 2 : ℕ) : ℝ) ^ m := by positivity
    calc Real.exp (-r) * (r : ℝ) ^ (m + (H + 1)) / ((m + (H + 1))! : ℝ)
        ≤ Real.exp (-r) * (r : ℝ) ^ (m + (H + 1)) / (((H + 1)! : ℝ) * ((H + 2 : ℕ) : ℝ) ^ m) :=
          div_le_div_of_nonneg_left (by positivity) hpos hfac
      _ = a * q ^ m := by
          rw [ha, hq, div_pow]
          push_cast
          have : ((H : ℝ) + 2) ≠ 0 := by positivity
          have : ((H + 1)! : ℝ) ≠ 0 := by positivity
          field_simp
          ring
  calc ∑' m : ℕ, poissonMeasure r {m + (H + 1)}
      ≤ ∑' m : ℕ, ENNReal.ofReal (a * q ^ m) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (Spec.poissonTail H r) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hgeo.summable, hgeo.tsum_eq,
          htail]

end RebuildBound.P10Proof
