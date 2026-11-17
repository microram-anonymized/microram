import RebuildBound.Spec.Phase0

/-!
# X2: one-key Pois(1) replacement

`E f(x + V) ≤ E f(x + V₁ + ⋯ + V_K)` with `K ∼ Po(1)`, for a finite-valued
directionally convex `f`.

Proof outline.
1. `vecIneq`: from the unit-increment form of `DirConvex` and finiteness,
   `f (y + u) + f (y + v) ≤ f (y + u + v) + f y` for all vectors `u v`
   (done in `ℝ` through `toReal`).
2. `convPow_convex`: `g k = ∫⁻ v, f (x + v) ∂(convPow μ k)` is convex in `k`,
   by expanding `convPow μ (k + 2) = (convPow μ k ∗ μ) ∗ μ` with
   `Measure.lintegral_conv` and applying step 1 pointwise.
3. `poisson_jensen`: for a convex `g : ℕ → ℝ≥0∞` with `g 0 < ∞`,
   `g 1 ≤ ∑' k, Po(1){k} * g k`, via `k * g 1 + g 0 ≤ g k + k * g 0`,
   `∑ π_k = 1` and `∑ k π_k = 1`.
4. Unfold `compoundPoisson` with `lintegral_sum_measure` and
   `lintegral_smul_measure`.

The measure-based API sufficed; no PMF or finite-sum fallback was needed.
Every function on the countable discrete space `κ → ℕ` is measurable
(`Measurable.of_discrete`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RebuildBound.X2Proof

open RebuildBound.Spec

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-! ### Step 1: vector increments -/

/-- Nondecreasing along unit steps implies nondecreasing along any increment. -/
lemma le_add_of_unit {g : (κ → ℕ) → ℝ} (hg : ∀ y k, g y ≤ g (y + unitVec k))
    (y u : κ → ℕ) : g y ≤ g (y + u) := by
  have hsingle : ∀ (i : κ) (m : ℕ) (y : κ → ℕ), g y ≤ g (y + Pi.single i m) := by
    intro i m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      have : y + Pi.single i (m + 1) = (y + Pi.single i m) + unitVec i := by
        rw [unitVec, add_assoc, ← Pi.single_add]
      rw [this]
      exact (ih y).trans (hg _ _)
  have hs : ∀ (s : Finset κ) (y : κ → ℕ), g y ≤ g (y + ∑ i ∈ s, Pi.single i (u i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro y; simp
    | insert a s ha ih =>
      intro y
      rw [Finset.sum_insert ha, ← add_assoc]
      exact (hsingle a (u a) y).trans (ih _)
  simpa [Finset.univ_sum_single] using hs Finset.univ y

/-- Step 1 in `ℝ`. -/
lemma vecIneqReal {F : (κ → ℕ) → ℝ}
    (hF : ∀ y k l, F (y + unitVec k) + F (y + unitVec l) ≤ F (y + unitVec k + unitVec l) + F y)
    (y u v : κ → ℕ) : F (y + u) + F (y + v) ≤ F (y + u + v) + F y := by
  -- the unit increment in direction `l` is nondecreasing along any increment
  have hA : ∀ l (y w : κ → ℕ),
      F (y + unitVec l) - F y ≤ F (y + w + unitVec l) - F (y + w) := by
    intro l y w
    refine le_add_of_unit (g := fun y => F (y + unitVec l) - F y) ?_ y w
    intro z k
    have := hF z k l
    linarith
  -- hence so is the increment `u`
  have hB : ∀ (y w : κ → ℕ), F (y + u) - F y ≤ F (y + w + u) - F (y + w) := by
    intro y w
    refine le_add_of_unit (g := fun y => F (y + u) - F y) ?_ y w
    intro z k
    have := hA k z u
    rw [add_right_comm z (unitVec k) u]
    linarith
  have := hB y v
  rw [add_right_comm y v u] at this
  linarith

/-- Step 1: vector increments of a finite-valued directionally convex function. -/
lemma vecIneq {f : (κ → ℕ) → ℝ≥0∞} (hf : DirConvex f) (hfin : ∀ y, f y ≠ ∞)
    (y u v : κ → ℕ) : f (y + u) + f (y + v) ≤ f (y + u + v) + f y := by
  have hF : ∀ y k l, (f (y + unitVec k)).toReal + (f (y + unitVec l)).toReal ≤
      (f (y + unitVec k + unitVec l)).toReal + (f y).toReal := by
    intro y k l
    rw [← ENNReal.toReal_add (hfin _) (hfin _), ← ENNReal.toReal_add (hfin _) (hfin _)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin _, hfin _⟩) (hf y k l)
  have := vecIneqReal (F := fun y => (f y).toReal) hF y u v
  rw [← ENNReal.toReal_add (hfin _) (hfin _), ← ENNReal.toReal_add (hfin _) (hfin _)] at this
  exact (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.2 ⟨hfin _, hfin _⟩)
    (ENNReal.add_ne_top.2 ⟨hfin _, hfin _⟩)).1 this

/-! ### Step 2: convexity in the number of summands -/

omit [DecidableEq κ] in
/-- For a probability measure, a double integral of a sum of one-variable functions. -/
lemma lintegral_lintegral_add (μ : Measure (κ → ℕ)) [IsProbabilityMeasure μ]
    (F G : (κ → ℕ) → ℝ≥0∞) :
    ∫⁻ a, ∫⁻ b, (F a + G b) ∂μ ∂μ = ∫⁻ a, F a ∂μ + ∫⁻ b, G b ∂μ := by
  simp [lintegral_add_left, Measurable.of_discrete, lintegral_const]

omit [DecidableEq κ] in
lemma convPow_convex (F : (κ → ℕ) → ℝ≥0∞)
    (hF : ∀ s a b, F (s + a) + F (s + b) ≤ F (s + a + b) + F s)
    (μ : Measure (κ → ℕ)) [IsProbabilityMeasure μ] (k : ℕ) :
    ∫⁻ v, F v ∂(convPow μ (k + 1)) + ∫⁻ v, F v ∂(convPow μ (k + 1)) ≤
      ∫⁻ v, F v ∂(convPow μ (k + 2)) + ∫⁻ v, F v ∂(convPow μ k) := by
  have h1 : ∫⁻ v, F v ∂(convPow μ (k + 1)) = ∫⁻ s, ∫⁻ a, F (s + a) ∂μ ∂(convPow μ k) :=
    Measure.lintegral_conv Measurable.of_discrete
  have h2 : ∫⁻ v, F v ∂(convPow μ (k + 2)) =
      ∫⁻ s, ∫⁻ a, ∫⁻ b, F (s + a + b) ∂μ ∂μ ∂(convPow μ k) := by
    change ∫⁻ v, F v ∂((convPow μ k ∗ μ) ∗ μ) = _
    rw [Measure.lintegral_conv Measurable.of_discrete,
      Measure.lintegral_conv Measurable.of_discrete]
  have h0 : ∫⁻ v, F v ∂(convPow μ k) = ∫⁻ s, ∫⁻ a, ∫⁻ b, F s ∂μ ∂μ ∂(convPow μ k) := by
    simp [lintegral_const]
  rw [h1, h2, h0, ← lintegral_add_left Measurable.of_discrete,
    ← lintegral_add_left Measurable.of_discrete]
  refine lintegral_mono fun s => ?_
  have eL : ∫⁻ a, F (s + a) ∂μ + ∫⁻ a, F (s + a) ∂μ =
      ∫⁻ a, ∫⁻ b, (F (s + a) + F (s + b)) ∂μ ∂μ :=
    (lintegral_lintegral_add μ (fun a => F (s + a)) (fun b => F (s + b))).symm
  have eR : ∫⁻ a, ∫⁻ b, F (s + a + b) ∂μ ∂μ + ∫⁻ a, ∫⁻ b, F s ∂μ ∂μ =
      ∫⁻ a, ∫⁻ b, (F (s + a + b) + F s) ∂μ ∂μ := by
    rw [← lintegral_add_left Measurable.of_discrete]
    refine lintegral_congr fun a => ?_
    rw [← lintegral_add_left Measurable.of_discrete]
  rw [eL, eR]
  exact lintegral_mono fun a => lintegral_mono fun b => hF s a b

/-! ### Step 3: Jensen for `K ∼ Po(1)` -/

lemma real_convex_lin (G : ℕ → ℝ) (hG : ∀ k, G (k + 1) + G (k + 1) ≤ G (k + 2) + G k) (k : ℕ) :
    (k : ℝ) * G 1 + G 0 ≤ G k + k * G 0 := by
  have hd : ∀ k, G 1 - G 0 ≤ G (k + 1) - G k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => have := hG k; linarith
  induction k with
  | zero => simp
  | succ k ih => have := hd k; push_cast; linarith

lemma ennreal_convex_lin (g : ℕ → ℝ≥0∞) (hg : ∀ k, g (k + 1) + g (k + 1) ≤ g (k + 2) + g k)
    (hfin : ∀ k, g k ≠ ∞) (k : ℕ) : (k : ℝ≥0∞) * g 1 + g 0 ≤ g k + k * g 0 := by
  have hG : ∀ k, (g (k + 1)).toReal + (g (k + 1)).toReal ≤ (g (k + 2)).toReal + (g k).toReal := by
    intro k
    rw [← ENNReal.toReal_add (hfin _) (hfin _), ← ENNReal.toReal_add (hfin _) (hfin _)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin _, hfin _⟩) (hg k)
  have := real_convex_lin (fun k => (g k).toReal) hG k
  have hk1 : (k : ℝ≥0∞) * g 1 ≠ ∞ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top k) (hfin 1)
  have hk0 : (k : ℝ≥0∞) * g 0 ≠ ∞ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top k) (hfin 0)
  rw [← ENNReal.toReal_le_toReal (ENNReal.add_ne_top.2 ⟨hk1, hfin _⟩)
    (ENNReal.add_ne_top.2 ⟨hfin _, hk0⟩), ENNReal.toReal_add hk1 (hfin _),
    ENNReal.toReal_add (hfin _) hk0, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_natCast]
  exact this

/-- The Poisson(1) weights. -/
lemma poisson_one_singleton (k : ℕ) :
    poissonMeasure 1 {k} = ENNReal.ofReal (Real.exp (-1) / k.factorial) := by
  rw [poissonMeasure_singleton]
  simp

lemma poisson_one_ne_zero (k : ℕ) : poissonMeasure 1 {k} ≠ 0 := by
  rw [poisson_one_singleton]
  exact (ENNReal.ofReal_pos.2 (by positivity)).ne'

lemma tsum_poisson_one : ∑' k, poissonMeasure 1 {k} = 1 := by
  have h := hasSum_one_poissonMeasure 1
  simp only [NNReal.coe_one, one_pow, mul_one] at h
  simp_rw [poisson_one_singleton]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) h.summable, h.tsum_eq,
    ENNReal.ofReal_one]

lemma poisson_one_succ_mul (k : ℕ) :
    poissonMeasure 1 {k + 1} * ((k + 1 : ℕ) : ℝ≥0∞) = poissonMeasure 1 {k} := by
  rw [poisson_one_singleton, poisson_one_singleton, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp

lemma tsum_poisson_one_mul : ∑' k, poissonMeasure 1 {k} * (k : ℝ≥0∞) = 1 := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, mul_zero, zero_add]
  simp_rw [poisson_one_succ_mul]
  exact tsum_poisson_one

lemma poisson_jensen (g : ℕ → ℝ≥0∞) (hg : ∀ k, g (k + 1) + g (k + 1) ≤ g (k + 2) + g k)
    (h0 : g 0 ≠ ∞) : g 1 ≤ ∑' k, poissonMeasure 1 {k} * g k := by
  by_cases htop : ∃ k, g k = ∞
  · obtain ⟨k, hk⟩ := htop
    calc g 1 ≤ ∞ := le_top
      _ = poissonMeasure 1 {k} * g k := by rw [hk, ENNReal.mul_top (poisson_one_ne_zero k)]
      _ ≤ ∑' k, poissonMeasure 1 {k} * g k :=
        ENNReal.le_tsum (f := fun k => poissonMeasure 1 {k} * g k) k
  simp only [not_exists] at htop
  have hlin := ennreal_convex_lin g hg htop
  refine ENNReal.le_of_add_le_add_right h0 ?_
  calc g 1 + g 0
      = ∑' k, poissonMeasure 1 {k} * ((k : ℝ≥0∞) * g 1 + g 0) := by
        simp_rw [mul_add, ← mul_assoc]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right,
          tsum_poisson_one_mul, tsum_poisson_one, one_mul, one_mul]
    _ ≤ ∑' k, poissonMeasure 1 {k} * (g k + (k : ℝ≥0∞) * g 0) :=
        ENNReal.tsum_le_tsum fun k => mul_le_mul_right (hlin k) _
    _ = ∑' k, poissonMeasure 1 {k} * g k + g 0 := by
        simp_rw [mul_add, ← mul_assoc]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_poisson_one_mul, one_mul]

end RebuildBound.X2Proof

open RebuildBound.Spec RebuildBound.X2Proof in
theorem RebuildBound.X2 : RebuildBound.Spec.X2_statement := by
  intro κ _ _ f hf hfin μ _ x
  set F : (κ → ℕ) → ℝ≥0∞ := fun v => f (x + v) with hFdef
  have hF : ∀ s a b, F (s + a) + F (s + b) ≤ F (s + a + b) + F s := by
    intro s a b
    have := vecIneq hf hfin (x + s) a b
    simpa [F, add_assoc] using this
  set g : ℕ → ℝ≥0∞ := fun k => ∫⁻ v, F v ∂(convPow μ k) with hgdef
  have hconv : ∀ k, g (k + 1) + g (k + 1) ≤ g (k + 2) + g k :=
    fun k => convPow_convex F hF μ k
  have hg0 : g 0 ≠ ∞ := by
    simp only [g, convPow, lintegral_dirac]
    exact hfin _
  have hg1 : g 1 = ∫⁻ v, f (x + v) ∂μ := by
    simp only [g, convPow, Measure.dirac_zero_conv, hFdef]
  have hrhs : ∫⁻ v, f (x + v) ∂(compoundPoisson 1 μ) = ∑' k, poissonMeasure 1 {k} * g k := by
    simp only [compoundPoisson, lintegral_sum_measure, lintegral_smul_measure, g, F, smul_eq_mul]
  rw [hrhs, ← hg1]
  exact poisson_jensen g hconv hg0
