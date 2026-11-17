import RebuildBound.Spec.Prob.Subset
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! Finite weighted laws. Union bounds need no normalization; probability
normalization and the P3 adapter explicitly require normalized history weights
and a nonempty word space. Geometry and operational contracts stay in consumers. -/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.FiniteLawProof

open RebuildBound.Spec

variable {Hist Word Value : Type} [Fintype Hist] [Fintype Word]
    (weight : Hist → ℝ≥0∞) (wordFn : Word → Value)

noncomputable def prob (E : Hist → Value → Prop) : ℝ≥0∞ := by
  classical
  exact ∑ hist, weight hist * ((Fintype.card Word : ℝ≥0∞)⁻¹ *
    ∑ h, if E hist (wordFn h) then 1 else 0)

theorem card_words_ne_zero [Nonempty Word] : (Fintype.card Word : ℝ≥0∞) ≠ 0 := by
  exact_mod_cast (Fintype.card_pos (α := Word)).ne'

/-- Monotonicity of `prob`; only the word functions `wordFn h` matter. -/
theorem prob_mono {E F : Hist → Value → Prop}
    (h : ∀ hist hw, E hist (wordFn hw) → F hist (wordFn hw)) : prob weight wordFn E ≤ prob weight wordFn F := by
  classical
  unfold prob
  gcongr with hist _ hw _
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h hist hw h1) h2
  · exact zero_le
  · exact le_rfl

/-- Subadditivity of `prob`. -/
theorem prob_or (E F : Hist → Value → Prop) :
    prob weight wordFn (fun hist w => E hist w ∨ F hist w) ≤ prob weight wordFn E + prob weight wordFn F := by
  classical
  unfold prob
  rw [← Finset.sum_add_distrib]
  gcongr with hist _
  rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib]
  gcongr with hw _
  split_ifs <;> simp_all

/-- Finite subadditivity of `prob`. -/
theorem prob_exists_lt (n : ℕ) (E : ℕ → Hist → Value → Prop) :
    prob weight wordFn (fun hist w => ∃ j < n, E j hist w) ≤ ∑ j ∈ Finset.range n, prob weight wordFn (E j) := by
  classical
  induction n with
  | zero => simp [prob]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc prob weight wordFn (fun hist w => ∃ j < n + 1, E j hist w)
        ≤ prob weight wordFn (fun hist w => (∃ j < n, E j hist w) ∨ E n hist w) := by
          refine prob_mono weight wordFn fun hist hw ⟨j, hj, he⟩ => ?_
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · exact Or.inl ⟨j, hj, he⟩
          · exact Or.inr he
      _ ≤ _ := prob_or weight wordFn _ _
      _ ≤ _ := by gcongr

/-- Cover an event by finitely many events, without normalization assumptions. -/
theorem prob_le_cover (E : Hist → Value → Prop) (F : ℕ → Hist → Value → Prop)
    (n : ℕ) (h : ∀ hist hw, E hist (wordFn hw) → ∃ j < n, F j hist (wordFn hw)) :
    prob weight wordFn E ≤ ∑ j ∈ Finset.range n, prob weight wordFn (F j) :=
  (prob_mono weight wordFn h).trans (prob_exists_lt weight wordFn n F)

/-- First-moment domination needs no normalized or nonempty sample space. -/
theorem prob_le_sum (E : Hist → Value → Prop) (f : Hist → Word → ℝ≥0∞)
    (hE : ∀ hist h, E hist (wordFn h) → 1 ≤ f hist h) :
    prob weight wordFn E ≤ ∑ hist, weight hist *
      ((Fintype.card Word : ℝ≥0∞)⁻¹ * ∑ h, f hist h) := by
  classical
  unfold prob
  gcongr with hist _ h _
  split_ifs with h1
  · exact hE hist h h1
  · exact zero_le

/-- Only collapsing history weights requires their normalization. -/
theorem prob_le_avg (hw : ∑ hist, weight hist = 1) (E : Hist → Value → Prop)
    (f : Word → ℝ≥0∞) (hE : ∀ hist h, E hist (wordFn h) → 1 ≤ f h) :
    prob weight wordFn E ≤ (Fintype.card Word : ℝ≥0∞)⁻¹ * ∑ h, f h := by
  refine le_trans (prob_le_sum weight wordFn E (fun _ h => f h) hE) ?_
  rw [← Finset.sum_mul, hw, one_mul]

/-- The pushforward of a finite weighted law under a count vector. -/
noncomputable def pushLaw {n : ℕ} (X : Hist → Word → Fin n → ℕ) :
    Measure (Fin n → ℕ) :=
  ∑ hist, weight hist • ((Fintype.card Word : ℝ≥0∞)⁻¹ •
    ∑ h, Measure.dirac (X hist h))

theorem pushLaw_apply {n : ℕ} (X : Hist → Word → Fin n → ℕ)
    (s : Set (Fin n → ℕ)) :
    pushLaw weight X s = ∑ hist, weight hist *
      ((Fintype.card Word : ℝ≥0∞)⁻¹ * ∑ h, s.indicator 1 (X hist h)) := by
  classical
  simp [pushLaw, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply]

theorem pushLaw_lintegral {n : ℕ} (X : Hist → Word → Fin n → ℕ)
    (f : (Fin n → ℕ) → ℝ≥0∞) :
    ∫⁻ x, f x ∂(pushLaw weight X) = ∑ hist, weight hist *
      ((Fintype.card Word : ℝ≥0∞)⁻¹ * ∑ h, f (X hist h)) := by
  classical
  simp [pushLaw, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac]

theorem pushLaw_prob [Nonempty Word] (hw : ∑ hist, weight hist = 1) {n : ℕ}
    (X : Hist → Word → Fin n → ℕ) :
    IsProbabilityMeasure (pushLaw weight X) := by
  classical
  constructor
  rw [pushLaw_apply]
  simp only [Set.indicator_univ, Pi.one_apply, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  rw [ENNReal.inv_mul_cancel (card_words_ne_zero (Word := Word)) (ENNReal.natCast_ne_top _)]
  simpa using hw

/-- **P3 applied to a finite weighted law.** A demand event of (history, words) whose
excess is at most `Σ_v (X_v - C)` of a count vector with the subset MGF
envelope has probability at most `Bsub`. -/
theorem prob_le_Bsub [Nonempty Word] (h3 : P3_statement) (hw : ∑ hist, weight hist = 1)
    {n : ℕ} (C S : ℕ) (lam D : ℝ) (hlam : 0 < lam) (hC : lam ≤ C) (hD : 0 ≤ D)
    (X : Hist → Word → Fin n → ℕ)
    (hmgf : ∀ (J : Finset (Fin n)) (z : ℝ), 1 ≤ z →
      ∑ hist, weight hist * ((Fintype.card Word : ℝ≥0∞)⁻¹ *
        ∑ h, ENNReal.ofReal (z ^ ∑ v ∈ J, X hist h v)) ≤
        ENNReal.ofReal (D * Real.exp (lam * J.card * (z - 1))))
    (E : Hist → Value → Prop)
    (hE : ∀ hist h, E hist (wordFn h) → S < ∑ v, (X hist h v - C)) :
    prob weight wordFn E ≤ ENNReal.ofReal (Bsub n C lam S D) := by
  classical
  have := pushLaw_prob weight hw X
  have key := h3 n C S lam D (pushLaw weight X) inferInstance hlam hC hD
    (fun J z hz => by rw [pushLaw_lintegral]; exact hmgf J z hz)
  refine le_trans ?_ key
  rw [pushLaw_apply]
  unfold prob
  gcongr with hist _ h _
  split_ifs with hE'
  · have := hE hist h hE'
    simp [Set.indicator, this]
  · exact zero_le

end RebuildBound.FiniteLawProof
