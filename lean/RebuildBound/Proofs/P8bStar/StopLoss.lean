import RebuildBound.Spec.P8bStar
import RebuildBound.Spec.Prob.Tests
import Mathlib.Tactic

/-! The stop loss is supermodular along every center/leaf edge. The inner
excess sum is separable; applying the outer positive part preserves its
nonnegative mixed differences. No expectation or integrability premise enters. -/
namespace RebuildBound
open Spec
open scoped ENNReal

theorem P8bStarStopLoss : Spec.P8bStarStopLoss_statement := by
  intro n C S x i a b c d hab hcd
  let F (u v : ℕ) := ∑ j : Option (Fin n),
    (Function.update (Function.update x none u) (some i) v j - C)
  have mono (a b c d : ℕ) (hab : a ≤ b) (hcd : c ≤ d) : F a c ≤ F b d := by
    apply Finset.sum_le_sum
    intro v _
    by_cases hn : v = none
    · subst v
      simpa [Function.update] using Nat.sub_le_sub_right hab C
    · by_cases hi : v = some i
      · subst v
        simpa [Function.update] using Nat.sub_le_sub_right hcd C
      · simp [Function.update, hn, hi]
  have h₁ := mono a a c d (le_refl a) hcd
  have h₂ := mono a b c c hab (le_refl c)
  have h₃ := mono a b d d hab (le_refl d)
  have h₄ := mono b b c d (le_refl b) hcd
  have heq : F a d + F b c = F a c + F b d := by
    dsimp only [F]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hn : v = none
    · subst v; simp [Function.update]
    · by_cases hi : v = some i
      · subst v; simp [Function.update, Nat.add_comm]
      · simp [Function.update, hn, hi]
  change ((F a d - S : ℕ) : ℝ≥0∞) + ((F b c - S : ℕ) : ℝ≥0∞) ≤
    ((F a c - S : ℕ) : ℝ≥0∞) + ((F b d - S : ℕ) : ℝ≥0∞)
  rw [← Nat.cast_add, ← Nat.cast_add]
  exact_mod_cast (show (F a d - S) + (F b c - S) ≤ (F a c - S) + (F b d - S) by omega)

namespace P8bStarProof

lemma excess_mono {n C : ℕ} {x y : Option (Fin n) → ℕ} (h : x ≤ y) :
    (∑ j, (x j - C)) ≤ ∑ j, (y j - C) :=
  Finset.sum_le_sum fun j _ => Nat.sub_le_sub_right (h j) C

lemma stopLoss_mono (n C S : ℕ) : Monotone (starStopLoss n C S) := by
  intro x y h
  have hh := excess_mono (C := C) h
  unfold starStopLoss
  exact_mod_cast (Nat.sub_le_sub_right hh S)

lemma stopLoss_finite (n C S : ℕ) (x : Option (Fin n) → ℕ) :
    starStopLoss n C S x ≠ ∞ := ENNReal.natCast_ne_top _

/-- Keep a shared key's entire increment vector when applying per-key
Poissonization. This inequality holds for arbitrary nonnegative vectors. -/
lemma stopLoss_increments (n C S : ℕ) (x u v : Option (Fin n) → ℕ) :
    starStopLoss n C S (x + u) + starStopLoss n C S (x + v) ≤
      starStopLoss n C S (x + u + v) + starStopLoss n C S x := by
  have h₁ := excess_mono (C := C) (x := x) (y := x + u)
    (fun j => by simp)
  have h₂ := excess_mono (C := C) (x := x) (y := x + v)
    (fun j => by simp)
  have h₃ := excess_mono (C := C) (x := x + u) (y := x + u + v)
    (fun j => by simp)
  have h₄ := excess_mono (C := C) (x := x + v) (y := x + u + v)
    (fun j => by simp only [Pi.add_apply]; omega)
  have h₅ : (∑ j, ((x + u) j - C)) + (∑ j, ((x + v) j - C)) ≤
      (∑ j, ((x + u + v) j - C)) + ∑ j, (x j - C) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    simp only [Pi.add_apply]
    omega
  unfold starStopLoss
  rw [← Nat.cast_add, ← Nat.cast_add]
  exact_mod_cast (by omega : _)

lemma stopLoss_dirConvex (n C S : ℕ) : DirConvex (starStopLoss n C S) := by
  intro x k l
  exact stopLoss_increments n C S x (unitVec k) (unitVec l)

end P8bStarProof
end RebuildBound
