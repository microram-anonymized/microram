import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! Shared transfer from nonnegative rational allocations to finite probability sums. -/
open scoped ENNReal
namespace RebuildBound.RationalBudget

/-- A finite analytic sum is bounded by any pointwise nonnegative rational
allocation. Geometry and exposure counts are left to the caller. -/
lemma sum_ofReal_le {α : Type*} (xs : List α) (f : α → ℝ≥0∞) (q : α → ℚ)
    (hq : ∀ x ∈ xs, 0 ≤ q x)
    (hf : ∀ x ∈ xs, f x ≤ ENNReal.ofReal (q x : ℝ)) :
    (xs.map f).sum ≤ ENNReal.ofReal ((xs.map q).sum : ℝ) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hn := hq x List.mem_cons_self
    have ht : 0 ≤ (xs.map q).sum :=
      List.sum_nonneg (by simpa using fun y hy => hq y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons, List.sum_cons]
    calc
      _ ≤ ENNReal.ofReal (q x : ℝ) + ENNReal.ofReal ((xs.map q).sum : ℝ) :=
        add_le_add (hf x List.mem_cons_self)
          (ih (fun y hy => hq y (List.mem_cons_of_mem x hy))
            (fun y hy => hf y (List.mem_cons_of_mem x hy)))
      _ = _ := by
        rw [← ENNReal.ofReal_add (by exact_mod_cast hn) (by exact_mod_cast ht)]
        push_cast
        rfl


lemma weighted_sum_le {α : Type*} (xs : List α) (n : α → ℕ)
    (f : α → ℝ≥0∞) (q : α → ℚ) (hq : ∀ x ∈ xs, 0 ≤ q x)
    (hf : ∀ x ∈ xs, f x ≤ ENNReal.ofReal (q x : ℝ)) :
    (xs.map fun x => (n x : ℝ≥0∞) * f x).sum ≤
      ENNReal.ofReal ((xs.map fun x => (n x : ℚ) * q x).sum : ℝ) := by
  apply sum_ofReal_le
  · intro x hx
    exact mul_nonneg (Nat.cast_nonneg _) (hq x hx)
  · intro x hx
    calc
      _ ≤ (n x : ℝ≥0∞) * ENNReal.ofReal (q x : ℝ) := mul_le_mul' le_rfl (hf x hx)
      _ = _ := by
        push_cast
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

end RebuildBound.RationalBudget
