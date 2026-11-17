import RebuildBound.Spec.Subtotal

open scoped ENNReal NNReal

namespace RebuildBound

private lemma sub_arith (s : ℝ≥0∞) (h : s ≤ 7 / (10 * 2 ^ 70)) :
    s + 257 * ENNReal.ofReal (5845 / (10000 * 2 ^ 78)) ≤ ENNReal.ofReal (129 / (100 * 2 ^ 70)) := by
  have h7 : (7 : ℝ≥0∞) / (10 * 2 ^ 70) = ENNReal.ofReal (7 / (10 * 2 ^ 70)) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    simp [ENNReal.ofReal_mul, ENNReal.ofReal_pow]
  have h257 : (257 : ℝ≥0∞) = ENNReal.ofReal 257 := by simp
  calc s + 257 * ENNReal.ofReal (5845 / (10000 * 2 ^ 78))
      ≤ ENNReal.ofReal (7 / (10 * 2 ^ 70)) + ENNReal.ofReal 257 * ENNReal.ofReal (5845 / (10000 * 2 ^ 78)) := by
        rw [← h7, ← h257]; gcongr
    _ = ENNReal.ofReal (7 / (10 * 2 ^ 70) + 257 * (5845 / (10000 * 2 ^ 78))) := by
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by norm_num)

theorem Subtotal_of (h : Spec.SelOrd_statement) : Spec.Subtotal_statement :=
  ⟨sub_arith _ h.1, sub_arith _ h.2⟩

end RebuildBound
