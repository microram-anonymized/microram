import RebuildBound.Spec.P8bStar
import Mathlib.Tactic.NormNum

/-! Kernel-checked nonzero-rate and strict stop-loss examples. -/
open RebuildBound.Spec
open scoped NNReal ENNReal

example : DenseStarShape 8 2 := by norm_num [DenseStarShape]
example : denseStarCenter 32 8 2 (31 / 32) = 417 / 14 := by
  have h : (1 : ℝ≥0) - 31 / 448 = 417 / 448 :=
    (tsub_eq_iff_eq_add_of_le ((div_le_one₀ (by norm_num)).2 (by norm_num))).2 (by norm_num)
  norm_num [denseStarCenter, h]
example : denseStarShared 32 8 1 = 32 / 7 := by
  norm_num [denseStarShared]
example : 3 * denseStarShared 32 8 1 + 225 / 14 =
    denseStarCenter 32 8 2 (31 / 32) := by
  have h : (1 : ℝ≥0) - 31 / 448 = 417 / 448 :=
    (tsub_eq_iff_eq_add_of_le ((div_le_one₀ (by norm_num)).2 (by norm_num))).2 (by norm_num)
  norm_num [denseStarCenter, denseStarShared, h]

private def counts (a b : ℕ) : Option (Fin 1) → ℕ
  | none => a
  | some _ => b

example : starStopLoss 1 64 1 (counts 64 64) = 0 := by
  norm_num [starStopLoss, counts, Fintype.sum_option, Fin.sum_univ_one]
example : starStopLoss 1 64 1 (counts 65 64) = 0 := by
  norm_num [starStopLoss, counts, Fintype.sum_option, Fin.sum_univ_one]
example : starStopLoss 1 64 1 (counts 64 65) = 0 := by
  norm_num [starStopLoss, counts, Fintype.sum_option, Fin.sum_univ_one]
example : starStopLoss 1 64 1 (counts 65 65) = 1 := by
  norm_num [starStopLoss, counts, Fintype.sum_option, Fin.sum_univ_one]
