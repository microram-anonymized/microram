import RebuildBound.Spec.P7
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp

open PowerSeries Finset
open scoped BigOperators

namespace RebuildBound
open Spec

namespace P7algAux

lemma cauchyPow_eq (q : ℕ → ℝ) (n k : ℕ) :
    cauchyPow q n k = coeff k ((PowerSeries.mk q) ^ n) := by
  induction n generalizing k with
  | zero => simp [cauchyPow, coeff_one]
  | succ n ih => simp [cauchyPow, pow_succ, coeff_mul, ih]

lemma cauchyPow_nonneg (q : ℕ → ℝ) (hq : ∀ j, 0 ≤ q j) (n k : ℕ) : 0 ≤ cauchyPow q n k := by
  induction n generalizing k with
  | zero => simp only [cauchyPow]; split_ifs <;> norm_num
  | succ n ih =>
    simp only [cauchyPow]
    exact Finset.sum_nonneg fun ij _ => mul_nonneg (ih _) (hq _)

lemma cauchyPow_mono (q r : ℕ → ℝ) (hq : ∀ j, 0 ≤ q j) (hqr : ∀ j, q j ≤ r j) (n k : ℕ) :
    cauchyPow q n k ≤ cauchyPow r n k := by
  induction n generalizing k with
  | zero => simp [cauchyPow]
  | succ n ih =>
    simp only [cauchyPow]
    exact Finset.sum_le_sum fun ij _ =>
      mul_le_mul (ih _) (hqr _) (hq _) (cauchyPow_nonneg r (fun j => (hq j).trans (hqr j)) _ _)

variable (C : ℕ) (lam : ℝ)

noncomputable def Wc : ℕ → ℝ := fun j => if j = 0 then 0 else seriesW C lam j

noncomputable def Ws : ℝ⟦X⟧ := PowerSeries.mk (Wc C lam)

lemma Ws_coeff_lt (m k : ℕ) (h : k < m) : coeff k (Ws C lam ^ m) = 0 := by
  have h1 : (X : ℝ⟦X⟧) ∣ Ws C lam := by
    rw [X_dvd_iff]; simp [Ws, Wc]
  have h2 := pow_dvd_pow_of_dvd h1 m
  exact (X_pow_dvd_iff.mp h2) k h

lemma Ws_deriv (m k : ℕ) :
    ((k : ℝ) + 1) * coeff (k + 1) (Ws C lam ^ (m + 1)) =
      ((m : ℝ) + 1) * ∑ ij ∈ antidiagonal k,
        coeff ij.1 (Ws C lam ^ m) * (((ij.2 : ℝ) + 1) * seriesW C lam (ij.2 + 1)) := by
  have h := congrArg (coeff k) (derivative_pow (Ws C lam) (m + 1))
  rw [coeff_derivative] at h
  have h2 : d⁄dX (Ws C lam) = PowerSeries.mk (fun j => ((j : ℝ) + 1) * seriesW C lam (j + 1)) := by
    ext j; rw [coeff_derivative]; simp [Ws, Wc, mul_comm]
  rw [h2] at h
  have h3 : ∀ (f : ℝ⟦X⟧) (n : ℕ), coeff k ((n : ℝ⟦X⟧) * f) = n * coeff k f := by
    intro f n
    rw [← map_natCast (PowerSeries.C (R := ℝ)), coeff_C_mul]
  rw [Nat.add_sub_cancel, mul_assoc, h3, coeff_mul] at h
  push_cast at h
  rw [mul_comm, h]
  simp only [coeff_mk]

noncomputable def ee (n : ℕ) (k : ℕ) : ℝ :=
  ∑ m ∈ range (k + 1), (n : ℝ) ^ m / (m.factorial : ℝ) * coeff k (Ws C lam ^ m)

lemma ee_ext (n k N : ℕ) (hN : k + 1 ≤ N) :
    ∑ m ∈ range N, (n : ℝ) ^ m / (m.factorial : ℝ) * coeff k (Ws C lam ^ m) = ee C lam n k := by
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hN)
  intro m hm hm'
  simp only [mem_range, not_lt] at hm hm'
  rw [Ws_coeff_lt C lam m k (by omega), mul_zero]

lemma ee_zero (n : ℕ) : ee C lam n 0 = 1 := by
  simp [ee]

lemma ee_succ (n k : ℕ) :
    ee C lam n (k + 1) = (n : ℝ) / ((k + 1 : ℕ) : ℝ) *
      ∑ i ∈ range (k + 1), ((i + 1 : ℕ) : ℝ) * seriesW C lam (i + 1) * ee C lam n (k - i) := by
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, eq_div_iff hk]
  have key : ee C lam n (k + 1) * ((k + 1 : ℕ) : ℝ) = (n : ℝ) * ∑ ij ∈ antidiagonal k,
      (((ij.2 : ℝ) + 1) * seriesW C lam (ij.2 + 1)) * ee C lam n ij.1 := by
    conv_lhs => unfold ee
    rw [Finset.sum_mul, sum_range_succ']
    simp only [pow_zero, coeff_one, Nat.succ_ne_zero, ite_false, mul_zero, zero_mul, add_zero]
    have hs : ∀ m ∈ range (k + 1),
        (n : ℝ) ^ (m + 1) / ((m + 1).factorial : ℝ) * coeff (k + 1) (Ws C lam ^ (m + 1)) *
          ((k + 1 : ℕ) : ℝ) =
        (n : ℝ) * ∑ ij ∈ antidiagonal k, (n : ℝ) ^ m / (m.factorial : ℝ) *
          coeff ij.1 (Ws C lam ^ m) * (((ij.2 : ℝ) + 1) * seriesW C lam (ij.2 + 1)) := by
      intro m _
      have h := Ws_deriv C lam m k
      have hf : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * m.factorial := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hm' : (m.factorial : ℝ) ≠ 0 := by positivity
      push_cast
      rw [hf, pow_succ, Finset.mul_sum]
      have h' : ((k : ℝ) + 1) * coeff (k + 1) (Ws C lam ^ (m + 1)) = _ := h
      calc (n : ℝ) ^ m * n / (((m : ℝ) + 1) * m.factorial) * coeff (k + 1) (Ws C lam ^ (m + 1)) *
              ((k : ℝ) + 1)
          = (n : ℝ) ^ m * n / (((m : ℝ) + 1) * m.factorial) *
              (((k : ℝ) + 1) * coeff (k + 1) (Ws C lam ^ (m + 1))) := by ring
        _ = _ := by
          rw [h', mul_left_comm, ← mul_assoc, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ij _
          field_simp
    rw [Finset.sum_congr rfl hs, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ij hij
    have hle : ij.1 ≤ k := by
      have := mem_antidiagonal.mp hij; omega
    rw [← ee_ext C lam n ij.1 (k + 1) (by omega), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [key, ← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (((i : ℝ) + 1) * seriesW C lam (i + 1)) * ee C lam n j)]
  apply congrArg
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  ring

lemma ee_eq (n k : ℕ) : ee C lam n k = seriesCoeff n C lam k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero => rw [ee_zero, seriesCoeff]
    | succ k =>
      rw [ee_succ, seriesCoeff]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih (k - i) (by omega)]

lemma Ws_coeff_nonneg (hl : 0 ≤ lam) (m k : ℕ) : 0 ≤ coeff k (Ws C lam ^ m) := by
  have : ∀ j, 0 ≤ Wc C lam j := by
    intro j; unfold Wc seriesW; split_ifs
    · exact le_rfl
    · positivity
  have h := cauchyPow_nonneg _ this m k
  rw [cauchyPow_eq] at h
  exact h

lemma excess_nonneg (hl : 0 ≤ lam) (j : ℕ) : 0 ≤ excessPmf C lam j := by
  cases j with
  | zero => unfold excessPmf; exact Finset.sum_nonneg fun z _ => by positivity
  | succ j => unfold excessPmf seriesW; positivity

lemma excess_le (hl : 0 ≤ lam) (j : ℕ) :
    excessPmf C lam j ≤ (if j = 0 then 1 else seriesW C lam j) := by
  cases j with
  | zero =>
    simp only [excessPmf, ite_true]
    have h := Real.sum_le_exp_of_nonneg hl (C + 1)
    calc _ = Real.exp (-lam) * ∑ z ∈ range (C + 1), lam ^ z / (z.factorial : ℝ) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
      _ ≤ Real.exp (-lam) * Real.exp lam := by gcongr
      _ = 1 := by rw [← Real.exp_add]; simp
  | succ j => simp [excessPmf]

lemma main (n C k : ℕ) (lam : ℝ) (hl : 0 ≤ lam) :
    cauchyPow (excessPmf C lam) n k ≤ seriesCoeff n C lam k := by
  set r : ℕ → ℝ := fun j => if j = 0 then 1 else seriesW C lam j with hr
  have hr0 : ∀ j, 0 ≤ r j := by
    intro j; simp only [hr]; split_ifs
    · norm_num
    · unfold seriesW; positivity
  refine (cauchyPow_mono _ r (excess_nonneg C lam hl) (excess_le C lam hl) n k).trans ?_
  have hmk : PowerSeries.mk r = Ws C lam + 1 := by
    ext j
    cases j with
    | zero => simp [hr, Ws, Wc]
    | succ j => simp [hr, Ws, Wc, coeff_one]
  rw [cauchyPow_eq, hmk, add_pow, map_sum]
  simp only [one_pow, mul_one, ← map_natCast (PowerSeries.C (R := ℝ)),
    mul_comm _ (PowerSeries.C _), coeff_C_mul]
  rw [← ee_eq]
  have hnn : ∀ m, 0 ≤ (n : ℝ) ^ m / (m.factorial : ℝ) * coeff k (Ws C lam ^ m) :=
    fun m => mul_nonneg (by positivity) (Ws_coeff_nonneg C lam hl m k)
  calc _ ≤ ∑ m ∈ range (n + 1), (n : ℝ) ^ m / (m.factorial : ℝ) * coeff k (Ws C lam ^ m) :=
        Finset.sum_le_sum fun m _ =>
          mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div m n) (Ws_coeff_nonneg C lam hl m k)
    _ ≤ ∑ m ∈ range (n + k + 1), (n : ℝ) ^ m / (m.factorial : ℝ) * coeff k (Ws C lam ^ m) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
          fun m _ _ => hnn m
    _ = _ := ee_ext C lam n k (n + k + 1) (by omega)

end P7algAux

/-- The series coefficients are nonnegative. -/
theorem seriesCoeff_nonneg (n C : ℕ) {lam : ℝ} (h : 0 ≤ lam) : ∀ k, 0 ≤ seriesCoeff n C lam k
  | 0 => by simp [seriesCoeff]
  | k + 1 => by
    rw [seriesCoeff]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i hi => ?_)
    have := seriesCoeff_nonneg n C h (k - i)
    have : 0 ≤ seriesW C lam (i + 1) := by unfold seriesW; positivity
    positivity

theorem P7alg : RebuildBound.Spec.P7alg_statement := by
  intro n C k lam hl
  exact P7algAux.main n C k lam hl

end RebuildBound
