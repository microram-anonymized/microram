import RebuildBound.Proofs.NCA5.Class
import RebuildBound.Proofs.SelRange1.Glue

/-!
# SelRange7: one `r = 7` shape (package SelRange7)

`selRange7_le`: the range term of an `r = 7` shape from its two class laws.
With `M = 64 - k` and `2^M mod 7 = 1`, NCA5's `qCount_eq` gives class `0` the
count `qc_A = ⌊2^M / 7⌋ + 1` and classes `1 … 6` the count `qc_B = ⌊2^M / 7⌋`, so
`Σ_{a<7} stopLoss ≤ x_A + 6 x_B` with `x_X = tn_X / td + 10^-50` (`Class.lean`).
The old-map density is bounded as in SelRange1 (`SelRange1.density_le`), and the
budget is checked as one inequality of natural numbers (`combine7`).
-/

open MeasureTheory ProbabilityTheory RebuildBound.Spec RebuildBound.Model
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.SelRange7

lemma natDiv_eq_ofReal (a b : ℕ) (hb : 0 < b) :
    (a : ℝ≥0∞) / (b : ℝ≥0∞) = ENNReal.ofReal ((a : ℝ) / b) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hb), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

/-- The budget arithmetic of one shape: density bound `a / b`, `2^t` ranges, class
bounds `tA / td + 10^-50` (class 0) and `tB / td + 10^-50` (six classes). -/
lemma combine7 {a b tA tB td e f t : ℕ} (hb : 0 < b) (htd : 0 < td) (hf : 0 < f)
    (h : a * 2 ^ t * ((tA + 6 * tB) * 10 ^ 50 + 7 * td) * f ≤ e * (b * (td * 10 ^ 50))) :
    (a : ℝ≥0∞) / b * 2 ^ t * (((tA : ℝ≥0∞) / (td : ℕ) + 1 / 10 ^ 50) +
      6 * ((tB : ℝ≥0∞) / (td : ℕ) + 1 / 10 ^ 50)) ≤ ENNReal.ofReal ((e : ℝ) / f) := by
  have hE : (1 : ℝ≥0∞) / 10 ^ 50 = ENNReal.ofReal (1 / 10 ^ 50) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]; norm_num
  have h2 : (2 : ℝ≥0∞) ^ t = ENNReal.ofReal (2 ^ t) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; norm_num
  have h6 : (6 : ℝ≥0∞) = ENNReal.ofReal 6 := by norm_num
  have hL : (a : ℝ≥0∞) / b * 2 ^ t * (((tA : ℝ≥0∞) / (td : ℕ) + 1 / 10 ^ 50) +
      6 * ((tB : ℝ≥0∞) / (td : ℕ) + 1 / 10 ^ 50)) = ENNReal.ofReal ((a : ℝ) / b * 2 ^ t *
        (((tA : ℝ) / td + 1 / 10 ^ 50) + 6 * ((tB : ℝ) / td + 1 / 10 ^ 50))) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity), ← natDiv_eq_ofReal a b hb,
      ← natDiv_eq_ofReal tA td htd, ← natDiv_eq_ofReal tB td htd, ← hE, ← h2, ← h6]
  rw [hL]
  apply ENNReal.ofReal_le_ofReal
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have htd' : (0 : ℝ) < td := by exact_mod_cast htd
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have hR : (a : ℝ) * 2 ^ t * (((tA : ℝ) + 6 * tB) * 10 ^ 50 + 7 * td) * f ≤
      e * (b * (td * 10 ^ 50)) := by exact_mod_cast h
  rw [show (a : ℝ) / b * 2 ^ t * (((tA : ℝ) / td + 1 / 10 ^ 50) + 6 * ((tB : ℝ) / td + 1 / 10 ^ 50)) =
      (a : ℝ) * 2 ^ t * (((tA : ℝ) + 6 * tB) * 10 ^ 50 + 7 * td) / (b * (td * 10 ^ 50)) by
    field_simp; ring]
  rw [div_le_div_iff₀ (by positivity) hf']
  linarith

/-- **One `r = 7` shape.** The shape's numbers are checked by `rfl` (`t`, `i`, `P`,
`n`, `m`, `num`, `M`) and `norm_num` (the class counts and the arithmetic); the two
class laws are hypotheses (`class_<S>A`, `class_<S>B`). -/
theorem selRange7_le (g : SepGeom) {t i P n m num M qA qB tA tB td bn bd : ℕ} {q : ℚ}
    (hr : g.r = 7) (hC : g.C = 64) (ht : g.k - g.I = t) (hi : g.I = i) (hP : g.earlyCap = P)
    (hn : 32 * ((g.d - 1) * g.U) = n) (hm : SelRange1.oldExp g 64 = m)
    (hnum : SelRange1.oldNum g 64 = num) (hM : 64 - g.k = M)
    (hmod : 2 ^ M % 7 = 1) (hqA : 2 ^ M / 7 + 1 = qA) (hqB : 2 ^ M / 7 = qB)
    (hXA : ∀ q : I, (q : ℝ) = (qA : ℝ) / ((2 ^ M : ℕ) : ℝ) →
      stopLoss (rangeLawR 64 32 P (2 ^ i) t 7 q) 64 ≤ (tA : ℝ≥0∞) / (td : ℕ) + 1 / 10 ^ 50)
    (hXB : ∀ q : I, (q : ℝ) = (qB : ℝ) / ((2 ^ M : ℕ) : ℝ) →
      stopLoss (rangeLawR 64 32 P (2 ^ i) t 7 q) 64 ≤ (tB : ℝ≥0∞) / (td : ℕ) + 1 / 10 ^ 50)
    (hq : (q : ℝ) = (bn : ℝ) / (bd : ℕ))
    (hle : 2 ^ m ≤ num) (hlt : n * (num - 2 ^ m) < 2 ^ m) (htd : 0 < td) (hbd : 0 < bd)
    (hfin : 2 ^ m * 2 ^ t * ((tA + 6 * tB) * 10 ^ 50 + 7 * td) * bd ≤
      bn * ((2 ^ m - n * (num - 2 ^ m)) * (td * 10 ^ 50))) :
    selRange g ≤ ENNReal.ofReal (q : ℝ) := by
  have hcA : qCount 64 g.k 7 0 = qA := by
    rw [NCA5.qCount_eq (by norm_num), hM, hmod, ← hqA]
    simp
  have hcB : ∀ a, a < 6 → qCount 64 g.k 7 (a + 1) = qB := by
    intro a ha
    rw [NCA5.qCount_eq (by omega), hM, hmod, ← hqB]
    simp
  have hsum : ∑ a ∈ Finset.range 7, stopLoss (rangeLawR 64 32 P (2 ^ i) t 7 (qMass 64 g.k 7 a)) 64 ≤
      ((tA : ℝ≥0∞) / (td : ℕ) + 1 / 10 ^ 50) + 6 * ((tB : ℝ≥0∞) / (td : ℕ) + 1 / 10 ^ 50) := by
    rw [Finset.sum_range_succ', add_comm]
    have h0 := hXA (qMass 64 g.k 7 0) (by rw [NCA5.qMass_coe, hcA, hM])
    have hrest : ∑ a ∈ Finset.range 6,
        stopLoss (rangeLawR 64 32 P (2 ^ i) t 7 (qMass 64 g.k 7 (a + 1))) 64 ≤
        ∑ _a ∈ Finset.range 6, ((tB : ℝ≥0∞) / (td : ℕ) + 1 / 10 ^ 50) :=
      Finset.sum_le_sum fun a ha =>
        hXB _ (by rw [NCA5.qMass_coe, hcB a (Finset.mem_range.mp ha), hM])
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hrest
    exact add_le_add h0 (by exact_mod_cast hrest)
  unfold selRange sepRange
  rw [hr, hC, ht, hi, hP, hn, SelRange1.oldDensity_eq, hm, hnum, hq]
  calc _ ≤ ((2 ^ m : ℕ) : ℝ≥0∞) / ((2 ^ m - n * (num - 2 ^ m) : ℕ) : ℝ≥0∞) * 2 ^ t *
        (((tA : ℝ≥0∞) / (td : ℕ) + 1 / 10 ^ 50) + 6 * ((tB : ℝ≥0∞) / (td : ℕ) + 1 / 10 ^ 50)) := by
        gcongr
        exact SelRange1.density_le hle hlt
    _ ≤ _ := combine7 (by omega) htd hbd hfin

end RebuildBound.SelRange7
