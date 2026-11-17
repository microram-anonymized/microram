import RebuildBound.Spec.P8bStar
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Feasibility is proved in the ordered NNReal semiring.  The private
center coefficient is bounded explicitly, before using truncated subtraction.
No success event or positive marginal scale is assumed. -/
namespace RebuildBound.P8bStarRatesProof

open RebuildBound.Spec
open scoped NNReal

private theorem interval_rates (L a b n lo theta hi : ℝ≥0)
    (hlo : lo ≤ theta) (hhi : theta ≤ hi) (hhi1 : hi ≤ 1)
    (ha : a ≤ 1) (hb : b ≤ 1) (hbudget : n * b + a ≤ 1) :
    theta ≤ 1 ∧ theta * a ≤ 1 ∧
      L * (1 - theta * a) ≤ L * (1 - lo * a) ∧
      L * theta * b ≤ L * hi * b ∧
      n * (L * hi * b) ≤ L * (1 - lo * a) ∧
      L * hi * b ≤ L := by
  have ht1 := hhi.trans hhi1
  have hlo1 := hlo.trans ht1
  have hla : lo * a ≤ a := by simpa using mul_le_mul_left hlo1 a
  have hta : theta * a ≤ a := by simpa using mul_le_mul_left ht1 a
  have hnb : n * hi * b ≤ n * b := by
    simpa using mul_le_mul_left (mul_le_mul_right hhi1 n) b
  have hprivate : n * hi * b ≤ 1 - lo * a :=
    le_tsub_of_add_le_right ((add_le_add hnb hla).trans hbudget)
  have hshared : hi * b ≤ 1 :=
    (by simpa using mul_le_mul_left hhi1 b : hi * b ≤ b).trans hb
  refine ⟨ht1, hta.trans ha, ?_, ?_, ?_, ?_⟩
  · exact mul_le_mul_right (tsub_le_tsub_left (mul_le_mul_left hlo a) 1) L
  · exact mul_le_mul_left (mul_le_mul_right hhi L) b
  · calc
      n * (L * hi * b) = L * (n * hi * b) := by ring
      _ ≤ L * (1 - lo * a) := mul_le_mul_right hprivate L
  · simpa only [mul_assoc, mul_one] using mul_le_mul_right hshared L

theorem rates : P8bStarRates_statement := by
  intro L d t j theta hs hj hlo hhi
  have hupper : (((j + 1 : ℕ) : ℝ≥0) / 32) ≤ 1 := by
    apply (div_le_one₀ (by norm_num : (0 : ℝ≥0) < 32)).mpr
    exact_mod_cast (show j + 1 ≤ 32 by omega)
  have ha : ((t - 1 : ℕ) : ℝ≥0) /
      (((d - 1 : ℕ) : ℝ≥0) * (t : ℝ≥0)) ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have hb : (1 : ℝ≥0) / ((d - 1 : ℕ) : ℝ≥0) ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have hbudget : ((d / t - 1 : ℕ) : ℝ≥0) *
      (1 / ((d - 1 : ℕ) : ℝ≥0)) +
      ((t - 1 : ℕ) : ℝ≥0) /
        (((d - 1 : ℕ) : ℝ≥0) * (t : ℝ≥0)) ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have h := interval_rates L
    (((t - 1 : ℕ) : ℝ≥0) / (((d - 1 : ℕ) : ℝ≥0) * (t : ℝ≥0)))
    (1 / ((d - 1 : ℕ) : ℝ≥0)) ((d / t - 1 : ℕ) : ℝ≥0)
    ((j : ℝ≥0) / 32) theta (((j + 1 : ℕ) : ℝ≥0) / 32)
    hlo hhi hupper ha hb hbudget
  simpa only [denseStarCenter, denseStarShared, div_eq_mul_inv, one_mul, mul_assoc] using h

end RebuildBound.P8bStarRatesProof

theorem RebuildBound.P8bStarRates : RebuildBound.Spec.P8bStarRates_statement :=
  RebuildBound.P8bStarRatesProof.rates
