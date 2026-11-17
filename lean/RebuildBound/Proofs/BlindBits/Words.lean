import RebuildBound.Proofs.BlindBits.Bits

/-!
# BlindBits: word averages and ranges (from G2.Words, G2.Range)

`avg_comp` (averages over words pulled back along a bijection) and
`inRange_natToBits`. Moved from the binary d = 2 chain (`G2.Words`,
`G2.Range`); namespace `RebuildBound.G2` kept.
-/

open scoped ENNReal
namespace RebuildBound.G2
open RebuildBound.Model RebuildBound.Spec
theorem avg_comp {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B] (π : A → B) (m : ℕ)
    (hm : m ≠ 0) (hfib : ∀ y, (Finset.univ.filter (fun a => π a = y)).card = m)
    (F : B → ℝ≥0∞) :
    (Fintype.card A : ℝ≥0∞)⁻¹ * ∑ a, F (π a) = (Fintype.card B : ℝ≥0∞)⁻¹ * ∑ y, F y := by
  have hsum : ∑ a, F (π a) = (m : ℝ≥0∞) * ∑ y, F y := by
    rw [← Finset.sum_fiberwise' Finset.univ π F, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_const, hfib, nsmul_eq_mul]
  have hcard : Fintype.card A = m * Fintype.card B := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := π) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
    simp [hfib, mul_comm]
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast hm
  rw [hsum, hcard, Nat.cast_mul, ENNReal.mul_inv (Or.inl hm0) (Or.inl (ENNReal.natCast_ne_top m))]
  calc (m : ℝ≥0∞)⁻¹ * (Fintype.card B : ℝ≥0∞)⁻¹ * (m * ∑ y, F y) =
      ((m : ℝ≥0∞)⁻¹ * m) * ((Fintype.card B : ℝ≥0∞)⁻¹ * ∑ y, F y) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hm0 (ENNReal.natCast_ne_top m), one_mul]

end RebuildBound.G2

namespace RebuildBound.G2
open RebuildBound.Model RebuildBound.Spec
theorem inRange_natToBits {b lo R n : ℕ} (hlo : lo ≤ b) (hR : R < 2 ^ (b - lo)) :
    InRange lo (natToBits b (R * 2 ^ lo)) (natToBits b n) ↔ n % 2 ^ b / 2 ^ lo = R := by
  unfold InRange natToBits
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro s
    rw [Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow]
    by_cases hs : s + lo < b
    · have := h ⟨s + lo, hs⟩ (by simp)
      simp only at this
      rw [this, Nat.testBit_mul_two_pow]
      simp [hs]
    · simp only [hs, decide_false, Bool.false_and]
      exact (testBit_eq_false_of_lt_pow hR (by omega)).symm
  · intro h i hi
    have := congrArg (fun m => m.testBit (i.val - lo)) h
    simp only [Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow] at this
    rw [Nat.sub_add_cancel hi] at this
    rw [Nat.testBit_mul_two_pow, ← this]
    simp [hi, i.isLt]

end RebuildBound.G2
