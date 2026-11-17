import RebuildBound.Proofs.NTop
import RebuildBound.Spec.TopPrepG
import RebuildBound.Proofs.G3

/-! Shared complete-excess arithmetic. One weighted checker implication serves
preparation, initialization and top finish at every geometry. The checker scale,
Taylor cutoff and load are fixed; job dimensions and truncation remain explicit. -/

namespace RebuildBound.NumericalPhi
open Spec Model
open scoped ENNReal

set_option exponentiation.threshold 500

lemma phi_le (K n C S : ℕ) :
    Phi K n C 32 S ≤ (NTop.phiNum (2 ^ 400) 100 32 K n C S 32 1 : ℝ) / 2 ^ 400 := by
  have h := NTop.phi_sound (by positivity : 0 < 2 ^ 400)
    100 32 K n C S 32 1 one_pos (by norm_num) (by norm_num) (by norm_num) NTop_pos
  push_cast at h
  convert h using 1 <;> norm_num

/-- One exact checker value gives a compact upward-rounded dyadic bound. -/
lemma single_le (K n C S exponent : ℕ)
    (hc : 2 ^ exponent * NTop.phiNum (2 ^ 400) 100 32 K n C S 32 1 ≤ 2 ^ 400) :
    Phi K n C 32 S ≤ 1 / (2 : ℝ) ^ exponent := by
  apply (phi_le K n C S).trans
  have hc' : (2 : ℝ) ^ exponent *
      (NTop.phiNum (2 ^ 400) 100 32 K n C S 32 1 : ℝ) ≤ 2 ^ 400 := by
    exact_mod_cast hc
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  simpa only [mul_comm, one_mul] using hc'

/-- A common denominator check bounds two weighted complete-excess terms. -/
lemma pair_le (w K₁ n₁ C₁ S₁ K₂ n₂ C₂ S₂ num den : ℕ) (hden : 0 < den)
    (hc : (w * NTop.phiNum (2 ^ 400) 100 32 K₁ n₁ C₁ S₁ 32 1 +
      NTop.phiNum (2 ^ 400) 100 32 K₂ n₂ C₂ S₂ 32 1) * den ≤ num * 2 ^ 400) :
    (w : ℝ) * Phi K₁ n₁ C₁ 32 S₁ + Phi K₂ n₂ C₂ 32 S₂ ≤ (num : ℝ) / den := by
  have hc' : ((w : ℝ) *
      (NTop.phiNum (2 ^ 400) 100 32 K₁ n₁ C₁ S₁ 32 1 : ℝ) +
      (NTop.phiNum (2 ^ 400) 100 32 K₂ n₂ C₂ S₂ 32 1 : ℝ)) * den ≤
        num * 2 ^ 400 := by exact_mod_cast hc
  calc
    _ ≤ (w : ℝ) *
          ((NTop.phiNum (2 ^ 400) 100 32 K₁ n₁ C₁ S₁ 32 1 : ℝ) / 2 ^ 400) +
        (NTop.phiNum (2 ^ 400) 100 32 K₂ n₂ C₂ S₂ 32 1 : ℝ) / 2 ^ 400 := by
          gcongr <;> apply phi_le
    _ = ((w : ℝ) *
          (NTop.phiNum (2 ^ 400) 100 32 K₁ n₁ C₁ S₁ 32 1 : ℝ) +
        (NTop.phiNum (2 ^ 400) 100 32 K₂ n₂ C₂ S₂ 32 1 : ℝ)) / 2 ^ 400 := by ring
    _ ≤ _ := by
      rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast hden)]
      exact hc'

lemma tp_remainder_le (g : TPGeom) (K₁ K₂ num den : ℕ) (hden : 0 < den)
    (hc : (g.k * NTop.phiNum (2 ^ 400) 100 32 K₁ g.T g.C
        (g.stashPages * g.C) 32 1 +
      NTop.phiNum (2 ^ 400) 100 32 K₂ g.T g.C (g.drainPages * g.C) 32 1) * den ≤
        num * 2 ^ 400) :
    g.k * ENNReal.ofReal (Phi K₁ g.T g.C 32 (g.stashPages * g.C)) +
      ENNReal.ofReal (Phi K₂ g.T g.C 32 (g.drainPages * g.C)) ≤
        ENNReal.ofReal ((num : ℝ) / den) := by
  have hs0 := G3Proof.Phi_nonneg K₁ g.T g.C (lam := 32) (by norm_num)
    (g.stashPages * g.C)
  have hd0 := G3Proof.Phi_nonneg K₂ g.T g.C (lam := 32) (by norm_num)
    (g.drainPages * g.C)
  calc
    _ = ENNReal.ofReal ((g.k : ℝ) * Phi K₁ g.T g.C 32 (g.stashPages * g.C) +
        Phi K₂ g.T g.C 32 (g.drainPages * g.C)) := by
      rw [ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) hs0) hd0,
        ENNReal.ofReal_mul (by positivity)]
      simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal (pair_le _ _ _ _ _ _ _ _ _ _ _ hden hc)

/-- The optional top range term is retained exactly, including a one-page
retained carry where that term vanishes. -/
lemma top_le (g : TopGeom) (K₁ K₂ num den : ℕ) (hden : 0 < den)
    (hc : ((if g.C < g.SR then 2 ^ g.rho else 0) *
      NTop.phiNum (2 ^ 400) 100 32 K₁ (2 ^ g.I) g.C g.C 32 1 +
      NTop.phiNum (2 ^ 400) 100 32 K₂ g.T g.C
        (min g.SMerge g.STier) 32 1) * den ≤ num * 2 ^ 400) :
    topFinishBound g.C g.SR g.rho g.I g.T (min g.SMerge g.STier) K₁ K₂ 32 ≤
      (num : ℝ) / den := by
  have h := pair_le (if g.C < g.SR then 2 ^ g.rho else 0)
    K₁ (2 ^ g.I) g.C g.C K₂ g.T g.C (min g.SMerge g.STier) num den hden hc
  simpa only [topFinishBound, Nat.cast_ite, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_zero, ite_mul, zero_mul] using h

end RebuildBound.NumericalPhi
