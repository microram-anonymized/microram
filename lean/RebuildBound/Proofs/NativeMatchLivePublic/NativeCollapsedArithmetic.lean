import RebuildBound.Proofs.NativeMatchTightPublic
import RebuildBound.Proofs.NativeMatchLivePairs

namespace RebuildBound.NativeCollapsedArithmetic
open Spec NativeMatchProduction NativeNormalizePairs
open scoped ENNReal

lemma pair_quarter (I n N h : Nat) (hI : I ≤ N) (hN : N ≤ 2^31)
    (hq : I+n ≤ h*2^31) : pairBound 128 (I.choose 2+n*N) ≤
      (h : ℝ≥0∞)*ENNReal.ofReal (1/(2:ℝ)^66) := by
  have hcount := NativeMatchLivePairWindow I n N h hI hN hq
  have hcast : ((I.choose 2+n*N : Nat) : ℝ≥0∞) ≤ ((h*2^62 : Nat) : ℝ≥0∞) := by
    exact_mod_cast hcount
  have he : (2 : ℝ≥0∞)^62/(2 : ℝ≥0∞)^128 = ENNReal.ofReal (1/(2:ℝ)^66) := by
    have hr := congrArg ENNReal.ofReal (show (2:ℝ)^62/(2:ℝ)^128=1/(2:ℝ)^66 by norm_num)
    simpa only [ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ)<2^128),
      ENNReal.ofReal_pow (by positivity : (0:ℝ)≤2), ENNReal.ofReal_ofNat] using hr
  apply (min_le_right _ _).trans
  apply (ENNReal.div_le_div_right hcast _).trans_eq
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_div_assoc,he]

lemma strict_window (member : ConfigurationFamily.Member) (hm : member∈ConfigurationFamily.members)
    (initialized : Bool) (h : Nat) (hh : 1≤h) (I n N : Nat)
    (hI : I≤N) (hN : N≤2^31) (hq : I+n≤h*2^31) :
    (h : ℝ≥0∞)*NativeMatchTightPublic.allocation member initialized + pairBound 128 (I.choose 2+n*N) <
      (h : ℝ≥0∞)*ENNReal.ofReal (3/(4*(2:ℝ)^64)) := by
  have ha : NativeMatchTightPublic.allocation member initialized < ENNReal.ofReal (1/(2:ℝ)^65) := by
    rw [NativeMatchTightPublicAllocation member hm initialized]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using
      (Rat.cast_lt (K:=ℝ)).mpr (NativeMatchTightArithmetic member hm initialized).2
  have hd : ENNReal.ofReal (1/(2:ℝ)^66)+ENNReal.ofReal (1/(2:ℝ)^65) =
      ENNReal.ofReal (3/(4*(2:ℝ)^64)) := by
    rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    norm_num
  have hsum : NativeMatchTightPublic.allocation member initialized + ENNReal.ofReal (1/(2:ℝ)^66) <
      ENNReal.ofReal (3/(4*(2:ℝ)^64)) := by
    have hs := ENNReal.add_lt_add_left (by finiteness : ENNReal.ofReal (1/(2:ℝ)^66)≠⊤) ha
    simpa only [add_comm (NativeMatchTightPublic.allocation member initialized) _,hd] using hs
  calc
    _ ≤ (h : ℝ≥0∞)*NativeMatchTightPublic.allocation member initialized +
        (h : ℝ≥0∞)*ENNReal.ofReal (1/(2:ℝ)^66) :=
      add_le_add le_rfl (pair_quarter I n N h hI hN hq)
    _ = (h : ℝ≥0∞)*(NativeMatchTightPublic.allocation member initialized+ENNReal.ofReal (1/(2:ℝ)^66)) := by
      rw [mul_add]
    _ < _ := by
      have hz : (h : ℝ≥0∞)≠0 := by exact_mod_cast (by omega : h≠0)
      simpa only [mul_comm] using ENNReal.mul_lt_mul_left hz (by finiteness) hsum

end RebuildBound.NativeCollapsedArithmetic
