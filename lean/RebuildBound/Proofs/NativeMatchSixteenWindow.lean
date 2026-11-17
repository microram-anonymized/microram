import RebuildBound.Spec.NativeMatch.SixteenWindow
import RebuildBound.Proofs.NativeMatchTightNumerics
import RebuildBound.Proofs.NativeMatchTightPublic

/-! Sixteen-byte keys over any number of windows. The normalization cost of
the sixteen-byte key model is zero, so the error term is `h` times the
refined allocation, and that allocation is below `2^-65` for every member and
either start. -/
namespace RebuildBound
open Spec NativeMatchProduction NativeMatchEndpoint
open scoped ENNReal

theorem NativeMatchSixteenWindowError : NativeMatchSixteenWindowError_statement := by
  intro member hm initialized h hh ctx
  have ha : NativeMatchTightPublic.allocation member initialized <
      ENNReal.ofReal (1 / (2 : ℝ)^65) := by
    rw [NativeMatchTightPublicAllocation member hm initialized]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr (NativeMatchTightArithmetic member hm initialized).2
  have hz : (h : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  have h65 : NativeMatchTightPublic.error ctx .sixteen <
      (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ)^65) := by
    simpa only [NativeMatchTightPublic.error, NativeMatchEndpoint.normalizeCost, add_zero]
      using ENNReal.mul_lt_mul_right hz (by finiteness) ha
  have hle : ENNReal.ofReal (1 / (2 : ℝ)^65) ≤ ENNReal.ofReal (1 / (2 : ℝ)^64) :=
    ENNReal.ofReal_le_ofReal (by norm_num)
  exact ⟨h65, h65.trans_le (mul_le_mul' le_rfl hle)⟩

end RebuildBound
