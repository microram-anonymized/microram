import RebuildBound.Proofs.NativeMatchLivePublic.NativeCollapsedArithmetic
import RebuildBound.Spec.NativeMatch.LivePublic

namespace RebuildBound
open Spec NativeMatchProduction NativeNormalizePairs
open scoped ENNReal

theorem NativeMatchLiveWindowError : NativeMatchLiveWindowError_statement := by
  intro member hm initialized h hh ctx hv hN hq
  have ht := NativeCollapsedArithmetic.strict_window member hm initialized h hh
    ctx.init.length ctx.accesses ctx.geo.keyCapacity hv.1.2.1 hN hq
  refine ⟨ht,lt_of_lt_of_le ht ?_,?_⟩
  · have hf : ENNReal.ofReal (3 / (4 * (2 : ℝ)^64)) ≤ ENNReal.ofReal (1/(2:ℝ)^64) :=
      ENNReal.ofReal_le_ofReal (by norm_num)
    exact mul_le_mul le_rfl hf bot_le bot_le
  · unfold NativeMatchLivePublic.observationError NativeMatchLivePublic.failureError
    apply add_le_add le_rfl
    unfold pairBound
    apply min_le_min le_rfl
    apply ENNReal.div_le_div_right
    exact_mod_cast (Nat.le_add_right (ctx.init.length.choose 2) (ctx.accesses*ctx.geo.keyCapacity))

end RebuildBound
