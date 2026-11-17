import RebuildBound.Spec.Subtotal
import RebuildBound.Proofs.NumericalPhi

/-!
# TopNum2: the selected top finish is at most `0.5845 · 2^-78`

Reuses the NTop checker (`phiNum`, `phi_sound`) at scale `2^400`; the rational
target is closed by one `decide +kernel` comparison on `Nat`.
-/

namespace RebuildBound
open NTop

theorem TopNum2_check :
    10000 * 2 ^ 78 * (16 * phiNum (2 ^ 400) 100 32 256 (2 ^ 18) 64 64 32 1
      + phiNum (2 ^ 400) 100 32 256 (2 ^ 22) 64 128 32 1) ≤ 5845 * 2 ^ 400 := by
  decide +kernel

theorem TopNum2 : Spec.TopNum2_statement := by
  have h := NumericalPhi.pair_le 16 256 (2 ^ 18) 64 64 256 (2 ^ 22) 64 128
    5845 (10000 * 2 ^ 78) (by positivity)
    (by simpa only [mul_comm] using TopNum2_check)
  norm_num [Spec.TopNum2_statement, Spec.topFinishBound] at h ⊢
  exact h

end RebuildBound
