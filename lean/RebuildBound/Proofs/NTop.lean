import RebuildBound.Spec.TopBound
import RebuildBound.Proofs.NTop.Sound

/-!
# Numerics of the top finish (package NTop)

`Phi` is bounded by the executable checker `RebuildBound.NTop.phiNum`
(upward-rounded fixed point, scale `D = 2^400`, 100 Taylor terms, range
reduction `r = 32`), proved sound in `NTop/Sound.lean`. TopNum2 and TPNum
apply it; `NTop_pos` is their shared positivity check (`decide +kernel`).
-/

namespace RebuildBound
open NTop

theorem NTop_pos : 0 < lmNum (2 ^ 400) 100 32 32 1 := by
  decide +kernel

end RebuildBound
