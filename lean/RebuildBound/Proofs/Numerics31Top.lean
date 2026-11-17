import RebuildBound.Spec.Numerics31Pilot
import RebuildBound.Proofs.NumericalPhi

/-!
# Complete-excess numerical pilots for the capacity-2^31 geometry

The existing upward-rounded NTop checker certifies all complete-excess terms
at cutoff 576 and scale `2^400`. Preparation and initialization are evaluated
through their actual geometry records, retaining their distinct drain sizes.
The shared range term is certified separately.
-/

namespace RebuildBound
open Spec Model
open scoped ENNReal

set_option exponentiation.threshold 500

namespace Numerics31Top

set_option maxRecDepth 4096 in
theorem top_check :
    (2 ^ top31.rho * NTop.phiNum (2 ^ 400) 100 32 576 (2 ^ top31.I)
      top31.C top31.C 32 1 +
      NTop.phiNum (2 ^ 400) 100 32 576 top31.T top31.C
        (min top31.SMerge top31.STier) 32 1) * (16 * 2 ^ 70) ≤ 9 * 2 ^ 400 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem prep_check :
    (prep31.k * NTop.phiNum (2 ^ 400) 100 32 576 prep31.T prep31.C
      (prep31.stashPages * prep31.C) 32 1 +
      NTop.phiNum (2 ^ 400) 100 32 576 prep31.T prep31.C
        (prep31.drainPages * prep31.C) 32 1) * 2 ^ 107 ≤ 2 ^ 400 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem init_check :
    (init31.k * NTop.phiNum (2 ^ 400) 100 32 576 init31.T init31.C
      (init31.stashPages * init31.C) 32 1 +
      NTop.phiNum (2 ^ 400) 100 32 576 init31.T init31.C
        (init31.drainPages * init31.C) 32 1) * 2 ^ 71 ≤ 2 ^ 400 := by
  decide +kernel

end Numerics31Top

theorem TopNum31 : Spec.TopNum31_statement := by
  have h := NumericalPhi.top_le top31 576 576 9 (16 * 2 ^ 70) (by positivity)
    (by simpa only [show top31.C < top31.SR from by decide, ite_true]
      using Numerics31Top.top_check)
  unfold Spec.TopNum31_statement
  convert h using 1 <;> norm_num

theorem TPRemainder31 : Spec.TPRemainder31_statement := by
  unfold Spec.TPRemainder31_statement
  constructor
  · have h := NumericalPhi.tp_remainder_le prep31 576 576 1 (2 ^ 107)
      (by positivity) (by simpa only [one_mul] using Numerics31Top.prep_check)
    push_cast at h
    convert h using 1 <;> norm_num
  · have h := NumericalPhi.tp_remainder_le init31 576 576 1 (2 ^ 71)
      (by positivity) (by simpa only [one_mul] using Numerics31Top.init_check)
    push_cast at h
    convert h using 1 <;> norm_num

end RebuildBound
