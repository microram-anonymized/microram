import RebuildBound.Spec.NativeMatch.TightOverflow
import RebuildBound.Proofs.IdealCapacity.Analytic
import RebuildBound.Proofs.NativeMatchTightNumerics

/-! The refined overflow budget as one number, and the canonical capacity
theorem with that budget. The numerical bound is a kernel evaluation of the
exact rational budget of every family member. The capacity theorem is the
analytic capacity theorem, whose exposure sum is bounded by the refined
budget. -/
namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online IdealHierarchy IdealDirect
open scoped ENNReal

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every member's refined budget `x` satisfies `0 ≤ x` and `x * x < 2^-131`,
checked by kernel evaluation over the whole family. -/
theorem NativeMatchTightOverflow : NativeMatchTightOverflow_statement := by
  unfold NativeMatchTightOverflow_statement
  decide +kernel

/-- The analytic capacity theorem bounds the overflow probability by `h` times
the exposure sum, which is at most the refined budget. -/
theorem IdealCapacityTight : IdealCapacityTight_statement := by
  intro initialized member hm h hh geo c g S init m width batches fs choose n compiled
    hinit hgeom hE hn hS hcap a
  have hb := IdealCapacityAnalytic initialized member hm h hh c g S init m width batches
    choose hinit hgeom hE hn hS hcap
  exact hb.trans (mul_le_mul' le_rfl (NativeMatchTightExposure member hm initialized))

end RebuildBound
