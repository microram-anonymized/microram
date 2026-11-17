import RebuildBound.Spec.NativeMatch.Dense

/-! Production dense row/column recovery regressions. -/
namespace RebuildBound.NativeMatchDenseTests
open Spec Spec.NativeMatchDense Spec.NativeMatch Spec.NativeNormalize

def word (lo hi : Nat) : Key :=
  ⟨(lo + hi * 2 ^ 64) % 2 ^ 128, Nat.mod_lt _ (by positivity)⟩
def victim : Key := word 1 2
def displacedBucket : Bucket := fun i =>
  if i.val = 0 then victim else if i.val = 8 then word 1 3
  else if i.val = 9 then word 4 2 else word 99 99
def displacedLive : Live := fun i => decide (i.val = 0 ∨ i.val = 8 ∨ i.val = 9)

example : subsetMatch displacedBucket displacedLive victim false 1 = true := by decide +kernel
example : selected displacedBucket displacedLive victim = 8 := by decide +kernel
example : hit displacedBucket displacedLive victim true = false := by decide +kernel
example : Unique displacedBucket displacedLive := by
  unfold Spec.NativeMatchDense.Unique
  decide +kernel

/-- All stale nonzero dummy bytes are excluded before intersections. -/
example : hit (fun _ => word 1 2) (fun _ => false) victim true = false := by decide +kernel
/-- A zero-valued half must be supplied by a LIVE partner in that subset. -/
example : subsetMatch (fun _ => word 0 0) (fun _ => false) (word 0 0) false 7 = false := by
  decide +kernel
/-- A live complete-zero key survives zero repair. -/
example : hit (fun _ => word 0 0) (fun i => decide (i.val = 63)) (word 0 0) true = true := by
  decide +kernel
/-- No output is published for inactive query lanes. -/
example : hit (fun _ => word 0 0) (fun i => decide (i.val = 63)) (word 0 0) false = false := by
  decide +kernel
end RebuildBound.NativeMatchDenseTests
