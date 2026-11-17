import RebuildBound.Proofs.NativeRoutingFamilySupport
import RebuildBound.Proofs.NativeRoutingCoupling

/-! Complete-message family separation and the strict physical ring boundary.
The examples do not assert an execution-wide family population bound. -/
namespace RebuildBound.NativeRoutingFamilySupportTests
open Model Spec NativeNormalize NativeRouting NativeRoutingCoupling.Coordinates
open NativeRoutingCouplingProof.Coordinates NativeMatchPhysical

private def keyA : LogicalKey := [0]
private def keyB : LogicalKey := [1]
private def collapsed : Tape 128 := fun _ => 0

/-- Different keys under the same family do alias if their fingerprints agree. -/
example : nativeCode collapsed (.real 3 2 keyA) = nativeCode collapsed (.real 3 2 keyB) := rfl

/-- Repetition of a logical key under the same family reads the same message. -/
example (stored : Tape 128) :
    nativeCode stored (.real 3 2 keyA) = nativeCode stored (.real 3 2 keyA) := rfl

/-- Complete-message counters separate families despite normalization collision. -/
example : nativeCode collapsed (.real 3 2 keyA) ≠ nativeCode collapsed (.real 4 2 keyB) := by
  intro heq
  have : (3 : Counter) = 4 :=
    ((NativeRoutingRealCodeFamily collapsed 3 4 2 2 keyA keyB).mp heq).1
  revert this
  decide +kernel

/-- The level field is also part of the complete family identity. -/
example : nativeCode collapsed (.real 3 2 keyA) ≠ nativeCode collapsed (.real 3 3 keyB) := by
  intro heq
  have : (2 : Level) = 3 :=
    ((NativeRoutingRealCodeFamily collapsed 3 3 2 3 keyA keyB).mp heq).2.1
  revert this
  decide +kernel

/-- At r0=2, two complete prefixes, one partial unit and the current unit
fill exactly six requester units. Position 1279 is one below the bound 1280. -/
example : fillDenseUnits 2 2 7 19 = some [14, 15, 16, 17, 18, 19] := by decide +kernel
example : 19 * 64 + 63 + 1 = 7 * (64 * 2) + 3 * (64 * 2) := by decide +kernel

/-- Crossing the next complete-prefix boundary fails the unchanged ring guard. -/
example : fillDenseUnits 2 2 7 20 = none := by decide +kernel

/-- A stale consumed counter cannot evade the ring guard after a long gap. -/
example : fillDenseUnits 2 2 0 1000 = none := by decide +kernel

/-- The registered theorem turns this actual successful ring plan into the
strict bound for every current-unit position, including its last lane. -/
example (current position : Nat) (hcurrent : current < 64)
    (hposition : position = 19 * 64 + current) : position < 1280 := by
  exact NativeRoutingRingPosition 2 7 19 current position (by decide) hcurrent hposition
    [14, 15, 16, 17, 18, 19] (by decide +kernel)

end RebuildBound.NativeRoutingFamilySupportTests
