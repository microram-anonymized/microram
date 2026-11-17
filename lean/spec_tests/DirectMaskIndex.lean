import RebuildBound.Spec.DirectMaskIndex
import RebuildBound.Spec.DirectMask64
/-! Small-instance evaluation of the DirectMaskIndex / DirectMask64 statements:
`lake env lean spec_tests/DirectMaskIndex.lean` (every `#guard` must pass). -/
open RebuildBound RebuildBound.Model RebuildBound.Model.DirectMaskIndex

def r (k v : Nat) : Option Rec := some ⟨LogicalKey.ofNat (k), v, false⟩
def eq : DirectMasks.Comparison := fun a b => a == b
def lowBits : DirectMasks.Comparison := fun a b => LogicalKey.toNat a % 4 == LogicalKey.toNat b % 4

-- Decode: all small (unit, count).
#guard (List.range 4).all fun unit => (List.range 6).all fun count =>
  (List.range (pairs unit count)).map (decode unit) ==
    (DirectMaskSweep.schedule count).flatMap fun c =>
      (List.range unit).flatMap fun i => (List.range unit).map fun j => (c.1 * unit + i, c.2 * unit + j)

-- Three units of two buckets; key 1 repeats in every unit, key 2 in two units,
-- holes and a unit-internal pair of buckets.
def units : List DirectMaskBuckets.FlushUnit :=
  [ [[r 1 10, none, r 2 20], [r 3 30]],
    [[none, r 2 21], [r 1 11, r 5 50]],
    [[r 1 12], [none, none, r 6 60]] ]

def sweep (cmp) := (DirectMaskSweep.run cmp units (DirectMaskSweep.schedule units.length)).flatten

#guard runRange eq 2 units.flatten 0 (pairs 2 units.length) == sweep eq
#guard runRange lowBits 2 units.flatten 0 (pairs 2 units.length) == sweep lowBits
-- every width and every cut point
#guard (List.range 14).all fun w =>
  runTasks eq 2 units.flatten (plan w 0 (pairs 2 units.length)) == sweep eq
#guard (List.range (pairs 2 3 + 1)).all fun m =>
  runRange eq 2 (runRange eq 2 units.flatten 0 m) m (pairs 2 3) == sweep eq
#guard DirectMasks.records (sweep eq) ==
  DirectPrefix.winners (DirectMasks.records (units.map List.flatten))
#guard (DirectMasks.records (sweep eq)).map (fun r => LogicalKey.toNat r.key) == [3, 2, 5, 1, 6]

-- DirectMask64.
open DirectMask64 in
#guard
  let fd : Payload := fun l => ⟨LogicalKey.ofNat (l % 5), l, false⟩
  let od : Payload := fun l => ⟨LogicalKey.ofNat (l % 7), 100 + l, false⟩
  let fm : BitVec 64 := 0x00000000000000A5
  let om : BitVec 64 := 0xF0F0F0F0F0F0FFFF
  bucket od (pairMask eq fd fm od om) == DirectMasks.pair eq (bucket fd fm) (bucket od om) &&
  bucket od (pairMask eq fd fm od om) != bucket od om
open DirectMask64 in
#guard
  let data : Nat → Payload := fun b l => ⟨LogicalKey.ofNat ((b + l) % 9), 64 * b + l, false⟩
  let masks : List (BitVec 64) := [0xFF, 0xF00F, 0x1, 0xFFFF0000, 0x0F, 0x3]
  (List.range 9).all fun m =>
    buckets data (DirectMask64.runRange eq data 2 masks 1 (m + 5)) ==
      DirectMaskIndex.runRange eq 2 (buckets data masks) 1 (m + 5)
