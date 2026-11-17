import RebuildBound.Spec.DirectNative
/-! Small-instance evaluation of the DirectNative statements:
`lake env lean spec_tests/DirectNative.lean` (every `#guard` must pass). -/
open RebuildBound RebuildBound.Model

-- Three flush units of two buckets; keys unique within a unit, overlapping across units.
def data : Nat → DirectMask64.Payload := fun b l => ⟨LogicalKey.ofNat (64 * (b % 2) + l + 10 * (b / 2)), 1000 * b + l, l % 11 == 0⟩
def masks : List (BitVec 64) :=
  [0xFFFFFFFFFFFFFFFF, 0x00FF00FF00FF00FF, 0xFFFF0000FFFF0000, 0x0F0F0F0F0F0F0F0F,
   0xFFFFFFFFFFFFFFF0, 0x8000000000000001]
def flat := DirectMask64.buckets data masks
def units : List DirectMaskBuckets.FlushUnit := [flat.take 2, (flat.drop 2).take 2, flat.drop 4]
def word (k : LogicalKey) : Nat := (LogicalKey.toNat k * 2654435761) % 4294967296
def eq : DirectMasks.Comparison := fun a b => a == b

#guard units.flatten == flat
#guard units.all fun u => ((Bucket.recs u.flatten).map Rec.key).Nodup
#guard DirectMask64.buckets data (DirectMask64.runRange eq data 2 masks 0 (DirectMaskIndex.pairs 2 3)) ==
  (DirectMaskBuckets.run eq [] units).flatten
-- every home count up to 5 and digit-one tier capacities across the failure threshold
#guard [1, 2, 3, 5].all fun U => [2].all fun digit =>
  DirectNative.build eq digit 64 U 2 3 word data masks ==
    DirectMaskedRecords.build eq digit 64 U word (units.map List.flatten)
#guard [1, 2, 3, 5].all fun U => (List.range 30).all fun o =>
  DirectNative.build eq 1 (10 * o) U 2 3 word data masks ==
    DirectMaskedRecords.build eq 1 (10 * o) U word (units.map List.flatten)
-- both outcomes occur
#guard (DirectNative.build eq 1 0 1 2 3 word data masks).isNone
#guard (DirectNative.build eq 1 290 1 2 3 word data masks).isSome
#guard ((DirectNative.build eq 1 290 1 2 3 word data masks).map (·.2.length)) != some 0
