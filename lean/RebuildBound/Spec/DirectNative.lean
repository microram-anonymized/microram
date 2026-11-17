import RebuildBound.Spec.Model.DirectNative
import RebuildBound.Spec.DirectMaskBuckets

namespace RebuildBound.Spec
open Model Model.DirectNative

/-- The native dedup over every pair index, read through the masks, is the
multi-bucket chronological pass on the flush units, for every comparison. -/
def DirectNativeDedup_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (unit : Nat) (data : Nat → DirectMask64.Payload)
    (masks : List (BitVec 64)) (units : List DirectMaskBuckets.FlushUnit),
    (∀ u ∈ units, u.length = unit) →
    DirectMask64.buckets data masks = units.flatten →
    DirectMask64.buckets data
        (DirectMask64.runRange compare data unit masks 0
          (DirectMaskIndex.pairs unit units.length)) =
      (DirectMaskBuckets.run compare [] units).flatten

/-- The native flat build is the logical masked-record build on the grouped
flush units: same main table, same tier records in order, same failure. -/
def DirectNativeBuild_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (digit output U unit : Nat) (word : LogicalKey → Nat)
    (data : Nat → DirectMask64.Payload) (masks : List (BitVec 64))
    (units : List DirectMaskBuckets.FlushUnit),
    0 < U → DirectMasks.ExactComparison compare →
    (∀ u ∈ units, u.length = unit) →
    (∀ u ∈ units, ((Bucket.recs u.flatten).map Rec.key).Nodup) →
    DirectMask64.buckets data masks = units.flatten →
    build compare digit output U unit units.length word data masks =
      DirectMaskedRecords.build compare digit output U word (units.map List.flatten)

end RebuildBound.Spec
