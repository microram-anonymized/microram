import RebuildBound.Spec.Model.DirectMaskBuckets
import RebuildBound.Spec.DirectMasks

namespace RebuildBound.Spec
open Model Model.DirectMaskBuckets

/-- Bucket-by-bucket mask mutation equals one grouped-unit comparison, for
every comparison function, without an exact-key or uniqueness premise. -/
def DirectMaskBucketsPair_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (fresh older : FlushUnit),
    (pair compare fresh older).flatten = DirectMasks.pair compare fresh.flatten older.flatten

/-- The multi-bucket pass refines the existing chronological mask pass,
including arbitrary states resumed at whole-unit boundaries. -/
def DirectMaskBucketsRun_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (state units : List FlushUnit),
    (run compare state units).map List.flatten =
      DirectMasks.run compare (state.map List.flatten) (units.map List.flatten)

/-- Every unit retains its ordered list of physical bucket widths. -/
def DirectMaskBucketsShape_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (state units : List FlushUnit),
    (run compare state units).map (List.map List.length) =
      (state ++ units).map (List.map List.length)

/-- Exact comparisons and uniqueness across the entire flush unit give the
existing chronological winner list, with complete records and tombstones. -/
def DirectMaskBucketsWinners_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (units : List FlushUnit),
    DirectMasks.ExactComparison compare →
    (∀ unit ∈ units, ((Bucket.recs unit.flatten).map Rec.key).Nodup) →
    DirectMasks.records ((run compare [] units).map List.flatten) =
      DirectPrefix.winners (DirectMasks.records (units.map List.flatten))

end RebuildBound.Spec
