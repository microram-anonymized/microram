import RebuildBound.Spec.Model.DirectMaskSweep
import RebuildBound.Spec.DirectMaskBuckets

namespace RebuildBound.Spec
open Model Model.DirectMaskSweep

/-- A chronological prefix changes only the processed units. The untouched
suffix supplies the original fresh masks when its turn arrives. -/
def DirectMaskSweepPrefix_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (units : List DirectMaskBuckets.FlushUnit)
    (count : Nat), count ≤ units.length →
    run compare units (schedule count) =
      DirectMaskBuckets.run compare [] (units.take count) ++ units.drop count

/-- The complete indexed sweep equals the existing multi-bucket append fold,
without exact-comparison or key-uniqueness assumptions. -/
def DirectMaskSweepComplete_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (units : List DirectMaskBuckets.FlushUnit),
    run compare units (schedule units.length) = DirectMaskBuckets.run compare [] units

/-- Pause/resume at any unit-pair command boundary, including inside a row of
older units. Native cuts inside a physical bucket block still need an adapter. -/
def DirectMaskSweepResume_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (state : List DirectMaskBuckets.FlushUnit)
    (front back : List Command),
    run compare state (front ++ back) = run compare (run compare state front) back

/-- Reuse the existing chronological winner law for the indexed sweep.
Uniqueness is required across each entire flush unit, not just each bucket. -/
def DirectMaskSweepWinners_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (units : List DirectMaskBuckets.FlushUnit),
    DirectMasks.ExactComparison compare →
    (∀ unit ∈ units, ((Bucket.recs unit.flatten).map Rec.key).Nodup) →
    DirectMasks.records ((run compare units (schedule units.length)).map List.flatten) =
      DirectPrefix.winners (DirectMasks.records (units.map List.flatten))

end RebuildBound.Spec
