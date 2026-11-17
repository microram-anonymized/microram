import RebuildBound.Spec.Model.DirectMasks
import Mathlib.Data.List.Nodup
namespace RebuildBound.Spec
open Model Model.DirectMasks
def DirectMasksLanes_statement : Prop :=
  ∀ (compare : Comparison) (fresh older : Bucket),
    (pair compare fresh older).length = older.length
def DirectMasksStep_statement : Prop :=
  ∀ (compare : Comparison) (older : List Bucket) (fresh : Bucket),
    ExactComparison compare →
    records (step compare older fresh) = DirectPrefix.unitStep (records older) fresh.recs
/-- Within-unit real-key uniqueness and exact comparison imply latest winners. -/
def DirectMasksWinners_statement : Prop :=
  ∀ (compare : Comparison) (units : List Bucket),
    ExactComparison compare →
    (∀ unit ∈ units, (unit.recs.map Rec.key).Nodup) →
    records (run compare [] units) = DirectPrefix.winners (records units)
end RebuildBound.Spec
