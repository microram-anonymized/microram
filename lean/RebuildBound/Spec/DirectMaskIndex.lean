import RebuildBound.Spec.Model.DirectMaskIndex
import RebuildBound.Spec.DirectMaskSweep

namespace RebuildBound.Spec
open Model Model.DirectMaskIndex

/-- The native pair indices enumerate the unit-pair schedule, each unit pair
expanded older-bucket-major, fresh-bucket-minor. -/
def DirectMaskIndexDecode_statement : Prop :=
  ∀ (unit count : Nat),
    (List.range (pairs unit count)).map (decode unit) =
      (DirectMaskSweep.schedule count).flatMap fun command =>
        (List.range unit).flatMap fun i =>
          (List.range unit).map fun j => (command.1 * unit + i, command.2 * unit + j)

/-- A task may be cut at any pair index, including inside a unit-pair block. -/
def DirectMaskIndexResume_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (unit : Nat) (buckets : List Bucket)
    (begin middle stop : Nat), begin ≤ middle → middle ≤ stop →
    runRange compare unit buckets begin stop =
      runRange compare unit (runRange compare unit buckets begin middle) middle stop

/-- The planned slices, for every width, run the whole range. -/
def DirectMaskIndexPlan_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (unit : Nat) (buckets : List Bucket)
    (width begin stop : Nat),
    runTasks compare unit buckets (plan width begin stop) =
      runRange compare unit buckets begin stop

/-- The complete native range on the flat array is the flattened indexed sweep,
for every comparison, when every flush unit has `unit` buckets. -/
def DirectMaskIndexComplete_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (unit : Nat)
    (units : List DirectMaskBuckets.FlushUnit),
    (∀ u ∈ units, u.length = unit) →
    runRange compare unit units.flatten 0 (pairs unit units.length) =
      (DirectMaskSweep.run compare units (DirectMaskSweep.schedule units.length)).flatten

/-- The planned native slices yield the chronological winners under exact
comparison and uniqueness across each entire flush unit. -/
def DirectMaskIndexWinners_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (unit width : Nat)
    (units : List DirectMaskBuckets.FlushUnit),
    DirectMasks.ExactComparison compare →
    (∀ u ∈ units, u.length = unit) →
    (∀ u ∈ units, ((Bucket.recs u.flatten).map Rec.key).Nodup) →
    DirectMasks.records
        (runTasks compare unit units.flatten (plan width 0 (pairs unit units.length))) =
      DirectPrefix.winners (DirectMasks.records (units.map List.flatten))

end RebuildBound.Spec
