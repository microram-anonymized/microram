import RebuildBound.Spec.Model.LaneFold

namespace RebuildBound.Spec
open Model Model.LaneFold

/-- Lane copies at least as wide as the phase stash add no failure, and the
fold rebuilds the one-lane stash exactly. The phase stash holds at
most its capacity when the stage begins. -/
def LaneFoldExact_statement : Prop :=
  ∀ (α : Type) (laneCapacity capacity : Nat) (init : List α)
    (lanes : List (List (List α))),
    capacity ≤ laneCapacity → init.length ≤ capacity →
    run laneCapacity capacity init lanes =
      DirectDrain.appendChecked capacity init lanes.flatten.flatten

/-- The width premise is needed: narrower lane copies can fail a stage that
fits the phase stash. -/
def LaneFoldNarrow_statement : Prop :=
  ∀ (laneCapacity capacity : Nat), laneCapacity < capacity →
    ∃ lanes : List (List (List Nat)),
      run laneCapacity capacity [] lanes = none ∧
      (DirectDrain.appendChecked capacity [] lanes.flatten.flatten).isSome

end RebuildBound.Spec
