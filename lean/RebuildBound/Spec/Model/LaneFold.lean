import RebuildBound.Spec.Model.DirectDrain

/-! Lane copies of a stage's stashes, from `FoldLanes`,
`FoldLaneStash` and `SetStashWidths` in
`src/oram/levelarena/cpu_byteslice_level_arena_job.hpp`.

A laned stage splits its one-lane shed order into contiguous runs, one per
lane. Each lane sheds into a private, initially empty stash with its own
capacity check; at the stage's end every lane's stash buckets are merged into
the phase's stash, lane after lane and bucket after bucket, with the checked
merge. A lane is a list of its private stash's bucket contents. Natively each
lane copy has its phase stash's own width, so `laneCapacity = capacity`.

Native premises: the lanes are contiguous runs of the one-lane order, in lane
order; stash insertion keeps shed order; and nothing leaves a stash during a
routing stage.
-/
namespace RebuildBound.Model.LaneFold

/-- A laned stage: every lane's private check, then the checked fold of all
lanes' buckets into the phase stash, which already holds `init`. -/
def run {α : Type} (laneCapacity capacity : Nat) (init : List α)
    (lanes : List (List (List α))) : Option (List α) :=
  if lanes.all (fun lane => lane.flatten.length ≤ laneCapacity) then
    DirectDrain.run capacity init lanes.flatten
  else none

end RebuildBound.Model.LaneFold
