import RebuildBound.Spec.Model.OnlineBatch

/-! A public shape condition for requester chronology. Every internal operation
ends at or before the next unit boundary; suppressed lanes still count as
positions. External batch boundaries need not coincide with these cuts. -/
namespace RebuildBound.Model.RequesterCuts

def WidthsFit (entries : Nat) : Nat → List Nat → Prop
  | _, [] => True
  | position, width :: rest =>
      0 < width ∧ width ≤ entries - position % entries ∧
      WidthsFit entries (position + width) rest

/-- Logical lane boundary represented by a finite run's first `n` trace inputs.
The trace contains only frozen units. Its empty tail saturates this boundary
at the last complete unit, excluding any unfinished current-unit suffix. -/
def traceCutSlots (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun) (n : Nat) : Nat :=
  min (n * g.unitsPerPrefix)
    (OnlineBatch.stateAt g run run.ops.length).frozen.length * g.unitEntries

end RebuildBound.Model.RequesterCuts
