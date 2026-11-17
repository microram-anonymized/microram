import RebuildBound.Spec.Model.DirectCapacity
/-! Logical checked source-order drain. Chunks represent the surviving lanes
of successive source buckets. A failing append returns no publishable result;
this does not assert that native scratch storage is rolled back on failure.
The physical stash implementation and mask extraction remain separate. -/
namespace RebuildBound.Model.DirectDrain

def appendChecked {α : Type} (capacity : Nat) (state chunk : List α) : Option (List α) :=
  if (state ++ chunk).length ≤ capacity then some (state ++ chunk) else none

def run {α : Type} (capacity : Nat) : List α → List (List α) → Option (List α)
  | state, [] => some state
  | state, chunk :: chunks =>
    (appendChecked capacity state chunk).bind (fun next => run capacity next chunks)

/-- Digit one drains directly into the configured output tier. Above digit
one the temporary B producer has exactly one 64-slot bucket. -/
def tierCapacity (digit output : Nat) : Nat := DirectCapacity.producerCapacity digit 64 output

end RebuildBound.Model.DirectDrain
