import RebuildBound.Spec.Model.DirectDrain
import RebuildBound.Spec.Model.DirectB
namespace RebuildBound.Spec
open Model.DirectDrain

def DirectDrainExact_statement : Prop :=
  ∀ (capacity : Nat) (state : List Nat) (chunks : List (List Nat)),
    state.length ≤ capacity →
    run capacity state chunks =
      if (state ++ chunks.flatten).length ≤ capacity
      then some (state ++ chunks.flatten) else none

def DirectDrainRechunk_statement : Prop :=
  ∀ (capacity : Nat) (state : List Nat) (first second : List (List Nat)),
    state.length ≤ capacity → first.flatten = second.flatten →
    run capacity state first = run capacity state second

end RebuildBound.Spec
