import RebuildBound.Spec.Model.DirectSelect
/-! Logical remaining-mask updates on unique occurrence indices. Each completed
home clears precisely its stable selected prefix. The fold preserves source
order and permits pauses between homes. Native pdep and cached-home candidate
computation are separate correspondence obligations. -/
namespace RebuildBound.Model.DirectRemaining

def clear (selected source : List Nat) : List Nat :=
  source.filter (fun i => i ∉ selected)

def run (cap : Nat) (source : List Nat) (homes : List (List Nat)) : List Nat :=
  homes.foldl (fun remaining xs => clear (xs.take cap) remaining) source

end RebuildBound.Model.DirectRemaining
