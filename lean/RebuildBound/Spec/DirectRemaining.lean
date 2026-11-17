import RebuildBound.Spec.Model.DirectRemaining
import RebuildBound.Spec.Model.DirectDrain
namespace RebuildBound.Spec
open Model Model.DirectRemaining

def DirectRemainingFold_statement : Prop :=
  ∀ cap source homes,
    run cap source homes = clear (DirectB.main cap homes).flatten source

def DirectRemainingDrain_statement : Prop :=
  ∀ cap source homes, DirectSelect.Grouped source homes →
    run cap source homes = DirectSelect.drain cap source homes

def DirectRemainingOccupancy_statement : Prop :=
  ∀ cap source homes, DirectSelect.Grouped source homes →
    (run cap source homes).length = DirectB.excess cap homes

/-- Source buckets keep their boundaries through the logical mask updates. -/
def DirectRemainingChunks_statement : Prop :=
  ∀ (cap : Nat) (chunks homes : List (List Nat)),
    (chunks.map (fun source => run cap source homes)).flatten =
      run cap chunks.flatten homes

/-- Earlier homes cannot clear a candidate for a distinct unprocessed home. -/
def DirectRemainingFreshHome_statement : Prop :=
  ∀ (cap : Nat) (source : List Nat) (homes : List (List Nat))
    (home : Nat → Nat) (h : Nat),
    (∀ xs ∈ homes, ∀ i ∈ xs, home i ≠ h) →
    (run cap source homes).filter (fun i => home i == h) =
      source.filter (fun i => home i == h)

end RebuildBound.Spec
