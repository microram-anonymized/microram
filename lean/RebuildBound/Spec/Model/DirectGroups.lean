import RebuildBound.Spec.Model.DirectSelect
namespace RebuildBound.Model.DirectGroups
/-- Stable grouping of occurrence indices by their actual home. -/
def groups (U : Nat) (home : Nat → Nat) (source : List Nat) : List (List Nat) :=
  (List.range U).map (fun h => source.filter (fun i => home i == h))
end RebuildBound.Model.DirectGroups
