import RebuildBound.Spec.LaneFold
/-! `lake env lean spec_tests/LaneFold.lean` (every `#guard` must pass). -/
open RebuildBound RebuildBound.Model

def laneSets : List (List (List (List Nat))) :=
  [[], [[]], [[[1, 2], [3]], [[4]]], [[[1, 2, 3, 4, 5]]], [[[1], [2], [3]], [], [[4, 5], [6]]],
   [[[1, 2]], [[3, 4]], [[5, 6]], [[7]]]]

#guard laneSets.all fun lanes => [[], [0], [0, 0, 0]].all fun init =>
  (List.range 9).all fun c => (List.range 4).all fun extra => c < init.length ||
    LaneFold.run (c + extra) c init lanes == DirectDrain.appendChecked c init lanes.flatten.flatten

-- without the init premise an empty fold does not re-check an overfull stash
#guard LaneFold.run 0 0 [0] [] == some [0] && DirectDrain.appendChecked 0 [0] [] == none

-- narrower lane copies fail a stage that fits
#guard LaneFold.run 1 2 [] [[[1, 2]]] == none &&
  (DirectDrain.appendChecked 2 [] [1, 2]).isSome
