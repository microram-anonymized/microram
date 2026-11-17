import RebuildBound.Spec.Model.DirectMaskBuckets

/-! Indexed chronological comparisons over preloaded mutable flush units.

`step` reads the fresh unit from the current state and updates only the older
unit. Each command groups the physical bucket comparisons already modeled by
`DirectMaskBuckets.pair`. `schedule` visits fresh units increasingly, then all
their older units, as in `kPrefixLogDedup`.

This closes the preloaded-state versus append-fold boundary. Decoding the
native triangular pair index and physical bucket offsets, task cuts inside a
unit-pair block, fixed-width masks and SIMD comparisons remain separate.
The definitions are total on arbitrary commands; correspondence to chronology
is claimed only for `schedule`, with the stated prefix bound.
-/
namespace RebuildBound.Model.DirectMaskSweep

abbrev Command := Nat × Nat

/-- One (older, fresh) unit comparison, reading the current fresh masks. -/
def step (compare : DirectMasks.Comparison)
    (state : List DirectMaskBuckets.FlushUnit) (command : Command) :
    List DirectMaskBuckets.FlushUnit :=
  state.modify command.1
    (DirectMaskBuckets.pair compare (state.getD command.2 []))

/-- Fresh-unit-major, older-unit-minor order; unit zero needs no comparison. -/
def schedule (count : Nat) : List Command :=
  (List.range count).flatMap fun fresh =>
    (List.range fresh).map fun older => (older, fresh)

/-- Execute unit-pair commands in order, retaining every preloaded unit. -/
def run (compare : DirectMasks.Comparison)
    (state : List DirectMaskBuckets.FlushUnit) (commands : List Command) :
    List DirectMaskBuckets.FlushUnit :=
  commands.foldl (step compare) state

end RebuildBound.Model.DirectMaskSweep
