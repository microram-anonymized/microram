import RebuildBound.Spec.Model.DirectMaskSweep

/-! Native pair-index decoding and task ranges of `kPrefixLogDedup`
(`src/oram/scheduler/cpu_byteslice_subtask_run.hpp`), planned by
`PlanBuildDenseDirect` (`cpu_byteslice_level_arena_merge.hpp`) as
`PlanTaggedRange` slices of `[0, DensePrefixDedupPairs)`.

The prefix is one flat array of `unit · count` buckets (`unit` =
`StashBuckets`, `count` = `PrefixFlushes`). Pair index `p` names one bucket
comparison: `p / unit²` is the unit pair, numbered `fresh (fresh - 1) / 2 + older`
by the native triangular loop, and `p % unit²` is older-bucket-major,
fresh-bucket-minor within it. Each comparison reads the current fresh bucket
and updates only the older one.

This closes pair-index decoding, flat bucket indices and task cuts inside a
unit-pair block. That the scheduler runs this ordered stage's slices in plan
order, byte offsets, and the fixed-width comparison remain separate.
-/
namespace RebuildBound.Model.DirectMaskIndex

/-- The native `fresh = 1; while (pu >= fresh) pu -= fresh++;`, entered with
`fresh + 1`; returns the (older, fresh) unit pair. -/
def unitPairFrom (fresh pu : Nat) : Nat × Nat :=
  if pu < fresh + 1 then (pu, fresh + 1)
  else unitPairFrom (fresh + 1) (pu - (fresh + 1))
termination_by pu

/-- Flat (older, fresh) bucket indices of pair index `p`. -/
def decode (unit p : Nat) : Nat × Nat :=
  let units := unitPairFrom 0 (p / (unit * unit))
  let within := p % (unit * unit)
  (units.1 * unit + within / unit, units.2 * unit + within % unit)

/-- `DensePrefixDedupPairs`: `unit² · count (count - 1) / 2`. -/
def pairs (unit count : Nat) : Nat := unit * unit * (count * (count - 1) / 2)

/-- One bucket comparison, reading the fresh bucket from the current state.
Out-of-range indices read an empty bucket or leave the state unchanged. -/
def step (compare : DirectMasks.Comparison) (unit : Nat)
    (buckets : List Bucket) (p : Nat) : List Bucket :=
  buckets.modify (decode unit p).1
    (DirectMasks.pair compare (buckets.getD (decode unit p).2 []))

/-- One task: the pair indices `[begin, stop)` in increasing order. -/
def runRange (compare : DirectMasks.Comparison) (unit : Nat)
    (buckets : List Bucket) (begin stop : Nat) : List Bucket :=
  (List.range' begin (stop - begin)).foldl (step compare unit) buckets

/-- `PlanTaggedRange`: consecutive slices of `width` indices, 0 meaning 1. -/
def plan (width begin stop : Nat) : List (Nat × Nat) :=
  if begin < stop then
    (begin, min stop (begin + max width 1)) ::
      plan width (min stop (begin + max width 1)) stop
  else []
termination_by stop - begin
decreasing_by omega

/-- Run tasks in order. -/
def runTasks (compare : DirectMasks.Comparison) (unit : Nat)
    (buckets : List Bucket) (tasks : List (Nat × Nat)) : List Bucket :=
  tasks.foldl (fun state task => runRange compare unit state task.1 task.2) buckets

end RebuildBound.Model.DirectMaskIndex
