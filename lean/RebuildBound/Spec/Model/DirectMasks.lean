import RebuildBound.Spec.Model.DirectPrefix

/-! Abstract chronological pairwise mask semantics.
A unit is a lane list with absent lanes represented by `none`. Only older
masks change, and units are visited oldest to newest, as in `kPrefixLogDedup`
in `src/oram/scheduler/cpu_byteslice_subtask_run.hpp`.
`ExactComparison` is an explicit premise, material for wide-key false positives.
This is not SIMD extraction, bit packing, scheduler pair-index decoding, or
multi-bucket layout correspondence; it formalizes grouped unit comparisons. -/
namespace RebuildBound.Model.DirectMasks
abbrev Comparison := LogicalKey → LogicalKey → Bool
/-- Exact-key comparison event. -/
def ExactComparison (compare : Comparison) : Prop :=
  ∀ fresh old, compare fresh old = (fresh == old)
/-- Clear matching real older lanes; preserve lane positions and record data. -/
def pair (compare : Comparison) (fresh older : Bucket) : Bucket :=
  older.map fun lane => lane.filter fun old =>
    !(fresh.recs.any fun r => compare r.key old.key)
/-- Visit every older unit and append the fresh unit unchanged. -/
def step (compare : Comparison) (older : List Bucket) (fresh : Bucket) : List Bucket :=
  older.map (pair compare fresh) ++ [fresh]
/-- Resumable chronological mask pass. -/
def run (compare : Comparison) (state units : List Bucket) : List Bucket :=
  units.foldl (step compare) state
/-- Stable lane-order extraction. -/
def records (units : List Bucket) : List Rec := units.flatMap Bucket.recs
end RebuildBound.Model.DirectMasks
