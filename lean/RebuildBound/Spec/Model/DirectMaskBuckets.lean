import RebuildBound.Spec.Model.DirectMasks

/-! Multi-bucket flush units for the direct prefix mask pass.

For each older bucket, `pair` visits the fresh unit's buckets in order,
updating only the older mask. This is the old-bucket-major, fresh-bucket-minor
loop in `kPrefixLogDedup` (`cpu_byteslice_subtask_run.hpp`). Chronological
steps retain physical bucket and lane boundaries, including empty buckets.

The missing adapter in `DirectMasks` is that its unit is one lane list,
whereas a native flush unit can contain several buckets. Flattening each unit
will relate this loop to that existing model. The indexed sweep over preloaded
native state, pair-index decoding, task ranges, fixed-width mask/SIMD extraction
and native memory layout remain separate.
-/
namespace RebuildBound.Model.DirectMaskBuckets

abbrev FlushUnit := List Bucket

/-- Compare every fresh bucket against each older bucket. Fresh masks and all
payloads remain unchanged; successive comparisons see the updated older mask. -/
def pair (compare : DirectMasks.Comparison) (fresh older : FlushUnit) : FlushUnit :=
  older.map fun bucket =>
    fresh.foldl (fun masked freshBucket => DirectMasks.pair compare freshBucket masked) bucket

/-- Chronological unit step, retaining the fresh unit unchanged. -/
def step (compare : DirectMasks.Comparison)
    (older : List FlushUnit) (fresh : FlushUnit) : List FlushUnit :=
  older.map (pair compare fresh) ++ [fresh]

/-- Resume at a complete flush-unit boundary. This does not decode arbitrary
native task slices through the middle of a unit comparison. -/
def run (compare : DirectMasks.Comparison)
    (state units : List FlushUnit) : List FlushUnit :=
  units.foldl (step compare) state

end RebuildBound.Model.DirectMaskBuckets
