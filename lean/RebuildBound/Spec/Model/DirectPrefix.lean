import RebuildBound.Spec.Model.Basic

/-! Chronological, exact-key specification for the direct B prefix.

The input is in oldest-to-newest order. Records within each native flush unit
must already have distinct keys; chronology between flush units determines the
winner. This specification also defines a last-lane winner on arbitrary lists,
without claiming native correspondence for malformed flush units.
Tombstones participate exactly like values and are retained.

This is a logical specification, not an extraction of SIMD dedup masks,
cached-home byte lines, selection chunks or the checked drain.

Native source anchors (repository-relative paths):
* `src/oram/levelarena/cpu_byteslice_level_arena_dense.hpp`: oldest-first units
  and `ClearFromCurrentUnit`'s within-unit uniqueness prerequisite.
* `src/oram/scheduler/cpu_byteslice_subtask_run.hpp`: `kPrefixLogDedup` visits pairs
  in increasing fresh-unit order and mutates only the old unit's masks.
* `src/oram/rebuild/cpu_byteslice_dedup_masks.hpp`: sixteen-byte stored keys
  can have segmentwise false positives under the default VP2INTERSECT option;
  correspondence requires the exact-key comparison event, not an unconditional
  equality assumption about that code.
* `src/oram/rebuild/cpu_byteslice_dense_select.hpp`: selection and drain retain
  source order. `DirectB.residual` instead concatenates in home order; its
  occupancy theorem is not a proof of equality to the native drain sequence.
-/
namespace RebuildBound.Model.DirectPrefix

/-- Stable chronological dedup: retain precisely the last occurrence of each
exact key, with its complete value and tombstone flag. -/
def winners : List Rec → List Rec
  | [] => []
  | r :: rs =>
    if r.key ∈ rs.map Rec.key then winners rs else r :: winners rs

/-- Independently specified newest record, searching from the fresh end. -/
def latest (key : LogicalKey) (rs : List Rec) : Option Rec :=
  rs.reverse.find? (fun r => r.key == key)

/-- Logical effect of a fresh, internally unique flush unit: clear its keys
from all older survivors, then retain the entire fresh unit. -/
def unitStep (older fresh : List Rec) : List Rec :=
  older.filter (fun r => r.key ∉ fresh.map Rec.key) ++ fresh

/-- A resumable chronological fold. The accumulator and each unit retain
source order; this is not the native pairwise mutable-mask algorithm. -/
def runUnits (state : List Rec) (units : List (List Rec)) : List Rec :=
  units.foldl unitStep state

/-- The cache is key-based and uses the current job's word family. For native
power-of-two U, this is the low-bit home; U > 0 is needed for an in-range home. -/
def cachedHome (word : LogicalKey → Nat) (U : Nat) (r : Rec) : Nat :=
  word r.key % U

end RebuildBound.Model.DirectPrefix
