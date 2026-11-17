import RebuildBound.Spec.Model.DirectMaskIndex

/-! 64-lane mask-word semantics of one `kPrefixLogDedup` comparison,
`masks[o] &= ~CrossBucketDuplicateMask(fresh, masks[f], older, masks[o])`
(`cpu_byteslice_subtask_run.hpp`, `cpu_byteslice_dedup_masks.hpp`).

A native bucket is a lane payload function and a 64-bit real-lane mask; the
dedup never writes payloads. `duplicateMask` is specified by its lane bits with
a pairwise comparison. Stored keys below sixteen bytes, and sixteen-byte keys in
exact builds, are compared pairwise. With VP2INTERSECT and the default wide-key
option, sixteen-byte stored keys are compared segment-wise, which is not of this
form (`Spec/NativeMatch.lean` bounds that rule's false matches). Extracting the lane bits from the VP2INTERSECT kernels, including
zero-key dummy repair, and the byte-line payload layout remain native.
-/
namespace RebuildBound.Model.DirectMask64

abbrev Payload := Nat → Rec

/-- The lane list that a payload and a real-lane mask represent. -/
def bucket (data : Payload) (mask : BitVec 64) : Bucket :=
  (List.range 64).map fun lane => if mask.getLsbD lane then some (data lane) else none

/-- Lane bits of `CrossBucketDuplicateMask`: real older lanes whose key matches
the key of some real fresh lane. -/
def duplicateMask (compare : DirectMasks.Comparison) (freshData : Payload)
    (freshMask : BitVec 64) (olderData : Payload) (olderMask : BitVec 64) :
    BitVec 64 :=
  (BitVec.ofBoolListLE ((List.range 64).map fun lane =>
    olderMask.getLsbD lane && (List.range 64).any fun j =>
      freshMask.getLsbD j && compare (freshData j).key (olderData lane).key)).setWidth 64

/-- The older mask after the native update. -/
def pairMask (compare : DirectMasks.Comparison) (freshData : Payload)
    (freshMask : BitVec 64) (olderData : Payload) (olderMask : BitVec 64) :
    BitVec 64 :=
  olderMask &&& ~~~duplicateMask compare freshData freshMask olderData olderMask

/-- One native pair index on the mask array; payloads are read-only. -/
def step (compare : DirectMasks.Comparison) (data : Nat → Payload) (unit : Nat)
    (masks : List (BitVec 64)) (p : Nat) : List (BitVec 64) :=
  masks.modify (DirectMaskIndex.decode unit p).1
    (pairMask compare (data (DirectMaskIndex.decode unit p).2)
      (masks.getD (DirectMaskIndex.decode unit p).2 0)
      (data (DirectMaskIndex.decode unit p).1))

/-- One native task over the mask array. -/
def runRange (compare : DirectMasks.Comparison) (data : Nat → Payload) (unit : Nat)
    (masks : List (BitVec 64)) (begin stop : Nat) : List (BitVec 64) :=
  (List.range' begin (stop - begin)).foldl (step compare data unit) masks

/-- The lane lists of the flat bucket array. -/
def buckets (data : Nat → Payload) (masks : List (BitVec 64)) : List Bucket :=
  masks.mapIdx fun b mask => bucket (data b) mask

end RebuildBound.Model.DirectMask64
