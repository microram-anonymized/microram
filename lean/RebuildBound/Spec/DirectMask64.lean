import RebuildBound.Spec.Model.DirectMask64
import RebuildBound.Spec.Model.DirectMasks

namespace RebuildBound.Spec
open Model Model.DirectMask64

/-- Clearing the duplicate-mask bits from the older mask is the lane-list
comparison, for every comparison function and arbitrary payloads. -/
def DirectMask64Pair_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (freshData olderData : Payload)
    (freshMask olderMask : BitVec 64),
    bucket olderData (pairMask compare freshData freshMask olderData olderMask) =
      DirectMasks.pair compare (bucket freshData freshMask) (bucket olderData olderMask)

/-- A native task on the mask array refines the flat lane-list task, including
out-of-range indices. -/
def DirectMask64Run_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (data : Nat → Payload) (unit : Nat)
    (masks : List (BitVec 64)) (begin stop : Nat),
    buckets data (runRange compare data unit masks begin stop) =
      DirectMaskIndex.runRange compare unit (buckets data masks) begin stop

end RebuildBound.Spec
