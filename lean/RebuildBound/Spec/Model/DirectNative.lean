import RebuildBound.Spec.Model.DirectMask64
import RebuildBound.Spec.Model.DirectSelect64
import RebuildBound.Spec.Model.DirectMaskedRecords

/-! The level-one direct B build on the native flat prefix, at lane level:
`kPrefixLogDedup` over every pair index (`DirectMask64`), the home selection
over homes `0 .. U-1` (`DirectSelect64`) and the drain's capacity checks.
Records are read back from the read-only payloads at (bucket, lane) addresses.

`homeMask` is the lane-level home predicate. It is part of this model, not a
premise. The native byte cache computes it through
`DirectNativeCacheCandidate`/`DirectNativeCacheHomeMask` under their storage
premise, with `U = 2^bits` and the tag's low bits as `word`. The tier is the
drained addresses in bucket and lane order; the residual stash's internal
permutation, payload bytes and the scheduler's in-order execution remain native.
-/
namespace RebuildBound.Model.DirectNative

open DirectSelect64 in
/-- Lanes of source bucket `s` whose payload's home is `h`. -/
def homeMask (U : Nat) (word : LogicalKey → Nat) (data : Nat → DirectMask64.Payload)
    (s h : Nat) : BitVec 64 :=
  ofLanes fun lane => DirectPrefix.cachedHome word U (data s lane) == h

def payloadAt (data : Nat → DirectMask64.Payload) (a : DirectSelect64.Address) : Rec :=
  data a.1 a.2

/-- Dedup, select and drain on `unit · count` flat buckets; `none` is the
declared tier overflow. -/
def build (compare : DirectMasks.Comparison) (digit output U unit count : Nat)
    (word : LogicalKey → Nat) (data : Nat → DirectMask64.Payload) (masks : List (BitVec 64)) :
    Option (List (List Rec) × List Rec) :=
  let deduped := DirectMask64.runRange compare data unit masks 0
    (DirectMaskIndex.pairs unit count)
  let sel := DirectSelect64.selectHomes (homeMask U word data) deduped (List.range U)
  (DirectSelect64.drainCount (DirectDrain.tierCapacity digit output) sel.1).map fun _ =>
    (sel.2.map (fun out => out.1.filterMap (Option.map (payloadAt data))),
      (DirectSelect64.addresses sel.1).flatten.map (payloadAt data))

end RebuildBound.Model.DirectNative
