import RebuildBound.Spec.Model.DirectCache

/-! Fixed-width scalar semantics of `ComputeDenseHomesRange` and
`DenseHomeCandidates` in `src/oram/rebuild/cpu_byteslice_dense_select.hpp`.
The mask has 64 lanes and the cache uses the native byte-line offsets.
The comparison primitive is specified by its lane bits; extracting the SIMD
packing (`LowByteLine`) and comparison instructions remains a native obligation.
Likewise, this model takes an already computed tag and does not assert an AES law.
-/
namespace RebuildBound.Model.DirectCache64

abbrev Storage := Nat → BitVec 8

/-- LowMask64 on the supported domain `bits ≤ 64`, including both endpoints. -/
def lowMask (bits : Nat) : BitVec 64 := BitVec.ofNat 64 (2 ^ bits - 1)

/-- Logical right shift followed by extraction of the low byte. -/
def wordByte (word : BitVec 64) (j : Nat) : BitVec 8 :=
  (word >>> (8 * j)).setWidth 8

/-- Per-lane arithmetic before `LowByteLine` packs the byte line. -/
def storedByte (bits : Nat) (raw : BitVec 64) (j : Nat) : BitVec 8 :=
  wordByte (raw &&& lowMask bits) j

/-- Byte-line layout: bucket, byte of the cached home, then physical lane. -/
def offset (bits bucket j lane : Nat) : Nat :=
  (bucket * DirectCache.lines bits + j) * 64 + lane

/-- Lane semantics of one 64-byte equality comparison. -/
def equalMask (bits : Nat) (storage : Storage) (bucket j : Nat)
    (home : BitVec 64) : BitVec 64 :=
  (BitVec.ofBoolListLE ((List.range 64).map (fun lane =>
    storage (offset bits bucket j lane) == wordByte home j))).setWidth 64

/-- The native loop intersects the remaining mask with each comparison mask. -/
def candidates (bits : Nat) (storage : Storage) (bucket : Nat)
    (remaining home : BitVec 64) : BitVec 64 :=
  (List.range (DirectCache.lines bits)).foldl
    (fun mask j => mask &&& equalMask bits storage bucket j home) remaining

end RebuildBound.Model.DirectCache64
