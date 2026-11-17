import RebuildBound.Spec.Model.DirectPrefix

/-! Scalar semantics of cached home bytes and their candidate-mask intersection.
The native loops are `DenseHomeLines`, `ComputeDenseHomesRange` and
`DenseHomeCandidates` in `src/oram/rebuild/cpu_byteslice_dense_select.hpp`.
A cache represents one fixed physical lane across byte lines. Payload/cache
storage is independent of its remaining-mask bit; clears do not rewrite bytes.
The cache encoding contract below is explicit: native hashing, SIMD packing,
64-bit shifts and the physical byte-line layout have not been extracted. -/
namespace RebuildBound.Model.DirectCache

/-- The native line-count branch includes one zero line at zero home bits. -/
def lines (bits : Nat) : Nat :=
  if bits ≤ 8 then 1 else (bits + 7) / 8

/-- Little-endian base-256 byte of an arbitrary natural number. -/
def byte (value index : Nat) : Nat := (value / 256 ^ index) % 256

/-- Cached bytes for one immutable source payload lane. -/
def cached (word : LogicalKey → Nat) (bits : Nat) (r : Rec) (index : Nat) : Nat :=
  byte (DirectPrefix.cachedHome word (2 ^ bits) r) index

/-- Lane-level intersection of the remaining bit and all byte equalities. -/
def candidate (bits : Nat) (cache : Nat → Nat) (remaining : Bool) (home : Nat) : Bool :=
  remaining && (List.range (lines bits)).all (fun j => cache j == byte home j)

/-- Extraction premise for the used bytes only. A false remaining bit
makes the candidate false regardless of cache contents. -/
def Encodes (bits : Nat) (cache : Nat → Nat) (value : Nat) : Prop :=
  ∀ j, j < lines bits → cache j = byte value j

end RebuildBound.Model.DirectCache
