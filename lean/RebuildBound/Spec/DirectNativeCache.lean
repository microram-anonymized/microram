import RebuildBound.Spec.Model.DirectNative

/-! The packed byte cache supplies the home predicate used by `DirectNative`.
The stored bytes must come from the same key-based tags as the native build's
word family. Native packing, SIMD comparison extraction and the engine's tag
correspondence remain obligations. -/
namespace RebuildBound.Spec
open Model

/-- At an in-range home, packed-cache candidates are precisely the remaining
lanes selected by `DirectNative.homeMask`, for any remaining mask. -/
def DirectNativeCacheCandidate_statement : Prop :=
  ∀ (bits : Nat) (storage : DirectCache64.Storage)
    (tags : LogicalKey → BitVec 64) (data : Nat → DirectMask64.Payload)
    (bucket : Nat) (remaining home : BitVec 64),
    bits ≤ 64 → home.toNat < 2 ^ bits →
    (∀ lane, lane < 64 → ∀ j, j < DirectCache.lines bits →
      storage (DirectCache64.offset bits bucket j lane) =
        DirectCache64.storedByte bits (tags (data bucket lane).key) j) →
    DirectCache64.candidates bits storage bucket remaining home =
      remaining &&& DirectNative.homeMask (2 ^ bits) (fun key => (tags key).toNat)
        data bucket home.toNat

/-- The all-ones cache query produces the native home mask. A natural home
below `2^bits` fits in the 64-bit argument without truncation. -/
def DirectNativeCacheHomeMask_statement : Prop :=
  ∀ (bits : Nat) (storage : DirectCache64.Storage)
    (tags : LogicalKey → BitVec 64) (data : Nat → DirectMask64.Payload) (bucket home : Nat),
    bits ≤ 64 → home < 2 ^ bits →
    (∀ lane, lane < 64 → ∀ j, j < DirectCache.lines bits →
      storage (DirectCache64.offset bits bucket j lane) =
        DirectCache64.storedByte bits (tags (data bucket lane).key) j) →
    DirectCache64.candidates bits storage bucket (BitVec.allOnes 64) (BitVec.ofNat 64 home) =
      DirectNative.homeMask (2 ^ bits) (fun key => (tags key).toNat) data bucket home

end RebuildBound.Spec
