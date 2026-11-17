import RebuildBound.Spec.Model.DirectCache64

namespace RebuildBound.Spec
open Model Model.DirectCache64

/-- Masking and shifting a 64-bit tag produces the existing reference byte. -/
def DirectCache64Byte_statement : Prop :=
  ∀ (bits : Nat) (raw : BitVec 64) (j : Nat), bits ≤ 64 →
    (storedByte bits raw j).toNat = DirectCache.byte (raw.toNat % 2 ^ bits) j

/-- The byte-line mask loop refines the existing scalar candidate predicate,
even for malformed caches and cleared lanes. -/
def DirectCache64Fold_statement : Prop :=
  ∀ (bits : Nat) (storage : Storage) (bucket : Nat)
    (remaining home : BitVec 64) (lane : Nat), lane < 64 →
    (candidates bits storage bucket remaining home).getLsbD lane =
      DirectCache.candidate bits
        (fun j => (storage (offset bits bucket j lane)).toNat)
        (remaining.getLsbD lane) home.toNat

/-- A packed cache containing the computed bytes selects exactly live lanes
at the requested home. The storage premise is precisely the remaining native
packing/layout obligation, and only used bytes of this lane are required. -/
def DirectCache64Candidate_statement : Prop :=
  ∀ (bits : Nat) (storage : Storage) (bucket : Nat)
    (remaining home raw : BitVec 64) (lane : Nat),
    bits ≤ 64 → lane < 64 → home.toNat < 2 ^ bits →
    (∀ j, j < DirectCache.lines bits →
      storage (offset bits bucket j lane) = storedByte bits raw j) →
    ((candidates bits storage bucket remaining home).getLsbD lane = true ↔
      remaining.getLsbD lane = true ∧ raw.toNat % 2 ^ bits = home.toNat)

/-- Mask clears commute with candidate calculation without rewriting bytes
or requiring a well-formed cache. -/
def DirectCache64Clear_statement : Prop :=
  ∀ (bits : Nat) (storage : Storage) (bucket : Nat)
    (remaining keep home : BitVec 64),
    candidates bits storage bucket (remaining &&& keep) home =
      candidates bits storage bucket remaining home &&& keep

end RebuildBound.Spec
