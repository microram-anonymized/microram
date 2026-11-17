import RebuildBound.Spec.DirectNativeCache

/-! Check the cache/native interface on a two-byte, two-bucket layout. Homes
1 and 257 share the low byte, so the high byte and bucket offset both matter.
`lake env lean spec_tests/DirectNativeCache.lean` (every `#guard` must pass). -/
open RebuildBound.Model

namespace DirectNativeCacheTests

def data : Nat → DirectMask64.Payload := fun bucket lane =>
  ⟨LogicalKey.ofNat (64 * bucket + lane), 1000 * bucket + lane, lane % 3 == 0⟩

-- Add discarded tag bits, and swap the two homes in the second bucket.
def tags (key : LogicalKey) : BitVec 64 :=
  let key := LogicalKey.toNat key
  BitVec.ofNat 64 (2 ^ 32 + 512 + 1 + 256 * ((key / 64 + key % 64) % 2))

-- Independently encode the low and high byte lines at their packed offsets.
def storage (address : Nat) : BitVec 8 :=
  if address / 64 % 2 = 0 then 1
  else BitVec.ofNat 8 ((address / 128 + address % 64) % 2)

#guard (List.range 2).all fun bucket => (List.range 64).all fun lane =>
  (List.range 2).all fun j =>
    storage (DirectCache64.offset 9 bucket j lane) ==
      DirectCache64.storedByte 9 (tags (data bucket lane).key) j

-- Matching lane bits reverse between the two buckets, including lane 63.
#guard DirectCache64.candidates 9 storage 0 (BitVec.allOnes 64) 257 == 0xAAAAAAAAAAAAAAAA
#guard DirectCache64.candidates 9 storage 1 (BitVec.allOnes 64) 257 == 0x5555555555555555

#guard (List.range 2).all fun bucket => [1, 257].all fun home =>
  ([0, 0x8000000000000001, 0x0123456789ABCDEF, BitVec.allOnes 64] : List (BitVec 64)).all
    fun remaining =>
      DirectCache64.candidates 9 storage bucket remaining (BitVec.ofNat 64 home) ==
        remaining &&& DirectNative.homeMask 512 (fun key => (tags key).toNat) data bucket home

-- A corrupted high byte invalidates the bridge: it loses bucket 0's lane 63.
def corrupt (address : Nat) : BitVec 8 := if address = 127 then 0 else storage address
#guard DirectCache64.candidates 9 corrupt 0 (BitVec.allOnes 64) 257 !=
  DirectNative.homeMask 512 (fun key => (tags key).toNat) data 0 257

end DirectNativeCacheTests
