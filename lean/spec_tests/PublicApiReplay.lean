import RebuildBound.Oracle.PublicApiDiff

/-! The compressed one-bucket initialization evaluator agrees with the ORIGINAL
full dense model on small geometries, including all-to-one routing and collisions.
This regression does not assert a universal sparse-evaluator refinement theorem. -/
namespace RebuildBound.PublicApiReplayTests
open Model Oracle.PublicApiDiff
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def agrees (k seed n : Nat) : Bool :=
  let g : TPGeom := ⟨64,k,1,1,3,min k 4,k-min k 4,true⟩
  let input := (List.range n).map fun i => (⟨LogicalKey.ofNat (i+1),37*i,false⟩ : Model.Rec)
  let w := fun key : LogicalKey =>
    let key := LogicalKey.toNat key
    if seed == 0 then 0 else if seed == 1 then 2^k-1
    else key * (2*seed+1) + key / 3
  match initJob engineRule g w input with
  | .error _ => false
  | .ok o =>
    let compact := o.main.zipIdx.filterMap fun (b,i) => if occupied b == 0 then none else some (i,b)
    compact == sparseInit k w input && o.tier.all Option.isNone

#guard ((List.range' 1 7).all fun k =>
  (List.range 4).all fun seed => [0,1,17,32].all fun n => agrees k seed n)

-- The physical codec retains payload, tombstone and unshadowed bits.
#guard stored (logical ⟨LogicalKey.ofNat (7), 0xA000, true⟩) == (⟨LogicalKey.ofNat (7),0xA000,true⟩ : Model.Rec)
#guard stored (logical ⟨LogicalKey.ofNat (7), 0xFF, false⟩) == (⟨LogicalKey.ofNat (7),0xFF,false⟩ : Model.Rec)
-- Four-byte payloads preserve the high byte and metadata above bit 31.
#guard storedFor 32 (logicalFor 32 ⟨LogicalKey.ofNat (7), 0xA0FEDCBA98, true⟩) ==
  (⟨LogicalKey.ofNat (7),0xA0FEDCBA98,true⟩ : Model.Rec)
#guard storedFor 32 (logicalFor 32 ⟨LogicalKey.ofNat (7), 0xFEDCBA98, false⟩) ==
  (⟨LogicalKey.ofNat (7),0xFEDCBA98,false⟩ : Model.Rec)
end RebuildBound.PublicApiReplayTests
