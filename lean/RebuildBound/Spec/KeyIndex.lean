import RebuildBound.Spec.Model.Key
import Mathlib.Data.Fintype.EquivFin

/-! Finite views indexed by exact logical keys. The bound limits
only this view; it is neither a key-width nor a storage-capacity rule. -/
namespace RebuildBound.Spec
open Model

abbrev KeyIndex (N : Nat) := {key : LogicalKey // key.toNat < N}

namespace KeyIndex

def range (N : Nat) : Finset LogicalKey := (Finset.range N).image LogicalKey.ofNat

@[simp] theorem mem_range {key : LogicalKey} {N : Nat} : key ∈ range N ↔ key.toNat < N := by
  simp only [range, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    simpa only [LogicalKey.toNat_ofNat] using hn
  · intro h
    exact ⟨key.toNat, h, LogicalKey.ofNat_toNat key⟩

@[simp] theorem range_card (N : Nat) : (range N).card = N := by
  rw [range, Finset.card_image_of_injective]
  · exact Finset.card_range N
  · intro a b h
    simpa only [LogicalKey.toNat_ofNat] using congrArg LogicalKey.toNat h


def equivFin (N : Nat) : KeyIndex N ≃ Fin N where
  toFun key := ⟨key.val.toNat, key.property⟩
  invFun n := ⟨LogicalKey.ofNat n.val, by simpa only [LogicalKey.toNat_ofNat] using n.isLt⟩
  left_inv key := by apply Subtype.ext; exact LogicalKey.ofNat_toNat key.val
  right_inv n := by apply Fin.ext; exact LogicalKey.toNat_ofNat n.val

instance (N : Nat) : Fintype (KeyIndex N) := Fintype.ofEquiv (Fin N) (equivFin N).symm

@[simp] theorem card (N : Nat) : Fintype.card (KeyIndex N) = N := by
  simpa using Fintype.card_congr (equivFin N)

theorem isLt {N : Nat} (key : KeyIndex N) : key.val.toNat < N := key.property

end KeyIndex
end RebuildBound.Spec
