import RebuildBound.Spec.Model.Key
import Mathlib.Data.Finset.Card

/-! Explicit adapters for historical numeric regression identifiers. Model
records and requests always retain byte keys; these helpers do not introduce
numeric coercions or a bound on the model key space. -/
namespace RebuildBound.Model

attribute [simp] LogicalKey.toNat_ofNat LogicalKey.ofNat_toNat

def fixtureKeys (ids : Finset Nat) : Finset LogicalKey := ids.image LogicalKey.ofNat

@[simp] theorem mem_fixtureKeys (key : LogicalKey) (ids : Finset Nat) :
    key ∈ fixtureKeys ids ↔ LogicalKey.toNat key ∈ ids := by
  constructor
  · intro h
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp h
    simpa only [LogicalKey.toNat_ofNat] using hn
  · intro h
    exact Finset.mem_image.mpr ⟨LogicalKey.toNat key, h, LogicalKey.ofNat_toNat key⟩

@[simp] theorem card_fixtureKeys (ids : Finset Nat) : (fixtureKeys ids).card = ids.card := by
  apply Finset.card_image_of_injective
  intro a b h
  simpa only [LogicalKey.toNat_ofNat] using congrArg LogicalKey.toNat h

end RebuildBound.Model
