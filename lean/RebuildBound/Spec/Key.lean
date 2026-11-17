import RebuildBound.Spec.Model.Key

namespace RebuildBound.Spec
open Model

/-- Both adapters round-trip without a word-size or capacity restriction. -/
def LogicalKeyRoundtrip_statement : Prop :=
  (∀ key : LogicalKey, LogicalKey.ofNat (LogicalKey.toNat key) = key) ∧
  (∀ n : Nat, LogicalKey.toNat (LogicalKey.ofNat n) = n)

/-- Exact identity, including leading zero bytes and distinct lengths. -/
def LogicalKeyIdentity_statement : Prop :=
  (∀ a b : LogicalKey, LogicalKey.toNat a = LogicalKey.toNat b ↔ a = b) ∧
  (∀ a b : Nat, LogicalKey.ofNat a = LogicalKey.ofNat b ↔ a = b) ∧
  (∀ key : LogicalKey, (0 : Fin 256) :: key ≠ key) ∧
  (∀ n : Nat, ∃ key : LogicalKey, n < key.length)

end RebuildBound.Spec
