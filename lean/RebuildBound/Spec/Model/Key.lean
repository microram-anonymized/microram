import Std

/-!
# Logical keys and routing words

The byte-string domain has exact length-sensitive equality and no capacity or
native-width bound. Records, requests and routing functions use this concrete domain. Numeric
encodings occur only at compatibility and fixture boundaries.
-/
namespace RebuildBound.Model

abbrev LogicalKey := List (Fin 256)
abbrev Word64 := Fin (2 ^ 64)

namespace LogicalKey

/-- A bijective base-256 encoding. The extra one preserves empty and leading
zero bytes; this is an exact mathematical adapter, not a routing hash. -/
def toNat : LogicalKey → Nat
  | [] => 0
  | b :: bs => b.val + 1 + 256 * toNat bs

/-- Decode an unbounded numeric fixture identifier into an exact byte string. -/
def ofNat : Nat → LogicalKey
  | 0 => []
  | n + 1 => ⟨n % 256, Nat.mod_lt _ (by decide)⟩ :: ofNat (n / 256)
termination_by n => n
decreasing_by omega

/-- The exact boundary encoding retains every byte and the full length. -/
theorem ofNat_toNat (key : LogicalKey) : ofNat (toNat key) = key := by
  induction key with
  | nil => simp [toNat, ofNat]
  | cons b bs ih =>
    have hb := b.isLt
    have hmod : (b.val + 256 * toNat bs) % 256 = b.val := by omega
    have hdiv : (b.val + 256 * toNat bs) / 256 = toNat bs := by omega
    have hsucc : b.val + 1 + 256 * toNat bs =
        (b.val + 256 * toNat bs) + 1 := by omega
    simp only [toNat, hsucc, ofNat, hdiv, ih]
    congr 1
    exact Fin.ext hmod

/-- Numeric fixture identifiers also round-trip without a width bound. -/
theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [toNat, ofNat]
    | succ n =>
      have hlt : n / 256 < n + 1 := by omega
      simp only [ofNat, toNat, ih _ hlt]
      omega

end LogicalKey
end RebuildBound.Model
