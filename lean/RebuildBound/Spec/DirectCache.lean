import RebuildBound.Spec.Model.DirectCache

namespace RebuildBound.Spec
open Model Model.DirectCache

/-- Exactly the native line policy, sufficient to encode every home; at most
eight lines in the supported 64-bit word domain. -/
def DirectCacheLines_statement : Prop :=
  ∀ bits : Nat, 0 < lines bits ∧ bits ≤ 8 * lines bits ∧
    (bits ≤ 64 → lines bits ≤ 8)

/-- Equal bytes uniquely determine any value that fits in the chosen width. -/
def DirectCacheBytes_statement : Prop :=
  ∀ (count a b : Nat), a < 256 ^ count → b < 256 ^ count →
    ((∀ j, j < count → byte a j = byte b j) ↔ a = b)

/-- The exact home predicate follows from cached-byte agreement. The queried
home must be in range; truncating an out-of-range home can otherwise alias. -/
def DirectCacheHome_statement : Prop :=
  ∀ (bits : Nat) (word : LogicalKey → Nat) (r : Rec) (home : Nat),
    home < 2 ^ bits →
    ((∀ j, j < lines bits → cached word bits r j = byte home j) ↔
      DirectPrefix.cachedHome word (2 ^ bits) r = home)

/-- Native candidate-mask scalar semantics under an explicit lane-cache
encoding premise. This does not assume a cleared lane has a live payload. -/
def DirectCacheCandidate_statement : Prop :=
  ∀ (bits : Nat) (cache : Nat → Nat) (remaining : Bool) (value home : Nat),
    value < 2 ^ bits → home < 2 ^ bits → Encodes bits cache value →
    (candidate bits cache remaining home = true ↔ remaining = true ∧ value = home)

/-- Clearing a lane commutes with candidate calculation on its unchanged
cache, even if the cache is malformed or the requested home is out of range. -/
def DirectCacheClear_statement : Prop :=
  ∀ (bits : Nat) (cache : Nat → Nat) (remaining keep : Bool) (home : Nat),
    candidate bits cache (remaining && keep) home =
      (candidate bits cache remaining home && keep)

end RebuildBound.Spec
