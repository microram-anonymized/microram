import RebuildBound.Spec.NativeRouting
import RebuildBound.Spec.Model.Hierarchy

/-! The native family fields are an encoding of the existing canonical
hierarchy coordinates. No allocator or forwarding execution is added here.
The lifetime check reserves direct initialization even for an empty start. -/
namespace RebuildBound.Spec.NativeRouting
open Model Model.Hierarchy

/-- Synthetic access positions reserved by DirectInitializationSeed. -/
def initialPositions (cfg : Config) : Nat :=
  cfg.topDigit * cfg.carryPositions cfg.levels

/-- RequireLifetimeFits checks this next speculative ordinal at every level. -/
def nextOrdinal (cfg : Config) (level : Nat) : Nat :=
  (initialPositions cfg + cfg.horizon) / cfg.carryPositions level + 1

/-- Ordinary FamilyId accepts positive, bounded terminal coordinates.
The empty top's ordinal zero is deliberately handled separately. -/
def FamilyFits (family : Nat × Nat) : Prop :=
  1 ≤ family.1 ∧ family.1 < 2^15 ∧ 0 < family.2 ∧ family.2 < 2^48

/-- The complete message at a canonical family, using the existing encoder. -/
def familyMessage (d : Bool) (family : Nat × Nat) (h : FamilyFits family)
    (lo hi : Word) : Block × Block :=
  message d ⟨family.2, h.2.2.2⟩ ⟨family.1, h.2.1⟩ lo hi

end RebuildBound.Spec.NativeRouting

namespace RebuildBound.Spec
open Model Model.Hierarchy NativeRouting

/-- The native constructor's conservative check covers every model ordinal,
including initialization and one speculative job, for either start. Full
window bounds are separate from the 48-bit ordinal bound. -/
def NativeRoutingLifetime_statement : Prop :=
  ∀ (cfg : Config) (level : Nat), 0 < cfg.carryPositions level →
    cfg.seed level + cfg.ordinals level ≤ nextOrdinal cfg level ∧
    (cfg.initialized = true →
      cfg.seed level + cfg.ordinals level = nextOrdinal cfg level) ∧
    ∀ ordinal, ordinal ≤ cfg.seed level + cfg.ordinals level →
      (nextOrdinal cfg level < 2^48 → ordinal < 2^48) ∧
      (nextOrdinal cfg level * cfg.carryPositions level < 2^64 →
        ordinal * cfg.carryPositions level < 2^64)

/-- Constructor bounds supply the actual canonical family's field bounds.
Forwarding may identify jobs at different levels; it never increases ordinals. -/
def NativeRoutingFamilyBounds_statement : Prop :=
  ∀ (cfg : Config), cfg.levels < 2^15 →
    ∀ level ordinal, 1 ≤ level → level ≤ cfg.levels → 0 < ordinal →
      ordinal ≤ cfg.seed level + cfg.ordinals level →
      0 < cfg.carryPositions level → nextOrdinal cfg level < 2^48 →
      let family := familyOf cfg level ordinal
      FamilyFits family ∧ level ≤ family.1 ∧ family.1 ≤ cfg.levels ∧
        family.2 ≤ ordinal

/-- Complete routing messages identify canonical families, domains and stored
keys exactly. This is injectivity of messages, not of CBC outputs. -/
def NativeRoutingFamilyEncoding_statement : Prop :=
  ∀ (a b : Nat × Nat) (ha : FamilyFits a) (hb : FamilyFits b)
    (d e : Bool) (lo hi lo' hi' : Word),
    familyMessage d a ha lo hi = familyMessage e b hb lo' hi' ↔
      d = e ∧ a = b ∧ lo = lo' ∧ hi = hi'

end RebuildBound.Spec
