import RebuildBound.Proofs.NativeRouting.Families
import RebuildBound.Proofs.HierarchyLevelOne.Coords

/-! Constructor guards and canonical-family encoding. These are arithmetic
and representation checks, not native execution or cryptographic refinement. -/
namespace RebuildBound.NativeRoutingFamilyTests
open Model Model.Hierarchy Spec Spec.NativeRouting

def mixed (initialized : Bool) : Config :=
  ⟨[2, 4, 8], 2, 3, 32, 0, initialized⟩

/-- Heterogeneous forwarding identifies the producer, every intermediate
carry and its terminal consumer. It does not allocate a fresh family per job. -/
example : familyOf (mixed false) 1 64 = (4, 1) := by decide
example : familyOf (mixed false) 2 32 = (4, 1) := by decide
example : familyOf (mixed false) 3 8 = (4, 1) := by decide
example : familyOf (mixed false) 4 1 = (4, 1) := by decide
example : familyOf (mixed false) 2 1 = (2, 1) := by decide

/-- The constructor reserves initialized positions for an empty start too. -/
example : initialPositions (mixed false) = 12288 := by decide
example : nextOrdinal (mixed false) 1 = 193 := by decide
example : (mixed false).seed 1 + (mixed false).ordinals 1 = 1 := by decide
example : (mixed true).seed 1 + (mixed true).ordinals 1 = 193 := by decide

/-- The guard supplies field bounds for every modeled ordinal, without
assuming a bound on the already-forwarded coordinate. -/
example : FamilyFits (familyOf (mixed true) 1 64) :=
  (NativeRoutingFamilyBounds (mixed true) (by decide) 1 64 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).1

def emptyRun : Config := { mixed false with horizon := 64 * 64 }
example : FamilyFits (familyOf emptyRun 1 64) :=
  (NativeRoutingFamilyBounds emptyRun (by decide) 1 64 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).1

/-- Boundaries include the speculative ordinal: accepting one more access
at this boundary would overflow the 48-bit family field. -/
def boundary (horizon : Nat) : Config := ⟨[], 1, 1, 1, horizon, false⟩
example : nextOrdinal (boundary (2^48 - 3)) 1 = 2^48 - 1 := by decide
example : nextOrdinal (boundary (2^48 - 2)) 1 = 2^48 := by decide
example : ¬ nextOrdinal (boundary (2^48 - 2)) 1 < 2^48 := by decide

/-- Fitting family ordinals do not imply fitting complete windows. -/
def windowOverflow : Config := ⟨[], 2^32, 1, 1, 2^64 - 2^32 - 1, false⟩
example : nextOrdinal windowOverflow 1 < 2^48 := by decide
example : nextOrdinal windowOverflow 1 * windowOverflow.carryPositions 1 = 2^64 := by
  decide

/-- The symbolic initialized identity discharges the seeded-offset relation;
the zero-span premise cannot be dropped. -/
example (cfg : Config) (level : Nat) (hs : 0 < cfg.carryPositions level)
    (hi : cfg.initialized = true) :
    cfg.seed level + cfg.ordinals level = nextOrdinal cfg level :=
  (NativeRoutingLifetime cfg level hs).2.1 hi
example : let cfg : Config := ⟨[], 0, 3, 32, 0, true⟩
    ¬ cfg.seed 1 + cfg.ordinals 1 ≤ nextOrdinal cfg 1 := by decide

/-- Family encoding composes directly with the actual mask/shift theorem. -/
example (family : Nat × Nat) (h : FamilyFits family) (d : Bool) (lo hi : Word) :
    (rawPacked (nonceLow d ⟨family.1, h.2.1⟩)
      (BitVec.ofNat 64 family.2)).toNat =
      (familyMessage d family h lo hi).1.1.val :=
  NativeRoutingPacking.1 d ⟨family.2, h.2.2.2⟩ ⟨family.1, h.2.1⟩

/-- Different ordinals at the same source level cannot reuse a message,
even when both forward through several levels. -/
example (cfg : Config) (level v w : Nat)
    (hv : FamilyFits (familyOf cfg level v)) (hw : FamilyFits (familyOf cfg level w))
    (d : Bool) (lo hi : Word)
    (h : familyMessage d (familyOf cfg level v) hv lo hi =
      familyMessage d (familyOf cfg level w) hw lo hi) : v = w := by
  have heq := (NativeRoutingFamilyEncoding _ _ hv hw d d lo hi lo hi).1 h
  exact HierarchyLevelOneProof.familyOfAux_injective cfg cfg.levels level v w heq.2.1

/-- Producer/consumer sharing is required, even with arbitrary stored keys. -/
example (cfg : Config) (level ordinal : Nat) (hl : 2 ≤ level)
    (ht : level ≤ cfg.levels) (hb : 0 < cfg.fanout (level - 1))
    (ha : FamilyFits (familyOf cfg (level - 1) (ordinal * cfg.fanout (level - 1))))
    (hc : FamilyFits (familyOf cfg level ordinal)) (d : Bool) (lo hi : Word) :
    familyMessage d (familyOf cfg (level - 1) (ordinal * cfg.fanout (level - 1))) ha lo hi =
      familyMessage d (familyOf cfg level ordinal) hc lo hi :=
  (NativeRoutingFamilyEncoding _ _ ha hc d d lo hi lo hi).2
    ⟨rfl, NativeRoutingProof.familyOf_carry cfg level ordinal hl ht hb, rfl, rfl⟩

/-- Ordinal zero stays exclusive to the separately constructed empty top. -/
example : ¬ FamilyFits (4, 0) := by simp [FamilyFits]
example (family : Nat × Nat) (h : FamilyFits family) (top : Level)
    (d e : Bool) (lo hi lo' hi' : Word) :
    familyMessage d family h lo hi ≠ message e 0 top lo' hi' := by
  intro heq
  have hcounter := ((NativeRoutingMessage d e _ 0 _ top lo hi lo' hi').1 heq).2.1
  have := congrArg Fin.val hcounter
  have := h.2.2.1
  simp only [Fin.val_zero] at *
  omega

/-- All ordinary identities avoid the dense sentinel, in either domain. -/
example (family : Nat × Nat) (h : FamilyFits family) (d : Bool) (lo hi : Word) :
    (familyMessage d family h lo hi).1.1 ≠ 0 :=
  NativeRoutingProof.packed_ne_zero d _ _ h.1

end RebuildBound.NativeRoutingFamilyTests
