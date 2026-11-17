import RebuildBound.Spec.HierarchyGeometry

/-! Shared arithmetic constructors for separated hierarchy rows. Concrete
configurations and their numerical inventories are defined separately. -/

namespace RebuildBound.Model

/-- Ceiling of binary logarithm, including the empty/singleton case. -/
def ceilLog2 (n : Nat) : Nat := if n ≤ 1 then 0 else (n - 1).log2 + 1

/-- Range bits for a routed one-page DFS: eight ranges per pool page,
capped by the main width, with at most 18 index bits per range. This
constructor is for routed pools; it does not select the native direct plan. -/
def routedRangeBits (mainBits poolPages : Nat) : Nat :=
  max (min mainBits (ceilLog2 (8 * poolPages))) (mainBits - 18)

/-- A separated row from carry geometry and per-level page schedules. At
digit two A is the adopted carry, so its old tier has the preceding level's
width. Later digits use this level's published tier. -/
def separatedGeometry (cfg : Config) (stash tier : Nat → Nat) (ℓ d : Nat) : SepGeom :=
  let K := (cfg.carry ℓ).log2
  let e := val2 d
  let r := d / 2 ^ e
  let a := tier (if d = 2 then ℓ - 1 else ℓ)
  let pool := (K + e + if 1 < r then 1 else 0) * stash ℓ + a
  let mainBits := ceilLog2 (d * cfg.carry ℓ)
  let bits := routedRangeBits mainBits pool
  { C := 64, K, e, r, rangeBits := bits, I := mainBits - bits,
    stashPages := stash ℓ, aTierPages := a, bTierPages := tier (ℓ - 1),
    tierPages := tier ℓ }

/-- Complete separated rows in the configuration's class order, with the
existing exact ordinal counts. No independently maintained exposure list. -/
def separatedRows (cfg : Config) (stash tier : Nat → Nat) : List (SepGeom × Nat) :=
  cfg.separatedClasses.map fun (ℓ, d) =>
    (separatedGeometry cfg stash tier ℓ d, cfg.ordinaryCount ℓ d)

end RebuildBound.Model
