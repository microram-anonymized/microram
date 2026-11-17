import RebuildBound.Spec.ConfigurationGeometry

/-! Compact public parameters for the finite planner family. These
constructors derive all job fields; the native fixture compares the results.
No probability bound or claim about all native planner outputs is asserted. -/

namespace RebuildBound.Spec.ConfigurationFamily
open RebuildBound.Model RebuildBound.Spec

structure Member where
  name : String
  r0 : Nat
  fanouts : List Nat
  tiers : List Nat
  stashes : List Nat

def Member.tierPages (m : Member) (ℓ : Nat) : Nat := m.tiers.getD (ℓ - 1) 0
def Member.stashPages (m : Member) (ℓ : Nat) : Nat := m.stashes.getD (ℓ - 1) 0

def Member.config (m : Member) (initialized : Bool) : Config :=
  { fanouts := m.fanouts, carry1 := 2 * m.r0, topDigit := 8,
    load := 32, horizon := 2 ^ 32, initialized }

def Member.direct (m : Member) (d : Nat) : DirectJob.Geometry :=
  let K := (2 * m.r0).log2
  let tier := 64 * m.tierPages 1
  let stash := 64 * m.stashPages 1
  let base : DirectJob.Geometry :=
    { K, digit := d, outputHomes := d * (2 * m.r0), outputCapacity := tier,
      aTierCapacity := if d = 1 then 0 else tier,
      routeCapacity := stash, radixCapacity := stash, insertionCapacity := stash,
      copyCapacity := tier, ranges := .direct }
  if base.outputHomes ≤ 8 ∨ base.poolCapacity = 0 then base else
    let bits := routedRangeBits (ceilLog2 base.outputHomes) (base.poolCapacity / 64)
    { base with ranges := .dfs (ceilLog2 base.outputHomes - bits) bits base.poolCapacity }

def Member.geometry (m : Member) (initialized : Bool) : HierarchyGeometry :=
  let cfg := m.config initialized
  let k := (cfg.carry cfg.levels).log2
  let e := cfg.topDigit.log2
  let retained := m.stashPages cfg.levels
  let rho := routedRangeBits (k + e) retained
  let top : TopGeom :=
    { C := 64, k, e, rho, I := k + e - rho, dfs := true,
      rPages := retained, bPages := m.tierPages (cfg.levels - 1),
      mergePages := retained, tierPages := m.tierPages cfg.levels }
  let prepK := k + e
  let stash := m.stashPages cfg.levels
  let tier := m.tierPages cfg.levels
  let bits := routedRangeBits prepK ((prepK - 1) * stash + tier)
  let prep : TPGeom :=
    { C := 64, k := prepK, stashPages := stash, aTierPages := tier,
      drainPages := top.rPages, rangeBits := bits, I := prepK - bits, dfs := true }
  let initial := { prep with drainPages := top.tierPages }
  { cfg, rows := separatedRows cfg m.stashPages m.tierPages, top, prep,
    init := initial, keyCapacity := cfg.load * top.T, direct := m.direct }

end RebuildBound.Spec.ConfigurationFamily
