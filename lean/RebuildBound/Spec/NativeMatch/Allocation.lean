import RebuildBound.Spec.ConfigurationFamilyBudget
import RebuildBound.Spec.ConfigurationFamilyData
import RebuildBound.Spec.IdealCapacity
import RebuildBound.Spec.HierarchyChunkBase

/-! Public production comparison allocations. Values are calculated from
geometry and the existing carry-ordinal exposures. The registered arithmetic
certificate reserves matching error before rounding the capacity allocation;
execution-inventory correspondence is a separate registered proof layer. -/
namespace RebuildBound.Spec.NativeMatchInventory
open Model ConfigurationFamily

/-- Per-site S_min allocations computed from public geometry and record bounds.
These definitions alone do not establish execution-inventory correspondence. -/
structure SiteCharge where
  prefixDedup : Nat := 0
  fixedDedup : Nat := 0
  offerALeaf : Nat := 0
  offerBTier : Nat := 0
  resolveALeaf : Nat := 0
  resolveBTier : Nat := 0
  poolDedup : Nat := 0
  leftoverDedup : Nat := 0
  deriving Repr

def SiteCharge.total (s : SiteCharge) : Nat :=
  s.prefixDedup + s.fixedDedup + s.offerALeaf + s.offerBTier +
    s.resolveALeaf + s.resolveBTier + s.poolDedup + s.leftoverDedup

def ordinary (m : Member) (level digit : Nat) : SiteCharge :=
  let cfg := m.config true
  let prefixCharge := if level = 1 then 64 * (m.r0 * (m.r0 - 1) / 2) else 0
  if digit < 2 then { prefixDedup := prefixCharge } else
    let U := cfg.carry level
    let e := val2 digit
    let r := digit / 2 ^ e
    let output := digit * U
    let recA := 32 * (digit - 1) * U
    let recB := 32 * U
    let tB := if level = 1 then 1 else m.tierPages (level - 1)
    let tA := if 2 ≤ level ∧ digit = 2 ∧ 2 < cfg.fanout level then
      m.tierPages (level - 1) else m.tierPages level
    let sb := m.stashPages level
    let msb := if level = 1 then max sb (m.tierPages 1) else sb
    let tier := m.tierPages level
    let aSlots := sb * (U.log2 + e + if 1 < r then 1 else 0) + tA
    let aRes := min recA (64 * aSlots)
    let bTier := min recB (64 * tB)
    let outputRecs := min (recA + recB) (64 * output)
    { prefixDedup := prefixCharge,
      fixedDedup := min recA (64 * output),
      offerALeaf := aRes,
      offerBTier := min (tB * outputRecs) bTier,
      poolDedup := min (tB * aRes) (aSlots * bTier),
      leftoverDedup := tier * min (64 * msb) recB + msb * min (64 * tier) recA }

def top (m : Member) : SiteCharge :=
  let cfg := m.config true
  let U := cfg.carry cfg.levels
  let T := cfg.topDigit * U
  let recA := 32 * T
  let recB := 32 * U
  let tB := m.tierPages (cfg.levels - 1)
  let sb := m.stashPages cfg.levels
  let tier := m.tierPages cfg.levels
  let aMain := min recA (64 * T)
  let retained := min (64 * sb) recA
  let bTier := min recB (64 * tB)
  { fixedDedup := aMain,
    resolveALeaf := retained,
    resolveBTier := min (tB * aMain) bTier,
    poolDedup := min (tB * retained) (sb * bTier),
    leftoverDedup := tier * min (64 * sb) recB + sb * min (64 * tier) recA }

def classCharge (m : Member) : JobClass → Nat
  | .ordinary level digit => (ordinary m level digit).total
  | .topFinish => (top m).total
  | .topPrepare | .initialization => 0

/-- Count by the existing carry-ordinal exposure definitions, not a CSV table.
The zero preparation/initialization allocation requires a path proof. -/
def sMin (m : Member) (initialized : Bool) : Nat :=
  ((m.config initialized).exposures.map fun p => p.2 * classCharge m p.1).sum

def arenaSlots (m : Member) : Nat :=
  (m.fanouts.map fun fanout => 1 + if fanout = 8 then 1 else 0).sum +
    2 * m.fanouts.length + 2

def denseBuckets (m : Member) : Nat := 3 * m.r0 + arenaSlots m

def weight (m : Member) (initialized : Bool) : Nat :=
  64 ^ 4 * sMin m initialized + 2 ^ 32 * denseBuckets m * 14 * 8 ^ 2

def Fits (m : Member) (initialized : Bool) : Prop :=
  exposureBudget m + (weight m initialized : ℚ) / 2 ^ 128 ≤ 1 / 2 ^ 64

instance (m : Member) (initialized : Bool) : Decidable (Fits m initialized) :=
  inferInstanceAs (Decidable (_ ≤ _))

end RebuildBound.Spec.NativeMatchInventory
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online IdealHierarchy IdealDirect MeasureTheory
open scoped ENNReal
def NativeMatchCapacityAllocation_statement : Prop :=
  ∀ (initialized : Bool) (member : ConfigurationFamily.Member),
    member ∈ ConfigurationFamily.members → ∀ h, 1 ≤ h →
    let geo := (member.geometry initialized).chunk h
    ∀ (c : Api.Codec) g S init m width batches,
    let fs := ApiAdaptive.frames width g.unitEntries batches
    ∀ choose : ApiLegal.Chooser geo.cfg (ApiAdaptive.shape fs) S m,
    let n := Adaptive.slotCount (ApiAdaptive.shape fs)
    let compiled := ApiLegal.adapt geo.cfg (ApiAdaptive.shape fs) S choose
    ApiCapacity.InitialStateValid geo.keyCapacity geo.cfg.initialized init →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → n ≤ geo.cfg.horizon → SchedulePremises geo.cfg S n m →
    (∀ t : ApiLegal.Prefix geo.cfg (ApiAdaptive.shape fs) S m n,
      ApiCapacity.LiveCapacity geo.keyCapacity (Api.stateOf c init) (init.map Rec.key)
        ((ApiAdaptive.requestGroups compiled (Adaptive.rowsOf (ApiLegal.erase t) n) fs).flatMap
          PublicApi.Group.lanes)) →
    let a := ApiAdaptive.run c geo.cfg geo.shapes g S init fs compiled
    IdealKey.tapeLaw {tape | Fails geo.cfg geo.shapes
      (trace geo.cfg geo.shapes g S a tape) (words tape)} +
      (h : ℝ≥0∞) * ((NativeMatchInventory.weight member initialized : ℝ≥0∞) / (2 : ℝ≥0∞)^128) ≤
      (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ)^64)


end RebuildBound.Spec

namespace RebuildBound.Spec
open ConfigurationFamily NativeMatchInventory
/-- Reproducible exact arithmetic over the constructors, all 94 geometries and
both starts. No external integer weight table is an input. -/
def NativeMatchFamilyArithmetic_statement : Prop :=
  ∀ member ∈ members, Fits member true ∧ Fits member false
end RebuildBound.Spec

namespace RebuildBound.Spec
open Model ConfigurationFamily NativeMatchInventory
open scoped ENNReal
/-- Combine the shared analytic capacity allocations and the geometry-derived
matching allocation before rounding. -/
def NativeMatchCombinedAllocation_statement : Prop :=
  ∀ (member : Member), member ∈ members → ∀ initialized,
    (member.config initialized).exposureSum (classBudget member initialized) +
      (weight member initialized : ℝ≥0∞) / (2 : ℝ≥0∞)^128 ≤
      ENNReal.ofReal (1 / (2 : ℝ)^64)
end RebuildBound.Spec
