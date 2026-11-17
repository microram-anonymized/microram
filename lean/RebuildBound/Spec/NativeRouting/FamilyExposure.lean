import RebuildBound.Spec.NativeRouting.FamilySupport
import Mathlib.Data.Finset.Interval

/-! Production probe support, counted by actual charged lanes. The coefficients
depend only on the fixed geometry. Build support and a sparse execution reader
are separate obligations; these inventories contain only real probing keys. -/
namespace RebuildBound.Spec.NativeRoutingFamilyExposure
open Model Model.Hierarchy Model.Online NativeMatchProduction NativeMatchPhysical

def nonTopWidth (cfg : Config) : Nat :=
  (Finset.Ico 1 cfg.levels).sup (fun level => cfg.fanout level * cfg.carryPositions level)

def probeSpan (member : ConfigurationFamily.Member) (initialized : Bool) : Nat :=
  (allocatedSlots (member.config initialized).levels (member.config initialized).fanout).length *
    nonTopWidth (member.config initialized) + 3 * (64 * member.r0) + 64

noncomputable def probeSlots {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (tape : IdealKey.Tape)
    (family : IdealKey.Family) : Finset Nat := by
  classical
  exact (Finset.range ctx.accesses).filter fun t =>
    ∃ slot, (OnlineBatch.slots (ctx.run tape))[t]? = some slot ∧ slot.probes = true ∧
      ∃ coordinate ∈ (ctx.schedule (OnlineBatch.chunkStart (OnlineBatch.widths (ctx.run tape)) t)).tables,
        familyOf ctx.geo.cfg coordinate.1 coordinate.2 = family

noncomputable def probeKeys {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (tape : IdealKey.Tape)
    (family : IdealKey.Family) : Finset LogicalKey := by
  classical
  exact (probeSlots ctx tape family).image fun t =>
    (((OnlineBatch.slots (ctx.run tape))[t]?).map fun slot => slot.record.key).getD []

noncomputable def probeOrdinals {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (tape : IdealKey.Tape) (level : Nat) : Finset Nat := by
  classical
  exact (((List.range ctx.accesses).flatMap fun t =>
    if OnlineBatch.probePattern (ctx.run tape) t then
      ((ctx.schedule (OnlineBatch.chunkStart (OnlineBatch.widths (ctx.run tape)) t)).tables.map
        fun coordinate => familyOf ctx.geo.cfg coordinate.1 coordinate.2).filterMap
          fun family => if family.1 = level then some family.2 else none
    else []).toFinset)

end RebuildBound.Spec.NativeRoutingFamilyExposure

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online NativeMatchProduction NativeMatchPhysical
open NativeRoutingFamilyExposure

/-- The generic exposure interval instantiated from the existing production
contract. The generated internal frames supply their own 64-lane bound. -/
def NativeRoutingProductionInterval_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), member ∈ ConfigurationFamily.members → ctx.Valid →
    ∀ tape, ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true →
    ∀ family t, t ∈ probeSlots ctx tape family →
      family.2 * ctx.geo.cfg.carryPositions family.1 ≤ pos ctx.geo.cfg t ∧
      pos ctx.geo.cfg t < family.2 * ctx.geo.cfg.carryPositions family.1 + probeSpan member initialized

/-- Deduplicated real probing keys retain historical misses and deleted keys,
but their population is bounded independently of both q and the horizon. -/
def NativeRoutingProbeKeysBound_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), member ∈ ConfigurationFamily.members → ctx.Valid →
    ∀ tape, ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true →
    ∀ family, (probeKeys ctx tape family).card ≤ (probeSlots ctx tape family).card ∧
      (probeSlots ctx tape family).card ≤ probeSpan member initialized

/-- Only terminal families whose endpoints have actually been reached are
probed. The single startup ordinal covers the seeded or empty initial top.
No capacity certificate horizon appears in this count. -/
def NativeRoutingProbeOrdinalsBound_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), member ∈ ConfigurationFamily.members → ctx.Valid →
    ∀ tape level, 1 ≤ level → level ≤ ctx.geo.cfg.levels →
      probeOrdinals ctx tape level ⊆ Finset.Icc (ctx.geo.cfg.seed level)
        (ctx.geo.cfg.seed level + ctx.accesses / ctx.geo.cfg.carryPositions level) ∧
      (probeOrdinals ctx tape level).card ≤ 1 + ctx.accesses / ctx.geo.cfg.carryPositions level

end RebuildBound.Spec
