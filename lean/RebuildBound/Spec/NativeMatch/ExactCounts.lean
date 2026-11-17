import RebuildBound.Spec.NativeMatch.LocalApi

/-! Geometry-only accounting for exact normalization comparisons. The bounds
use actual issued lanes, including blind lanes. Record populations are logical:
they retain tombstones and cover unconditional reference overflow continuations.
The ring guard controls the requester suffix; no capacity-success or lifetime
key-universe premise is introduced. -/
namespace RebuildBound.Spec.NativeMatchExactCounts
open Model NativeMatchPhysical ConfigurationFamily

/-- Maximum logical population of an initialized/top table or lower table.
Only public geometry enters this coefficient, never the start, horizon, keys,
or random outcomes. -/
def maxRecords (member : Member) : Nat :=
  max (member.geometry false).keyCapacity
    ((Finset.range ((member.config false).levels - 1)).sup fun i =>
      32 * ((member.config false).fanout (i + 1) * (member.config false).carry (i + 1)))

/-- Three 64-lane allowances cover forwarding, current-unit removal and
supersession. Successful ring filling exposes at most `3*r0` requester units;
each scheduled table is charged its entire logical population once. -/
def perAccess (member : Member) : Nat :=
  192 + 192 * member.r0 +
    (allocatedSlots (member.config false).levels (member.config false).fanout).length *
      maxRecords member

end RebuildBound.Spec.NativeMatchExactCounts

namespace RebuildBound.Spec
open Model Model.Hierarchy NativeMatchProduction NativeMatchPhysical
open NativeMatchLocalApi NativeMatchExactCounts

/-- Every valid reference table coordinate has a geometry-only logical record
bound, including seeded tables and overflow continuations. -/
def NativeMatchExactTableCount_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), member ∈ ConfigurationFamily.members → ctx.Valid →
    ∀ (tape : IdealKey.Tape) level ordinal,
    1 ≤ level → level ≤ ctx.geo.cfg.levels →
    ordinal ≤ ctx.geo.cfg.seed level + ctx.geo.cfg.ordinals level →
    (table ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape))
      (IdealHierarchy.words tape) level ordinal).records.length ≤ maxRecords member

/-- The complete canonical exact-byte inventory is linear in actual accesses.
Internal frame bounds are derived from the existing API constructor, without
adding a user-facing batch bound. Only ring success is needed for this count. -/
def NativeMatchExactPairsLinear_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), member ∈ ConfigurationFamily.members → ctx.Valid →
    ∀ (tape : IdealKey.Tape),
    ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true →
    (exactPairs ctx tape).length ≤ ctx.accesses * perAccess member

end RebuildBound.Spec
