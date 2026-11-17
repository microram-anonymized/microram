import RebuildBound.Spec.NativeMatch.LinearCoded

/-! Public arithmetic certificates for the complete-message routing adapter.
The family certificate covers the dependency cones of speculative coordinates,
not only jobs actually invoked. Counter reservations include dense placeholders
and tiers, even though the declared view lists hashed probes only. -/
namespace RebuildBound.Spec.NativeMatchPublicFit
open Model Model.Hierarchy NativeMatchProduction NativeMatchPhysical

/-- A public bound for every family's ordinal: level-one ordinal time at each
level's last potential coordinate. There are only `levels` arithmetic checks. -/
def FamilyTimeFit {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) : Prop :=
  ∀ level, 1 ≤ level → level ≤ ctx.geo.cfg.levels →
    time ctx.geo.cfg level (ctx.geo.cfg.seed level + ctx.geo.cfg.ordinals level) < 2^48

/-- Four dense-prefix placeholders plus at most a main and a tier entry per
allocated physical slot. This bounds all reservations, including plan holes. -/
def maxStride (member : ConfigurationFamily.Member) (initialized : Bool) : Nat :=
  4 + 2 * (allocatedSlots (member.config initialized).levels
    (member.config initialized).fanout).length

/-- A constant-size public reservation check, independent of publications,
request kinds, chunking and routing replies. It conservatively charges every
access at the maximum physical stride, including blind accesses. -/
def ReservationFit {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) : Prop :=
  ctx.accesses * maxStride member initialized < 2^64

end RebuildBound.Spec.NativeMatchPublicFit

namespace RebuildBound.Spec
open NativeMatchProduction NativeMatchPublicFit NativeMatchRoutingBudget

def NativeMatchPublicFieldsFit_statement : Prop :=
  ∀ member initialized h (ctx : Context member initialized h),
    member ∈ ConfigurationFamily.members → ctx.Valid → FamilyTimeFit ctx → FieldsFit ctx

def NativeMatchPublicCounterFit_statement : Prop :=
  ∀ member initialized h (ctx : Context member initialized h),
    ReservationFit ctx → CounterFit ctx

end RebuildBound.Spec
