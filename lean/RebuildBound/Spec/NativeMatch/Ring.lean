import RebuildBound.Spec.NativeMatch.LinearCoded

/-! The finite production ring guard is a public schedule check. It depends on
operation kinds, chunk boundaries and consumed-prefix counts, not logical keys
or oracle answers. This does not prove native scheduler progress or completion. -/
namespace RebuildBound.Spec.NativeMatchPhysical
open Model Model.Online Model.OnlineBatch Model.Adaptive

/-- Public FillDensePrefix preflight. Every chunk uses its starting snapshot
and the number of complete requester units preceding that chunk. Blind lanes
and positions beyond the shape do not probe and require no ring plan. -/
def publicReady {slots : Nat} (g : OnlineGeom) (snapshots : Nat → Snapshot slots)
    (shape : List Kind) (n : Nat) : Bool :=
  (List.range n).all fun t =>
    if shapePattern shape t then
      let start := chunkStart (shapeWidths shape) t
      (fillDenseUnits g.unitsPerPrefix 2 (snapshots start).consumed
        (start / g.unitEntries)).isSome
    else true

end RebuildBound.Spec.NativeMatchPhysical

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.Adaptive NativeMatchPhysical NativeMatchProduction
open scoped ENNReal

/-- Ring readiness of the adaptive reference execution is exactly the public
preflight, for every oracle outcome and every client. -/
def NativeMatchRingPublic_statement : Prop :=
  ∀ {slots : Nat} (cfg : Config) (sh : Shapes) (g : OnlineGeom), 0 < g.unitEntries →
  ∀ (S : Schedule) {m : Nat} (client : AdaptiveRun m)
    (snapshots : Nat → Snapshot slots) (n : Nat) (words : Words) (dummy : Nat → Nat → Nat),
    ready g (realized cfg sh g S client words dummy) snapshots n =
      publicReady g snapshots client.shape n

/-- The canonical ring-stop term is zero or one according to the same public
preflight. No stochastic stop assumption is needed once that check passes. -/
def NativeMatchRingCost_statement : Prop :=
  ∀ {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h),
    NativeMatchCoded.ringCost ctx =
      if publicReady ctx.unit ctx.snapshots ctx.client.shape ctx.accesses then 0 else 1

end RebuildBound.Spec
