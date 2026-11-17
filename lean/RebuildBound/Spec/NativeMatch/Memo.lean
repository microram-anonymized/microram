import RebuildBound.Spec.NativeMatch.Production
import RebuildBound.Spec.NativeRouting.Actual

/-! The actual finite routing program determines the reference comparison
inventory and its capacity/ring charge guard. The memo retains logical routing
coordinates; this projection assumes neither a routing law nor execution
agreement. Cryptographic, normalization, other stop and compiled-execution
obligations remain separate. -/
namespace RebuildBound.Spec.NativeMatchMemo
open Model Model.Hierarchy Model.Online NativeMatchProduction NativeMatchPhysical NativeMatchHierarchy
open NativeRoutingActual

noncomputable def decoded {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (result : Acc ctx.transcriptWidth × Memo) : List NativeMatchTrace.Event := by
  classical
  let run := suppliedRun ctx.client result.1
  let words := IdealHierarchy.words (memoTape result.2)
  exact if Fails ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit run) words ∨
      ready ctx.unit run ctx.snapshots ctx.accesses = false then []
    else referenceEvents ctx.geo.cfg ctx.geo.shapes ctx.unit run ctx.schedule words ctx.accesses

def decodedCapacity {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (result : Acc ctx.transcriptWidth × Memo) : Prop :=
  Fails ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (suppliedRun ctx.client result.1))
    (IdealHierarchy.words (memoTape result.2))

end RebuildBound.Spec.NativeMatchMemo

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online NativeMatchHierarchy NativeMatchProduction NativeRoutingActual

def NativeMatchMemoReference_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.LowerCompatible → ∀ (g : OnlineGeom) (schedule : Schedule)
    (m : Nat) (client : Adaptive.AdaptiveRun m),
    g.unitEntries*g.unitsPerPrefix = geo.cfg.carryPositions 1 → 0 < g.unitEntries →
    (client.init.map Rec.key).Nodup → ∀ tape : IdealKey.Tape,
    let run := Adaptive.realized geo.cfg geo.shapes g schedule client (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)
    referenceEvents geo.cfg geo.shapes g run schedule (IdealHierarchy.words tape) (Adaptive.slotCount client.shape) =
      referenceEvents geo.cfg geo.shapes g run schedule
        (IdealHierarchy.words (memoTape (ReadTree.evaluate tape (readProgram geo.cfg geo.shapes g schedule client)).2))
        (Adaptive.slotCount client.shape)

def NativeMatchMemoFailure_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.LowerCompatible → ∀ (g : OnlineGeom) (schedule : Schedule)
    (m : Nat) (client : Adaptive.AdaptiveRun m),
    g.unitEntries*g.unitsPerPrefix = geo.cfg.carryPositions 1 → 0 < g.unitEntries →
    (client.init.map Rec.key).Nodup → ∀ tape : IdealKey.Tape,
    let run := Adaptive.realized geo.cfg geo.shapes g schedule client (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)
    Fails geo.cfg geo.shapes (OnlineBatch.traceOf g run) (IdealHierarchy.words tape) ↔
      Fails geo.cfg geo.shapes (OnlineBatch.traceOf g run)
        (IdealHierarchy.words (memoTape (ReadTree.evaluate tape (readProgram geo.cfg geo.shapes g schedule client)).2))

/-- The same finite causal result supplies both the guarded inventory and the
unconditional capacity event; ring readiness depends only on its actual run. -/
def NativeMatchMemoDecoded_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool), member ∈ ConfigurationFamily.members →
    ∀ h (ctx : Context member initialized h), ctx.Valid → ∀ tape : IdealKey.Tape,
    let result := ReadTree.evaluate tape (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)
    NativeMatchMemo.decoded ctx result = ctx.inventory tape ∧
      (NativeMatchMemo.decodedCapacity ctx result ↔ ctx.capacityBad tape)
end RebuildBound.Spec
