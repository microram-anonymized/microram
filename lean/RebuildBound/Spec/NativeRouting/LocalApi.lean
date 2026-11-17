import RebuildBound.Spec.NativeRouting.LocalNative
import RebuildBound.Spec.NativeRouting.LocalReplay
import RebuildBound.Spec.NativeRouting.LocalLog
import RebuildBound.Spec.NativeRouting.LocalLoggedCoupling
import RebuildBound.Spec.NativeMatch.LocalBound

/-! Local safety for the existing native API. Only scheduled tables of probing
lanes contribute construction diagnostics. Blind updates retain their exact
requester comparisons; no second API execution engine is introduced. -/
namespace RebuildBound.Spec.NativeRoutingLocalApi
open Model Model.Hierarchy Model.Online NativeRoutingActual NativeRoutingLocalDiagnostics
open NativeMatchProduction NativeMatchTrace NativeMatchHierarchy NativeMatchPhysical
open NativeMatchLocalApi NativeNormalizePairs NativeMatch NativeMatch.Lanes

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

/-- Diagnostics of precisely the table reconstructions requested by probing
lanes. Repeated table reconstructions may repeat diagnostics. -/
def diagnostics (ctx : Context member initialized h) (tape : IdealKey.Tape) : List Diagnostic :=
  let run := ctx.run tape
  (List.range ctx.accesses).flatMap fun t =>
    match (OnlineBatch.slots run)[t]? with
    | none => []
    | some slot => if slot.probes then
        (OnlineBatch.slotSchedule (OnlineBatch.widths run) ctx.schedule t).tables.flatMap fun c =>
          (ReadTree.evaluate tape (tableProgram ctx.geo.cfg ctx.geo.shapes
            (OnlineBatch.traceOf ctx.unit run) c.1 c.2)).diagnostics
      else []

/-- Capacity and matching safety is local to invoked jobs and actual API
comparison sites. Ring readiness retains the existing guard. -/
def Safe (ctx : Context member initialized h) (stored : LogicalKey → Stored)
    (tape : IdealKey.Tape) : Prop :=
  ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true ∧
  ¬PairBad stored (exactPairs ctx tape) ∧
  (∀ e ∈ batchPrefixEvents ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape)
      ctx.schedule (IdealHierarchy.words tape) ctx.accesses, ¬e.bad stored) ∧
  ∀ d ∈ diagnostics ctx tape, d.failed = false ∧ ∀ e ∈ d.events, ¬e.bad stored

/-- The finite replay result supplies the entire local guard through its
recorded routing replies. No unknown future diagnostic is queried. -/
def decodedSafe (ctx : Context member initialized h) (stored : LogicalKey → Stored)
    (result : Acc ctx.transcriptWidth × Memo) : Prop :=
  Safe ctx stored (memoTape result.2)

end RebuildBound.Spec.NativeRoutingLocalApi

namespace RebuildBound.Spec
open Model NativeMatchProduction NativeMatchApi NativeRoutingLocalApi NativeNormalize

/-- Safe returned local diagnostics suffice for selected values, requester
updates, adaptive decisions and the complete existing API result. This theorem
applies to every coherent routing tape, including complete-message native tapes. -/
def NativeRoutingLocalApiProjection_statement : Prop :=
  ∀ member initialized h (ctx : Context member initialized h),
    member ∈ ConfigurationFamily.members → ctx.Valid → ∀ policy stored tape,
    Safe ctx stored tape → production ctx policy stored tape = .ok (reference ctx tape)

/-- The one canonical error event already covers the local API guard.
This is event containment on the unconditional canonical product experiment. -/
def NativeRoutingLocalApiGuard_statement : Prop :=
  ∀ member initialized h (ctx : Context member initialized h),
    member ∈ ConfigurationFamily.members → ctx.Valid → ∀ tape stored,
    ¬NativeMatchLocalBound.bad ctx (tape, stored) → Safe ctx stored tape

/-- The sparse reader's exact read log determines the complete local API
guard on every coherent tape, including native complete-message tapes. -/
def NativeRoutingLocalApiMemoSafe_statement : Prop :=
  NativeRoutingLocalLogEvaluate_statement → NativeRoutingLocalLogMemo_statement →
  NativeRoutingLocalLogCongruence_statement → NativeRoutingLocalLoggedTableReads_statement →
  ∀ member initialized h (ctx : Context member initialized h),
    member ∈ ConfigurationFamily.members → ctx.Valid → ∀ stored tape,
    Safe ctx stored (NativeRoutingActual.memoTape (NativeRoutingActual.ReadTree.reads tape
      (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))) ↔
      Safe ctx stored tape

end RebuildBound.Spec
