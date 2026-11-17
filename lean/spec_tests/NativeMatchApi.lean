import RebuildBound.Spec.NativeMatch.Api
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace RebuildBound.NativeMatchApiTests
open Model Model.Hierarchy Model.Online Spec NativeMatch NativeMatch.Lanes NativeMatchDispatch NativeMatchApi

private def keyA : LogicalKey := List.replicate 16 1
private def keyB : LogicalKey := List.replicate 16 2
private def codec : Api.Codec where
  pack v b := 2*v + if b then 1 else 0
  payload v := v/2
  flag v := decide (v%2=1)
  payload_pack := by intro v b; cases b <;> simp <;> omega
  flag_pack := by intro v b; cases b <;> simp <;> omega
private def donor : Rec := ⟨keyA,codec.pack 7 false,false⟩
private def target : Rec := ⟨keyB,codec.pack 11 false,false⟩
private def readB : Api.Request := ⟨keyB,.read⟩
private def postB : Rec := ⟨keyB,codec.pack 7 false,false⟩
private def scalar : Policy := fun _ _ _=>.scalar
private def collide : LogicalKey→Stored := fun _=>0
private def noTables : Schedule := fun _=>⟨0,[]⟩
private def state : Requester.State := ⟨[],[some donor,some target]⟩

/-- A stored collision exposes physical lane precedence in the exact fallback. -/
example : storedFirst collide keyB [donor,target]=some donor := by decide +kernel
example : NativeMatchTrace.storedLatest collide keyB [donor,target]=some target := by decide +kernel

/-- The second lane forwards the first native postrecord, rather than restoring
an exact-reference value after a matching error. The requester remains the
same pre-operation input for the complete wave. -/
example : chunk scalar collide codec config31 geometry31.shapes ⟨64,16⟩ noTables []
    (fun _ _ _=>0) (fun _ _=>0) 0 0 state [] [readB,readB] =
      .ok ([postB,postB],[⟨some donor,[]⟩,⟨some postB,[]⟩]) := by decide +kernel

/-- Blind clears use complete stored bytes; all physical equal lanes are cleared. -/
example : storedClear collide state.current [keyB]=[none,none] := by decide +kernel

/-- A native producer failure is propagated before the query proceeds. -/
example : requireTables (fun _=>none) [(1,3),(2,1)] = .error (.tableProducer (1,3)) := by decide +kernel

example : batchCross true 64 [16]=true := by decide +kernel
example : batchCross true 63 [16]=false := by decide +kernel
example : batchCross true 64 [15]=false := by decide +kernel
example : batchCross true 64 [65536]=true := by decide +kernel
example : batchCross true 64 [65537]=false := by decide +kernel
example : workerCross true 64 15 [16]=false := by decide +kernel
example : workerCross true 64 16 [16]=true := by decide +kernel
end RebuildBound.NativeMatchApiTests
