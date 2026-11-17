import RebuildBound.Spec.NativeMatch.Api
import RebuildBound.Proofs.ApiCapacity

set_option maxRecDepth 10000
set_option maxHeartbeats 16000000
namespace NativeDeadAliasWitness
open RebuildBound RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.Online
open RebuildBound.Spec RebuildBound.Spec.NativeMatch RebuildBound.Spec.NativeMatch.Lanes

def keyA : LogicalKey := List.replicate 17 0
def keyB : LogicalKey := 1 :: List.replicate 16 0

def tombA : Rec := ⟨keyA,0,true⟩
def tombB : Rec := ⟨keyB,0,true⟩
def cfg : Config := ⟨[2],4,8,32,2,false⟩
def direct (d : Nat) : Model.DirectJob.Geometry := ⟨0,d,d,64,64,64,64,64,64,.direct⟩
def top : TopGeom := ⟨64,2,0,0,2,false,1,1,1,1⟩
def prep : TPGeom := ⟨64,2,1,1,1,0,2,false⟩
def sh : Shapes := ⟨direct,fun _ _ => ⟨64,0,0,1,0,0,1,1,1,1⟩,top,prep,prep⟩
def unit : OnlineGeom := ⟨64,2⟩
def schedule : Schedule := fun _ => ⟨0,[(2,0)]⟩
def words : Words := fun _ _ _ => 0
def dummy : Nat → Nat → Nat := fun _ _ => 1
def stored : LogicalKey → Stored := fun _ => 0

def requests : List Api.Request := [⟨keyA,.read⟩,⟨keyB,.read⟩]
def run : OnlineBatch.BatchRun := ⟨[.probe tombA,.probe tombB],[],fun _=>true⟩
def before : Requester.State := OnlineBatch.stateAt unit run 1

def nativeSecond : Except NativeMatchApi.Stop Probe.Result :=
  NativeMatchApi.query (fun _ _ _ => .scalar) stored cfg sh unit schedule [] (fun _=>true)
    words dummy 1 1 0 before [] keyB

def logicalSecond : Probe.Result := Probe.batch cfg sh unit run schedule words dummy 1

theorem zero_live_capacity : ApiCapacity.LiveCapacity 0 (fun _=>none) [] requests := by
  exact ApiMissCapacity [keyA,keyB]

theorem different_logical_keys : keyA ≠ keyB := by decide

def baseOut : Output := ⟨List.replicate sh.prep.T (Bucket.empty sh.prep.C), []⟩

theorem native_base (tr : Trace) :
    NativeMatchHierarchy.nativeTable stored cfg sh tr words 2 0 = some baseOut := by
  rw [NativeMatchHierarchy.nativeTable]
  simp [base, baseOut, cfg, Config.seed, Config.levels]

theorem exact_base (tr : Trace) : table cfg sh tr words 2 0 = baseOut := by
  rw [table]
  simp [base, baseOut, cfg, Config.seed, Config.levels]

theorem native_result : nativeSecond = .ok ⟨some tombA,[1]⟩ := by
  simp only [nativeSecond, NativeMatchApi.query, schedule, NativeMatchApi.requireTables, native_base]
  decide +kernel

theorem logical_result : logicalSecond = ⟨none,[0]⟩ := by
  simp only [logicalSecond, Probe.batch, run, OnlineBatch.slots, OnlineBatch.Op.lanes,
    List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons, List.flatMap_nil, List.map_cons,
    List.map_nil, List.append_nil, List.cons_append, List.nil_append, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Probe.hierarchy, Probe.cascade, Probe.cascadeWith]
  simp only [OnlineBatch.slotSchedule,OnlineBatch.widths,List.map_cons,List.map_nil,
    OnlineBatch.Op.lanes,List.length_singleton,OnlineBatch.chunkStart,schedule]
  simp only [Probe.cascadeWith,exact_base]
  decide +kernel

theorem both_reply_absent : Probe.decode (some tombA) = Probe.decode logicalSecond.found := by
  rw [logical_result]
  rfl

theorem addresses_differ : (match nativeSecond with
    | .ok result => result.addresses
    | .error _ => []) ≠ logicalSecond.addresses := by
  rw [native_result,logical_result]
  decide

/-- A live-only collision event has no partners, despite this address mismatch. -/
theorem no_live_partners (codec : Api.Codec) :
    (ApiCapacity.supportAt (fun _=>none) [] requests 1).length = 0 := by
  decide +kernel
end NativeDeadAliasWitness
