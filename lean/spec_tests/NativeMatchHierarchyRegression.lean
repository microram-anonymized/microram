import RebuildBound.Proofs.NativeMatchHierarchy

set_option maxRecDepth 10000
set_option maxHeartbeats 16000000
namespace RebuildBound.NativeMatchHierarchyRegression
open Model Model.DirectJob Model.Hierarchy Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchHierarchy

def key (n : Nat) : LogicalKey := [(⟨n%256,Nat.mod_lt _ (by decide)⟩ : Fin 256)] ++ List.replicate 15 0
def record (n value : Nat) : Rec := ⟨key n,value,false⟩
def cfg : Config := ⟨[4],1,1,32,128,false⟩
def direct (d : Nat) : Geometry := ⟨0,d,d,64,64,64,64,64,64,.direct⟩
def top : TopGeom := ⟨64,2,0,0,2,false,1,1,1,1⟩
def prep : TPGeom := ⟨64,2,1,1,1,0,2,false⟩
def sh : Shapes := ⟨direct,fun _ _ => ⟨64,0,0,1,0,0,1,1,1,1⟩,top,prep,prep⟩
def words : Words := fun _ _ _ => 0
def stored (k : LogicalKey) : Stored := ⟨k.toNat % 2^128,Nat.mod_lt _ (by decide)⟩
def trace (current future : Nat) : Trace := ⟨fun i =>
  if i=0 then [[some (record 1 10)]] else if i=1 then [[some (record 2 current)]]
  else [[some (record 3 future)]],[],fun _ => false⟩
def values (tr : Trace) : Option (List Nat) :=
  (nativeTable stored cfg sh tr words 1 2).map (fun out => (out.main.flatMap Bucket.recs ++ Bucket.recs out.tier).map Rec.val)

theorem atTwo (tr : Trace) : nativeTable stored cfg sh tr words 1 2 =
    (nativeStep stored cfg sh tr words 1 1 emptyOutput emptyOutput).bind
      (fun prev => nativeStep stored cfg sh tr words 1 2 prev emptyOutput) := by
  rw [nativeTable,ite_eq_right (by decide)]
  simp only [Nat.reduceSub,ite_true,Option.bind_some]
  rw [nativeTable,ite_eq_right (by decide)]
  simp only [Nat.reduceSub,ite_true,Option.bind_some]
  rw [nativeTable,ite_eq_left (by decide)]
  simp [base,cfg,Config.levels,emptyOutput,Option.bind_eq_bind']

/-- The later digit consumes its actual prior native output and current unit. -/
example : values (trace 20 30) = some [10,20] := by
  simp only [values,atTwo]
  decide +kernel
example : values (trace 99 30) = some [10,99] := by
  simp only [values,atTwo]
  decide +kernel

/-- Future requester units cannot influence this finite dependency prefix. -/
example : values (trace 20 30) = values (trace 20 777) := by
  simp only [values,atTwo]
  decide +kernel

/-- Allocated defaults introduce no empty-key comparison into the current
prefix; only the actual supplied 16-byte records are emitted as subjects. -/
example : (NativeMatchPrefixProducer.events [[some (record 1 10)],[some (record 2 20)]]).all
    (fun e => e.subject.length == 16 && e.partners.all (fun k => k.length == 16)) = true := by
  decide +kernel

end RebuildBound.NativeMatchHierarchyRegression
