import RebuildBound.Spec.NativeMatch.Jobs

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace RebuildBound.NativeMatchJobsTests
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchJobTrace

def key (n : Nat) : LogicalKey := LogicalKey.ofNat n
def record (n : Nat) : Rec := ⟨key n,n,false⟩
def sparse (n lane : Nat) : Page := (fun _ => record n,(1 : Mask) <<< lane)
def geom : SepGeom := ⟨64,0,0,1,0,0,1,1,1,1⟩
def bMain : List Bucket := [[some ⟨key 1,20,false⟩] ++ List.replicate 63 none]
def groups : List Page := [sparse 2 3,sparse 3 63,sparse 4 17,sparse 1 9]
def initial : FinishGhost :=
  ⟨⟨[[some (record 5)] ++ List.replicate 63 none],[],[pageRecords groups],[[]],[]⟩,[groups]⟩

/-- A four-group direct leaf retains physical holes and runs offers in group
order. The fourth group meets the B copy already installed in main. -/
example : ((finishExact geom (fun _ => 0) bMain initial).state.main.getD 0 []).recs.map Rec.val =
    [5,20,2,3,4] := by decide +kernel

example : ((finishEvents geom (fun _ => 0) bMain initial).filter
    (fun e => e.site == .offerALeaf)).map Event.comparison =
    [(key 2,[key 5,key 1]),(key 3,[key 5,key 1,key 2]),
     (key 4,[key 5,key 1,key 2,key 3]),(key 1,[key 5,key 1,key 2,key 3,key 4])] := by
  decide +kernel

def drainState : SFin := ⟨[],[⟨key 1,20,true⟩],[[record 1,record 4]],[[record 2]],[]⟩

def stored (k : LogicalKey) : Stored :=
  ⟨k.toNat % 2^128,Nat.mod_lt _ (by decide)⟩

/-- Ranked drain clears the older A copy, fills precisely that interior hole
with the shed tombstone, and keeps the original B record and trailing lanes. -/
example : drainNative stored 1 1 drainState =
    [some ⟨key 1,20,true⟩,some (record 4),some (record 2)] ++ List.replicate 61 none := by
  decide +kernel

/-- Final output padding is real storage only: it introduces no subjects in
any comparison inventory. -/
example : (drainEvents 1 1 drainState).map Event.comparison =
    [(key 1,[key 2]),(key 1,[key 1]),(key 4,[key 1])] := by
  decide +kernel

end RebuildBound.NativeMatchJobsTests
