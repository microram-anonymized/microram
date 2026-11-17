import RebuildBound.Spec.Model.ApiLowering
import RebuildBound.Spec.Model.Requester
import RebuildBound.Spec.Model.DirectPrefix

/-! Regression of the key-model chronology gate using the actual public
lowering. A 64-position unit is the standard L2_r2_D8_2 requester geometry.
These are snapshot/chronology checks, not claims of native capacity overflow. -/

namespace KeyBatchCutsTests
open RebuildBound.Model

def oldA : Rec := ⟨LogicalKey.ofNat (0), 7, false⟩
def deadA : Rec := ⟨LogicalKey.ofNat (0), 0, true⟩
def newB : Rec := ⟨LogicalKey.ofNat (1), 9, false⟩
def lanes : List Rec := [deadA, newB, deadA]

def lower (entries position : Nat) (rs : List Rec) : List Requester.Op :=
  (PublicApi.partition 64 entries position (fun _ => true) rs).map fun group =>
    match group with
    | .blind r => .access r true
    | .chunk rs => .batch rs

def liveCount (history : List Rec) : Nat :=
  ((DirectPrefix.winners history).filter fun r => !r.tomb).length

def start : Requester.State := ⟨[], List.replicate 62 none⟩
def unaligned := Requester.step 64 start (.batch lanes)
def aligned := Requester.run 64 start (lower 64 62 lanes)

example : ∀ t : Fin 4, liveCount ([oldA] ++ lanes.take t.val) ≤ 1 := by decide +kernel
example : unaligned.frozen.flatMap Bucket.recs = [newB] := by decide +kernel
example : liveCount ([oldA] ++ unaligned.frozen.flatMap Bucket.recs) = 2 := by decide +kernel
example : lower 64 62 lanes = [.batch [deadA, newB], .batch [deadA]] := by rfl
example : aligned.frozen.flatMap Bucket.recs = [deadA, newB] := by decide +kernel
example : liveCount ([oldA] ++ aligned.frozen.flatMap Bucket.recs) = 1 := by decide +kernel
example : aligned.current.recs = [deadA] := by decide +kernel
example : DirectPrefix.latest (LogicalKey.ofNat 0)
    ([oldA] ++ aligned.frozen.flatMap Bucket.recs ++ aligned.current.recs) = some deadA := by decide +kernel

-- A later chunk also cannot eagerly clear the preceding unit's newest A.
def newerA : Rec := ⟨LogicalKey.ofNat (0), 11, false⟩
def missC : Rec := ⟨LogicalKey.ofNat (2), 0, true⟩
def missD : Rec := ⟨LogicalKey.ofNat (3), 0, true⟩
def updated : Requester.State := ⟨[], some newerA :: List.replicate 61 none⟩
def repeated := Requester.run 64 updated (lower 64 62 [missC, missD, newerA])

example : repeated.frozen.flatMap Bucket.recs = [newerA, missC, missD] := by decide +kernel
example : DirectPrefix.latest (LogicalKey.ofNat 0) (repeated.frozen.flatMap Bucket.recs) = some newerA := by decide +kernel
example : repeated.current.recs = [newerA] := by decide +kernel

end KeyBatchCutsTests
