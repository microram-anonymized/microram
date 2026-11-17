import RebuildBound.Proofs.KeyRelabel.Core
import RebuildBound.Spec.Model.OnlineBatch

namespace RebuildBound.KeyRelabel
open Model

def requesterOp (e : LogicalKey ≃ LogicalKey) : Requester.Op → Requester.Op
  | .access r real => .access (rec e r) real
  | .batch rs => .batch (rs.map (rec e))

def requesterState (e : LogicalKey ≃ LogicalKey) (st : Requester.State) : Requester.State :=
  ⟨st.frozen.map (bucket e), bucket e st.current⟩

@[simp] theorem key_eq (e : LogicalKey ≃ LogicalKey) (a b : LogicalKey) : (e a == e b) = (a == b) := by
  exact key_beq e a b

@[simp] theorem requester_clearKey (e : LogicalKey ≃ LogicalKey) (k : LogicalKey) (u : Bucket) :
    Requester.clearKey (e k) (bucket e u) = bucket e (Requester.clearKey k u) := by
  simp only [Requester.clearKey, bucket, List.map_map]
  apply List.map_congr_left
  intro a ha
  cases a with
  | none => rfl
  | some r =>
    simp only [Function.comp_apply, Option.map_some, Option.filter, rec_key]
    by_cases h : r.key = k <;> simp [h, e.injective.eq_iff]


@[simp] theorem requester_insert (e : LogicalKey ≃ LogicalKey) (n : Nat) (st : Requester.State)
    (a : Option Rec) :
    Requester.insert n (requesterState e st) (a.map (rec e)) =
      requesterState e (Requester.insert n st a) := by
  simp [Requester.insert, requesterState, bucket]
  split <;> simp [bucket]

@[simp] theorem requester_superseded (e : LogicalKey ≃ LogicalKey) (rs : List Rec) (i : Nat) (r : Rec) :
    Requester.superseded (rs.map (rec e)) i (rec e r) = Requester.superseded rs i r := by
  simp [Requester.superseded, ← List.map_drop, List.any_map, Function.comp_def, rec]

private theorem clear_fold (e : LogicalKey ≃ LogicalKey) (rs : List Rec) (u : Bucket) :
    (rs.map (rec e)).foldl (fun u r => Requester.clearKey r.key u) (bucket e u) =
      bucket e (rs.foldl (fun u r => Requester.clearKey r.key u) u) := by
  induction rs generalizing u with
  | nil => rfl
  | cons r rs ih => simpa [rec] using ih (Requester.clearKey r.key u)

private theorem insert_fold (e : LogicalKey ≃ LogicalKey) (n : Nat) (rs : List Rec)
    (ris : List (Rec × Nat)) (st : Requester.State) :
    (ris.map (fun ri => (rec e ri.1, ri.2))).foldl
      (fun s ri => Requester.insert n s
        (if Requester.superseded (rs.map (rec e)) ri.2 ri.1 then none else some ri.1))
      (requesterState e st) =
    requesterState e (ris.foldl
      (fun s ri => Requester.insert n s
        (if Requester.superseded rs ri.2 ri.1 then none else some ri.1)) st) := by
  induction ris generalizing st with
  | nil => rfl
  | cons ri ris ih =>
    simp only [List.map_cons, List.foldl_cons, requester_superseded]
    rw [show (if Requester.superseded rs ri.2 ri.1 then none else some (rec e ri.1)) =
      (if Requester.superseded rs ri.2 ri.1 then none else some ri.1).map (rec e) by
        split <;> rfl, requester_insert]
    exact ih _

@[simp] theorem requester_step (e : LogicalKey ≃ LogicalKey) (n : Nat) (st : Requester.State)
    (o : Requester.Op) :
    Requester.step n (requesterState e st) (requesterOp e o) =
      requesterState e (Requester.step n st o) := by
  cases o with
  | access r real =>
    simp only [requesterOp, Requester.step, rec_key, requesterState]
    rw [requester_clearKey]
    change Requester.insert n (requesterState e ⟨st.frozen, Requester.clearKey r.key st.current⟩)
      (if real then some (rec e r) else none) = _
    rw [show (if real then some (rec e r) else none) =
      (if real then some r else none).map (rec e) by split <;> rfl]
    exact requester_insert e _ _ _
  | batch rs =>
    simp only [requesterOp, Requester.step]
    rw [show (rs.map (rec e)).zipIdx = rs.zipIdx.map (fun ri => (rec e ri.1, ri.2)) by
      simp [List.zipIdx_map]]
    simp only [requesterState]
    rw [clear_fold]
    exact insert_fold e n rs rs.zipIdx
      ⟨st.frozen, rs.foldl (fun u r => Requester.clearKey r.key u) st.current⟩

@[simp] theorem requester_run (e : LogicalKey ≃ LogicalKey) (n : Nat) (st : Requester.State)
    (ops : List Requester.Op) :
    Requester.run n (requesterState e st) (ops.map (requesterOp e)) =
      requesterState e (Requester.run n st ops) := by
  induction ops generalizing st with
  | nil => rfl
  | cons o ops ih =>
    simp only [Requester.run, List.map_cons, List.foldl_cons] at *
    rw [requester_step]
    exact ih _

end RebuildBound.KeyRelabel
