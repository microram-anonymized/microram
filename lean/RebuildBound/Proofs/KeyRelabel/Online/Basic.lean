import RebuildBound.Proofs.KeyRelabel.Online.Requester
import RebuildBound.Proofs.KeyRelabel.Hierarchy.Base

namespace RebuildBound.KeyRelabel
open Model Model.Hierarchy

def onlineOp (e : LogicalKey ≃ LogicalKey) : Online.Op → Online.Op
  | .probe r => .probe (rec e r)
  | .blind r => .blind (rec e r)

def onlineRun (e : LogicalKey ≃ LogicalKey) (run : Online.OnlineRun) : Online.OnlineRun :=
  ⟨run.ops.map (onlineOp e), run.init.map (rec e), unsh e run.unsh⟩

def batchOp (e : LogicalKey ≃ LogicalKey) : OnlineBatch.Op → OnlineBatch.Op
  | .probe r => .probe (rec e r)
  | .blind r => .blind (rec e r)
  | .batch rs => .batch (rs.map (rec e))

def batchRun (e : LogicalKey ≃ LogicalKey) (run : OnlineBatch.BatchRun) : OnlineBatch.BatchRun :=
  ⟨run.ops.map (batchOp e), run.init.map (rec e), unsh e run.unsh⟩

def slot (e : LogicalKey ≃ LogicalKey) (s : OnlineBatch.Slot) : OnlineBatch.Slot :=
  ⟨s.op, s.lane, rec e s.record, s.probes⟩

@[simp] theorem slot_op (e : LogicalKey ≃ LogicalKey) (s : OnlineBatch.Slot) : (slot e s).op = s.op := rfl
@[simp] theorem slot_lane (e : LogicalKey ≃ LogicalKey) (s : OnlineBatch.Slot) : (slot e s).lane = s.lane := rfl
@[simp] theorem slot_record (e : LogicalKey ≃ LogicalKey) (s : OnlineBatch.Slot) : (slot e s).record = rec e s.record := rfl
@[simp] theorem slot_probes (e : LogicalKey ≃ LogicalKey) (s : OnlineBatch.Slot) : (slot e s).probes = s.probes := rfl

@[simp] theorem onlineRun_ops (e : LogicalKey ≃ LogicalKey) (r : Online.OnlineRun) :
    (onlineRun e r).ops = r.ops.map (onlineOp e) := rfl
@[simp] theorem batchRun_ops (e : LogicalKey ≃ LogicalKey) (r : OnlineBatch.BatchRun) :
    (batchRun e r).ops = r.ops.map (batchOp e) := rfl

@[simp] theorem onlineOp_record (e : LogicalKey ≃ LogicalKey) (o : Online.Op) :
    (onlineOp e o).record = rec e o.record := by cases o <;> rfl
@[simp] theorem onlineOp_probes (e : LogicalKey ≃ LogicalKey) (o : Online.Op) :
    (onlineOp e o).probes = o.probes := by cases o <;> rfl
@[simp] theorem onlineRun_length (e : LogicalKey ≃ LogicalKey) (r : Online.OnlineRun) :
    (onlineRun e r).ops.length = r.ops.length := List.length_map _
@[simp] theorem batchRun_length (e : LogicalKey ≃ LogicalKey) (r : OnlineBatch.BatchRun) :
    (batchRun e r).ops.length = r.ops.length := List.length_map _
@[simp] theorem batchOp_lanes (e : LogicalKey ≃ LogicalKey) (o : OnlineBatch.Op) :
    (batchOp e o).lanes = o.lanes.map (fun rb => (rec e rb.1, rb.2)) := by
  cases o <;> simp [batchOp, OnlineBatch.Op.lanes, List.map_map]
@[simp] theorem batchOp_requester (e : LogicalKey ≃ LogicalKey) (o : OnlineBatch.Op) :
    (batchOp e o).requester = requesterOp e o.requester := by cases o <;> rfl

@[simp] theorem online_stateAt (e : LogicalKey ≃ LogicalKey) (g : Online.OnlineGeom)
    (run : Online.OnlineRun) (j : Nat) :
    Online.stateAt g (onlineRun e run) j = requesterState e (Online.stateAt g run j) := by
  unfold Online.stateAt
  simp only [onlineRun, ← List.map_take, List.map_map, Function.comp_def, onlineOp_record]
  rw [show (fun o : Online.Op => Requester.Op.access (rec e o.record) true) =
    requesterOp e ∘ (fun o => Requester.Op.access o.record true) by rfl]
  rw [← List.map_map]
  exact requester_run e g.unitEntries ⟨[], []⟩ _

@[simp] theorem batch_stateAt (e : LogicalKey ≃ LogicalKey) (g : Online.OnlineGeom)
    (run : OnlineBatch.BatchRun) (j : Nat) :
    OnlineBatch.stateAt g (batchRun e run) j =
      requesterState e (OnlineBatch.stateAt g run j) := by
  unfold OnlineBatch.stateAt
  simp only [batchRun, ← List.map_take, List.map_map, Function.comp_def, batchOp_requester]
  simpa only [List.map_map, Function.comp_def, requesterState, bucket, List.map_nil] using
    requester_run e g.unitEntries ⟨[], []⟩ ((run.ops.take j).map OnlineBatch.Op.requester)

@[simp] theorem batch_slots (e : LogicalKey ≃ LogicalKey) (run : OnlineBatch.BatchRun) :
    OnlineBatch.slots (batchRun e run) = (OnlineBatch.slots run).map (slot e) := by
  simp [OnlineBatch.slots, batchRun, List.zipIdx_map, List.flatMap_map,
    List.map_flatMap, batchOp_lanes, List.map_map, slot, Function.comp_def]

@[simp] theorem batch_widths (e : LogicalKey ≃ LogicalKey) (run : OnlineBatch.BatchRun) :
    OnlineBatch.widths (batchRun e run) = OnlineBatch.widths run := by
  simp [OnlineBatch.widths, batchRun, List.map_map, Function.comp_def]

@[simp] theorem online_probePattern (e : LogicalKey ≃ LogicalKey) (run : Online.OnlineRun) (j : Nat) :
    Online.probePattern (onlineRun e run) j = Online.probePattern run j := by
  simp [Online.probePattern, onlineRun, Option.map_map, Function.comp_def]

@[simp] theorem batch_probePattern (e : LogicalKey ≃ LogicalKey) (run : OnlineBatch.BatchRun) (t : Nat) :
    OnlineBatch.probePattern (batchRun e run) t = OnlineBatch.probePattern run t := by
  simp [OnlineBatch.probePattern, Option.map_map, Function.comp_def, slot]

private theorem flatMap_recs (e : LogicalKey ≃ LogicalKey) (us : List Bucket) :
    (us.map (bucket e)).flatMap Bucket.recs = (us.flatMap Bucket.recs).map (rec e) := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [ih, records]

@[simp] theorem output_records (e : LogicalKey ≃ LogicalKey) (o : Output) :
    (output e o).records = o.records.map (rec e) := by
  simp [Output.records, output, buckets, flatMap_recs, records]

@[simp] theorem online_denseRecords (e : LogicalKey ≃ LogicalKey) (cfg : Config) (g : Online.OnlineGeom)
    (run : Online.OnlineRun) (S : Online.Schedule) (j : Nat) :
    Online.denseRecords cfg g (onlineRun e run) S j =
      (Online.denseRecords cfg g run S j).map (rec e) := by
  simp [Online.denseRecords, online_stateAt, requesterState, ← List.map_drop,
    flatMap_recs, List.map_append, records]

@[simp] theorem batch_denseRecords (e : LogicalKey ≃ LogicalKey) (cfg : Config) (g : Online.OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Online.Schedule) (t : Nat) :
    OnlineBatch.denseRecords cfg g (batchRun e run) S t =
      (OnlineBatch.denseRecords cfg g run S t).map (rec e) := by
  simp only [OnlineBatch.denseRecords, batch_slots, List.getElem?_map]
  cases h : (OnlineBatch.slots run)[t]? with
  | none => simp
  | some s =>
    simp [batch_stateAt, requesterState, slot, batch_widths, ← List.map_drop,
      flatMap_recs, List.map_append, records]

@[simp] theorem online_denseKeys (e : LogicalKey ≃ LogicalKey) (cfg : Config) (g : Online.OnlineGeom)
    (run : Online.OnlineRun) (S : Online.Schedule) (j : Nat) :
    Online.denseKeys cfg g (onlineRun e run) S j =
      (Online.denseKeys cfg g run S j).map e := by
  simp [Online.denseKeys, List.map_map, Function.comp_def, rec]

@[simp] theorem batch_denseKeys (e : LogicalKey ≃ LogicalKey) (cfg : Config) (g : Online.OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Online.Schedule) (t : Nat) :
    OnlineBatch.denseKeys cfg g (batchRun e run) S t =
      (OnlineBatch.denseKeys cfg g run S t).map e := by
  simp [OnlineBatch.denseKeys, List.map_map, Function.comp_def, rec]


@[simp] theorem online_traceOf (e : LogicalKey ≃ LogicalKey) (g : Online.OnlineGeom)
    (run : Online.OnlineRun) :
    Online.traceOf g (onlineRun e run) = trace e (Online.traceOf g run) := by
  simp only [Online.traceOf, onlineRun_length, online_stateAt, trace, requesterState]
  simp [onlineRun, buckets, records, ← List.map_drop, ← List.map_take]

@[simp] theorem batch_traceOf (e : LogicalKey ≃ LogicalKey) (g : Online.OnlineGeom)
    (run : OnlineBatch.BatchRun) :
    OnlineBatch.traceOf g (batchRun e run) = trace e (OnlineBatch.traceOf g run) := by
  simp only [OnlineBatch.traceOf, batchRun_length, batch_stateAt, trace, requesterState]
  simp [batchRun, buckets, records, ← List.map_drop, ← List.map_take]


end RebuildBound.KeyRelabel
