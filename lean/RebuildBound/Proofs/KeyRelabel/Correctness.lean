import RebuildBound.Proofs.KeyRelabel.Premises
import RebuildBound.Proofs.KeyRelabel.Probe
import RebuildBound.Spec.KeyRelabel

namespace RebuildBound.KeyRelabel
open Model Model.Hierarchy Spec

@[simp] theorem online_history (e : LogicalKey ≃ LogicalKey) (run : Online.OnlineRun) (j : Nat) :
    (onlineRun e run).init ++ ((onlineRun e run).ops.take j).map Online.Op.record =
      (run.init ++ (run.ops.take j).map Online.Op.record).map (rec e) := by
  simp [onlineRun, ← List.map_take, List.map_map, Function.comp_def]

@[simp] theorem batch_history (e : LogicalKey ≃ LogicalKey) (run : OnlineBatch.BatchRun) (t : Nat) :
    (batchRun e run).init ++ ((OnlineBatch.slots (batchRun e run)).take t).map
        OnlineBatch.Slot.record =
      (run.init ++ ((OnlineBatch.slots run).take t).map OnlineBatch.Slot.record).map (rec e) := by
  simp only [batch_slots, ← List.map_take, List.map_map, Function.comp_def, slot_record]
  simp [batchRun, List.map_append, List.map_map, Function.comp_def]

/-- Correctness transports for arbitrary routing words, including every overflow outcome. -/
theorem onlineCorrectness_transport (geo : HierarchyGeometry) (h : OnlineCorrectnessFor geo) :
    UniverseOnlineCorrectnessFor geo := by
  intro U g run S n m hs w dummy j o hj ho hp
  let e := compression U
  have hsetting := online_setting geo U g run S n m hs
  have hop : (onlineRun e run).ops[j]? = some (onlineOp e o) := by
    simp [onlineRun, ho]
  have hprobe : (onlineOp e o).probes = true := by simpa using hp
  have hresult := h U.card g (onlineRun e run) S n m hsetting
    (words e w) dummy j (onlineOp e o) hj hop hprobe
  change Probe.decode (Probe.scalar geo.cfg geo.shapes g (onlineRun e run) S
      (words e w) dummy j).found = _ ∧ _ at hresult
  rw [online_history] at hresult
  simpa only [probe_scalar_value, onlineOp_record, rec_key, probe_latestValue,
    probe_scalar_addresses, online_touched] using hresult

/-- Batch transport retains the chronological histories of all duplicate lanes. -/
theorem batchCorrectness_transport (geo : HierarchyGeometry) (h : BatchCorrectnessFor geo) :
    UniverseBatchCorrectnessFor geo := by
  intro U g run S n m hs w dummy t s ht hslt hp
  let e := compression U
  have hsetting := batch_setting geo U g run S n m hs
  have hslot : (OnlineBatch.slots (batchRun e run))[t]? = some (slot e s) := by
    simp [hslt]
  have hprobe : (slot e s).probes = true := by simpa using hp
  have hresult := h U.card g (batchRun e run) S n m hsetting
    (words e w) dummy t (slot e s) ht hslot hprobe
  change Probe.decode (Probe.batch geo.cfg geo.shapes g (batchRun e run) S
      (words e w) dummy t).found = _ ∧ _ at hresult
  rw [batch_history] at hresult
  simpa only [probe_batch_value, slot_record, rec_key, probe_latestValue,
    probe_batch_addresses, batch_touched] using hresult

end RebuildBound.KeyRelabel
