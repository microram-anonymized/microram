import RebuildBound.Proofs.KeyRelabel.Online
import RebuildBound.Proofs.KeyRelabel.Online.ProbeBasic

namespace RebuildBound.KeyRelabel
open Model Model.Hierarchy

 theorem probe_hierarchy (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes) (tr : Trace)
    (w : Words) (dummy : Nat → Nat) (k : LogicalKey) (cs : List (Nat × Nat)) (initial : Option Rec) :
    Probe.hierarchy cfg sh (trace e tr) (words e w) dummy (e k) cs
      (initial.map (rec e)) =
      probeResult e (Probe.hierarchy cfg sh tr w dummy k cs initial) := by
  unfold Probe.hierarchy
  simp only [table_rename]
  simpa only [jobWord, words, word, Function.comp_apply, Equiv.symm_apply_apply]
    using probe_cascade e k (fun c => Hierarchy.table cfg sh tr w c.1 c.2)
      (fun c => Online.bucket cfg c.1 c.2 (jobWord cfg w c.1 c.2 k))
      (fun i c => Online.bucket cfg c.1 c.2 (dummy i)) cs initial 0

 theorem probe_scalar (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (run : Online.OnlineRun) (S : Online.Schedule) (w : Words)
    (dummy : Nat → Nat → Nat) (j : Nat) :
    Probe.scalar cfg sh g (onlineRun e run) S (words e w) dummy j =
      probeResult e (Probe.scalar cfg sh g run S w dummy j) := by
  simp only [Probe.scalar, onlineRun_ops, List.getElem?_map]
  cases h : run.ops[j]? with
  | none => rfl
  | some o =>
    simp only [Option.map_some, onlineOp_probes, onlineOp_record, rec_key,
      online_traceOf, online_denseRecords, latest_rename]
    split
    · exact probe_hierarchy e cfg sh (Online.traceOf g run) w (dummy j) o.record.key
        (S j).tables _
    · rfl

@[simp] theorem probe_earlier (e : LogicalKey ≃ LogicalKey) (run : OnlineBatch.BatchRun)
    (s : OnlineBatch.Slot) :
    Probe.earlier (batchRun e run) (slot e s) = (Probe.earlier run s).map (rec e) := by
  unfold Probe.earlier
  simp only [batchRun, slot, List.getElem?_map, Option.map_map, Function.comp_def]
  cases h : run.ops[s.op]? with
  | none => simp
  | some o => simp [batchOp_lanes, ← List.map_take, List.map_map, Function.comp_def]

 theorem probe_batch (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Online.Schedule) (w : Words)
    (dummy : Nat → Nat → Nat) (t : Nat) :
    Probe.batch cfg sh g (batchRun e run) S (words e w) dummy t =
      probeResult e (Probe.batch cfg sh g run S w dummy t) := by
  simp only [Probe.batch, batch_slots, List.getElem?_map]
  cases h : (OnlineBatch.slots run)[t]? with
  | none => rfl
  | some s =>
    simp only [Option.map_some, slot_record, slot_probes, batch_traceOf, batch_widths, batch_denseRecords,
      probe_earlier, rec_key, latest_rename, option_orElse_rec]
    split
    · exact probe_hierarchy e cfg sh (OnlineBatch.traceOf g run) w (dummy t) s.record.key
        (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables _
    · rfl

 theorem probe_scalar_found (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (g : Online.OnlineGeom) (run : Online.OnlineRun) (S : Online.Schedule) (w : Words)
    (dummy : Nat → Nat → Nat) (j : Nat) :
    (Probe.scalar cfg sh g (onlineRun e run) S (words e w) dummy j).found =
      (Probe.scalar cfg sh g run S w dummy j).found.map (rec e) := by
  rw [probe_scalar]; rfl

 theorem probe_scalar_addresses (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (g : Online.OnlineGeom) (run : Online.OnlineRun) (S : Online.Schedule) (w : Words)
    (dummy : Nat → Nat → Nat) (j : Nat) :
    (Probe.scalar cfg sh g (onlineRun e run) S (words e w) dummy j).addresses =
      (Probe.scalar cfg sh g run S w dummy j).addresses := by
  rw [probe_scalar]; rfl

 theorem probe_batch_found (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun) (S : Online.Schedule) (w : Words)
    (dummy : Nat → Nat → Nat) (t : Nat) :
    (Probe.batch cfg sh g (batchRun e run) S (words e w) dummy t).found =
      (Probe.batch cfg sh g run S w dummy t).found.map (rec e) := by
  rw [probe_batch]; rfl

 theorem probe_batch_addresses (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun) (S : Online.Schedule) (w : Words)
    (dummy : Nat → Nat → Nat) (t : Nat) :
    (Probe.batch cfg sh g (batchRun e run) S (words e w) dummy t).addresses =
      (Probe.batch cfg sh g run S w dummy t).addresses := by
  rw [probe_batch]; rfl

 theorem probe_scalar_value (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (g : Online.OnlineGeom) (run : Online.OnlineRun) (S : Online.Schedule) (w : Words)
    (dummy : Nat → Nat → Nat) (j : Nat) :
    Probe.decode (Probe.scalar cfg sh g (onlineRun e run) S (words e w) dummy j).found =
      Probe.decode (Probe.scalar cfg sh g run S w dummy j).found := by
  rw [probe_scalar_found, probe_decode]

 theorem probe_batch_value (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun) (S : Online.Schedule) (w : Words)
    (dummy : Nat → Nat → Nat) (t : Nat) :
    Probe.decode (Probe.batch cfg sh g (batchRun e run) S (words e w) dummy t).found =
      Probe.decode (Probe.batch cfg sh g run S w dummy t).found := by
  rw [probe_batch_found, probe_decode]

end RebuildBound.KeyRelabel
