import RebuildBound.Proofs.KeyRelabel.Hierarchy
import RebuildBound.Proofs.KeyRelabel.Online.Basic

namespace RebuildBound.KeyRelabel
open Model Model.Hierarchy
@[simp] theorem online_tableKeys (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (g : Online.OnlineGeom) (run : Online.OnlineRun) (w : Words) (l v : Nat) :
    Online.tableKeys cfg sh g (onlineRun e run) (words e w) l v =
      (Online.tableKeys cfg sh g run w l v).map e := by
  simp [Online.tableKeys, table_rename, List.map_map, Function.comp_def, rec]

@[simp] theorem batch_tableKeys (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun) (w : Words) (l v : Nat) :
    OnlineBatch.tableKeys cfg sh g (batchRun e run) (words e w) l v =
      (OnlineBatch.tableKeys cfg sh g run w l v).map e := by
  simp [OnlineBatch.tableKeys, table_rename, List.map_map, Function.comp_def, rec]

@[simp] theorem keys_contains (e : LogicalKey ≃ LogicalKey) (ks : List LogicalKey) (k : LogicalKey) :
    (ks.map e).contains (e k) = ks.contains k := by
  exact key_contains e k ks

@[simp] theorem online_isReal (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (g : Online.OnlineGeom) (run : Online.OnlineRun) (S : Online.Schedule)
    (w : Words) (j i : Nat) :
    Online.isReal cfg sh g (onlineRun e run) S (words e w) j i =
      Online.isReal cfg sh g run S w j i := by
  simp only [Online.isReal, onlineRun_ops, List.getElem?_map]
  cases h : run.ops[j]? <;> simp [onlineOp_record, onlineOp_probes, rec,
    online_denseKeys, online_tableKeys]

@[simp] theorem batch_duplicate (e : LogicalKey ≃ LogicalKey) (run : OnlineBatch.BatchRun)
    (s : OnlineBatch.Slot) :
    OnlineBatch.duplicate (batchRun e run) (slot e s) = OnlineBatch.duplicate run s := by
  unfold OnlineBatch.duplicate
  simp only [batchRun, slot, List.getElem?_map, Option.map_map, Function.comp_def]
  cases h : run.ops[s.op]? with
  | none => simp
  | some o =>
    simp [batchOp_lanes, ← List.map_take, List.any_map, Function.comp_def, rec]

@[simp] theorem batch_isReal (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun) (S : Online.Schedule)
    (w : Words) (t i : Nat) :
    OnlineBatch.isReal cfg sh g (batchRun e run) S (words e w) t i =
      OnlineBatch.isReal cfg sh g run S w t i := by
  simp only [OnlineBatch.isReal, batch_slots, List.getElem?_map]
  cases h : (OnlineBatch.slots run)[t]? <;>
    simp [batch_duplicate, batch_denseKeys, batch_tableKeys, rec]

@[simp] theorem online_touched (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (g : Online.OnlineGeom) (run : Online.OnlineRun) (S : Online.Schedule)
    (w : Words) (dummy : Nat → Nat → Nat) (j i : Nat) :
    Online.touched cfg sh g (onlineRun e run) S (words e w) dummy j i =
      Online.touched cfg sh g run S w dummy j i := by
  simp only [Online.touched, onlineRun_ops, List.getElem?_map]
  cases h : run.ops[j]? <;> cases hc : (S j).tables[i]? <;>
    simp [onlineOp_record, onlineOp_probes, online_isReal, jobWord, words, word, rec]

@[simp] theorem batch_touched (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun) (S : Online.Schedule)
    (w : Words) (dummy : Nat → Nat → Nat) (t i : Nat) :
    OnlineBatch.touched cfg sh g (batchRun e run) S (words e w) dummy t i =
      OnlineBatch.touched cfg sh g run S w dummy t i := by
  simp only [OnlineBatch.touched, batch_slots, List.getElem?_map, batch_widths]
  cases h : (OnlineBatch.slots run)[t]? <;>
    cases hc : (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables[i]? <;>
    simp [batch_isReal, jobWord, words, word, rec]

@[simp] theorem online_view (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (g : Online.OnlineGeom) (run : Online.OnlineRun) (S : Online.Schedule)
    (n m : Nat) (w : Words) (dummy : Nat → Nat → Nat) :
    Online.view cfg sh g (onlineRun e run) S n m (words e w) dummy =
      Online.view cfg sh g run S n m w dummy := by
  funext j i
  exact online_touched e cfg sh g run S w dummy j i

@[simp] theorem batch_view (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun) (S : Online.Schedule)
    (n m : Nat) (w : Words) (dummy : Nat → Nat → Nat) :
    OnlineBatch.view cfg sh g (batchRun e run) S n m (words e w) dummy =
      OnlineBatch.view cfg sh g run S n m w dummy := by
  funext t i
  exact batch_touched e cfg sh g run S w dummy t i

end RebuildBound.KeyRelabel
