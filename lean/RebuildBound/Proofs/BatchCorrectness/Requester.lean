import RebuildBound.Proofs.OnlineCorrectness.Requester
import RebuildBound.Proofs.BatchFresh.Requester

/-! Batch clearing and supersession preserve lookup in the complete stored
history. This statement intentionally does not restrict the supplied history
to any unit or prefix: a superseding lane may cross either boundary. -/

namespace RebuildBound.BatchCorrectnessProof

open Model Model.Online Model.OnlineBatch Model.DirectPrefix
open OnlineCorrectnessProof

private theorem latest_clears (key : LogicalKey) (lanes : List Rec)
    (h : key ∉ lanes.map Rec.key) (cur : Bucket) :
    latest key (lanes.foldl (fun u r => Requester.clearKey r.key u) cur).recs =
      latest key cur.recs := by
  induction lanes generalizing cur with
  | nil => rfl
  | cons r lanes ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [List.foldl_cons, ih h.2, RequesterAux.recs_clearKey,
      latest_filter_key key cur.recs (fun k => k != r.key)]
    simp [h.1]

/-- Inserting batch lanes leaves exactly their stable last-key winners.
This full-record equality is independent of where units freeze. -/
theorem requester_batch_records (E : Nat) (lanes : List Rec) :
    ∀ (remaining before : List Rec) (st : Requester.State), lanes = before ++ remaining →
      requesterRecords ((remaining.zipIdx before.length).foldl
        (fun s ri => Requester.insert E s
          (if Requester.superseded lanes ri.2 ri.1 then none else some ri.1)) st) =
        requesterRecords st ++ winners remaining := by
  intro remaining
  induction remaining with
  | nil => intro before st _; simp [winners]
  | cons r remaining ih =>
    intro before st h
    have hdrop : lanes.drop (before.length + 1) = remaining := by
      rw [h]; simp [List.drop_append]
    have hs : Requester.superseded lanes before.length r =
        remaining.any (·.key == r.key) := by simp [Requester.superseded, hdrop]
    simp only [List.zipIdx_cons, List.foldl_cons]
    have ht := ih (before ++ [r])
      (Requester.insert E st (if Requester.superseded lanes before.length r then none else some r))
      (by simp [h])
    simp only [List.length_append, List.length_singleton] at ht
    rw [ht, requesterRecords_insert, hs]
    by_cases hk : r.key ∈ remaining.map Rec.key
    · have ha : remaining.any (·.key == r.key) = true := by
        obtain ⟨x, hx, he⟩ := List.mem_map.mp hk
        exact List.any_eq_true.mpr ⟨x, hx, by simpa using he⟩
      rw [winners, ite_eq_left hk]
      simp only [ha, ite_true, Option.toList_none, List.append_nil]
    · have ha : remaining.any (·.key == r.key) = false := by
        apply List.any_eq_false.mpr
        intro x hx he
        exact hk (List.mem_map.mpr ⟨x, hx, by simpa using he⟩)
      rw [winners, ite_eq_right hk]
      simp only [ha, Bool.false_eq_true, ite_false, Option.toList_some, List.append_assoc,
        List.singleton_append]

/-- A completed batch has the same newest record as appending every supplied
lane, even though superseded lanes were inserted as empty positions. -/
theorem requester_step_batch (E : Nat) (key : LogicalKey) (st : Requester.State) (lanes : List Rec) :
    latest key (requesterRecords (Requester.step E st (.batch lanes))) =
      latest key (requesterRecords st ++ lanes) := by
  have h := requester_batch_records E lanes lanes []
    ⟨st.frozen, lanes.foldl (fun u r => Requester.clearKey r.key u) st.current⟩ (by simp)
  simp only [List.length_nil] at h
  change latest key (requesterRecords (lanes.zipIdx.foldl _ _)) = _
  rw [h, latest_append, latest_winners, latest_append]
  cases hl : latest key lanes with
  | some r => rfl
  | none =>
    simp only [Option.orElse_none]
    unfold requesterRecords
    rw [latest_append, latest_append, latest_clears key lanes ((latest_none_iff key lanes).mp hl)]

private theorem requester_step (E : Nat) (key : LogicalKey) (st : Requester.State) (op : OnlineBatch.Op) :
    latest key (requesterRecords (Requester.step E st op.requester)) =
      latest key (requesterRecords st ++ op.lanes.map Prod.fst) := by
  cases op with
  | probe r => exact requester_step_access E key st r
  | blind r => exact requester_step_access E key st r
  | batch lanes => simpa [Op.requester, Op.lanes, Function.comp_def] using requester_step_batch E key st lanes

private theorem requester_run (E : Nat) (key : LogicalKey) (st : Requester.State) (ops : List OnlineBatch.Op) :
    latest key (requesterRecords (Requester.run E st (ops.map Op.requester))) =
      latest key (requesterRecords st ++ ops.flatMap (fun o => o.lanes.map Prod.fst)) := by
  induction ops generalizing st with
  | nil => simp [Requester.run]
  | cons o ops ih =>
    simp only [List.map_cons, Requester.run, List.foldl_cons] at ⊢
    rw [← Requester.run, ih, latest_append, requester_step, latest_append]
    simp only [List.flatMap_cons, latest_append]
    cases latest key (ops.flatMap fun o => o.lanes.map Prod.fst) <;> rfl

/-- Completed operations preserve the full supplied lane history. -/
theorem requester_history (g : OnlineGeom) (run : BatchRun) (j : Nat) (key : LogicalKey) :
    latest key ((OnlineBatch.stateAt g run j).frozen.flatMap Bucket.recs ++
      (OnlineBatch.stateAt g run j).current.recs) =
      latest key ((run.ops.take j).flatMap fun o => o.lanes.map Prod.fst) := by
  simpa [OnlineBatch.stateAt, requesterRecords, Bucket.recs] using
    requester_run g.unitEntries key ⟨[], []⟩ (run.ops.take j)

open BatchFreshProof

private theorem opSlots_records (op : OnlineBatch.Op) (j : Nat) :
    (opSlots (op, j)).map Slot.record = op.lanes.map Prod.fst := by
  simpa only [opSlots, List.map_map, Function.comp_def] using
    congrArg (List.map (Prod.fst : Rec × Bool → Rec)) (List.zipIdx_map_fst 0 op.lanes)

private theorem slotsL_records (ops : List OnlineBatch.Op) (j : Nat) :
    (slotsL ops j).map Slot.record = ops.flatMap (fun o => o.lanes.map Prod.fst) := by
  induction ops generalizing j with
  | nil => rfl
  | cons o ops ih => rw [slotsL_cons, List.map_append, opSlots_records, ih, List.flatMap_cons]

/-- Completed operations are exactly the prefix of slots before the next
operation's first lane. -/
theorem slots_prefix_records (run : BatchRun) (j : Nat) :
    ((slots run).take (fs run j)).map Slot.record =
      (run.ops.take j).flatMap (fun o => o.lanes.map Prod.fst) := by
  have hs : slots run = slotsL (run.ops.take j) 0 ++
      slotsL (run.ops.drop j) (run.ops.take j).length := by
    conv_lhs => rw [slots_eq, ← List.take_append_drop j run.ops, slotsL_append]
    simp
  rw [hs, fs_eq, List.take_left, slotsL_records]

/-- Stored history at a chunk boundary agrees with all preceding slots. -/
theorem requester_history_slots (g : OnlineGeom) (run : BatchRun) (j : Nat) (key : LogicalKey) :
    latest key ((OnlineBatch.stateAt g run j).frozen.flatMap Bucket.recs ++
      (OnlineBatch.stateAt g run j).current.recs) =
      latest key (((slots run).take (fs run j)).map Slot.record) := by
  rw [slots_prefix_records, requester_history]

/-- A slot's history splits into preceding operations and earlier lanes of
its own operation. -/
theorem slots_history_split (run : BatchRun) {t : Nat} {s : Slot}
    (hs : (slots run)[t]? = some s) :
    ((slots run).take t).map Slot.record =
      ((slots run).take (fs run s.op)).map Slot.record ++
        ((((run.ops[s.op]?.map Op.lanes).getD []).take s.lane).map Prod.fst) := by
  obtain ⟨o, ho, hl, ht⟩ := slot_inv run hs
  obtain ⟨hj, he⟩ := List.getElem?_eq_some_iff.mp ho
  have hll : s.lane ≤ (opSlots (o, s.op)).length := by
    rw [length_opSlots]
    exact Nat.le_of_lt (List.getElem?_eq_some_iff.mp hl).1
  rw [slots_prefix_records, slots_split run hj, ht, fs_eq,
    List.take_length_add_append, List.take_append_of_le_length (by simpa [he] using hll),
    List.map_append, slotsL_records, List.map_take, opSlots_records]
  simp [ho, he]

/-- The latest matching earlier lane wins; when no earlier lane matches,
forwarding falls back to the chunk-start history. Tombstones remain records. -/
theorem forwarding_history (run : BatchRun) (key : LogicalKey) {t : Nat} {s : Slot}
    (hs : (slots run)[t]? = some s) :
    (latest key ((((run.ops[s.op]?.map Op.lanes).getD []).take s.lane).map Prod.fst)).orElse
      (fun _ => latest key (((slots run).take (fs run s.op)).map Slot.record)) =
      latest key (((slots run).take t).map Slot.record) := by
  rw [slots_history_split run hs, latest_append]

/-- The same forwarding law with initialization included as the oldest
part of the reference history. -/
theorem forwarding_history_init (init : List Rec) (run : BatchRun) (key : LogicalKey)
    {t : Nat} {s : Slot} (hs : (slots run)[t]? = some s) :
    (latest key (Probe.earlier run s)).orElse
      (fun _ => latest key (init ++ ((slots run).take (fs run s.op)).map Slot.record)) =
      latest key (init ++ ((slots run).take t).map Slot.record) := by
  rw [slots_history_split run hs]
  simp only [latest_append, Probe.earlier]
  cases latest key ((((run.ops[s.op]?.map Op.lanes).getD []).take s.lane).map Prod.fst) <;> rfl

/-- Final-trace consumed units and the chunk-start dense suffix reconstruct
the complete requester state, including supersession across boundaries. -/
theorem requester_partition (g : OnlineGeom) (run : BatchRun) (j n : Nat)
    (hj : j ≤ run.ops.length)
    (hn : n * g.unitsPerPrefix ≤ (OnlineBatch.stateAt g run j).frozen.length) :
    (List.range' 0 n).flatMap (fun i => DirectMasks.records ((OnlineBatch.traceOf g run).units i)) ++
      ((OnlineBatch.stateAt g run j).frozen.drop (n * g.unitsPerPrefix)).flatMap Bucket.recs ++
      (OnlineBatch.stateAt g run j).current.recs = requesterRecords (OnlineBatch.stateAt g run j) := by
  have hg := congrArg (List.flatMap Bucket.recs)
    (grouped_prefix (OnlineBatch.stateAt g run run.ops.length).frozen g.unitsPerPrefix n)
  simp only [List.flatMap_assoc] at hg
  change (List.range' 0 n).flatMap (fun i =>
    (((OnlineBatch.stateAt g run run.ops.length).frozen.drop (i * g.unitsPerPrefix)).take
      g.unitsPerPrefix).flatMap Bucket.recs) = _ at hg
  change _ = (OnlineBatch.stateAt g run j).frozen.flatMap Bucket.recs ++
    (OnlineBatch.stateAt g run j).current.recs
  rw [show (List.range' 0 n).flatMap (fun i =>
    DirectMasks.records ((OnlineBatch.traceOf g run).units i)) =
    ((OnlineBatch.stateAt g run run.ops.length).frozen.take
      (n * g.unitsPerPrefix)).flatMap Bucket.recs from hg]
  rw [frozen_take_prefix (BatchFreshProof.frozen_prefix g run run.ops.length hj (Nat.le_refl _))
    _ hn, ← List.flatMap_append, List.take_append_drop]

end RebuildBound.BatchCorrectnessProof
