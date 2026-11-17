import RebuildBound.Proofs.Requester
import RebuildBound.Proofs.OnlineCorrectness.Lookup
import RebuildBound.Proofs.OnlineFresh.Requester

/-! The requester preserves latest-record lookup across clearing and freezing.
The equality concerns the entire chronological state, so duplicate keys may
span any number of frozen units. -/

namespace RebuildBound.OnlineCorrectnessProof

open Model Model.Online Model.DirectPrefix

/-- All stored requester records, oldest first. -/
def requesterRecords (st : Requester.State) : List Rec :=
  st.frozen.flatMap Bucket.recs ++ st.current.recs

/-- Moving a full current unit into the frozen prefix does not change order. -/
theorem requesterRecords_insert (E : Nat) (st : Requester.State) (r : Option Rec) :
    requesterRecords (Requester.insert E st r) = requesterRecords st ++ r.toList := by
  unfold Requester.insert requesterRecords
  split_ifs <;> cases r <;> simp [Bucket.recs, List.flatMap_append, List.append_assoc]

/-- Clearing the insertion key cannot affect the newest-record result after
its replacement has been appended. -/
theorem requester_step_access (E : Nat) (key : LogicalKey) (st : Requester.State) (r : Rec) :
    latest key (requesterRecords (Requester.step E st (.access r true))) =
      latest key (requesterRecords st ++ [r]) := by
  simp only [Requester.step, ite_true, requesterRecords_insert, Option.toList_some]
  unfold requesterRecords
  simp only [RequesterAux.recs_clearKey, latest_append]
  by_cases h : r.key = key
  · simp [latest, h]
  · rw [latest_filter_key key st.current.recs (fun k => k != r.key)]
    simp [Ne.symm h]

private theorem requester_run_access (E : Nat) (key : LogicalKey) (st : Requester.State) (ops : List Op) :
    latest key (requesterRecords
      (Requester.run E st (ops.map fun o => .access o.record true))) =
      latest key (requesterRecords st ++ ops.map Op.record) := by
  induction ops generalizing st with
  | nil => simp [Requester.run]
  | cons o ops ih =>
    simp only [List.map_cons, Requester.run, List.foldl_cons] at ⊢
    rw [← Requester.run, ih, latest_append, requester_step_access, latest_append]
    rw [show o.record :: List.map Op.record ops = [o.record] ++ List.map Op.record ops by rfl,
      latest_append]
    simp only [latest_append]
    cases latest key (List.map Op.record ops) <;> rfl

/-- At operation boundaries, the stored records and all supplied records have
exactly the same newest record for every key. -/
theorem requester_history (g : OnlineGeom) (run : OnlineRun) (j : Nat) (key : LogicalKey) :
    latest key ((stateAt g run j).frozen.flatMap Bucket.recs ++
      (stateAt g run j).current.recs) =
      latest key ((run.ops.take j).map Op.record) := by
  simpa [stateAt, requesterRecords, Bucket.recs] using
    requester_run_access g.unitEntries key ⟨[], []⟩ (run.ops.take j)

/-- Grouping consecutive units into prefixes preserves their order. -/
theorem grouped_prefix {α : Type} (xs : List α) (width n : Nat) :
    (List.range' 0 n).flatMap (fun i => (xs.drop (i * width)).take width) =
      xs.take (n * width) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range'_1_concat, List.flatMap_append]
    simp only [Nat.zero_add, List.flatMap_cons, List.flatMap_nil, List.append_nil, ih,
      Nat.succ_mul, List.take_add]

/-- A prefix of the final frozen units agrees with the same completed units
at the earlier operation boundary. -/
theorem frozen_take_prefix {α : Type} {xs ys : List α} (h : xs <+: ys)
    (n : Nat) (hn : n ≤ xs.length) : ys.take n = xs.take n := by
  obtain ⟨tail, rfl⟩ := h
  exact List.take_append_of_le_length hn

/-- The consumed trace prefix followed by the unconsumed requester suffix
is precisely the complete requester state at this operation boundary. -/
theorem requester_partition (g : OnlineGeom) (run : OnlineRun) (j n : Nat)
    (hj : j ≤ run.ops.length)
    (hn : n * g.unitsPerPrefix ≤ (stateAt g run j).frozen.length) :
    (List.range' 0 n).flatMap (fun i => DirectMasks.records ((traceOf g run).units i)) ++
      ((stateAt g run j).frozen.drop (n * g.unitsPerPrefix)).flatMap Bucket.recs ++
      (stateAt g run j).current.recs = requesterRecords (stateAt g run j) := by
  have hg := congrArg (List.flatMap Bucket.recs)
    (grouped_prefix (stateAt g run run.ops.length).frozen g.unitsPerPrefix n)
  simp only [List.flatMap_assoc] at hg
  change (List.range' 0 n).flatMap (fun i =>
    (((stateAt g run run.ops.length).frozen.drop (i * g.unitsPerPrefix)).take
      g.unitsPerPrefix).flatMap Bucket.recs) = _ at hg
  change _ = (stateAt g run j).frozen.flatMap Bucket.recs ++ (stateAt g run j).current.recs
  rw [show (List.range' 0 n).flatMap (fun i => DirectMasks.records ((traceOf g run).units i)) =
    ((stateAt g run run.ops.length).frozen.take (n * g.unitsPerPrefix)).flatMap Bucket.recs from hg]
  rw [frozen_take_prefix (OnlineFreshProof.frozen_prefix g run run.ops.length hj (Nat.le_refl _))
    _ hn, ← List.flatMap_append, List.take_append_drop]

end RebuildBound.OnlineCorrectnessProof
