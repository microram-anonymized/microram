import RebuildBound.Proofs.OnlineCorrectness.Cascade

/-! The computed cascade addresses agree with the existing online views. -/
namespace RebuildBound.OnlineCorrectnessProof
open Model Model.Hierarchy Model.Online Model.DirectPrefix Model.Probe

/-- Address agreement needs only completeness of the selected real table scans. -/
theorem scalar_addresses {cfg : Config} {sh : Shapes} {g : OnlineGeom} {run : OnlineRun}
    {S : Schedule} {words : Words} {dummy : Nat → Nat → Nat} {j : Nat} {o : Online.Op}
    (ho : run.ops[j]? = some o) (hp : o.probes = true)
    (hs : ∀ c ∈ (S j).tables,
      scan o.record.key (table cfg sh (Online.traceOf g run) words c.1 c.2)
        (bucket cfg c.1 c.2 (jobWord cfg words c.1 c.2 o.record.key)) =
      latest o.record.key (table cfg sh (Online.traceOf g run) words c.1 c.2).records)
    (i : Nat) :
    (Probe.scalar cfg sh g run S words dummy j).addresses.getD i 0 =
      Online.touched cfg sh g run S words dummy j i := by
  unfold Probe.scalar
  simp only [ho]
  rw [ite_eq_left hp]
  unfold Probe.hierarchy
  rw [List.getD_eq_getElem?_getD, cascade_addresses _ _ _ _ _ _ _ i hs]
  cases he : (S j).tables[i]? with
  | none => simp [he, Online.touched, ho]
  | some c =>
    simp only [Option.map_some, Option.getD_some, Nat.zero_add]
    unfold Online.touched
    simp only [ho, he]
    rw [ite_eq_left hp]
    have hr : Online.isReal cfg sh g run S words j i = true ↔
        latest o.record.key (Online.denseRecords cfg g run S j) = none ∧
          ∀ earlier ∈ (S j).tables.take i,
            latest o.record.key (table cfg sh (Online.traceOf g run) words earlier.1 earlier.2).records = none := by
      simp [Online.isReal, ho, hp, Online.denseKeys, Online.tableKeys, latest_none_iff,
        List.all_eq_true]
    by_cases hreal : Online.isReal cfg sh g run S words j i = true
    · rw [ite_eq_left hreal, ite_eq_left (hr.mp hreal)]
    · rw [ite_eq_right hreal, ite_eq_right (fun h => hreal (hr.mpr h))]

/-- A duplicate lane has a preceding supplied record, including a tombstone. -/
theorem earlier_none_iff (run : OnlineBatch.BatchRun) (s : OnlineBatch.Slot) :
    latest s.record.key (Probe.earlier run s) = none ↔ OnlineBatch.duplicate run s = false := by
  rw [latest_none_iff]
  simp only [Probe.earlier, OnlineBatch.duplicate, List.any_eq_false, List.map_map,
    List.mem_map, Function.comp_apply, not_exists, not_and, beq_iff_eq]

theorem batch_addresses {cfg : Config} {sh : Shapes} {g : OnlineGeom} {run : OnlineBatch.BatchRun}
    {S : Schedule} {words : Words} {dummy : Nat → Nat → Nat} {t : Nat} {s : OnlineBatch.Slot}
    (ho : (OnlineBatch.slots run)[t]? = some s) (hp : s.probes = true)
    (hs : ∀ c ∈ (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables,
      scan s.record.key (table cfg sh (OnlineBatch.traceOf g run) words c.1 c.2)
        (bucket cfg c.1 c.2 (jobWord cfg words c.1 c.2 s.record.key)) =
      latest s.record.key (table cfg sh (OnlineBatch.traceOf g run) words c.1 c.2).records)
    (i : Nat) :
    (Probe.batch cfg sh g run S words dummy t).addresses.getD i 0 =
      OnlineBatch.touched cfg sh g run S words dummy t i := by
  unfold Probe.batch
  simp only [ho]
  rw [ite_eq_left hp]
  unfold Probe.hierarchy
  rw [List.getD_eq_getElem?_getD, cascade_addresses _ _ _ _ _ _ _ i hs]
  cases he : (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables[i]? with
  | none => simp [he, OnlineBatch.touched, ho]
  | some c =>
    simp only [Option.map_some, Option.getD_some, Nat.zero_add]
    unfold OnlineBatch.touched
    simp only [ho, he]
    rw [ite_eq_left hp]
    have hn : ((latest s.record.key (Probe.earlier run s)).orElse (fun _ =>
        latest s.record.key (OnlineBatch.denseRecords cfg g run S t))) = none ↔
        OnlineBatch.duplicate run s = false ∧
          latest s.record.key (OnlineBatch.denseRecords cfg g run S t) = none := by
      rw [← earlier_none_iff]
      cases latest s.record.key (Probe.earlier run s) <;> simp
    have hr : OnlineBatch.isReal cfg sh g run S words t i = true ↔
        ((latest s.record.key (Probe.earlier run s)).orElse (fun _ =>
          latest s.record.key (OnlineBatch.denseRecords cfg g run S t))) = none ∧
          ∀ earlier ∈ (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables.take i,
            latest s.record.key (table cfg sh (OnlineBatch.traceOf g run) words earlier.1 earlier.2).records = none := by
      rw [hn]
      simp [OnlineBatch.isReal, ho, hp, OnlineBatch.denseKeys, OnlineBatch.tableKeys,
        latest_none_iff, List.all_eq_true, and_assoc]
    by_cases hreal : OnlineBatch.isReal cfg sh g run S words t i = true
    · rw [ite_eq_left hreal, ite_eq_left (hr.mp hreal)]
    · rw [ite_eq_right hreal, ite_eq_right (fun h => hreal (hr.mpr h))]

end RebuildBound.OnlineCorrectnessProof
