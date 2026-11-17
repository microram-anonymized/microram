import RebuildBound.Spec.ApiExecution
import RebuildBound.Proofs.AdaptiveFound.Causal
import RebuildBound.Proofs.AdaptiveReplay

namespace RebuildBound.ApiExecutionProof
open Spec Model Model.Hierarchy Model.Online Model.OnlineBatch Model.PublicApi
open Model.ApiExecution BatchFreshProof

variable (c : Api.Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
  (S : Schedule) (init : List Rec)

@[simp] theorem chunkRecords_length (pre : List OnlineBatch.Op) (earlier : List Rec)
    (qs : List Api.Request) :
    (chunkRecords c cfg sh g S init pre earlier qs).length = qs.length := by
  induction qs generalizing earlier with
  | nil => rfl
  | cons q qs ih => simp only [chunkRecords, List.length_cons, ih]

@[simp] theorem chunkRecords_keys (pre : List OnlineBatch.Op) (earlier : List Rec)
    (qs : List Api.Request) :
    (chunkRecords c cfg sh g S init pre earlier qs).map Rec.key = qs.map Api.Request.key := by
  induction qs generalizing earlier with
  | nil => rfl
  | cons q qs ih => simp only [chunkRecords, List.map_cons, Api.postRecord, ih]

@[simp] theorem operation_length (pre : List OnlineBatch.Op) (group : PublicApi.Group Api.Request) :
    (operation c cfg sh g S init pre group).lanes.length = group.lanes.length := by
  cases group <;> simp [operation, Op.lanes, Group.lanes]

@[simp] theorem operations_widths (pre : List OnlineBatch.Op) (groups : List (PublicApi.Group Api.Request)) :
    (operations c cfg sh g S init pre groups).map (fun o => o.lanes.length) =
      groups.map (fun group => group.lanes.length) := by
  induction groups generalizing pre with
  | nil => rfl
  | cons group rest ih => simp only [operations, List.map_cons, operation_length, ih]

@[simp] theorem operation_keys (pre : List OnlineBatch.Op) (group : PublicApi.Group Api.Request)
    (hv : Valid group) :
    (operation c cfg sh g S init pre group).lanes.map (fun rp => (rp.1.key, rp.2)) =
      group.lanes.map (fun q => (q.key, q.probes)) := by
  cases group with
  | blind q => simp [operation, Op.lanes, Group.lanes, Api.postRecord, Valid] at hv ⊢; exact hv
  | chunk qs =>
    simp only [operation, Op.lanes, List.map_map, Group.lanes]
    have hp : qs.map (fun q => (q.key, q.probes)) = qs.map (fun q => (q.key, true)) := by
      apply List.map_congr_left
      intro q hq
      rw [hv q hq]
    rw [hp]
    have he := congrArg (List.map (fun k => (k, true))) (chunkRecords_keys c cfg sh g S init pre [] qs)
    simpa only [List.map_map, Function.comp_def] using he

theorem operations_keys (pre : List OnlineBatch.Op) (groups : List (PublicApi.Group Api.Request))
    (hv : ∀ group ∈ groups, Valid group) :
    ((operations c cfg sh g S init pre groups).flatMap Op.lanes).map
        (fun rp => (rp.1.key, rp.2)) =
      (groups.flatMap Group.lanes).map (fun q => (q.key, q.probes)) := by
  induction groups generalizing pre with
  | nil => rfl
  | cons group rest ih =>
    simp only [operations, List.flatMap_cons, List.map_append]
    rw [operation_keys c cfg sh g S init pre group (hv group (by simp)),
      ih _ (fun x hx => hv x (by simp [hx]))]

theorem shape (groups : List (PublicApi.Group Api.Request))
    (hv : ∀ group ∈ groups, Valid group) :
    widths (run c cfg sh g S init groups) = groups.map (fun group => group.lanes.length) ∧
    (slots (run c cfg sh g S init groups)).map (fun s => (s.record.key, s.probes)) =
      (groups.flatMap Group.lanes).map (fun q => (q.key, q.probes)) := by
  refine ⟨operations_widths c cfg sh g S init [] groups, ?_⟩
  rw [show (slots (run c cfg sh g S init groups)).map (fun s => (s.record.key, s.probes)) =
    (run c cfg sh g S init groups).ops.flatMap (fun o => o.lanes.map (fun rp => (rp.1.key, rp.2))) from
      AdaptiveReplayProof.slots_map _ (fun rp => (rp.1.key, rp.2))]
  simpa only [run, List.map_flatMap] using operations_keys c cfg sh g S init [] groups hv

/-- Locate a lane after a supplied operation prelude, independently of the suffix. -/
theorem slot_append (pre : List OnlineBatch.Op) (op : OnlineBatch.Op)
    (rest : List OnlineBatch.Op) (unsh : Rec → Bool) (l : Nat) (rp : Rec × Bool)
    (hl : op.lanes[l]? = some rp) :
    (slots ⟨pre ++ op :: rest, init, unsh⟩)[offset pre + l]? =
      some ⟨pre.length, l, rp.1, rp.2⟩ := by
  have ho : (pre ++ op :: rest)[pre.length]? = some op := by simp
  have h := slot_at (⟨pre ++ op :: rest, init, unsh⟩ : BatchRun) ho hl
  simpa [fs, widths, ← List.map_take, offset] using h

/-- Earlier-lane forwarding observes exactly the already constructed lane list. -/
theorem earlier_append (pre : List OnlineBatch.Op) (earlier : List Rec)
    (r : Rec) (later : List Rec) (rest : List OnlineBatch.Op) (unsh : Rec → Bool) :
    Probe.earlier ⟨pre ++ .batch (earlier ++ r :: later) :: rest, init, unsh⟩
      ⟨pre.length, earlier.length, r, true⟩ = earlier := by
  simp [Probe.earlier, Op.lanes, Function.comp_def]

/-- Replace a provisional lane by its generated record and finish its group and
future operations. Causality preserves the complete selected record. -/
theorem selected_provisional (pre : List OnlineBatch.Op) (earlier : List Rec)
    (q : Api.Request) (r : Rec) (later : List Rec) (rest : List OnlineBatch.Op)
    (n m : Nat) (hg : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hS : SchedulePremises cfg S n m)
    (ht : offset pre + earlier.length < n) (hk : r.key = q.key) :
    (Probe.batch cfg sh g (provisional c init pre earlier q) S
      (fun _ _ _ => 0) (fun _ _ => 0) (offset pre + earlier.length)).found =
    (Probe.batch cfg sh g
      ⟨pre ++ .batch (earlier ++ r :: later) :: rest, init, fun r => c.flag r.val⟩ S
      (fun _ _ _ => 0) (fun _ _ => 0) (offset pre + earlier.length)).found := by
  let full : BatchRun :=
    ⟨pre ++ .batch (earlier ++ r :: later) :: rest, init, fun r => c.flag r.val⟩
  let temp := provisional c init pre earlier q
  have hs : (slots full)[offset pre + earlier.length]? =
      some ⟨pre.length, earlier.length, r, true⟩ :=
    slot_append init pre (.batch (earlier ++ r :: later)) rest _ earlier.length (r, true) (by
      simp only [Op.lanes, List.getElem?_map, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.map_some])
  have hs' : (slots temp)[offset pre + earlier.length]? =
      some ⟨pre.length, earlier.length, Api.postRecord c q none, true⟩ :=
    slot_append init pre (.batch (earlier ++ [Api.postRecord c q none])) [] _ earlier.length (Api.postRecord c q none, true) (by
      simp only [Op.lanes, List.getElem?_map, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.map_some])
  exact AdaptiveFoundProof.foundCausal cfg sh g full temp S n m
    (fun _ _ _ => 0) (fun _ _ => 0) _ _ _ hg hE hS ht rfl rfl
    (by simp [full, temp, provisional]) hs hs' rfl
    (by simpa [Api.postRecord] using hk.symm) rfl
    (by simp only [full, temp, provisional]; rw [earlier_append, earlier_append])

/-- Every lane of a completed chunk was constructed from that completed run's
physical selection. The statement allows arbitrary earlier lanes and future ops. -/
theorem chunk_correct (pre : List OnlineBatch.Op) (earlier : List Rec)
    (qs : List Api.Request) (rest : List OnlineBatch.Op)
    (n m : Nat) (hg : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hS : SchedulePremises cfg S n m)
    (hn : offset pre + earlier.length + qs.length ≤ n) :
    ∀ i q, qs[i]? = some q →
    let full : BatchRun :=
      ⟨pre ++ .batch (earlier ++ chunkRecords c cfg sh g S init pre earlier qs) :: rest,
        init, fun r => c.flag r.val⟩
    ∃ r, (slots full)[offset pre + earlier.length + i]? =
        some ⟨pre.length, earlier.length + i, r, true⟩ ∧
      r.key = q.key ∧ r = Api.postRecord c q
        (Probe.batch cfg sh g full S (fun _ _ _ => 0) (fun _ _ => 0)
          (offset pre + earlier.length + i)).found := by
  induction qs generalizing earlier with
  | nil => intro i q hq; simp at hq
  | cons head qs ih =>
    let selected := (Probe.batch cfg sh g (provisional c init pre earlier head) S
      (fun _ _ _ => 0) (fun _ _ => 0) (offset pre + earlier.length)).found
    let r := Api.postRecord c head selected
    let tail := chunkRecords c cfg sh g S init pre (earlier ++ [r]) qs
    intro i q hq
    cases i with
    | zero =>
      have hq' : head = q := by simpa using hq
      subst q
      refine ⟨r, ?_, rfl, ?_⟩
      · simpa only [Nat.add_zero, chunkRecords] using
          slot_append init pre (.batch (earlier ++ r :: tail)) rest (fun r => c.flag r.val)
            earlier.length (r, true) (by
              simp only [Op.lanes, List.getElem?_map,
                List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
                List.getElem?_cons_zero, Option.map_some])
      · simp only [Nat.add_zero, chunkRecords]
        exact congrArg (Api.postRecord c head)
          (selected_provisional c cfg sh g S init pre earlier head r tail rest n m
            hg hE hS (by simp only [List.length_cons] at hn; omega) rfl)
    | succ i =>
      have hn' : offset pre + (earlier ++ [r]).length + qs.length ≤ n := by
        simp only [List.length_append, List.length_cons, List.length_nil] at *
        omega
      have hi := ih (earlier ++ [r]) hn' i q (by simpa using hq)
      simpa only [chunkRecords, List.length_append, List.length_singleton,
        List.append_assoc, List.singleton_append, Nat.add_assoc,
        Nat.add_comm 1 i] using hi

@[simp] theorem offset_append (pre rest : List OnlineBatch.Op) :
    offset (pre ++ rest) = offset pre + offset rest := by
  simp [offset, List.sum_append]

@[simp] theorem offset_singleton (op : OnlineBatch.Op) : offset [op] = op.lanes.length := by
  simp [offset]

/-- Each newly compiled request implements its physical lane, even when the
compiled fragment has a prelude and a continuation. -/
theorem operations_correct (pre : List OnlineBatch.Op) (groups : List (PublicApi.Group Api.Request))
    (rest : List OnlineBatch.Op) (n m : Nat)
    (hg : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hS : SchedulePremises cfg S n m)
    (hv : ∀ group ∈ groups, Valid group)
    (hn : offset pre + (groups.flatMap Group.lanes).length ≤ n) :
    ∀ i q, (groups.flatMap Group.lanes)[i]? = some q →
    let full : BatchRun :=
      ⟨pre ++ operations c cfg sh g S init pre groups ++ rest, init, fun r => c.flag r.val⟩
    ∃ s, (slots full)[offset pre + i]? = some s ∧ s.record.key = q.key ∧
      s.probes = q.probes ∧ s.record = Api.postRecord c q
        (Probe.batch cfg sh g full S (fun _ _ _ => 0) (fun _ _ => 0) (offset pre + i)).found := by
  induction groups generalizing pre with
  | nil => intro i q hq; simp at hq
  | cons group groups ih =>
    intro i q hq
    have hvgroup : Valid group := hv group (by simp)
    have hvrest : ∀ x ∈ groups, Valid x := fun x hx => hv x (by simp [hx])
    let op := operation c cfg sh g S init pre group
    let next := operations c cfg sh g S init (pre ++ [op]) groups
    by_cases hi : i < group.lanes.length
    · have hqg : group.lanes[i]? = some q := by
        simpa only [List.flatMap_cons, List.getElem?_append_left hi] using hq
      cases group with
      | blind head =>
        have hi0 : i = 0 := by simpa [Group.lanes] using hi
        subst i
        have hhead : head = q := by simpa [Group.lanes] using hqg
        subst q
        let r := Api.postRecord c head none
        have hs : (slots (⟨pre ++ .blind r :: (next ++ rest), init,
            fun r => c.flag r.val⟩ : BatchRun))[offset pre]? =
            some ⟨pre.length, 0, r, false⟩ := by
          simpa using slot_append init pre (.blind r) (next ++ rest) (fun r => c.flag r.val)
            0 (r, false) rfl
        have hsfull : (slots (⟨pre ++ operations c cfg sh g S init pre
            (.blind head :: groups) ++ rest, init, fun r => c.flag r.val⟩ : BatchRun))[offset pre + 0]? = some ⟨pre.length, 0, r, false⟩ := by
          simpa only [Nat.add_zero, operations, operation, List.cons_append,
            List.append_assoc, next, op, r] using hs
        refine ⟨⟨pre.length, 0, r, false⟩, hsfull, rfl, hvgroup.symm, ?_⟩
        simp only [Probe.batch, hsfull, Bool.false_eq_true, ite_false]
        rfl
      | chunk qs =>
        have hnq : offset pre + ([] : List Rec).length + qs.length ≤ n := by
          simp only [List.flatMap_cons, Group.lanes, List.length_append] at hn
          simp only [List.length_nil, Nat.add_zero]
          omega
        obtain ⟨r, hs, hk, hr⟩ := chunk_correct c cfg sh g S init pre [] qs (next ++ rest)
          n m hg hE hS hnq i q hqg
        refine ⟨⟨pre.length, i, r, true⟩, ?_, hk, (hvgroup q (List.mem_of_getElem? hqg)).symm, ?_⟩
        · simpa only [operations, operation, List.length_nil, Nat.add_zero, Nat.zero_add,
            List.nil_append, List.cons_append, List.append_assoc, next, op] using hs
        · simpa only [operations, operation, List.length_nil, Nat.add_zero,
            List.nil_append, List.cons_append, List.append_assoc, next, op] using hr
    · have hge : group.lanes.length ≤ i := by omega
      have hqr : (groups.flatMap Group.lanes)[i - group.lanes.length]? = some q := by
        simpa only [List.flatMap_cons, List.getElem?_append_right hge] using hq
      have hn' : offset (pre ++ [op]) + (groups.flatMap Group.lanes).length ≤ n := by
        simp only [offset_append, offset_singleton, op, operation_length]
        simpa only [List.flatMap_cons, List.length_append, Nat.add_assoc] using hn
      have ht : offset (pre ++ [op]) + (i - group.lanes.length) = offset pre + i := by
        simp only [offset_append, offset_singleton, op, operation_length]
        omega
      have hx := ih (pre ++ [op]) hvrest hn' (i - group.lanes.length) q hqr
      simpa only [ht, operations, List.append_assoc, List.singleton_append,
        List.cons_append, List.nil_append, op] using hx

theorem implements (groups : List (PublicApi.Group Api.Request)) (m : Nat)
    (hg : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hv : ∀ group ∈ groups, Valid group)
    (hS : SchedulePremises cfg S (groups.flatMap Group.lanes).length m) :
    Api.Implements c cfg sh g (run c cfg sh g S init groups) S
      (fun _ _ _ => 0) (fun _ _ => 0) (groups.flatMap Group.lanes) := by
  have hshape := (shape c cfg sh g S init groups hv).2
  refine ⟨?_, ?_⟩
  · have hlen := congrArg List.length hshape
    simpa only [List.length_map] using hlen.symm
  · intro t q s hq hs
    obtain ⟨s', hs', hk, hp, hr⟩ := operations_correct c cfg sh g S init [] groups []
      (groups.flatMap Group.lanes).length m hg hE hS hv (by simp [offset]) t q hq
    have hs'' : (slots (run c cfg sh g S init groups))[t]? = some s' := by
      simpa [offset, run] using hs'
    rw [hs] at hs''
    cases hs''
    refine ⟨hk, hp, ?_⟩
    simpa [offset, run] using hr

end RebuildBound.ApiExecutionProof

namespace RebuildBound
theorem ApiExecutionShape : Spec.ApiExecutionShape_statement := ApiExecutionProof.shape

theorem ApiExecutionImplements : Spec.ApiExecutionImplements_statement := ApiExecutionProof.implements
end RebuildBound
