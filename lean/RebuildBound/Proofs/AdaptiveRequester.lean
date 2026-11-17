import RebuildBound.Spec.AdaptiveSteps
import RebuildBound.Proofs.Requester

/-!
# AdaptiveRequester: the trace premises of any batch run

The trace of a batch run reads the frozen units of the requester state after
the whole run, `r0 = unitsPerPrefix` units per level-one ordinal.

* `nodup`: every unit stays internally unique (`RequesterUnique` from the
  fresh ring).
* `load`: every frozen unit has `E = unitEntries` lanes (`RequesterShape`), a
  unit's records are at most its lanes, and an ordinal holds at most `r0`
  units, so at most `r0 · E = carryPositions 1 = load · carry1` records.
* `keys`: a record of the requester state is a lane record of some operation,
  and every lane record is a slot record (fold invariant `KeysIn`).
* `init` fields: the trace's initialization input is the run's.

No probability is involved, so the measure-based API is not used.
-/

namespace RebuildBound

namespace AdaptiveRequesterProof

open Spec Model

/-- A fold invariant that may use membership of the folded element. -/
theorem foldl_inv_mem {α β : Type} (P : β → Prop) (f : β → α → β) :
    ∀ (xs : List α) (s : β), P s → (∀ s x, x ∈ xs → P s → P (f s x)) → P (xs.foldl f s)
  | [], _, h, _ => h
  | x :: xs, s, h, hf =>
    foldl_inv_mem P f xs _ (hf s x (List.mem_cons_self ..) h)
      (fun s' y hy hs => hf s' y (List.mem_cons_of_mem _ hy) hs)

/-- A requester operation whose records have keys in `U`. -/
def GoodOp (U : Finset LogicalKey) : Requester.Op → Prop
  | .access r _ => r.key ∈ U
  | .batch lanes => ∀ r ∈ lanes, r.key ∈ U

/-- Every record of the requester state, frozen or current, has its key in `U`. -/
def KeysIn (U : Finset LogicalKey) (st : Requester.State) : Prop :=
  (∀ u ∈ st.frozen, ∀ x ∈ Bucket.recs u, x.key ∈ U) ∧ ∀ x ∈ Bucket.recs st.current, x.key ∈ U

theorem insert_keys {U : Finset LogicalKey} (e : Nat) (st : Requester.State) (l : Option Rec)
    (h : KeysIn U st) (hl : ∀ r, l = some r → r.key ∈ U) :
    KeysIn U (Requester.insert e st l) := by
  have key : ∀ x ∈ Bucket.recs (st.current ++ [l]), x.key ∈ U := by
    intro x hx
    rw [RequesterAux.recs_append_single] at hx
    rcases List.mem_append.1 hx with hx | hx
    · exact h.2 x hx
    · cases l with
      | none => simp at hx
      | some r =>
        simp only [Option.toList_some, List.mem_singleton] at hx
        rw [hx]
        exact hl r rfl
  unfold Requester.insert
  split_ifs
  · refine ⟨?_, by simp [Bucket.recs]⟩
    intro u hu
    rcases List.mem_append.1 hu with hu | hu
    · exact h.1 u hu
    · rw [List.mem_singleton.1 hu]
      exact key
  · exact ⟨h.1, key⟩

theorem step_keys {U : Finset LogicalKey} (e : Nat) (st : Requester.State) (op : Requester.Op)
    (h : KeysIn U st) (hop : GoodOp U op) : KeysIn U (Requester.step e st op) := by
  cases op with
  | access r real =>
    simp only [Requester.step]
    refine insert_keys e _ _ ⟨h.1, ?_⟩ ?_
    · intro x hx
      rw [RequesterAux.recs_clearKey] at hx
      exact h.2 x (List.mem_filter.1 hx).1
    · intro r' hr'
      by_cases hreal : real = true
      · simp only [hreal, ↓reduceIte] at hr'
        cases hr'
        exact hop
      · simp only [hreal] at hr'
        cases hr'
  | batch lanes =>
    simp only [Requester.step]
    have h0 : KeysIn U ⟨st.frozen, lanes.foldl (fun u r => Requester.clearKey r.key u) st.current⟩ :=
      ⟨h.1, fun x hx => h.2 x ((RequesterAux.foldl_clear_sub lanes _).subset hx)⟩
    refine foldl_inv_mem (KeysIn U) _ lanes.zipIdx _ h0 ?_
    intro s ri hri hs
    refine insert_keys e s _ hs ?_
    intro r hr
    by_cases hsup : Requester.superseded lanes ri.2 ri.1 = true
    · simp only [hsup, ↓reduceIte] at hr
      cases hr
    · simp only [hsup] at hr
      cases hr
      exact hop _ (List.fst_mem_of_mem_zipIdx hri)

theorem run_keys {U : Finset LogicalKey} (e : Nat) (ops : List Requester.Op) (st : Requester.State)
    (h : KeysIn U st) (hops : ∀ op ∈ ops, GoodOp U op) : KeysIn U (Requester.run e st ops) := by
  unfold Requester.run
  exact foldl_inv_mem _ _ ops st h (fun s op hop hs => step_keys e s op hs (hops op hop))

/-- Every lane record of every operation is a slot record. -/
theorem lanes_keys {U : Finset LogicalKey} {run : OnlineBatch.BatchRun}
    (h : ∀ s ∈ OnlineBatch.slots run, s.record.key ∈ U) :
    ∀ o ∈ run.ops, ∀ rp ∈ o.lanes, rp.1.key ∈ U := by
  intro o ho rp hrp
  have ho' : o ∈ run.ops.zipIdx.map Prod.fst := by
    rw [List.zipIdx_map_fst]
    exact ho
  obtain ⟨oj, hoj, rfl⟩ := List.mem_map.1 ho'
  have hrp' : rp ∈ oj.1.lanes.zipIdx.map Prod.fst := by
    rw [List.zipIdx_map_fst]
    exact hrp
  obtain ⟨rl, hrl, rfl⟩ := List.mem_map.1 hrp'
  exact h ⟨oj.2, rl.2, rl.1.1, rl.1.2⟩
    (List.mem_flatMap.2 ⟨oj, hoj, List.mem_map.2 ⟨rl, hrl, rfl⟩⟩)

theorem good_requester {U : Finset LogicalKey} (o : OnlineBatch.Op)
    (h : ∀ rp ∈ o.lanes, rp.1.key ∈ U) : GoodOp U o.requester := by
  cases o with
  | probe r => exact h (r, true) (by simp [OnlineBatch.Op.lanes])
  | blind r => exact h (r, false) (by simp [OnlineBatch.Op.lanes])
  | batch lanes =>
    intro r hr
    exact h (r, true) (by simp [OnlineBatch.Op.lanes, hr])

/-- Units of `E` lanes hold at most `E` records each. -/
theorem records_length_le (E : Nat) :
    ∀ L : List Bucket, (∀ u ∈ L, u.length = E) →
      (DirectMasks.records L).length ≤ L.length * E
  | [], _ => by simp [DirectMasks.records]
  | u :: L, h => by
    have h1 : (Bucket.recs u).length ≤ u.length := by
      unfold Bucket.recs
      exact List.length_filterMap_le _ _
    have h2 := records_length_le E L (fun v hv => h v (List.mem_cons_of_mem _ hv))
    have hu := h u (List.mem_cons_self ..)
    rw [hu] at h1
    simp only [DirectMasks.records, List.flatMap_cons, List.length_append,
      List.length_cons] at h2 ⊢
    rw [Nat.succ_mul]
    omega

end AdaptiveRequesterProof

open AdaptiveRequesterProof Model

theorem RequesterTrace : Spec.RequesterTrace_statement := by
  intro cfg U g run hgeom hE hkeys hinit hinitU
  -- the requester state after the whole run, from the fresh ring
  have hst : OnlineBatch.stateAt g run run.ops.length =
      Model.Requester.run g.unitEntries ⟨[], []⟩
        ((run.ops.take run.ops.length).map OnlineBatch.Op.requester) := rfl
  have hunits : ∀ i, ∀ u ∈ (OnlineBatch.traceOf g run).units i,
      u ∈ (OnlineBatch.stateAt g run run.ops.length).frozen := by
    intro i u hu
    exact List.mem_of_mem_drop (List.mem_of_mem_take hu)
  have huniq : Model.Requester.Unique (OnlineBatch.stateAt g run run.ops.length) := by
    rw [hst]
    exact RequesterUnique _ _ _ ⟨by simp, by simp [Model.Bucket.recs]⟩
  have hshape := RequesterShape g.unitEntries ⟨[], []⟩
    ((run.ops.take run.ops.length).map OnlineBatch.Op.requester) hE (by simp) (by simpa using hE)
  rw [← hst] at hshape
  have hkin : KeysIn U (OnlineBatch.stateAt g run run.ops.length) := by
    rw [hst]
    refine run_keys _ _ _ ⟨by simp, by simp [Model.Bucket.recs]⟩ ?_
    intro op hop
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hop
    exact good_requester o (lanes_keys hkeys o (List.mem_of_mem_take ho))
  have hcarry : cfg.carryPositions 1 = cfg.load * cfg.carry1 := by
    simp [Model.Config.carryPositions, Model.Config.carry]
  refine ⟨?_, ?_, ?_, hinit, hinitU⟩
  · intro i u hu
    exact huniq.1 u (hunits i u hu)
  · intro i
    have hlen : ((OnlineBatch.traceOf g run).units i).length ≤ g.unitsPerPrefix :=
      List.length_take_le _ _
    have := records_length_le g.unitEntries ((OnlineBatch.traceOf g run).units i)
      (fun u hu => hshape.1 u (hunits i u hu))
    calc (Model.DirectMasks.records ((OnlineBatch.traceOf g run).units i)).length
        ≤ ((OnlineBatch.traceOf g run).units i).length * g.unitEntries := this
      _ ≤ g.unitsPerPrefix * g.unitEntries := Nat.mul_le_mul_right _ hlen
      _ = cfg.load * cfg.carry1 := by rw [Nat.mul_comm, hgeom, hcarry]
  · intro i x hx
    obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.1 hx
    exact hkin.1 u (hunits i u hu) x hxu

end RebuildBound
