import RebuildBound.Spec.AdaptiveNative
import RebuildBound.Proofs.BatchCorrectness.Endpoint
import RebuildBound.Proofs.BatchCorrectness.Scalar
import RebuildBound.Proofs.OnlineCorrectness
import RebuildBound.Proofs.HierarchyLawsChunks31
import RebuildBound.Proofs.HierarchyTopLaw.Init

/-!
# AdaptiveFoundMem: the selected record is a supplied record of the lane's key

`BatchFoundMem31` (`Spec/AdaptiveNative.lean`). The cascade returns the
initial hit (the latest earlier lane of the chunk with the key, else the
latest dense record with the key) or the first table hit, and both
`DirectPrefix.latest` and `Probe.scan` only return a record of the probed key.
Every candidate is a supplied record:

* earlier lanes are the slots `fs op + l < t` (`slots_history_split`);
* the dense records are requester records at the chunk start, and the
  requester only stores supplied lanes (`requester_sub`);
* every record of a table `(ℓ, v)` of the plan is an initialization record or
  a record of the trace units of the level-one ordinals up to `time ℓ v`
  (`table_prov`: below the top the tables are permutations of the winners of
  their inputs, `lowFor`; the top's reference jobs only move records,
  `topReference_P`, `tpReference_P`). The plan's windows end by the consumed
  positions, so those units are frozen at the chunk start
  (`consumed_frozen`, `requester_partition`).

No unshadowed promise is used, and nothing depends on the words.
-/

namespace RebuildBound.AdaptiveFoundMemProof

open Model Model.Hierarchy Model.Online Spec
open HierarchyInvariantProof OnlineFreshProof OnlineCorrectnessProof BatchFreshProof
  BatchCorrectnessProof

/-! ### The cascade selects the initial hit or a table record -/

theorem scan_mem {key : LogicalKey} {t : Output} {a : Nat} {f : Rec}
    (h : Probe.scan key t a = some f) : f ∈ t.records ∧ f.key = key := by
  unfold Probe.scan at h
  refine ⟨?_, latest_some_key h⟩
  have hm := latest_some_mem h
  unfold Output.records
  rcases List.mem_append.1 hm with hm | hm
  · refine List.mem_append_left _ (List.mem_flatMap.2 ?_)
    cases e : t.main[a]? with
    | none => simp [List.getD_eq_getElem?_getD, e, Bucket.recs] at hm
    | some B =>
      rw [List.getD_eq_getElem?_getD, e, Option.getD_some] at hm
      exact ⟨B, List.mem_of_getElem? e, hm⟩
  · exact List.mem_append_right _ hm

theorem orElse_eq_some {a : Option Rec} {b : Unit → Option Rec} {f : Rec}
    (h : a.orElse b = some f) : a = some f ∨ b () = some f := by
  cases a with
  | none => exact Or.inr h
  | some x => exact Or.inl h

theorem cascade_mem (key : LogicalKey) (tableAt : Nat × Nat → Output) (real : Nat × Nat → Nat)
    (dummy : Nat → Nat × Nat → Nat) :
    ∀ (cs : List (Nat × Nat)) (initial : Option Rec) (offset : Nat) (f : Rec),
      (Probe.cascade key tableAt real dummy cs initial offset).found = some f →
      initial = some f ∨ ∃ c ∈ cs, f ∈ (tableAt c).records ∧ f.key = key := by
  intro cs
  induction cs with
  | nil => intro initial offset f h; exact Or.inl h
  | cons c cs ih =>
    intro initial offset f h
    simp only [Probe.cascade, Probe.cascadeWith] at h
    rcases ih _ _ f h with h' | ⟨c', hc', hm⟩
    · rcases orElse_eq_some h' with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨c, List.mem_cons_self .., scan_mem h'⟩
    · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', hm⟩

/-! ### The requester stores only supplied lanes -/

theorem requester_step_sub (E : Nat) (st : Requester.State) (o : OnlineBatch.Op) :
    ∀ x ∈ requesterRecords (Requester.step E st o.requester),
      x ∈ requesterRecords st ∨ x ∈ o.lanes.map Prod.fst := by
  have hacc : ∀ r : Rec, ∀ x ∈ requesterRecords (Requester.step E st (.access r true)),
      x ∈ requesterRecords st ∨ x = r := by
    intro r x hx
    simp only [Requester.step, ite_true, requesterRecords_insert, Option.toList_some] at hx
    rcases List.mem_append.1 hx with h | h
    · left
      unfold requesterRecords at h ⊢
      rcases List.mem_append.1 h with h | h
      · exact List.mem_append_left _ h
      · rw [RequesterAux.recs_clearKey] at h
        exact List.mem_append_right _ (List.mem_of_mem_filter h)
    · right; simpa using h
  intro x hx
  cases o with
  | probe r =>
    rcases hacc r x hx with h | h
    · exact Or.inl h
    · right; simp [OnlineBatch.Op.lanes, h]
  | blind r =>
    rcases hacc r x hx with h | h
    · exact Or.inl h
    · right; simp [OnlineBatch.Op.lanes, h]
  | batch lanes =>
    have h := requester_batch_records E lanes lanes []
      ⟨st.frozen, lanes.foldl (fun u r => Requester.clearKey r.key u) st.current⟩ (by simp)
    simp only [List.length_nil] at h
    have e : requesterRecords (Requester.step E st (OnlineBatch.Op.batch lanes).requester) =
        requesterRecords ⟨st.frozen, lanes.foldl (fun u r => Requester.clearKey r.key u) st.current⟩ ++
          DirectPrefix.winners lanes := h
    rw [e] at hx
    rcases List.mem_append.1 hx with h | h
    · left
      unfold requesterRecords at h ⊢
      rcases List.mem_append.1 h with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ ((RequesterAux.foldl_clear_sub lanes st.current).subset h)
    · right
      have hx' := (prefix_sublist lanes).subset h
      simp [OnlineBatch.Op.lanes, hx']

theorem requester_run_sub (E : Nat) : ∀ (ops : List OnlineBatch.Op) (st : Requester.State),
    ∀ x ∈ requesterRecords (Requester.run E st (ops.map OnlineBatch.Op.requester)),
      x ∈ requesterRecords st ∨ x ∈ ops.flatMap (fun o => o.lanes.map Prod.fst)
  | [], _, _, hx => Or.inl hx
  | o :: ops, st, x, hx => by
    rcases requester_run_sub E ops (Requester.step E st o.requester) x hx with h | h
    · rcases requester_step_sub E st o x h with h | h
      · exact Or.inl h
      · right; rw [List.flatMap_cons]; exact List.mem_append_left _ h
    · right; rw [List.flatMap_cons]; exact List.mem_append_right _ h

/-- Every stored record after `j` operations is the record of a slot before
the `j`-th operation's first lane. -/
theorem requester_sub (g : OnlineGeom) (run : OnlineBatch.BatchRun) (j : Nat) :
    ∀ x ∈ requesterRecords (OnlineBatch.stateAt g run j),
      x ∈ ((OnlineBatch.slots run).take (fs run j)).map OnlineBatch.Slot.record := by
  intro x hx
  rw [slots_prefix_records]
  rcases requester_run_sub g.unitEntries (run.ops.take j) ⟨[], []⟩ x hx with h | h
  · simp [requesterRecords, Bucket.recs] at h
  · exact h

/-! ### Every table record is supplied -/

/-- A record of the initialization or of the trace units of the level-one
ordinals up to `K`. -/
def Supplied (tr : Trace) (s1 K : Nat) (x : Rec) : Prop :=
  x ∈ tr.init ∨ ∃ i, s1 + i + 1 ≤ K ∧ x ∈ DirectMasks.records (tr.units i)

theorem supplied_mono {tr : Trace} {s1 K K' : Nat} {x : Rec} (h : K ≤ K') :
    Supplied tr s1 K x → Supplied tr s1 K' x
  | Or.inl hx => Or.inl hx
  | Or.inr ⟨i, hi, hm⟩ => Or.inr ⟨i, hi.trans h, hm⟩

section prov
variable (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct) {N : Nat} {tr : Trace}
  (hT : TracePremises geo.cfg N tr) (words : Words)
include F hT

/-- Below the top, a table holds only records of the trace units up to its time. -/
theorem low_prov :
    ∀ ℓ, 1 ≤ ℓ → ℓ < geo.cfg.levels → ∀ v,
      ∀ x ∈ (table geo.cfg geo.shapes tr words ℓ v).records,
        ∃ i, geo.cfg.seed 1 + i + 1 ≤ time geo.cfg ℓ v ∧ x ∈ DirectMasks.records (tr.units i) := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ihℓ =>
  intro h1 hL v
  induction v using Nat.strong_induction_on with
  | _ v ihv =>
  intro x hx
  by_cases hv : geo.cfg.seed ℓ < v
  · have hp := (lowFor geo F hT words ℓ h1 hL v hv).2
    rcases mem_win (hp.mem_iff.1 hx) with h | h
    · unfold prevInFor at h
      split_ifs at h with hd
      · simp at h
      · obtain ⟨i, hi, hm⟩ := ihv (v - 1) (by omega) x h
        exact ⟨i, hi.trans (OnlineCorrectnessProof.time_mono _ _ (by omega)), hm⟩
    · unfold srcBFor at h
      split_ifs at h with hl
      · subst hl
        refine ⟨v - geo.cfg.seed 1 - 1, ?_, (prefix_sublist _).subset h⟩
        rw [OnlineCorrectnessProof.time_one]
        omega
      · unfold carryOf at h
        obtain ⟨i, hi, hm⟩ := ihℓ (ℓ - 1) (by omega) (by omega) (by omega) _ x h
        refine ⟨i, ?_, hm⟩
        rwa [OnlineCorrectnessProof.time_carry F (ℓ := ℓ - 1) (by omega) (by omega),
          Nat.sub_add_cancel (by omega)] at hi
  · rw [table_base (Or.inr (Or.inr (by omega))), base_low (by omega), records_empty] at hx
    simp at hx

omit hT in
/-- At and below the seeded top counter, the top table holds only
initialization records. -/
theorem top_base_prov {v : Nat} (hv : v ≤ geo.cfg.seed geo.cfg.levels) :
    ∀ x ∈ (table geo.cfg geo.shapes tr words geo.cfg.levels v).records, x ∈ tr.init := by
  intro x hx
  cases hi : geo.cfg.initialized with
  | false =>
    rw [top_base_emptyFor geo hi words hv] at hx
    simp [Output.records, Bucket.recs, Bucket.empty] at hx
  | true =>
    rw [top_base_eqFor geo hi words hv] at hx
    exact tpReference_P (P := fun x => x ∈ tr.init) _ _ _ _
      (fun y hy => HierarchyTopLawProof.initMain_mem _ _ y hy) x hx

/-- The top table holds only initialization records and records of the trace
units up to its time. -/
theorem top_prov :
    ∀ v, ∀ x ∈ (table geo.cfg geo.shapes tr words geo.cfg.levels v).records,
      Supplied tr (geo.cfg.seed 1) (time geo.cfg geo.cfg.levels v) x := by
  intro v
  induction v with
  | zero => intro x hx; exact Or.inl (top_base_prov geo F words (Nat.zero_le _) x hx)
  | succ v ih =>
    intro x hx
    by_cases hv : geo.cfg.seed geo.cfg.levels < v + 1
    · rw [top_table_eqFor geo F words hv] at hx
      refine topReference_P
        (P := Supplied tr (geo.cfg.seed 1) (time geo.cfg geo.cfg.levels (v + 1))) _ _ _ _ ?_ x hx
      intro y hy
      rcases List.mem_append.1 hy with h | h
      · rw [finishInputsAt_eqFor geo, fin_aAll] at h
        refine tpReference_P
          (P := Supplied tr (geo.cfg.seed 1) (time geo.cfg geo.cfg.levels (v + 1))) _ _ _ _ ?_ y h
        intro z hz
        rw [prep_aAll, Nat.add_sub_cancel] at hz
        exact supplied_mono (OnlineCorrectnessProof.time_mono _ _ (by omega)) (ih z hz)
      · rw [finishInputsAt_eqFor geo, fin_bAll] at h
        unfold carryOf at h
        have hL2 := F.levels2
        obtain ⟨i, hi, hm⟩ :=
          low_prov geo F hT words (geo.cfg.levels - 1) (by omega) (by omega) _ y h
        refine Or.inr ⟨i, ?_, hm⟩
        rwa [OnlineCorrectnessProof.time_carry F (ℓ := geo.cfg.levels - 1) (by omega) (by omega),
          Nat.sub_add_cancel (by omega)] at hi
    · exact Or.inl (top_base_prov geo F words (by omega) x hx)

/-- Every record of a table `(ℓ, v)`, `1 ≤ ℓ ≤ L`, is supplied by time `time ℓ v`. -/
theorem table_prov {ℓ v : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ ≤ geo.cfg.levels) :
    ∀ x ∈ (table geo.cfg geo.shapes tr words ℓ v).records,
      Supplied tr (geo.cfg.seed 1) (time geo.cfg ℓ v) x := by
  intro x hx
  rcases Nat.lt_or_ge ℓ geo.cfg.levels with hl | hl
  · exact Or.inr (low_prov geo F hT words ℓ h1 hl v x hx)
  · obtain rfl : ℓ = geo.cfg.levels := by omega
    exact top_prov geo F hT words v x hx

end prov

/-! ### The selected record -/

theorem foundMemFor (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct) {N : Nat}
    (g : OnlineGeom) (run : OnlineBatch.BatchRun) (S : Schedule) (m : Nat)
    (hgeom : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1) (hE : 0 < g.unitEntries)
    (hT : TracePremises geo.cfg N (OnlineBatch.traceOf g run))
    (hS : SchedulePremises geo.cfg S (OnlineBatch.slots run).length m)
    (words : Words) (dummy : Nat → Nat → Nat) (t : Nat) (s : OnlineBatch.Slot) (f : Rec)
    (hs : (OnlineBatch.slots run)[t]? = some s)
    (hf : (Probe.batch geo.cfg geo.shapes g run S words dummy t).found = some f) :
    f.key = s.record.key ∧
      f ∈ run.init ++ ((OnlineBatch.slots run).take t).map OnlineBatch.Slot.record := by
  obtain ⟨o, ho, -, -⟩ := slot_inv run hs
  have hop : s.op ≤ run.ops.length := (List.getElem?_eq_some_iff.1 ho).1.le
  have htn : t < (OnlineBatch.slots run).length := (List.getElem?_eq_some_iff.1 hs).1
  have hJt : fs run s.op ≤ t := fs_le run hs
  have hhist := slots_history_split run hs
  -- stored records at the chunk start are earlier slot records
  have hreq : ∀ x ∈ requesterRecords (OnlineBatch.stateAt g run s.op),
      x ∈ run.init ++ ((OnlineBatch.slots run).take t).map OnlineBatch.Slot.record := by
    intro x hx
    rw [hhist]
    exact List.mem_append_right _ (List.mem_append_left _ (requester_sub g run s.op x hx))
  -- the earlier lanes of the chunk
  have hearly : ∀ x ∈ Probe.earlier run s,
      x ∈ run.init ++ ((OnlineBatch.slots run).take t).map OnlineBatch.Slot.record := by
    intro x hx
    rw [hhist]
    exact List.mem_append_right _ (List.mem_append_right _ hx)
  -- the dense records
  have hdense : ∀ x ∈ OnlineBatch.denseRecords geo.cfg g run S t,
      x ∈ run.init ++ ((OnlineBatch.slots run).take t).map OnlineBatch.Slot.record := by
    intro x hx
    unfold OnlineBatch.denseRecords at hx
    rw [hs] at hx
    apply hreq
    unfold requesterRecords
    rcases List.mem_append.1 hx with h | h
    · obtain ⟨B, hB, hr⟩ := List.mem_flatMap.1 h
      exact List.mem_append_left _ (List.mem_flatMap.2 ⟨B, List.mem_of_mem_drop hB, hr⟩)
    · exact List.mem_append_right _ h
  -- the plan's tables
  have hJ : OnlineBatch.chunkStart (OnlineBatch.widths run) t = fs run s.op := chunkStart_slot run hs
  have hJn : fs run s.op < (OnlineBatch.slots run).length := lt_of_le_of_lt hJt htn
  have htable : ∀ c ∈ (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables,
      ∀ x ∈ (table geo.cfg geo.shapes (OnlineBatch.traceOf g run) words c.1 c.2).records,
        x ∈ run.init ++ ((OnlineBatch.slots run).take t).map OnlineBatch.Slot.record := by
    intro c hc x hx
    simp only [OnlineBatch.slotSchedule, hJ] at hc
    obtain ⟨hc1, hcL, -⟩ := hS.coords _ hJn c hc
    obtain ⟨hseed, hcons⟩ := hS.consumed _ hJn
    have hcp := cp_pos F (ℓ := 1) le_rfl (by have := F.levels2; omega)
    have hwe := (tiles_bounds (hS.tile _ hJn) c hc).2.2
    simp only [we, window_snd] at hwe
    rw [← OnlineCorrectnessProof.time_cp] at hwe
    have htime : time geo.cfg c.1 c.2 ≤ (S (fs run s.op)).consumed :=
      Nat.le_of_mul_le_mul_right hwe hcp
    rcases table_prov geo F hT words hc1 hcL x hx with hi | ⟨i, hi, hm⟩
    · exact List.mem_append_left _ hi
    · -- the unit is frozen at the chunk start
      have hI := inv_stateAt g run hE s.op hop
      have hfz := consumed_frozen hgeom hE hI.len hI.cur hseed (by simpa [pos] using hcons)
      have hpart := requester_partition g run s.op _ hop hfz
      apply hreq
      rw [← hpart]
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨i, ?_, hm⟩))
      rw [List.mem_range'_1]
      omega
  -- the cascade
  unfold Probe.batch at hf
  rw [hs] at hf
  dsimp only at hf
  split_ifs at hf with hp
  · unfold Probe.hierarchy at hf
    rcases cascade_mem _ _ _ _ _ _ _ f hf with hi | ⟨c, hc, hm, hk⟩
    · rcases orElse_eq_some hi with h | h
      · exact ⟨latest_some_key h, hearly f (latest_some_mem h)⟩
      · exact ⟨latest_some_key h, hdense f (latest_some_mem h)⟩
    · exact ⟨hk, htable c hc f hm⟩

/-- Numeric trace premises from membership in a finite universe. -/
theorem tracePremises_of_universe {cfg : Config} {U : Finset LogicalKey} {tr : Trace}
    (h : UniverseTracePremises cfg U tr) : TracePremises cfg (U.sup LogicalKey.toNat + 1) tr where
  nodup := h.nodup
  load := h.load
  keys i x hx := Nat.lt_succ_of_le (Finset.le_sup (f := LogicalKey.toNat) (h.keys i x hx))
  initNodup := h.initNodup
  initKeys x hx := Nat.lt_succ_of_le (Finset.le_sup (f := LogicalKey.toNat) (h.initKeys x hx))

end RebuildBound.AdaptiveFoundMemProof

open RebuildBound.AdaptiveFoundMemProof in
/-- **BatchFoundMem31**: the record a lane selects, under any words, is a
supplied record of its key, from the initialization or an earlier slot. -/
theorem RebuildBound.BatchFoundMem31 : RebuildBound.Spec.BatchFoundMem31_statement := by
  intro h _ U g run S m hgeom hE _ hUT hS words dummy t s f hs hf
  exact foundMemFor (RebuildBound.Spec.geometry31.chunk h)
    (RebuildBound.HierarchyLawsChunks31Proof.lowFacts_horizon
      RebuildBound.HierarchyInvariant31Proof.lowFacts (h * 2 ^ 32))
    g run S m hgeom hE (tracePremises_of_universe hUT) hS words dummy t s f hs hf
