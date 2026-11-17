import RebuildBound.Spec.AdaptiveSteps

/-!
# Package AdaptiveReplay

Deterministic facts about the adaptive
interaction (`Spec/Model/Adaptive.lean`):

* `ReplayShape`: a replayed run has the shape's widths, probe pattern, slot
  count, initialization input and flag, and its records are client records.
* `AdaptiveReplayStep`: from row causality, the realized run is the replay of
  the transcript, the transcript is the realized run's view, and the
  transcript is `t` exactly when the replay of `t` has view `t`.
* `AdaptiveConstantStep`: the adaptive model specializes to fixed runs.
* `AdaptiveAdmissibleStep`: from the requester's trace premises, the adaptive
  setting of any client whose keys lie in `U`.

The interaction is a left fold of `issue`. Two invariants carry it: the rows
only grow (`fold_rows`), and every row is the `touched` row of the operations
issued so far (`fold_inv`). The replayed operations follow from the first,
the transcript-as-view from the second and row causality.
-/

namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online Model.Adaptive

namespace AdaptiveReplayProof

/-! ### Slots of a run -/

theorem flatMap_zipIdx_fst {α β : Type} (l : List α) (g : α → List β) :
    (l.zipIdx.flatMap fun p => g p.1) = l.flatMap g := by
  rw [List.flatMap_def, List.flatMap_def]
  congr 1
  have : (l.zipIdx.map fun p => g p.1) = (l.zipIdx.map Prod.fst).map g := by
    rw [List.map_map]; rfl
  rw [this, List.zipIdx_map_fst]

theorem slots_map {β : Type} (run : OnlineBatch.BatchRun) (f : Rec × Bool → β) :
    (OnlineBatch.slots run).map (fun s => f (s.record, s.probes)) =
      run.ops.flatMap fun o => o.lanes.map f := by
  unfold OnlineBatch.slots
  rw [List.map_flatMap]
  simp only [List.map_map]
  have : ∀ o : OnlineBatch.Op × Nat,
      (List.map ((fun s : OnlineBatch.Slot => f (s.record, s.probes)) ∘
        fun rl : (Rec × Bool) × Nat => (⟨o.2, rl.2, rl.1.1, rl.1.2⟩ : OnlineBatch.Slot))
          o.1.lanes.zipIdx) =
      o.1.lanes.map f := by
    intro o
    have h2 : ((fun s : OnlineBatch.Slot => f (s.record, s.probes)) ∘
        fun rl : (Rec × Bool) × Nat => (⟨o.2, rl.2, rl.1.1, rl.1.2⟩ : OnlineBatch.Slot)) =
        f ∘ Prod.fst := by funext rl; rfl
    rw [h2, ← List.map_map, List.zipIdx_map_fst]
  simp only [this]
  exact flatMap_zipIdx_fst run.ops (fun o => o.lanes.map f)

theorem slots_length (run : OnlineBatch.BatchRun) :
    (OnlineBatch.slots run).length = (run.ops.map fun o => o.lanes.length).sum := by
  unfold OnlineBatch.slots
  rw [List.length_flatMap]
  congr 1
  have : ((fun a : OnlineBatch.Op × Nat =>
      (a.1.lanes.zipIdx.map fun rl => (⟨a.2, rl.2, rl.1.1, rl.1.2⟩ : OnlineBatch.Slot)).length)) =
      (fun o : OnlineBatch.Op => o.lanes.length) ∘ Prod.fst := by
    funext a; simp
  rw [this, ← List.map_map, List.zipIdx_map_fst]

/-! ### Operations of a kind -/

theorem op_lanes_length (k : Kind) (rec : Nat → Rec) : (k.op rec).lanes.length = k.width := by
  cases k <;> simp [Kind.op, Kind.width, OnlineBatch.Op.lanes]

theorem op_lanes_snd (k : Kind) (rec : Nat → Rec) :
    (k.op rec).lanes.map Prod.snd = List.replicate k.width k.probes := by
  cases k <;> simp [Kind.op, Kind.width, Kind.probes, OnlineBatch.Op.lanes]
  rename_i w
  have : (Prod.snd ∘ (fun r => (r, true)) ∘ rec : Nat → Bool) = fun _ => true := rfl
  rw [this, List.map_const', List.length_range]

theorem op_lanes_rec (k : Kind) (rec : Nat → Rec) :
    ∀ x ∈ (k.op rec).lanes, ∃ i, x.1 = rec i := by
  cases k <;> simp [Kind.op, OnlineBatch.Op.lanes]

theorem replayOps_map {β : Type} {n m : Nat} (C : Client m) (t : Fin n → Fin m → Nat)
    (f : OnlineBatch.Op → β) (g : Kind → β) (hfg : ∀ k rec, f (k.op rec) = g k) :
    ∀ ks s, (replayOps C t ks s).map f = ks.map g := by
  intro ks; induction ks with
  | nil => intro s; rfl
  | cons k ks ih => intro s; simp [replayOps, hfg, ih]

/-! ### Rows read from a candidate transcript -/

theorem getD_eq_getElem' {α : Type} {l : List α} {d : α} {r : Nat} (h : r < l.length) :
    l.getD r d = l[r] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem rowsOf_length {n m : Nat} (t : Fin n → Fin m → Nat) (s : Nat) :
    (rowsOf t s).length = s := by
  simp [rowsOf]

theorem rowsOf_add {n m : Nat} (t : Fin n → Fin m → Nat) (s w : Nat) :
    rowsOf t (s + w) = rowsOf t s ++ (List.range w).map
      (fun l (i : Fin m) => if h : s + l < n then t ⟨s + l, h⟩ i else 0) := by
  simp [rowsOf, List.range_add, List.map_append, List.map_map]

/-- A client that reads only how many rows it has seen issues the same
operations on every candidate transcript. -/
theorem replayOps_const {n m : Nat} (C : Client m)
    (hC : ∀ rows rows' : List (Fin m → Nat), rows.length = rows'.length → C rows = C rows')
    (t t' : Fin n → Fin m → Nat) :
    ∀ ks s, replayOps C t ks s = replayOps C t' ks s := by
  intro ks; induction ks with
  | nil => intro s; rfl
  | cons k ks ih =>
    intro s
    simp only [replayOps]
    rw [hC (rowsOf t s) (rowsOf t' s) (by simp [rowsOf_length]), ih]

/-! ### The interaction fold -/

section Fold

variable (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat}
  (a : AdaptiveRun m) (words : Words) (dummy : Nat → Nat → Nat)

theorem issue_eq (ops0 : List OnlineBatch.Op) (rows0 : List (Fin m → Nat)) (k : Kind) :
    issue cfg sh g S a words dummy (ops0, rows0) k =
      (ops0 ++ [k.op (a.client rows0)], rows0 ++ (List.range k.width).map fun l (i : Fin m) =>
        OnlineBatch.touched cfg sh g ⟨ops0 ++ [k.op (a.client rows0)], a.init, a.unsh⟩ S words
          dummy (rows0.length + l) i) := rfl

/-- The rows only grow, by one row per lane. -/
theorem fold_rows : ∀ (ks : List Kind) (acc : List OnlineBatch.Op × List (Fin m → Nat)),
    ∃ rest, (ks.foldl (issue cfg sh g S a words dummy) acc).2 = acc.2 ++ rest ∧
      rest.length = (ks.map Kind.width).sum := by
  intro ks
  induction ks with
  | nil => intro acc; exact ⟨[], by simp, rfl⟩
  | cons k ks ih =>
    intro acc
    obtain ⟨ops0, rows0⟩ := acc
    obtain ⟨rest, h1, h2⟩ := ih (issue cfg sh g S a words dummy (ops0, rows0) k)
    refine ⟨(List.range k.width).map (fun l (i : Fin m) =>
        OnlineBatch.touched cfg sh g ⟨ops0 ++ [k.op (a.client rows0)], a.init, a.unsh⟩ S words
          dummy (rows0.length + l) i) ++ rest, ?_, ?_⟩
    · rw [List.foldl_cons, h1, issue_eq]
      simp
    · simp [h2]

/-- The operations issued are the client's operations on every candidate
transcript that agrees with the client's reads. -/
theorem fold_ops {n : Nat} (t : Fin n → Fin m → Nat) :
    ∀ (ks : List Kind) (ops0 : List OnlineBatch.Op) (rows0 : List (Fin m → Nat)),
      (∀ rows, rows <+: (ks.foldl (issue cfg sh g S a words dummy) (ops0, rows0)).2 →
        rows0 <+: rows → a.client rows = a.client (rowsOf t rows.length)) →
      (ks.foldl (issue cfg sh g S a words dummy) (ops0, rows0)).1 =
        ops0 ++ replayOps a.client t ks rows0.length := by
  intro ks
  induction ks with
  | nil => intro ops0 rows0 _; simp [replayOps]
  | cons k ks ih =>
    intro ops0 rows0 H
    rw [List.foldl_cons, issue_eq] at H ⊢
    have hpre : rows0 <+: (ks.foldl (issue cfg sh g S a words dummy)
        (ops0 ++ [k.op (a.client rows0)], rows0 ++ (List.range k.width).map fun l (i : Fin m) =>
          OnlineBatch.touched cfg sh g ⟨ops0 ++ [k.op (a.client rows0)], a.init, a.unsh⟩ S words
            dummy (rows0.length + l) i)).2 := by
      obtain ⟨rest, h1, _⟩ := fold_rows cfg sh g S a words dummy ks
        (ops0 ++ [k.op (a.client rows0)], rows0 ++ (List.range k.width).map fun l (i : Fin m) =>
          OnlineBatch.touched cfg sh g ⟨ops0 ++ [k.op (a.client rows0)], a.init, a.unsh⟩ S words
            dummy (rows0.length + l) i)
      rw [h1]
      exact (List.prefix_append _ _).trans (List.prefix_append _ _)
    have hc : a.client rows0 = a.client (rowsOf t rows0.length) :=
      H rows0 hpre (List.prefix_refl _)
    rw [ih _ _ (fun rows h1 h2 => H rows h1 ((List.prefix_append _ _).trans h2))]
    simp only [replayOps, List.length_append, List.length_map, List.length_range,
      List.append_assoc, List.cons_append, List.nil_append]
    rw [hc]

/-- Every row of the interaction is the `touched` row, at its slot, of the
operations issued up to its own. -/
def RowsInv (ops : List OnlineBatch.Op) (rows : List (Fin m → Nat)) : Prop :=
  rows.length = (ops.map fun o => o.lanes.length).sum ∧
    ∀ r (hr : r < rows.length), ∃ j ≤ ops.length,
      r < (OnlineBatch.slots ⟨ops.take j, a.init, a.unsh⟩).length ∧
      ∀ i, rows[r] i =
        OnlineBatch.touched cfg sh g ⟨ops.take j, a.init, a.unsh⟩ S words dummy r i

theorem rowsInv_issue (ops0 : List OnlineBatch.Op) (rows0 : List (Fin m → Nat)) (k : Kind)
    (h : RowsInv cfg sh g S a words dummy ops0 rows0) :
    RowsInv cfg sh g S a words dummy (issue cfg sh g S a words dummy (ops0, rows0) k).1
      (issue cfg sh g S a words dummy (ops0, rows0) k).2 := by
  obtain ⟨hlen, hrow⟩ := h
  rw [issue_eq]
  refine ⟨?_, ?_⟩
  · simp [hlen, op_lanes_length]
  · intro r hr
    simp only [List.length_append, List.length_map, List.length_range] at hr
    by_cases hlt : r < rows0.length
    · obtain ⟨j, hj, hs, hi⟩ := hrow r hlt
      have htake : (ops0 ++ [k.op (a.client rows0)]).take j = ops0.take j :=
        List.take_append_of_le_length hj
      refine ⟨j, by simp only [List.length_append, List.length_singleton]; omega,
        by rw [htake]; exact hs, fun i => ?_⟩
      rw [htake, List.getElem_append_left hlt]
      exact hi i
    · refine ⟨ops0.length + 1, by simp, ?_, fun i => ?_⟩
      · have htake : (ops0 ++ [k.op (a.client rows0)]).take (ops0.length + 1) =
            ops0 ++ [k.op (a.client rows0)] := List.take_of_length_le (by simp)
        rw [htake, slots_length]
        simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, op_lanes_length, ← hlen]
        omega
      · have htake : (ops0 ++ [k.op (a.client rows0)]).take (ops0.length + 1) =
            ops0 ++ [k.op (a.client rows0)] := List.take_of_length_le (by simp)
        rw [htake, List.getElem_append_right (Nat.le_of_not_lt hlt)]
        simp only [List.getElem_map, List.getElem_range]
        have hr' : rows0.length + (r - rows0.length) = r := by omega
        rw [hr']

theorem rowsInv_fold : ∀ (ks : List Kind) (ops0 : List OnlineBatch.Op)
    (rows0 : List (Fin m → Nat)), RowsInv cfg sh g S a words dummy ops0 rows0 →
    RowsInv cfg sh g S a words dummy (ks.foldl (issue cfg sh g S a words dummy) (ops0, rows0)).1
      (ks.foldl (issue cfg sh g S a words dummy) (ops0, rows0)).2 := by
  intro ks
  induction ks with
  | nil => intro ops0 rows0 h; exact h
  | cons k ks ih =>
    intro ops0 rows0 h
    rw [List.foldl_cons]
    exact ih _ _ (rowsInv_issue cfg sh g S a words dummy ops0 rows0 k h)

/-- The interaction's rows: one per slot of the shape. -/
theorem interact_rows_length :
    (interact cfg sh g S a words dummy).2.length = slotCount a.shape := by
  obtain ⟨rest, h1, h2⟩ := fold_rows cfg sh g S a words dummy a.shape ([], [])
  unfold interact
  rw [h1]
  simp [h2, slotCount, shapeWidths]

theorem interact_rowsInv :
    RowsInv cfg sh g S a words dummy (interact cfg sh g S a words dummy).1
      (interact cfg sh g S a words dummy).2 :=
  rowsInv_fold cfg sh g S a words dummy a.shape [] [] ⟨by simp, fun r hr => by simp at hr⟩

/-- The interaction's operations are the client's on every candidate
transcript that agrees with the interaction's rows on the rows the client read. -/
theorem interact_ops {n : Nat} (t : Fin n → Fin m → Nat)
    (H : ∀ rows, rows <+: (interact cfg sh g S a words dummy).2 →
      a.client rows = a.client (rowsOf t rows.length)) :
    (interact cfg sh g S a words dummy).1 = replayOps a.client t a.shape 0 := by
  have := fold_ops cfg sh g S a words dummy t a.shape [] [] (fun rows h1 _ => H rows h1)
  simpa [interact] using this

end Fold

/-- The transcript's rows, read back, are the interaction's rows. -/
theorem rowsOf_transcript (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat}
    (a : AdaptiveRun m) (n : Nat) (hn : n = slotCount a.shape) (words : Words)
    (dummy : Nat → Nat → Nat) (rows : List (Fin m → Nat))
    (h : rows <+: (interact cfg sh g S a words dummy).2) :
    rows = rowsOf (transcript cfg sh g S a n words dummy) rows.length := by
  have hlenF := interact_rows_length cfg sh g S a words dummy
  have hle : rows.length ≤ (interact cfg sh g S a words dummy).2.length := h.length_le
  apply List.ext_getElem (by simp [rowsOf_length])
  intro r h1 h2
  have hrn : r < n := by omega
  have hrF : r < (interact cfg sh g S a words dummy).2.length := by omega
  simp only [rowsOf, List.getElem_map, List.getElem_range, hrn, ↓reduceDIte]
  funext i
  simp only [transcript]
  rw [getD_eq_getElem' hrF, h.getElem h1]

end AdaptiveReplayProof

open AdaptiveReplayProof

/-! ### ReplayShape -/

theorem ReplayShape : ReplayShape_statement := by
  intro m a n t
  have hw : OnlineBatch.widths (replay a t) = shapeWidths a.shape := by
    unfold OnlineBatch.widths shapeWidths replay
    exact replayOps_map _ _ _ _ (fun k rec => op_lanes_length k rec) _ _
  have hprobes : (OnlineBatch.slots (replay a t)).map OnlineBatch.Slot.probes =
      a.shape.flatMap fun k => List.replicate k.width k.probes := by
    have := slots_map (replay a t) Prod.snd
    simp only at this
    rw [this]
    simp only [replay]
    rw [List.flatMap_def, List.flatMap_def]
    congr 1
    exact replayOps_map _ _ _ _ (fun k rec => op_lanes_snd k rec) _ _
  refine ⟨hw, ?_, ?_, rfl, rfl, ?_⟩
  · funext s
    unfold OnlineBatch.probePattern shapePattern
    rw [← hprobes, List.getElem?_map]
  · have := congrArg List.length hprobes
    rw [List.length_map] at this
    rw [this, slotCount, List.length_flatMap]
    simp only [List.length_replicate]
    rfl
  · intro s hs
    have hmem : id (s.record, s.probes) ∈
        (OnlineBatch.slots (replay a t)).map fun s => id (s.record, s.probes) :=
      List.mem_map.2 ⟨s, hs, rfl⟩
    rw [slots_map (replay a t) id] at hmem
    simp only [List.map_id] at hmem
    obtain ⟨o, ho, hx⟩ := List.mem_flatMap.1 hmem
    simp only [replay] at ho
    suffices h : ∀ ks s0, o ∈ replayOps a.client t ks s0 → ∃ rows i, s.record = a.client rows i from
      h _ _ ho
    intro ks; induction ks with
    | nil => intro s0 h; simp [replayOps] at h
    | cons k ks ih =>
      intro s0 h
      simp only [replayOps, List.mem_cons] at h
      rcases h with rfl | h
      · obtain ⟨i, hi⟩ := op_lanes_rec k _ _ hx
        exact ⟨_, i, hi⟩
      · exact ih _ h

/-! ### The replay identity -/

namespace AdaptiveReplayProof

/-- The realized run is the replay of the transcript (no premise but the slot
count). -/
theorem realized_eq_replay (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat}
    (a : AdaptiveRun m) (n : Nat) (hn : n = slotCount a.shape) (words : Words)
    (dummy : Nat → Nat → Nat) :
    realized cfg sh g S a words dummy = replay a (transcript cfg sh g S a n words dummy) := by
  have h := interact_ops cfg sh g S a words dummy (transcript cfg sh g S a n words dummy)
    (fun rows hr => congrArg a.client (rowsOf_transcript cfg sh g S a n hn words dummy rows hr))
  simp only [realized, replay, h]

/-- The transcript is the realized run's view, from row causality. -/
theorem transcript_eq_view (hRC : RowCausality_statement) (cfg : Config) (sh : Shapes)
    (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m) (n : Nat)
    (hn : n = slotCount a.shape)
    (hg : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1) (hE : 0 < g.unitEntries)
    (hS : SchedulePremises cfg S n m) (words : Words) (dummy : Nat → Nat → Nat) :
    transcript cfg sh g S a n words dummy =
      OnlineBatch.view cfg sh g (realized cfg sh g S a words dummy) S n m words dummy := by
  funext r i
  have hlenF := interact_rows_length cfg sh g S a words dummy
  have hrF : r.1 < (interact cfg sh g S a words dummy).2.length := by omega
  obtain ⟨_, hrow⟩ := interact_rowsInv cfg sh g S a words dummy
  obtain ⟨j, _, hs, hi⟩ := hrow r.1 hrF
  have hc := hRC cfg sh g (realized cfg sh g S a words dummy) S n m j words dummy r.1 i hg hE hS
    r.2 hs
  simp only [transcript, OnlineBatch.view]
  rw [getD_eq_getElem' hrF, hi i]
  exact hc

/-- The `←` direction of the replay identity, from row causality. -/
theorem replay_back (hRC : RowCausality_statement) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (S : Schedule) (m : Nat) (a : AdaptiveRun m) (n : Nat) (hn : n = slotCount a.shape)
    (hg : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1) (hE : 0 < g.unitEntries)
    (hS : SchedulePremises cfg S n m) (words : Words) (dummy : Nat → Nat → Nat)
    (t : Fin n → Fin m → Nat)
    (hV : OnlineBatch.view cfg sh g (replay a t) S n m words dummy = t) :
    transcript cfg sh g S a n words dummy = t := by
  set R := replay a t with hRdef
  have key : ∀ (ks : List Kind) (ops0 : List OnlineBatch.Op) (s : Nat),
      R.ops = ops0 ++ replayOps a.client t ks s →
      (ops0.map fun o => o.lanes.length).sum = s →
      s + (ks.map Kind.width).sum ≤ n →
      ks.foldl (issue cfg sh g S a words dummy) (ops0, rowsOf t s) =
        (ops0 ++ replayOps a.client t ks s, rowsOf t (s + (ks.map Kind.width).sum)) := by
    intro ks
    induction ks with
    | nil => intro ops0 s _ _ _; simp [replayOps]
    | cons k ks ih =>
      intro ops0 s hR hs hle
      simp only [List.foldl_cons, List.map_cons, List.sum_cons] at hle ⊢
      set op := k.op (a.client (rowsOf t s)) with hop
      have hrows : (rowsOf t s ++ (List.range k.width).map fun l (i : Fin m) =>
          OnlineBatch.touched cfg sh g ⟨ops0 ++ [op], a.init, a.unsh⟩ S words dummy
            ((rowsOf t s).length + l) i) = rowsOf t (s + k.width) := by
        rw [rowsOf_add, rowsOf_length]
        congr 1
        apply List.map_congr_left
        intro l hl
        rw [List.mem_range] at hl
        funext i
        have hlt : s + l < n := by omega
        simp only [hlt, ↓reduceDIte]
        have hpre : (⟨ops0 ++ [op], a.init, a.unsh⟩ : OnlineBatch.BatchRun) =
            ⟨R.ops.take (ops0.length + 1), R.init, R.unsh⟩ := by
          rw [hR]
          have h1 : List.take (ops0.length + 1) (ops0 ++ replayOps a.client t (k :: ks) s) =
              ops0 ++ [op] := by
            simp only [replayOps, hop]
            rw [List.take_append, List.take_of_length_le (by omega)]
            simp
          rw [h1, hRdef]; rfl
        rw [hpre, hRC cfg sh g R S n m (ops0.length + 1) words dummy (s + l) i hg hE hS hlt]
        · have := congrFun (congrFun hV ⟨s + l, hlt⟩) i
          simpa [OnlineBatch.view] using this
        · rw [← hpre, slots_length]
          simp only [List.map_append, List.sum_append, hs, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, hop, op_lanes_length]
          omega
      have hstep : issue cfg sh g S a words dummy (ops0, rowsOf t s) k =
          (ops0 ++ [op], rowsOf t (s + k.width)) := by
        rw [issue_eq, ← hrows]
      rw [hstep]
      have := ih (ops0 ++ [op]) (s + k.width) (by rw [hR]; simp [replayOps, hop])
        (by simp [hs, hop, op_lanes_length]) (by omega)
      rw [this]
      simp [replayOps, hop, Nat.add_assoc]
  have hall := key a.shape [] 0 (by simp [hRdef, replay]) (by simp)
    (by rw [hn]; simp [slotCount, shapeWidths])
  have hI : interact cfg sh g S a words dummy = (R.ops, rowsOf t n) := by
    unfold interact
    have h0 : (([] : List OnlineBatch.Op), ([] : List (Fin m → Nat))) = ([], rowsOf t 0) := by
      simp [rowsOf]
    rw [h0, hall]
    simp [hRdef, replay, hn, slotCount, shapeWidths]
  funext r i
  unfold transcript
  rw [hI]
  simp [rowsOf, r.2]

/-- The replay identity, from row causality alone. -/
theorem adaptiveReplay (hRC : RowCausality_statement) : AdaptiveReplay_statement := by
  intro cfg sh g S m a n hn hg hE hS words dummy
  have h1 := realized_eq_replay cfg sh g S a n hn words dummy
  have h2 := transcript_eq_view hRC cfg sh g S a n hn hg hE hS words dummy
  refine ⟨h1, h2, fun t => ⟨fun ht => ?_, replay_back hRC cfg sh g S m a n hn hg hE hS words dummy t⟩⟩
  subst ht
  rw [← h1, ← h2]

end AdaptiveReplayProof

theorem AdaptiveReplayStep : AdaptiveReplayStep_statement :=
  fun hRC _ => adaptiveReplay hRC

/-! ### AdaptiveConstant -/

namespace AdaptiveReplayProof

/-- The kind of an operation. -/
def kindOf : OnlineBatch.Op → Kind
  | .probe _ => .probe
  | .blind _ => .blind
  | .batch l => .chunk l.length

/-- The records of a list of operations, lane by lane. -/
def recsOf (ops : List OnlineBatch.Op) : List Rec := ops.flatMap fun o => o.lanes.map Prod.fst

theorem kindOf_width (o : OnlineBatch.Op) : (kindOf o).width = o.lanes.length := by
  cases o <;> simp [kindOf, Kind.width, OnlineBatch.Op.lanes]

theorem kindOf_op (o : OnlineBatch.Op) (pre rest : List Rec) :
    (kindOf o).op (fun i => ((pre ++ (o.lanes.map Prod.fst) ++ rest)[pre.length + i]?).getD
      default) = o := by
  cases o with
  | probe r => simp [kindOf, Kind.op, OnlineBatch.Op.lanes]
  | blind r => simp [kindOf, Kind.op, OnlineBatch.Op.lanes]
  | batch l =>
    simp only [kindOf, Kind.op, OnlineBatch.Op.lanes, List.map_map]
    congr 1
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [List.append_assoc, List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      rw [List.getElem?_append_left (by simp at h1 ⊢; omega)]
      simp at h1 ⊢
      simp [List.getElem?_eq_getElem h2]

theorem replayOps_recsOf (m n : Nat) (t : Fin n → Fin m → Nat) (all : List Rec) :
    ∀ (ops : List OnlineBatch.Op) (pre : List Rec), all = pre ++ recsOf ops →
      replayOps (fun rows i => (all[rows.length + i]?).getD default) t (ops.map kindOf)
        pre.length = ops := by
  intro ops
  induction ops with
  | nil => intro pre _; rfl
  | cons o os ih =>
    intro pre hall
    simp only [List.map_cons, replayOps]
    have hlen : (rowsOf t pre.length).length = pre.length := rowsOf_length t _
    rw [hlen]
    congr 1
    · have : all = pre ++ (o.lanes.map Prod.fst) ++ recsOf os := by
        rw [hall]; simp [recsOf]
      rw [this]; exact kindOf_op o pre (recsOf os)
    · have := ih (pre ++ o.lanes.map Prod.fst) (by rw [hall]; simp [recsOf])
      simpa [kindOf_width] using this

/-- Every fixed run is the replay of a client that reads only how many rows it
has seen. -/
theorem fixed_run_client : ∀ m n (run : OnlineBatch.BatchRun), ∃ a : AdaptiveRun m,
    (∀ rows rows' : List (Fin m → Nat), rows.length = rows'.length →
      a.client rows = a.client rows') ∧
    ∀ t : Fin n → Fin m → Nat, replay a t = run := by
  intro m n run
  refine ⟨⟨run.ops.map kindOf, run.init, run.unsh,
    fun rows i => ((recsOf run.ops)[rows.length + i]?).getD default⟩, ?_, ?_⟩
  · intro rows rows' h; simp only [h]
  · intro t
    have := replayOps_recsOf m n t (recsOf run.ops) run.ops [] (by simp)
    simp only [List.length_nil] at this
    simp only [replay]
    rw [this]

end AdaptiveReplayProof

theorem AdaptiveConstantStep : AdaptiveConstantStep_statement := by
  intro hRC hRS
  refine ⟨fun m a n t => ⟨(hRS m a n t).1.symm, (hRS m a n t).2.1.symm⟩, ?_, fixed_run_client⟩
  intro geo U g m a S n t₀ hC
  have hrep : ∀ t : Fin n → Fin m → Nat, replay a t = replay a t₀ := by
    intro t
    simp only [replay]
    rw [replayOps_const a.client hC t t₀]
  have hreal : ∀ words dummy, realized geo.cfg geo.shapes g S a words dummy = replay a t₀ := by
    intro words dummy
    have h := interact_ops geo.cfg geo.shapes g S a words dummy t₀
      (fun rows _ => hC _ _ (rowsOf_length t₀ _).symm)
    simp only [realized, replay, h]
  refine ⟨⟨fun ⟨hn, h⟩ => ⟨hn, h t₀⟩, fun ⟨hn, h⟩ => ⟨hn, fun t => by rw [hrep t]; exact h⟩⟩,
    fun words dummy => ⟨hreal words dummy, ?_, ?_⟩⟩
  · unfold AdaptiveFails
    rw [hreal words dummy]
  · intro ⟨hn, hset⟩
    obtain ⟨_, _, _, hprem, hS⟩ := hset t₀
    rw [transcript_eq_view hRC geo.cfg geo.shapes g S a n hn hprem.geom.1 hprem.geom.2 hS
      words dummy, hreal words dummy]

/-! ### AdaptiveAdmissible -/

theorem AdaptiveAdmissibleStep : AdaptiveAdmissibleStep_statement := by
  intro hRT hRS geo U g m a S hU hcard hg hE hhor hnodup hinit hkeys hunsh hS
  refine ⟨rfl, fun t => ?_⟩
  obtain ⟨_, _, hlen, hinit', _, hrec⟩ := hRS m a (slotCount a.shape) t
  have hslotkeys : ∀ s ∈ OnlineBatch.slots (replay a t), s.record.key ∈ U := by
    intro s hs
    obtain ⟨rows, i, h⟩ := hrec s hs
    rw [h]; exact hkeys rows i
  refine ⟨hU, hcard, hlen.ge, ⟨⟨hg, hE⟩, by rw [hlen]; exact hhor, hslotkeys, ?_, ?_⟩, hS⟩
  · exact hRT geo.cfg U g (replay a t) hg hE hslotkeys (by rw [hinit']; exact hnodup)
      (by rw [hinit']; exact hinit)
  · intro words o _ r _ hr
    have : (OnlineBatch.traceOf g (replay a t)).unsh r = false := hunsh r
    simp [earlyDrop, this] at hr

end RebuildBound
