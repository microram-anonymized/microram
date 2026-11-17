import RebuildBound.Proofs.BatchFresh.Slots
import RebuildBound.Proofs.OnlineFresh.Requester

/-!
# BatchFresh: where a slot's record sits in the requester

After the first `j` operations (`fs j` slots), the record of slot `t < fs j`
sits in the unit `⌊t / E⌋` (`E = unitEntries`), frozen or current, unless a
later slot before `fs j` has the same key (`inv_stateAt`). A batch clears its
lanes' keys from the current unit, then inserts them in order, a superseded
lane as `none`; a lane not superseded is placed real. Frozen units only grow
(`frozen_prefix`).
-/

namespace RebuildBound.BatchFreshProof

open RebuildBound.Model RebuildBound.Model.OnlineBatch
open RebuildBound.Model.Online (OnlineGeom)
open RebuildBound.OnlineFreshProof (Placed mem_clearKey)

/-- The key of slot `u`. -/
def slotKey (run : BatchRun) (u : Nat) : Option LogicalKey := (slots run)[u]?.map fun s => s.record.key

theorem slotKey_of {run : BatchRun} {u : Nat} {s : Slot} (h : (slots run)[u]? = some s) :
    slotKey run u = some s.record.key := by simp [slotKey, h]

theorem stateAt_zero (g : OnlineGeom) (run : BatchRun) : stateAt g run 0 = ⟨[], []⟩ := by
  simp [stateAt, Requester.run]

theorem stateAt_succ (g : OnlineGeom) (run : BatchRun) {j : Nat} {o : Op}
    (h : run.ops[j]? = some o) :
    stateAt g run (j + 1) = Requester.step g.unitEntries (stateAt g run j) o.requester := by
  unfold stateAt Requester.run
  simp only [List.take_add_one, h, Option.toList_some, List.map_append, List.foldl_append,
    List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]

/-- A fold with an invariant indexed by the number of elements processed. -/
theorem foldl_idx {α β : Type} (f : β → α → β) (P : Nat → β → Prop) :
    ∀ (xs : List α) (k : Nat) (s : β), P k s →
      (∀ i (h : i < xs.length) s, P (k + i) s → P (k + i + 1) (f s xs[i])) →
      P (k + xs.length) (xs.foldl f s)
  | [], k, s, h, _ => by simpa using h
  | x :: xs, k, s, h, hf => by
    have h1 : P (k + 1) (f s x) := by
      have := hf 0 (by simp) s (by simpa using h)
      exact this
    have := foldl_idx f P xs (k + 1) (f s x) h1 (fun i hi s' hs' => by
      have := hf (i + 1) (by simp; omega) s' (by rw [show k + (i + 1) = k + 1 + i by omega]; exact hs')
      rw [show k + (i + 1) + 1 = k + 1 + i + 1 by omega] at this
      exact this)
    rw [List.foldl_cons, List.length_cons, show k + (xs.length + 1) = k + 1 + xs.length by omega]
    exact this

/-! ### One insert -/

section insert
variable {E : Nat}

theorem insert_len (st : Requester.State) (v : Option Rec) (hc : st.current.length < E) :
    (Requester.insert E st v).frozen.length * E + (Requester.insert E st v).current.length =
      st.frozen.length * E + st.current.length + 1 := by
  unfold Requester.insert
  split_ifs with h
  · simp only [List.length_append, List.length_singleton, List.length_nil] at h ⊢
    rw [Nat.succ_mul]; omega
  · simp only [List.length_append, List.length_singleton]; omega

theorem insert_cur (st : Requester.State) (v : Option Rec) (hE : 0 < E)
    (_hc : st.current.length < E) : (Requester.insert E st v).current.length < E := by
  unfold Requester.insert
  split_ifs with h
  · simpa using hE
  · simp only [List.length_append, List.length_singleton] at h ⊢; omega

theorem insert_old (st : Requester.State) (v : Option Rec) {t : Nat} {r : Rec}
    (hc : st.current.length < E) (ht : t < st.frozen.length * E + st.current.length)
    (hp : Placed E st t r) : Placed E (Requester.insert E st v) t r := by
  unfold Requester.insert
  split_ifs with h
  · simp only [List.length_append, List.length_singleton] at h
    left
    rcases hp with ⟨u, hu, h1, h2, h3⟩ | ⟨h1, h2⟩
    · exact ⟨u, by simp; omega, h1, h2, by rw [List.getElem_append_left hu]; exact h3⟩
    · refine ⟨st.frozen.length, by simp, h1, by rw [Nat.succ_mul]; omega, ?_⟩
      simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton]
      exact List.mem_append_left _ h2
  · rcases hp with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, List.mem_append_left _ h2⟩

theorem insert_new (st : Requester.State) (r : Rec) (hc : st.current.length < E) :
    Placed E (Requester.insert E st (some r)) (st.frozen.length * E + st.current.length) r := by
  unfold Requester.insert
  split_ifs with h
  · simp only [List.length_append, List.length_singleton] at h
    left
    refine ⟨st.frozen.length, by simp, by omega, by rw [Nat.succ_mul]; omega, ?_⟩
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · exact Or.inr ⟨by dsimp only; omega, List.mem_append_right _ (List.mem_singleton_self _)⟩

theorem insert_prefix (st : Requester.State) (v : Option Rec) :
    st.frozen <+: (Requester.insert E st v).frozen := by
  unfold Requester.insert
  split_ifs
  · exact List.prefix_append _ _
  · exact List.prefix_refl _

/-- Changing only the current unit, keeping the record. -/
theorem placed_cur {st : Requester.State} {f : Bucket → Bucket} {t : Nat} {r : Rec}
    (hp : Placed E st t r) (hf : some r ∈ st.current → some r ∈ f st.current) :
    Placed E ⟨st.frozen, f st.current⟩ t r := by
  rcases hp with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, hf h2⟩

end insert

theorem mem_foldl_clear (L : List Rec) :
    ∀ (cur : Bucket) {x : Rec}, some x ∈ cur → (∀ y ∈ L, x.key ≠ y.key) →
      some x ∈ L.foldl (fun u r => Requester.clearKey r.key u) cur := by
  induction L with
  | nil => intro cur x h _; exact h
  | cons a L ih =>
    intro cur x h hne
    exact ih _ (mem_clearKey h (hne a (by simp))) (fun y hy => hne y (List.mem_cons_of_mem _ hy))

theorem length_foldl_clear (L : List Rec) :
    ∀ cur : Bucket, (L.foldl (fun u r => Requester.clearKey r.key u) cur).length = cur.length := by
  induction L with
  | nil => intro cur; rfl
  | cons a L ih => intro cur; rw [List.foldl_cons, ih]; simp [Requester.clearKey]

theorem superseded_true {lanes : List Rec} {i : Nat} (hi : i < lanes.length)
    (h : Requester.superseded lanes i lanes[i] = true) :
    ∃ l2, ∃ h2 : l2 < lanes.length, i < l2 ∧ lanes[l2].key = lanes[i].key := by
  unfold Requester.superseded at h
  obtain ⟨x, hx, hk⟩ := List.any_eq_true.1 h
  obtain ⟨n, hn, e⟩ := List.mem_iff_getElem.1 hx
  rw [List.getElem_drop] at e
  simp only [List.length_drop] at hn
  refine ⟨i + 1 + n, by omega, by omega, ?_⟩
  rw [e]; simpa using hk

/-! ### The invariant -/

/-- The requester invariant after `j` operations. -/
structure Inv (E : Nat) (run : BatchRun) (j : Nat) (st : Requester.State) : Prop where
  len : st.frozen.length * E + st.current.length = fs run j
  cur : st.current.length < E
  placed : ∀ t s, t < fs run j → (slots run)[t]? = some s →
    (∀ u, t < u → u < fs run j → slotKey run u ≠ some s.record.key) → Placed E st t s.record

theorem inv_access {E : Nat} {run : BatchRun} {j : Nat} {st : Requester.State} {o : Op} {r : Rec}
    {b : Bool} (hE : 0 < E) (hI : Inv E run j st) (ho : run.ops[j]? = some o)
    (hl : o.lanes = [(r, b)]) :
    Inv E run (j + 1) (Requester.step E st (.access r true)) := by
  obtain ⟨hlen, hcur, hpl⟩ := hI
  have hfs : fs run (j + 1) = fs run j + 1 := by rw [fs_succ run ho, hl]; rfl
  have hat : (slots run)[fs run j]? = some ⟨j, 0, r, b⟩ := by
    have := slot_at run ho (l := 0) (rp := (r, b)) (by rw [hl]; rfl)
    simpa using this
  have hclen : (Requester.clearKey r.key st.current).length = st.current.length := by
    simp [Requester.clearKey]
  simp only [Requester.step, ite_true]
  refine ⟨?_, ?_, ?_⟩
  · rw [insert_len _ _ (by dsimp only; omega)]; dsimp only; omega
  · exact insert_cur _ _ hE (by dsimp only; omega)
  · intro t s ht hs hno
    rw [hfs] at ht hno
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
    · have hp := hpl t s ht hs (fun u h1 h2 => hno u h1 (by omega))
      have hne : s.record.key ≠ r.key := by
        intro e
        exact hno (fs run j) ht (by omega) (by rw [slotKey_of hat, e])
      refine insert_old _ _ (by dsimp only; omega) (by dsimp only; omega) ?_
      exact placed_cur hp (fun h => mem_clearKey h hne)
    · subst ht
      rw [hat] at hs
      cases hs
      have := insert_new (E := E) ⟨st.frozen, Requester.clearKey r.key st.current⟩ r
        (by dsimp only; omega)
      dsimp only at this
      rw [hclen, hlen] at this
      exact this

/-- The invariant inside a batch, after its first `i` lanes. -/
def BInv (E : Nat) (run : BatchRun) (j i : Nat) (σ : Requester.State) : Prop :=
  σ.frozen.length * E + σ.current.length = fs run j + i ∧ σ.current.length < E ∧
    ∀ t s, t < fs run j + i → (slots run)[t]? = some s →
      (∀ u, t < u → u < fs run (j + 1) → slotKey run u ≠ some s.record.key) →
      Placed E σ t s.record

/-- One lane of a batch step. -/
def bstep (E : Nat) (lanes : List Rec) (s : Requester.State) (ri : Rec × Nat) : Requester.State :=
  Requester.insert E s (if Requester.superseded lanes ri.2 ri.1 then none else some ri.1)

theorem step_batch (E : Nat) (st : Requester.State) (lanes : List Rec) :
    Requester.step E st (.batch lanes) = lanes.zipIdx.foldl (bstep E lanes)
      ⟨st.frozen, lanes.foldl (fun u r => Requester.clearKey r.key u) st.current⟩ := rfl

theorem inv_batch {E : Nat} {run : BatchRun} {j : Nat} {st : Requester.State} {lanes : List Rec}
    (hE : 0 < E) (hI : Inv E run j st) (ho : run.ops[j]? = some (.batch lanes)) :
    Inv E run (j + 1) (Requester.step E st (.batch lanes)) := by
  obtain ⟨hlen, hcur, hpl⟩ := hI
  have hfs : fs run (j + 1) = fs run j + lanes.length := by
    rw [fs_succ run ho]; simp [Op.lanes]
  have hat : ∀ l (h : l < lanes.length), (slots run)[fs run j + l]? = some ⟨j, l, lanes[l], true⟩ := by
    intro l h
    exact slot_at run ho (rp := (lanes[l], true)) (by simp [Op.lanes, h])
  have h0 : BInv E run j 0 ⟨st.frozen, lanes.foldl (fun u r => Requester.clearKey r.key u) st.current⟩ := by
    refine ⟨?_, ?_, ?_⟩
    · dsimp only; rw [length_foldl_clear]; omega
    · dsimp only; rw [length_foldl_clear]; exact hcur
    · intro t s ht hs hno
      have ht' : t < fs run j := by omega
      have hp := hpl t s ht' hs (fun u h1 h2 => hno u h1 (by rw [hfs]; omega))
      refine placed_cur (f := fun c => lanes.foldl (fun u r => Requester.clearKey r.key u) c) hp
        (fun h => mem_foldl_clear lanes _ h ?_)
      intro y hy e
      obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.1 hy
      exact hno (fs run j + l) (by omega) (by rw [hfs]; omega) (by rw [slotKey_of (hat l hl), e])
  have hstep : ∀ i (h : i < lanes.zipIdx.length) σ, BInv E run j (0 + i) σ →
      BInv E run j (0 + i + 1) (bstep E lanes σ lanes.zipIdx[i]) := by
    intro i hi σ hσ
    have hi' : i < lanes.length := by simpa using hi
    have hz : lanes.zipIdx[i] = (lanes[i], i) := by simp
    simp only [Nat.zero_add, hz, bstep] at hσ ⊢
    obtain ⟨hl1, hl2, hl3⟩ := hσ
    refine ⟨?_, insert_cur _ _ hE hl2, ?_⟩
    · rw [insert_len _ _ hl2]; omega
    · intro t s ht hs hno
      rcases Nat.lt_or_ge t (fs run j + i) with ht | ht
      · exact insert_old _ _ hl2 (by omega) (hl3 t s ht hs hno)
      · obtain rfl : t = fs run j + i := by omega
        rw [hat i hi'] at hs
        cases hs
        have hsup : Requester.superseded lanes i lanes[i] = false := by
          cases e : Requester.superseded lanes i lanes[i]
          · rfl
          · obtain ⟨l2, h2, hlt, hk⟩ := superseded_true hi' e
            exact absurd (by rw [slotKey_of (hat l2 h2), hk])
              (hno (fs run j + l2) (by omega) (by rw [hfs]; omega))
        rw [hsup, if_neg (by simp)]
        have := insert_new (E := E) σ lanes[i] hl2
        rw [hl1] at this
        exact this
  rw [step_batch]
  have := foldl_idx (bstep E lanes) (BInv E run j) lanes.zipIdx 0 _ h0 hstep
  simp only [Nat.zero_add, List.length_zipIdx] at this
  obtain ⟨hl1, hl2, hl3⟩ := this
  refine ⟨by rw [hfs]; exact hl1, hl2, ?_⟩
  intro t s ht hs hno
  exact hl3 t s (by rw [← hfs]; exact ht) hs hno

theorem inv_stateAt (g : OnlineGeom) (run : BatchRun) (hE : 0 < g.unitEntries) :
    ∀ j, j ≤ run.ops.length → Inv g.unitEntries run j (stateAt g run j) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [stateAt_zero]
    exact ⟨by simp [fs_zero], by simpa using hE, fun t _ h => by rw [fs_zero] at h; omega⟩
  | succ j ih =>
    intro hj
    have hjl : j < run.ops.length := hj
    have ho : run.ops[j]? = some run.ops[j] := List.getElem?_eq_getElem hjl
    rw [stateAt_succ g run ho]
    have hI := ih (Nat.le_of_lt hjl)
    generalize run.ops[j] = o at ho
    cases o with
    | probe r => exact inv_access hE hI ho rfl
    | blind r => exact inv_access hE hI ho rfl
    | batch lanes => exact inv_batch hE hI ho

theorem step_prefix (E : Nat) (st : Requester.State) (op : Requester.Op) :
    st.frozen <+: (Requester.step E st op).frozen := by
  cases op with
  | access r real => exact insert_prefix (E := E) ⟨st.frozen, Requester.clearKey r.key st.current⟩ _
  | batch lanes =>
    rw [step_batch]
    exact foldl_idx (bstep E lanes) (fun _ σ => st.frozen <+: σ.frozen) lanes.zipIdx 0
      ⟨st.frozen, lanes.foldl (fun u r => Requester.clearKey r.key u) st.current⟩ (List.prefix_refl _)
      (fun i _ σ h => h.trans (insert_prefix _ _))

theorem frozen_prefix (g : OnlineGeom) (run : BatchRun) {j : Nat} :
    ∀ j', j ≤ j' → j' ≤ run.ops.length → (stateAt g run j).frozen <+: (stateAt g run j').frozen := by
  intro j'
  induction j' with
  | zero => intro h _; rw [Nat.le_zero.1 h]
  | succ j' ih =>
    intro h hl
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with h' | h'
    · refine (ih (Nat.le_of_lt_succ h') (Nat.le_of_succ_le hl)).trans ?_
      rw [stateAt_succ g run (List.getElem?_eq_getElem hl)]
      exact step_prefix _ _ _
    · rw [h']

end RebuildBound.BatchFreshProof
