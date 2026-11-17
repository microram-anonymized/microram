import RebuildBound.Spec.Model.Online
import RebuildBound.Proofs.HierarchyInvariant.Low

/-!
# OnlineFresh: where an operation's record sits in the requester

After the first `j` operations, the record of operation `t < j` sits in the
unit `⌊t / E⌋` (`E = unitEntries`), frozen or current, unless a later
operation before `j` had the same key. Frozen units only grow.
-/

namespace RebuildBound.OnlineFreshProof

open RebuildBound.Model RebuildBound.Model.Online

/-- The key of operation `t`. -/
def keyAt (run : OnlineRun) (t : Nat) : Option LogicalKey := run.ops[t]?.map fun o => o.record.key

theorem stateAt_zero (g : OnlineGeom) (run : OnlineRun) : stateAt g run 0 = ⟨[], []⟩ := by
  simp [stateAt, Requester.run]

theorem stateAt_succ (g : OnlineGeom) (run : OnlineRun) {j : Nat} (hj : j < run.ops.length) :
    stateAt g run (j + 1) =
      Requester.step g.unitEntries (stateAt g run j) (.access run.ops[j].record true) := by
  unfold stateAt Requester.run
  simp only [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.map_append,
    List.foldl_append, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]

theorem mem_clearKey {k : LogicalKey} {cur : Bucket} {x : Rec} (h : some x ∈ cur) (hx : x.key ≠ k) :
    some x ∈ Requester.clearKey k cur := by
  unfold Requester.clearKey
  exact List.mem_map.2 ⟨some x, h, by simp [Option.filter, hx]⟩

/-- Operation `t`'s record `r` sits in a frozen unit `u` with `u E ≤ t < (u + 1) E`, or in
the current unit. -/
def Placed (E : Nat) (st : Requester.State) (t : Nat) (r : Rec) : Prop :=
  (∃ u, ∃ h : u < st.frozen.length, u * E ≤ t ∧ t < (u + 1) * E ∧ some r ∈ st.frozen[u]) ∨
    (st.frozen.length * E ≤ t ∧ some r ∈ st.current)

/-- The requester invariant after `j` operations. -/
structure Inv (E : Nat) (run : OnlineRun) (j : Nat) (st : Requester.State) : Prop where
  len : st.frozen.length * E + st.current.length = j
  cur : st.current.length < E
  placed : ∀ t o, t < j → run.ops[t]? = some o →
    (∀ u, t < u → u < j → keyAt run u ≠ some o.record.key) → Placed E st t o.record

theorem inv_stateAt (g : OnlineGeom) (run : OnlineRun) (hE : 0 < g.unitEntries) :
    ∀ j, j ≤ run.ops.length → Inv g.unitEntries run j (stateAt g run j) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [stateAt_zero]
    exact ⟨by simp, by simpa using hE, fun t _ h => absurd h (Nat.not_lt_zero t)⟩
  | succ j ih =>
    intro hj
    have hjl : j < run.ops.length := hj
    obtain ⟨hlen, hcur, hpl⟩ := ih (Nat.le_of_lt hjl)
    rw [stateAt_succ g run hjl]
    generalize hst : stateAt g run j = st at hlen hcur hpl
    generalize hr : run.ops[j] = op
    have hkey : keyAt run j = some op.record.key := by
      simp [keyAt, List.getElem?_eq_getElem hjl, hr]
    have hopj : run.ops[j]? = some op := by rw [List.getElem?_eq_getElem hjl, hr]
    have hclen : (Requester.clearKey op.record.key st.current).length = st.current.length := by
      simp [Requester.clearKey]
    -- the earlier operations' records, kept by the clear
    have hold : ∀ t o, t < j → run.ops[t]? = some o →
        (∀ u, t < u → u < j + 1 → keyAt run u ≠ some o.record.key) →
        (∃ u, ∃ h : u < st.frozen.length, u * g.unitEntries ≤ t ∧ t < (u + 1) * g.unitEntries ∧
          some o.record ∈ st.frozen[u]) ∨
        (st.frozen.length * g.unitEntries ≤ t ∧
          some o.record ∈ Requester.clearKey op.record.key st.current) := by
      intro t o ht ho hno
      have hne : op.record.key ≠ o.record.key := by
        intro e; exact hno j ht (Nat.lt_succ_self j) (by rw [hkey, e])
      rcases hpl t o ht ho (fun u h1 h2 => hno u h1 (Nat.lt_succ_of_lt h2)) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.1, mem_clearKey h.2 (Ne.symm hne)⟩
    dsimp only [Requester.step, Requester.insert]
    simp only [ite_true]
    split_ifs with hfz
    · -- the unit freezes
      simp only [List.length_append, List.length_singleton, hclen] at hfz
      have hc1 : st.current.length + 1 = g.unitEntries := by omega
      refine ⟨?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton, List.length_nil, Nat.add_zero,
          Nat.succ_mul]
        omega
      · simpa using hE
      · intro t o ht ho hno
        left
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
        · rcases hold t o ht ho hno with ⟨u, hu, h1, h2, h3⟩ | ⟨h1, h2⟩
          · refine ⟨u, by simp; omega, h1, h2, ?_⟩
            rw [List.getElem_append_left hu]; exact h3
          · refine ⟨st.frozen.length, by simp, h1, ?_, ?_⟩
            · rw [Nat.succ_mul]; omega
            · simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
                List.getElem_singleton]
              exact List.mem_append_left _ h2
        · subst ht
          rw [hopj] at ho
          cases ho
          refine ⟨st.frozen.length, by simp, by omega, ?_, ?_⟩
          · rw [Nat.succ_mul]; omega
          · simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
              List.getElem_singleton]
            exact List.mem_append_right _ (List.mem_singleton_self _)
    · simp only [List.length_append, List.length_singleton, hclen] at hfz
      refine ⟨?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton, hclen]
        omega
      · simp only [List.length_append, List.length_singleton, hclen]
        omega
      · intro t o ht ho hno
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
        · rcases hold t o ht ho hno with h | ⟨h1, h2⟩
          · exact Or.inl h
          · exact Or.inr ⟨h1, List.mem_append_left _ h2⟩
        · subst ht
          rw [hopj] at ho
          cases ho
          exact Or.inr ⟨by dsimp only; omega, List.mem_append_right _ (List.mem_singleton_self _)⟩

theorem frozen_prefix (g : OnlineGeom) (run : OnlineRun) {j : Nat} :
    ∀ j', j ≤ j' → j' ≤ run.ops.length → (stateAt g run j).frozen <+: (stateAt g run j').frozen := by
  intro j'
  induction j' with
  | zero => intro h _; rw [Nat.le_zero.1 h]
  | succ j' ih =>
    intro h hl
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with h' | h'
    · refine (ih (Nat.le_of_lt_succ h') (Nat.le_of_succ_le hl)).trans ?_
      rw [stateAt_succ g run hl]
      dsimp only [Requester.step, Requester.insert]
      split_ifs
      all_goals first | exact List.prefix_append _ _ | exact List.prefix_refl _
    · rw [h']

/-- The last operation in `[j, j')` with a given property. -/
theorem last_occ (P : Nat → Prop) [DecidablePred P] {j j' : Nat} (hj : j < j') (hP : P j) :
    ∃ t, j ≤ t ∧ t < j' ∧ P t ∧ ∀ u, t < u → u < j' → ¬ P u := by
  induction j' with
  | zero => omega
  | succ j' ih =>
    by_cases h : P j'
    · exact ⟨j', by omega, Nat.lt_succ_self _, h, fun u h1 h2 => by omega⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · obtain ⟨t, h1, h2, h3, h4⟩ := ih hj
        refine ⟨t, h1, Nat.lt_succ_of_lt h2, h3, fun u hu1 hu2 => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu2 with hu2 | hu2
        · exact h4 u hu1 hu2
        · rw [hu2]; exact h
      · subst hj; exact absurd hP h

end RebuildBound.OnlineFreshProof
