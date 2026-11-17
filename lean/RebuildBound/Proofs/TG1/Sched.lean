import RebuildBound.Spec.TopPrepG

/-!
# TG1: the first-failure inventory of the engine job

`canonicalValid`: `g.canonicalOps` is a valid schedule. `fail_cases`: a failing engine job
(TP6 with TPEngine) is a stash of bit `j < k`, a DFS node (only if `g.dfs`), or the drain,
and TP4a/TP4b turn each into a reference event.
-/

namespace RebuildBound.TG1Proof

open RebuildBound.Model RebuildBound.Spec

theorem pairwise_idx {α : Type} [BEq α] [LawfulBEq α] (f : α → ℕ) :
    ∀ l : List α, l.Pairwise (fun a b => f a ≤ f b) →
      ∀ a ∈ l, ∀ b ∈ l, f a < f b → l.idxOf a < l.idxOf b := by
  intro l
  induction l with
  | nil => simp
  | cons x t ih =>
    intro hp a ha b hb hab
    rw [List.pairwise_cons] at hp
    have hbx : b ≠ x := by
      intro h
      rcases List.mem_cons.mp ha with hax | ha'
      · rw [hax, h] at hab; exact lt_irrefl _ hab
      · have := hp.1 a ha'; rw [h] at hab; omega
    by_cases hax : a = x
    · subst hax
      simp [List.idxOf_cons_self, List.idxOf_cons_ne _ (Ne.symm hbx)]
    · have ha' : a ∈ t := by simpa [hax] using ha
      have hb' : b ∈ t := by simpa [hbx] using hb
      rw [List.idxOf_cons_ne _ (Ne.symm hax), List.idxOf_cons_ne _ (Ne.symm hbx)]
      have := ih hp.2 a ha' b hb' hab
      omega

theorem canonicalValid (g : TPGeom) : TPValidSchedule g g.canonicalOps := by
  refine ⟨List.Perm.refl _, ?_⟩
  have hpw : g.canonicalOps.Pairwise (fun a b => a.1 ≤ b.1) := by
    unfold TPGeom.canonicalOps
    rw [List.pairwise_flatMap]
    refine ⟨fun j _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      exact List.pairwise_iff_getElem.mpr (fun _ _ _ _ _ => le_rfl)
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij a ha b hb
      simp only [List.mem_map] at ha hb
      obtain ⟨a', _, rfl⟩ := ha
      obtain ⟨b', _, rfl⟩ := hb
      have hs : (List.range (g.k - 1)).Pairwise (· < ·) := List.pairwise_lt_range
      rw [List.pairwise_iff_getElem] at hs
      have := hs i j hi hj hij
      simp only [List.getElem_range] at this
      show _ ≤ _
      simp only [List.getElem_range]
      omega
  intro a ha b hb hab _
  exact pairwise_idx (fun o : ℕ × ℕ => o.1) _ hpw a ha b hb hab

/-! ### The trace -/

theorem runTPOps_trace (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → ℕ) (ops : List (ℕ × ℕ)) :
    ∀ (st : TPRoute) (e : TPTest × ℕ), e ∈ (runTPOps rule g w ops st).trace →
      e ∈ st.trace ∨ ∃ o ∈ ops, e.1 = .stash o.1 := by
  induction ops with
  | nil => intro st e he; exact Or.inl he
  | cons o ops ih =>
    intro st e he
    unfold runTPOps at he
    simp only [List.foldl_cons] at he
    have := ih (tpPairStep rule g w o.1 o.2 st) e he
    rcases this with h | ⟨o', ho', h⟩
    · simp only [tpPairStep, List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨o, List.mem_cons_self, by rw [h]⟩
    · exact Or.inr ⟨o', List.mem_cons_of_mem _ ho', h⟩

theorem tpOffer_trace (g : TPGeom) (w : Model.LogicalKey → ℕ) (b : ℕ) (st : TPFin) :
    (tpOffer g w b st).trace = st.trace := rfl

theorem tpFinish_trace (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → ℕ) (routed : List Bucket)
    (leaves : List (List Rec)) (e : TPTest × ℕ) (he : e ∈ (tpFinish rule g w routed leaves).trace) :
    e.1 = .stash (g.k - 1) := by
  unfold tpFinish at he
  have key : ∀ (l : List ℕ) (st : TPFin), (∀ e ∈ st.trace, e.1 = .stash (g.k - 1)) →
      ∀ e ∈ (l.foldl (fun st i => tpLastStep rule g w i st) st).trace, e.1 = .stash (g.k - 1) := by
    intro l
    induction l with
    | nil => intro st h; exact h
    | cons i l ih =>
      intro st h
      simp only [List.foldl_cons]
      refine ih _ ?_
      intro e he
      simp only [tpLastStep, tpOffer_trace, List.mem_append, List.mem_singleton] at he
      rcases he with he | he
      · exact h e he
      · rw [he]
  exact key _ _ (by simp) e he

theorem tpDrain_trace (st : TPFin) (e : TPTest × ℕ) (he : e ∈ (tpDrain st).2) :
    e.1 = .drain := by
  unfold tpDrain at he
  have key : ∀ (l : List (List Rec)) (acc : List (Option Rec) × List (TPTest × ℕ)),
      (∀ e ∈ acc.2, e.1 = .drain) →
      ∀ e ∈ (l.foldl tpDrainStep acc).2, e.1 = .drain := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons L l ih =>
      intro acc h
      simp only [List.foldl_cons]
      refine ih _ ?_
      intro e he
      simp only [tpDrainStep, List.mem_append, List.mem_singleton] at he
      rcases he with he | he
      · exact h e he
      · rw [he]
  exact key _ _ (by simp) e he

/-- The kinds of failing test of the reference execution under the canonical schedule. -/
theorem firstFailure_kind (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (w : Model.LogicalKey → ℕ)
    (inp : TPInputs) (t : TPTest) (hk : 1 ≤ g.k)
    (h : tpFirstFailure g (tpReferenceWith rule g unsh w inp g.canonicalOps).trace = some t) :
    (∃ j, j < g.k ∧ t = .stash j) ∨ (g.dfs = true ∧ ∃ dd c, t = .dfs dd c) ∨ t = .drain := by
  unfold tpFirstFailure at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  have he' := List.mem_of_find?_eq_some he
  simp only [tpReferenceWith, List.mem_append] at he'
  rcases he' with ((he' | he') | he') | he'
  · rcases runTPOps_trace rule g w g.canonicalOps _ e he' with h1 | ⟨o, ho, h1⟩
    · simp [tpRouteInit] at h1
    · left
      refine ⟨o.1, ?_, h1⟩
      unfold TPGeom.canonicalOps at ho
      simp only [List.mem_flatMap, List.mem_map, List.mem_range] at ho
      obtain ⟨j, hj, i, _, rfl⟩ := ho
      simp only; omega
  · split at he'
    · rename_i hd
      right; left
      refine ⟨hd, ?_⟩
      unfold tpDfsTrace at he'
      simp only [List.mem_flatMap, List.mem_map] at he'
      obtain ⟨dd, _, c, _, rfl⟩ := he'
      exact ⟨dd, c, rfl⟩
    · simp at he'
  · left
    have := tpFinish_trace rule g w _ _ e he'
    exact ⟨g.k - 1, by omega, this⟩
  · right; right
    exact tpDrain_trace _ e he'

theorem fail_cases (hE : TPEngine_statement) (h6 : TP6_statement) (h4a : TP4a_statement)
    (h4b : TP4b_statement) (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (pos w : Model.LogicalKey → ℕ)
    (inp : TPInputs) (hr : rule.Valid) (hv : g.Valid) (hs : TPShape g pos inp)
    (hfit : TPTiersFit g inp) (hfail : (tpJob rule g unsh w inp).toBool = false) :
    (∃ j, j < g.k ∧ g.stashPages * g.C < tpRawStageExcess g unsh pos w inp j) ∨
    (g.dfs = true ∧ ∃ R < g.ranges, g.C < tpRefCoarse g unsh w
      (tpReferenceWith rule g unsh w inp g.canonicalOps) inp g.earlyCap R) ∨
    g.drainPages * g.C < tpHomeExcess g unsh w inp := by
  have hlanes : TPLanes g inp := ⟨hs.aLen, hs.aLanes⟩
  have h6' := (h6 rule g unsh w inp (tpEngineOps g) hr hv hlanes (hE g hv)).2.2
  have hfail' : (tpJobWith rule g unsh w inp g.canonicalOps).toBool = false := by
    rw [← h6']; exact hfail
  have h4a' := h4a rule g unsh pos w inp g.canonicalOps hr hv hs (canonicalValid g)
  have h4b' := h4b rule g unsh w inp g.canonicalOps hr hv hlanes (canonicalValid g)
  unfold tpJobWith at hfail'
  dsimp only at hfail'
  cases hff : tpFirstFailure g (tpReferenceWith rule g unsh w inp g.canonicalOps).trace with
  | none => rw [hff] at hfail'; simp [Except.toBool] at hfail'
  | some t =>
    rcases firstFailure_kind rule g unsh w inp t hv.1 hff with ⟨j, hj, rfl⟩ | ⟨hd, dd, c, rfl⟩ | rfl
    · exact Or.inl ⟨j, hj, h4a'.1 j hff⟩
    · exact Or.inr (Or.inl ⟨hd, h4a'.2 dd c hfit hff⟩)
    · exact Or.inr (Or.inr (h4b' hff))

end RebuildBound.TG1Proof
