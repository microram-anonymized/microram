import RebuildBound.Proofs.SG1.Terms

/-!
# SG1: the shape of the reference trace and the stash lengths
-/

namespace RebuildBound.SG1Proof

open RebuildBound.Model RebuildBound.Spec

/-! ### One pair operation -/

theorem sPairStep_spec (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → ℕ) (j i : ℕ) (st : SRoute) :
    ∃ (sj : List Rec) (c : Bool),
      (sPairStep rule g w j i st).trace = st.trace ++ [(.stash j c, sj.length)] ∧
      (∀ s ∈ (sPairStep rule g w j i st).stash, s ∈ st.stash ∨ s = sj) ∧
      (sPairStep rule g w j i st).stash.length = st.stash.length :=
  ⟨_, _, rfl, fun s hs => List.mem_or_eq_of_mem_set hs, List.length_set⟩

/-- Trace entries of a run of pair operations. -/
theorem runSOps_trace (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → ℕ) (ops : List (ℕ × ℕ))
    (st : SRoute) (hops : ∀ o ∈ ops, o.1 < g.k)
    (hst : ∀ e ∈ st.trace, ∃ j c, e.1 = .stash j c ∧ j < g.k) :
    ∀ e ∈ (runSOps rule g w ops st).trace, ∃ j c, e.1 = .stash j c ∧ j < g.k := by
  induction ops generalizing st with
  | nil => exact hst
  | cons o ops ih =>
    refine ih (sPairStep rule g w o.1 o.2 st)
      (fun o' ho' => hops o' (List.mem_cons_of_mem _ ho')) ?_
    intro e he
    obtain ⟨sj, c, ht, _, _⟩ := sPairStep_spec rule g w o.1 o.2 st
    rw [ht] at he
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact hst e he
    · exact ⟨o.1, c, rfl, hops o List.mem_cons_self⟩

theorem runSOps_trace_mono (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → ℕ) (ops : List (ℕ × ℕ))
    (st : SRoute) : ∀ e ∈ st.trace, e ∈ (runSOps rule g w ops st).trace := by
  induction ops generalizing st with
  | nil => exact fun e he => he
  | cons o ops ih =>
    intro e he
    refine ih (sPairStep rule g w o.1 o.2 st) e ?_
    obtain ⟨sj, c, ht, _, _⟩ := sPairStep_spec rule g w o.1 o.2 st
    rw [ht]; exact List.mem_append_left _ he

theorem runSOps_stash_length (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → ℕ) (ops : List (ℕ × ℕ))
    (st : SRoute) : (runSOps rule g w ops st).stash.length = st.stash.length := by
  induction ops generalizing st with
  | nil => rfl
  | cons o ops ih =>
    show (runSOps rule g w ops (sPairStep rule g w o.1 o.2 st)).stash.length = _
    rw [ih]
    exact (sPairStep_spec rule g w o.1 o.2 st).choose_spec.choose_spec.2.2

/-- If every stash test of the run passes `S`, every stash list has at most `S` records. -/
theorem runSOps_stash_le (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → ℕ) (ops : List (ℕ × ℕ))
    (S : ℕ) (st : SRoute)
    (htr : ∀ e ∈ (runSOps rule g w ops st).trace, ∀ j c, e.1 = .stash j c → e.2 ≤ S)
    (hst : ∀ s ∈ st.stash, s.length ≤ S) :
    ∀ s ∈ (runSOps rule g w ops st).stash, s.length ≤ S := by
  induction ops generalizing st with
  | nil => exact hst
  | cons o ops ih =>
    refine ih (sPairStep rule g w o.1 o.2 st) htr ?_
    obtain ⟨sj, c, ht, hs, _⟩ := sPairStep_spec rule g w o.1 o.2 st
    intro s hs'
    rcases hs s hs' with h | rfl
    · exact hst s h
    · have hm : ((.stash o.1 c, s.length) : STest × ℕ) ∈
          (runSOps rule g w ops (sPairStep rule g w o.1 o.2 st)).trace := by
        refine runSOps_trace_mono rule g w ops _ _ ?_
        rw [ht]; simp
      exact htr _ hm o.1 c rfl

/-! ### The radix pass -/

theorem radixPass_stash (g : SepGeom) (w : Model.LogicalKey → ℕ) (st : SRoute) :
    (radixPass g w st).stash = st.stash := by
  unfold radixPass
  split_ifs
  · generalize List.range g.blk = l
    induction l generalizing st with
    | nil => rfl
    | cons p l ih => exact (ih (radixStep g w p st)).trans rfl
  · rfl

theorem radixPass_trace (g : SepGeom) (w : Model.LogicalKey → ℕ) (st : SRoute)
    (hst : ∀ e ∈ st.trace, (∃ j c, e.1 = .stash j c ∧ j < g.k)) :
    ∀ e ∈ (radixPass g w st).trace, (∃ j c, e.1 = .stash j c ∧ j < g.k) ∨
      (e.1 = .radix ∧ 1 < g.r) := by
  unfold radixPass
  split_ifs with hr
  · have : ∀ (l : List ℕ) (st : SRoute),
        (∀ e ∈ st.trace, (∃ j c, e.1 = .stash j c ∧ j < g.k) ∨ (e.1 = .radix ∧ 1 < g.r)) →
        ∀ e ∈ (l.foldl (fun st p => radixStep g w p st) st).trace,
          (∃ j c, e.1 = .stash j c ∧ j < g.k) ∨ (e.1 = .radix ∧ 1 < g.r) := by
      intro l
      induction l with
      | nil => exact fun st h => h
      | cons p l ih =>
        intro st h
        refine ih _ ?_
        intro e he
        simp only [radixStep, List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact h e he
        · exact Or.inr ⟨rfl, hr⟩
    exact this _ st (fun e he => Or.inl (hst e he))
  · exact fun e he => Or.inl (hst e he)

theorem sRouteWith_trace (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → ℕ) (aMain : List Bucket)
    (ops : List (ℕ × ℕ)) (hops : ∀ o ∈ ops, o.1 < g.k) :
    ∀ e ∈ (sRouteWith rule g w aMain ops).trace, (∃ j c, e.1 = .stash j c ∧ j < g.k) ∨
      (e.1 = .radix ∧ 1 < g.r) := by
  unfold sRouteWith
  refine radixPass_trace g w _ ?_
  exact runSOps_trace rule g w ops _ hops (by simp [sRouteInit])

theorem sRouteWith_stash (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → ℕ) (aMain : List Bucket)
    (ops : List (ℕ × ℕ)) :
    (sRouteWith rule g w aMain ops).stash = (runSOps rule g w ops (sRouteInit g aMain)).stash :=
  radixPass_stash _ _ _

theorem sRouteWith_stash_length (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → ℕ) (aMain : List Bucket)
    (ops : List (ℕ × ℕ)) : (sRouteWith rule g w aMain ops).stash.length = g.k := by
  rw [sRouteWith_stash, runSOps_stash_length]
  simp [sRouteInit]

/-! ### The later phases -/

theorem sDfsTrace_dfs (g : SepGeom) (w : Model.LogicalKey → ℕ) (pool : List Rec) :
    ∀ e ∈ sDfsTrace g w pool, ∃ dd c, e.1 = .dfs dd c := by
  intro e he
  simp only [sDfsTrace, List.mem_flatMap, List.mem_range, List.mem_map] at he
  obtain ⟨d, _, c, _, rfl⟩ := he
  exact ⟨d, c, rfl⟩

theorem sOfferB_trace (g : SepGeom) (w : Model.LogicalKey → ℕ) (ci : ℕ) (st : SFin) :
    (sOfferB g w ci st).trace = st.trace := by
  unfold sOfferB
  generalize List.range st.bcopy.length = l
  induction l generalizing st with
  | nil => rfl
  | cons p l ih => exact (ih (sOfferPage g w ci st p)).trans rfl

theorem sInsertBucket_trace (g : SepGeom) (w : Model.LogicalKey → ℕ) (bMain : List Bucket) (i : ℕ)
    (st : SFin) (hst : ∀ e ∈ st.trace, e.1 = .insertion) :
    ∀ e ∈ (sInsertBucket g w bMain i st).trace, e.1 = .insertion := by
  unfold sInsertBucket
  simp only
  generalize (List.range g.d) = l
  have key : ∀ (l : List ℕ) (acc : SFin × List Rec), (∀ e ∈ acc.1.trace, e.1 = .insertion) →
      ∀ e ∈ (l.foldl (fun (acc : SFin × List Rec) q =>
        let ci := i + q * g.U
        let f := fill (acc.1.main.getD ci []) ((bMain.getD i []).recs.filter fun x =>
          g.wayOf (w x.key) == q)
        let sheds := acc.2 ++ f.2
        let st := { acc.1 with main := acc.1.main.set ci f.1 }
        let st := if q + 1 = g.d then
            let ins := st.ins ++ sheds
            { st with ins := ins, trace := st.trace ++ [(.insertion, ins.length)] }
          else st
        (sOfferB g w ci (sOfferA g w ci st), sheds)) acc).1.trace, e.1 = .insertion := by
    intro l
    induction l with
    | nil => exact fun acc h => h
    | cons q l ih =>
      intro acc h
      refine ih _ ?_
      simp only
      rw [sOfferB_trace]
      have hA : ∀ (ci : ℕ) (s : SFin), (sOfferA g w ci s).trace = s.trace := fun _ _ => rfl
      rw [hA]
      split_ifs
      · intro e he
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact h e he
        · rfl
      · exact h
  exact key l _ hst

theorem sFinish_trace (g : SepGeom) (w : Model.LogicalKey → ℕ) (inp : SInputs) (routed : List Bucket)
    (leaves : List (List Rec)) : ∀ e ∈ (sFinish g w inp routed leaves).trace, e.1 = .insertion := by
  unfold sFinish
  generalize (List.range g.U) = l
  have key : ∀ (l : List ℕ) (st : SFin), (∀ e ∈ st.trace, e.1 = .insertion) →
      ∀ e ∈ (l.foldl (fun st i => sInsertBucket g w inp.bMain i st) st).trace,
        e.1 = .insertion := by
    intro l
    induction l with
    | nil => exact fun st h => h
    | cons i l ih => exact fun st h => ih _ (sInsertBucket_trace g w _ i st h)
  exact key l _ (by simp)

theorem sDrain_trace (st : SFin) : ∀ e ∈ (sDrain st).2, e.1 = .drain := by
  have key : ∀ (l : List (List (Rec × Bool)))
      (acc : List (Option (Rec × Bool)) × List (STest × ℕ)), (∀ e ∈ acc.2, e.1 = .drain) →
      ∀ e ∈ (l.foldl sDrainStep acc).2, e.1 = .drain := by
    intro l
    induction l with
    | nil => exact fun acc h => h
    | cons L l ih =>
      intro acc h
      refine ih _ ?_
      intro e he
      simp only [sDrainStep, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact h e he
      · rfl
  intro e he
  simp only [sDrain, sDrainStep, List.mem_append, List.mem_singleton] at he
  rcases he with he | rfl
  · exact key _ _ (by simp) e he
  · rfl

end RebuildBound.SG1Proof
