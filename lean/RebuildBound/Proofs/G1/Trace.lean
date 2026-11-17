import RebuildBound.Spec.G

/-!
# G1: the shape of the reference trace

Only stage stashes `j < b = k + 1` are tested: the route's trace has one entry
`.stash j` per pair operation `(j, i)` of the model's schedule; the DFS,
insertion and drain phases record only `.dfs`, `.insertion` and `.drain`
entries. And a failing job has a first failing test.
-/

namespace RebuildBound.G1Proof

open RebuildBound.Model

theorem runOps_trace (rule : CapRule) (g : Geom) (w : Model.LogicalKey → ℕ) (ops : List (ℕ × ℕ))
    (st : RouteState) (hops : ∀ o ∈ ops, o.1 < g.stages)
    (hst : ∀ e ∈ st.trace, ∀ j, e.1 = .stash j → j < g.stages) :
    ∀ e ∈ (runOps rule g w ops st).trace, ∀ j, e.1 = .stash j → j < g.stages := by
  induction ops generalizing st with
  | nil => exact hst
  | cons o ops ih =>
    refine ih (pairStep rule g w o.1 o.2 st)
      (fun o' ho' => hops o' (List.mem_cons_of_mem _ ho')) ?_
    intro e he j hj
    simp only [pairStep, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact hst e he j hj
    · simp only [Test.stash.injEq] at hj
      subst hj
      exact hops o List.mem_cons_self

theorem canonicalOps_lt (g : Geom) : ∀ o ∈ canonicalOps g, o.1 < g.stages := by
  intro o ho
  simp only [canonicalOps, stageOps, List.mem_flatMap, List.mem_range, List.mem_map] at ho
  obtain ⟨j, hj, i, _, rfl⟩ := ho
  exact hj

theorem insertBucket_trace (g : Geom) (w : Model.LogicalKey → ℕ) (bMain : List Bucket) (i : ℕ)
    (st : FinState) : ∃ n, (insertBucket g w bMain i st).trace = st.trace ++ [(.insertion, n)] :=
  ⟨_, rfl⟩

theorem finish_trace_aux (g : Geom) (w : Model.LogicalKey → ℕ) (bMain : List Bucket) (l : List ℕ)
    (st : FinState) (hst : ∀ e ∈ st.trace, e.1 = .insertion) :
    ∀ e ∈ (l.foldl (fun st i => insertBucket g w bMain i st) st).trace, e.1 = .insertion := by
  induction l generalizing st with
  | nil => exact hst
  | cons i l ih =>
    refine ih _ ?_
    obtain ⟨n, hn⟩ := insertBucket_trace g w bMain i st
    rw [hn]
    intro e he
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact hst e he
    · rfl

theorem finish_trace (g : Geom) (w : Model.LogicalKey → ℕ) (inp : Inputs) (routed : List Bucket)
    (leaves : List (List Rec)) :
    ∀ e ∈ (finish g w inp routed leaves).trace, e.1 = .insertion :=
  finish_trace_aux g w inp.bMain _ _ (by simp)

theorem drain_foldl_trace (l : List (List (Rec × Bool)))
    (acc : List (Option (Rec × Bool)) × List (Test × ℕ)) (hacc : ∀ e ∈ acc.2, e.1 = .drain) :
    ∀ e ∈ (l.foldl drainStep acc).2, e.1 = .drain := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons L l ih =>
    refine ih _ ?_
    intro e he
    simp only [drainStep, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact hacc e he
    · rfl

theorem drain_trace (st : FinState) : ∀ e ∈ (drain st).2, e.1 = .drain := by
  intro e he
  simp only [drain, drainStep, List.mem_append, List.mem_singleton] at he
  rcases he with he | rfl
  · exact drain_foldl_trace _ _ (by simp) e he
  · rfl

theorem dfsTrace_ne (g : Geom) (w : Model.LogicalKey → ℕ) (pool : List Rec) :
    ∀ e ∈ dfsTrace g w pool, ∀ j, e.1 ≠ .stash j := by
  intro e he j
  simp only [dfsTrace, List.mem_flatMap, List.mem_range, List.mem_map] at he
  obtain ⟨d, _, c, _, rfl⟩ := he
  simp

/-- The reference trace tests stage stashes of bits `j < k + 1` only. -/
theorem reference_stash_lt (rule : CapRule) (g : Geom) (w : Model.LogicalKey → ℕ) (inp : Inputs) :
    ∀ e ∈ (reference rule g w inp).trace, ∀ j, e.1 = .stash j → j < g.stages := by
  intro e he j hj
  simp only [reference, referenceWith, List.mem_append] at he
  rcases he with ((he | he) | he) | he
  · exact runOps_trace rule g w _ _ (canonicalOps_lt g) (by simp [routeInit]) e he j hj
  · exact absurd hj (dfsTrace_ne g w _ e he j)
  · rw [finish_trace g w inp _ _ e he] at hj; cases hj
  · rw [drain_trace _ e he] at hj; cases hj

/-- A failing job has a first failing test, which is a test of the trace. -/
theorem fail_some (rule : CapRule) (g : Geom) (caps : Caps) (w : Model.LogicalKey → ℕ) (inp : Inputs)
    (h : (job rule g caps w inp).toBool = false) :
    ∃ t, firstFailure g caps (reference rule g w inp).trace = some t := by
  unfold job jobWith at h
  unfold reference
  cases hf : firstFailure g caps (referenceWith rule g w inp (canonicalOps g)).trace with
  | none => simp [hf, Except.toBool] at h
  | some t => exact ⟨t, rfl⟩

theorem firstFailure_mem (g : Geom) (caps : Caps) (trace : List (Test × ℕ)) (t : Test)
    (h : firstFailure g caps trace = some t) : ∃ e ∈ trace, e.1 = t := by
  unfold firstFailure at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨e, List.mem_of_find?_eq_some he, rfl⟩

end RebuildBound.G1Proof
