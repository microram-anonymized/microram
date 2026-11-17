import RebuildBound.Proofs.SG1.Trace
import RebuildBound.Spec.SepT

/-!
# SG1: the failure inventory on one outcome (ST4a, ST4b, ST6, SEngine)
-/

namespace RebuildBound.SG1Proof

open RebuildBound.Model RebuildBound.Spec

theorem radixPass_trace_mono (g : SepGeom) (w : Model.LogicalKey → ℕ) (st : SRoute) :
    ∀ e ∈ st.trace, e ∈ (radixPass g w st).trace := by
  unfold radixPass
  split_ifs
  · have : ∀ (l : List ℕ) (st : SRoute), ∀ e ∈ st.trace,
        e ∈ (l.foldl (fun st p => radixStep g w p st) st).trace := by
      intro l
      induction l with
      | nil => exact fun st e he => he
      | cons p l ih =>
        intro st e he
        refine ih _ e ?_
        simp only [radixStep, List.mem_append]
        exact Or.inl he
    exact this _ st
  · exact fun e he => he

theorem ops_lt (g : SepGeom) (ops : List (ℕ × ℕ)) (h : SValidSched g ops) :
    ∀ o ∈ ops, o.1 < g.k := by
  intro o ho
  have := h.1.subset ho
  simp only [SepGeom.canonicalOps, List.mem_flatMap, List.mem_range, List.mem_map] at this
  obtain ⟨j, hj, i, _, rfl⟩ := this
  exact hj

theorem ref_trace (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → ℕ) (inp : SInputs)
    (ops : List (ℕ × ℕ)) :
    (sReferenceWith rule g w inp ops).trace =
      (sRouteWith rule g w inp.aMain ops).trace ++
        (sDfsTrace g w (sPool (sRouteWith rule g w inp.aMain ops) inp.aTier inp.bTier) ++
          ((sFinish g w inp (sRouteWith rule g w inp.aMain ops).main
            (sLeaves g w (sPool (sRouteWith rule g w inp.aMain ops) inp.aTier inp.bTier))).trace ++
            (sDrain (sFinish g w inp (sRouteWith rule g w inp.aMain ops).main
            (sLeaves g w (sPool (sRouteWith rule g w inp.aMain ops) inp.aTier inp.bTier)))).2)) := by
  simp only [sReferenceWith, List.append_assoc]

theorem ff_prefix (g : SepGeom) (r1 r2 : List (STest × ℕ)) (t : STest)
    (h : sFirstFailure g (r1 ++ r2) = some t) (ht : ∀ e ∈ r1, e.1 ≠ t) :
    ∀ e ∈ r1, e.2 ≤ g.capOf e.1 := by
  unfold sFirstFailure at h
  rw [List.find?_append] at h
  cases hf : r1.find? (fun t => decide (g.capOf t.1 < t.2)) with
  | some x =>
    rw [hf] at h
    simp only [Option.some_or, Option.map_some, Option.some.injEq] at h
    exact absurd h (ht x (List.mem_of_find?_eq_some hf))
  | none =>
    intro e he
    have := List.find?_eq_none.mp hf e he
    simpa using this

theorem ff_mem (g : SepGeom) (trace : List (STest × ℕ)) (t : STest)
    (h : sFirstFailure g trace = some t) : ∃ e ∈ trace, e.1 = t := by
  unfold sFirstFailure at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨e, List.mem_of_find?_eq_some he, rfl⟩

theorem sJob_some (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → ℕ) (inp : SInputs)
    (h : (sJob rule g w inp).toBool = false) :
    ∃ t, sFirstFailure g (sReferenceWith rule g w inp (engineOps g)).trace = some t := by
  unfold sJob sJobWith at h
  cases hf : sFirstFailure g (sReferenceWith rule g w inp (engineOps g)).trace with
  | none => simp [hf, Except.toBool] at h
  | some t => exact ⟨t, rfl⟩

/-- Membership in the reference trace: the kind of each entry. -/
theorem trace_kind (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → ℕ) (inp : SInputs)
    (ops : List (ℕ × ℕ)) (hops : ∀ o ∈ ops, o.1 < g.k) :
    ∀ e ∈ (sReferenceWith rule g w inp ops).trace,
      ((∃ j c, e.1 = .stash j c ∧ j < g.k) ∨ (e.1 = .radix ∧ 1 < g.r)) ∨
      (∃ dd c, e.1 = .dfs dd c) ∨ e.1 = .insertion ∨ e.1 = .drain := by
  intro e he
  rw [ref_trace] at he
  simp only [List.mem_append] at he
  rcases he with he | he | he | he
  · exact Or.inl (sRouteWith_trace rule g w inp.aMain ops hops e he)
  · exact Or.inr (Or.inl (sDfsTrace_dfs _ _ _ e he))
  · exact Or.inr (Or.inr (Or.inl (sFinish_trace _ _ _ _ _ e he)))
  · exact Or.inr (Or.inr (Or.inr (sDrain_trace _ e he)))

/-! ### The coarse count -/

theorem flatten_perm_of_getD : ∀ (l1 l2 : List (List Rec)), l1.length = l2.length →
    (∀ j, (l1.getD j []).Perm (l2.getD j [])) → l1.flatten.Perm l2.flatten
  | [], [], _, _ => List.Perm.refl _
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l1, b :: l2, h, hj => by
    simp only [List.flatten_cons]
    refine List.Perm.append (by simpa using hj 0) (flatten_perm_of_getD l1 l2 (by simpa using h) ?_)
    intro j
    simpa using hj (j + 1)

theorem coarse_eq (g : SepGeom) (w : Model.LogicalKey → ℕ) (run : SRun) (inp : SInputs) (v : ℕ)
    (hfit : STiersFit g inp) (hS : ∀ s ∈ run.route.stash, s.length ≤ g.stashPages * g.C) :
    sRefCoarse g w run inp g.earlyCap v =
      (inp.aTier ++ run.route.stash.flatten ++ run.route.radix).countP
        fun x => sRange g w x == v := by
  unfold sRefCoarse sEarlyList sLateSheds
  have h1 : inp.aTier.length ≤ g.aTierPages * g.C := hfit
  have h2 : (run.route.stash.take g.I).flatten.length ≤ g.I * (g.stashPages * g.C) := by
    rw [List.length_flatten]
    calc _ ≤ (((run.route.stash.take g.I).map List.length).length) • (g.stashPages * g.C) :=
          List.sum_le_length_nsmul _ _ (by
            intro x hx
            obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
            exact hS s (List.mem_of_mem_take hs))
      _ ≤ g.I • (g.stashPages * g.C) := by
          apply Nat.mul_le_mul_right
          simp
      _ = _ := smul_eq_mul _ _
  have hlen : (inp.aTier ++ (run.route.stash.take g.I).flatten).length ≤ g.earlyCap := by
    rw [List.length_append]
    unfold SepGeom.earlyCap
    omega
  rw [List.take_of_length_le hlen]
  congr 1
  rw [List.append_assoc, List.append_assoc, ← List.append_assoc (List.flatten _),
    ← List.flatten_append, List.take_append_drop]

theorem coarse_transfer (h6 : ST6_statement) (rule : CapRule) (g : SepGeom)
    (wOld w : Model.LogicalKey → ℕ) (inp : SInputs) (ops : List (ℕ × ℕ))
    (hrule : rule.Valid) (hg : g.Valid) (hsh : SInputShape g wOld w inp) (hvs : SValidSched g ops)
    (hfit : STiersFit g inp)
    (hpass : ∀ e ∈ (sRouteWith rule g w inp.aMain ops).trace, ∀ j c, e.1 = .stash j c →
      e.2 ≤ g.stashPages * g.C) (v : ℕ) :
    sRefCoarse g w (sReferenceWith rule g w inp ops) inp g.earlyCap v =
      sRefCoarse g w (sReferenceWith rule g w inp g.canonicalOps) inp g.earlyCap v := by
  obtain ⟨-, hst, hrad, -⟩ := h6 rule g wOld w inp ops hrule hg hsh hvs
  have hE : ∀ s ∈ (sRouteWith rule g w inp.aMain ops).stash, s.length ≤ g.stashPages * g.C := by
    rw [sRouteWith_stash]
    refine runSOps_stash_le rule g w ops _ _ ?_ (by simp [sRouteInit])
    intro e he j c hj
    refine hpass e ?_ j c hj
    exact radixPass_trace_mono g w _ e he
  have hlenE := sRouteWith_stash_length rule g w inp.aMain ops
  have hlenK := sRouteWith_stash_length rule g w inp.aMain g.canonicalOps
  have hK : ∀ s ∈ (sRouteWith rule g w inp.aMain g.canonicalOps).stash,
      s.length ≤ g.stashPages * g.C := by
    intro s hs
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hs
    have hjE : j < (sRouteWith rule g w inp.aMain ops).stash.length := by omega
    have hp := hst j
    have e1 : ∀ (l : List (List Rec)) (hj : j < l.length), l.getD j [] = l[j] := by
      intro l hj; simp [hj]
    rw [e1 _ hjE, e1 _ hj] at hp
    rw [← hp.length_eq]
    exact hE _ (List.getElem_mem hjE)
  rw [coarse_eq g w _ inp v hfit hE, coarse_eq g w _ inp v hfit hK]
  refine List.Perm.countP_eq _ ?_
  show (inp.aTier ++ _ ++ _).Perm (inp.aTier ++ _ ++ _)
  have hrad' : (sReferenceWith rule g w inp ops).route.radix =
      (sReferenceWith rule g w inp g.canonicalOps).route.radix := hrad
  rw [hrad']
  exact List.Perm.append_right _ (List.Perm.append_left _
    (flatten_perm_of_getD _ _ (hlenE.trans hlenK.symm) hst))

/-! ### The failure inventory -/

theorem fail_cases (h4a : ST4a_statement) (h4b : ST4b_statement) (h6 : ST6_statement)
    (hEng : SEngine_statement) (rule : CapRule) (g : SepGeom) (wOld w : Model.LogicalKey → ℕ) (inp : SInputs)
    (hrule : rule.Valid) (hg : g.Valid) (hsh : SInputShape g wOld w inp)
    (hfit : STiersFit g inp) (hfail : (sJob rule g w inp).toBool = false) :
    (((∃ j < g.k, g.stashPages * g.C < sRawStageExcess g wOld w inp j) ∨
        (1 < g.r ∧ g.stashPages * g.C < sAHomeExcess g w inp)) ∨
      (∃ v < g.ranges, g.C < sRefCoarse g w (sReferenceWith rule g w inp g.canonicalOps) inp
          g.earlyCap v)) ∨
      min (g.stashPages * g.C) (g.tierPages * g.C) < sHomeExcess g w inp := by
  have hvs := hEng g hg
  have hops := ops_lt g _ hvs
  obtain ⟨t, ht⟩ := sJob_some rule g w inp hfail
  have ha := h4a rule g wOld w inp (engineOps g) hrule hg hsh hvs
  have hb := h4b rule g wOld w inp (engineOps g) hrule hg hsh hvs
  obtain ⟨e, he, het⟩ := ff_mem g _ t ht
  have hk := trace_kind rule g w inp (engineOps g) hops e he
  cases t with
  | stash j c =>
    rw [het] at hk
    rcases hk with (⟨j', c', h1, h2⟩ | ⟨h1, _⟩) | (⟨dd, c', h1⟩ | h1 | h1)
    · simp only [STest.stash.injEq] at h1
      obtain ⟨rfl, -⟩ := h1
      exact Or.inl (Or.inl (Or.inl ⟨j, h2, ha.1 j c ht⟩))
    all_goals simp_all
  | radix =>
    rw [het] at hk
    rcases hk with (⟨j', c', h1, h2⟩ | ⟨h1, h2⟩) | (⟨dd, c', h1⟩ | h1 | h1)
    · simp_all
    · exact Or.inl (Or.inl (Or.inr ⟨h2, ha.2.1 ht⟩))
    all_goals simp_all
  | dfs dd c =>
    refine Or.inl (Or.inr ?_)
    obtain ⟨v, hv, hc⟩ := ha.2.2 dd c ht hfit
    refine ⟨v, hv, ?_⟩
    rw [← coarse_transfer h6 rule g wOld w inp (engineOps g) hrule hg hsh hvs hfit ?_ v]
    · exact hc
    · have hp := ff_prefix g _ _ (.dfs dd c) (by
        rw [ref_trace] at ht
        exact ht) (by
        intro e he
        rcases sRouteWith_trace rule g w inp.aMain (engineOps g) hops e he with
          ⟨j, c, h1, _⟩ | ⟨h1, _⟩
        · rw [h1]; simp
        · rw [h1]; simp)
      intro e he j c hj
      have := hp e he
      rw [hj] at this
      exact this
  | insertion =>
    exact Or.inr (lt_of_le_of_lt (min_le_left _ _) (hb.1 ht))
  | drain =>
    exact Or.inr (lt_of_le_of_lt (min_le_right _ _) (hb.2 ht))

end RebuildBound.SG1Proof
