import RebuildBound.Proofs.S4b.Whole

/-!
# S4b, the coordinated drain and the reference bounds

The first drain appends A's leftovers and each B-tier page's leftovers to a
tier with no free lane, so its trace quantities are prefix sums of their
lengths. The last append follows the leftover dedup. Both are bounded by
counting distinct keys shut out of full homes.
-/

namespace RebuildBound.S4b

open RebuildBound.Model
open RebuildBound.D4b (nodup_of_subperm getD_set_self getD_set_of_ne getD_sublist_flatten
  mem_flatten_getD flatten_set_sublist fill_snd fill_of_full fill_recs_perm keys_eq mem_keys
  free_zero_of_full fill_placed_eq mem_getD_set_self' mem_getD_set' length_filter_split
  recs_sublist_flatMap not_mem_keys_clear occupied_append occupied_map_some free_map_some
  occupied_appendFill appendFill_full occupied_map_filter)

theorem sDrainStep_snd (acc : List (Option (Rec × Bool)) × List (STest × Nat))
    (L : List (Rec × Bool)) :
    (sDrainStep acc L).2 = acc.2 ++ [(.drain, occupied acc.1 + L.length)] := by
  unfold sDrainStep; simp only; rw [occupied_appendFill]

theorem drain_fold : ∀ (Ls : List (List (Rec × Bool))) (T : List (Option (Rec × Bool)))
    (tr : List (STest × Nat)), T.countP (·.isNone) = 0 →
    (Ls.foldl sDrainStep (T, tr)).1 = T ++ Ls.flatten.map some ∧
    ∀ e ∈ (Ls.foldl sDrainStep (T, tr)).2,
      e ∈ tr ∨ (e.1 = .drain ∧ e.2 ≤ occupied T + Ls.flatten.length)
  | [], T, tr, _ => ⟨by simp, fun e he => Or.inl he⟩
  | L :: Ls, T, tr, h => by
    simp only [List.foldl_cons]
    have hd : sDrainStep (T, tr) L =
        (T ++ L.map some, tr ++ [(.drain, occupied T + L.length)]) := by
      unfold sDrainStep; simp only; rw [appendFill_full T h, occupied_append, occupied_map_some]
    rw [hd]
    have h' : (T ++ L.map some).countP (·.isNone) = 0 := by
      rw [List.countP_append, h, free_map_some]
    obtain ⟨ih1, ih2⟩ := drain_fold Ls _ (tr ++ [(.drain, occupied T + L.length)]) h'
    refine ⟨by rw [ih1]; simp, ?_⟩
    intro e he
    rcases ih2 e he with he | he
    · rcases List.mem_append.1 he with he | he
      · exact Or.inl he
      · right
        rw [List.mem_singleton] at he
        subst he
        simp
    · right
      refine ⟨he.1, ?_⟩
      rw [occupied_append, occupied_map_some] at he
      simp only [List.flatten_cons, List.length_append]
      omega

/-- The first drain's lists. -/
def sFirstL (st : SFin) : List (List (Rec × Bool)) :=
  (st.leaves.map fun L => L.map fun x => (x, true)) ++
    st.bcopy.map fun L => L.map fun x => (x, false)

/-- The leftover dedup's lane test. -/
def sdq (st : SFin) : Rec × Bool → Bool :=
  fun p => !(p.2 && (st.ins.map Rec.key).contains p.1.key)

theorem sdrain_snd_eq (st : SFin) : ∃ p : Rec → Bool,
    (sDrain st).2 = ((sFirstL st).foldl sDrainStep ([], [])).2 ++
      [(.drain, occupied (((sFirstL st).foldl sDrainStep ([], [])).1.map fun s => s.filter (sdq st)) +
        (st.ins.filter p).length)] := by
  refine ⟨fun r => !(((((((sFirstL st).foldl sDrainStep ([], [])).1.map fun s =>
    s.filter (sdq st)).filterMap id).filter fun p => !p.2).map fun p => p.1.key).contains r.key), ?_⟩
  have : (sDrain st).2 = (sDrainStep ((((sFirstL st).foldl sDrainStep ([], [])).1.map fun s =>
      s.filter (sdq st)), ((sFirstL st).foldl sDrainStep ([], [])).2)
      ((st.ins.filter fun r => !(((((((sFirstL st).foldl sDrainStep ([], [])).1.map fun s =>
        s.filter (sdq st)).filterMap id).filter fun p => !p.2).map
        fun p => p.1.key).contains r.key)).map fun r => (r, false))).2 := rfl
  rw [this, sDrainStep_snd, List.length_map]

theorem sFirstL_flatten (st : SFin) : (sFirstL st).flatten =
    st.leaves.flatten.map (fun r => (r, true)) ++ st.bcopy.flatten.map fun r => (r, false) := by
  unfold sFirstL
  rw [List.flatten_append]
  simp [List.map_flatten]

/-- Every drain-trace quantity is at most `E`, given the two counting bounds. -/
theorem sdrain_bound (st : SFin) (E : Nat)
    (hA : st.leaves.flatten.length + st.bcopy.flatten.length ≤ E)
    (hB : ∀ p : Rec → Bool,
      (st.leaves.flatten.filter fun r => !(st.ins.map Rec.key).contains r.key).length +
      st.bcopy.flatten.length + (st.ins.filter p).length ≤ E) :
    ∀ e ∈ (sDrain st).2, e.1 = .drain ∧ e.2 ≤ E := by
  obtain ⟨p, hp⟩ := sdrain_snd_eq st
  obtain ⟨h1, h2⟩ := drain_fold (sFirstL st) [] [] rfl
  intro e he
  rw [hp] at he
  rcases List.mem_append.1 he with he | he
  · rcases h2 e he with he | he
    · simp at he
    · refine ⟨he.1, ?_⟩
      have := he.2
      rw [sFirstL_flatten] at this
      simp only [List.length_append, List.length_map] at this
      simp only [occupied, List.countP_nil] at this
      omega
  · rw [List.mem_singleton] at he
    subst he
    refine ⟨rfl, ?_⟩
    show occupied _ + _ ≤ E
    rw [h1, List.nil_append, occupied_map_filter, sFirstL_flatten, List.countP_append,
      List.countP_map, List.countP_map]
    have e1 : ((st.leaves.flatten).countP ((sdq st) ∘ fun r => (r, true))) =
        (st.leaves.flatten.filter fun r => !(st.ins.map Rec.key).contains r.key).length := by
      rw [List.countP_eq_length_filter]; rfl
    have e2 : (st.bcopy.flatten.countP ((sdq st) ∘ fun r => (r, false))) =
        st.bcopy.flatten.length := by
      rw [List.countP_eq_length]; intro a _; simp [sdq]
    rw [e1, e2]
    exact hB p

theorem sFirstFailure_mem {g : SepGeom} {trace : List (STest × Nat)} {t : STest}
    (h : sFirstFailure g trace = some t) :
    ∃ e ∈ trace, e.1 = t ∧ g.capOf e.1 < e.2 := by
  unfold sFirstFailure at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  have hp := List.find?_some he
  exact ⟨e, List.mem_of_find?_eq_some he, rfl, by simpa using hp⟩

theorem sDfsTrace_tests (g : SepGeom) (w : Model.LogicalKey → Nat) (pool : List Rec) :
    ∀ e ∈ sDfsTrace g w pool, ∃ d c, e.1 = STest.dfs d c := by
  intro e he
  unfold sDfsTrace at he
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at he
  obtain ⟨d, _, c, _, rfl⟩ := he
  exact ⟨d, c, rfl⟩

/-- Every insertion-trace and drain-trace quantity of the reference execution
is at most `sHomeExcess`, given the route's output. -/
theorem reference_bounds {rule : CapRule} {g : SepGeom} (hg : g.Valid) {wOld w : Model.LogicalKey → Nat}
    {inp : SInputs} {ops : List (Nat × Nat)} (hI : SInputShape g wOld w inp)
    (ro : RouteOut g w inp (sRouteWith rule g w inp.aMain ops)) :
    (∀ e ∈ (sReferenceWith rule g w inp ops).trace, e.1 = .insertion →
      e.2 ≤ sHomeExcess g w inp) ∧
    (∀ e ∈ (sReferenceWith rule g w inp ops).trace, e.1 = .drain →
      e.2 ≤ sHomeExcess g w inp) := by
  set route := sRouteWith rule g w inp.aMain ops with hroute
  set pool := sPool route inp.aTier inp.bTier with hpool
  have hbAll := hI.bNodup
  unfold SInputs.bAll at hbAll
  rw [List.map_append, List.nodup_append] at hbAll
  have cx : Ctx g w inp pool :=
    { valid := hg
      pA := ro.poolIn
      pB := ro.poolNotB
      bTnd := hbAll.2.1
      bMnd := hbAll.1
      bdis := fun r hr hk => by
        obtain ⟨s, hs, e⟩ := List.mem_map.1 hk
        exact hbAll.2.2 _ (List.mem_map_of_mem hr) _ (List.mem_map_of_mem hs) e.symm
      bHome := hI.bHome
      bLen := hI.bLen }
  set fin := sFinish g w inp route.main (sLeaves g w pool) with hfin
  have G : GInv g w inp pool (fun _ => True) (fun _ _ => True) (fun _ => True) fin.ins fin :=
    ginv_finish cx ro.len ro.ok ro.poolNd
  have hleft : ∀ r ∈ fin.leaves.flatten, r ∈ pool ∧
      Blocks g r.key (fin.main.getD (sHome g w r) []) := by
    intro r hr
    obtain ⟨R, hR⟩ := mem_flatten_getD hr
    exact ⟨(G.lv R r hR).1, G.aD R r hR trivial⟩
  have hbcB : ∀ r ∈ fin.bcopy.flatten, r ∈ inp.bTier.flatten ∧
      Blocks g r.key (fin.main.getD (sHome g w r) []) := by
    intro r hr
    obtain ⟨p, hp⟩ := mem_flatten_getD hr
    exact ⟨G.bc.subset hr, G.bD p r hp trivial⟩
  have hbc : ∀ r ∈ fin.bcopy.flatten, r.key ∈ inp.bTier.flatten.map Rec.key :=
    fun r hr => List.mem_map_of_mem (G.bc.subset hr)
  have hbcnd : (fin.bcopy.flatten.map Rec.key).Nodup := cx.bTnd.sublist (G.bc.map _)
  -- first drain
  have hA : fin.leaves.flatten.length + fin.bcopy.flatten.length ≤ sHomeExcess g w inp := by
    have := count_main hg fin.main G.ok (fin.leaves.flatten ++ fin.bcopy.flatten) ?_ ?_
    · simp only [List.length_append] at this; exact this
    · rw [List.map_append, List.nodup_append]
      refine ⟨G.lvnd, hbcnd, ?_⟩
      intro a ha b hb e
      subst e
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha
      obtain ⟨s, hs, e⟩ := List.mem_map.1 hb
      exact cx.pB r (hleft r hr).1 (e ▸ hbc s hs)
    · intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact ⟨mem_WK_of_a (cx.pA r (hleft r hr).1), (hleft r hr).2⟩
      · exact ⟨mem_WK_of_b (List.mem_append_right _ (hbcB r hr).1), (hbcB r hr).2⟩
  -- last drain
  have hB : ∀ p : Rec → Bool,
      (fin.leaves.flatten.filter fun r => !(fin.ins.map Rec.key).contains r.key).length +
        fin.bcopy.flatten.length + (fin.ins.filter p).length ≤ sHomeExcess g w inp := by
    intro p
    have := count_main hg fin.main G.ok
      ((fin.leaves.flatten.filter fun r => !(fin.ins.map Rec.key).contains r.key) ++
        fin.bcopy.flatten ++ fin.ins.filter p) ?_ ?_
    · simp only [List.length_append] at this; exact this
    · rw [List.map_append, List.map_append, List.nodup_append, List.nodup_append]
      refine ⟨⟨G.lvnd.sublist (List.filter_sublist.map _), hbcnd, ?_⟩,
        G.insnd.sublist (List.filter_sublist.map _), ?_⟩
      · intro a ha b hb e
        subst e
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha
        obtain ⟨s, hs, e⟩ := List.mem_map.1 hb
        exact cx.pB r (hleft r (List.mem_filter.1 hr).1).1 (e ▸ hbc s hs)
      · intro a ha b hb e
        subst e
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
        have hxi := (List.mem_filter.1 hx).1
        rcases List.mem_append.1 ha with ha | ha
        · obtain ⟨r, hr, e⟩ := List.mem_map.1 ha
          have := (List.mem_filter.1 hr).2
          rw [e] at this
          simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_mem,
            decide_eq_false_iff_not] at this
          exact this (List.mem_map_of_mem hxi)
        · obtain ⟨s, hs, e⟩ := List.mem_map.1 ha
          exact cx.bdis x (G.ins x hxi).1 (e ▸ hbc s hs)
    · intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · rcases List.mem_append.1 hr with hr | hr
        · have h := hleft r (List.mem_filter.1 hr).1
          exact ⟨mem_WK_of_a (cx.pA r h.1), h.2⟩
        · exact ⟨mem_WK_of_b (List.mem_append_right _ (hbcB r hr).1), (hbcB r hr).2⟩
      · have h := G.ins r (List.mem_filter.1 hr).1
        exact ⟨mem_WK_of_b (List.mem_append_left _ h.1), h.2.2⟩
  have hD := sdrain_bound fin _ hA hB
  have htrace : (sReferenceWith rule g w inp ops).trace =
      route.trace ++ sDfsTrace g w pool ++ fin.trace ++ (sDrain fin).2 := rfl
  rw [htrace]
  constructor
  · intro e he het
    simp only [List.mem_append] at he
    rcases he with ((he | he) | he) | he
    · rcases ro.tr e he with ⟨j, c, hj⟩ | hj <;> rw [hj] at het <;> cases het
    · obtain ⟨d, c, hj⟩ := sDfsTrace_tests g w pool e he; rw [hj] at het; cases het
    · exact (G.tr e he).2
    · rw [(hD e he).1] at het; cases het
  · intro e he het
    simp only [List.mem_append] at he
    rcases he with ((he | he) | he) | he
    · rcases ro.tr e he with ⟨j, c, hj⟩ | hj <;> rw [hj] at het <;> cases het
    · obtain ⟨d, c, hj⟩ := sDfsTrace_tests g w pool e he; rw [hj] at het; cases het
    · rw [(G.tr e he).1] at het; cases het
    · exact (hD e he).2

end RebuildBound.S4b
