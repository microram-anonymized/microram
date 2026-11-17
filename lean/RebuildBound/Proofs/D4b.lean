import RebuildBound.Proofs.ListAux.Occupancy
import RebuildBound.Proofs.D4b.Finish

/-!
# D4b: first-failure inventory, insertion stash and output tier (T4b)

Both bounds hold for the reference execution on every word assignment:
every insertion-trace quantity and every drain-trace quantity is at most
`homeExcess = Σ_v (X_v - C)₊`. A first failure at `.insertion` (resp.
`.drain`) is a trace entry whose quantity exceeds `S`, hence `S < homeExcess`.

* `D4b/Basic`: lists, `fill`, and the counting lemma `count_main`: distinct
  union keys, each absent from its full home (`Blocks`), number at most
  `homeExcess`, since a full home holds `C` distinct union keys of that home.
* `D4b/Route`: after A's route every main record sits at its home, buckets
  have `C` lanes, and main with the stashes is a permutation of A's main, so
  buckets and the swept pool are distinct by key.
* `D4b/Offers`, `D4b/Finish`: the finish invariant `GInv`. A record shed by a
  fill, or left over by an offer, is shut out of a full home; A's offer
  leaves a full home unchanged, B's tier offer keeps it full (each freed lane
  held a key of a candidate) and adds only B-tier keys. Hence the insertion
  stash is distinct B-main records shut out of full homes whenever it is
  tested.
* `ListAux/Occupancy`: the drain's quantities are prefix sums of the leftovers, then
  the deduplicated leftovers plus the insertion stash; each is a list of
  distinct keys shut out of full homes.
-/

namespace RebuildBound.D4b

open RebuildBound.Model

theorem firstFailure_mem {g : Geom} {caps : Caps} {trace : List (Test × Nat)} {t : Test}
    (h : firstFailure g caps trace = some t) :
    ∃ e ∈ trace, e.1 = t ∧ exceeds (caps.capOf g e.1) e.2 = true := by
  unfold firstFailure at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  have hp := List.find?_some he
  exact ⟨e, List.mem_of_find?_eq_some he, rfl, hp⟩

theorem dfsTrace_tests (g : Geom) (w : Model.LogicalKey → Nat) (pool : List Rec) :
    ∀ e ∈ dfsTrace g w pool, ∃ d c, e.1 = Test.dfs d c := by
  intro e he
  unfold dfsTrace at he
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at he
  obtain ⟨d, _, c, _, rfl⟩ := he
  exact ⟨d, c, rfl⟩

/-- Every insertion-trace and drain-trace quantity of the reference execution
is at most `homeExcess`. -/
theorem reference_bounds {rule : CapRule} {g : Geom} {TA TB : Nat} {wOld w : Model.LogicalKey → Nat}
    {inp : Inputs} (hv : rule.Valid) (hI : InputValid g TA TB wOld w inp) :
    (∀ e ∈ (reference rule g w inp).trace, e.1 = .insertion → e.2 ≤ homeExcess g w inp) ∧
    (∀ e ∈ (reference rule g w inp).trace, e.1 = .drain → e.2 ≤ homeExcess g w inp) := by
  have ro := routeOut hv hI
  set route := routeA rule g w inp.aMain with hroute
  set pool := poolA route inp.aTier inp.bTier with hpool
  have hbAll := hI.bNodup
  unfold Inputs.bAll at hbAll
  rw [List.map_append, List.nodup_append] at hbAll
  have cx : Ctx g w inp pool :=
    { pA := ro.poolIn
      pB := ro.poolNotB
      bTnd := hbAll.2.1
      bMnd := hbAll.1
      bdis := fun r hr hk => by
        obtain ⟨s, hs, e⟩ := List.mem_map.1 hk
        exact hbAll.2.2 _ (List.mem_map_of_mem hr) _ (List.mem_map_of_mem hs) e.symm
      bHome := hI.bHome
      bLen := hI.bLen }
  set fin := finish g w inp route.main (leavesOf g w pool) with hfin
  have G : GInv g w inp pool (fun _ => True) (fun _ => True) (fun _ => True) fin.ins fin :=
    ginv_finish cx ro.len ro.ok ro.poolNd
  -- leftovers of A
  have hleft : ∀ r ∈ fin.leaves.flatten, r ∈ pool ∧
      Blocks g r.key (fin.main.getD (home g w r) []) := by
    intro r hr
    obtain ⟨R, hR⟩ := mem_flatten_getD hr
    exact ⟨(G.lv R r hR).1, G.aD R r hR trivial⟩
  have hbc : ∀ r ∈ fin.bcopy, r.key ∈ inp.bTier.map Rec.key :=
    fun r hr => List.mem_map_of_mem (G.bc.subset hr)
  have hbcnd : (fin.bcopy.map Rec.key).Nodup := cx.bTnd.sublist (G.bc.map _)
  -- first drain
  have hA : fin.leaves.flatten.length + fin.bcopy.length ≤ homeExcess g w inp := by
    have := count_main fin.main G.ok (fin.leaves.flatten ++ fin.bcopy) ?_ ?_
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
      · exact ⟨mem_WK_of_b (List.mem_append_right _ (G.bc.subset hr)), G.bD r hr trivial⟩
  -- last drain
  have hB : ∀ p : Rec → Bool,
      (fin.leaves.flatten.filter fun r => !(fin.ins.map Rec.key).contains r.key).length +
        fin.bcopy.length + (fin.ins.filter p).length ≤ homeExcess g w inp := by
    intro p
    have := count_main fin.main G.ok
      ((fin.leaves.flatten.filter fun r => !(fin.ins.map Rec.key).contains r.key) ++ fin.bcopy ++
        fin.ins.filter p) ?_ ?_
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
        · exact ⟨mem_WK_of_b (List.mem_append_right _ (G.bc.subset hr)), G.bD r hr trivial⟩
      · have h := G.ins r (List.mem_filter.1 hr).1
        exact ⟨mem_WK_of_b (List.mem_append_left _ h.1), h.2.2⟩
  have hD := drain_bound fin _ hA hB
  have htrace : (reference rule g w inp).trace =
      route.trace ++ dfsTrace g w pool ++ fin.trace ++ (drain fin).2 := rfl
  rw [htrace]
  constructor
  · intro e he het
    simp only [List.mem_append] at he
    rcases he with ((he | he) | he) | he
    · obtain ⟨j, hj⟩ := ro.tr e he; rw [hj] at het; cases het
    · obtain ⟨d, c, hj⟩ := dfsTrace_tests g w pool e he; rw [hj] at het; cases het
    · exact (G.tr e he).2
    · rw [(hD e he).1] at het; cases het
  · intro e he het
    simp only [List.mem_append] at he
    rcases he with ((he | he) | he) | he
    · obtain ⟨j, hj⟩ := ro.tr e he; rw [hj] at het; cases het
    · obtain ⟨d, c, hj⟩ := dfsTrace_tests g w pool e he; rw [hj] at het; cases het
    · rw [(G.tr e he).1] at het; cases het
    · exact (hD e he).2

end RebuildBound.D4b

theorem RebuildBound.T4b : RebuildBound.Spec.T4b_statement := by
  intro rule g caps TA TB wOld w inp hv hI
  obtain ⟨hins, hdr⟩ := RebuildBound.D4b.reference_bounds hv hI
  constructor
  · intro S hS hff
    obtain ⟨e, he, het, hex⟩ := RebuildBound.D4b.firstFailure_mem hff
    rw [het] at hex
    simp only [RebuildBound.Model.Caps.capOf, hS, RebuildBound.Model.exceeds,
      decide_eq_true_eq] at hex
    exact Nat.lt_of_lt_of_le hex (hins e he het)
  · intro S hS hff
    obtain ⟨e, he, het, hex⟩ := RebuildBound.D4b.firstFailure_mem hff
    rw [het] at hex
    simp only [RebuildBound.Model.Caps.capOf, hS, RebuildBound.Model.exceeds,
      decide_eq_true_eq] at hex
    exact Nat.lt_of_lt_of_le hex (hdr e he het)
