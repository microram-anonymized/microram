import RebuildBound.Proofs.S4b.Offers

/-!
# S4b, B's insertion with the fused offers

The invariant `GInv` of the finish phase, preserved by each offer and by the
insertion of one B bucket. Its field `tr` is the insertion half of ST4b: every
insertion-trace quantity is at most `sHomeExcess`.
-/

namespace RebuildBound.S4b

open RebuildBound.Model
open RebuildBound.D4b (nodup_of_subperm getD_set_self getD_set_of_ne getD_sublist_flatten
  mem_flatten_getD flatten_set_sublist fill_snd fill_of_full fill_recs_perm keys_eq mem_keys
  free_zero_of_full fill_placed_eq mem_getD_set_self' mem_getD_set' length_filter_split
  recs_sublist_flatMap not_mem_keys_clear)

/-- Facts about the inputs and the swept pool used throughout the finish. -/
structure Ctx (g : SepGeom) (w : Model.LogicalKey → Nat) (inp : SInputs) (pool : List Rec) : Prop where
  valid : g.Valid
  pA : ∀ r ∈ pool, r ∈ inp.aAll
  pB : ∀ r ∈ pool, r.key ∉ inp.bTier.flatten.map Rec.key
  bTnd : (inp.bTier.flatten.map Rec.key).Nodup
  bMnd : ((inp.bMain.flatMap Bucket.recs).map Rec.key).Nodup
  bdis : ∀ r ∈ inp.bMain.flatMap Bucket.recs, r.key ∉ inp.bTier.flatten.map Rec.key
  bHome : ∀ i < g.U, ∀ r ∈ (inp.bMain.getD i []).recs, w r.key % g.U = i
  bLen : inp.bMain.length = g.U

/-- The invariant of the finish phase. Homes `v` with `Pa v` have offered A's
candidates, homes `v` with `Pb p v` B's tier candidates of page `p`; `I` is the
insertion stash (with homes `Pi`). -/
structure GInv (g : SepGeom) (w : Model.LogicalKey → Nat) (inp : SInputs) (pool : List Rec)
    (Pa : Nat → Prop) (Pb : Nat → Nat → Prop) (Pi : Nat → Prop) (I : List Rec) (st : SFin) :
    Prop where
  len : st.main.length = g.N
  ok : ∀ v < g.N, HomeOK g w inp v (st.main.getD v [])
  lv : ∀ R, ∀ r ∈ st.leaves.getD R [], r ∈ pool ∧ sRange g w r = R
  lvnd : (st.leaves.flatten.map Rec.key).Nodup
  bc : List.Sublist st.bcopy.flatten inp.bTier.flatten
  aD : ∀ R, ∀ r ∈ st.leaves.getD R [], Pa (sHome g w r) →
    Blocks g r.key (st.main.getD (sHome g w r) [])
  bD : ∀ p, ∀ r ∈ st.bcopy.getD p [], Pb p (sHome g w r) →
    Blocks g r.key (st.main.getD (sHome g w r) [])
  ins : ∀ x ∈ I, x ∈ inp.bMain.flatMap Bucket.recs ∧ Pi (sHome g w x) ∧
    Blocks g x.key (st.main.getD (sHome g w x) [])
  insnd : (I.map Rec.key).Nodup
  tr : ∀ e ∈ st.trace, e.1 = STest.insertion ∧ e.2 ≤ sHomeExcess g w inp

section
variable {g : SepGeom} {w : Model.LogicalKey → Nat} {inp : SInputs} {pool : List Rec}
  {Pa : Nat → Prop} {Pb : Nat → Nat → Prop} {Pi : Nat → Prop} {I : List Rec} {st : SFin}

theorem GInv.mono (hg : g.Valid) {Pa' : Nat → Prop} {Pb' : Nat → Nat → Prop} {Pi' : Nat → Prop}
    (h : GInv g w inp pool Pa Pb Pi I st)
    (ha : ∀ v < g.N, Pa' v → Pa v)
    (hb : ∀ p, ∀ r ∈ st.bcopy.getD p [], Pb' p (sHome g w r) → Pb p (sHome g w r))
    (hi : ∀ v < g.N, Pi v → Pi' v) : GInv g w inp pool Pa' Pb' Pi' I st where
  len := h.len
  ok := h.ok
  lv := h.lv
  lvnd := h.lvnd
  bc := h.bc
  aD R r hr hp := h.aD R r hr (ha _ (sHome_lt hg w r) hp)
  bD p r hr hp := h.bD p r hr (hb p r hr hp)
  ins x hx := ⟨(h.ins x hx).1, hi _ (sHome_lt hg w x) (h.ins x hx).2.1, (h.ins x hx).2.2⟩
  insnd := h.insnd
  tr := h.tr

theorem leaf_sublist (st : SFin) (R : Nat) :
    List.Sublist ((st.leaves.getD R []).map Rec.key) (st.leaves.flatten.map Rec.key) :=
  (getD_sublist_flatten st.leaves R).map _

/-- Keys of different pages of a list of pages with distinct keys differ. -/
theorem pages_disjoint : ∀ (l : List (List Rec)), (l.flatten.map Rec.key).Nodup →
    ∀ p q, p ≠ q → ∀ r ∈ l.getD p [], ∀ s ∈ l.getD q [], r.key ≠ s.key
  | [], _, p, q, _, r, hr, _, _, _ => by simp at hr
  | a :: t, h, p, q, hpq, r, hr, s, hs, e => by
    simp only [List.flatten_cons, List.map_append, List.nodup_append] at h
    obtain ⟨h1, h2, h3⟩ := h
    cases p with
    | zero =>
      cases q with
      | zero => exact hpq rfl
      | succ q =>
        simp only [List.getD_cons_zero] at hr
        simp only [List.getD_cons_succ] at hs
        exact h3 r.key (List.mem_map_of_mem hr) s.key
          (List.mem_map_of_mem ((getD_sublist_flatten t q).subset hs)) e
    | succ p =>
      cases q with
      | zero =>
        simp only [List.getD_cons_succ] at hr
        simp only [List.getD_cons_zero] at hs
        exact h3 s.key (List.mem_map_of_mem hs) r.key
          (List.mem_map_of_mem ((getD_sublist_flatten t p).subset hr)) e.symm
      | succ q =>
        simp only [List.getD_cons_succ] at hr hs
        exact pages_disjoint t h2 p q (fun e' => hpq (by omega)) r hr s hs e

/-! ### A's offer -/

theorem sOfferA_getD (ci v : Nat) (st : SFin) (h : v ≠ ci) :
    (sOfferA g w ci st).main.getD v [] = st.main.getD v [] := by
  rw [sOfferA_eq]; exact getD_set_of_ne _ (Ne.symm h) _ _

theorem sOfferA_getD_self {ci : Nat} {st : SFin} (h : ci < st.main.length) :
    (sOfferA g w ci st).main.getD ci [] = (fill (st.main.getD ci []) (aStale g w ci st)).1 := by
  rw [sOfferA_eq]; exact getD_set_self _ h _ _

/-- A's offer keeps every shut-out key shut out. -/
theorem sOfferA_blocks (hG : GInv g w inp pool Pa Pb Pi I st) {ci v : Nat} {x : Model.LogicalKey}
    (hv : v < g.N) (hb : Blocks g x (st.main.getD v [])) :
    Blocks g x ((sOfferA g w ci st).main.getD v []) := by
  by_cases e : v = ci
  · subst e
    rw [sOfferA_getD_self (by rw [hG.len]; exact hv),
      fill_of_blocks (hG.ok v hv).len hb]
    exact hb
  · rw [sOfferA_getD ci v st e]; exact hb

theorem ginv_offerA (cx : Ctx g w inp pool) {ci : Nat} (hci : ci < g.N)
    (h : GInv g w inp pool Pa Pb Pi I st) :
    GInv g w inp pool (fun v => Pa v ∨ v = ci) Pb Pi I (sOfferA g w ci st) := by
  have hciL : ci < st.main.length := by rw [h.len]; exact hci
  have hBok := h.ok ci hci
  have hL : ∀ r ∈ aStale g w ci st, r ∈ st.leaves.getD (ci / 2 ^ g.I) [] ∧
      sHome g w r = ci ∧ r.key ∉ (st.main.getD ci []).keys := by
    intro r hr
    unfold aStale aCand at hr
    obtain ⟨hr, h2⟩ := List.mem_filter.1 hr
    obtain ⟨hr, h1⟩ := List.mem_filter.1 hr
    exact ⟨hr, by simpa using h1, by simpa using h2⟩
  have hLnd : ((aStale g w ci st).map Rec.key).Nodup := by
    refine h.lvnd.sublist (List.Sublist.trans ?_ (leaf_sublist st (ci / 2 ^ g.I)))
    unfold aStale aCand
    exact (List.filter_sublist.trans List.filter_sublist).map _
  have hnew : HomeOK g w inp ci (fill (st.main.getD ci []) (aStale g w ci st)).1 := by
    refine homeOK_fill hBok _ ?_ hLnd (fun r hr => (hL r hr).2.2)
    intro r hr
    exact ⟨(hL r hr).2.1, mem_WK_of_a (cx.pA r (h.lv _ r (hL r hr).1).1)⟩
  have hlvold : ∀ R r, r ∈ (sOfferA g w ci st).leaves.getD R [] → r ∈ st.leaves.getD R [] := by
    intro R r hr
    rw [sOfferA_eq] at hr
    rcases mem_getD_set' hr with ⟨e, hr'⟩ | hr'
    · rw [e]; exact (List.mem_filter.1 hr').1
    · exact hr'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sOfferA_eq]; simp [h.len]
  · intro v hv
    by_cases e : v = ci
    · subst e; rw [sOfferA_getD_self hciL]; exact hnew
    · rw [sOfferA_getD ci v st e]; exact h.ok v hv
  · intro R r hr; exact h.lv R r (hlvold R r hr)
  · rw [sOfferA_eq]
    exact h.lvnd.sublist ((flatten_set_sublist _ _ _ List.filter_sublist).map _)
  · exact h.bc
  · intro R r hr hp
    rcases hp with hp | hp
    · exact sOfferA_blocks h (sHome_lt cx.valid w r) (h.aD R r (hlvold R r hr) hp)
    · have hR : R = ci / 2 ^ g.I := by
        rw [← (h.lv R r (hlvold R r hr)).2]; show sHome g w r / 2 ^ g.I = _; rw [hp]
      subst hR
      rw [sOfferA_eq] at hr
      have hr := mem_getD_set_self' hr
      obtain ⟨hr, hgone⟩ := List.mem_filter.1 hr
      have hgone : r.key ∉ aGone g w ci st := by simpa using hgone
      have hin : r.key ∉ (st.main.getD ci []).keys := by
        intro hk
        apply hgone
        unfold aGone
        refine List.mem_map.2 ⟨r, List.mem_append_left _ (List.mem_filter.2 ⟨?_, ?_⟩), rfl⟩
        · exact List.mem_filter.2 ⟨hr, by simpa using hp⟩
        · simpa using hk
      have hst : r ∈ aStale g w ci st := by
        unfold aStale
        exact List.mem_filter.2 ⟨List.mem_filter.2 ⟨hr, by simpa using hp⟩, by simpa using hin⟩
      have hnt : r.key ∉ ((aStale g w ci st).take (min (aStale g w ci st).length
          ((st.main.getD ci []).countP (·.isNone)))).map Rec.key := by
        rw [← fill_placed_eq]
        intro hk
        apply hgone
        unfold aGone
        rw [List.map_append]
        exact List.mem_append_right _ hk
      show Blocks g r.key ((sOfferA g w ci st).main.getD (sHome g w r) [])
      rw [hp, sOfferA_getD_self hciL]
      exact blocks_fill hBok.len hst hin hnt
  · intro p r hr hp
    exact sOfferA_blocks h (sHome_lt cx.valid w r) (h.bD p r hr hp)
  · intro x hx
    obtain ⟨h1, h2, h3⟩ := h.ins x hx
    exact ⟨h1, h2, sOfferA_blocks h (sHome_lt cx.valid w x) h3⟩
  · exact h.insnd
  · exact h.tr

/-! ### B's tier offers -/

theorem sOfferPage_getD (ci v pg : Nat) (st : SFin) (h : v ≠ ci) :
    (sOfferPage g w ci st pg).main.getD v [] = st.main.getD v [] := by
  rw [sOfferPage_eq]; exact getD_set_of_ne _ (Ne.symm h) _ _

theorem sOfferPage_getD_self {ci pg : Nat} {st : SFin} (h : ci < st.main.length) :
    (sOfferPage g w ci st pg).main.getD ci [] =
      (fill (bClr g w ci pg st) (bFc g w ci pg st)).1 := by
  rw [sOfferPage_eq]; exact getD_set_self _ h _ _

theorem bFc_sub (ci pg : Nat) (st : SFin) {r : Rec} (hr : r ∈ bFc g w ci pg st) :
    r ∈ st.bcopy.getD pg [] := (List.mem_filter.1 hr).1

/-- A page's offer keeps shut out every key outside that page. -/
theorem sOfferPage_blocks (hG : GInv g w inp pool Pa Pb Pi I st) {ci v : Nat} {x : Model.LogicalKey} {pg : Nat}
    (hv : v < g.N) (hx : ∀ s ∈ st.bcopy.getD pg [], s.key ≠ x)
    (hb : Blocks g x (st.main.getD v [])) :
    Blocks g x ((sOfferPage g w ci st pg).main.getD v []) := by
  by_cases e : v = ci
  · subst e
    rw [sOfferPage_getD_self (by rw [hG.len]; exact hv)]
    refine ⟨full_fill_clear (hG.ok v hv) hb.1 _, ?_⟩
    apply not_mem_keys_fill
    · intro hk
      rw [bClr, keys_eq, D1Lemmas.clear_recs] at hk
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hk
      exact hb.2 (List.mem_map_of_mem (List.mem_filter.1 hr).1)
    · intro r hr e
      exact hx r (bFc_sub _ _ _ hr) e
  · rw [sOfferPage_getD ci v pg st e]; exact hb

theorem ginv_offerPage (cx : Ctx g w inp pool) {ci : Nat} (hci : ci < g.N) (pg : Nat)
    (h : GInv g w inp pool Pa Pb Pi I st) :
    GInv g w inp pool Pa (fun p v => Pb p v ∨ (p = pg ∧ v = ci)) Pi I (sOfferPage g w ci st pg) := by
  have hciL : ci < st.main.length := by rw [h.len]; exact hci
  have hBok := h.ok ci hci
  have hbcnd : (st.bcopy.flatten.map Rec.key).Nodup := cx.bTnd.sublist (h.bc.map _)
  have hfc : ∀ r ∈ bFc g w ci pg st, r ∈ st.bcopy.getD pg [] ∧ sHome g w r = ci := by
    intro r hr
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hr
    exact ⟨h1, by simpa using h2⟩
  have hpgsub : ∀ s ∈ st.bcopy.getD pg [], s ∈ inp.bTier.flatten :=
    fun s hs => h.bc.subset ((getD_sublist_flatten st.bcopy pg).subset hs)
  have hfcnd : ((bFc g w ci pg st).map Rec.key).Nodup := by
    refine hbcnd.sublist (List.Sublist.trans ?_ ((getD_sublist_flatten st.bcopy pg).map _))
    exact (List.filter_sublist).map _
  have hclr : ∀ r ∈ bFc g w ci pg st, r.key ∉ (bClr g w ci pg st).keys := by
    intro r hr hk
    rw [bClr, keys_eq, D1Lemmas.clear_recs] at hk
    obtain ⟨s, hs, e⟩ := List.mem_map.1 hk
    have := (List.mem_filter.1 hs).2
    rw [e] at this
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_mem,
      decide_eq_false_iff_not] at this
    exact this (List.mem_map_of_mem hr)
  have hnew : HomeOK g w inp ci (fill (bClr g w ci pg st) (bFc g w ci pg st)).1 := by
    refine homeOK_fill (homeOK_clear hBok _) _ ?_ hfcnd hclr
    intro r hr
    exact ⟨(hfc r hr).2, mem_WK_of_b (List.mem_append_right _ (hpgsub r (hfc r hr).1))⟩
  have hbclr : (bClr g w ci pg st).length = g.C := by
    rw [bClr, D1Lemmas.clear_length]; exact hBok.len
  have hxB : ∀ x : Model.LogicalKey, x ∉ inp.bTier.flatten.map Rec.key →
      ∀ s ∈ st.bcopy.getD pg [], s.key ≠ x := by
    intro x hx s hs e
    apply hx
    rw [← e]
    exact List.mem_map_of_mem (hpgsub s hs)
  refine ⟨?_, ?_, h.lv, h.lvnd, ?_, ?_, ?_, ?_, h.insnd, h.tr⟩
  · rw [sOfferPage_eq]; simp [h.len]
  · intro v hv
    by_cases e : v = ci
    · subst e; rw [sOfferPage_getD_self hciL]; exact hnew
    · rw [sOfferPage_getD ci v pg st e]; exact h.ok v hv
  · exact (flatten_set_sublist st.bcopy pg _ List.filter_sublist).trans h.bc
  · intro R r hr hp
    exact sOfferPage_blocks h (sHome_lt cx.valid w r) (hxB _ (cx.pB r (h.lv R r hr).1))
      (h.aD R r hr hp)
  · intro p r hr hp
    by_cases hpp : p = pg
    · subst hpp
      rw [sOfferPage_eq] at hr
      have hr := mem_getD_set_self' hr
      obtain ⟨hr, hpl⟩ := List.mem_filter.1 hr
      by_cases e : sHome g w r = ci
      · have hpl : r.key ∉ bPlaced g w ci p st := by simpa using hpl
        have hrf : r ∈ bFc g w ci p st := List.mem_filter.2 ⟨hr, by simpa using e⟩
        have hnt : r.key ∉ ((bFc g w ci p st).take (min (bFc g w ci p st).length
            ((bClr g w ci p st).countP (·.isNone)))).map Rec.key := by
          rw [← fill_placed_eq]; exact hpl
        show Blocks g r.key ((sOfferPage g w ci st p).main.getD (sHome g w r) [])
        rw [e, sOfferPage_getD_self hciL]
        exact blocks_fill hbclr hrf (hclr r hrf) hnt
      · have hpb : Pb p (sHome g w r) := by
          rcases hp with hp | hp
          · exact hp
          · exact absurd hp.2 e
        rw [sOfferPage_getD ci _ p st e]
        exact h.bD p r hr hpb
    · have hr' : r ∈ st.bcopy.getD p [] := by
        rw [sOfferPage_eq] at hr
        rwa [getD_set_of_ne _ (Ne.symm hpp)] at hr
      have hpb : Pb p (sHome g w r) := by
        rcases hp with hp | hp
        · exact hp
        · exact absurd hp.1 hpp
      exact sOfferPage_blocks h (sHome_lt cx.valid w r)
        (fun s hs e => pages_disjoint st.bcopy hbcnd p pg hpp r hr' s hs e.symm)
        (h.bD p r hr' hpb)
  · intro x hx
    obtain ⟨h1, h2, h3⟩ := h.ins x hx
    exact ⟨h1, h2, sOfferPage_blocks h (sHome_lt cx.valid w x) (hxB _ (cx.bdis x h1)) h3⟩

theorem sOfferPage_bcopy_length (ci pg : Nat) (st : SFin) :
    (sOfferPage g w ci st pg).bcopy.length = st.bcopy.length := by
  rw [sOfferPage_eq]; simp

theorem ginv_offerB (cx : Ctx g w inp pool) {ci : Nat} (hci : ci < g.N)
    (h : GInv g w inp pool Pa Pb Pi I st) :
    GInv g w inp pool Pa (fun p v => Pb p v ∨ v = ci) Pi I (sOfferB g w ci st) := by
  have key : ∀ m, GInv g w inp pool Pa (fun p v => Pb p v ∨ (v = ci ∧ p < m)) Pi I
      ((List.range m).foldl (sOfferPage g w ci) st) ∧
      ((List.range m).foldl (sOfferPage g w ci) st).bcopy.length = st.bcopy.length := by
    intro m
    induction m with
    | zero =>
      refine ⟨h.mono cx.valid (fun _ _ => id) ?_ (fun _ _ => id), rfl⟩
      intro p r _ hp
      rcases hp with hp | hp
      · exact hp
      · omega
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine ⟨?_, by rw [sOfferPage_bcopy_length, ih.2]⟩
      refine (ginv_offerPage cx hci m ih.1).mono cx.valid (fun _ _ => id) ?_ (fun _ _ => id)
      intro p r _ hp
      rcases hp with hp | hp
      · exact Or.inl (Or.inl hp)
      · by_cases hpm : p < m
        · exact Or.inl (Or.inr ⟨hp.1, hpm⟩)
        · exact Or.inr ⟨by omega, hp.1⟩
  obtain ⟨G, hl⟩ := key st.bcopy.length
  unfold sOfferB
  refine G.mono cx.valid (fun _ _ => id) ?_ (fun _ _ => id)
  intro p r hr hq
  rcases hq with hq | hq
  · exact Or.inl hq
  · refine Or.inr ⟨hq, ?_⟩
    by_contra hp
    rw [List.getD_eq_default _ _ (by omega)] at hr
    simp at hr

end

end RebuildBound.S4b
