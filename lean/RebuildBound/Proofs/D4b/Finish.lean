import RebuildBound.Proofs.D4b.Offers

/-!
# D4b, B's insertion with the fused offers

The invariant `GInv` of the finish phase, preserved by each offer and by the
insertion of one B bucket. Its field `tr` is the insertion half of T4b: every
insertion-trace quantity is at most `homeExcess`.
-/

namespace RebuildBound.D4b

open RebuildBound.Model

/-- Facts about the inputs and the swept pool used throughout the finish. -/
structure Ctx (g : Geom) (w : Model.LogicalKey → Nat) (inp : Inputs) (pool : List Rec) : Prop where
  pA : ∀ r ∈ pool, r ∈ inp.aAll
  pB : ∀ r ∈ pool, r.key ∉ inp.bTier.map Rec.key
  bTnd : (inp.bTier.map Rec.key).Nodup
  bMnd : ((inp.bMain.flatMap Bucket.recs).map Rec.key).Nodup
  bdis : ∀ r ∈ inp.bMain.flatMap Bucket.recs, r.key ∉ inp.bTier.map Rec.key
  bHome : ∀ i < g.U, ∀ r ∈ (inp.bMain.getD i []).recs, w r.key % g.U = i
  bLen : inp.bMain.length = g.U

/-- The invariant of the finish phase. Homes `v` with `Pa v` have offered A's
candidates, homes with `Pb v` B's tier candidates; `I` is the insertion stash
(with homes `Pi`). -/
structure GInv (g : Geom) (w : Model.LogicalKey → Nat) (inp : Inputs) (pool : List Rec)
    (Pa Pb Pi : Nat → Prop) (I : List Rec) (st : FinState) : Prop where
  len : st.main.length = g.homes
  ok : ∀ v < g.homes, HomeOK g w inp v (st.main.getD v [])
  lv : ∀ R, ∀ r ∈ st.leaves.getD R [], r ∈ pool ∧ rangeOf g w r = R
  lvnd : (st.leaves.flatten.map Rec.key).Nodup
  bc : List.Sublist st.bcopy inp.bTier
  aD : ∀ R, ∀ r ∈ st.leaves.getD R [], Pa (home g w r) →
    Blocks g r.key (st.main.getD (home g w r) [])
  bD : ∀ r ∈ st.bcopy, Pb (home g w r) → Blocks g r.key (st.main.getD (home g w r) [])
  ins : ∀ x ∈ I, x ∈ inp.bMain.flatMap Bucket.recs ∧ Pi (home g w x) ∧
    Blocks g x.key (st.main.getD (home g w x) [])
  insnd : (I.map Rec.key).Nodup
  tr : ∀ e ∈ st.trace, e.1 = Test.insertion ∧ e.2 ≤ homeExcess g w inp

section
variable {g : Geom} {w : Model.LogicalKey → Nat} {inp : Inputs} {pool : List Rec}
  {Pa Pb Pi : Nat → Prop} {I : List Rec} {st : FinState}

theorem home_lt (g : Geom) (w : Model.LogicalKey → Nat) (r : Rec) : home g w r < g.homes :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

theorem home_eq_of_key {g : Geom} {w : Model.LogicalKey → Nat} {r s : Rec} (h : r.key = s.key) :
    home g w r = home g w s := by simp [home, h]

theorem GInv.mono {Pa' Pb' Pi' : Nat → Prop} (h : GInv g w inp pool Pa Pb Pi I st)
    (ha : ∀ v < g.homes, Pa' v → Pa v) (hb : ∀ v < g.homes, Pb' v → Pb v)
    (hi : ∀ v < g.homes, Pi v → Pi' v) : GInv g w inp pool Pa' Pb' Pi' I st where
  len := h.len
  ok := h.ok
  lv := h.lv
  lvnd := h.lvnd
  bc := h.bc
  aD R r hr hp := h.aD R r hr (ha _ (home_lt g w r) hp)
  bD r hr hp := h.bD r hr (hb _ (home_lt g w r) hp)
  ins x hx := ⟨(h.ins x hx).1, hi _ (home_lt g w x) (h.ins x hx).2.1, (h.ins x hx).2.2⟩
  insnd := h.insnd
  tr := h.tr

theorem leaf_sublist (st : FinState) (R : Nat) :
    List.Sublist ((st.leaves.getD R []).map Rec.key) (st.leaves.flatten.map Rec.key) :=
  (getD_sublist_flatten st.leaves R).map _

/-! ### A's offer -/

theorem offerA_getD (ci v : Nat) (st : FinState) (h : v ≠ ci) :
    (offerA g w ci st).main.getD v [] = st.main.getD v [] := by
  rw [offerA_eq]; exact getD_set_of_ne _ (Ne.symm h) _ _

theorem offerA_getD_self {ci : Nat} {st : FinState} (h : ci < st.main.length) :
    (offerA g w ci st).main.getD ci [] = (fill (st.main.getD ci []) (staleA g w ci st)).1 := by
  rw [offerA_eq]; exact getD_set_self _ h _ _

/-- A's offer keeps every shut-out key shut out. -/
theorem offerA_blocks (hG : GInv g w inp pool Pa Pb Pi I st) {ci v : Nat} {x : Model.LogicalKey}
    (hv : v < g.homes) (hb : Blocks g x (st.main.getD v [])) :
    Blocks g x ((offerA g w ci st).main.getD v []) := by
  by_cases e : v = ci
  · subst e
    rw [offerA_getD_self (by rw [hG.len]; exact hv),
      fill_of_blocks (hG.ok v hv).len hb]
    exact hb
  · rw [offerA_getD ci v st e]; exact hb

theorem ginv_offerA (cx : Ctx g w inp pool) {ci : Nat} (hci : ci < g.homes)
    (h : GInv g w inp pool Pa Pb Pi I st) :
    GInv g w inp pool (fun v => Pa v ∨ v = ci) Pb Pi I (offerA g w ci st) := by
  have hciL : ci < st.main.length := by rw [h.len]; exact hci
  have hBok := h.ok ci hci
  have hL : ∀ r ∈ staleA g w ci st, r ∈ st.leaves.getD (ci / 2 ^ g.lo) [] ∧
      home g w r = ci ∧ r.key ∉ (st.main.getD ci []).keys := by
    intro r hr
    unfold staleA candA at hr
    obtain ⟨hr, h2⟩ := List.mem_filter.1 hr
    obtain ⟨hr, h1⟩ := List.mem_filter.1 hr
    exact ⟨hr, by simpa using h1, by simpa using h2⟩
  have hLnd : ((staleA g w ci st).map Rec.key).Nodup := by
    refine h.lvnd.sublist (List.Sublist.trans ?_ (leaf_sublist st (ci / 2 ^ g.lo)))
    unfold staleA candA
    exact (List.filter_sublist.trans List.filter_sublist).map _
  have hnew : HomeOK g w inp ci (fill (st.main.getD ci []) (staleA g w ci st)).1 := by
    refine homeOK_fill hBok _ ?_ hLnd (fun r hr => (hL r hr).2.2)
    intro r hr
    exact ⟨(hL r hr).2.1, mem_WK_of_a (cx.pA r (h.lv _ r (hL r hr).1).1)⟩
  have hlvold : ∀ R r, r ∈ (offerA g w ci st).leaves.getD R [] → r ∈ st.leaves.getD R [] := by
    intro R r hr
    rw [offerA_eq] at hr
    rcases mem_getD_set' hr with ⟨e, hr'⟩ | hr'
    · rw [e]; exact (List.mem_filter.1 hr').1
    · exact hr'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [offerA_eq]; simp [h.len]
  · intro v hv
    by_cases e : v = ci
    · subst e; rw [offerA_getD_self hciL]; exact hnew
    · rw [offerA_getD ci v st e]; exact h.ok v hv
  · intro R r hr; exact h.lv R r (hlvold R r hr)
  · rw [offerA_eq]
    exact h.lvnd.sublist ((flatten_set_sublist _ _ _ List.filter_sublist).map _)
  · exact h.bc
  · intro R r hr hp
    rcases hp with hp | hp
    · exact offerA_blocks h (home_lt g w r) (h.aD R r (hlvold R r hr) hp)
    · have hR : R = ci / 2 ^ g.lo := by
        rw [← (h.lv R r (hlvold R r hr)).2]; show home g w r / 2 ^ g.lo = _; rw [hp]
      subst hR
      rw [offerA_eq] at hr
      have hr := mem_getD_set_self' hr
      obtain ⟨hr, hgone⟩ := List.mem_filter.1 hr
      have hgone : r.key ∉ goneA g w ci st := by simpa using hgone
      have hin : r.key ∉ (st.main.getD ci []).keys := by
        intro hk
        apply hgone
        unfold goneA
        refine List.mem_map.2 ⟨r, List.mem_append_left _ (List.mem_filter.2 ⟨?_, ?_⟩), rfl⟩
        · exact List.mem_filter.2 ⟨hr, by simpa using hp⟩
        · simpa using hk
      have hst : r ∈ staleA g w ci st := by
        unfold staleA
        exact List.mem_filter.2 ⟨List.mem_filter.2 ⟨hr, by simpa using hp⟩, by simpa using hin⟩
      have hnt : r.key ∉ ((staleA g w ci st).take (min (staleA g w ci st).length
          ((st.main.getD ci []).countP (·.isNone)))).map Rec.key := by
        rw [← fill_placed_eq]
        intro hk
        apply hgone
        unfold goneA
        rw [List.map_append]
        exact List.mem_append_right _ hk
      show Blocks g r.key ((offerA g w ci st).main.getD (home g w r) [])
      rw [hp, offerA_getD_self hciL]
      exact blocks_fill hBok.len hst hin hnt
  · intro r hr hp
    exact offerA_blocks h (home_lt g w r) (h.bD r hr hp)
  · intro x hx
    obtain ⟨h1, h2, h3⟩ := h.ins x hx
    exact ⟨h1, h2, offerA_blocks h (home_lt g w x) h3⟩
  · exact h.insnd
  · exact h.tr

/-! ### B's tier offer -/

theorem offerB_getD (ci v : Nat) (st : FinState) (h : v ≠ ci) :
    (offerB g w ci st).main.getD v [] = st.main.getD v [] := by
  rw [offerB_eq]; exact getD_set_of_ne _ (Ne.symm h) _ _

theorem offerB_getD_self {ci : Nat} {st : FinState} (h : ci < st.main.length) :
    (offerB g w ci st).main.getD ci [] = (fill (clrB g w ci st) (fcB g w ci st)).1 := by
  rw [offerB_eq]; exact getD_set_self _ h _ _

theorem fcB_sub (hG : GInv g w inp pool Pa Pb Pi I st) (ci : Nat) {r : Rec}
    (hr : r ∈ fcB g w ci st) : r ∈ inp.bTier :=
  hG.bc.subset (List.mem_filter.1 hr).1

/-- B's tier offer keeps shut out every key outside B's tier. -/
theorem offerB_blocks (hG : GInv g w inp pool Pa Pb Pi I st) {ci v : Nat} {x : Model.LogicalKey}
    (hv : v < g.homes) (hx : x ∉ inp.bTier.map Rec.key) (hb : Blocks g x (st.main.getD v [])) :
    Blocks g x ((offerB g w ci st).main.getD v []) := by
  by_cases e : v = ci
  · subst e
    rw [offerB_getD_self (by rw [hG.len]; exact hv)]
    refine ⟨full_fill_clear (hG.ok v hv) hb.1 _, ?_⟩
    apply not_mem_keys_fill
    · intro hk
      rw [clrB, keys_eq, D1Lemmas.clear_recs] at hk
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hk
      exact hb.2 (List.mem_map_of_mem (List.mem_filter.1 hr).1)
    · intro r hr e
      exact hx (e ▸ List.mem_map_of_mem (fcB_sub hG v hr))
  · rw [offerB_getD ci v st e]; exact hb

theorem ginv_offerB (cx : Ctx g w inp pool) {ci : Nat} (hci : ci < g.homes)
    (h : GInv g w inp pool Pa Pb Pi I st) :
    GInv g w inp pool Pa (fun v => Pb v ∨ v = ci) Pi I (offerB g w ci st) := by
  have hciL : ci < st.main.length := by rw [h.len]; exact hci
  have hBok := h.ok ci hci
  have hfc : ∀ r ∈ fcB g w ci st, r ∈ st.bcopy ∧ home g w r = ci := by
    intro r hr
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hr
    exact ⟨h1, by simpa using h2⟩
  have hfcnd : ((fcB g w ci st).map Rec.key).Nodup :=
    cx.bTnd.sublist ((List.filter_sublist.trans h.bc).map _)
  have hclr : ∀ r ∈ fcB g w ci st, r.key ∉ (clrB g w ci st).keys := by
    intro r hr hk
    rw [clrB, keys_eq, D1Lemmas.clear_recs] at hk
    obtain ⟨s, hs, e⟩ := List.mem_map.1 hk
    have := (List.mem_filter.1 hs).2
    rw [e] at this
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_mem,
      decide_eq_false_iff_not] at this
    exact this (List.mem_map_of_mem hr)
  have hnew : HomeOK g w inp ci (fill (clrB g w ci st) (fcB g w ci st)).1 := by
    refine homeOK_fill (homeOK_clear hBok _) _ ?_ hfcnd hclr
    intro r hr
    exact ⟨(hfc r hr).2, mem_WK_of_b (List.mem_append_right _ (fcB_sub h ci hr))⟩
  have hbcold : ∀ r ∈ (offerB g w ci st).bcopy, r ∈ st.bcopy := by
    intro r hr
    rw [offerB_eq] at hr
    exact (List.mem_filter.1 hr).1
  have hbclr : (clrB g w ci st).length = g.C := by
    rw [clrB, D1Lemmas.clear_length]; exact hBok.len
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [offerB_eq]; simp [h.len]
  · intro v hv
    by_cases e : v = ci
    · subst e; rw [offerB_getD_self hciL]; exact hnew
    · rw [offerB_getD ci v st e]; exact h.ok v hv
  · rw [offerB_eq]; exact h.lv
  · rw [offerB_eq]; exact h.lvnd
  · rw [offerB_eq]; exact List.filter_sublist.trans h.bc
  · intro R r hr hp
    rw [offerB_eq] at hr
    exact offerB_blocks h (home_lt g w r) (cx.pB r (h.lv R r hr).1) (h.aD R r hr hp)
  · intro r hr hp
    by_cases e : home g w r = ci
    · rw [offerB_eq] at hr
      obtain ⟨hr, hpl⟩ := List.mem_filter.1 hr
      have hpl : r.key ∉ placedB g w ci st := by simpa using hpl
      have hrf : r ∈ fcB g w ci st := List.mem_filter.2 ⟨hr, by simpa using e⟩
      have hnt : r.key ∉ ((fcB g w ci st).take (min (fcB g w ci st).length
          ((clrB g w ci st).countP (·.isNone)))).map Rec.key := by
        rw [← fill_placed_eq]; exact hpl
      show Blocks g r.key ((offerB g w ci st).main.getD (home g w r) [])
      rw [e, offerB_getD_self hciL]
      exact blocks_fill hbclr hrf (hclr r hrf) hnt
    · rcases hp with hp | hp
      · rw [offerB_getD ci _ st e]; exact h.bD r (hbcold r hr) hp
      · exact absurd hp e
  · intro x hx
    obtain ⟨h1, h2, h3⟩ := h.ins x hx
    exact ⟨h1, h2, offerB_blocks h (home_lt g w x) (cx.bdis x h1) h3⟩
  · exact h.insnd
  · rw [offerB_eq]; exact h.tr

end

/-! ### The insertion of one B bucket -/

/-- Output bucket `B` with the lanes of B bucket `i`'s keys freed. -/
def clrI (bMain : List Bucket) (i : Nat) (B : Bucket) : Bucket :=
  B.clear fun key => (bMain.getD i []).keys.contains key

/-- B bucket `i`'s records of direction 0 (home `i`). -/
def src0 (g : Geom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i : Nat) : List Rec :=
  (bMain.getD i []).recs.filter fun r => !dirBit w g.k r

/-- B bucket `i`'s records of direction 1 (home `i + U`). -/
def src1 (g : Geom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i : Nat) : List Rec :=
  (bMain.getD i []).recs.filter fun r => dirBit w g.k r

/-- The fill of direction 0. -/
def fl0 (g : Geom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i : Nat) (st : FinState) :
    List (Option Rec) × List Rec :=
  fill (clrI bMain i (st.main.getD i [])) (src0 g w bMain i)

/-- After the dedup and direction 0's insertion. -/
def stI1 (g : Geom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i : Nat) (st : FinState) : FinState :=
  { st with
    main := ((st.main.set i (fl0 g w bMain i st).1).set (i + g.U)
      (clrI bMain i (st.main.getD (i + g.U) []))) }

/-- After the offers to home `i`. -/
def stI3 (g : Geom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i : Nat) (st : FinState) : FinState :=
  offerB g w i (offerA g w i (stI1 g w bMain i st))

/-- The fill of direction 1. -/
def fl1 (g : Geom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i : Nat) (st : FinState) :
    List (Option Rec) × List Rec :=
  fill ((stI3 g w bMain i st).main.getD (i + g.U) []) (src1 g w bMain i)

/-- After direction 1's insertion and the capacity test. -/
def stI4 (g : Geom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i : Nat) (st : FinState) : FinState :=
  { stI3 g w bMain i st with
    main := (stI3 g w bMain i st).main.set (i + g.U) (fl1 g w bMain i st).1
    ins := (stI3 g w bMain i st).ins ++ (fl0 g w bMain i st).2 ++ (fl1 g w bMain i st).2
    trace := (stI3 g w bMain i st).trace ++ [(.insertion,
      ((stI3 g w bMain i st).ins ++ (fl0 g w bMain i st).2 ++ (fl1 g w bMain i st).2).length)] }

theorem insertBucket_eq (g : Geom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i : Nat)
    (st : FinState) :
    insertBucket g w bMain i st = offerB g w (i + g.U) (offerA g w (i + g.U) (stI4 g w bMain i st)) :=
  rfl

theorem offerA_ins (g : Geom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : FinState) :
    (offerA g w ci st).ins = st.ins := rfl

theorem offerB_ins (g : Geom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : FinState) :
    (offerB g w ci st).ins = st.ins := rfl

theorem mod_homes (g : Geom) (x : Nat) :
    x % g.homes = x % g.U + if x.testBit g.k then g.U else 0 := by
  unfold Geom.homes Geom.U
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ g.k) with h | h <;> simp [h]

section
variable {g : Geom} {w : Model.LogicalKey → Nat} {inp : Inputs} {pool : List Rec}

theorem Bi_sub (cx : Ctx g w inp pool) {i : Nat} (hi : i < g.U) :
    List.Sublist (inp.bMain.getD i []).recs (inp.bMain.flatMap Bucket.recs) := by
  have : inp.bMain.getD i [] ∈ inp.bMain := by
    rw [List.getD_eq_getElem _ _ (by rw [cx.bLen]; exact hi)]; exact List.getElem_mem _
  exact recs_sublist_flatMap this

theorem home_src0 (cx : Ctx g w inp pool) {i : Nat} (hi : i < g.U) {r : Rec}
    (hr : r ∈ src0 g w inp.bMain i) : home g w r = i := by
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hr
  have hc := cx.bHome i hi r h1
  have hb : (w r.key).testBit g.k = false := by simpa [dirBit] using h2
  unfold home
  rw [mod_homes, hc, hb]; simp

theorem home_src1 (cx : Ctx g w inp pool) {i : Nat} (hi : i < g.U) {r : Rec}
    (hr : r ∈ src1 g w inp.bMain i) : home g w r = i + g.U := by
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hr
  have hc := cx.bHome i hi r h1
  have hb : (w r.key).testBit g.k = true := by simpa [dirBit] using h2
  unfold home
  rw [mod_homes, hc, hb]; simp

/-- The insertion fill of one direction into home `ci`. -/
theorem ins_fill (cx : Ctx g w inp pool) {i ci : Nat} (hi : i < g.U) {B : Bucket}
    (hok : HomeOK g w inp ci B) {src : List Rec}
    (hsub : List.Sublist src (inp.bMain.getD i []).recs) (hh : ∀ r ∈ src, home g w r = ci) :
    HomeOK g w inp ci (fill (clrI inp.bMain i B) src).1 ∧
    (∀ x ∈ (fill (clrI inp.bMain i B) src).2, Blocks g x.key (fill (clrI inp.bMain i B) src).1) ∧
    List.Sublist (fill (clrI inp.bMain i B) src).2 src := by
  have hBi := Bi_sub cx hi
  have hnd : (src.map Rec.key).Nodup := cx.bMnd.sublist ((hsub.trans hBi).map _)
  have hcl : ∀ r ∈ src, r.key ∉ (clrI inp.bMain i B).keys := by
    intro r hr
    apply not_mem_keys_clear
    simpa [Bucket.keys] using ⟨r, hsub.subset hr, rfl⟩
  have hsnd : List.Sublist (fill (clrI inp.bMain i B) src).2 src := by
    rw [fill_snd]; exact List.drop_sublist _ _
  refine ⟨?_, ?_, hsnd⟩
  · refine homeOK_fill (homeOK_clear hok _) src ?_ hnd hcl
    intro r hr
    exact ⟨hh r hr, mem_WK_of_b (List.mem_append_left _ ((hsub.trans hBi).subset hr))⟩
  · intro x hx
    have hxs := hsnd.subset hx
    refine blocks_fill (by rw [clrI, D1Lemmas.clear_length]; exact hok.len) hxs (hcl x hxs) ?_
    rw [fill_snd] at hx
    intro hk
    have hnd2 := hnd
    rw [← List.take_append_drop (min src.length ((clrI inp.bMain i B).countP (·.isNone))) src,
      List.map_append, List.nodup_append] at hnd2
    exact hnd2.2.2 _ hk _ (List.mem_map_of_mem hx) rfl

theorem carry_cases {v U : Nat} (h : v < 2 * U) :
    (v < U ∧ v % U = v) ∨ (U ≤ v ∧ v % U = v - U) := by
  by_cases hv : v < U
  · exact Or.inl ⟨hv, Nat.mod_eq_of_lt hv⟩
  · right
    refine ⟨by omega, ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem ginv_insertBucket (cx : Ctx g w inp pool) {n : Nat} (hn : n < g.U) {st : FinState}
    (h : GInv g w inp pool (fun v => v % g.U < n) (fun v => v % g.U < n) (fun v => v % g.U < n)
      st.ins st) :
    GInv g w inp pool (fun v => v % g.U < n + 1) (fun v => v % g.U < n + 1)
      (fun v => v % g.U < n + 1) (insertBucket g w inp.bMain n st).ins
      (insertBucket g w inp.bMain n st) := by
  have hU : 0 < g.U := Nat.two_pow_pos _
  have hH := D5.homes_eq g
  have hnh : n < g.homes := by omega
  have hnUh : n + g.U < g.homes := by omega
  have hne : n ≠ n + g.U := by omega
  have cn : n % g.U = n := Nat.mod_eq_of_lt hn
  have cnU : (n + g.U) % g.U = n := by rw [Nat.add_mod_right, cn]
  have hlen : st.main.length = g.homes := h.len
  have hok0 := h.ok n hnh
  have hok1 := h.ok (n + g.U) hnUh
  -- direction 0
  obtain ⟨F0ok, F0bl, F0sub⟩ := ins_fill cx hn hok0 (src := src0 g w inp.bMain n)
    List.filter_sublist (fun r hr => home_src0 cx hn hr)
  have e1n : (stI1 g w inp.bMain n st).main.getD n [] = (fl0 g w inp.bMain n st).1 := by
    show ((st.main.set n _).set (n + g.U) _).getD n [] = _
    rw [getD_set_of_ne _ (Ne.symm hne), getD_set_self _ (by omega)]
  have e1nU : (stI1 g w inp.bMain n st).main.getD (n + g.U) [] =
      clrI inp.bMain n (st.main.getD (n + g.U) []) := by
    show ((st.main.set n _).set (n + g.U) _).getD (n + g.U) [] = _
    rw [getD_set_self _ (by simp; omega)]
  have e1o : ∀ v, v ≠ n → v ≠ n + g.U →
      (stI1 g w inp.bMain n st).main.getD v [] = st.main.getD v [] := by
    intro v h1 h2
    show ((st.main.set n _).set (n + g.U) _).getD v [] = _
    rw [getD_set_of_ne _ (Ne.symm h2), getD_set_of_ne _ (Ne.symm h1)]
  have hlow : ∀ v, v % g.U < n → v ≠ n ∧ v ≠ n + g.U := by
    intro v hv
    refine ⟨fun e => ?_, fun e => ?_⟩
    · rw [e, cn] at hv; omega
    · rw [e, cnU] at hv; omega
  have G1 : GInv g w inp pool (fun v => v % g.U < n) (fun v => v % g.U < n)
      (fun v => v % g.U < n ∨ v = n) (st.ins ++ (fl0 g w inp.bMain n st).2)
      (stI1 g w inp.bMain n st) := by
    refine ⟨?_, ?_, h.lv, h.lvnd, h.bc, ?_, ?_, ?_, ?_, h.tr⟩
    · show ((st.main.set n _).set (n + g.U) _).length = _
      simp [hlen]
    · intro v hv
      by_cases a : v = n
      · subst a; rw [e1n]; exact F0ok
      · by_cases b : v = n + g.U
        · subst b; rw [e1nU]; exact homeOK_clear hok1 _
        · rw [e1o v a b]; exact h.ok v hv
    · intro R r hr hp
      obtain ⟨a, b⟩ := hlow _ hp
      rw [e1o _ a b]; exact h.aD R r hr hp
    · intro r hr hp
      obtain ⟨a, b⟩ := hlow _ hp
      rw [e1o _ a b]; exact h.bD r hr hp
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨h1, h2, h3⟩ := h.ins x hx
        obtain ⟨a, b⟩ := hlow _ h2
        exact ⟨h1, Or.inl h2, by rw [e1o _ a b]; exact h3⟩
      · have hs := F0sub.subset hx
        have hh := home_src0 cx hn hs
        refine ⟨(Bi_sub cx hn).subset (List.mem_filter.1 hs).1, Or.inr hh, ?_⟩
        rw [hh, e1n]; exact F0bl x hx
    · refine nodup_keys_append_of_home (g := g) (w := w) h.insnd
        (cx.bMnd.sublist (((F0sub.trans List.filter_sublist).trans (Bi_sub cx hn)).map _)) ?_
      intro x hx y hy e
      have := (h.ins x hx).2.1
      rw [e, home_src0 cx hn (F0sub.subset hy), cn] at this
      omega
  -- offers to home n
  have G3 := ginv_offerB cx hnh (ginv_offerA cx hnh G1)
  have e3nU : (stI3 g w inp.bMain n st).main.getD (n + g.U) [] =
      clrI inp.bMain n (st.main.getD (n + g.U) []) := by
    unfold stI3
    rw [offerB_getD _ _ _ (Ne.symm hne), offerA_getD _ _ _ (Ne.symm hne), e1nU]
  have e3ins : (stI3 g w inp.bMain n st).ins = st.ins := rfl
  -- direction 1
  obtain ⟨F1ok, F1bl, F1sub⟩ := ins_fill cx hn hok1 (src := src1 g w inp.bMain n)
    List.filter_sublist (fun r hr => home_src1 cx hn hr)
  have hfl1 : fl1 g w inp.bMain n st =
      fill (clrI inp.bMain n (st.main.getD (n + g.U) [])) (src1 g w inp.bMain n) := by
    unfold fl1; rw [e3nU]
  rw [← hfl1] at F1ok F1bl F1sub
  have hlen3 : (stI3 g w inp.bMain n st).main.length = g.homes := G3.len
  have e4nU : (stI4 g w inp.bMain n st).main.getD (n + g.U) [] = (fl1 g w inp.bMain n st).1 := by
    show ((stI3 g w inp.bMain n st).main.set (n + g.U) _).getD (n + g.U) [] = _
    rw [getD_set_self _ (by omega)]
  have e4o : ∀ v, v ≠ n + g.U →
      (stI4 g w inp.bMain n st).main.getD v [] = (stI3 g w inp.bMain n st).main.getD v [] := by
    intro v hv
    show ((stI3 g w inp.bMain n st).main.set (n + g.U) _).getD v [] = _
    rw [getD_set_of_ne _ (Ne.symm hv)]
  have hmid : ∀ v, (v % g.U < n ∨ v = n) → v ≠ n + g.U := by
    intro v hv e
    rcases hv with hv | hv
    · exact (hlow v hv).2 e
    · exact hne (hv ▸ e)
  have hI4 : (stI4 g w inp.bMain n st).ins =
      (st.ins ++ (fl0 g w inp.bMain n st).2) ++ (fl1 g w inp.bMain n st).2 := by
    show (stI3 g w inp.bMain n st).ins ++ _ ++ _ = _
    rw [e3ins]
  have hok4 : ∀ v < g.homes, HomeOK g w inp v ((stI4 g w inp.bMain n st).main.getD v []) := by
    intro v hv
    by_cases b : v = n + g.U
    · subst b; rw [e4nU]; exact F1ok
    · rw [e4o v b]; exact G3.ok v hv
  have hins4 : ∀ x ∈ (st.ins ++ (fl0 g w inp.bMain n st).2) ++ (fl1 g w inp.bMain n st).2,
      x ∈ inp.bMain.flatMap Bucket.recs ∧
        ((home g w x % g.U < n ∨ home g w x = n) ∨ home g w x = n + g.U) ∧
      Blocks g x.key ((stI4 g w inp.bMain n st).main.getD (home g w x) []) := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨h1, h2, h3⟩ := G3.ins x hx
      exact ⟨h1, Or.inl h2, by rw [e4o _ (hmid _ h2)]; exact h3⟩
    · have hs := F1sub.subset hx
      have hh := home_src1 cx hn hs
      refine ⟨(Bi_sub cx hn).subset (List.mem_filter.1 hs).1, Or.inr hh, ?_⟩
      rw [hh, e4nU]; exact F1bl x hx
  have hnd4 : (((st.ins ++ (fl0 g w inp.bMain n st).2) ++ (fl1 g w inp.bMain n st).2).map
      Rec.key).Nodup := by
    refine nodup_keys_append_of_home (g := g) (w := w) G3.insnd
      (cx.bMnd.sublist (((F1sub.trans List.filter_sublist).trans (Bi_sub cx hn)).map _)) ?_
    intro x hx y hy e
    rw [home_src1 cx hn (F1sub.subset hy)] at e
    exact hmid _ (G3.ins x hx).2.1 e
  have G4 : GInv g w inp pool (fun v => v % g.U < n ∨ v = n) (fun v => v % g.U < n ∨ v = n)
      (fun v => (v % g.U < n ∨ v = n) ∨ v = n + g.U)
      ((st.ins ++ (fl0 g w inp.bMain n st).2) ++ (fl1 g w inp.bMain n st).2)
      (stI4 g w inp.bMain n st) := by
    refine ⟨?_, hok4, G3.lv, G3.lvnd, G3.bc, ?_, ?_, ?_, hnd4, ?_⟩
    · show ((stI3 g w inp.bMain n st).main.set (n + g.U) _).length = _
      simp [hlen3]
    · intro R r hr hp
      rw [e4o _ (hmid _ hp)]; exact G3.aD R r hr hp
    · intro r hr hp
      rw [e4o _ (hmid _ hp)]; exact G3.bD r hr hp
    · intro x hx
      exact hins4 x hx
    · intro e he
      simp only [stI4, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact G3.tr e he
      · refine ⟨rfl, ?_⟩
        show ((stI3 g w inp.bMain n st).ins ++ _ ++ _).length ≤ _
        rw [e3ins]
        refine count_main _ hok4 _ hnd4 ?_
        intro x hx
        obtain ⟨h1, _, h3⟩ := hins4 x hx
        exact ⟨mem_WK_of_b (List.mem_append_left _ h1), h3⟩
  -- offers to home n + U
  have G6 := ginv_offerB cx hnUh (ginv_offerA cx hnUh G4)
  rw [insertBucket_eq, offerB_ins, offerA_ins, hI4]
  refine G6.mono ?_ ?_ ?_
  · intro v hv hp
    rcases carry_cases (by rw [← hH]; exact hv) with ⟨a, b⟩ | ⟨a, b⟩
    · rw [b] at hp
      by_cases c : v < n
      · exact Or.inl (Or.inl (by rw [b]; exact c))
      · exact Or.inl (Or.inr (by omega))
    · rw [b] at hp
      by_cases c : v - g.U < n
      · exact Or.inl (Or.inl (by rw [b]; exact c))
      · exact Or.inr (by omega)
  · intro v hv hp
    rcases carry_cases (by rw [← hH]; exact hv) with ⟨a, b⟩ | ⟨a, b⟩
    · rw [b] at hp
      by_cases c : v < n
      · exact Or.inl (Or.inl (by rw [b]; exact c))
      · exact Or.inl (Or.inr (by omega))
    · rw [b] at hp
      by_cases c : v - g.U < n
      · exact Or.inl (Or.inl (by rw [b]; exact c))
      · exact Or.inr (by omega)
  · intro v _ hp
    rcases hp with (hp | hp) | hp
    · omega
    · rw [hp, cn]; omega
    · rw [hp, cnU]; omega

/-! ### The whole finish -/

/-- The finish phase's start state. -/
def fin0 (inp : Inputs) (routed : List Bucket) (leaves : List (List Rec)) : FinState :=
  { main := routed, ins := [], leaves := leaves, bcopy := inp.bTier, trace := [] }

theorem finish_eq (g : Geom) (w : Model.LogicalKey → Nat) (inp : Inputs) (routed : List Bucket)
    (leaves : List (List Rec)) :
    finish g w inp routed leaves =
      (List.range g.U).foldl (fun st i => insertBucket g w inp.bMain i st) (fin0 inp routed leaves) :=
  rfl

theorem ginv_fold (cx : Ctx g w inp pool) (st0 : FinState)
    (h0 : GInv g w inp pool (fun v => v % g.U < 0) (fun v => v % g.U < 0) (fun v => v % g.U < 0)
      st0.ins st0) : ∀ n, n ≤ g.U →
    GInv g w inp pool (fun v => v % g.U < n) (fun v => v % g.U < n) (fun v => v % g.U < n)
      ((List.range n).foldl (fun st i => insertBucket g w inp.bMain i st) st0).ins
      ((List.range n).foldl (fun st i => insertBucket g w inp.bMain i st) st0)
  | 0, _ => h0
  | n + 1, hn => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact ginv_insertBucket cx (by omega) (ginv_fold cx st0 h0 n (by omega))

theorem leavesOf_getD (g : Geom) (w : Model.LogicalKey → Nat) (pool : List Rec) (R : Nat) {r : Rec}
    (hr : r ∈ (leavesOf g w pool).getD R []) : r ∈ pool ∧ rangeOf g w r = R := by
  unfold leavesOf at hr
  by_cases hR : R < g.ranges
  · rw [List.getD_eq_getElem _ _ (by simpa using hR)] at hr
    simp only [List.getElem_map, List.getElem_range, List.mem_filter] at hr
    exact ⟨hr.1, by simpa using hr.2⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hr
    simp at hr

theorem leavesOf_nodup (g : Geom) (w : Model.LogicalKey → Nat) {pool : List Rec}
    (hp : (pool.map Rec.key).Nodup) : ((leavesOf g w pool).flatten.map Rec.key).Nodup := by
  unfold leavesOf
  rw [List.map_flatten, List.map_map, List.nodup_flatten]
  refine ⟨?_, ?_⟩
  · intro l hl
    obtain ⟨R, _, rfl⟩ := List.mem_map.1 hl
    exact hp.sublist (List.filter_sublist.map _)
  · rw [List.pairwise_map]
    refine List.nodup_range.pairwise_of_forall_ne ?_
    intro R _ R' _ hne x hx hx'
    simp only [Function.comp, List.mem_map, List.mem_filter] at hx hx'
    obtain ⟨r, ⟨_, hr⟩, rfl⟩ := hx
    obtain ⟨r', ⟨_, hr'⟩, e⟩ := hx'
    have h1 : rangeOf g w r = R := by simpa using hr
    have h2 : rangeOf g w r' = R' := by simpa using hr'
    apply hne
    rw [← h1, ← h2]
    simp [rangeOf, home, e]

theorem ginv_init {routed : List Bucket}
    (hlen : routed.length = g.homes) (hok : ∀ v < g.homes, HomeOK g w inp v (routed.getD v []))
    (hp : (pool.map Rec.key).Nodup) :
    GInv g w inp pool (fun v => v % g.U < 0) (fun v => v % g.U < 0) (fun v => v % g.U < 0)
      (fin0 inp routed (leavesOf g w pool)).ins (fin0 inp routed (leavesOf g w pool)) where
  len := hlen
  ok := hok
  lv R r hr := leavesOf_getD g w pool R hr
  lvnd := leavesOf_nodup g w hp
  bc := List.Sublist.refl _
  aD _ _ _ hq := absurd hq (Nat.not_lt_zero _)
  bD _ _ hq := absurd hq (Nat.not_lt_zero _)
  ins _ hx := by simp [fin0] at hx
  insnd := by simp [fin0]
  tr _ he := by simp [fin0] at he

/-- The finish phase ends with every home offered and every insertion-trace
quantity at most `homeExcess`. -/
theorem ginv_finish (cx : Ctx g w inp pool) {routed : List Bucket}
    (hlen : routed.length = g.homes) (hok : ∀ v < g.homes, HomeOK g w inp v (routed.getD v []))
    (hp : (pool.map Rec.key).Nodup) :
    GInv g w inp pool (fun _ => True) (fun _ => True) (fun _ => True)
      (finish g w inp routed (leavesOf g w pool)).ins
      (finish g w inp routed (leavesOf g w pool)) := by
  have h := ginv_fold cx _ (ginv_init hlen hok hp) g.U le_rfl
  rw [← finish_eq] at h
  have hH := D5.homes_eq g
  refine h.mono ?_ ?_ (fun _ _ _ => trivial)
  · intro v hv _
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  · intro v hv _
    exact Nat.mod_lt _ (Nat.two_pow_pos _)

end

end RebuildBound.D4b
