import RebuildBound.Proofs.S12.Home

/-!
# S12: the offers, home by home

`gparts g w st E v` is the share of home `v` in a finish state, with the
insertion sheds `E` given explicitly (B's insertion keeps a bucket's sheds
pending until its last way): main bucket `v`, the candidates of home `v` in
its leaf, each B-tier page's candidates of home `v`, and `E`'s records of
home `v`. The offers to home `ci` act on `gparts ci` as `gOffA`/`gPages` and
leave every other home's parts alone, because a record's home is a function
of its key.
-/

namespace RebuildBound.S12

open RebuildBound.Model RebuildBound.D23

/-- The records of `L` whose home is `v`. -/
def hfil (g : SepGeom) (w : Model.LogicalKey → Nat) (v : Nat) (L : List Rec) : List Rec :=
  L.filter fun x => sHome g w x == v

/-- The share of home `v` in a finish state, with insertion sheds `E`. -/
def gparts (g : SepGeom) (w : Model.LogicalKey → Nat) (st : SFin) (E : List Rec) (v : Nat) : GP :=
  ⟨st.main.getD v [], hfil g w v (st.leaves.getD (v / 2 ^ g.I) []), st.bcopy.map (hfil g w v),
    hfil g w v E⟩

/-- A's leaf offer at one home. -/
def gOffA (h : GP) : GP := ⟨(offA ⟨h.m, h.P, [], h.I⟩).m, (offA ⟨h.m, h.P, [], h.I⟩).P, h.T, h.I⟩
/-- B's insertion of `S` into one home (after its dedup). -/
def gFill (S : List Rec) (h : GP) : GP := ⟨(fill h.m S).1, h.P, h.T, h.I ++ (fill h.m S).2⟩
/-- B's tier offer rounds at one home. -/
def gPages (h : GP) : GP := ⟨(pagesRun h.m h.T).1, h.P, (pagesRun h.m h.T).2, h.I⟩
/-- The dedup of one home against B's keys. -/
def gClr (clr : Model.LogicalKey → Bool) (h : GP) : GP := ⟨h.m.clear clr, h.P, h.T, h.I⟩

theorem gStep_eq (clr : Model.LogicalKey → Bool) (S : List Rec) (h : GP) :
    gStep clr S h = gPages (gOffA (gFill S (gClr clr h))) := rfl

theorem hfil_nil (g : SepGeom) (w : Model.LogicalKey → Nat) (v : Nat) : hfil g w v [] = [] := rfl

theorem hfil_append (g : SepGeom) (w : Model.LogicalKey → Nat) (v : Nat) (A B : List Rec) :
    hfil g w v (A ++ B) = hfil g w v A ++ hfil g w v B := List.filter_append ..

theorem hfil_self (g : SepGeom) (w : Model.LogicalKey → Nat) (v : Nat) (L : List Rec)
    (h : ∀ r ∈ L, sHome g w r = v) : hfil g w v L = L := by
  unfold hfil; rw [List.filter_eq_self]; intro r hr; simp [h r hr]

theorem hfil_nil_of (g : SepGeom) (w : Model.LogicalKey → Nat) (v : Nat) (L : List Rec)
    (h : ∀ r ∈ L, sHome g w r ≠ v) : hfil g w v L = [] := by
  unfold hfil; rw [List.filter_eq_nil_iff]; intro r hr; simp [h r hr]

theorem mem_hfil {g : SepGeom} {w : Model.LogicalKey → Nat} {v : Nat} {L : List Rec} {r : Rec} :
    r ∈ hfil g w v L ↔ r ∈ L ∧ sHome g w r = v := by
  unfold hfil; simp

theorem getD_map_nil {α β : Type} (f : List α → List β) (hf : f [] = []) (L : List (List α)) (n : Nat) :
    (L.map f).getD n [] = f (L.getD n []) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[n]? <;> simp [hf]

theorem not_contains_of_sHome (g : SepGeom) (w : Model.LogicalKey → Nat) {ci v : Nat} (hne : v ≠ ci)
    (L : List Rec) (hL : ∀ r ∈ L, sHome g w r = ci) (r : Rec) (hr : sHome g w r = v) :
    (!(L.map Rec.key).contains r.key) = true := by
  have : r.key ∉ L.map Rec.key := by
    intro hk
    obtain ⟨r', hr', he⟩ := List.mem_map.1 hk
    have := sHome_of_key g w he
    rw [hL r' hr', hr] at this
    exact hne this.symm
  simpa [List.contains_iff_mem] using this

theorem map_set_filter (p q : Rec → Bool) (h : ∀ r, p r = true → q r = true) :
    ∀ (l : List (List Rec)) (pg : Nat),
      (l.set pg ((l.getD pg []).filter q)).map (fun L => L.filter p) = l.map (fun L => L.filter p)
  | [], _ => rfl
  | a :: l, 0 => by simp [filter_filter_of_imp _ _ _ h]
  | a :: l, pg + 1 => by
    have := map_set_filter p q h l pg
    simp only [List.set_cons_succ, List.map_cons, List.getD_cons_succ] at this ⊢
    rw [this]

/-! ### A's leaf offer -/

section offA
variable (g : SepGeom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : SFin)

theorem sOfferA_main_length : (sOfferA g w ci st).main.length = st.main.length := by
  simp [sOfferA]
theorem sOfferA_leaves_length : (sOfferA g w ci st).leaves.length = st.leaves.length := by
  simp [sOfferA]
theorem sOfferA_bcopy : (sOfferA g w ci st).bcopy = st.bcopy := rfl
theorem sOfferA_ins : (sOfferA g w ci st).ins = st.ins := rfl

theorem sOfferA_lrange (h : ∀ R, ∀ x ∈ st.leaves.getD R [], sRange g w x = R) :
    ∀ R, ∀ x ∈ (sOfferA g w ci st).leaves.getD R [], sRange g w x = R := by
  intro R r hr
  simp only [sOfferA] at hr
  by_cases hR : ci / 2 ^ g.I = R
  · subst hR
    by_cases hl : ci / 2 ^ g.I < st.leaves.length
    · rw [getD_set_self _ _ _ _ hl] at hr
      exact h _ r (List.mem_filter.1 hr).1
    · rw [List.set_eq_of_length_le (by omega)] at hr
      exact h _ r hr
  · rw [D6.getD_set_ne _ _ _ hR] at hr
    exact h R r hr

theorem sOfferA_parts_self (E : List Rec) (hci : ci < st.main.length)
    (hR : ci / 2 ^ g.I < st.leaves.length) :
    gparts g w (sOfferA g w ci st) E ci = gOffA (gparts g w st E ci) := by
  simp only [gparts, sOfferA, gOffA, offA, hfil, getD_set_self _ _ _ _ hci,
    getD_set_self _ _ _ _ hR, GP.mk.injEq, true_and, and_true]
  exact filter_comm _ _ _

theorem sOfferA_parts_ne (E : List Rec) {v : Nat} (hne : v ≠ ci) :
    gparts g w (sOfferA g w ci st) E v = gparts g w st E v := by
  simp only [gparts, sOfferA, hfil, D6.getD_set_ne _ _ _ (Ne.symm hne), GP.mk.injEq, true_and,
    and_true]
  apply getD_set_filter
  intro r hr
  have hr' : sHome g w r = v := by simpa using hr
  apply not_contains_of_sHome g w hne _ ?_ r hr'
  intro r' hr'
  rcases List.mem_append.1 hr' with h1 | h1
  · have := (List.mem_filter.1 (List.mem_filter.1 h1).1).2; simpa using this
  · have := (List.mem_filter.1 (List.mem_filter.1 (List.mem_of_mem_take h1)).1).2
    simpa using this

end offA

/-! ### One B-tier page round -/

section page
variable (g : SepGeom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : SFin) (pg : Nat)

theorem sOfferPage_main_length : (sOfferPage g w ci st pg).main.length = st.main.length := by
  simp [sOfferPage]
theorem sOfferPage_bcopy_length : (sOfferPage g w ci st pg).bcopy.length = st.bcopy.length := by
  simp [sOfferPage]
theorem sOfferPage_leaves : (sOfferPage g w ci st pg).leaves = st.leaves := rfl
theorem sOfferPage_ins : (sOfferPage g w ci st pg).ins = st.ins := rfl

theorem sOfferPage_self (hci : ci < st.main.length) :
    (sOfferPage g w ci st pg).main.getD ci [] =
      (offB ⟨st.main.getD ci [], [], hfil g w ci (st.bcopy.getD pg []), []⟩).m ∧
    (sOfferPage g w ci st pg).bcopy.map (hfil g w ci) =
      (st.bcopy.map (hfil g w ci)).set pg
        (offB ⟨st.main.getD ci [], [], hfil g w ci (st.bcopy.getD pg []), []⟩).T := by
  constructor
  · simp only [sOfferPage, getD_set_self _ _ _ _ hci]; rfl
  · simp only [sOfferPage, List.map_set]
    congr 1
    simp only [offB, hfil]
    exact filter_comm _ _ _

theorem sOfferPage_ne {v : Nat} (hne : v ≠ ci) :
    (sOfferPage g w ci st pg).main.getD v [] = st.main.getD v [] ∧
    (sOfferPage g w ci st pg).bcopy.map (hfil g w v) = st.bcopy.map (hfil g w v) := by
  constructor
  · simp only [sOfferPage]; exact D6.getD_set_ne _ _ _ (Ne.symm hne)
  · simp only [sOfferPage]
    apply map_set_filter
    intro r hr
    have hr' : sHome g w r = v := by simpa using hr
    apply not_contains_of_sHome g w hne _ ?_ r hr'
    intro r' hr'
    have := (List.mem_filter.1 (List.mem_of_mem_take hr')).2; simpa using this

end page

/-! ### B's tier offers -/

/-- The page rounds' fold, after `n` pages. -/
structure OBInv (g : SepGeom) (w : Model.LogicalKey → Nat) (ci : Nat) (st st' : SFin) (n : Nat) : Prop where
  mlen : st'.main.length = st.main.length
  blen : st'.bcopy.length = st.bcopy.length
  leaves : st'.leaves = st.leaves
  ins : st'.ins = st.ins
  m : st'.main.getD ci [] = (pagesRun (st.main.getD ci []) ((st.bcopy.map (hfil g w ci)).take n)).1
  T : st'.bcopy.map (hfil g w ci) =
    (pagesRun (st.main.getD ci []) ((st.bcopy.map (hfil g w ci)).take n)).2 ++
      (st.bcopy.map (hfil g w ci)).drop n
  ne : ∀ v, v ≠ ci → st'.main.getD v [] = st.main.getD v [] ∧
    st'.bcopy.map (hfil g w v) = st.bcopy.map (hfil g w v)

theorem sOfferB_fold (g : SepGeom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : SFin)
    (hci : ci < st.main.length) : ∀ n ≤ st.bcopy.length,
    OBInv g w ci st ((List.range n).foldl (sOfferPage g w ci) st) n
  | 0, _ => ⟨rfl, rfl, rfl, rfl, by simp [pagesRun_nil], by simp [pagesRun_nil],
      fun _ _ => ⟨rfl, rfl⟩⟩
  | n + 1, hn => by
    have ih := sOfferB_fold g w ci st hci n (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set s := (List.range n).foldl (sOfferPage g w ci) st with hs
    set T := st.bcopy.map (hfil g w ci) with hT
    have hTl : n < T.length := by rw [hT, List.length_map]; omega
    have hpl : ((pagesRun (st.main.getD ci []) (T.take n)).2).length = n := by
      rw [pagesRun_snd_length, List.length_take]; omega
    have hfc : hfil g w ci (s.bcopy.getD n []) = T[n] := by
      rw [← getD_map_nil (hfil g w ci) (hfil_nil g w ci), ih.T,
        List.getD_append_right _ _ _ _ (by rw [hpl]), hpl, Nat.sub_self,
        List.drop_eq_getElem_cons hTl]
      rfl
    have hself := sOfferPage_self g w ci s n (by rw [ih.mlen]; exact hci)
    rw [ih.m, hfc] at hself
    have htake : T.take (n + 1) = T.take n ++ [T[n]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hTl]; rfl
    refine ⟨by rw [sOfferPage_main_length, ih.mlen], by rw [sOfferPage_bcopy_length, ih.blen],
      by rw [sOfferPage_leaves, ih.leaves], by rw [sOfferPage_ins, ih.ins], ?_, ?_, ?_⟩
    · rw [hself.1, htake, pagesRun_snoc]
    · rw [hself.2, ih.T, htake, pagesRun_snoc,
        List.set_append_right _ _ (by rw [hpl]), hpl, Nat.sub_self, List.drop_eq_getElem_cons hTl,
        List.set_cons_zero, List.append_assoc]
      rfl
    · intro v hv
      have := sOfferPage_ne g w ci s n hv
      rw [this.1, this.2]
      exact ih.ne v hv

theorem sOfferB_inv (g : SepGeom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : SFin)
    (hci : ci < st.main.length) : OBInv g w ci st (sOfferB g w ci st) st.bcopy.length :=
  sOfferB_fold g w ci st hci _ (Nat.le_refl _)

theorem sOfferB_parts_self (g : SepGeom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : SFin) (E : List Rec)
    (hci : ci < st.main.length) :
    gparts g w (sOfferB g w ci st) E ci = gPages (gparts g w st E ci) := by
  have h := sOfferB_inv g w ci st hci
  have e1 : (st.bcopy.map (hfil g w ci)).take st.bcopy.length = st.bcopy.map (hfil g w ci) := by
    apply List.take_of_length_le; simp
  have e2 : (st.bcopy.map (hfil g w ci)).drop st.bcopy.length = [] := by
    apply List.drop_of_length_le; simp
  have hm := h.m
  have hT := h.T
  rw [e1] at hm hT
  rw [e2, List.append_nil] at hT
  simp only [gparts, gPages, hm, hT, h.leaves]

theorem sOfferB_parts_ne (g : SepGeom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : SFin) (E : List Rec)
    (hci : ci < st.main.length) {v : Nat} (hne : v ≠ ci) :
    gparts g w (sOfferB g w ci st) E v = gparts g w st E v := by
  have h := sOfferB_inv g w ci st hci
  have := h.ne v hne
  simp only [gparts, this.1, this.2, h.leaves]

end RebuildBound.S12
