import RebuildBound.Proofs.S6.Radix
import RebuildBound.Proofs.HomeFinish.Leaf

/-!
# S6: the fused offers of one home, for two leaf orders

The general-digit counterpart of `D6/Offer.lean`. `sOfferA` places a prefix of
the stale A candidates of a home, so which candidates are placed depends on
the leaf order; the number placed does not, and placed A candidates never
carry a B-tier key. B's offers (`sOfferB`, one round per B-tier page) see, at
each round, a bucket whose free-lane count and whose records with a B-tier
key agree between the two runs (`BRel`), so they place the same B-tier
candidates.
-/

namespace RebuildBound.S6

open RebuildBound.Model RebuildBound.D6

section Offers

variable (g : SepGeom) (w : Model.LogicalKey → Nat)

theorem sHome_eq_of_key {x y : Rec} (h : x.key = y.key) : sHome g w x = sHome g w y := by
  simp [sHome, h]

/-- The A candidates of home `ci` in a leaf. -/
def sCand (ci : Nat) (leaf : List Rec) : List Rec := leaf.filter fun r => sHome g w r == ci

theorem sOfferA_eq (ci : Nat) (st : SFin) :
    sOfferA g w ci st = { st with
      main := st.main.set ci (fill (st.main.getD ci [])
        (staleOf (st.main.getD ci []) (sCand g w ci (st.leaves.getD (ci / 2 ^ g.I) [])))).1
      leaves := st.leaves.set (ci / 2 ^ g.I) ((st.leaves.getD (ci / 2 ^ g.I) []).filter fun r =>
        !(goneOf (st.main.getD ci []) (sCand g w ci (st.leaves.getD (ci / 2 ^ g.I) []))).contains
          r.key) } := rfl

theorem sOfferA_main_getD (ci : Nat) (st : SFin) :
    (sOfferA g w ci st).main.getD ci [] = (fill (st.main.getD ci [])
      (staleOf (st.main.getD ci []) (sCand g w ci (st.leaves.getD (ci / 2 ^ g.I) [])))).1 := by
  rw [sOfferA_eq]
  exact getD_set_self st.main ci [] (fun B => (fill B _).1) (by rw [fill_nil])

theorem sCand_home {ci : Nat} {l : List Rec} {x : Rec} (hx : x ∈ sCand g w ci l) :
    sHome g w x = ci := by
  unfold sCand at hx
  simpa using (List.mem_filter.mp hx).2

theorem s_gone_subperm (ci : Nat) (B0 : Bucket) (l : List Rec) (m : Nat) :
    (dropOf B0 (sCand g w ci l) ++ (staleOf B0 (sCand g w ci l)).take m).Subperm l := by
  have h1 : (dropOf B0 (sCand g w ci l) ++ (staleOf B0 (sCand g w ci l)).take m).Sublist
      (dropOf B0 (sCand g w ci l) ++ staleOf B0 (sCand g w ci l)) :=
    (List.take_sublist _ _).append_left _
  have h2 : (dropOf B0 (sCand g w ci l) ++ staleOf B0 (sCand g w ci l)).Perm
      (sCand g w ci l) := List.filter_append_perm _ _
  have h3 : (sCand g w ci l).Sublist l := List.filter_sublist
  exact h1.subperm.trans (h2.subperm.trans h3.subperm)

/-- A key-distinct leaf loses exactly the consumed records. -/
theorem s_gone_length (ci : Nat) (B0 : Bucket) (l : List Rec) (hn : (l.map Rec.key).Nodup) :
    (l.filter fun r => !(goneOf B0 (sCand g w ci l)).contains r.key).length =
      l.length - ((dropOf B0 (sCand g w ci l)).length +
        min (nNone B0) (staleOf B0 (sCand g w ci l)).length) := by
  set G := dropOf B0 (sCand g w ci l) ++ (staleOf B0 (sCand g w ci l)).take
    (min (nNone B0) (staleOf B0 (sCand g w ci l)).length) with hG
  have hgone : goneOf B0 (sCand g w ci l) = G.map Rec.key := by rw [goneOf_eq]
  have hGl : G.Subperm l := s_gone_subperm g w ci B0 l _
  have hl : l.Nodup := List.Nodup.of_map Rec.key hn
  have hGn : G.Nodup := by
    obtain ⟨l', hp, hs⟩ := hGl
    exact hp.nodup_iff.mp (hl.sublist hs)
  have hfilt : (l.filter fun r => (G.map Rec.key).contains r.key).Perm G := by
    rw [List.perm_ext_iff_of_nodup (hl.sublist List.filter_sublist) hGn]
    intro a
    simp only [List.mem_filter, contains_iff, List.mem_map]
    constructor
    · rintro ⟨ha, x, hx, hxa⟩
      have := List.inj_on_of_nodup_map hn (hGl.subset hx) ha hxa
      subst this
      exact hx
    · intro ha
      exact ⟨hGl.subset ha, a, ha, rfl⟩
  have hsplit := List.length_eq_length_filter_add (l := l) fun r => (G.map Rec.key).contains r.key
  rw [hgone]
  rw [hfilt.length_eq] at hsplit
  have hGlen : G.length = (dropOf B0 (sCand g w ci l)).length +
      min (nNone B0) (staleOf B0 (sCand g w ci l)).length := by
    rw [hG, List.length_append, List.length_take]
    congr 1
    omega
  omega

/-- The key predicate after the offer: forget home `ci` except for keys in `K`. -/
def sKeepAfter (keep : Rec → Bool) (K : List Model.LogicalKey) (ci : Nat) (r : Rec) : Bool :=
  (sHome g w r != ci && keep r) || K.contains r.key

theorem sKeepAfter_imp {keep : Rec → Bool} {K : List Model.LogicalKey} {ci : Nat}
    (hKk : ∀ r, K.contains r.key = true → keep r = true) (r : Rec)
    (h : sKeepAfter g w keep K ci r = true) : keep r = true := by
  unfold sKeepAfter at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨_, h⟩ | h
  · exact h
  · exact hKk r h

/-- The records of a leaf that survive the offer and are still tracked. -/
def sKeepQ (keep : Rec → Bool) (K : List Model.LogicalKey) (ci : Nat) (B0 : Bucket) (r : Rec) : Bool :=
  if sHome g w r = ci then (!B0.keys.contains r.key && K.contains r.key)
  else sKeepAfter g w keep K ci r

theorem s_gone_filter_keep (keep : Rec → Bool) (K : List Model.LogicalKey) (ci : Nat) (B0 : Bucket)
    (l : List Rec) (hK : ∀ r, sHome g w r = ci → K.contains r.key = true → nNone B0 = 0) :
    (l.filter fun r => !(goneOf B0 (sCand g w ci l)).contains r.key).filter
        (sKeepAfter g w keep K ci) =
      l.filter (sKeepQ g w keep K ci B0) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro r hr
  unfold sKeepQ
  split_ifs with hh
  · have hka : sKeepAfter g w keep K ci r = K.contains r.key := by
      simp [sKeepAfter, hh]
    rw [hka]
    cases hk : K.contains r.key
    · simp
    · have h0 := hK r hh hk
      have hiff : ((dropOf B0 (sCand g w ci l)).map Rec.key).contains r.key =
          B0.keys.contains r.key := by
        rw [Bool.eq_iff_iff, contains_iff, contains_iff, List.mem_map]
        constructor
        · rintro ⟨x, hx, hxr⟩
          unfold dropOf at hx
          have := (List.mem_filter.mp hx).2
          rw [contains_iff] at this
          rw [← hxr]
          exact this
        · intro hB
          refine ⟨r, ?_, rfl⟩
          unfold dropOf
          rw [List.mem_filter]
          refine ⟨?_, by rw [contains_iff]; exact hB⟩
          unfold sCand
          rw [List.mem_filter]
          exact ⟨hr, by simp [hh]⟩
      rw [goneOf_eq, h0]
      simp only [Nat.zero_min, List.take_zero, List.append_nil, hiff]
      simp
  · have hng : (goneOf B0 (sCand g w ci l)).contains r.key = false := by
      rw [Bool.eq_false_iff]
      intro hc
      rw [contains_iff, goneOf_eq, List.mem_map] at hc
      obtain ⟨x, hx, hxr⟩ := hc
      have hxc : x ∈ sCand g w ci l := by
        rcases List.mem_append.mp hx with hx | hx
        · exact List.mem_of_mem_filter hx
        · exact List.mem_of_mem_filter (List.mem_of_mem_take hx)
      have := sCand_home g w hxc
      rw [sHome_eq_of_key g w hxr] at this
      exact hh this
    rw [hng]
    simp

/-- **The core leaf lemma.** -/
theorem s_offer_leaf_rel (keep : Rec → Bool) (K : List Model.LogicalKey) (ci : Nat) (B0 : Bucket)
    (l1 l2 : List Rec) (hrel : LeafRel keep l1 l2) (hn1 : (l1.map Rec.key).Nodup)
    (hn2 : (l2.map Rec.key).Nodup) (hci : ∀ r, sHome g w r = ci → keep r = true)
    (hKk : ∀ r, K.contains r.key = true → keep r = true)
    (hK : ∀ r, sHome g w r = ci → K.contains r.key = true → nNone B0 = 0) :
    LeafRel (sKeepAfter g w keep K ci)
      (l1.filter fun r => !(goneOf B0 (sCand g w ci l1)).contains r.key)
      (l2.filter fun r => !(goneOf B0 (sCand g w ci l2)).contains r.key) := by
  have hc : (sCand g w ci l1).Perm (sCand g w ci l2) :=
    hrel.filter fun r h => hci r (by simpa using h)
  refine ⟨?_, ?_⟩
  · have e1 : (dropOf B0 (sCand g w ci l1)).length = (dropOf B0 (sCand g w ci l2)).length :=
      (hc.filter _).length_eq
    have e2 : (staleOf B0 (sCand g w ci l1)).length = (staleOf B0 (sCand g w ci l2)).length :=
      (hc.filter _).length_eq
    rw [s_gone_length g w ci B0 l1 hn1, s_gone_length g w ci B0 l2 hn2, hrel.1, e1, e2]
  · rw [s_gone_filter_keep g w keep K ci B0 l1 hK, s_gone_filter_keep g w keep K ci B0 l2 hK]
    refine hrel.filter fun r h => ?_
    unfold sKeepQ at h
    split_ifs at h with hh
    · exact hci r hh
    · exact sKeepAfter_imp g w hKk r h

/-! ### B's page offers -/

/-- The records of a bucket with a key in `TK`. -/
def tkRecs (TK : List Model.LogicalKey) (X : Bucket) : List Rec := X.recs.filter fun r => TK.contains r.key

/-- The state of home `ci` that B's offers depend on: the B-tier copy, the
free-lane count and the records with a B-tier key. -/
structure BRel (TK : List Model.LogicalKey) (ci : Nat) (s1 s2 : SFin) : Prop where
  bcopy : s1.bcopy = s2.bcopy
  bT : ∀ pg, ∀ r ∈ s1.bcopy.getD pg [], TK.contains r.key = true
  free : nNone (s1.main.getD ci []) = nNone (s2.main.getD ci [])
  tk : (tkRecs TK (s1.main.getD ci [])).Perm (tkRecs TK (s2.main.getD ci []))

/-- The B-tier candidates of home `ci` in page `pg`. -/
def sFc (ci : Nat) (page : List Rec) : List Rec := page.filter fun x => sHome g w x == ci

theorem sOfferPage_main_getD (ci : Nat) (st : SFin) (pg : Nat) :
    (sOfferPage g w ci st pg).main.getD ci [] =
      (fill ((st.main.getD ci []).clear fun key =>
          ((sFc g w ci (st.bcopy.getD pg [])).map Rec.key).contains key)
        (sFc g w ci (st.bcopy.getD pg []))).1 := by
  show (st.main.set ci _).getD ci [] = _
  exact getD_set_self st.main ci [] (fun B => (fill (B.clear fun key =>
          ((sFc g w ci (st.bcopy.getD pg [])).map Rec.key).contains key)
        (sFc g w ci (st.bcopy.getD pg []))).1) (by rw [show Bucket.clear _ [] = [] from rfl, fill_nil])

theorem sOfferPage_bcopy (ci : Nat) (st : SFin) (pg : Nat) :
    (sOfferPage g w ci st pg).bcopy = st.bcopy.set pg ((st.bcopy.getD pg []).filter fun x =>
      !(((sFc g w ci (st.bcopy.getD pg [])).take
        (min (nNone ((st.main.getD ci []).clear fun key =>
          ((sFc g w ci (st.bcopy.getD pg [])).map Rec.key).contains key))
          (sFc g w ci (st.bcopy.getD pg [])).length)).map Rec.key).contains x.key) := by
  show st.bcopy.set pg ((st.bcopy.getD pg []).filter fun x =>
    !(((sFc g w ci (st.bcopy.getD pg [])).take ((sFc g w ci (st.bcopy.getD pg [])).length -
      (fill ((st.main.getD ci []).clear fun key =>
          ((sFc g w ci (st.bcopy.getD pg [])).map Rec.key).contains key)
        (sFc g w ci (st.bcopy.getD pg []))).2.length)).map Rec.key).contains x.key) = _
  rw [fill_placed]

theorem sOfferPage_facts (ci : Nat) (st : SFin) (pg : Nat) :
    (sOfferPage g w ci st pg).ins = st.ins ∧ (sOfferPage g w ci st pg).trace = st.trace ∧
    (sOfferPage g w ci st pg).leaves = st.leaves ∧
    (∀ v, v ≠ ci → (sOfferPage g w ci st pg).main.getD v [] = st.main.getD v []) := by
  refine ⟨rfl, rfl, rfl, fun v hv => ?_⟩
  show (st.main.set ci _).getD v [] = _
  rw [getD_set_ne _ _ _ (Ne.symm hv)]

theorem countP_eq_of_tk (TK : List Model.LogicalKey) (p : Rec → Bool)
    (hp : ∀ r, p r = true → TK.contains r.key = true) (l : List Rec) :
    l.countP p = (l.filter fun r => TK.contains r.key).countP p := by
  rw [List.countP_filter]
  apply List.countP_congr
  intro x _
  cases h : p x
  · simp
  · have := hp x h
    rw [Bool.true_and, this]

theorem tkRecs_clear (TK : List Model.LogicalKey) (p : Model.LogicalKey → Bool) (X : Bucket) :
    tkRecs TK (X.clear p) = (tkRecs TK X).filter fun r => !p r.key := by
  unfold tkRecs
  rw [D1Lemmas.clear_recs, List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro x _
  rw [Bool.and_comm]

theorem tkRecs_fill (TK : List Model.LogicalKey) (X : Bucket) (L : List Rec) (m : Nat)
    (hm : m = min (nNone X) L.length) :
    (tkRecs TK (fill X L).1).Perm (tkRecs TK X ++ (L.take m).filter fun r => TK.contains r.key) := by
  unfold tkRecs Bucket.recs
  rw [hm, ← List.filter_append]
  exact (fill_recs X L).filter _

theorem BRel.page {TK : List Model.LogicalKey} {ci : Nat} {s1 s2 : SFin} (h : BRel TK ci s1 s2) (pg : Nat) :
    BRel TK ci (sOfferPage g w ci s1 pg) (sOfferPage g w ci s2 pg) := by
  set fc := sFc g w ci (s1.bcopy.getD pg []) with hfc
  have hfc2 : sFc g w ci (s2.bcopy.getD pg []) = fc := by rw [← h.bcopy]
  have hfcT : ∀ r ∈ fc, TK.contains r.key = true :=
    fun r hr => h.bT pg r (List.mem_of_mem_filter hr)
  have hp : ∀ r : Rec, (fc.map Rec.key).contains r.key = true → TK.contains r.key = true := by
    intro r hr
    rw [contains_iff, List.mem_map] at hr
    obtain ⟨x, hx, hxr⟩ := hr
    rw [← hxr]
    exact hfcT x hx
  have hcl : ∀ s : SFin, nNone ((s.main.getD ci []).clear fun key => (fc.map Rec.key).contains key) =
      nNone (s.main.getD ci []) +
        (tkRecs TK (s.main.getD ci [])).countP (fun r => (fc.map Rec.key).contains r.key) := by
    intro s
    rw [nNone_clear]
    congr 1
    exact countP_eq_of_tk TK _ hp _
  have hfree : nNone ((s1.main.getD ci []).clear fun key => (fc.map Rec.key).contains key) =
      nNone ((s2.main.getD ci []).clear fun key => (fc.map Rec.key).contains key) := by
    rw [hcl, hcl, h.free, h.tk.countP_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sOfferPage_bcopy, sOfferPage_bcopy, ← h.bcopy, ← hfc, hfree]
  · intro pg' r hr
    rw [sOfferPage_bcopy, getD_set_eq] at hr
    split_ifs at hr with hh
    · obtain ⟨rfl, _⟩ := hh
      exact h.bT pg r (List.mem_of_mem_filter hr)
    · exact h.bT pg' r hr
  · rw [sOfferPage_main_getD, sOfferPage_main_getD, hfc2, ← hfc, fill_nNone, fill_nNone, hfree]
  · rw [sOfferPage_main_getD, sOfferPage_main_getD, hfc2, ← hfc]
    refine (tkRecs_fill TK _ fc _ rfl).trans (List.Perm.trans ?_ (tkRecs_fill TK _ fc _ rfl).symm)
    rw [hfree, tkRecs_clear, tkRecs_clear]
    exact (h.tk.filter _).append_right _

theorem BRel.foldl {TK : List Model.LogicalKey} {ci : Nat} :
    ∀ (l : List Nat) (s1 s2 : SFin), BRel TK ci s1 s2 →
      BRel TK ci (l.foldl (sOfferPage g w ci) s1) (l.foldl (sOfferPage g w ci) s2)
  | [], _, _, h => h
  | pg :: l, _, _, h => BRel.foldl l _ _ (h.page g w pg)

theorem foldl_sOfferPage_facts (ci : Nat) :
    ∀ (l : List Nat) (st : SFin),
      (l.foldl (sOfferPage g w ci) st).ins = st.ins ∧
      (l.foldl (sOfferPage g w ci) st).trace = st.trace ∧
      (l.foldl (sOfferPage g w ci) st).leaves = st.leaves ∧
      (∀ v, v ≠ ci → (l.foldl (sOfferPage g w ci) st).main.getD v [] = st.main.getD v [])
  | [], _ => ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  | pg :: l, st => by
    obtain ⟨a1, a2, a3, a4⟩ := sOfferPage_facts g w ci st pg
    obtain ⟨b1, b2, b3, b4⟩ := foldl_sOfferPage_facts ci l (sOfferPage g w ci st pg)
    simp only [List.foldl_cons]
    exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, fun v hv => (b4 v hv).trans (a4 v hv)⟩

theorem foldl_sOfferPage_bT (TK : List Model.LogicalKey) (ci : Nat) :
    ∀ (l : List Nat) (st : SFin), (∀ pg, ∀ r ∈ st.bcopy.getD pg [], TK.contains r.key = true) →
      ∀ pg, ∀ r ∈ (l.foldl (sOfferPage g w ci) st).bcopy.getD pg [], TK.contains r.key = true
  | [], _, h => h
  | pg0 :: l, st, h => by
    simp only [List.foldl_cons]
    apply foldl_sOfferPage_bT TK ci l
    intro pg r hr
    rw [sOfferPage_bcopy, getD_set_eq] at hr
    split_ifs at hr with hh
    · obtain ⟨rfl, _⟩ := hh
      exact h pg0 r (List.mem_of_mem_filter hr)
    · exact h pg r hr

/-- Everything a single run's offers keep. -/
theorem s_offer_single (ci : Nat) (TK : List Model.LogicalKey) (st : SFin) :
    (sOfferB g w ci (sOfferA g w ci st)).ins = st.ins ∧
    (sOfferB g w ci (sOfferA g w ci st)).trace = st.trace ∧
    (∀ v, v ≠ ci → (sOfferB g w ci (sOfferA g w ci st)).main.getD v [] = st.main.getD v []) ∧
    (sOfferB g w ci (sOfferA g w ci st)).leaves.length = st.leaves.length ∧
    (LeafOK TK st.leaves → LeafOK TK (sOfferB g w ci (sOfferA g w ci st)).leaves) ∧
    ((∀ pg, ∀ r ∈ st.bcopy.getD pg [], TK.contains r.key = true) →
      ∀ pg, ∀ r ∈ (sOfferB g w ci (sOfferA g w ci st)).bcopy.getD pg [],
        TK.contains r.key = true) := by
  obtain ⟨f1, f2, f3, f4⟩ := foldl_sOfferPage_facts g w ci
    (List.range (sOfferA g w ci st).bcopy.length) (sOfferA g w ci st)
  have e : sOfferB g w ci (sOfferA g w ci st) =
      (List.range (sOfferA g w ci st).bcopy.length).foldl (sOfferPage g w ci)
        (sOfferA g w ci st) := rfl
  rw [e]
  refine ⟨f1, f2, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [f4 v hv, sOfferA_eq, getD_set_ne _ _ _ (Ne.symm hv)]
  · rw [f3, sOfferA_eq]
    simp
  · intro hok R
    rw [f3]
    show (((sOfferA g w ci st).leaves.getD R []).map Rec.key).Nodup ∧
      ∀ r ∈ (sOfferA g w ci st).leaves.getD R [], TK.contains r.key = false
    rw [sOfferA_eq]
    simp only
    rw [getD_set_eq]
    split_ifs with h
    · obtain ⟨rfl, _⟩ := h
      obtain ⟨h1, h2⟩ := hok (ci / 2 ^ g.I)
      exact ⟨h1.sublist (List.filter_sublist.map _),
        fun r hr => h2 r (List.mem_of_mem_filter hr)⟩
    · exact hok R
  · intro hb
    exact foldl_sOfferPage_bT g w TK ci _ _ hb

/-- **The offers of one home, for two leaf orders.** -/
theorem s_offer_rel (keep : Rec → Bool) (K TK : List Model.LogicalKey) (ci : Nat) (s1 s2 : SFin)
    (hmain : s1.main.getD ci [] = s2.main.getD ci [])
    (hbc : s1.bcopy = s2.bcopy)
    (hbT : ∀ pg, ∀ r ∈ s1.bcopy.getD pg [], TK.contains r.key = true)
    (hrel : ∀ R, LeafRel keep (s1.leaves.getD R []) (s2.leaves.getD R []))
    (hok1 : LeafOK TK s1.leaves) (hok2 : LeafOK TK s2.leaves)
    (hci : ∀ r, sHome g w r = ci → keep r = true)
    (hKk : ∀ r, K.contains r.key = true → keep r = true)
    (hK : ∀ r, sHome g w r = ci → K.contains r.key = true → nNone (s1.main.getD ci []) = 0) :
    (sOfferB g w ci (sOfferA g w ci s1)).bcopy = (sOfferB g w ci (sOfferA g w ci s2)).bcopy ∧
    ∀ R, LeafRel (sKeepAfter g w keep K ci)
      ((sOfferB g w ci (sOfferA g w ci s1)).leaves.getD R [])
      ((sOfferB g w ci (sOfferA g w ci s2)).leaves.getD R []) := by
  set R0 := ci / 2 ^ g.I
  have hc : (sCand g w ci (s1.leaves.getD R0 [])).Perm (sCand g w ci (s2.leaves.getD R0 [])) :=
    (hrel _).filter fun r h => hci r (by simpa using h)
  set B := s1.main.getD ci [] with hB
  have hstale : (staleOf B (sCand g w ci (s1.leaves.getD R0 []))).Perm
      (staleOf B (sCand g w ci (s2.leaves.getD R0 []))) := hc.filter _
  have hstT : ∀ (s : SFin), LeafOK TK s.leaves →
      ∀ r ∈ staleOf B (sCand g w ci (s.leaves.getD R0 [])), TK.contains r.key = false :=
    fun s hok r hr => (hok _).2 r (List.mem_of_mem_filter (List.mem_of_mem_filter hr))
  have htk0 : ∀ (s : SFin), LeafOK TK s.leaves →
      (tkRecs TK (fill B (staleOf B (sCand g w ci (s.leaves.getD R0 [])))).1).Perm
        (tkRecs TK B) := by
    intro s hok
    refine (tkRecs_fill TK _ _ _ rfl).trans ?_
    rw [List.filter_eq_nil_iff.mpr (fun r hr => by
      rw [hstT s hok r (List.mem_of_mem_take hr)]; simp), List.append_nil]
  have hA : BRel TK ci (sOfferA g w ci s1) (sOfferA g w ci s2) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · show s1.bcopy = s2.bcopy
      exact hbc
    · exact hbT
    · rw [sOfferA_main_getD, sOfferA_main_getD, ← hmain, ← hB, fill_nNone, fill_nNone,
        hstale.length_eq]
    · rw [sOfferA_main_getD, sOfferA_main_getD, ← hmain, ← hB]
      exact (htk0 s1 hok1).trans (htk0 s2 hok2).symm
  have hlen : (sOfferA g w ci s1).bcopy.length = (sOfferA g w ci s2).bcopy.length := by
    rw [hA.bcopy]
  have e : ∀ s, sOfferB g w ci s = (List.range s.bcopy.length).foldl (sOfferPage g w ci) s :=
    fun s => rfl
  refine ⟨?_, ?_⟩
  · rw [e, e, ← hlen]
    exact (hA.foldl g w _ _ _).bcopy
  · intro R
    rw [e, e, (foldl_sOfferPage_facts g w ci _ _).2.2.1,
      (foldl_sOfferPage_facts g w ci _ _).2.2.1]
    show LeafRel _ ((sOfferA g w ci s1).leaves.getD R []) ((sOfferA g w ci s2).leaves.getD R [])
    rw [sOfferA_eq, sOfferA_eq]
    simp only
    by_cases hR : R0 = R
    · subst hR
      rw [getD_set_self s1.leaves R0 [] (fun l => l.filter fun r =>
          !(goneOf (s1.main.getD ci []) (sCand g w ci l)).contains r.key) (by rfl),
        getD_set_self s2.leaves R0 [] (fun l => l.filter fun r =>
          !(goneOf (s2.main.getD ci []) (sCand g w ci l)).contains r.key) (by rfl)]
      rw [← hmain]
      exact s_offer_leaf_rel g w keep K ci _ _ _ (hrel _) (hok1 _).1 (hok2 _).1 hci hKk hK
    · rw [getD_set_ne _ _ _ hR, getD_set_ne _ _ _ hR]
      exact (hrel R).mono (sKeepAfter_imp g w hKk)

end Offers

end RebuildBound.S6
