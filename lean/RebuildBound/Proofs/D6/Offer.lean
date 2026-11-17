import RebuildBound.Proofs.ListAux.Fill
import RebuildBound.Proofs.HomeFinish.Leaf

/-!
# D6: the fused offers of one home, for two leaf orders

`offerA` places a prefix of the stale A candidates of a home, so which
candidates are placed depends on the leaf order. What does not depend on it:

* the number of dropped and placed candidates (hence every leaf length);
* the free-lane count seen by `offerB` (placed A candidates never carry a
  B-tier key), hence the B-tier candidates it places;
* the leftovers whose key lies in a set `K` of keys whose home is full when
  offered (`K` will be the keys of the insertion stash).

`LeafRel keep` relates two leaves of equal length that agree up to order on
the records `keep` selects; `offer_rel` shows the offers of home `ci` turn
`LeafRel keep` into `LeafRel keep'`, where `keep'` forgets home `ci` except
for the keys in `K`.
-/

namespace RebuildBound.D6

open RebuildBound.Model

/-! ### The leaf relation -/

theorem LeafRel.congr {keep keep' : Rec → Bool} {l1 l2 : List Rec} (h : LeafRel keep l1 l2)
    (hk : ∀ r, keep r = keep' r) : LeafRel keep' l1 l2 :=
  h.mono fun r h' => by rw [hk]; exact h'

theorem home_eq_of_key {g : Geom} {w : Model.LogicalKey → Nat} {r x : Rec} (h : x.key = r.key) :
    home g w x = home g w r := by
  simp [home, h]

section Offers

variable (g : Geom) (w : Model.LogicalKey → Nat)

/-- The A candidates of home `ci` in a leaf. -/
def candOf (ci : Nat) (leaf : List Rec) : List Rec := leaf.filter fun r => home g w r == ci

theorem offerA_eq (ci : Nat) (st : FinState) :
    offerA g w ci st = { st with
      main := st.main.set ci (fill (st.main.getD ci [])
        (staleOf (st.main.getD ci []) (candOf g w ci (st.leaves.getD (ci / 2 ^ g.lo) [])))).1
      leaves := st.leaves.set (ci / 2 ^ g.lo) ((st.leaves.getD (ci / 2 ^ g.lo) []).filter fun r =>
        !(goneOf (st.main.getD ci []) (candOf g w ci (st.leaves.getD (ci / 2 ^ g.lo) []))).contains
          r.key) } := rfl

/-- The B-tier candidates of home `ci`. -/
def fcOf (ci : Nat) (bc : List Rec) : List Rec := bc.filter fun r => home g w r == ci

/-- A bucket with the lanes of the candidates' keys freed. -/
def clearedOf (X : Bucket) (fc : List Rec) : Bucket :=
  X.clear fun key => (fc.map Rec.key).contains key

/-- The B-tier copy after `offerB` placed `min m |fc|` candidates. -/
def bcopyAfter (ci : Nat) (bc : List Rec) (m : Nat) : List Rec :=
  bc.filter fun r =>
    !(((fcOf g w ci bc).take (min m (fcOf g w ci bc).length)).map Rec.key).contains r.key

theorem offerB_main (ci : Nat) (st : FinState) :
    (offerB g w ci st).main = st.main.set ci
      (fill (clearedOf (st.main.getD ci []) (fcOf g w ci st.bcopy)) (fcOf g w ci st.bcopy)).1 :=
  rfl

theorem offerB_bcopy (ci : Nat) (st : FinState) :
    (offerB g w ci st).bcopy = bcopyAfter g w ci st.bcopy
      (nNone (clearedOf (st.main.getD ci []) (fcOf g w ci st.bcopy))) := by
  show st.bcopy.filter (fun r => !(((fcOf g w ci st.bcopy).take ((fcOf g w ci st.bcopy).length -
    (fill (clearedOf (st.main.getD ci []) (fcOf g w ci st.bcopy))
      (fcOf g w ci st.bcopy)).2.length)).map Rec.key).contains r.key) = _
  rw [fill_placed]
  rfl

/-- The main bucket of home `ci` right after `offerA`. -/
theorem offerA_main_getD (ci : Nat) (st : FinState) :
    (offerA g w ci st).main.getD ci [] = (fill (st.main.getD ci [])
      (staleOf (st.main.getD ci []) (candOf g w ci (st.leaves.getD (ci / 2 ^ g.lo) [])))).1 := by
  rw [offerA_eq]
  exact getD_set_self st.main ci [] (fun B => (fill B _).1) (by rw [fill_nil])

/-- Everything a single run's offers keep. -/
theorem offer_single (ci : Nat) (TK : List Model.LogicalKey) (st : FinState) :
    (offerB g w ci (offerA g w ci st)).ins = st.ins ∧
    (offerB g w ci (offerA g w ci st)).trace = st.trace ∧
    (∀ v, v ≠ ci → (offerB g w ci (offerA g w ci st)).main.getD v [] = st.main.getD v []) ∧
    (offerB g w ci (offerA g w ci st)).leaves.length = st.leaves.length ∧
    (LeafOK TK st.leaves → LeafOK TK (offerB g w ci (offerA g w ci st)).leaves) ∧
    ((∀ r ∈ st.bcopy, TK.contains r.key = true) →
      ∀ r ∈ (offerB g w ci (offerA g w ci st)).bcopy, TK.contains r.key = true) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [offerB_main, getD_set_ne _ _ _ (Ne.symm hv), offerA_eq, getD_set_ne _ _ _ (Ne.symm hv)]
  · show (offerA g w ci st).leaves.length = _
    rw [offerA_eq]
    simp
  · intro hok R
    show (((offerA g w ci st).leaves.getD R []).map Rec.key).Nodup ∧
      ∀ r ∈ (offerA g w ci st).leaves.getD R [], TK.contains r.key = false
    rw [offerA_eq]
    simp only
    rw [getD_set_eq]
    split_ifs with h
    · obtain ⟨rfl, _⟩ := h
      obtain ⟨h1, h2⟩ := hok (ci / 2 ^ g.lo)
      exact ⟨h1.sublist (List.filter_sublist.map _),
        fun r hr => h2 r (List.mem_of_mem_filter hr)⟩
    · exact hok R
  · intro hb r hr
    rw [offerB_bcopy] at hr
    exact hb r (List.mem_of_mem_filter hr)

/-! ### The core leaf lemma -/

theorem candOf_home {ci : Nat} {l : List Rec} {x : Rec} (hx : x ∈ candOf g w ci l) :
    home g w x = ci := by
  unfold candOf at hx
  simpa using (List.mem_filter.mp hx).2

/-- The consumed records are a sub-multiset of the leaf. -/
theorem gone_subperm (ci : Nat) (B0 : Bucket) (l : List Rec) (m : Nat) :
    (dropOf B0 (candOf g w ci l) ++ (staleOf B0 (candOf g w ci l)).take m).Subperm l := by
  have h1 : (dropOf B0 (candOf g w ci l) ++ (staleOf B0 (candOf g w ci l)).take m).Sublist
      (dropOf B0 (candOf g w ci l) ++ staleOf B0 (candOf g w ci l)) :=
    (List.take_sublist _ _).append_left _
  have h2 : (dropOf B0 (candOf g w ci l) ++ staleOf B0 (candOf g w ci l)).Perm
      (candOf g w ci l) := List.filter_append_perm _ _
  have h3 : (candOf g w ci l).Sublist l := List.filter_sublist
  exact h1.subperm.trans (h2.subperm.trans h3.subperm)

/-- A key-distinct leaf loses exactly the consumed records. -/
theorem gone_length (ci : Nat) (B0 : Bucket) (l : List Rec) (hn : (l.map Rec.key).Nodup) :
    (l.filter fun r => !(goneOf B0 (candOf g w ci l)).contains r.key).length =
      l.length - ((dropOf B0 (candOf g w ci l)).length +
        min (nNone B0) (staleOf B0 (candOf g w ci l)).length) := by
  set G := dropOf B0 (candOf g w ci l) ++ (staleOf B0 (candOf g w ci l)).take
    (min (nNone B0) (staleOf B0 (candOf g w ci l)).length) with hG
  have hgone : goneOf B0 (candOf g w ci l) = G.map Rec.key := by rw [goneOf_eq]
  have hGl : G.Subperm l := gone_subperm g w ci B0 l _
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
  have hGlen : G.length = (dropOf B0 (candOf g w ci l)).length +
      min (nNone B0) (staleOf B0 (candOf g w ci l)).length := by
    rw [hG, List.length_append, List.length_take]
    congr 1
    omega
  omega

/-- The key predicate of the offer: forget home `ci` except for keys in `K`. -/
def keepAfter (keep : Rec → Bool) (K : List Model.LogicalKey) (ci : Nat) (r : Rec) : Bool :=
  (home g w r != ci && keep r) || K.contains r.key

theorem keepAfter_imp {keep : Rec → Bool} {K : List Model.LogicalKey} {ci : Nat}
    (hKk : ∀ r, K.contains r.key = true → keep r = true) (r : Rec)
    (h : keepAfter g w keep K ci r = true) : keep r = true := by
  unfold keepAfter at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨_, h⟩ | h
  · exact h
  · exact hKk r h

/-- The records of a leaf that survive the offer and are still tracked. -/
def keepQ (keep : Rec → Bool) (K : List Model.LogicalKey) (ci : Nat) (B0 : Bucket) (r : Rec) : Bool :=
  if home g w r = ci then (!B0.keys.contains r.key && K.contains r.key)
  else keepAfter g w keep K ci r

theorem gone_filter_keep (keep : Rec → Bool) (K : List Model.LogicalKey) (ci : Nat) (B0 : Bucket)
    (l : List Rec) (hK : ∀ r, home g w r = ci → K.contains r.key = true → nNone B0 = 0) :
    (l.filter fun r => !(goneOf B0 (candOf g w ci l)).contains r.key).filter
        (keepAfter g w keep K ci) =
      l.filter (keepQ g w keep K ci B0) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro r hr
  unfold keepQ
  split_ifs with hh
  · -- home ci
    have hka : keepAfter g w keep K ci r = K.contains r.key := by
      simp [keepAfter, hh]
    rw [hka]
    cases hk : K.contains r.key
    · simp
    · have h0 := hK r hh hk
      have hiff : ((dropOf B0 (candOf g w ci l)).map Rec.key).contains r.key =
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
          unfold candOf
          rw [List.mem_filter]
          exact ⟨hr, by simp [hh]⟩
      rw [goneOf_eq, h0]
      simp only [Nat.zero_min, List.take_zero, List.append_nil, hiff]
      simp
  · -- other homes: nothing of theirs is consumed
    have hng : (goneOf B0 (candOf g w ci l)).contains r.key = false := by
      rw [Bool.eq_false_iff]
      intro hc
      rw [contains_iff, goneOf_eq, List.mem_map] at hc
      obtain ⟨x, hx, hxr⟩ := hc
      have hxc : x ∈ candOf g w ci l := by
        rcases List.mem_append.mp hx with hx | hx
        · exact List.mem_of_mem_filter hx
        · exact List.mem_of_mem_filter (List.mem_of_mem_take hx)
      have := candOf_home g w hxc
      rw [home_eq_of_key hxr] at this
      exact hh this
    rw [hng]
    simp

/-- **The core leaf lemma.** -/
theorem offer_leaf_rel (keep : Rec → Bool) (K : List Model.LogicalKey) (ci : Nat) (B0 : Bucket)
    (l1 l2 : List Rec) (hrel : LeafRel keep l1 l2) (hn1 : (l1.map Rec.key).Nodup)
    (hn2 : (l2.map Rec.key).Nodup) (hci : ∀ r, home g w r = ci → keep r = true)
    (hKk : ∀ r, K.contains r.key = true → keep r = true)
    (hK : ∀ r, home g w r = ci → K.contains r.key = true → nNone B0 = 0) :
    LeafRel (keepAfter g w keep K ci)
      (l1.filter fun r => !(goneOf B0 (candOf g w ci l1)).contains r.key)
      (l2.filter fun r => !(goneOf B0 (candOf g w ci l2)).contains r.key) := by
  have hc : (candOf g w ci l1).Perm (candOf g w ci l2) :=
    hrel.filter fun r h => hci r (by simpa using h)
  refine ⟨?_, ?_⟩
  · have e1 : (dropOf B0 (candOf g w ci l1)).length = (dropOf B0 (candOf g w ci l2)).length :=
      (hc.filter _).length_eq
    have e2 : (staleOf B0 (candOf g w ci l1)).length = (staleOf B0 (candOf g w ci l2)).length :=
      (hc.filter _).length_eq
    rw [gone_length g w ci B0 l1 hn1, gone_length g w ci B0 l2 hn2, hrel.1, e1, e2]
  · rw [gone_filter_keep g w keep K ci B0 l1 hK, gone_filter_keep g w keep K ci B0 l2 hK]
    refine hrel.filter fun r h => ?_
    unfold keepQ at h
    split_ifs at h with hh
    · exact hci r hh
    · exact keepAfter_imp g w hKk r h

/-- The free-lane count `offerB` sees after `offerA` placed candidates that
avoid the B-tier keys. -/
theorem cleared_nNone (B0 : Bucket) (st fc : List Rec) (TK : List Model.LogicalKey)
    (hst : ∀ r ∈ st, TK.contains r.key = false) (hfc : ∀ r ∈ fc, TK.contains r.key = true) :
    nNone (clearedOf (fill B0 st).1 fc) =
      nNone B0 - min (nNone B0) st.length +
        B0.recs.countP (fun r => (fc.map Rec.key).contains r.key) := by
  unfold clearedOf
  rw [nNone_clear, fill_nNone]
  congr 1
  unfold Bucket.recs
  rw [(fill_recs B0 st).countP_eq, List.countP_append]
  have : (st.take (min (nNone B0) st.length)).countP
      (fun r => (fc.map Rec.key).contains r.key) = 0 := by
    rw [List.countP_eq_zero]
    intro a ha hq
    rw [contains_iff, List.mem_map] at hq
    obtain ⟨x, hx, hxa⟩ := hq
    have h1 := hst a (List.mem_of_mem_take ha)
    have h2 := hfc x hx
    rw [hxa] at h2
    rw [h1] at h2
    exact Bool.false_ne_true h2
  rw [this, Nat.add_zero]

/-- **The offers of one home, for two leaf orders.** -/
theorem offer_rel (keep : Rec → Bool) (K TK : List Model.LogicalKey) (ci : Nat) (s1 s2 : FinState)
    (hmain : s1.main.getD ci [] = s2.main.getD ci [])
    (hbc : s1.bcopy = s2.bcopy)
    (hbT : ∀ r ∈ s1.bcopy, TK.contains r.key = true)
    (hrel : ∀ R, LeafRel keep (s1.leaves.getD R []) (s2.leaves.getD R []))
    (hok1 : LeafOK TK s1.leaves) (hok2 : LeafOK TK s2.leaves)
    (hci : ∀ r, home g w r = ci → keep r = true)
    (hKk : ∀ r, K.contains r.key = true → keep r = true)
    (hK : ∀ r, home g w r = ci → K.contains r.key = true → nNone (s1.main.getD ci []) = 0) :
    (offerB g w ci (offerA g w ci s1)).bcopy = (offerB g w ci (offerA g w ci s2)).bcopy ∧
    ∀ R, LeafRel (keepAfter g w keep K ci)
      ((offerB g w ci (offerA g w ci s1)).leaves.getD R [])
      ((offerB g w ci (offerA g w ci s2)).leaves.getD R []) := by
  have hc : (candOf g w ci (s1.leaves.getD (ci / 2 ^ g.lo) [])).Perm
      (candOf g w ci (s2.leaves.getD (ci / 2 ^ g.lo) [])) :=
    (hrel _).filter fun r h => hci r (by simpa using h)
  have hstale : (staleOf (s1.main.getD ci []) (candOf g w ci (s1.leaves.getD (ci / 2 ^ g.lo) []))).Perm
      (staleOf (s1.main.getD ci []) (candOf g w ci (s2.leaves.getD (ci / 2 ^ g.lo) []))) :=
    hc.filter _
  have e : ∀ s : FinState, (offerB g w ci (offerA g w ci s)).bcopy =
      bcopyAfter g w ci s.bcopy (nNone (clearedOf (fill (s.main.getD ci [])
        (staleOf (s.main.getD ci []) (candOf g w ci (s.leaves.getD (ci / 2 ^ g.lo) [])))).1
        (fcOf g w ci s.bcopy))) := fun s => by
    rw [offerB_bcopy, offerA_main_getD]; rfl
  have hfc : ∀ r ∈ fcOf g w ci s1.bcopy, TK.contains r.key = true :=
    fun r hr => hbT r (List.mem_of_mem_filter hr)
  have hst : ∀ (s : FinState), LeafOK TK s.leaves →
      ∀ r ∈ staleOf (s1.main.getD ci []) (candOf g w ci (s.leaves.getD (ci / 2 ^ g.lo) [])),
        TK.contains r.key = false :=
    fun s hok r hr => (hok _).2 r (List.mem_of_mem_filter (List.mem_of_mem_filter hr))
  refine ⟨?_, ?_⟩
  · rw [e s1, e s2, ← hbc, ← hmain,
      cleared_nNone _ _ _ TK (hst s1 hok1) hfc, cleared_nNone _ _ _ TK (hst s2 hok2) hfc,
      hstale.length_eq]
  · intro R
    show LeafRel _ ((offerA g w ci s1).leaves.getD R []) ((offerA g w ci s2).leaves.getD R [])
    rw [offerA_eq, offerA_eq]
    simp only
    by_cases hR : ci / 2 ^ g.lo = R
    · subst hR
      rw [getD_set_self s1.leaves (ci / 2 ^ g.lo) [] (fun l => l.filter fun r =>
          !(goneOf (s1.main.getD ci []) (candOf g w ci l)).contains r.key) (by rfl),
        getD_set_self s2.leaves (ci / 2 ^ g.lo) [] (fun l => l.filter fun r =>
          !(goneOf (s2.main.getD ci []) (candOf g w ci l)).contains r.key) (by rfl)]
      rw [← hmain]
      exact offer_leaf_rel g w keep K ci _ _ _ (hrel _) (hok1 _).1 (hok2 _).1 hci hKk hK
    · rw [getD_set_ne _ _ _ hR, getD_set_ne _ _ _ hR]
      exact (hrel R).mono (keepAfter_imp g w hKk)

end Offers

end RebuildBound.D6
