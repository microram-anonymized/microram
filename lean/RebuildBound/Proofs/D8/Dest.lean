import RebuildBound.Proofs.D8.Step

/-!
# D8: the destination lemma

At home `v`, after the clear against B bucket `v mod U` and the resolution,
the records of C[v], B's live direction-`v/U` records, the remaining leaf
candidates and the remaining B-tier candidates are, up to order, the live
winners homed at `v` (`dest_perm`); in particular their keys are distinct
(`live_nodup`).
-/

namespace RebuildBound.D8

open RebuildBound.Model RebuildBound.D23

section defs
variable (g : TopGeom) (unsh : Rec → Bool) (w : Model.LogicalKey → Nat) (inp : TopInputs)

/-- B's main bucket `i`. -/
def Bi (i : Nat) : Bucket := inp.bMain.getD i []

/-- The clear predicate of B bucket `i`: the keys of all its records. -/
def clrOf (i : Nat) : Model.LogicalKey → Bool := fun key => (Bi inp i).keys.contains key

/-- B's main records of home `v`: direction `v / U` of bucket `v mod U`,
tombstones included. -/
def dirv (v : Nat) : List Rec :=
  (Bi inp (v % g.U)).recs.filter fun r => topWay g w r == v / g.U

/-- B's live direction records of home `v`. -/
def Sv (v : Nat) : List Rec := (dirv g w inp v).filter fun r => !r.tomb

/-- B's tier records of home `v`. -/
def Tb (v : Nat) : List Rec := inp.bTier.filter fun r => topHome g w r == v

/-- The keys of B's records of home `v`. -/
def Kv (v : Nat) : List Model.LogicalKey := (dirv g w inp v ++ Tb g w inp v).map Rec.key

/-- C's initial bucket `v`. -/
def mv (v : Nat) : Bucket := inp.cMain.getD v []

/-- The leaf candidates of home `v`. -/
def Pv (v : Nat) : List Rec := (topPool unsh inp).filter fun r => topHome g w r == v

/-- The B-tier candidates of home `v`. -/
def Tv (v : Nat) : List Rec := (topTierCopy unsh inp).filter fun r => topHome g w r == v

/-- The initial share of home `v`. -/
def H0 (v : Nat) : HQ := ⟨mv inp v, Pv g unsh w inp v, Tv g unsh w inp v⟩

/-- Home `v` after its visit: the new share and the sheds. -/
def Hv (v : Nat) : HQ × List Rec :=
  hstep (clrOf inp (v % g.U)) ((dirv g w inp v).map Rec.key) (Sv g w inp v) (H0 g unsh w inp v)

/-- Home `v` after the clear and the resolution. -/
def H1 (v : Nat) : HQ :=
  hres ((dirv g w inp v).map Rec.key)
    ⟨(mv inp v).clear (clrOf inp (v % g.U)), Pv g unsh w inp v, Tv g unsh w inp v⟩

end defs

section main
variable {g : TopGeom} {unsh : Rec → Bool} {w : Model.LogicalKey → Nat} {inp : TopInputs}
variable (hs : TopShape g unsh w inp)
include hs

theorem Bi_home {i : Nat} (hi : i < g.U) : ∀ r ∈ (Bi inp i).recs, w r.key % g.U = i :=
  hs.bHome i hi

theorem home_eq_way_iff {r : Rec} {v : Nat} (h : w r.key % g.U = v % g.U) :
    (topHome g w r == v) = (topWay g w r == v / g.U) := by
  have h1 := home_split g w r _ h
  have h2 := split_home g (v := v)
  have hU := U_pos g
  apply Bool.eq_iff_iff.2
  simp only [beq_iff_eq]
  constructor
  · intro e
    unfold topWay; rw [e]
  · intro e
    rw [h1, e]; omega

theorem Bi_filter (v : Nat) (hv : v < g.T) :
    (Bi inp (v % g.U)).recs.filter (fun r => topHome g w r == v) = dirv g w inp v := by
  have hU := U_pos g
  unfold dirv
  apply List.filter_congr
  intro r hr
  exact home_eq_way_iff hs (by rw [Bi_home hs (Nat.mod_lt _ hU) r hr])

theorem bMain_filter (v : Nat) (hv : v < g.T) :
    (inp.bMain.flatMap Bucket.recs).filter (fun r => topHome g w r == v) = dirv g w inp v := by
  have hU := U_pos g
  have hj : v % g.U < inp.bMain.length := by rw [hs.bLen]; exact Nat.mod_lt _ hU
  rw [flatMap_filter_single inp.bMain Bucket.recs _ [] (v % g.U) hj]
  · exact Bi_filter hs v hv
  · intro j' hj' hne
    apply filter_home_nil
    intro r hr hrv
    have h1 := hs.bHome j' (by rw [← hs.bLen]; exact hj') r hr
    have h2 := home_mod_U g w r
    rw [hrv, h1] at h2
    exact hne h2.symm

theorem cMain_filter (v : Nat) (hv : v < g.T) :
    (inp.cMain.flatMap Bucket.recs).filter (fun r => topHome g w r == v) = (mv inp v).recs := by
  have hj : v < inp.cMain.length := by rw [hs.cLen]; exact hv
  rw [flatMap_filter_single inp.cMain Bucket.recs _ [] v hj]
  · exact filter_home_self g w v _ (hs.cHome v hv)
  · intro j' hj' hne
    apply filter_home_nil
    intro r hr hrv
    rw [hs.cHome j' (by rw [← hs.cLen]; exact hj') r hr] at hrv
    exact hne hrv

theorem bAll_filter (v : Nat) (hv : v < g.T) :
    inp.bAll.filter (fun r => topHome g w r == v) = dirv g w inp v ++ Tb g w inp v := by
  rw [TopInputs.bAll, List.filter_append, bMain_filter hs v hv]; rfl

theorem aAll_filter (v : Nat) (hv : v < g.T) :
    inp.aAll.filter (fun r => topHome g w r == v) =
      (mv inp v).recs ++ inp.carry.filter (fun r => topHome g w r == v) := by
  rw [TopInputs.aAll, List.filter_append, cMain_filter hs v hv]

theorem contains_bAll (v : Nat) (hv : v < g.T) (r : Rec) (hr : topHome g w r = v) :
    (inp.bAll.map Rec.key).contains r.key = (Kv g w inp v).contains r.key := by
  rw [contains_home g w _ r hr, bAll_filter hs v hv]; rfl

/-! ### The live set -/

theorem winners_nodup : (inp.winners.map Rec.key).Nodup := by
  unfold TopInputs.winners
  apply nodup_keys_append hs.bNodup
  · exact nodup_keys_sublist List.filter_sublist hs.aNodup
  · intro r hr hk
    have h := (List.mem_filter.1 hr).2
    have h2 : (inp.bAll.map Rec.key).contains r.key = false := by
      cases hb : (inp.bAll.map Rec.key).contains r.key
      · rfl
      · rw [hb] at h; simp at h
    rw [List.contains_iff_mem.2 hk] at h2
    exact Bool.noConfusion h2

theorem live_nodup : (inp.live.map Rec.key).Nodup :=
  nodup_keys_sublist List.filter_sublist (winners_nodup hs)

theorem live_filter (v : Nat) (hv : v < g.T) :
    inp.live.filter (fun r => topHome g w r == v) =
      (dirv g w inp v ++ Tb g w inp v).filter (fun r => !r.tomb) ++
      ((mv inp v).recs.filter (fun r => !(Kv g w inp v).contains r.key)).filter (fun r => !r.tomb) ++
      (((inp.carry.filter (fun r => topHome g w r == v)).filter
        (fun r => !(Kv g w inp v).contains r.key)).filter (fun r => !r.tomb)) := by
  unfold TopInputs.live TopInputs.winners
  rw [filter_comm, List.filter_append, bAll_filter hs v hv, filter_comm, aAll_filter hs v hv]
  simp only [List.filter_append]
  have e1 : (mv inp v).recs.filter (fun r => !(inp.bAll.map Rec.key).contains r.key) =
      (mv inp v).recs.filter (fun r => !(Kv g w inp v).contains r.key) := by
    apply List.filter_congr
    intro r hr
    rw [contains_bAll hs v hv r (hs.cHome v hv r hr)]
  have e2 : (inp.carry.filter (fun r => topHome g w r == v)).filter
      (fun r => !(inp.bAll.map Rec.key).contains r.key) =
      (inp.carry.filter (fun r => topHome g w r == v)).filter
      (fun r => !(Kv g w inp v).contains r.key) := by
    apply List.filter_congr
    intro r hr
    have : topHome g w r = v := by simpa using (List.mem_filter.1 hr).2
    rw [contains_bAll hs v hv r this]
  rw [e1, e2]
  simp only [List.append_assoc]

/-! ### The resolved shares -/

omit hs in
theorem Tv_sub (v : Nat) : List.Sublist (Tv g unsh w inp v) (Tb g w inp v) := by
  unfold Tv Tb topTierCopy
  rw [filter_comm]
  exact List.filter_sublist

theorem tb_contains (v : Nat) (r : Rec) (hr : r ∈ (mv inp v).recs) (hnt : r.tomb = false) :
    ((Tv g unsh w inp v).map Rec.key).contains r.key =
      ((Tb g w inp v).map Rec.key).contains r.key := by
  apply Bool.eq_iff_iff.2
  simp only [List.contains_iff_mem]
  constructor
  · intro h; exact ((Tv_sub v).map Rec.key).subset h
  · intro h
    obtain ⟨t, ht, he⟩ := List.mem_map.1 h
    obtain ⟨htT, htH⟩ := List.mem_filter.1 ht
    by_cases hed : earlyDrop unsh t = true
    · exfalso
      have hrc : r ∈ inp.cMain.flatMap Bucket.recs :=
        (sublist_flatMap_getD Bucket.recs inp.cMain v [] (by
          by_cases hl : v < inp.cMain.length
          · exact hl
          · exfalso
            have : inp.cMain.getD v [] = [] := List.getD_eq_default _ _ (by omega)
            change r ∈ (inp.cMain.getD v []).recs at hr
            rw [this] at hr
            simp [Bucket.recs] at hr)).subset hr
      have := hs.tierUnsh t htT hed r hrc he.symm
      rw [hnt] at this; exact Bool.noConfusion this
    · refine List.mem_map.2 ⟨t, List.mem_filter.2 ⟨List.mem_filter.2 ⟨htT, ?_⟩, htH⟩, he⟩
      simpa using hed

omit hs in
theorem H1_T (v : Nat) : (H1 g unsh w inp v).T = (Tb g w inp v).filter (fun r => !r.tomb) := by
  unfold H1 hres Tv Tb topTierCopy
  simp only [List.filter_filter]
  apply List.filter_congr
  intro r _
  cases hc : r.tomb <;> simp [earlyDrop, hc]

omit hs in
theorem H1_P (v : Nat) : (H1 g unsh w inp v).P =
    ((inp.carry.filter (fun r => topHome g w r == v)).filter
        (fun r => !(Kv g w inp v).contains r.key)).filter (fun r => !r.tomb) := by
  unfold H1 hres Pv topPool
  simp only [List.filter_filter]
  apply List.filter_congr
  intro r _
  by_cases hH : topHome g w r = v
  · have h1 := contains_home g w inp.bTier r hH
    have h2 : (Kv g w inp v).contains r.key =
        (((dirv g w inp v).map Rec.key).contains r.key || ((Tb g w inp v).map Rec.key).contains r.key) := by
      unfold Kv; exact keys_contains_append _ _ _
    rw [h2]
    have h3 : ((Tb g w inp v).map Rec.key) = ((inp.bTier.filter fun r => topHome g w r == v).map Rec.key) := rfl
    rw [← h3] at h1
    rw [h1]
    simp only [hH, beq_self_eq_true]
    cases hc : r.tomb <;> cases hd : ((dirv g w inp v).map Rec.key).contains r.key <;>
      cases he : ((Tb g w inp v).map Rec.key).contains r.key <;> simp [earlyDrop, hc, hd, he]
  · have : (topHome g w r == v) = false := by simpa using hH
    simp [this]

theorem H1_m (v : Nat) (hv : v < g.T) : (H1 g unsh w inp v).m.recs =
    ((mv inp v).recs.filter (fun r => !(Kv g w inp v).contains r.key)).filter (fun r => !r.tomb) := by
  unfold H1 hres
  simp only
  rw [D1Lemmas.clear_recs]
  have e1 : (dropTombs ((mv inp v).clear (clrOf inp (v % g.U)))).recs =
      ((mv inp v).clear (clrOf inp (v % g.U))).recs.filter (fun r => !r.tomb) :=
    D1Lemmas.recs_map_filter _ _
  rw [e1, D1Lemmas.clear_recs]
  simp only [List.filter_filter]
  apply List.filter_congr
  intro r hr
  have hH := hs.cHome v hv r hr
  have h1 : clrOf inp (v % g.U) r.key = ((dirv g w inp v).map Rec.key).contains r.key := by
    unfold clrOf Bucket.keys
    rw [contains_home g w _ r hH, Bi_filter hs v hv]
  have h2 : (Kv g w inp v).contains r.key =
      (((dirv g w inp v).map Rec.key).contains r.key || ((Tb g w inp v).map Rec.key).contains r.key) := by
    unfold Kv; exact keys_contains_append _ _ _
  rw [h2, h1]
  cases hc : r.tomb
  · rw [tb_contains hs v r hr hc]
    simp [Bool.and_comm]
  · simp

/-- **The destination lemma.** -/
theorem dest_perm (v : Nat) (hv : v < g.T) :
    List.Perm ((H1 g unsh w inp v).m.recs ++ Sv g w inp v ++ (H1 g unsh w inp v).P ++
      (H1 g unsh w inp v).T) (inp.live.filter (fun r => topHome g w r == v)) := by
  rw [live_filter hs v hv, H1_m hs v hv, H1_P v, H1_T, List.filter_append]
  have : Sv g w inp v = (dirv g w inp v).filter (fun r => !r.tomb) := rfl
  rw [this]
  rw [List.perm_iff_count]
  intro x
  simp only [List.count_append]
  omega

theorem dest_nodup (v : Nat) (hv : v < g.T) :
    (((H1 g unsh w inp v).m.recs ++ Sv g w inp v ++ (H1 g unsh w inp v).P ++
      (H1 g unsh w inp v).T).map Rec.key).Nodup :=
  nodup_keys_perm (dest_perm hs v hv) (nodup_keys_sublist List.filter_sublist (live_nodup hs))

end main
end RebuildBound.D8
