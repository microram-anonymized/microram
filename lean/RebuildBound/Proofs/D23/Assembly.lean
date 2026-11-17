import RebuildBound.Proofs.D23.Finish
import RebuildBound.Proofs.ListAux.Drain

/-!
# D23: the reference execution, home by home

Names for the phases of the reference execution (`rt`, `pl`, `lv`, `st0`,
`fin`) and for the initial parts of home `v` (`mv`, `Pv`, `Tv`, `Sv`), and
the main per-home fact `parts_fin`: after the finish every home holds
`homeStep` of its initial parts (`Hv`), whose inputs meet `HomeOK`.
-/

namespace RebuildBound.D23

open RebuildBound.Model

/-! ### Generic list facts -/

theorem count_filter_home (g : Geom) (w : Model.LogicalKey → Nat) (x : Rec) (L : List Rec) :
    L.count x = (L.filter fun r => home g w r == home g w x).count x := by
  rw [List.count_filter]; simp

theorem home_lt (g : Geom) (w : Model.LogicalKey → Nat) (r : Rec) : home g w r < g.homes := by
  unfold home; exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- For a record of home `v`, membership of its key among `L`'s keys is decided by `L`'s
records of home `v`. -/
theorem contains_home (g : Geom) (w : Model.LogicalKey → Nat) (L : List Rec) (r : Rec) {v : Nat}
    (hr : home g w r = v) :
    (L.map Rec.key).contains r.key = ((L.filter fun r => home g w r == v).map Rec.key).contains r.key := by
  apply Bool.eq_iff_iff.2
  simp only [List.contains_iff_mem, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨r', hr', he⟩
    refine ⟨r', ⟨hr', ?_⟩, he⟩
    rw [home_of_key g w he, hr]; simp
  · rintro ⟨r', ⟨hr', _⟩, he⟩
    exact ⟨r', hr', he⟩

theorem contains_perm {L L' : List Rec} (h : List.Perm L L') (k : Model.LogicalKey) :
    (L.map Rec.key).contains k = (L'.map Rec.key).contains k := by
  apply Bool.eq_iff_iff.2
  simp only [List.contains_iff_mem]
  exact (h.map Rec.key).mem_iff

/-! ### The reference execution -/

section ref
variable (rule : CapRule) (g : Geom) (w : Model.LogicalKey → Nat) (inp : Inputs)

/-- A's route. -/
def rt : RouteState := routeA rule g w inp.aMain
/-- The swept A pool. -/
def pl : List Rec := poolA (rt rule g w inp) inp.aTier inp.bTier
/-- The DFS leaves. -/
def lv : List (List Rec) := leavesOf g w (pl rule g w inp)
/-- The initial finish state. -/
def st0 : FinState :=
  { main := (rt rule g w inp).main, ins := [], leaves := lv rule g w inp, bcopy := inp.bTier,
    trace := [] }
/-- The final finish state. -/
def fin : FinState := finish g w inp (rt rule g w inp).main (lv rule g w inp)

theorem reference_output :
    (reference rule g w inp).output = ⟨(fin rule g w inp).main, (drain (fin rule g w inp)).1⟩ :=
  rfl

/-- Home `v`'s initial main bucket. -/
def mv (v : Nat) : Bucket := (rt rule g w inp).main.getD v []
/-- Home `v`'s A candidates. -/
def Pv (v : Nat) : List Rec := (pl rule g w inp).filter fun r => home g w r == v
/-- Home `v`'s B tier candidates. -/
def Tv (v : Nat) : List Rec := inp.bTier.filter fun r => home g w r == v
/-- B's main records of home `v`. -/
def Sv (v : Nat) : List Rec := (inp.bMain.getD (v % g.U) []).recs.filter fun r => home g w r == v
/-- Home `v` after the finish. -/
def Hv (v : Nat) : HP :=
  homeStep (clrOf inp.bMain (v % g.U)) (Sv g w inp v) ⟨mv rule g w inp v, Pv rule g w inp v, Tv g w inp v, []⟩

end ref

section main
variable {rule : CapRule} {g : Geom} {TA TB : Nat} {wOld w : Model.LogicalKey → Nat} {inp : Inputs}
variable (hv : rule.Valid) (hI : InputValid g TA TB wOld w inp)
include hv hI

theorem rt_inv : RInv g inp.aMain (rt rule g w inp) := routeA_inv hv g w inp.aMain hI.aLen hI.aLanes

theorem rt_home : ∀ v < g.homes, ∀ r ∈ (mv rule g w inp v).recs, home g w r = v :=
  routeA_home hv g w inp.aMain hI.aLen hI.aLanes

omit hv hI in
theorem lv_getD {R : Nat} (hR : R < g.ranges) :
    (lv rule g w inp).getD R [] = (pl rule g w inp).filter fun r => rangeOf g w r == R := by
  simp [lv, leavesOf, List.getD_eq_getElem?_getD, hR]

omit hv hI in
theorem lv_lrange : ∀ R, ∀ r ∈ (lv rule g w inp).getD R [], rangeOf g w r = R := by
  intro R r hr
  by_cases hR : R < g.ranges
  · rw [lv_getD hR, List.mem_filter] at hr; simpa using hr.2
  · simp [lv, leavesOf, List.getD_eq_getElem?_getD, hR] at hr

omit hv hI in
theorem lv_part {v : Nat} (hv' : v < g.homes) :
    ((lv rule g w inp).getD (v / 2 ^ g.lo) []).filter (fun r => home g w r == v) =
      Pv rule g w inp v := by
  rw [lv_getD (range_lt g hv'), Pv]
  apply filter_filter_of_imp
  intro r hr
  have : home g w r = v := by simpa using hr
  simp [rangeOf, this]

omit hv hI in
theorem parts_st0 {v : Nat} (hv' : v < g.homes) :
    parts g w (st0 rule g w inp) v = ⟨mv rule g w inp v, Pv rule g w inp v, Tv g w inp v, []⟩ := by
  simp only [parts, st0, mv, Tv, List.filter_nil, lv_part hv']

omit hv in
theorem src0_eq {i : Nat} (hi : i < g.U) : src0 g w inp.bMain i = Sv g w inp i := by
  unfold src0 Sv
  rw [Nat.mod_eq_of_lt hi]
  apply List.filter_congr
  intro r hr
  rw [home_split g w r i (hI.bHome i hi r hr)]
  have : i + g.U ≠ i := by have : 0 < g.U := Nat.two_pow_pos _; omega
  have hU0 : g.U ≠ 0 := Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _)
  cases dirBit w g.k r <;> simp [hU0]

omit hv in
theorem src1_eq {i : Nat} (hi : i < g.U) : src1 g w inp.bMain i = Sv g w inp (i + g.U) := by
  unfold src1 Sv
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  apply List.filter_congr
  intro r hr
  rw [home_split g w r i (hI.bHome i hi r hr)]
  have : i ≠ i + g.U := by have : 0 < g.U := Nat.two_pow_pos _; omega
  have hU0 : g.U ≠ 0 := Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _)
  cases dirBit w g.k r <;> simp [hU0]

/-- After the finish every home holds `homeStep` of its initial parts. -/
theorem parts_fin {v : Nat} (hv' : v < g.homes) : parts g w (fin rule g w inp) v = Hv rule g w inp v := by
  have hF := finish_inv g w inp (rt rule g w inp).main (lv rule g w inp) (rt_inv hv hI).len
    (by simp [lv, leavesOf]) lv_lrange hI.bHome
  rw [homes_eq] at hv'
  by_cases hlt : v < g.U
  · have := hF.lo v hlt
    simp only [hlt, ite_true] at this
    rw [fin, this]
    show homeStep _ _ (parts g w (st0 rule g w inp) v) = _
    rw [parts_st0 (rule := rule) (inp := inp) (v := v) (by rw [homes_eq]; omega), src0_eq hI hlt, Hv, Nat.mod_eq_of_lt hlt]
  · obtain ⟨i, rfl⟩ : ∃ i, v = i + g.U := ⟨v - g.U, by omega⟩
    have hi : i < g.U := by omega
    have := hF.hi i hi
    simp only [hi, ite_true] at this
    rw [fin, this]
    show homeStep _ _ (parts g w (st0 rule g w inp) (i + g.U)) = _
    rw [parts_st0 (rule := rule) (inp := inp) (v := i + g.U) (by rw [homes_eq]; omega), src1_eq hI hi, Hv, Nat.add_mod_right,
      Nat.mod_eq_of_lt hi]

theorem fin_inv : FInv g w inp.bMain (st0 rule g w inp) (fin rule g w inp) g.U :=
  finish_inv g w inp (rt rule g w inp).main (lv rule g w inp) (rt_inv hv hI).len
    (by simp [lv, leavesOf]) lv_lrange hI.bHome

/-- A's records, reordered along the route. -/
theorem aAll_perm : List.Perm inp.aAll ((rt rule g w inp).main.flatMap Bucket.recs ++
    ((rt rule g w inp).stash.flatten ++ inp.aTier)) := by
  rw [← List.append_assoc]
  exact ((rt_inv hv hI).perm.append_right inp.aTier).symm

theorem homeOK {v : Nat} (hv' : v < g.homes) :
    HomeOK (clrOf inp.bMain (v % g.U)) (Sv g w inp v) (mv rule g w inp v) (Pv rule g w inp v)
      (Tv g w inp v) where
  nodupA := by
    have hn : (((rt rule g w inp).main.flatMap Bucket.recs ++
        ((rt rule g w inp).stash.flatten ++ inp.aTier)).map Rec.key).Nodup :=
      nodup_keys_perm (aAll_perm hv hI).symm hI.aNodup
    refine nodup_keys_sublist (List.Sublist.append ?_ ?_) hn
    · exact sublist_flatMap_getD _ _ _ _ (by rw [(rt_inv hv hI).len]; exact hv')
    · exact List.filter_sublist.trans List.filter_sublist
  nodupB := by
    refine nodup_keys_sublist (List.Sublist.append ?_ List.filter_sublist) hI.bNodup
    exact List.filter_sublist.trans (sublist_flatMap_getD _ _ _ _ (by
      rw [hI.bLen]; exact Nat.mod_lt _ (Nat.two_pow_pos _)))
  PT := by
    intro r hr hk
    have h1 := (List.mem_filter.1 (List.mem_filter.1 hr).1).2
    have h2 : r.key ∈ inp.bTier.map Rec.key := (List.filter_sublist.map Rec.key).subset hk
    simp at h1
    obtain ⟨r', hr', he⟩ := List.mem_map.1 h2
    exact h1 r' hr' he
  clr := by
    intro r hr
    exact contains_home g w _ r (rt_home hv hI v hv' r hr)

theorem fin_main {v : Nat} (hv' : v < g.homes) :
    (fin rule g w inp).main.getD v [] = (Hv rule g w inp v).m :=
  congrArg HP.m (parts_fin hv hI hv')

theorem fin_P {v : Nat} (hv' : v < g.homes) :
    ((fin rule g w inp).leaves.getD (v / 2 ^ g.lo) []).filter (fun r => home g w r == v) =
      (Hv rule g w inp v).P :=
  congrArg HP.P (parts_fin hv hI hv')

theorem fin_T {v : Nat} (hv' : v < g.homes) :
    (fin rule g w inp).bcopy.filter (fun r => home g w r == v) = (Hv rule g w inp v).T :=
  congrArg HP.T (parts_fin hv hI hv')

theorem fin_I {v : Nat} (hv' : v < g.homes) :
    (fin rule g w inp).ins.filter (fun r => home g w r == v) = (Hv rule g w inp v).I :=
  congrArg HP.I (parts_fin hv hI hv')

/-- Every final main record sits at its home. -/
theorem fin_home {v : Nat} (hv' : v < g.homes) :
    ∀ r ∈ ((fin rule g w inp).main.getD v []).recs, home g w r = v := by
  rw [fin_main hv hI hv']
  apply homeStep_mem (fun r => home g w r = v) (rt_home hv hI v hv')
  · intro r hr; simpa using (List.mem_filter.1 hr).2
  · intro r hr; simpa using (List.mem_filter.1 hr).2
  · intro r hr; simpa using (List.mem_filter.1 hr).2

theorem fin_lanes {v : Nat} (hv' : v < g.homes) :
    ((fin rule g w inp).main.getD v []).length = g.C := by
  rw [fin_main hv hI hv', Hv, homeStep_length]
  exact (rt_inv hv hI).lanes _ (getD_mem _ _ _ (by rw [(rt_inv hv hI).len]; exact hv'))

omit hv hI in
/-- A main table whose bucket `j` holds only records of home `j`, filtered by home `v`. -/
theorem main_filter_home (M : List Bucket) (hlen : M.length = g.homes)
    (hM : ∀ j < g.homes, ∀ r ∈ (M.getD j []).recs, home g w r = j) {v : Nat} (hv' : v < g.homes) :
    (M.flatMap Bucket.recs).filter (fun r => home g w r == v) = (M.getD v []).recs := by
  rw [flatMap_filter_single M Bucket.recs _ [] v (by rw [hlen]; exact hv')]
  · exact filter_home_self g w v _ (hM v hv')
  · intro j' hj' hne
    apply filter_home_nil
    intro r hr
    rw [hM j' (by rw [← hlen]; exact hj') r hr]
    exact hne

theorem fin_leaves_filter {v : Nat} (hv' : v < g.homes) :
    (fin rule g w inp).leaves.flatten.filter (fun r => home g w r == v) = (Hv rule g w inp v).P := by
  rw [← fin_P hv hI hv', ← List.flatMap_id]
  have hF := fin_inv hv hI
  rw [flatMap_filter_single (fin rule g w inp).leaves id _ [] (v / 2 ^ g.lo)
    (by rw [hF.llen]; exact range_lt g hv')]
  · rfl
  · intro j' _ hne
    apply filter_home_nil
    intro r hr hrv
    have := hF.lrange j' r hr
    rw [rangeOf, hrv] at this
    exact hne this.symm

theorem fin_bcopy_sub : ∀ r ∈ (fin rule g w inp).bcopy, r ∈ inp.bTier := by
  intro r hr
  have hv' := home_lt g w r
  have : r ∈ (fin rule g w inp).bcopy.filter (fun x => home g w x == home g w r) := by
    simp [hr]
  rw [fin_T hv hI hv'] at this
  exact (List.mem_filter.1 ((homeStep_T_sub _ _ _ _ _).subset this)).1

theorem fin_ins_sub : ∀ r ∈ (fin rule g w inp).ins, r ∈ inp.bMain.flatMap Bucket.recs := by
  intro r hr
  have hv' := home_lt g w r
  have : r ∈ (fin rule g w inp).ins.filter (fun x => home g w x == home g w r) := by
    simp [hr]
  rw [fin_I hv hI hv', Hv, homeStep_I] at this
  have h1 := (List.mem_filter.1 (List.mem_of_mem_drop this)).1
  exact (sublist_flatMap_getD Bucket.recs inp.bMain _ [] (by
    rw [hI.bLen]; exact Nat.mod_lt _ (Nat.two_pow_pos _))).subset h1

/-- The output tier: A leftovers minus B's shed keys, B tier leftovers, B's sheds. -/
theorem tier_perm : List.Perm ((drain (fin rule g w inp)).1.filterMap id)
    ((fin rule g w inp).leaves.flatten.filter
        (fun r => !((fin rule g w inp).ins.map Rec.key).contains r.key) ++
      (fin rule g w inp).bcopy ++ (fin rule g w inp).ins) := by
  obtain ⟨K, hK, hp⟩ := drain_perm (fin rule g w inp)
  rw [filter_keys_self (fin rule g w inp).ins K] at hp
  · exact hp
  · intro r hr hk
    obtain ⟨r', hr', he⟩ := List.mem_map.1 (hK _ hk)
    have h1 := fin_bcopy_sub hv hI r' hr'
    have h2 := fin_ins_sub hv hI r hr
    exact keys_disjoint_of_nodup hI.bNodup r' h1 (he ▸ List.mem_map_of_mem h2)

/-- The tier's share of home `v`. -/
theorem tier_filter {v : Nat} (hv' : v < g.homes) :
    List.Perm (((drain (fin rule g w inp)).1.filterMap id).filter (fun r => home g w r == v))
      ((Hv rule g w inp v).P.filter (fun r => !((Hv rule g w inp v).I.map Rec.key).contains r.key) ++
        (Hv rule g w inp v).T ++ (Hv rule g w inp v).I) := by
  refine ((tier_perm hv hI).filter _).trans ?_
  rw [List.filter_append, List.filter_append, filter_comm, fin_leaves_filter hv hI hv',
    fin_T hv hI hv', fin_I hv hI hv']
  apply List.Perm.of_eq
  congr 2
  apply List.filter_congr
  intro r hr
  have hrv : home g w r = v := by
    have := (homeStep_P_sub _ _ _ _ _).subset hr
    simpa using (List.mem_filter.1 this).2
  rw [contains_home g w _ r hrv, fin_I hv hI hv']

omit hv in
theorem bMain_filter {v : Nat} :
    (inp.bMain.flatMap Bucket.recs).filter (fun r => home g w r == v) = Sv g w inp v := by
  have hU : 0 < g.U := Nat.two_pow_pos _
  rw [flatMap_filter_single inp.bMain Bucket.recs _ [] (v % g.U) (by rw [hI.bLen]; exact Nat.mod_lt _ hU)]
  · rfl
  · intro j' hj' hne
    apply filter_home_nil
    intro r hr hrv
    have h1 := hI.bHome j' (by rw [← hI.bLen]; exact hj') r hr
    have h2 : home g w r % g.U = w r.key % g.U := by
      unfold home
      exact Nat.mod_mod_of_dvd _ (by rw [homes_eq]; exact ⟨2, by omega⟩)
    rw [hrv, h1] at h2
    exact hne h2.symm

omit hv in
theorem bAll_filter {v : Nat} :
    inp.bAll.filter (fun r => home g w r == v) = Sv g w inp v ++ Tv g w inp v := by
  rw [Inputs.bAll, List.filter_append, bMain_filter hI]; rfl

/-- The union's share of home `v`. -/
theorem winners_filter {v : Nat} (hv' : v < g.homes) :
    List.Perm (inp.winners.filter (fun r => home g w r == v))
      (Sv g w inp v ++ Tv g w inp v ++
        (mv rule g w inp v).recs.filter
          (fun r => !((Sv g w inp v ++ Tv g w inp v).map Rec.key).contains r.key) ++
        (Pv rule g w inp v).filter (fun r => !((Sv g w inp v).map Rec.key).contains r.key)) := by
  rw [Inputs.winners, List.filter_append, bAll_filter hI]
  simp only [List.append_assoc]
  refine List.Perm.append_left _ (List.Perm.append_left _ ?_)
  refine (((aAll_perm hv hI).filter _).filter _).trans ?_
  rw [filter_comm, List.filter_append,
    main_filter_home (rt rule g w inp).main (rt_inv hv hI).len (rt_home hv hI) hv', List.filter_append]
  apply List.Perm.of_eq
  congr 1
  · apply List.filter_congr
    intro r hr
    rw [contains_home g w _ r (rt_home hv hI v hv' r hr), bAll_filter hI]
  · simp only [Pv, pl, poolA, List.filter_filter]
    apply List.filter_congr
    intro r _
    by_cases hrv : home g w r = v
    · rw [contains_home g w inp.bAll r hrv, bAll_filter hI, keys_contains_append,
        contains_home g w inp.bTier r hrv]
      simp only [hrv, beq_self_eq_true, Bool.and_true, Bool.true_and, Tv]
      cases ((Sv g w inp v).map Rec.key).contains r.key <;>
        cases ((inp.bTier.filter fun r => home g w r == v).map Rec.key).contains r.key <;> rfl
    · have hf : (home g w r == v) = false := by simpa using hrv
      rw [hf]; simp

end main

end RebuildBound.D23
