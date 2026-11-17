import RebuildBound.Proofs.S12.RouteHome
import RebuildBound.Proofs.S12.Insert
import RebuildBound.Proofs.S12.Drain

/-!
# S12: the reference execution, home by home

Names for the phases of the reference execution (`srt`, `spl`, `slv`,
`sfin`) and for the initial parts of home `v` (`smv`, `sPv`, `sTv`, `sSv`);
after the finish every home holds `gStep` of its initial parts (`sHv`,
`parts_fin`), whose inputs meet `GHomeOK` (`homeOK`). The route's placement
(every main record of the route at its home) is a hypothesis `RouteHome`
here; `S12.lean` derives it from ST6.
-/

namespace RebuildBound.S12

open RebuildBound.Model RebuildBound.D23

/-! ### Generic facts -/

theorem contains_sHome (g : SepGeom) (w : Model.LogicalKey → Nat) (L : List Rec) (r : Rec) {v : Nat}
    (hr : sHome g w r = v) :
    (L.map Rec.key).contains r.key = ((hfil g w v L).map Rec.key).contains r.key := by
  apply Bool.eq_iff_iff.2
  simp only [List.contains_iff_mem, List.mem_map, mem_hfil]
  constructor
  · rintro ⟨r', hr', he⟩
    exact ⟨r', ⟨hr', by rw [sHome_of_key g w he, hr]⟩, he⟩
  · rintro ⟨r', ⟨hr', _⟩, he⟩
    exact ⟨r', hr', he⟩

theorem count_hfil (g : SepGeom) (w : Model.LogicalKey → Nat) (x : Rec) (L : List Rec) :
    L.count x = (hfil g w (sHome g w x) L).count x := by
  unfold hfil; rw [List.count_filter]; simp

/-- A main table whose bucket `j` holds only records of home `j`, filtered by home `v`. -/
theorem main_hfil (g : SepGeom) (w : Model.LogicalKey → Nat) (M : List Bucket) (hlen : M.length = g.N)
    (hM : ∀ j < g.N, ∀ r ∈ (M.getD j []).recs, sHome g w r = j) {v : Nat} (hv : v < g.N) :
    hfil g w v (M.flatMap Bucket.recs) = (M.getD v []).recs := by
  unfold hfil
  rw [flatMap_filter_single M Bucket.recs _ [] v (by rw [hlen]; exact hv)]
  · exact hfil_self g w v _ (hM v hv)
  · intro j' hj' hne
    apply hfil_nil_of
    intro r hr
    rw [hM j' (by rw [← hlen]; exact hj') r hr]
    exact hne

theorem srcW_eq (g : SepGeom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) {v : Nat}
    (hB : ∀ x ∈ (bMain.getD (v % g.U) []).recs, w x.key % g.U = v % g.U) :
    srcW g w bMain (v % g.U) (v / g.U) = hfil g w v ((bMain.getD (v % g.U) []).recs) := by
  unfold srcW hfil
  apply List.filter_congr
  intro x hx
  rw [sHome_carry g w x (hB x hx)]
  have hU := U_pos g
  have e := home_decomp g v
  apply Bool.eq_iff_iff.2
  simp only [beq_iff_eq]
  constructor
  · intro h; rw [h]; exact e.symm
  · intro h
    have : g.wayOf (w x.key) * g.U = v / g.U * g.U := by omega
    exact Nat.eq_of_mul_eq_mul_right hU this

/-! ### The reference execution -/

section ref
variable (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat))

/-- A's route. -/
def srt : SRoute := sRouteWith rule g w inp.aMain ops
/-- The swept A pool. -/
def spl : List Rec := sPool (srt rule g w inp ops) inp.aTier inp.bTier
/-- The DFS leaves. -/
def slv : List (List Rec) := sLeaves g w (spl rule g w inp ops)
/-- The final finish state. -/
def sfin : SFin := sFinish g w inp (srt rule g w inp ops).main (slv rule g w inp ops)

theorem sref_output : (sReferenceWith rule g w inp ops).output =
    ⟨(sfin rule g w inp ops).main, (sDrain (sfin rule g w inp ops)).1⟩ := rfl

/-- Home `v`'s initial main bucket. -/
def smv (v : Nat) : Bucket := (srt rule g w inp ops).main.getD v []
/-- Home `v`'s A candidates. -/
def sPv (v : Nat) : List Rec := hfil g w v (spl rule g w inp ops)
/-- Home `v`'s B tier candidates, page by page. -/
def sTv (v : Nat) : List (List Rec) := inp.bTier.map (hfil g w v)
/-- B's main records of home `v`. -/
def sSv (v : Nat) : List Rec := srcW g w inp.bMain (v % g.U) (v / g.U)
/-- Home `v` after the finish. -/
def sHv (v : Nat) : GP :=
  gStep (clrOf inp.bMain (v % g.U)) (sSv g w inp v)
    ⟨smv rule g w inp ops v, sPv rule g w inp ops v, sTv g w inp v, []⟩

/-- Every main record of the route sits at its home. -/
def RouteHome : Prop :=
  ∀ v < g.N, ∀ x ∈ ((srt rule g w inp ops).main.getD v []).recs, sHome g w x = v

end ref

section main
variable {rule : CapRule} {g : SepGeom} {wOld w : Model.LogicalKey → Nat} {inp : SInputs}
  {ops : List (Nat × Nat)}
variable (hv : rule.Valid) (hg : g.Valid) (hS : SInputShape g wOld w inp)
  (hops : List.Perm ops g.canonicalOps) (hH : RouteHome rule g w inp ops)
include hv hg hS hops

theorem srt_inv : SRInv g inp.aMain (srt rule g w inp ops) :=
  route_SRInv hv hg w hS.aLen hS.aLanes hops

omit hv hg hS hops in
theorem slv_getD {R : Nat} (hR : R < g.ranges) :
    (slv rule g w inp ops).getD R [] = (spl rule g w inp ops).filter fun x => sRange g w x == R := by
  simp [slv, sLeaves, List.getD_eq_getElem?_getD, hR]

omit hv hg hS hops in
theorem slv_length : (slv rule g w inp ops).length = g.ranges := by simp [slv, sLeaves]

omit hv hg hS hops in
theorem slv_lrange : ∀ R, ∀ x ∈ (slv rule g w inp ops).getD R [], sRange g w x = R := by
  intro R x hx
  by_cases hR : R < g.ranges
  · rw [slv_getD hR, List.mem_filter] at hx; simpa using hx.2
  · simp [slv, sLeaves, List.getD_eq_getElem?_getD, hR] at hx

omit hv hS hops in
theorem slv_part {v : Nat} (hv' : v < g.N) :
    hfil g w v ((slv rule g w inp ops).getD (v / 2 ^ g.I) []) = sPv rule g w inp ops v := by
  rw [slv_getD (range_lt g hg hv'), sPv, hfil, hfil]
  apply filter_filter_of_imp
  intro r hr
  have : sHome g w r = v := by simpa using hr
  simp [sRange, this]

omit hv hg hS hops in
theorem parts_fin0 (v : Nat) :
    gparts g w (fin0 inp (srt rule g w inp ops).main (slv rule g w inp ops))
      (fin0 inp (srt rule g w inp ops).main (slv rule g w inp ops)).ins v =
    ⟨smv rule g w inp ops v, hfil g w v ((slv rule g w inp ops).getD (v / 2 ^ g.I) []),
      sTv g w inp v, []⟩ := rfl

theorem sfin_inv : GFInv g w inp.bMain (fin0 inp (srt rule g w inp ops).main (slv rule g w inp ops))
    (sfin rule g w inp ops) g.U :=
  sFinish_inv hg w inp _ _ (srt_inv hv hg hS hops).len slv_length slv_lrange hS.bHome

/-- After the finish every home holds `gStep` of its initial parts. -/
theorem parts_fin {v : Nat} (hv' : v < g.N) :
    gparts g w (sfin rule g w inp ops) (sfin rule g w inp ops).ins v = sHv rule g w inp ops v := by
  rw [(sfin_inv hv hg hS hops).parts v hv', ite_eq_left (Nat.mod_lt _ (U_pos g)), parts_fin0,
    slv_part hg hv']
  rfl

theorem sfin_main {v : Nat} (hv' : v < g.N) :
    (sfin rule g w inp ops).main.getD v [] = (sHv rule g w inp ops v).m :=
  congrArg GP.m (parts_fin hv hg hS hops hv')
theorem sfin_P {v : Nat} (hv' : v < g.N) :
    hfil g w v ((sfin rule g w inp ops).leaves.getD (v / 2 ^ g.I) []) = (sHv rule g w inp ops v).P :=
  congrArg GP.P (parts_fin hv hg hS hops hv')
theorem sfin_T {v : Nat} (hv' : v < g.N) :
    (sfin rule g w inp ops).bcopy.map (hfil g w v) = (sHv rule g w inp ops v).T :=
  congrArg GP.T (parts_fin hv hg hS hops hv')
theorem sfin_I {v : Nat} (hv' : v < g.N) :
    hfil g w v (sfin rule g w inp ops).ins = (sHv rule g w inp ops v).I :=
  congrArg GP.I (parts_fin hv hg hS hops hv')

/-- A's records, reordered along the route. -/
theorem aAll_perm : List.Perm inp.aAll ((srt rule g w inp ops).main.flatMap Bucket.recs ++
    ((srt rule g w inp ops).stash.flatten ++ (srt rule g w inp ops).radix ++ inp.aTier)) := by
  rw [← List.append_assoc, ← List.append_assoc]
  exact ((srt_inv hv hg hS hops).perm.append_right inp.aTier).symm

omit hv hg hops in
theorem bucket_home {i : Nat} (hi : i < g.U) :
    ∀ x ∈ (inp.bMain.getD i []).recs, w x.key % g.U = i := hS.bHome i hi

omit hv hg hops in
theorem sSv_eq (v : Nat) : sSv g w inp v = hfil g w v ((inp.bMain.getD (v % g.U) []).recs) :=
  srcW_eq g w inp.bMain (bucket_home hS (Nat.mod_lt _ (U_pos g)))

omit hv hg hops in
theorem sSv_sub (v : Nat) : List.Sublist (sSv g w inp v) (inp.bMain.flatMap Bucket.recs) := by
  rw [sSv_eq hS]
  exact List.filter_sublist.trans (sublist_flatMap_getD _ _ _ _ (by
    rw [hS.bLen]; exact Nat.mod_lt _ (U_pos g)))

omit hv hg hS hops in
theorem sTv_flatten (v : Nat) : (sTv g w inp v).flatten = hfil g w v inp.bTier.flatten := by
  unfold sTv hfil; rw [List.filter_flatten]

include hH in
theorem homeOK {v : Nat} (hv' : v < g.N) :
    GHomeOK (clrOf inp.bMain (v % g.U)) (sSv g w inp v) (smv rule g w inp ops v)
      (sPv rule g w inp ops v) (sTv g w inp v) where
  nodupA := by
    have hn := nodup_keys_perm (aAll_perm hv hg hS hops).symm hS.aNodup
    refine nodup_keys_sublist (List.Sublist.append ?_ ?_) hn
    · exact sublist_flatMap_getD _ _ _ _ (by rw [(srt_inv hv hg hS hops).len]; exact hv')
    · exact List.filter_sublist.trans List.filter_sublist
  nodupB := by
    refine nodup_keys_sublist (List.Sublist.append (sSv_sub hS v) ?_) hS.bNodup
    rw [sTv_flatten]; exact List.filter_sublist
  PT := by
    intro r hr hk
    have h1 := (List.mem_filter.1 (mem_hfil.1 hr).1).2
    rw [sTv_flatten] at hk
    have h2 : r.key ∈ inp.bTier.flatten.map Rec.key := (List.filter_sublist.map Rec.key).subset hk
    have h3 : (inp.bTier.flatten.map Rec.key).contains r.key = true := (keys_contains_iff _ _).2 h2
    have h1' : (!(inp.bTier.flatten.map Rec.key).contains r.key) = true := h1
    rw [h3] at h1'
    exact absurd h1' (by decide)
  clr := by
    intro r hr
    have hrv := hH v hv' r hr
    rw [sSv_eq hS, ← contains_sHome g w _ r hrv]
    rfl

include hH in
/-- Every final main record sits at its home. -/
theorem sfin_home {v : Nat} (hv' : v < g.N) :
    ∀ r ∈ ((sfin rule g w inp ops).main.getD v []).recs, sHome g w r = v := by
  rw [sfin_main hv hg hS hops hv']
  apply gStep_mem (fun r => sHome g w r = v) (hH v hv')
  · intro r hr
    exact srcW_home g w inp.bMain (bucket_home hS (Nat.mod_lt _ (U_pos g))) r hr |>.trans
      (home_decomp g v).symm
  · intro r hr; exact (mem_hfil.1 hr).2
  · intro r hr
    rw [sTv_flatten] at hr
    exact (mem_hfil.1 hr).2

theorem sfin_lanes {v : Nat} (hv' : v < g.N) :
    ((sfin rule g w inp ops).main.getD v []).length = g.C := by
  rw [sfin_main hv hg hS hops hv', sHv, gStep_length]
  exact (srt_inv hv hg hS hops).lanes _ (getD_mem _ _ _ (by
    rw [(srt_inv hv hg hS hops).len]; exact hv'))

theorem sfin_leaves_hfil {v : Nat} (hv' : v < g.N) :
    hfil g w v (sfin rule g w inp ops).leaves.flatten = (sHv rule g w inp ops v).P := by
  rw [← sfin_P hv hg hS hops hv', ← List.flatMap_id]
  have hF := sfin_inv hv hg hS hops
  unfold hfil
  rw [flatMap_filter_single (sfin rule g w inp ops).leaves id _ [] (v / 2 ^ g.I)
    (by rw [hF.llen]; exact range_lt g hg hv')]
  · rfl
  · intro j' _ hne
    apply hfil_nil_of
    intro r hr hrv
    have := hF.lrange j' r hr
    rw [sRange, hrv] at this
    exact hne this.symm

theorem sfin_ins_sub : ∀ r ∈ (sfin rule g w inp ops).ins, r ∈ inp.bMain.flatMap Bucket.recs := by
  intro r hr
  have hv' := sHome_lt g hg.1 w r
  have : r ∈ hfil g w (sHome g w r) (sfin rule g w inp ops).ins := mem_hfil.2 ⟨hr, rfl⟩
  rw [sfin_I hv hg hS hops hv', sHv, gStep_I_eq] at this
  exact (sSv_sub hS _).subset (List.mem_of_mem_drop this)

theorem sfin_bcopy_sub : ∀ r ∈ (sfin rule g w inp ops).bcopy.flatten, r ∈ inp.bTier.flatten := by
  intro r hr
  have hv' := sHome_lt g hg.1 w r
  obtain ⟨L, hL, hrL⟩ := List.mem_flatten.1 hr
  have : r ∈ ((sfin rule g w inp ops).bcopy.map (hfil g w (sHome g w r))).flatten :=
    List.mem_flatten.2 ⟨_, List.mem_map_of_mem hL, mem_hfil.2 ⟨hrL, rfl⟩⟩
  rw [sfin_T hv hg hS hops hv', sHv] at this
  have h2 := (gStep_T_sub _ _ _ _ _).subset this
  rw [sTv_flatten] at h2
  exact (mem_hfil.1 h2).1

/-- The output tier: A leftovers minus B's shed keys, B tier leftovers, B's sheds. -/
theorem tier_perm : List.Perm ((sDrain (sfin rule g w inp ops)).1.filterMap id)
    ((sfin rule g w inp ops).leaves.flatten.filter
        (fun r => !((sfin rule g w inp ops).ins.map Rec.key).contains r.key) ++
      (sfin rule g w inp ops).bcopy.flatten ++ (sfin rule g w inp ops).ins) := by
  obtain ⟨K, hK, hp⟩ := sDrain_perm (sfin rule g w inp ops)
  rw [filter_keys_self (sfin rule g w inp ops).ins K] at hp
  · exact hp
  · intro r hr hk
    obtain ⟨r', hr', he⟩ := List.mem_map.1 (hK _ hk)
    have h1 := sfin_bcopy_sub hv hg hS hops r' hr'
    have h2 := sfin_ins_sub hv hg hS hops r hr
    have hb : ∀ r ∈ inp.bTier.flatten, r.key ∉ (inp.bMain.flatMap Bucket.recs).map Rec.key :=
      keys_disjoint_of_nodup hS.bNodup
    exact hb r' h1 (he ▸ List.mem_map_of_mem h2)

/-- The tier's share of home `v`. -/
theorem tier_hfil {v : Nat} (hv' : v < g.N) :
    List.Perm (hfil g w v ((sDrain (sfin rule g w inp ops)).1.filterMap id))
      ((sHv rule g w inp ops v).P.filter
          (fun r => !((sHv rule g w inp ops v).I.map Rec.key).contains r.key) ++
        (sHv rule g w inp ops v).T.flatten ++ (sHv rule g w inp ops v).I) := by
  refine ((tier_perm hv hg hS hops).filter _).trans ?_
  rw [List.filter_append, List.filter_append, filter_comm]
  change List.Perm (List.filter _ (hfil g w v (sfin rule g w inp ops).leaves.flatten) ++
    hfil g w v (sfin rule g w inp ops).bcopy.flatten ++ hfil g w v (sfin rule g w inp ops).ins) _
  rw [sfin_leaves_hfil hv hg hS hops hv', sfin_I hv hg hS hops hv']
  have hT : hfil g w v (sfin rule g w inp ops).bcopy.flatten = (sHv rule g w inp ops v).T.flatten := by
    rw [← sfin_T hv hg hS hops hv']; unfold hfil; rw [List.filter_flatten]
  rw [hT]
  apply List.Perm.of_eq
  congr 2
  apply List.filter_congr
  intro r hr
  have hrv : sHome g w r = v := by
    have := (gStep_P_sub _ _ _ _ _).subset hr
    exact (mem_hfil.1 this).2
  rw [contains_sHome g w _ r hrv, sfin_I hv hg hS hops hv']

omit hv hg hops in
theorem bMain_hfil (v : Nat) :
    hfil g w v (inp.bMain.flatMap Bucket.recs) = sSv g w inp v := by
  have hU := U_pos g
  unfold hfil
  rw [flatMap_filter_single inp.bMain Bucket.recs _ [] (v % g.U)
    (by rw [hS.bLen]; exact Nat.mod_lt _ hU)]
  · rw [sSv_eq hS]; rfl
  · intro j' hj' hne
    apply hfil_nil_of
    intro r hr hrv
    have h1 := hS.bHome j' (by rw [← hS.bLen]; exact hj') r hr
    have h2 : sHome g w r % g.U = w r.key % g.U := homeOf_mod g _
    rw [hrv, h1] at h2
    exact hne h2.symm

omit hv hg hops in
theorem bAll_hfil (v : Nat) : hfil g w v inp.bAll = sSv g w inp v ++ (sTv g w inp v).flatten := by
  rw [SInputs.bAll, hfil_append, bMain_hfil hS, sTv_flatten]

include hH in
/-- The union's share of home `v`. -/
theorem winners_hfil {v : Nat} (hv' : v < g.N) :
    List.Perm (hfil g w v inp.winners)
      (sSv g w inp v ++ (sTv g w inp v).flatten ++
        (smv rule g w inp ops v).recs.filter
          (fun r => !((sSv g w inp v ++ (sTv g w inp v).flatten).map Rec.key).contains r.key) ++
        (sPv rule g w inp ops v).filter (fun r => !((sSv g w inp v).map Rec.key).contains r.key)) := by
  rw [SInputs.winners, hfil_append, bAll_hfil hS]
  simp only [List.append_assoc]
  refine List.Perm.append_left _ (List.Perm.append_left _ ?_)
  refine (((aAll_perm hv hg hS hops).filter _).filter _).trans ?_
  have hmh := main_hfil g w (srt rule g w inp ops).main (srt_inv hv hg hS hops).len hH hv'
  unfold hfil at hmh
  rw [filter_comm, List.filter_append, hmh, List.filter_append]
  apply List.Perm.of_eq
  congr 1
  · apply List.filter_congr
    intro r hr
    rw [contains_sHome g w _ r (hH v hv' r hr), bAll_hfil hS]
  · simp only [sPv, spl, sPool, hfil, List.filter_filter]
    apply List.filter_congr
    intro r _
    by_cases hrv : sHome g w r = v
    · rw [contains_sHome g w inp.bAll r hrv, bAll_hfil hS, keys_contains_append,
        contains_sHome g w inp.bTier.flatten r hrv, ← sTv_flatten]
      simp only [hrv, beq_self_eq_true, Bool.and_true, Bool.true_and]
      cases ((sSv g w inp v).map Rec.key).contains r.key <;>
        cases ((sTv g w inp v).flatten.map Rec.key).contains r.key <;> rfl
    · have hf : (sHome g w r == v) = false := by simpa using hrv
      rw [hf]; simp

end main

end RebuildBound.S12
