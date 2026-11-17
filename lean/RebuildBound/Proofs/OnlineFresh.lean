import RebuildBound.Proofs.OnlineFresh.Flow
import RebuildBound.Proofs.HierarchyInvariantChunks
import RebuildBound.Proofs.HierarchyHorizonFree
import RebuildBound.Spec.Oblivious

/-!
# OnlineFresh: every real probe reads a distinct family-tape word

Why the view is simulatable.

(a) A real entry's table is a published coordinate whose window ends at or
before `pos j < s_1 P + H`, so its family is a coordinate of the horizon
(`familyOf_mem`); its key is below `N` by the run premises.

(b) All members of a family share their window end (`familyOf_end`). Two
entries of one plan have distinct ends (lower windows are nonempty and there
is at most one top entry, including the possibly empty initial top).
For `j < j'` with the same family and key `k`, let `t ∈ [j, j')` be the last
operation of key `k` before `j'`. Its record is still in the requester at
`j'` (`inv_stateAt`): in the dense prefix, or in a consumed unit whose
position `q = pos t` lies in some plan table `c*` (`tiles_cover`). That table
ends after `q ≥ pos j ≥` the family's end, so it precedes `c'` in the plan,
hence is below the top (the top's window begins at 0), and holds `k`
(`flow`). Either way `(j', i')` is not real.
-/

namespace RebuildBound.OnlineFreshProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.Online RebuildBound.Spec
open RebuildBound.HierarchyInvariantProof

theorem isReal_true {cfg : Config} {sh : Shapes} {g : OnlineGeom} {run : OnlineRun} {S : Schedule}
    {words : Words} {j i : Nat} (h : isReal cfg sh g run S words j i = true) :
    ∃ o, run.ops[j]? = some o ∧ o.record.key ∉ denseKeys cfg g run S j ∧
      ∀ c ∈ (S j).tables.take i, o.record.key ∉ tableKeys cfg sh g run words c.1 c.2 := by
  unfold isReal at h
  cases ho : run.ops[j]? with
  | none => rw [ho] at h; simp at h
  | some o =>
    rw [ho] at h
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_true,
      List.elem_eq_mem, decide_eq_false_iff_not] at h
    exact ⟨o, rfl, h.1.2, h.2⟩

theorem mem_recs {B : Bucket} {r : Rec} (h : some r ∈ B) : r ∈ Bucket.recs B :=
  List.mem_filterMap.2 ⟨some r, h, rfl⟩

section main
variable (geo : HierarchyGeometry)

/-- The positions argument: a later operation of the same key does not get a
real probe in a member of the family. -/
theorem coreFor (F : LowFacts geo.cfg geo.rows geo.direct) {N : Nat} {g : OnlineGeom}
    {run : OnlineRun} {S : Schedule} {n m : Nat}
    (hR : OnlineRunPremises geo.cfg geo.shapes N g run) (hS : SchedulePremises geo.cfg S n m)
    (hn : n ≤ run.ops.length) (words : Words) {j j' i' : Nat} {c c' : Nat × Nat} {o o' : Op}
    (hjj : j < j') (hj' : j' < n) (hc : c ∈ (S j).tables) (ho : run.ops[j]? = some o)
    (hc' : (S j').tables[i']? = some c') (ho' : run.ops[j']? = some o')
    (hk : o.record.key = o'.record.key) (hend : we geo.cfg c = we geo.cfg c')
    (hreal : isReal geo.cfg geo.shapes g run S words j' i' = true) : False := by
  obtain ⟨o'', ho'', hdense, htab⟩ := isReal_true hreal
  rw [ho'] at ho''
  cases ho''
  have hj : j < n := lt_trans hjj hj'
  -- the last operation of the key before `j'`
  have hPj : keyAt run j = some o'.record.key := by simp [keyAt, ho, hk]
  obtain ⟨t, hjt, htj', hPt, hlast⟩ := last_occ (fun u => keyAt run u = some o'.record.key) hjj hPj
  obtain ⟨ot, hot, hotk⟩ : ∃ ot, run.ops[t]? = some ot ∧ ot.record.key = o'.record.key := by
    simp only [keyAt, Option.map_eq_some_iff] at hPt
    exact hPt
  have hinv := inv_stateAt g run hR.geom.2 j' (by omega)
  have hpl := hinv.placed t ot htj' hot (fun u h1 h2 => by rw [hotk]; exact hlast u h1 h2)
  -- the dense prefix at `j'`
  have hdk : ∀ B ∈ (stateAt g run j').frozen.drop
      (((S j').consumed - geo.cfg.seed 1) * g.unitsPerPrefix), some ot.record ∈ B → False := by
    intro B hB hm
    apply hdense
    simp only [denseKeys]
    exact List.mem_map.2 ⟨ot.record,
      List.mem_append_left _ (List.mem_flatMap.2 ⟨B, hB, mem_recs hm⟩), hotk⟩
  rcases hpl with ⟨u, hu, hu1, hu2, hmem⟩ | ⟨-, hmem⟩
  swap
  · apply hdense
    simp only [denseKeys]
    exact List.mem_map.2 ⟨ot.record, List.mem_append_right _ (mem_recs hmem), hotk⟩
  by_cases hD : ((S j').consumed - geo.cfg.seed 1) * g.unitsPerPrefix ≤ u
  · refine hdk _ (List.mem_of_getElem? (i := u - ((S j').consumed - geo.cfg.seed 1) * g.unitsPerPrefix) ?_) hmem
    rw [List.getElem?_drop, Nat.add_sub_cancel' hD, List.getElem?_eq_getElem hu]
  -- the record lies in a consumed prefix
  rw [Nat.not_le] at hD
  have hgeom := hR.geom.1
  generalize hE : g.unitEntries = E at hgeom hu1 hu2 hD
  generalize hr0 : g.unitsPerPrefix = r0 at hgeom hD hdk
  generalize hP : geo.cfg.carryPositions 1 = P at hgeom
  have hcj := hS.consumed j hj
  have hcj' := hS.consumed j' hj'
  have hPpos : 0 < P := by rw [← hP]; exact cp_pos F le_rfl (by have := F.levels2; omega)
  have hr0pos : 0 < r0 := by
    rcases Nat.eq_zero_or_pos r0 with h | h
    · rw [h, Nat.mul_zero] at hgeom; omega
    · exact h
  rw [hP] at hcj hcj'
  simp only [pos] at hcj hcj'
  rw [hP] at hcj hcj'
  -- the position of the record
  have hq1 : geo.cfg.seed 1 * P + t < (S j').consumed * P := by
    have h1 : (u + 1) * E ≤ ((S j').consumed - geo.cfg.seed 1) * r0 * E :=
      Nat.mul_le_mul_right _ hD
    have h2 : ((S j').consumed - geo.cfg.seed 1) * r0 * E = ((S j').consumed - geo.cfg.seed 1) * P := by
      rw [← hgeom]; ring
    have h3 : geo.cfg.seed 1 * P + ((S j').consumed - geo.cfg.seed 1) * P = (S j').consumed * P := by
      rw [← Nat.add_mul, Nat.add_sub_cancel' hcj'.1]
    omega
  have hcend : we geo.cfg c ≤ (S j).consumed * P := by
    have := (tiles_bounds (hS.tile j hj) c hc).2.2
    rw [hP] at this; exact this
  obtain ⟨is, cs, hcs, hcs1, hcs2⟩ := tiles_cover (hS.tile j' hj') (Nat.zero_le _)
    (by rw [hP]; exact hq1)
  have hb' := (tiles_bounds (hS.tile j' hj') c' (List.mem_of_getElem? hc')).2.1
  -- the covering table precedes `c'`
  have hlt : is < i' := by
    rcases lt_trichotomy is i' with h | h | h
    · exact h
    · subst h
      rw [hc'] at hcs; cases hcs
      omega
    · have := tiles_order (hS.tile j' hj') hc' hcs h
      omega
  have hpub : Published geo.cfg cs := hS.coords j' hj' cs (List.mem_of_getElem? hcs)
  -- and is below the top
  have hlow : cs.1 < geo.cfg.levels :=
    tiles_before_low F (hS.tile j' hj') (hS.coords j' hj') (hS.oneTop j' hj') hcs hc' hlt
  have hsv : geo.cfg.seed cs.1 < cs.2 := hpub.2.2.1 hlow
  -- the record's level-one ordinal
  have hpre := frozen_prefix g run (j := j') run.ops.length (by omega) le_rfl
  obtain ⟨tl, htl⟩ := hpre
  have hT := hR.trace
  have hq : ∀ w, geo.cfg.seed 1 < w → (w - 1) * geo.cfg.carryPositions 1 ≤ geo.cfg.seed 1 * P + t →
      geo.cfg.seed 1 * P + t < w * geo.cfg.carryPositions 1 →
      o'.record.key ∈ (DirectMasks.records ((traceOf g run).units (w - geo.cfg.seed 1 - 1))).map
        Rec.key := by
    intro w _ hw1 hw2
    rw [hP] at hw1 hw2
    have hi1 : u / r0 * r0 ≤ u := Nat.div_mul_le_self u r0
    have hi2 : u < u / r0 * r0 + r0 := Nat.lt_div_mul_add hr0pos
    generalize u / r0 = i0 at hi1 hi2
    have ht1 : (geo.cfg.seed 1 + i0) * P ≤ geo.cfg.seed 1 * P + t := by
      have := Nat.mul_le_mul_right E hi1
      rw [Nat.add_mul, ← hgeom]
      have e : i0 * (E * r0) = i0 * r0 * E := by ring
      omega
    have ht2 : geo.cfg.seed 1 * P + t < (geo.cfg.seed 1 + i0 + 1) * P := by
      have := Nat.mul_le_mul_right E (show u + 1 ≤ i0 * r0 + r0 by omega)
      rw [Nat.add_mul, Nat.add_mul, ← hgeom]
      have e : (i0 * r0 + r0) * E = i0 * (E * r0) + 1 * (E * r0) := by ring
      omega
    have hw3 : geo.cfg.seed 1 + i0 < w := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt ht1 hw2)
    have hw4 : w - 1 < geo.cfg.seed 1 + i0 + 1 := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt hw1 ht2)
    have hwi : w - geo.cfg.seed 1 - 1 = i0 := by omega
    rw [hwi]
    refine List.mem_map.2 ⟨ot.record, List.mem_flatMap.2 ⟨(stateAt g run j').frozen[u], ?_,
      mem_recs hmem⟩, hotk⟩
    simp only [traceOf]
    rw [hr0]
    refine List.mem_of_getElem? (i := u - i0 * r0) ?_
    rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop, Nat.add_sub_cancel' hi1, ← htl,
      List.getElem?_append_left hu, List.getElem?_eq_getElem hu]
  have hwin1 := hcs1
  have hwin2 := hcs2
  simp only [wb, we] at hwin1 hwin2
  rw [window_fst_low geo.cfg _ (by omega)] at hwin1
  rw [window_snd] at hwin2
  rw [← hP] at hwin1 hwin2 hq
  have hkey := flowFor geo F hT words hq cs.1 hpub.1 hlow cs.2 hsv hwin1 hwin2
  refine htab cs ?_ hkey
  refine List.mem_of_getElem? (i := is) ?_
  rw [List.getElem?_take, if_pos hlt, hcs]

/-- `OnlineFresh` from the invariant's lower facts, for either start. -/
theorem freshFor (F : LowFacts geo.cfg geo.rows geo.direct) : OnlineFreshFor geo := by
  intro N g run S n m hset words
  obtain ⟨-, hn, hR, hS⟩ := hset
  have hlevels := F.levels2
  have hcp1 := cp_pos F (ℓ := 1) le_rfl (by omega)
  -- a table's family shares its window end
  have hfend : ∀ j < n, ∀ c ∈ (S j).tables,
      (familyOf geo.cfg c.1 c.2).2 * geo.cfg.carryPositions (familyOf geo.cfg c.1 c.2).1 = we geo.cfg c := by
    intro j hj c hc
    have hpub : Published geo.cfg c := hS.coords j hj c hc
    rw [familyOf_end F hpub.1 hpub.2.1 hpub.seed_le, we, window_snd]
  refine ⟨?_, ?_⟩
  · intro j i hj hi hreal
    obtain ⟨o, ho, -⟩ := isReal_true hreal
    have hc : (S j).tables[i]'hi ∈ (S j).tables := List.getElem_mem hi
    refine ⟨_, o, List.getElem?_eq_getElem hi, ho, ?_, hR.keys o (List.mem_of_getElem? ho)⟩
    have hpub : Published geo.cfg ((S j).tables[i]'hi) := hS.coords j hj _ hc
    apply familyOf_mem F hpub.1 hpub.2.1 hpub.seed_le
    have h1 := (tiles_bounds (hS.tile j hj) _ hc).2.2
    have h2 := (hS.consumed j hj).2
    have h3 := hR.horizon
    simp only [we, window_snd, pos] at h1 h2
    omega
  · intro j i j' i' c c' o o' hj hi hj' hi' hne hr hr' hc hc' ho ho' heq
    obtain ⟨hf, hk⟩ := Prod.mk.inj heq
    have hcm := List.mem_of_getElem? hc
    have hcm' := List.mem_of_getElem? hc'
    have hend : we geo.cfg c = we geo.cfg c' := by
      rw [← hfend j hj c hcm, ← hfend j' hj' c' hcm', hf]
    rcases lt_trichotomy j j' with h | h | h
    · exact coreFor geo F hR hS hn words h hj' hcm ho hc' ho' hk hend hr'
    · subst h
      have hii : i ≠ i' := fun e => hne (by rw [e])
      rcases Nat.lt_or_gt_of_ne hii with h | h
      · exact tiles_ne_end F (hS.tile j hj) (hS.coords j hj) (hS.oneTop j hj)
          hc hc' h hend
      · exact tiles_ne_end F (hS.tile j hj) (hS.coords j hj) (hS.oneTop j hj)
          hc' hc h hend.symm
    · exact coreFor geo F hR hS hn words h hj (List.mem_of_getElem? hc') ho' hc ho hk.symm hend.symm hr

end main

section legacy
variable {cfg : Config} {rows : List (SepGeom × Nat)}

theorem core (F : Facts cfg rows) (hsL : 0 < cfg.seed cfg.levels) {N : Nat} {g : OnlineGeom}
    {run : OnlineRun} {S : Schedule} {n m : Nat}
    (hR : OnlineRunPremises cfg (hierarchyShapes cfg rows) N g run) (hS : SchedulePremises cfg S n m)
    (hn : n ≤ run.ops.length) (words : Words) {j j' i' : Nat} {c c' : Nat × Nat} {o o' : Op}
    (hjj : j < j') (hj' : j' < n) (hc : c ∈ (S j).tables) (ho : run.ops[j]? = some o)
    (hc' : (S j').tables[i']? = some c') (ho' : run.ops[j']? = some o')
    (hk : o.record.key = o'.record.key) (hend : we cfg c = we cfg c')
    (hreal : isReal cfg (hierarchyShapes cfg rows) g run S words j' i' = true) : False := by
  exact coreFor (HierarchyGeometry.selected cfg rows) F.lowFacts hR hS hn words hjj hj' hc ho hc' ho' hk hend hreal

theorem freshAt (F : Facts cfg rows) (hsL : 0 < cfg.seed cfg.levels) : OnlineFreshAt cfg rows := by
  exact freshFor (HierarchyGeometry.selected cfg rows) F.lowFacts

end legacy

theorem hsL_with (cfg : Config) (H : Nat) (h : 0 < cfg.seed cfg.levels) :
    0 < ({ cfg with horizon := H } : Config).seed ({ cfg with horizon := H } : Config).levels := h

end RebuildBound.OnlineFreshProof

open RebuildBound.OnlineFreshProof RebuildBound.HierarchyInvariantProof in
/-- **OnlineFresh**: at both selected configurations and every chunk horizon,
every real probe reads a word of the family tape, and no two read the same. -/
theorem RebuildBound.OnlineFresh : RebuildBound.Spec.OnlineFresh_statement := by
  intro h _
  exact ⟨freshAt (facts_horizon HierarchyHorizonFree uniformFacts (h * 2 ^ 32))
      (hsL_with _ _ (by decide)),
    freshAt (facts_horizon HierarchyHorizonFree halfFanoutFacts (h * 2 ^ 32))
      (hsL_with _ _ (by decide))⟩
