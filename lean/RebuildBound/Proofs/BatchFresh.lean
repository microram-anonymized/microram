import RebuildBound.Proofs.BatchFresh.Requester
import RebuildBound.Proofs.OnlineFresh
import RebuildBound.Spec.ObliviousBatch

/-!
# BatchFresh: every real probe of a run with batch chunks reads a distinct word

The scalar argument of
`Proofs/OnlineFresh.lean`, over slots.

(a) Slot `t` probes the plan at `J = chunkStart t ≤ t < n`, so a real
entry's table is a published coordinate whose window ends at or before
`pos J < s_1 P + H`; its family is a coordinate of the horizon.

(b) Two entries of one plan have distinct window ends. Two lanes of one
operation with the same key: the later one is a duplicate, never real. For
slots of operations `j < j'` with the same family and key `k`, let `u` be the
last slot of key `k` before operation `j'` (`u ≥ t`). Its record is still in
the requester at the start of `j'` (`inv_stateAt`): in the dense prefix, or
in a consumed unit whose position `pos u ≥ pos t ≥ pos J ≥` the family's end
lies in some table of `t'`'s plan preceding `c'`, below the top, which holds
`k` (`flow`).
-/

namespace RebuildBound.BatchFreshProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.OnlineBatch RebuildBound.Spec
open RebuildBound.Model.Online (OnlineGeom Schedule pos window)
open RebuildBound.HierarchyInvariantProof
open RebuildBound.OnlineFreshProof (wb we tiles_bounds tiles_cover tiles_order window_snd
  window_fst_top window_fst_low cp_pos familyOf_end familyOf_mem Published flowFor mem_recs last_occ
  Placed)

theorem isReal_true {cfg : Config} {sh : Shapes} {g : OnlineGeom} {run : BatchRun} {S : Schedule}
    {words : Words} {t i : Nat} (h : isReal cfg sh g run S words t i = true) :
    ∃ s, (slots run)[t]? = some s ∧ duplicate run s = false ∧
      s.record.key ∉ denseKeys cfg g run S t ∧
      ∀ c ∈ (slotSchedule (widths run) S t).tables.take i,
        s.record.key ∉ tableKeys cfg sh g run words c.1 c.2 := by
  unfold isReal at h
  cases hs : (slots run)[t]? with
  | none => rw [hs] at h; simp at h
  | some s =>
    rw [hs] at h
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_true,
      List.elem_eq_mem, decide_eq_false_iff_not] at h
    exact ⟨s, rfl, h.1.1.2, h.1.2, h.2⟩

theorem denseKeys_eq {cfg : Config} {g : OnlineGeom} {run : BatchRun} {S : Schedule} {t : Nat}
    {s : OnlineBatch.Slot} (hs : (slots run)[t]? = some s) :
    denseKeys cfg g run S t =
      (((stateAt g run s.op).frozen.drop (((slotSchedule (widths run) S t).consumed - cfg.seed 1) *
        g.unitsPerPrefix)).flatMap Bucket.recs ++ (stateAt g run s.op).current.recs).map Rec.key := by
  unfold denseKeys denseRecords
  rw [hs]

section main
variable {geo : HierarchyGeometry}

/-- The positions argument: a slot of a later operation with the same key does
not get a real probe in a member of the family. -/
theorem coreFor (F : LowFacts geo.cfg geo.rows geo.direct) {N : Nat} {g : OnlineGeom}
    {run : BatchRun} {S : Schedule} {n m : Nat}
    (hR : BatchRunPremises geo.cfg geo.shapes N g run) (hS : SchedulePremises geo.cfg S n m)
    (words : Words) {t t' i' : Nat} {c c' : Nat × Nat} {s s' : OnlineBatch.Slot}
    (hs : (slots run)[t]? = some s) (hs' : (slots run)[t']? = some s') (hop : s.op < s'.op)
    (ht' : t' < n) (hc : c ∈ (S (chunkStart (widths run) t)).tables)
    (hc' : (S (chunkStart (widths run) t')).tables[i']? = some c')
    (hk : s.record.key = s'.record.key) (hend : we geo.cfg c = we geo.cfg c')
    (hreal : isReal geo.cfg geo.shapes g run S words t' i' = true) : False := by
  obtain ⟨s'', hs'', -, hdense, htab⟩ := isReal_true hreal
  rw [hs'] at hs''
  cases hs''
  rw [denseKeys_eq hs'] at hdense
  have hJ := chunkStart_le (widths run) t
  have hJ' := chunkStart_slot run hs'
  generalize chunkStart (widths run) t = J at hc hJ
  unfold slotSchedule at hdense htab
  rw [hJ'] at hc' hdense htab
  have htj : t < fs run s'.op := lt_fs run hs hop
  have hj'n : fs run s'.op < n := lt_of_le_of_lt (fs_le run hs') ht'
  have hJn : J < n := by omega
  generalize hj' : s'.op = j' at hc' hdense htab htj hj'n
  have hj'len : j' ≤ run.ops.length := by
    obtain ⟨o, ho, -⟩ := slot_inv run hs'
    rw [hj'] at ho
    exact Nat.le_of_lt (List.getElem?_eq_some_iff.1 ho).1
  -- the last slot of the key before operation `j'`
  obtain ⟨u, htu, huj', hPu, hlast⟩ :=
    last_occ (fun u => slotKey run u = some s'.record.key) htj (by rw [slotKey_of hs, hk])
  obtain ⟨su, hsu, hsuk⟩ : ∃ su, (slots run)[u]? = some su ∧ su.record.key = s'.record.key := by
    simp only [slotKey, Option.map_eq_some_iff] at hPu
    exact hPu
  have hinv := inv_stateAt g run hR.geom.2 j' hj'len
  have hpl := hinv.placed u su huj' hsu (fun v h1 h2 => by rw [hsuk]; exact hlast v h1 h2)
  -- the dense prefix at `j'`
  have hdk : ∀ B ∈ (stateAt g run j').frozen.drop
      (((S (fs run j')).consumed - geo.cfg.seed 1) * g.unitsPerPrefix), some su.record ∈ B → False := by
    intro B hB hm
    apply hdense
    exact List.mem_map.2 ⟨su.record,
      List.mem_append_left _ (List.mem_flatMap.2 ⟨B, hB, mem_recs hm⟩), hsuk⟩
  rcases hpl with ⟨u0, hu, hu1, hu2, hmem⟩ | ⟨-, hmem⟩
  swap
  · apply hdense
    exact List.mem_map.2 ⟨su.record, List.mem_append_right _ (mem_recs hmem), hsuk⟩
  by_cases hD : ((S (fs run j')).consumed - geo.cfg.seed 1) * g.unitsPerPrefix ≤ u0
  · refine hdk _ (List.mem_of_getElem?
      (i := u0 - ((S (fs run j')).consumed - geo.cfg.seed 1) * g.unitsPerPrefix) ?_) hmem
    rw [List.getElem?_drop, Nat.add_sub_cancel' hD, List.getElem?_eq_getElem hu]
  -- the record lies in a consumed prefix
  rw [Nat.not_le] at hD
  have hgeom := hR.geom.1
  generalize hE : g.unitEntries = E at hgeom hu1 hu2 hD
  generalize hr0 : g.unitsPerPrefix = r0 at hgeom hD hdk
  generalize hP : geo.cfg.carryPositions 1 = P at hgeom
  have hcj := hS.consumed J hJn
  have hcj' := hS.consumed (fs run j') hj'n
  have hPpos : 0 < P := by rw [← hP]; exact cp_pos F le_rfl (by have := F.levels2; omega)
  have hr0pos : 0 < r0 := by
    rcases Nat.eq_zero_or_pos r0 with h | h
    · rw [h, Nat.mul_zero] at hgeom; omega
    · exact h
  rw [hP] at hcj hcj'
  simp only [pos] at hcj hcj'
  rw [hP] at hcj hcj'
  -- the position of the record
  have hq1 : geo.cfg.seed 1 * P + u < (S (fs run j')).consumed * P := by
    have h1 : (u0 + 1) * E ≤ ((S (fs run j')).consumed - geo.cfg.seed 1) * r0 * E :=
      Nat.mul_le_mul_right _ hD
    have h2 : ((S (fs run j')).consumed - geo.cfg.seed 1) * r0 * E =
        ((S (fs run j')).consumed - geo.cfg.seed 1) * P := by
      rw [← hgeom]; ring
    have h3 : geo.cfg.seed 1 * P + ((S (fs run j')).consumed - geo.cfg.seed 1) * P =
        (S (fs run j')).consumed * P := by
      rw [← Nat.add_mul, Nat.add_sub_cancel' hcj'.1]
    omega
  have hcend : we geo.cfg c ≤ (S J).consumed * P := by
    have := (tiles_bounds (hS.tile J hJn) c hc).2.2
    rw [hP] at this; exact this
  obtain ⟨is, cs, hcs, hcs1, hcs2⟩ := tiles_cover (hS.tile (fs run j') hj'n) (Nat.zero_le _)
    (by rw [hP]; exact hq1)
  have hb' := (tiles_bounds (hS.tile (fs run j') hj'n) c' (List.mem_of_getElem? hc')).2.1
  -- the covering table precedes `c'`
  have hlt : is < i' := by
    rcases lt_trichotomy is i' with h | h | h
    · exact h
    · subst h
      rw [hc'] at hcs; cases hcs
      omega
    · have := tiles_order (hS.tile (fs run j') hj'n) hc' hcs h
      omega
  have hpub : Published geo.cfg cs := hS.coords (fs run j') hj'n cs (List.mem_of_getElem? hcs)
  -- and is below the top
  have hlow : cs.1 < geo.cfg.levels :=
    OnlineFreshProof.tiles_before_low F (hS.tile (fs run j') hj'n) (hS.coords (fs run j') hj'n)
      (hS.oneTop (fs run j') hj'n) hcs hc' hlt
  have hsv : geo.cfg.seed cs.1 < cs.2 := hpub.2.2.1 hlow
  -- the record's level-one ordinal
  obtain ⟨tl, htl⟩ := frozen_prefix g run (j := j') run.ops.length hj'len le_rfl
  have hT := hR.trace
  have hq : ∀ w, geo.cfg.seed 1 < w → (w - 1) * geo.cfg.carryPositions 1 ≤ geo.cfg.seed 1 * P + u →
      geo.cfg.seed 1 * P + u < w * geo.cfg.carryPositions 1 →
      s'.record.key ∈ (DirectMasks.records ((traceOf g run).units (w - geo.cfg.seed 1 - 1))).map
        Rec.key := by
    intro w _ hw1 hw2
    rw [hP] at hw1 hw2
    have hi1 : u0 / r0 * r0 ≤ u0 := Nat.div_mul_le_self u0 r0
    have hi2 : u0 < u0 / r0 * r0 + r0 := Nat.lt_div_mul_add hr0pos
    generalize u0 / r0 = i0 at hi1 hi2
    have ht1 : (geo.cfg.seed 1 + i0) * P ≤ geo.cfg.seed 1 * P + u := by
      have := Nat.mul_le_mul_right E hi1
      rw [Nat.add_mul, ← hgeom]
      have e : i0 * (E * r0) = i0 * r0 * E := by ring
      omega
    have ht2 : geo.cfg.seed 1 * P + u < (geo.cfg.seed 1 + i0 + 1) * P := by
      have := Nat.mul_le_mul_right E (show u0 + 1 ≤ i0 * r0 + r0 by omega)
      rw [Nat.add_mul, Nat.add_mul, ← hgeom]
      have e : (i0 * r0 + r0) * E = i0 * (E * r0) + 1 * (E * r0) := by ring
      omega
    have hw3 : geo.cfg.seed 1 + i0 < w := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt ht1 hw2)
    have hw4 : w - 1 < geo.cfg.seed 1 + i0 + 1 := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt hw1 ht2)
    have hwi : w - geo.cfg.seed 1 - 1 = i0 := by omega
    rw [hwi]
    refine List.mem_map.2 ⟨su.record, List.mem_flatMap.2 ⟨(stateAt g run j').frozen[u0], ?_,
      mem_recs hmem⟩, hsuk⟩
    simp only [traceOf]
    rw [hr0]
    refine List.mem_of_getElem? (i := u0 - i0 * r0) ?_
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

/-- `BatchFresh` from the invariant's lower facts, for either start. -/
theorem freshFor (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct) : BatchFreshFor geo := by
  intro N g run S n m hset words
  obtain ⟨-, hn, hR, hS⟩ := hset
  have hlevels := F.levels2
  have hcp1 := cp_pos F (ℓ := 1) le_rfl (by omega)
  -- a table's family shares its window end
  have hfend : ∀ J < n, ∀ c ∈ (S J).tables,
      (familyOf geo.cfg c.1 c.2).2 * geo.cfg.carryPositions (familyOf geo.cfg c.1 c.2).1 = we geo.cfg c := by
    intro J hJ c hc
    have hpub : Published geo.cfg c := hS.coords J hJ c hc
    rw [familyOf_end F hpub.1 hpub.2.1 hpub.seed_le, we, window_snd]
  refine ⟨?_, ?_⟩
  · intro t i ht hi hreal
    obtain ⟨s, hs, -⟩ := isReal_true hreal
    have hJ := chunkStart_le (widths run) t
    unfold slotSchedule at hi ⊢
    generalize chunkStart (widths run) t = J at hi hJ ⊢
    have hJn : J < n := by omega
    have hc : (S J).tables[i]'hi ∈ (S J).tables := List.getElem_mem hi
    refine ⟨_, s, List.getElem?_eq_getElem hi, hs, ?_, hR.keys s (List.mem_of_getElem? hs)⟩
    have hpub : Published geo.cfg ((S J).tables[i]'hi) := hS.coords J hJn _ hc
    apply familyOf_mem F hpub.1 hpub.2.1 hpub.seed_le
    have h1 := (tiles_bounds (hS.tile J hJn) _ hc).2.2
    have h2 := (hS.consumed J hJn).2
    have h3 := hR.horizon
    simp only [we, window_snd, pos] at h1 h2
    omega
  · intro t i t' i' c c' s s' ht hi ht' hi' hne hr hr' hc hc' hs hs' heq
    obtain ⟨hf, hk⟩ := Prod.mk.inj heq
    unfold slotSchedule at hc hc'
    have hcm := List.mem_of_getElem? hc
    have hcm' := List.mem_of_getElem? hc'
    have hJn : chunkStart (widths run) t < n := lt_of_le_of_lt (chunkStart_le _ _) ht
    have hJn' : chunkStart (widths run) t' < n := lt_of_le_of_lt (chunkStart_le _ _) ht'
    have hend : we geo.cfg c = we geo.cfg c' := by
      rw [← hfend _ hJn c hcm, ← hfend _ hJn' c' hcm', hf]
    rcases lt_trichotomy t t' with h | h | h
    · rcases (op_mono run hs hs' h).lt_or_eq with hop | hop
      · exact coreFor F hR hS words hs hs' hop ht' hcm hc' hk hend hr'
      · obtain ⟨s'', hs'', hd, -⟩ := isReal_true hr'
        rw [hs'] at hs''; cases hs''
        rw [duplicate_of run hs hs' hop h hk] at hd
        exact Bool.noConfusion hd
    · subst h
      rw [hs] at hs'; cases hs'
      have hii : i ≠ i' := fun e => hne (by rw [e])
      rcases Nat.lt_or_gt_of_ne hii with h | h
      · exact OnlineFreshProof.tiles_ne_end F (hS.tile _ hJn) (hS.coords _ hJn) (hS.oneTop _ hJn)
          hc hc' h hend
      · exact OnlineFreshProof.tiles_ne_end F (hS.tile _ hJn) (hS.coords _ hJn) (hS.oneTop _ hJn)
          hc' hc h hend.symm
    · rcases (op_mono run hs' hs h).lt_or_eq with hop | hop
      · exact coreFor F hR hS words hs' hs hop ht hcm' hc hk.symm hend.symm hr
      · obtain ⟨s'', hs'', hd, -⟩ := isReal_true hr
        rw [hs] at hs''; cases hs''
        rw [duplicate_of run hs' hs hop h hk.symm] at hd
        exact Bool.noConfusion hd

end main

/-- Original selected-geometry interface. -/
theorem freshAt {cfg : Config} {rows : List (SepGeom × Nat)} (F : Facts cfg rows)
    (hsL : 0 < cfg.seed cfg.levels) : BatchFreshAt cfg rows :=
  freshFor (HierarchyGeometry.selected cfg rows) F.lowFacts

end RebuildBound.BatchFreshProof

open RebuildBound.BatchFreshProof RebuildBound.HierarchyInvariantProof RebuildBound.OnlineFreshProof in
/-- **BatchFresh**: at both selected configurations and every chunk horizon,
every real probe of a run with batch chunks reads a word of the family tape,
and no two read the same. -/
theorem RebuildBound.BatchFresh : RebuildBound.Spec.BatchFresh_statement := by
  intro h _
  exact ⟨freshAt (facts_horizon HierarchyHorizonFree uniformFacts (h * 2 ^ 32))
      (hsL_with _ _ (by decide)),
    freshAt (facts_horizon HierarchyHorizonFree halfFanoutFacts (h * 2 ^ 32))
      (hsL_with _ _ (by decide))⟩
