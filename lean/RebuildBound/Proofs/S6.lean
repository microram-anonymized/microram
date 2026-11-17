import RebuildBound.Proofs.S6.Drain
import RebuildBound.Proofs.ListAux.Bucket

/-!
# S6: schedule independence at a general digit (ST6)

Every valid schedule of A's binary pair operations gives the stage-by-stage
schedule's main buckets and radix stash, its stage stashes up to order, and
the same verdict of the whole job.

* `S6/Route.lean`: by the shared exchange argument (`Exchange`), pair operations on disjoint
  bucket pairs commute up to stage stash order, so a valid schedule's binary
  route is `SREq` to the stage-by-stage one (`binRoute_SREq`). The route trace
  records running stash lengths, and every stage stash test has the same
  capacity, so it fails iff some touched stash's final length exceeds it
  (`binRoute_fails_iff`).
* `S6/Radix.lean`: the radix pass reads only main and the radix stash
  (`radixPass_congr`), so it gives equal results and equal trace entries. The
  binary route conserves A's records and the radix stash is a sub-multiset of
  the routed records, so the pool is key-distinct (`route_sheds_subperm`).
* The pool is a permutation of the stage-by-stage pool, so the DFS trace is
  equal and the leaves agree leaf by leaf up to order.
* `S6/Offer.lean`, `S6/Finish.lean`: B's insertion reads only routed buckets,
  so the insertion stash and trace coincide; the offers keep leaf lengths,
  B-tier leftovers and the leftovers whose key is in the insertion stash
  (their home was full, by `SInputShape.bHome` and `homeOf = carry + U way`).
* `S6/Drain.lean`: the drain trace depends only on those.

Probability: none (a deterministic package).
-/

namespace RebuildBound.S6

open RebuildBound.Model RebuildBound.D6

theorem sMatch_toBool (o : Option STest) (out : Output) :
    (match o with
      | some t => (Except.error t : Except STest Output)
      | none => Except.ok out).toBool = o.isNone := by
  cases o <;> rfl

theorem sJobWith_toBool (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → Nat) (inp : SInputs)
    (ops : List (Nat × Nat)) :
    (sJobWith rule g w inp ops).toBool = true ↔
      ¬ SFails g (sReferenceWith rule g w inp ops).trace := by
  have e : (sJobWith rule g w inp ops).toBool =
      (sFirstFailure g (sReferenceWith rule g w inp ops).trace).isNone :=
    sMatch_toBool _ _
  rw [e]
  cases h : sFirstFailure g (sReferenceWith rule g w inp ops).trace with
  | none =>
    simp only [Option.isNone_none, true_iff]
    unfold sFirstFailure at h
    rw [Option.map_eq_none_iff, List.find?_eq_none] at h
    rintro ⟨x, hx, hf⟩
    exact h x hx (by simpa using hf)
  | some t =>
    simp only [Option.isNone_some, Bool.false_eq_true, false_iff, not_not]
    unfold sFirstFailure at h
    obtain ⟨x, hx, -⟩ := Option.map_eq_some_iff.mp h
    have h2 := List.find?_some hx
    exact ⟨x, List.mem_of_find?_eq_some hx, by simpa using h2⟩

theorem sDfsTrace_perm (g : SepGeom) (w : Model.LogicalKey → Nat) {p1 p2 : List Rec} (h : p1.Perm p2) :
    sDfsTrace g w p1 = sDfsTrace g w p2 := by
  unfold sDfsTrace
  apply List.flatMap_congr
  intro d _
  apply List.map_congr_left
  intro c _
  rw [(h.filter _).length_eq]

theorem sLeaves_getD (g : SepGeom) (w : Model.LogicalKey → Nat) (pool : List Rec) (R : Nat) :
    (sLeaves g w pool).getD R [] =
      if R < g.ranges then pool.filter (fun x => sRange g w x == R) else [] := by
  unfold sLeaves
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  split_ifs with h
  · rw [List.getElem?_range h]; rfl
  · rw [List.getElem?_eq_none (by simpa using h)]; rfl

theorem sPool_perm {r1 r2 : SRoute} (hl : r1.stash.length = r2.stash.length)
    (hp : ∀ j, (r1.stash.getD j []).Perm (r2.stash.getD j [])) (hr : r1.radix = r2.radix)
    (aT : List Rec) (bT : List (List Rec)) : (sPool r1 aT bT).Perm (sPool r2 aT bT) := by
  unfold sPool
  refine List.Perm.filter _ (List.Perm.append_right _ ?_)
  rw [hr]
  exact List.Perm.append_right _ (flatten_perm_of_forall₂ (forall₂_of_getD List.Perm [] [] _ _ hl hp))

theorem sPool_avoids (st : SRoute) (aT : List Rec) (bT : List (List Rec)) :
    ∀ r ∈ sPool st aT bT, (bT.flatten.map Rec.key).contains r.key = false := by
  intro r hr
  unfold sPool at hr
  simpa using (List.mem_filter.mp hr).2

theorem sLeaves_ok (g : SepGeom) (w : Model.LogicalKey → Nat) (pool : List Rec) (TK : List Model.LogicalKey)
    (hn : (pool.map Rec.key).Nodup) (hb : ∀ r ∈ pool, TK.contains r.key = false) :
    LeafOK TK (sLeaves g w pool) := by
  intro R
  rw [sLeaves_getD]
  split_ifs
  · exact ⟨hn.sublist (List.filter_sublist.map _), fun r hr => hb r (List.mem_of_mem_filter hr)⟩
  · simp

/-- The stage-by-stage pool is key-distinct. -/
theorem sPool_nodup {rule : CapRule} (hv : rule.Valid) (g : SepGeom) (hd : 1 ≤ g.d)
    (wOld w : Model.LogicalKey → Nat) (inp : SInputs) (hinp : SInputShape g wOld w inp) :
    ((sPool (sRouteWith rule g w inp.aMain g.canonicalOps) inp.aTier inp.bTier).map
      Rec.key).Nodup := by
  have h1 := route_sheds_subperm hv g hd w inp.aMain hinp.aLen hinp.aLanes
  have h2 : ((sRouteWith rule g w inp.aMain g.canonicalOps).stash.flatten ++
      (sRouteWith rule g w inp.aMain g.canonicalOps).radix ++ inp.aTier).Subperm inp.aAll := by
    obtain ⟨l, hp, hs⟩ := h1
    exact ⟨l ++ inp.aTier, hp.append_right _, hs.append_right _⟩
  have h3 := D4b.nodup_of_subperm (D4b.subperm_map Rec.key h2) hinp.aNodup
  unfold sPool
  exact h3.sublist (List.filter_sublist.map _)

theorem bTier_getD_mem (bT : List (List Rec)) (pg : Nat) (r : Rec) (h : r ∈ bT.getD pg []) :
    r ∈ bT.flatten := by
  rw [List.getD_eq_getElem?_getD] at h
  by_cases hp : pg < bT.length
  · rw [List.getElem?_eq_getElem hp] at h
    simp only [Option.getD_some] at h
    exact List.mem_flatten.mpr ⟨_, List.getElem_mem hp, h⟩
  · rw [List.getElem?_eq_none (by omega)] at h
    simp at h

end RebuildBound.S6

open RebuildBound.Model RebuildBound.D6 RebuildBound.S6 in
/-- **ST6, schedule independence.** -/
theorem RebuildBound.ST6 : RebuildBound.Spec.ST6_statement := by
  intro rule g wOld w inp ops hv hg hinp hsched
  have hd : 1 ≤ g.d := by have := hg.2.1; omega
  set b1 := runSOps rule g w ops (sRouteInit g inp.aMain) with hb1
  set b2 := runSOps rule g w g.canonicalOps (sRouteInit g inp.aMain) with hb2
  have hb := binRoute_SREq rule g w ops hsched (sRouteInit g inp.aMain)
  rw [← hb1, ← hb2] at hb
  have e1 : sRouteWith rule g w inp.aMain ops = radixPass g w b1 := rfl
  have e2 : sRouteWith rule g w inp.aMain g.canonicalOps = radixPass g w b2 := rfl
  have hrc := radixPass_congr g w b1 b2 hb.main hb.radix
  rw [← e1, ← e2] at hrc
  obtain ⟨hmain, hradix, hst1, hst2, T, ht1, ht2⟩ := hrc
  set r1 := sRouteWith rule g w inp.aMain ops with hr1
  set r2 := sRouteWith rule g w inp.aMain g.canonicalOps with hr2
  have hlen : r1.stash.length = r2.stash.length := by rw [hst1, hst2, hb.len]
  have hperm : ∀ j, (r1.stash.getD j []).Perm (r2.stash.getD j []) := by
    intro j; rw [hst1, hst2]; exact hb.perm j
  refine ⟨hmain, hperm, hradix, ?_⟩
  -- the verdict
  have href1 : (sReferenceWith rule g w inp ops).trace =
      r1.trace ++ sDfsTrace g w (sPool r1 inp.aTier inp.bTier) ++
        (sFinish g w inp r1.main (sLeaves g w (sPool r1 inp.aTier inp.bTier))).trace ++
        (sDrain (sFinish g w inp r1.main (sLeaves g w (sPool r1 inp.aTier inp.bTier)))).2 := rfl
  have href2 : (sReferenceWith rule g w inp g.canonicalOps).trace =
      r2.trace ++ sDfsTrace g w (sPool r2 inp.aTier inp.bTier) ++
        (sFinish g w inp r2.main (sLeaves g w (sPool r2 inp.aTier inp.bTier))).trace ++
        (sDrain (sFinish g w inp r2.main (sLeaves g w (sPool r2 inp.aTier inp.bTier)))).2 := rfl
  have hpool := sPool_perm hlen hperm hradix inp.aTier inp.bTier
  have hn2 := sPool_nodup hv g hd wOld w inp hinp
  rw [← hr2] at hn2
  have hn1 : ((sPool r1 inp.aTier inp.bTier).map Rec.key).Nodup :=
    (hpool.map Rec.key).nodup_iff.mpr hn2
  -- the route verdict
  have hroute : SFails g r1.trace ↔ SFails g r2.trace := by
    rw [ht1, ht2, sFails_append, sFails_append,
      binRoute_fails_iff rule g w inp.aMain ops hsched]
  -- the finish phase
  set TK := inp.bTier.flatten.map Rec.key
  set routed := r2.main
  set i1 : SFin :=
    SFin.mk r1.main [] (sLeaves g w (sPool r1 inp.aTier inp.bTier)) inp.bTier []
  set i2 : SFin :=
    SFin.mk r2.main [] (sLeaves g w (sPool r2 inp.aTier inp.bTier)) inp.bTier []
  have h0 : FinInv g w inp routed TK 0 i1 i2 := by
    refine ⟨fun v _ => by show r1.main.getD v [] = r2.main.getD v []; rw [hmain],
      fun v _ => rfl, rfl, rfl, rfl, ?_, rfl, ?_, ?_,
      sLeaves_ok g w _ _ hn1 (sPool_avoids _ _ _), sLeaves_ok g w _ _ hn2 (sPool_avoids _ _ _)⟩
    · intro pg r hr
      rw [contains_iff]
      exact List.mem_map_of_mem (bTier_getD_mem _ pg r hr)
    · simp [i1, i2, sLeaves]
    · intro R
      show LeafRel _ ((sLeaves g w (sPool r1 inp.aTier inp.bTier)).getD R [])
        ((sLeaves g w (sPool r2 inp.aTier inp.bTier)).getD R [])
      rw [sLeaves_getD, sLeaves_getD]
      split_ifs
      · exact LeafRel.of_perm (hpool.filter _)
      · exact LeafRel.of_perm (List.Perm.refl _)
  have hU := FinInv.fold g w inp routed hd hinp.bHome h0 g.U le_rfl
  have hf1 : sFinish g w inp r1.main (sLeaves g w (sPool r1 inp.aTier inp.bTier)) =
      (List.range g.U).foldl (fun st i => sInsertBucket g w inp.bMain i st) i1 := rfl
  have hf2 : sFinish g w inp r2.main (sLeaves g w (sPool r2 inp.aTier inp.bTier)) =
      (List.range g.U).foldl (fun st i => sInsertBucket g w inp.bMain i st) i2 := rfl
  rw [← hf1, ← hf2] at hU
  have hdrain := sDrain_trace_eq _ _ hU.ins hU.bcopy hU.len (fun R => (hU.rel R).mono (fun r hr => by
    unfold S6.keepN
    rw [hU.ins1] at hr
    rw [show sKof g w inp routed = ((List.range g.U).flatMap (sInsOf g w inp routed)).map Rec.key
      from rfl, hr, Bool.or_true]))
  have hfails : SFails g (sReferenceWith rule g w inp ops).trace ↔
      SFails g (sReferenceWith rule g w inp g.canonicalOps).trace := by
    rw [href1, href2, sFails_append, sFails_append, sFails_append, sFails_append, sFails_append,
      sFails_append, hroute, sDfsTrace_perm g w hpool, hU.trace, hdrain]
  rw [Bool.eq_iff_iff, sJobWith_toBool, sJobWith_toBool, hfails]
