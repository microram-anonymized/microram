import RebuildBound.Proofs.D6.Route
import RebuildBound.Proofs.D6.Finish
import RebuildBound.Proofs.D6.Drain
import RebuildBound.Proofs.ListAux.Bucket

/-!
# D6: schedule independence (T6)

Every valid schedule of A's pair operations gives the same buckets, the same
stash contents up to order, and the same verdict of the whole job.

* `D6/Route.lean`: pair operations on disjoint bucket pairs commute up to
  stash order; the shared exchange argument (`Exchange`) turns a valid schedule into the canonical
  one (`route_REq`). The route trace records running stash lengths, so it
  fails iff some touched stash's final length fails (`route_fails_iff`). The
  route conserves A's records, so the pool is key-distinct.
* The pool is a permutation of the canonical pool, so the DFS trace is equal
  and the leaves agree leaf by leaf up to order.
* `D6/Offer.lean`, `D6/Finish.lean`: B's insertion reads only routed buckets,
  so the insertion stash and trace coincide; the offers keep leaf lengths,
  B-tier leftovers and the leftovers whose key is in the insertion stash
  (their home was full, by `InputValid.bHome`).
* `D6/Drain.lean`: the drain trace depends only on those.

Probability: none (a deterministic package).
-/

namespace RebuildBound.D6

open RebuildBound.Model

theorem match_toBool (o : Option Test) (out : Output) :
    (match o with
      | some t => (Except.error t : Except Test Output)
      | none => Except.ok out).toBool = o.isNone := by
  cases o <;> rfl

theorem jobWith_toBool (rule : CapRule) (g : Geom) (caps : Caps) (w : Model.LogicalKey → Nat) (inp : Inputs)
    (ops : List (Nat × Nat)) :
    (jobWith rule g caps w inp ops).toBool = true ↔
      ¬ Fails g caps (referenceWith rule g w inp ops).trace := by
  have e : (jobWith rule g caps w inp ops).toBool =
      (firstFailure g caps (referenceWith rule g w inp ops).trace).isNone :=
    match_toBool _ _
  rw [e]
  cases h : firstFailure g caps (referenceWith rule g w inp ops).trace with
  | none =>
    simp only [Option.isNone_none, true_iff]
    unfold firstFailure at h
    rw [Option.map_eq_none_iff, List.find?_eq_none] at h
    rintro ⟨x, hx, hf⟩
    exact h x hx hf
  | some t =>
    simp only [Option.isNone_some, Bool.false_eq_true, false_iff, not_not]
    unfold firstFailure at h
    obtain ⟨x, hx, -⟩ := Option.map_eq_some_iff.mp h
    have h2 := List.find?_some hx
    exact ⟨x, List.mem_of_find?_eq_some hx, h2⟩

theorem dfsTrace_perm (g : Geom) (w : Model.LogicalKey → Nat) {p1 p2 : List Rec} (h : p1.Perm p2) :
    dfsTrace g w p1 = dfsTrace g w p2 := by
  unfold dfsTrace
  apply List.flatMap_congr
  intro d _
  apply List.map_congr_left
  intro c _
  rw [(h.filter _).length_eq]

theorem leavesOf_getD (g : Geom) (w : Model.LogicalKey → Nat) (pool : List Rec) (R : Nat) :
    (leavesOf g w pool).getD R [] =
      if R < g.ranges then pool.filter (fun r => rangeOf g w r == R) else [] := by
  unfold leavesOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  split_ifs with h
  · rw [List.getElem?_range h]; rfl
  · rw [List.getElem?_eq_none (by simpa using h)]; rfl

theorem pool_perm {r1 r2 : RouteState} (h : REq r1 r2) (aT bT : List Rec) :
    (poolA r1 aT bT).Perm (poolA r2 aT bT) := by
  unfold poolA
  refine List.Perm.filter _ (List.Perm.append_right _ ?_)
  exact flatten_perm_of_forall₂ (forall₂_of_getD List.Perm [] [] _ _ h.len h.perm)

/-- The canonical pool is key-distinct. -/
theorem pool_nodup {rule : CapRule} (hv : rule.Valid) (g : Geom) (TA TB : Nat)
    (wOld w : Model.LogicalKey → Nat) (inp : Inputs) (hinp : InputValid g TA TB wOld w inp) :
    ((poolA (routeA rule g w inp.aMain) inp.aTier inp.bTier).map Rec.key).Nodup := by
  have hri := routeA_recInv hv g w inp.aMain hinp.aLen hinp.aLanes
  have h1 : (routeA rule g w inp.aMain).stash.flatten.Subperm (inp.aMain.flatMap Bucket.recs) :=
    (List.sublist_append_right _ _).subperm.trans hri.2.subperm
  have h2 : ((routeA rule g w inp.aMain).stash.flatten ++ inp.aTier).Subperm inp.aAll := by
    obtain ⟨l, hp, hs⟩ := h1
    exact ⟨l ++ inp.aTier, hp.append_right _, hs.append_right _⟩
  have h3 := D4b.nodup_of_subperm (D4b.subperm_map Rec.key h2) hinp.aNodup
  unfold poolA
  exact h3.sublist (List.filter_sublist.map _)

theorem leavesOf_ok (g : Geom) (w : Model.LogicalKey → Nat) (pool bT : List Rec)
    (hn : (pool.map Rec.key).Nodup)
    (hb : ∀ r ∈ pool, (bT.map Rec.key).contains r.key = false) :
    LeafOK (bT.map Rec.key) (leavesOf g w pool) := by
  intro R
  rw [leavesOf_getD]
  split_ifs
  · exact ⟨hn.sublist (List.filter_sublist.map _), fun r hr => hb r (List.mem_of_mem_filter hr)⟩
  · simp

theorem poolA_avoids (st : RouteState) (aT bT : List Rec) :
    ∀ r ∈ poolA st aT bT, (bT.map Rec.key).contains r.key = false := by
  intro r hr
  unfold poolA at hr
  simpa using (List.mem_filter.mp hr).2

theorem finish_foldl_inv (g : Geom) (w : Model.LogicalKey → Nat) (inp : Inputs) (routed : List Bucket)
    (TK : List Model.LogicalKey) (hbHome : ∀ i < g.U, ∀ r ∈ (inp.bMain.getD i []).recs, w r.key % g.U = i)
    (i1 i2 : FinState) (h0 : FinInv g w inp routed TK 0 i1 i2) :
    ∀ n, n ≤ g.U → FinInv g w inp routed TK n
      ((List.range n).foldl (fun st i => insertBucket g w inp.bMain i st) i1)
      ((List.range n).foldl (fun st i => insertBucket g w inp.bMain i st) i2)
  | 0, _ => h0
  | n + 1, hn => by
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    exact (finish_foldl_inv g w inp routed TK hbHome i1 i2 h0 n (by omega)).step g w inp routed
      hbHome (by omega)

end RebuildBound.D6

open RebuildBound.Model RebuildBound.D6 in
/-- **T6, schedule independence.** -/
theorem RebuildBound.T6 : RebuildBound.Spec.T6_statement := by
  intro rule g caps TA TB wOld w inp ops hv hinp hsched
  have hr := route_REq rule g w inp.aMain ops hsched
  refine ⟨hr.main, hr.perm, ?_⟩
  -- the verdict
  set r1 := routeWith rule g w inp.aMain ops with hr1
  set r2 := routeA rule g w inp.aMain with hr2
  have hjob : job rule g caps w inp = jobWith rule g caps w inp (canonicalOps g) := rfl
  have href1 : (referenceWith rule g w inp ops).trace =
      r1.trace ++ dfsTrace g w (poolA r1 inp.aTier inp.bTier) ++
        (finish g w inp r1.main (leavesOf g w (poolA r1 inp.aTier inp.bTier))).trace ++
        (drain (finish g w inp r1.main (leavesOf g w (poolA r1 inp.aTier inp.bTier)))).2 := rfl
  have href2 : (referenceWith rule g w inp (canonicalOps g)).trace =
      r2.trace ++ dfsTrace g w (poolA r2 inp.aTier inp.bTier) ++
        (finish g w inp r2.main (leavesOf g w (poolA r2 inp.aTier inp.bTier))).trace ++
        (drain (finish g w inp r2.main (leavesOf g w (poolA r2 inp.aTier inp.bTier)))).2 := rfl
  have hpool := pool_perm hr inp.aTier inp.bTier
  have hn2 := pool_nodup hv g TA TB wOld w inp hinp
  have hn1 : ((poolA r1 inp.aTier inp.bTier).map Rec.key).Nodup :=
    (hpool.map Rec.key).nodup_iff.mpr hn2
  -- the finish phase
  set TK := inp.bTier.map Rec.key
  set routed := r2.main
  set i1 : FinState :=
    FinState.mk r1.main [] (leavesOf g w (poolA r1 inp.aTier inp.bTier)) inp.bTier []
  set i2 : FinState :=
    FinState.mk r2.main [] (leavesOf g w (poolA r2 inp.aTier inp.bTier)) inp.bTier []
  have h0 : FinInv g w inp routed TK 0 i1 i2 := by
    refine ⟨fun v _ => by show r1.main.getD v [] = r2.main.getD v []; rw [hr.main], fun v _ => rfl, rfl, rfl, rfl, ?_, rfl, ?_, ?_,
      leavesOf_ok g w _ _ hn1 (poolA_avoids _ _ _), leavesOf_ok g w _ _ hn2 (poolA_avoids _ _ _)⟩
    · intro r hr
      rw [contains_iff]
      exact List.mem_map_of_mem hr
    · simp [i1, i2, leavesOf]
    · intro R
      show LeafRel _ ((leavesOf g w (poolA r1 inp.aTier inp.bTier)).getD R [])
        ((leavesOf g w (poolA r2 inp.aTier inp.bTier)).getD R [])
      rw [leavesOf_getD, leavesOf_getD]
      split_ifs
      · exact LeafRel.of_perm (hpool.filter _)
      · exact LeafRel.of_perm (List.Perm.refl _)
  have hU := finish_foldl_inv g w inp routed TK hinp.bHome i1 i2 h0 g.U le_rfl
  have hf1 : finish g w inp r1.main (leavesOf g w (poolA r1 inp.aTier inp.bTier)) =
      (List.range g.U).foldl (fun st i => insertBucket g w inp.bMain i st) i1 := rfl
  have hf2 : finish g w inp r2.main (leavesOf g w (poolA r2 inp.aTier inp.bTier)) =
      (List.range g.U).foldl (fun st i => insertBucket g w inp.bMain i st) i2 := rfl
  rw [← hf1, ← hf2] at hU
  have hdrain := drain_trace_eq _ _ hU.ins hU.bcopy hU.len (fun R => (hU.rel R).congr (fun r => by
    unfold keepN
    have : ¬ g.U ≤ home g w r % g.U := Nat.not_le.mpr (Nat.mod_lt _ (U_pos g))
    rw [decide_eq_false this, Bool.false_or, hU.ins1]
    rfl))
  have hfails : Fails g caps (referenceWith rule g w inp ops).trace ↔
      Fails g caps (referenceWith rule g w inp (canonicalOps g)).trace := by
    rw [href1, href2, fails_append, fails_append, fails_append, fails_append, fails_append,
      fails_append, route_fails_iff rule g caps w inp.aMain ops hsched, dfsTrace_perm g w hpool,
      hU.trace, hdrain]
  rw [hjob, Bool.eq_iff_iff, jobWith_toBool, jobWith_toBool, hfails]
