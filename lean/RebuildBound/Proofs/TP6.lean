import RebuildBound.Proofs.TP6.Finish
import RebuildBound.Spec.TopPrepT

/-!
# TP6: schedule independence of the top preparation's route

Every valid schedule gives the stage-by-stage buckets, the same stashes up to
order, and the same verdict of the job.

* `TP6/Route.lean`: by the shared exchange argument (`Exchange`), pair operations
  on disjoint bucket pairs commute up to stage stash order, so a valid
  schedule's route is `TPREq` to the stage-by-stage one. The route trace
  records running stash lengths and every stash test has the same capacity, so
  it fails iff some touched stash's final length exceeds it.
* The pool is a permutation of the stage-by-stage pool, so the DFS trace is
  equal and the leaves are permutations of each other.
* `TP6/Finish.lean`: the last level reads the routed buckets for its splits
  (equal), so its stash and trace coincide; the offers keep, for each leaf, its
  length and its count of records of each home (`LeafRel`); the drain's trace
  depends only on those lengths and the last stash.

Probability: none (a deterministic package).
-/

namespace RebuildBound.TP6Aux

open RebuildBound.Model RebuildBound.D6

theorem tpMatch_toBool (o : Option TPTest) (out : Output) :
    (match o with
      | some t => (Except.error t : Except TPTest Output)
      | none => Except.ok out).toBool = o.isNone := by
  cases o <;> rfl

theorem tpJobWith_toBool (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (w : Model.LogicalKey → Nat)
    (inp : TPInputs) (ops : List (Nat × Nat)) :
    (tpJobWith rule g unsh w inp ops).toBool = true ↔
      ¬ TPFails g (tpReferenceWith rule g unsh w inp ops).trace := by
  have e : (tpJobWith rule g unsh w inp ops).toBool =
      (tpFirstFailure g (tpReferenceWith rule g unsh w inp ops).trace).isNone :=
    tpMatch_toBool _ _
  rw [e]
  cases h : tpFirstFailure g (tpReferenceWith rule g unsh w inp ops).trace with
  | none =>
    simp only [Option.isNone_none, true_iff]
    unfold tpFirstFailure at h
    rw [Option.map_eq_none_iff, List.find?_eq_none] at h
    rintro ⟨x, hx, hf⟩
    exact h x hx (by simpa using hf)
  | some t =>
    simp only [Option.isNone_some, Bool.false_eq_true, false_iff, not_not]
    unfold tpFirstFailure at h
    obtain ⟨x, hx, -⟩ := Option.map_eq_some_iff.mp h
    have h2 := List.find?_some hx
    exact ⟨x, List.mem_of_find?_eq_some hx, by simpa using h2⟩

theorem tpDfsTrace_perm (g : TPGeom) (w : Model.LogicalKey → Nat) {p1 p2 : List Rec} (h : p1.Perm p2) :
    tpDfsTrace g w p1 = tpDfsTrace g w p2 := by
  unfold tpDfsTrace
  apply List.flatMap_congr
  intro d _
  apply List.map_congr_left
  intro c _
  rw [(h.filter _).length_eq]

theorem tpLeaves_getD (g : TPGeom) (w : Model.LogicalKey → Nat) (pool : List Rec) (R : Nat) :
    (tpLeaves g w pool).getD R [] =
      if R < g.ranges then pool.filter (fun x => tpRange g w x == R) else [] := by
  unfold tpLeaves
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  split_ifs with h
  · rw [List.getElem?_range h]; rfl
  · rw [List.getElem?_eq_none (by simpa using h)]; rfl

end RebuildBound.TP6Aux

open RebuildBound.Model RebuildBound.D6 RebuildBound.TP6Aux in
/-- **TP6, schedule independence.** -/
theorem RebuildBound.TP6 : RebuildBound.Spec.TP6_statement := by
  intro rule g unsh w inp ops hv hg hlanes hsched
  have hk : 1 ≤ g.k := hg.1
  set b1 := runTPOps rule g w ops (tpRouteInit g (copyMain unsh inp.aMain)) with hb1
  set b2 := runTPOps rule g w g.canonicalOps (tpRouteInit g (copyMain unsh inp.aMain)) with hb2
  have hb := binRoute_TPREq rule g w ops hsched (tpRouteInit g (copyMain unsh inp.aMain))
  rw [← hb1, ← hb2] at hb
  have r1 : (tpReferenceWith rule g unsh w inp ops).route = b1 := rfl
  have r2 : (tpReferenceWith rule g unsh w inp g.canonicalOps).route = b2 := rfl
  refine ⟨by rw [r1, r2]; exact hb.main, fun j => by rw [r1, r2]; exact hb.perm j, ?_⟩
  -- the verdict
  set pool1 := tpPool g unsh b1 inp.aTier with hpool1
  set pool2 := tpPool g unsh b2 inp.aTier with hpool2
  have href1 : (tpReferenceWith rule g unsh w inp ops).trace =
      b1.trace ++ (if g.dfs then tpDfsTrace g w pool1 else []) ++
        (tpFinish rule g w b1.main (tpLeaves g w pool1)).trace ++
        (tpDrain (tpFinish rule g w b1.main (tpLeaves g w pool1))).2 := rfl
  have href2 : (tpReferenceWith rule g unsh w inp g.canonicalOps).trace =
      b2.trace ++ (if g.dfs then tpDfsTrace g w pool2 else []) ++
        (tpFinish rule g w b2.main (tpLeaves g w pool2)).trace ++
        (tpDrain (tpFinish rule g w b2.main (tpLeaves g w pool2))).2 := rfl
  have hstash : List.Forall₂ List.Perm b1.stash b2.stash :=
    forall₂_of_getD List.Perm [] [] _ _ hb.len hb.perm
  have hpool : pool1.Perm pool2 := by
    rw [hpool1, hpool2]
    unfold tpPool
    refine List.Perm.filter _ (List.Perm.append_right _ ?_)
    exact flatten_perm_of_forall₂ (List.forall₂_take _ hstash)
  have hroute : TPFails g b1.trace ↔ TPFails g b2.trace :=
    binRoute_fails_iff rule g w (copyMain unsh inp.aMain) ops hsched
  have hdfs : (if g.dfs then tpDfsTrace g w pool1 else []) =
      (if g.dfs then tpDfsTrace g w pool2 else []) := by
    split_ifs
    · exact tpDfsTrace_perm g w hpool
    · rfl
  -- the finish phase
  have h0 : FinRel g w 0
      ({ main := b1.main, last := [], leaves := tpLeaves g w pool1, trace := [] } : TPFin)
      ({ main := b2.main, last := [], leaves := tpLeaves g w pool2, trace := [] } : TPFin) := by
    refine ⟨by simp only [hb.main], fun v _ => by simp only [hb.main], rfl, rfl, ?_, fun R => ?_⟩
    · simp [tpLeaves]
    · simp only [tpLeaves_getD]
      split_ifs
      · exact LeafRel.of_perm g w (hpool.filter _)
      · exact LeafRel.of_perm g w (List.Perm.refl _)
  have hU := finish_rel rule g w hk g.half le_rfl _ _ h0
  have hf1 : tpFinish rule g w b1.main (tpLeaves g w pool1) =
      (List.range g.half).foldl (fun st i => tpLastStep rule g w i st)
        { main := b1.main, last := [], leaves := tpLeaves g w pool1, trace := [] } := rfl
  have hf2 : tpFinish rule g w b2.main (tpLeaves g w pool2) =
      (List.range g.half).foldl (fun st i => tpLastStep rule g w i st)
        { main := b2.main, last := [], leaves := tpLeaves g w pool2, trace := [] } := rfl
  rw [← hf1, ← hf2] at hU
  have hF : List.Forall₂ (fun a b => a.length = b.length)
      ((tpFinish rule g w b1.main (tpLeaves g w pool1)).leaves ++
        [(tpFinish rule g w b1.main (tpLeaves g w pool1)).last])
      ((tpFinish rule g w b2.main (tpLeaves g w pool2)).leaves ++
        [(tpFinish rule g w b2.main (tpLeaves g w pool2)).last]) := by
    have hL : List.Forall₂ (fun a b => a.length = b.length)
        (tpFinish rule g w b1.main (tpLeaves g w pool1)).leaves
        (tpFinish rule g w b2.main (tpLeaves g w pool2)).leaves :=
      forall₂_of_getD _ [] [] _ _ hU.off.1 (fun R => (hU.off.2 R).1)
    exact List.rel_append hL (List.Forall₂.cons (by rw [hU.last]) List.Forall₂.nil)
  have hdrain := drain_trace_eq _ _ hF ([], []) ([], []) rfl rfl
  have hfails : TPFails g (tpReferenceWith rule g unsh w inp ops).trace ↔
      TPFails g (tpReferenceWith rule g unsh w inp g.canonicalOps).trace := by
    rw [href1, href2, tpFails_append, tpFails_append, tpFails_append, tpFails_append,
      tpFails_append, tpFails_append, hroute, hdfs, hU.trace]
    have : (tpDrain (tpFinish rule g w b1.main (tpLeaves g w pool1))).2 =
        (tpDrain (tpFinish rule g w b2.main (tpLeaves g w pool2))).2 := hdrain
    rw [this]
  rw [Bool.eq_iff_iff, tpJobWith_toBool, tpJobWith_toBool, hfails]
