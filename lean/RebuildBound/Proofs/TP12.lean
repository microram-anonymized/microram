import RebuildBound.Proofs.TP12.Assembly

/-!
# TP12: conservation, placement and counts of the top preparation

`TP12_of : TP6_statement → TP12_statement`. The route's final main is the
stage-by-stage main (`TP6`); every record of it agrees with its bucket on bits
`0 … k - 2` (`canonUpTo_inv`), so its home is `i + half · bit` for a record of
bucket `i` or `i + half`. Main and stashes are a permutation of A's
unflagged records at every point of every schedule (`runTPOps_RInv`).
The fused last level is analysed pair by pair (`Finish.lean`, `FinStep.lean`):
bucket `i` keeps `min C arrivals` records of its home from the split and then
`min C (arrivals + candidates)` after its offer, and a leftover or shed record
of a home implies that home is full. The drain is a permutation of the
leftovers (`Assembly.lean`).
-/

namespace RebuildBound.TP12

open RebuildBound.Model RebuildBound.D23 RebuildBound.S12

theorem flatten_take_last {α : Type} (l : List (List α)) (m : Nat) (hl : l.length = m + 1)
    (h : l.getD m [] = []) : l.flatten = (l.take m).flatten := by
  have e := List.take_append_drop m l
  have hd : l.drop m = [l.getD m []] := by
    rw [getD_eq_getElem' _ _ _ (by omega), List.drop_eq_getElem_cons (by omega),
      List.drop_of_length_le (by omega)]
  conv_lhs => rw [← e, List.flatten_append, hd, h]
  simp

theorem copyMain_recs (unsh : Rec → Bool) (aMain : List Bucket) :
    (copyMain unsh aMain).flatMap Bucket.recs =
      (aMain.flatMap Bucket.recs).filter fun r => !flagged unsh r := by
  unfold copyMain
  rw [List.flatMap_map, List.filter_flatMap]
  apply List.flatMap_congr
  intro B _
  exact D1Lemmas.recs_map_filter _ B

theorem low_mod (g : TPGeom) {x v : Nat} (h : ∀ b < g.k - 1, x.testBit b = v.testBit b) :
    x % g.half = v % g.half := by
  unfold TPGeom.half
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hb : b < g.k - 1
  · simp [hb, h b hb]
  · simp [hb]

end RebuildBound.TP12

theorem RebuildBound.TP12_of (h6 : RebuildBound.Spec.TP6_statement) :
    RebuildBound.Spec.TP12_statement := by
  open RebuildBound.Model RebuildBound.TP12 in
  intro rule g unsh w inp ops hv hg hlanes hops
  have hk := hg.1
  have hinit : RInv g ((copyMain unsh inp.aMain).flatMap Bucket.recs)
      (tpRouteInit g (copyMain unsh inp.aMain)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [tpRouteInit, copyMain, hlanes.1]
    · intro B hB
      simp only [tpRouteInit, copyMain, List.mem_map] at hB
      obtain ⟨B0, hB0, rfl⟩ := hB
      simpa using hlanes.2 B0 hB0
    · simp [tpRouteInit]
    · simp only [tpRouteInit]
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      have : g.k - 1 < g.k := by omega
      simp [this]
    · simp [tpRouteInit]
  have hopsOK : ∀ o ∈ ops, OpOK g o := by
    intro o ho
    have := hops.1.mem_iff.1 ho
    rw [canonicalOps_eq] at this
    exact canonUpTo_mem g (Nat.le_refl _) this
  have hr := runTPOps_RInv (w := w) hv ops _ hopsOK hinit
  obtain ⟨_, hlow⟩ := canonUpTo_inv hv g w hinit (g.k - 1) (Nat.le_refl _)
  have hmain := (h6 rule g unsh w inp ops hv hg hlanes hops).1
  have hmain' : (runTPOps rule g w ops (tpRouteInit g (copyMain unsh inp.aMain))).main =
      (runTPOps rule g w (canonUpTo g (g.k - 1)) (tpRouteInit g (copyMain unsh inp.aMain))).main :=
    hmain
  have hM : MData g w (runTPOps rule g w ops (tpRouteInit g (copyMain unsh inp.aMain))).main := by
    refine ⟨hr.len, hr.lanes, ?_⟩
    intro v hv' r hrr
    rw [hmain'] at hrr
    have hl := hlow v hv' r hrr
    have e1 := home_eq g hg (w r.key)
    have e2 := low_mod g hl
    unfold tpHome
    rw [e1, e2]
  have hS : List.Perm
      ((runTPOps rule g w ops (tpRouteInit g (copyMain unsh inp.aMain))).main.flatMap Bucket.recs ++
        tpPool g unsh (runTPOps rule g w ops (tpRouteInit g (copyMain unsh inp.aMain))) inp.aTier)
      (inp.survivors unsh) := by
    generalize runTPOps rule g w ops (tpRouteInit g (copyMain unsh inp.aMain)) = rt at hr ⊢
    have hst := flatten_take_last rt.stash (g.k - 1) (by rw [hr.slen]; omega) hr.slast
    have hperm := hr.perm
    rw [hst, copyMain_recs] at hperm
    unfold tpPool TPInputs.survivors TPInputs.aAll
    set q : Rec → Bool := fun r => !flagged unsh r with hq
    set Mr := rt.main.flatMap Bucket.recs
    set T := (rt.stash.take (g.k - 1)).flatten
    have hmem : ∀ x ∈ Mr ++ T, q x = true := by
      intro x hx
      exact (List.mem_filter.1 (hperm.mem_iff.1 hx)).2
    have e1 : (Mr ++ T).filter q = Mr ++ T := List.filter_eq_self.2 hmem
    have e2 : (Mr ++ T).filter q = Mr.filter q ++ T.filter q := List.filter_append ..
    have hMq : Mr.filter q = Mr := List.filter_eq_self.2 (fun x hx => hmem x (List.mem_append_left _ hx))
    have hTq : T.filter q = T := List.filter_eq_self.2 (fun x hx => hmem x (List.mem_append_right _ hx))
    have e3 : (T ++ inp.aTier).filter q = T ++ inp.aTier.filter q := by
      rw [List.filter_append, hTq]
    rw [e3, ← List.append_assoc, List.filter_append]
    refine (List.Perm.append_right _ ?_)
    exact hperm
  exact tp12_core hv hg hM hS _ rfl
