import Mathlib
import RebuildBound.Spec.TopPrepT
import RebuildBound.Proofs.ListAux.Lists
import RebuildBound.Proofs.TP4.Route
import RebuildBound.Proofs.TP4.Trace
import RebuildBound.Proofs.TP4.Fin

/-!
# TP4a: the stashes and the DFS (conditional on TP6)

The reference trace is the route trace (stage-stash entries), the DFS trace,
the last level's trace and the drain trace; `tpFirstFailure` returns the first
entry above its capacity.

* **Stage stash `j < k - 1`.** An entry is at most the final length of stash `j`
  (`RouteP`), which by TP6 is the stage-by-stage run's, at most
  `tpRawStageExcess j` (`TP4/Route.lean`).
* **Last stash.** The last level's merge-splits read the route's buckets, whose
  records sit at `dest (k - 1)`; the last stash is at most the complete-home
  excess (`TP4/Fin.lean`).
* **DFS node.** Every route entry passed, so every stash and the pool fit; the
  failing node's count exceeds `C 2^(rangeBits - dd)`; by pigeonhole over its
  coarse ranges one range holds more than `C` pool records. No TP6 here.
-/

namespace RebuildBound.TP4Proof

open RebuildBound.Model RebuildBound.Spec
open RebuildBound.D4aProof (length_flatten_take_le countP_block)

lemma div_eq_iff' (a M c : ℕ) (hM : 0 < M) : a / M = c ↔ c * M ≤ a ∧ a < c * M + M := by
  have h1 := Nat.le_div_iff_mul_le (x := c) (y := a) hM
  have h2 := Nat.div_lt_iff_lt_mul (x := a) (y := c + 1) hM
  rw [Nat.add_mul, Nat.one_mul] at h2
  omega

lemma sum_const_range (n S : ℕ) : ((List.range n).map fun _ => S).sum = n * S := by
  induction n with
  | zero => simp
  | succ n ih => rw [RebuildBound.D4aProof.sum_range_succ', ih]; ring

lemma take_take_sub {α : Type} (s : List α) (I m : ℕ) :
    (List.take I (List.take m s)).Sublist (List.take I s) := by
  rw [List.take_take]
  have : List.take (min I m) s = List.take (min I m) (List.take I s) := by
    rw [List.take_take, min_eq_left (min_le_left _ _)]
  rw [this]; exact List.take_sublist _ _

lemma mem_tpDfsTrace (g : TPGeom) (w : Model.LogicalKey → Nat) (pool : List Rec) (e : TPTest × ℕ)
    (he : e ∈ tpDfsTrace g w pool) :
    ∃ d, d < g.rangeBits + 1 ∧ ∃ c, c < 2 ^ d ∧
      e = (.dfs d c, (pool.filter fun r => tpRange g w r / 2 ^ (g.rangeBits - d) == c).length) := by
  unfold tpDfsTrace at he
  obtain ⟨d, hd, he⟩ := List.mem_flatMap.mp he
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
  exact ⟨d, List.mem_range.mp hd, c, List.mem_range.mp hc, rfl⟩

lemma tpDrain_tag (st : TPFin) : ∀ e ∈ (tpDrain st).2, e.1 = .drain := by
  unfold tpDrain
  have : ∀ (L : List (List Rec)) (acc : List (Option Rec) × List (TPTest × ℕ)),
      (∀ e ∈ acc.2, e.1 = .drain) →
      ∀ e ∈ (L.foldl tpDrainStep acc).2, e.1 = .drain := by
    intro L
    induction L with
    | nil => intro acc h; exact h
    | cons a L ih =>
      intro acc h
      rw [List.foldl_cons]
      apply ih
      intro e he
      simp only [tpDrainStep, List.mem_append, List.mem_singleton] at he
      rcases he with he | he
      · exact h e he
      · rw [he]
  exact this _ _ (by simp)

end RebuildBound.TP4Proof

open RebuildBound.Model RebuildBound.Spec RebuildBound.TP4Proof in
open RebuildBound.D4aProof (length_flatten_take_le countP_block) in
theorem RebuildBound.TP4a_of (h6 : RebuildBound.Spec.TP6_statement)
    (h12 : RebuildBound.Spec.TP12_statement) : RebuildBound.Spec.TP4a_statement := by
  intro rule g unsh pos w inp ops hr hg hin hops
  have _ := h12
  obtain ⟨hmain6, hstash6, _⟩ := h6 rule g unsh w inp ops hr hg ⟨hin.aLen, hin.aLanes⟩ hops
  set Rb := runTPOps rule g w ops (tpRouteInit g (copyMain unsh inp.aMain)) with hRb
  set Rc := runTPOps rule g w g.canonicalOps (tpRouteInit g (copyMain unsh inp.aMain)) with hRc
  set run := tpReferenceWith rule g unsh w inp ops with hrun
  have hroute : run.route = Rb := rfl
  have htrace : run.trace = Rb.trace ++ (if g.dfs then tpDfsTrace g w run.pool else []) ++
      run.fin.trace ++ (tpDrain run.fin).2 := rfl
  have hpool : run.pool = tpPool g unsh Rb inp.aTier := rfl
  have hfin : run.fin = tpFinish rule g w Rb.main (tpLeaves g w run.pool) := rfl
  have hmainE : Rb.main = Rc.main := hmain6
  have hstashE : ∀ j, List.Perm (Rb.stash.getD j []) (Rc.stash.getD j []) := hstash6
  have hopsk : ∀ o ∈ ops, o.1 < g.k := fun o ho => by
    have := canonicalOps_lt g o (hops.1.subset ho); omega
  obtain ⟨hRP, hRbs⟩ := runTPOps_routeP rule g w ops hopsk (tpRouteInit g (copyMain unsh inp.aMain))
    (by simp [tpRouteInit]) (routeInit_routeP g _)
  have hG := ginv_canon rule g unsh pos w inp hr hin hg
  rw [← hRc] at hG
  -- the last level's hypotheses
  have hrl : Rb.main.length = g.T := by rw [hmainE]; exact hG.shape.mainLen
  have hlanes : ∀ B ∈ Rb.main, B.length = g.C := by rw [hmainE]; exact hG.shape.lanes
  have hdest : ∀ m, ∀ r ∈ (Rb.main.getD m []).recs, m = dest pos w (g.k - 1) r := by
    rw [hmainE]; exact hG.at_dest
  have hcnt : ∀ p : Rec → Bool, (Rb.main.flatMap Bucket.recs).countP p ≤
      (inp.survivors unsh).countP p := by
    intro p
    have := hG.cons p
    have h2 := copyMain_countP_le unsh inp p
    rw [hmainE]; omega
  obtain ⟨hFtag, hFle⟩ := tpFinish_last_le rule g unsh pos w inp hr hg hin Rb.main hrl hlanes hdest
    hcnt (tpLeaves g w run.pool)
  rw [← hfin] at hFtag hFle
  have hFle' : run.fin.last.length ≤ tpRawStageExcess g unsh pos w inp (g.k - 1) := hFle
  have hkD : ∀ e ∈ (if g.dfs then tpDfsTrace g w run.pool else []), ∃ dd c, e.1 = .dfs dd c := by
    intro e he
    split_ifs at he with hd
    · obtain ⟨d, _, c, _, rfl⟩ := mem_tpDfsTrace g w _ e he
      exact ⟨d, c, rfl⟩
    · simp at he
  have hkDr : ∀ e ∈ (tpDrain run.fin).2, e.1 = .drain := tpDrain_tag _
  refine ⟨?_, ?_⟩
  · -- a stash failure
    intro j hfail
    obtain ⟨x, hx, hx1⟩ := Option.map_eq_some_iff.mp hfail
    have hxmem := List.mem_of_find?_eq_some hx
    have hxp := List.find?_some hx
    have hcap : g.capOf x.1 = g.stashPages * g.C := by rw [hx1]; rfl
    simp only [hcap, decide_eq_true_eq] at hxp
    rw [htrace] at hxmem
    simp only [List.mem_append] at hxmem
    rcases hxmem with ((h | h) | h) | h
    · obtain ⟨j', hj'⟩ := hRP.1 x h
      rw [hx1] at hj'
      have hle : x.2 ≤ (Rb.stash.getD j []).length := hRP.2.1 x h j hx1
      have hlen : (Rb.stash.getD j []).length ≤ tpRawStageExcess g unsh pos w inp j := by
        rw [(hstashE j).length_eq]
        rcases Nat.lt_or_ge j (g.k - 1) with hj | hj
        · exact hG.early j hj
        · rw [hG.later j hj]; simp
      omega
    · obtain ⟨dd, c, hdd⟩ := hkD x h
      rw [hx1] at hdd; cases hdd
    · obtain ⟨ht, hle⟩ := hFtag x h
      have hjk : j = g.k - 1 := by
        rw [hx1] at ht
        simpa using ht
      rw [hjk]
      omega
    · have := hkDr x h
      rw [hx1] at this; cases this
  · -- a DFS failure
    intro dd c hfit hfail
    obtain ⟨x, hx, hx1⟩ := Option.map_eq_some_iff.mp hfail
    have hxp := List.find?_some hx
    have hxmem := List.mem_of_find?_eq_some hx
    -- no route entry fails
    have hnoR : ∀ y ∈ Rb.trace, ¬ (decide (g.capOf y.1 < y.2) = true) := by
      intro y hy hpy
      have hne : Rb.trace.find? (fun t => decide (g.capOf t.1 < t.2)) ≠ none := by
        intro hnone; exact (List.find?_eq_none.mp hnone) y hy hpy
      obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.mp hne
      have h2 : run.trace.find? (fun t => decide (g.capOf t.1 < t.2)) = some z := by
        rw [htrace, List.find?_append, List.find?_append, List.find?_append, hz]
        simp
      rw [hx] at h2
      have hxz := Option.some.inj h2
      subst hxz
      obtain ⟨j, hj⟩ := hRP.1 x (List.mem_of_find?_eq_some hz)
      rw [hx1] at hj; cases hj
    rw [htrace] at hxmem
    have hxD : x ∈ tpDfsTrace g w run.pool := by
      simp only [List.mem_append] at hxmem
      rcases hxmem with ((h | h) | h) | h
      · exfalso
        obtain ⟨j, hj⟩ := hRP.1 x h
        rw [hx1] at hj; cases hj
      · split_ifs at h with hd
        · exact h
        · simp at h
      · exfalso; rw [(hFtag x h).1] at hx1; cases hx1
      · exfalso; rw [hkDr x h] at hx1; cases hx1
    obtain ⟨d', hd', c', hc', hxe⟩ := mem_tpDfsTrace g w run.pool x hxD
    rw [hxe] at hx1
    simp only [TPTest.dfs.injEq] at hx1
    obtain ⟨h1, h2⟩ := hx1
    subst h1; subst h2
    -- every stash and the pool fit
    have hstash : ∀ j, (Rb.stash.getD j []).length ≤ g.stashPages * g.C := by
      intro j
      rcases hRP.2.2 j with h | h
      · rw [h]; simp
      · have := hnoR _ h
        simpa [TPGeom.capOf] using this
    have hflat : (Rb.stash.take (g.k - 1)).flatten.length ≤ (g.k - 1) * (g.stashPages * g.C) := by
      have := length_flatten_take_le Rb.stash (fun _ => g.stashPages * g.C) hstash (g.k - 1)
      simpa [sum_const_range] using this
    unfold TPTiersFit at hfit
    have hpoolLen : run.pool.length ≤ g.poolPages * g.C := by
      rw [hpool]; unfold tpPool
      refine le_trans (List.length_filter_le _ _) ?_
      simp only [List.length_append]
      unfold TPGeom.poolPages
      have : (((g.k - 1) * g.stashPages + g.aTierPages) * g.C) =
          (g.k - 1) * (g.stashPages * g.C) + g.aTierPages * g.C := by ring
      rw [this]; omega
    -- the node count exceeds `C 2^(rangeBits - dd)`
    subst hxe
    set e := g.rangeBits - d' with he
    set n := (run.pool.filter fun y => tpRange g w y / 2 ^ e == c').length with hn
    have hnle : n ≤ run.pool.length := List.length_filter_le _ _
    have hxp' : min (g.poolPages * g.C) (g.C * 2 ^ e) < n := of_decide_eq_true hxp
    have hbig : g.C * 2 ^ e < n := by omega
    -- pigeonhole over the node's coarse ranges
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    have hpe : 0 < 2 ^ e := by positivity
    have hn' : n = run.pool.countP
        (fun y => decide (c' * 2 ^ e ≤ tpRange g w y ∧ tpRange g w y < c' * 2 ^ e + 2 ^ e)) := by
      rw [hn, ← List.countP_eq_length_filter]
      apply List.countP_congr
      intro y _
      simp only [beq_iff_eq, decide_eq_true_eq]
      exact div_eq_iff' _ _ _ hpe
    have hearly : (tpEarlyList g unsh run inp).length ≤ g.earlyCap := by
      unfold tpEarlyList TPGeom.earlyCap
      rw [List.length_append, hroute]
      have := length_flatten_take_le Rb.stash (fun _ => g.stashPages * g.C) hstash g.I
      rw [sum_const_range] at this
      have h3 := List.length_filter_le (fun x => !flagged unsh x) inp.aTier
      omega
    have hblock := countP_block run.pool (tpRange g w) (c' * 2 ^ e) g.C (2 ^ e) (by
      intro t ht
      have hR : c' * 2 ^ e + t < g.ranges := by
        have hdd : g.rangeBits = d' + e := by omega
        unfold TPGeom.ranges
        rw [hdd, pow_add]
        have : (c' + 1) * 2 ^ e ≤ 2 ^ d' * 2 ^ e := Nat.mul_le_mul_right _ hc'
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      refine le_trans ?_ (hcon _ hR)
      unfold tpRefCoarse
      rw [List.take_of_length_le hearly]
      unfold tpEarlyList tpLateSheds
      rw [hroute, hpool]
      unfold tpPool
      rw [List.filter_append, List.countP_append]
      have hsplit : (Rb.stash.take (g.k - 1)).flatten =
          (List.take g.I (Rb.stash.take (g.k - 1))).flatten ++
            ((Rb.stash.take (g.k - 1)).drop g.I).flatten := by
        rw [← List.flatten_append, List.take_append_drop]
      have hsub : (List.take g.I (Rb.stash.take (g.k - 1))).flatten.Sublist
          (Rb.stash.take g.I).flatten :=
        (take_take_sub _ _ _).flatten
      have h1 : ((Rb.stash.take (g.k - 1)).flatten.filter fun r => !flagged unsh r).countP
          (fun y => tpRange g w y == c' * 2 ^ e + t) ≤
          ((Rb.stash.take (g.k - 1)).flatten).countP (fun y => tpRange g w y == c' * 2 ^ e + t) :=
        List.filter_sublist.countP_le
      have h2 : (List.take g.I (Rb.stash.take (g.k - 1))).flatten.countP
          (fun y => tpRange g w y == c' * 2 ^ e + t) ≤
          (Rb.stash.take g.I).flatten.countP (fun y => tpRange g w y == c' * 2 ^ e + t) :=
        hsub.countP_le
      have h3 : ((Rb.stash.take (g.k - 1)).flatten).countP
          (fun y => tpRange g w y == c' * 2 ^ e + t) =
          (List.take g.I (Rb.stash.take (g.k - 1))).flatten.countP
            (fun y => tpRange g w y == c' * 2 ^ e + t) +
          ((Rb.stash.take (g.k - 1)).drop g.I).flatten.countP
            (fun y => tpRange g w y == c' * 2 ^ e + t) := by
        rw [hsplit, List.countP_append]
      simp only [List.countP_append] at ⊢
      omega)
    omega

