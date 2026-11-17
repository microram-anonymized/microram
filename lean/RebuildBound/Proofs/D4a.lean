import RebuildBound.Proofs.D4a.Route
import RebuildBound.Proofs.ListAux.Trace

/-!
# D4a: first-failure inventory, stage stashes and the DFS

`T4a_statement`. The reference trace is the route trace, then the DFS trace,
then the finish and drain traces; `firstFailure` returns the first entry that
exceeds its capacity.

* **Stage stash.** A `.stash j` entry lies in the route trace, whose entries
  are bounded by `rawStageExcess j` (`GInv.trace`, from `D4a/Route.lean`).
* **DFS node.** Every route entry passed, so every stash fits `S_j`, the pool
  fits `P_pool`, and the failing node's count exceeds `L · 2^(D_c - d)`. By
  pigeonhole over the node's `2^(D_c - d)` coarse ranges one range holds more
  than `L` pool records. The pool is a filtered permutation of the early list
  and the late sheds, and the early list fits `P`, so `refCoarse` counts all
  of them.

The model's definitions are used as they are; no probability is involved, so
the measure-based API is not used.
-/

namespace RebuildBound.D4aProof

open RebuildBound.Model RebuildBound.Spec

/-! ### The later phases record only insertion and drain tests -/

lemma insertBucket_trace (g : Geom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i : ℕ)
    (st : FinState) :
    ∃ q, (insertBucket g w bMain i st).trace = st.trace ++ [(.insertion, q)] := ⟨_, rfl⟩

lemma finish_trace (g : Geom) (w : Model.LogicalKey → Nat) (inp : Inputs) (routed : List Bucket)
    (leaves : List (List Rec)) :
    ∀ e ∈ (finish g w inp routed leaves).trace, e.1 = .insertion := by
  unfold finish
  suffices h : ∀ (L : List ℕ) (st : FinState), (∀ e ∈ st.trace, e.1 = .insertion) →
      ∀ e ∈ (L.foldl (fun st i => insertBucket g w inp.bMain i st) st).trace,
        e.1 = .insertion from h _ _ (by simp)
  intro L
  induction L with
  | nil => intro st h; simpa using h
  | cons i L ih =>
    intro st h
    rw [List.foldl_cons]
    apply ih
    obtain ⟨q, hq⟩ := insertBucket_trace g w inp.bMain i st
    rw [hq]
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact h e he
    · simp only [List.mem_singleton] at he; rw [he]

end RebuildBound.D4aProof

open RebuildBound.Model RebuildBound.Spec RebuildBound.D4aProof in
theorem RebuildBound.T4a : RebuildBound.Spec.T4a_statement := by
  intro rule g caps TA TB wOld w inp hv hin
  set r := reference rule g w inp with hr
  have hroute : r.route = routeA rule g w inp.aMain := rfl
  have htrace : r.trace = r.route.trace ++ dfsTrace g w r.pool ++ r.fin.trace ++
      (drain r.fin).2 := rfl
  have hpool : r.pool = poolA r.route inp.aTier inp.bTier := rfl
  have hG := ginv_routeA rule g wOld w inp hv hin
  rw [← hroute] at hG
  have hkR : ∀ e ∈ r.route.trace, ∃ j, e.1 = .stash j := by
    intro e he
    obtain ⟨j, _, h, _⟩ := hG.trace e he
    exact ⟨j, h⟩
  have hkF : ∀ e ∈ r.fin.trace, e.1 = .insertion := finish_trace _ _ _ _ _
  have hkD : ∀ e ∈ (drain r.fin).2, e.1 = .drain := drain_trace _
  constructor
  · -- a stage-stash failure
    intro j S hS hfail
    obtain ⟨x, hx, hx1⟩ := Option.map_eq_some_iff.mp hfail
    have hxmem := List.mem_of_find?_eq_some hx
    have hxp := List.find?_some hx
    rw [htrace] at hxmem
    have hxR : x ∈ r.route.trace := by
      simp only [List.mem_append] at hxmem
      rcases hxmem with ((h | h) | h) | h
      · exact h
      · exfalso
        obtain ⟨d, _, c, _, rfl⟩ := mem_dfsTrace g w r.pool x h
        cases hx1
      · exfalso; rw [hkF x h] at hx1; cases hx1
      · exfalso; rw [hkD x h] at hx1; cases hx1
    obtain ⟨j', _, hj', hle⟩ := hG.trace x hxR
    rw [hx1] at hj'
    cases hj'
    simp only [hx1, Caps.capOf, hS, exceeds, decide_eq_true_eq] at hxp
    omega
  · -- a DFS failure
    intro d c L Ss hL hSs hslots hfail
    obtain ⟨x, hx, hx1⟩ := Option.map_eq_some_iff.mp hfail
    have hxp := List.find?_some hx
    -- no route entry fails
    have hnoR : ∀ y ∈ r.route.trace, ¬ (exceeds (caps.capOf g y.1) y.2 = true) := by
      intro y hy hpy
      have hne : r.route.trace.find? (fun t => exceeds (caps.capOf g t.1) t.2) ≠ none := by
        intro hnone; exact (List.find?_eq_none.mp hnone) y hy hpy
      obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.mp hne
      have h2 : r.trace.find? (fun t => exceeds (caps.capOf g t.1) t.2) = some z := by
        rw [htrace, List.find?_append, List.find?_append, List.find?_append, hz]
        simp
      rw [hx] at h2
      cases h2
      obtain ⟨j, hj⟩ := hkR x (List.mem_of_find?_eq_some hz)
      rw [hx1] at hj
      cases hj
    -- the failing entry is a DFS node
    have hxmem := List.mem_of_find?_eq_some hx
    rw [htrace] at hxmem
    have hxD : x ∈ dfsTrace g w r.pool := by
      simp only [List.mem_append] at hxmem
      rcases hxmem with ((h | h) | h) | h
      · exfalso; obtain ⟨j, hj⟩ := hkR x h; rw [hx1] at hj; cases hj
      · exact h
      · exfalso; rw [hkF x h] at hx1; cases hx1
      · exfalso; rw [hkD x h] at hx1; cases hx1
    obtain ⟨d', hd', c', hc', hxe⟩ := mem_dfsTrace g w r.pool x hxD
    rw [hxe] at hx1
    simp only [Test.dfs.injEq] at hx1
    obtain ⟨h1, h2⟩ := hx1
    subst d' c'
    -- every stash fits its capacity
    have hstash : ∀ j, (r.route.stash.getD j []).length ≤ Ss j := by
      intro j
      rcases Nat.lt_or_ge j g.stages with hj | hj
      · rcases hG.recd j with h | h
        · rw [h]; simp
        · have := hnoR _ h
          simp only [Caps.capOf, hSs j hj, exceeds, decide_eq_true_eq] at this
          omega
      · rw [getD_of_le _ _ _ (by rw [hG.shape.stashLen]; exact hj)]; simp
    -- the pool fits its slots
    have hflat : r.route.stash.flatten.length ≤ sumUpTo Ss g.stages := by
      have := length_flatten_take_le r.route.stash Ss hstash g.stages
      rwa [List.take_of_length_le (by rw [hG.shape.stashLen])] at this
    have hpoolLen : r.pool.length ≤ g.poolSlots := by
      rw [hpool]
      unfold poolA
      have := List.length_filter_le (fun x => !(inp.bTier.map Rec.key).contains x.key)
        (r.route.stash.flatten ++ inp.aTier)
      rw [List.length_append] at this
      have := hin.aTierCap
      omega
    -- the node count exceeds `L · 2^(D_c - d)`
    set e := g.depth - d with he
    set n := (r.pool.filter fun y => rangeOf g w y / 2 ^ e == c).length with hn
    have hnle : n ≤ r.pool.length := List.length_filter_le _ _
    rw [hxe] at hxp
    simp only [Caps.capOf, hL, Option.map_some, exceeds, decide_eq_true_eq] at hxp
    have hbig : L * 2 ^ e < n := by
      rw [← he] at hxp
      omega
    -- pigeonhole over the node's coarse ranges
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    have hpe : 0 < 2 ^ e := by positivity
    have hn' : n = r.pool.countP
        (fun y => decide (c * 2 ^ e ≤ rangeOf g w y ∧ rangeOf g w y < c * 2 ^ e + 2 ^ e)) := by
      rw [hn, ← List.countP_eq_length_filter]
      apply List.countP_congr
      intro y _
      simp only [beq_iff_eq, decide_eq_true_eq]
      exact div_eq_iff' _ _ _ hpe
    have hblock := countP_block r.pool (rangeOf g w) (c * 2 ^ e) L (2 ^ e) (by
      intro t ht
      have hR : c * 2 ^ e + t < g.ranges := by
        have hdd : g.depth = d + e := by omega
        unfold Geom.ranges
        rw [hdd, pow_add]
        have : (c + 1) * 2 ^ e ≤ 2 ^ d * 2 ^ e := Nat.mul_le_mul_right _ hc'
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      refine le_trans ?_ (hcon _ hR)
      -- the pool's count in a range is at most the reference coarse count
      have hearly : (earlyList r inp g.lo).length ≤ TA + sumUpTo Ss g.lo := by
        unfold earlyList
        rw [List.length_append]
        have := length_flatten_take_le r.route.stash Ss hstash g.lo
        have := hin.aTierCap
        unfold sumUpTo at *
        omega
      unfold refCoarse
      rw [List.take_of_length_le hearly]
      unfold earlyList lateSheds
      rw [hpool]
      unfold poolA
      refine le_trans (List.filter_sublist.countP_le) ?_
      have hsplit : r.route.stash.flatten =
          (r.route.stash.take g.lo).flatten ++ (r.route.stash.drop g.lo).flatten := by
        rw [← List.flatten_append, List.take_append_drop]
      rw [hsplit]
      simp only [List.countP_append]
      omega)
    omega
