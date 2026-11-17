import RebuildBound.Spec.SepT
import RebuildBound.Proofs.S4a.Radix
import RebuildBound.Proofs.S4a.Route
import RebuildBound.Proofs.S4a.Pass
import RebuildBound.Proofs.S4a.Trace
import RebuildBound.Proofs.ListAux.Lists

/-!
# S4a: the route and the DFS at a general digit

`ST4a_of : ST6_statement → ST4a_statement`. The reference trace is the route
trace (stage-stash and radix entries), then the DFS trace, then the finish and
drain traces; `sFirstFailure` returns the first entry above its capacity.

* **Stage stash `j`.** An entry is at most the final length of stash `j`
  (`RouteP`), which by ST6 is the stage-by-stage run's, at most
  `sRawStageExcess j` (`S4a/Route.lean`).
* **Radix.** An entry is at most the final radix stash, which ST6 identifies
  with the stage-by-stage run's, at most `sAHomeExcess` (`S4a/Pass.lean`,
  with the class bound `S4a/Radix.lean`).
* **DFS node.** Every route entry passed, so every stash and the pool fit; the
  failing node's count exceeds `C 2^(rangeBits - dd)`; by pigeonhole over its
  coarse ranges one range holds more than `C` pool records. The pool is a
  filtered permutation of the early list and the late sheds, and the early list
  fits `earlyCap`, so `sRefCoarse` counts all of them. No ST6 here.
-/

namespace RebuildBound.S4aProof

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
  | succ n ih => rw [D4aProof.sum_range_succ', ih]; ring

lemma canonicalOps_lt (g : SepGeom) : ∀ o ∈ g.canonicalOps, o.1 < g.k := by
  intro o ho
  simp only [SepGeom.canonicalOps, List.mem_flatMap, List.mem_map, List.mem_range] at ho
  obtain ⟨j, hj, i, _, rfl⟩ := ho
  exact hj

end RebuildBound.S4aProof

open RebuildBound.Model RebuildBound.Spec RebuildBound.S4aProof in
open RebuildBound.D4aProof (length_flatten_take_le countP_block) in
theorem RebuildBound.ST4a_of (h6 : RebuildBound.Spec.ST6_statement) :
    RebuildBound.Spec.ST4a_statement := by
  intro rule g wOld w inp ops hr hg hin hops run
  obtain ⟨hmain6, hstash6, hrad6, _⟩ := h6 rule g wOld w inp ops hr hg hin hops
  -- the run's structure
  set Rb := runSOps rule g w ops (sRouteInit g inp.aMain) with hRb
  set R := radixPass g w Rb with hR
  have hroute : run.route = R := rfl
  have htrace : run.trace = R.trace ++ sDfsTrace g w run.pool ++ run.fin.trace ++
      (sDrain run.fin).2 := rfl
  have hpool : run.pool = sPool R inp.aTier inp.bTier := rfl
  have hopsk : ∀ o ∈ ops, o.1 < g.k := fun o ho => canonicalOps_lt g o (hops.1.subset ho)
  obtain ⟨hRP, hRbs, hRbr⟩ := runSOps_routeP rule g w ops hopsk (sRouteInit g inp.aMain)
    (by simp [sRouteInit]) (routeInit_routeP g inp.aMain)
  have hRP : RouteP Rb := hRP
  have hRbs : Rb.stash.length = g.k := hRbs
  have hRadP : RadixP Rb := by
    refine ⟨fun e he => Or.inl (hRP.1 e he), fun e he hre => ?_⟩
    obtain ⟨j, c, hjc⟩ := hRP.1 e he
    rw [hjc] at hre; cases hre
  have hRadP' : RadixP R := radixPass_radixP g w Rb hRadP
  have hRst : R.stash = Rb.stash := radixPass_stash g w Rb
  have hRbrad : Rb.radix = [] := by rw [hRbr]; simp [sRouteInit]
  -- the stage-by-stage run
  set Rc := runSOps rule g w g.canonicalOps (sRouteInit g inp.aMain) with hRc
  have hG := ginv_canon rule g wOld w inp hr hin hg
  rw [← hRc] at hG
  obtain ⟨_, _, hRcr⟩ := runSOps_routeP rule g w g.canonicalOps (canonicalOps_lt g)
    (sRouteInit g inp.aMain) (by simp [sRouteInit]) (routeInit_routeP g inp.aMain)
  have hRcrad : Rc.radix = [] := by rw [hRcr]; simp [sRouteInit]
  have hcanon : sRouteWith rule g w inp.aMain g.canonicalOps = radixPass g w Rc := rfl
  rw [hcanon] at hmain6 hstash6 hrad6
  have hRtr : sRouteWith rule g w inp.aMain ops = R := rfl
  rw [hRtr] at hmain6 hstash6 hrad6
  have hstashC : ∀ j, List.Perm (R.stash.getD j []) (Rc.stash.getD j []) := by
    intro j; have := hstash6 j; rw [radixPass_stash g w Rc] at this; exact this
  have hradC : R.radix = (radixPass g w Rc).radix := hrad6
  -- tags of the other phases
  have hkD : ∀ e ∈ sDfsTrace g w run.pool, ∃ dd c, e.1 = .dfs dd c := by
    intro e he
    obtain ⟨d, _, c, _, rfl⟩ := mem_sDfsTrace g w _ e he
    exact ⟨d, c, rfl⟩
  have hkF : ∀ e ∈ run.fin.trace, e.1 = .insertion := sFinish_tag _ _ _ _ _
  have hkDr : ∀ e ∈ (sDrain run.fin).2, e.1 = .drain := sDrain_tag _
  -- a failing entry lies in the route when it is a stash or radix test
  have hroute_mem : ∀ x ∈ run.trace, ((∃ j c, x.1 = .stash j c) ∨ x.1 = .radix) → x ∈ R.trace := by
    intro x hx hxt
    rw [htrace] at hx
    simp only [List.mem_append] at hx
    rcases hx with ((h | h) | h) | h
    · exact h
    · exfalso; obtain ⟨dd, c, hdd⟩ := hkD x h
      rcases hxt with ⟨j, c', h'⟩ | h' <;> simp [hdd] at h'
    · exfalso; have := hkF x h
      rcases hxt with ⟨j, c', h'⟩ | h' <;> simp [this] at h'
    · exfalso; have := hkDr x h
      rcases hxt with ⟨j, c', h'⟩ | h' <;> simp [this] at h'
  refine ⟨?_, ?_, ?_⟩
  · -- a stage-stash failure
    intro j c hfail
    obtain ⟨x, hx, hx1⟩ := Option.map_eq_some_iff.mp hfail
    have hxmem := List.mem_of_find?_eq_some hx
    have hxp := List.find?_some hx
    have hxR := hroute_mem x hxmem (Or.inl ⟨j, c, hx1⟩)
    rcases radixPass_trace g w Rb x hxR with hxb | hxb
    · have hle := hRP.2.1 x hxb j c hx1
      have hcap : g.capOf x.1 = g.stashPages * g.C := by rw [hx1]; rfl
      simp only [hcap, decide_eq_true_eq] at hxp
      -- the final stash `j`
      have hlen : (Rb.stash.getD j []).length ≤ sRawStageExcess g wOld w inp j := by
        have hP := (hstashC j).length_eq
        rw [hRst] at hP
        rw [hP]
        rcases Nat.lt_or_ge j g.k with hj | hj
        · exact hG.early j hj
        · rw [D4aProof.getD_of_le _ _ _ (by rw [hG.shape.stashLen]; exact hj)]
          simp
      omega
    · rw [hx1] at hxb; cases hxb
  · -- a radix failure
    intro hfail
    obtain ⟨x, hx, hx1⟩ := Option.map_eq_some_iff.mp hfail
    have hxmem := List.mem_of_find?_eq_some hx
    have hxp := List.find?_some hx
    have hxR := hroute_mem x hxmem (Or.inr hx1)
    have hle := hRadP'.2 x hxR hx1
    have hcap : g.capOf x.1 = g.stashPages * g.C := by rw [hx1]; rfl
    simp only [hcap, decide_eq_true_eq] at hxp
    have hb := radixPass_length_le hg hG.shape hG.cons hG.at_dest hRcrad
    rw [← hradC] at hb
    omega
  · -- a DFS failure
    intro dd c hfail hfit
    obtain ⟨x, hx, hx1⟩ := Option.map_eq_some_iff.mp hfail
    have hxp := List.find?_some hx
    -- no route entry fails
    have hnoR : ∀ y ∈ R.trace, ¬ (decide (g.capOf y.1 < y.2) = true) := by
      intro y hy hpy
      have hne : R.trace.find? (fun t => decide (g.capOf t.1 < t.2)) ≠ none := by
        intro hnone; exact (List.find?_eq_none.mp hnone) y hy hpy
      obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.mp hne
      have h2 : run.trace.find? (fun t => decide (g.capOf t.1 < t.2)) = some z := by
        rw [htrace, List.find?_append, List.find?_append, List.find?_append, hz]
        simp
      rw [hx] at h2
      have hxz := Option.some.inj h2
      subst hxz
      rcases hRadP'.1 x (List.mem_of_find?_eq_some hz) with ⟨j, c', hj⟩ | hj <;>
        rw [hx1] at hj <;> cases hj
    -- the failing entry is a DFS node
    have hxmem := List.mem_of_find?_eq_some hx
    rw [htrace] at hxmem
    have hxD : x ∈ sDfsTrace g w run.pool := by
      simp only [List.mem_append] at hxmem
      rcases hxmem with ((h | h) | h) | h
      · exfalso
        rcases hRadP'.1 x h with ⟨j, c', hj⟩ | hj <;> rw [hx1] at hj <;> cases hj
      · exact h
      · exfalso; rw [hkF x h] at hx1; cases hx1
      · exfalso; rw [hkDr x h] at hx1; cases hx1
    obtain ⟨d', hd', c', hc', hxe⟩ := mem_sDfsTrace g w run.pool x hxD
    rw [hxe] at hx1
    simp only [STest.dfs.injEq] at hx1
    obtain ⟨h1, h2⟩ := hx1
    subst h1; subst h2
    -- every stash, the radix stash and the pool fit
    have hstash : ∀ j, (R.stash.getD j []).length ≤ g.stashPages * g.C := by
      intro j
      rw [hRst]
      rcases Nat.lt_or_ge j g.k with hj | hj
      · rcases hRP.2.2 j with h | ⟨c', h⟩
        · rw [h]; simp
        · have hmem : (STest.stash j c', (Rb.stash.getD j []).length) ∈ R.trace :=
            radixPass_trace_sup g w Rb _ h
          have := hnoR _ hmem
          simpa [SepGeom.capOf] using this
      · rw [D4aProof.getD_of_le _ _ _ (by rw [hRbs]; exact hj)]; simp
    have hradlen : R.radix.length ≤ (if 1 < g.r then 1 else 0) * (g.stashPages * g.C) := by
      by_cases h1 : 1 < g.r
      · obtain ⟨e, he, he1, he2⟩ := radixPass_last g w Rb h1
        have := hnoR e he
        have h3 : g.capOf e.1 = g.stashPages * g.C := by rw [he1]; rfl
        simp only [h3, decide_eq_true_eq, not_lt] at this
        rw [if_pos h1, ← he2]; omega
      · have : R = Rb := radixPass_of_not g w Rb h1
        rw [this, hRbrad]; simp
    have hflat : R.stash.flatten.length ≤ g.k * (g.stashPages * g.C) := by
      have := length_flatten_take_le R.stash (fun _ => g.stashPages * g.C) hstash g.k
      rw [List.take_of_length_le (by rw [hRst, hRbs])] at this
      simpa using this
    have hpoolLen : run.pool.length ≤ g.poolPages * g.C := by
      rw [hpool]; unfold sPool
      refine le_trans (List.length_filter_le _ _) ?_
      simp only [List.length_append]
      unfold STiersFit at hfit
      unfold SepGeom.poolPages
      have : ((g.k + if 1 < g.r then 1 else 0) * g.stashPages + g.aTierPages) * g.C =
          g.k * (g.stashPages * g.C) + (if 1 < g.r then 1 else 0) * (g.stashPages * g.C) +
            g.aTierPages * g.C := by ring
      rw [this]; omega
    -- the node count exceeds `C 2^(rangeBits - dd)`
    subst hxe
    set e := g.rangeBits - d' with he
    set n := (run.pool.filter fun y => sRange g w y / 2 ^ e == c').length with hn
    have hnle : n ≤ run.pool.length := List.length_filter_le _ _
    have hxp' : min (g.poolPages * g.C) (g.C * 2 ^ e) < n := of_decide_eq_true hxp
    have hbig : g.C * 2 ^ e < n := by
      omega
    -- pigeonhole over the node's coarse ranges
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    have hpe : 0 < 2 ^ e := by positivity
    have hn' : n = run.pool.countP
        (fun y => decide (c' * 2 ^ e ≤ sRange g w y ∧ sRange g w y < c' * 2 ^ e + 2 ^ e)) := by
      rw [hn, ← List.countP_eq_length_filter]
      apply List.countP_congr
      intro y _
      simp only [beq_iff_eq, decide_eq_true_eq]
      exact div_eq_iff' _ _ _ hpe
    have hearly : (sEarlyList run inp g.I).length ≤ g.earlyCap := by
      unfold sEarlyList SepGeom.earlyCap
      rw [List.length_append, hroute]
      have := length_flatten_take_le R.stash (fun _ => g.stashPages * g.C) hstash g.I
      unfold STiersFit at hfit
      rw [sum_const_range] at this
      omega
    have hblock := countP_block run.pool (sRange g w) (c' * 2 ^ e) g.C (2 ^ e) (by
      intro t ht
      have hR : c' * 2 ^ e + t < g.ranges := by
        have hdd : g.rangeBits = d' + e := by omega
        unfold SepGeom.ranges
        rw [hdd, pow_add]
        have : (c' + 1) * 2 ^ e ≤ 2 ^ d' * 2 ^ e := Nat.mul_le_mul_right _ hc'
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      refine le_trans ?_ (hcon _ hR)
      unfold sRefCoarse
      rw [List.take_of_length_le hearly]
      unfold sEarlyList sLateSheds
      rw [hroute, hpool]
      unfold sPool
      refine le_trans (List.filter_sublist.countP_le) ?_
      have hsplit : R.stash.flatten =
          (R.stash.take g.I).flatten ++ (R.stash.drop g.I).flatten := by
        rw [← List.flatten_append, List.take_append_drop]
      rw [hsplit]
      simp only [List.countP_append]
      omega)
    omega
