import Mathlib
import RebuildBound.Spec.TopPrepT
import RebuildBound.Proofs.ListAux.Lists
import RebuildBound.Proofs.ListAux.Fill
import RebuildBound.Proofs.TP4.Route
import RebuildBound.Proofs.TP4.Trace
import RebuildBound.Proofs.TP4.Fin
import RebuildBound.Proofs.TP4.A

/-!
# TP4b: the drain (conditional on TP12)

By TP12 the drain target ends with exactly `Σ_v (X_v - C)₊` records: the
survivors minus `Σ_v min(X_v, C)` placed in main. Every drain-trace entry is the
occupancy of a prefix of the final target, so at most `tpHomeExcess`.
-/

namespace RebuildBound.TP4Proof

open RebuildBound.Model RebuildBound.Spec
open RebuildBound.D4aProof (sum_range_succ')

lemma sum_ite_range (a n : ℕ) :
    ((List.range n).map fun v => if a = v then 1 else 0).sum = if a < n then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ', ih]
    by_cases h1 : a = n <;> by_cases h2 : a < n <;> simp [h1, h2] <;> omega

lemma sum_countP_range (f : Rec → ℕ) (n : ℕ) (L : List Rec) (h : ∀ r ∈ L, f r < n) :
    ((List.range n).map fun v => L.countP (fun r => f r == v)).sum = L.length := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have h' : ∀ r ∈ L, f r < n := fun r hr => h r (by simp [hr])
    have hx := h x (by simp)
    have e : ((List.range n).map fun v => (x :: L).countP (fun r => f r == v)) =
        (List.range n).map (fun v => L.countP (fun r => f r == v) + if f x = v then 1 else 0) := by
      apply List.map_congr_left; intro v _
      rw [List.countP_cons]
      simp [Nat.add_comm]
    have hadd : ∀ (l : List ℕ) (g1 g2 : ℕ → ℕ),
        (l.map fun i => g1 i + g2 i).sum = (l.map g1).sum + (l.map g2).sum := by
      intro l g1 g2
      induction l with
      | nil => simp
      | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega
    rw [e, hadd, ih h', sum_ite_range, if_pos hx]
    simp

lemma length_main_eq (main : List Bucket) :
    (main.flatMap Bucket.recs).length =
      ((List.range main.length).map fun v => (main.getD v []).recs.length).sum := by
  have : main = (List.range main.length).map (fun v => main.getD v []) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp [List.getD_eq_getElem?_getD, h1]
  conv_lhs => rw [this]
  rw [List.flatMap_map, List.length_flatMap]

lemma finish_tag (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → Nat) (routed : List Bucket)
    (leaves : List (List Rec)) : ∀ e ∈ (tpFinish rule g w routed leaves).trace,
      e.1 = .stash (g.k - 1) := by
  unfold tpFinish
  have : ∀ (L : List ℕ) (st : TPFin), (∀ e ∈ st.trace, e.1 = .stash (g.k - 1)) →
      ∀ e ∈ (L.foldl (fun st i => tpLastStep rule g w i st) st).trace,
        e.1 = .stash (g.k - 1) := by
    intro L
    induction L with
    | nil => intro st h; exact h
    | cons i L ih =>
      intro st h
      rw [List.foldl_cons]
      apply ih
      intro e he
      simp only [tpLastStep] at he
      obtain ⟨_, _, _, h1⟩ := tpOffer_facts g w (i + g.half) (tpOffer g w i
        { main := (st.main.set i (rule.split g.C (dirBit w (g.k - 1)) (st.main.getD i [])
              (st.main.getD (i + g.half) [])).1).set (i + g.half)
              (rule.split g.C (dirBit w (g.k - 1)) (st.main.getD i [])
              (st.main.getD (i + g.half) [])).2.1
          last := st.last ++ (rule.split g.C (dirBit w (g.k - 1)) (st.main.getD i [])
              (st.main.getD (i + g.half) [])).2.2
          leaves := st.leaves
          trace := st.trace ++ [(.stash (g.k - 1), (st.last ++
              (rule.split g.C (dirBit w (g.k - 1)) (st.main.getD i [])
              (st.main.getD (i + g.half) [])).2.2).length)] })
      obtain ⟨_, _, _, h2⟩ := tpOffer_facts g w i
        { main := (st.main.set i (rule.split g.C (dirBit w (g.k - 1)) (st.main.getD i [])
              (st.main.getD (i + g.half) [])).1).set (i + g.half)
              (rule.split g.C (dirBit w (g.k - 1)) (st.main.getD i [])
              (st.main.getD (i + g.half) [])).2.1
          last := st.last ++ (rule.split g.C (dirBit w (g.k - 1)) (st.main.getD i [])
              (st.main.getD (i + g.half) [])).2.2
          leaves := st.leaves
          trace := st.trace ++ [(.stash (g.k - 1), (st.last ++
              (rule.split g.C (dirBit w (g.k - 1)) (st.main.getD i [])
              (st.main.getD (i + g.half) [])).2.2).length)] }
      rw [h1, h2] at he
      rcases List.mem_append.mp he with he | he
      · exact h e he
      · simp only [List.mem_singleton] at he; rw [he]
  exact this _ _ (by simp)

/-- Every drain entry is at most the final target's occupancy. -/
lemma tpDrain_le (st : TPFin) : ∀ e ∈ (tpDrain st).2, e.2 ≤ occupied (tpDrain st).1 := by
  unfold tpDrain
  have : ∀ (L : List (List Rec)) (acc : List (Option Rec) × List (TPTest × ℕ)),
      (∀ e ∈ acc.2, e.2 ≤ occupied acc.1) →
      ∀ e ∈ (L.foldl tpDrainStep acc).2, e.2 ≤ occupied (L.foldl tpDrainStep acc).1 := by
    intro L
    induction L with
    | nil => intro acc h; exact h
    | cons a L ih =>
      intro acc h
      rw [List.foldl_cons]
      apply ih
      have hocc : occupied (appendFill acc.1 a) = occupied acc.1 + a.length :=
        RebuildBound.D6.occupied_appendFill _ _
      intro e he
      simp only [tpDrainStep, List.mem_append, List.mem_singleton] at he ⊢
      rcases he with he | he
      · have := h e he; omega
      · rw [he, hocc]
  exact this _ _ (by simp)

end RebuildBound.TP4Proof

open RebuildBound.Model RebuildBound.Spec RebuildBound.TP4Proof in
theorem RebuildBound.TP4b_of
    (h12 : RebuildBound.Spec.TP12_statement) : RebuildBound.Spec.TP4b_statement := by
  intro rule g unsh w inp ops hr hg hlanes hops hfail
  have hT12 := h12 rule g unsh w inp ops hr hg hlanes hops
  simp only at hT12
  obtain ⟨hperm, hmlen, _, _, hcount, _⟩ := hT12
  set run := tpReferenceWith rule g unsh w inp ops with hrun
  have htrace : run.trace = run.route.trace ++ (if g.dfs then tpDfsTrace g w run.pool else []) ++
      run.fin.trace ++ (tpDrain run.fin).2 := rfl
  have hout : run.output = { main := run.fin.main, tier := (tpDrain run.fin).1 } := rfl
  have hopsk : ∀ o ∈ ops, o.1 < g.k := fun o ho => by
    have := canonicalOps_lt g o (hops.1.subset ho); omega
  obtain ⟨hRP, _⟩ := runTPOps_routeP rule g w ops hopsk
    (tpRouteInit g (copyMain unsh inp.aMain)) (by simp [tpRouteInit]) (routeInit_routeP g _)
  have hRP' : RouteP run.route := hRP
  -- the failing entry is a drain entry
  obtain ⟨x, hx, hx1⟩ := Option.map_eq_some_iff.mp hfail
  have hxmem := List.mem_of_find?_eq_some hx
  have hxp := List.find?_some hx
  have hcap : g.capOf x.1 = g.drainPages * g.C := by rw [hx1]; rfl
  simp only [hcap, decide_eq_true_eq] at hxp
  rw [htrace] at hxmem
  have hxD : x ∈ (tpDrain run.fin).2 := by
    simp only [List.mem_append] at hxmem
    rcases hxmem with ((h | h) | h) | h
    · exfalso; obtain ⟨j, hj⟩ := hRP'.1 x h; rw [hx1] at hj; cases hj
    · exfalso
      split_ifs at h with hd
      · obtain ⟨d, _, c, _, rfl⟩ := mem_tpDfsTrace g w _ x h
        cases hx1
      · simp at h
    · exfalso; have := finish_tag rule g w _ _ x h; rw [hx1] at this; cases this
    · exact h
  have hle := tpDrain_le run.fin x hxD
  -- the final target holds the complete-home excess
  have hmain : run.output.main = run.fin.main := rfl
  have htier : run.output.tier = (tpDrain run.fin).1 := rfl
  rw [RebuildBound.D6.occupied_eq] at hle
  rw [← htier] at hle
  have hsurv : ∀ r ∈ inp.survivors unsh, tpHome g w r < g.T := by
    intro r _
    unfold tpHome
    exact Nat.mod_lt _ (by unfold TPGeom.T; positivity)
  have hsum := sum_countP_range (tpHome g w) g.T (inp.survivors unsh) hsurv
  have hlen := hperm.length_eq
  rw [List.length_append] at hlen
  have hmsum := length_main_eq run.output.main
  rw [hmlen] at hmsum
  have hmin : ((List.range g.T).map fun v => (run.output.main.getD v []).recs.length).sum =
      ((List.range g.T).map fun v => min (tpHomeCount g w (inp.survivors unsh) v) g.C).sum := by
    apply congrArg
    apply List.map_congr_left
    intro v hv
    exact hcount v (List.mem_range.mp hv)
  have hadd : ∀ (l : List ℕ) (g1 g2 : ℕ → ℕ),
      (l.map fun i => g1 i + g2 i).sum = (l.map g1).sum + (l.map g2).sum := by
    intro l g1 g2
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega
  have hexc : tpHomeExcess g unsh w inp + ((List.range g.T).map fun v =>
      min (tpHomeCount g w (inp.survivors unsh) v) g.C).sum =
      ((List.range g.T).map fun v => tpHomeCount g w (inp.survivors unsh) v).sum := by
    unfold tpHomeExcess
    rw [← hadd]
    congr 1
    apply List.map_congr_left
    intro v _
    omega
  unfold tpHomeCount at hexc
  have hsum' : ((List.range g.T).map fun v => (inp.survivors unsh).countP (fun r => tpHome g w r == v)).sum
      = (inp.survivors unsh).length := hsum
  have hocc : (run.output.tier.filterMap id).length + (run.output.main.flatMap Bucket.recs).length
      = (inp.survivors unsh).length := by omega
  unfold tpHomeCount at hmin
  omega
