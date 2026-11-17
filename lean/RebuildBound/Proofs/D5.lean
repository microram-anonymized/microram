import Mathlib
import RebuildBound.Spec.T
import RebuildBound.Proofs.ListAux.Pairs
import RebuildBound.Proofs.RouteCore.Basic

/-!
# D5: blindness of the route (T5_step, T5_route)

Proof: the pairs of one stage are disjoint, so each `pairStep` reads buckets
of the stage's start state; `CapRule.Valid.local_dir` then shows the split
depends on the words only through bit `j` of the records of those buckets.
For the route, the invariant "main has `2U` buckets of `C` lanes and holds
only records of A's main" is kept by every pair of a stage `j ≤ k`.
-/

namespace RebuildBound

open RebuildBound.Model RebuildBound.Spec

namespace D5

/-- The core of T5_step, over an index list of one stage. -/
theorem run_eq (rule : CapRule) (hv : rule.Valid) (g : Geom) (w w' : Model.LogicalKey → Nat) (j : Nat)
    (st : RouteState)
    (hbits : ∀ B ∈ st.main, ∀ r ∈ B.recs, (w r.key).testBit j = (w' r.key).testBit j) :
    ∀ (I : List Nat), I.Nodup → (∀ i ∈ I, i.testBit j = false) → ∀ s : RouteState,
    (∀ i ∈ I, s.main.getD i [] = st.main.getD i [] ∧
      s.main.getD (i + 2 ^ j) [] = st.main.getD (i + 2 ^ j) []) →
    (I.foldl (fun s i => pairStep rule g w j i s) s) =
      (I.foldl (fun s i => pairStep rule g w' j i s) s) :=
  RouteCore.fold_eq_of_split hv (fun s => s.main) (fun i s => pairStep rule g w j i s)
    (fun i s => pairStep rule g w' j i s)
    (fun i s h => by unfold pairStep; simp only [RouteCore.split] at h ⊢; rw [h])
    (fun _ s _ h1 h2 => RouteCore.core_getD_ne (rule := rule) (C := g.C) (s.main, s.stash) h1 h2)
    st.main hbits

theorem stageOps_foldl {α : Type} (g : Geom) (j : Nat) (f : α → Nat × Nat → α) (a : α) :
    (stageOps g j).foldl f a =
      ((List.range g.homes).filter fun i => !i.testBit j).foldl (fun s i => f s (j, i)) a := by
  unfold stageOps; rw [List.foldl_map]

theorem stageStep_eq (rule : CapRule) (hv : rule.Valid) (g : Geom) (w w' : Model.LogicalKey → Nat) (j : Nat)
    (st : RouteState)
    (hbits : ∀ B ∈ st.main, ∀ r ∈ B.recs, (w r.key).testBit j = (w' r.key).testBit j) :
    stageStep rule g w j st = stageStep rule g w' j st := by
  unfold stageStep runOps
  rw [stageOps_foldl, stageOps_foldl]
  apply run_eq rule hv g w w' j st hbits
  · exact (List.nodup_range).filter _
  · intro i hi; simpa using (List.mem_filter.1 hi).2
  · intros; exact ⟨rfl, rfl⟩

end D5

theorem T5_step : RebuildBound.Spec.T5_step_statement := by
  intro rule g w w' j st hv hbits
  exact D5.stageStep_eq rule hv g w w' j st hbits

namespace D5

/-- The route invariant: `2U` buckets of `C` lanes, holding only records of `A`. -/
structure Inv (g : Geom) (A : List Rec) (s : RouteState) : Prop where
  len : s.main.length = 2 * g.U
  lanes : ∀ B ∈ s.main, B.length = g.C
  recs : ∀ B ∈ s.main, ∀ r ∈ B.recs, r ∈ A

theorem homes_eq (g : Geom) : g.homes = 2 * g.U := by
  simp [Geom.homes, Geom.U, Nat.pow_succ, Nat.mul_comm]

theorem Inv.step {rule : CapRule} (hv : rule.Valid) {g : Geom} {A : List Rec} {w : Model.LogicalKey → Nat}
    {j i : Nat} {s : RouteState} (h : Inv g A s) (hj : j ≤ g.k) (hi : i < g.homes)
    (hb : i.testBit j = false) : Inv g A (pairStep rule g w j i s) := by
  have hU : 2 * g.U = 2 ^ (g.k + 1) := by simp [Geom.U, Nat.pow_succ, Nat.mul_comm]
  have hi2 : i < 2 * g.U := by rw [← homes_eq]; exact hi
  have hi3 : i + 2 ^ j < 2 * g.U := by rw [hU]; exact pow_add_lt hj (by rw [← hU]; exact hi2) hb
  have h' := RouteCore.coreMain_inv (rule := rule) (w := w) hv h.len h.lanes hi3 s.stash h.recs
  exact ⟨h'.1, h'.2.1, h'.2.2⟩

theorem Inv.run {rule : CapRule} (hv : rule.Valid) {g : Geom} {A : List Rec} {w : Model.LogicalKey → Nat}
    {j : Nat} (hj : j ≤ g.k) :
    ∀ (I : List Nat) (s : RouteState), Inv g A s → (∀ i ∈ I, i < g.homes ∧ i.testBit j = false) →
    Inv g A (I.foldl (fun s i => pairStep rule g w j i s) s)
  | [], s, h, _ => h
  | i :: I, s, h, hI => by
    simp only [List.foldl_cons]
    exact Inv.run hv hj I _ (Inv.step hv h hj (hI i List.mem_cons_self).1
      (hI i List.mem_cons_self).2) (fun i' hi' => hI i' (List.mem_cons_of_mem _ hi'))

theorem Inv.stage {rule : CapRule} (hv : rule.Valid) {g : Geom} {A : List Rec} {w : Model.LogicalKey → Nat}
    {j : Nat} (hj : j ≤ g.k) {s : RouteState} (h : Inv g A s) :
    Inv g A (stageStep rule g w j s) := by
  unfold stageStep runOps
  rw [stageOps_foldl]
  apply Inv.run hv hj _ _ h
  intro i hi
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hi
  exact ⟨List.mem_range.1 h1, by simpa using h2⟩

theorem Inv.init {g : Geom} {TA TB : Nat} {wOld w : Model.LogicalKey → Nat} {inp : Inputs}
    (hI : InputValid g TA TB wOld w inp) :
    Inv g (inp.aMain.flatMap Bucket.recs) (routeInit g inp.aMain) where
  len := by simp [routeInit, hI.aLen]; omega
  lanes := by
    intro B hB
    simp only [routeInit, List.mem_append, List.mem_replicate] at hB
    rcases hB with hB | hB
    · rw [hB.2]; simp [Bucket.empty]
    · exact hI.aLanes B hB
  recs := by
    intro B hB r hr
    simp only [routeInit, List.mem_append, List.mem_replicate] at hB
    rcases hB with hB | hB
    · rw [hB.2] at hr; simp [Bucket.recs, Bucket.empty] at hr
    · exact List.mem_flatMap.2 ⟨B, hB, hr⟩

theorem routeUpTo_eq (rule : CapRule) (hv : rule.Valid) (g : Geom) (w w' : Model.LogicalKey → Nat)
    (A : List Rec) (aMain : List Bucket)
    (h0 : Inv g A (routeInit g aMain))
    (N : Nat) (hkeys : ∀ r ∈ A, ∀ i < N, (w r.key).testBit i = (w' r.key).testBit i) :
    ∀ n, n ≤ N → n ≤ g.stages →
      Inv g A (routeUpTo rule g w aMain n) ∧
      routeUpTo rule g w aMain n = routeUpTo rule g w' aMain n := by
  intro n
  induction n with
  | zero => intros; exact ⟨h0, rfl⟩
  | succ n ih =>
    intro hN hn
    obtain ⟨ih1, ih2⟩ := ih (by omega) (by omega)
    have hsplit : ∀ w'' : Model.LogicalKey → Nat, routeUpTo rule g w'' aMain (n + 1) =
        stageStep rule g w'' n (routeUpTo rule g w'' aMain n) := by
      intro w''
      unfold routeUpTo routeWith stageStep runOps
      rw [List.range_succ, List.flatMap_append, List.foldl_append]
      simp
    have hj : n ≤ g.k := by have : g.stages = g.k + 1 := rfl; omega
    refine ⟨?_, ?_⟩
    · rw [hsplit]; exact Inv.stage hv hj ih1
    · rw [hsplit, hsplit, ← ih2]
      apply stageStep_eq rule hv
      intro B hB r hr
      exact hkeys r (ih1.recs B hB r hr) n (by omega)

end D5

theorem T5_route : RebuildBound.Spec.T5_route_statement := by
  intro rule g TA TB wOld w w' inp n hv hI hn hkeys
  exact (D5.routeUpTo_eq rule hv g w w' _ inp.aMain (D5.Inv.init hI)
    n hkeys n le_rfl hn).2

end RebuildBound
