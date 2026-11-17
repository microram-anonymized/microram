import Mathlib
import RebuildBound.Spec.TopPrepT
import RebuildBound.Proofs.ListAux.Pairs
import RebuildBound.Proofs.RouteCore.Basic

/-!
# TP5: blindness of the top preparation's route (TP5_step, TP5_route)

Adapted from D5: the pairs of one stage are disjoint, so each `tpPairStep`
reads buckets of the stage's start state, and `CapRule.Valid.local_dir` shows
the split depends on the words only through bit `j` of those records. For the
route, the invariant "main has `T` buckets of `C` lanes and holds only
records of A's main" is kept by every pair of a stage `j < k - 1`.
-/

namespace RebuildBound

open RebuildBound.Model RebuildBound.Spec

namespace TP5

theorem run_eq (rule : CapRule) (hv : rule.Valid) (g : TPGeom) (w w' : Model.LogicalKey → Nat) (j : Nat)
    (st : TPRoute)
    (hbits : ∀ B ∈ st.main, ∀ r ∈ B.recs, (w r.key).testBit j = (w' r.key).testBit j) :
    ∀ (I : List Nat), I.Nodup → (∀ i ∈ I, i.testBit j = false) → ∀ s : TPRoute,
    (∀ i ∈ I, s.main.getD i [] = st.main.getD i [] ∧
      s.main.getD (i + 2 ^ j) [] = st.main.getD (i + 2 ^ j) []) →
    (I.foldl (fun s i => tpPairStep rule g w j i s) s) =
      (I.foldl (fun s i => tpPairStep rule g w' j i s) s) :=
  RouteCore.fold_eq_of_split hv (fun s => s.main) (fun i s => tpPairStep rule g w j i s)
    (fun i s => tpPairStep rule g w' j i s)
    (fun i s h => by unfold tpPairStep; simp only [RouteCore.split] at h ⊢; rw [h])
    (fun _ s _ h1 h2 => RouteCore.core_getD_ne (rule := rule) (C := g.C) (s.main, s.stash) h1 h2)
    st.main hbits

theorem stageOps_foldl {α : Type} (g : TPGeom) (j : Nat) (f : α → Nat × Nat → α) (a : α) :
    (tpStageOps g j).foldl f a =
      ((List.range g.T).filter fun i => !i.testBit j).foldl (fun s i => f s (j, i)) a := by
  unfold tpStageOps; rw [List.foldl_map]

theorem stage_eq (rule : CapRule) (hv : rule.Valid) (g : TPGeom) (w w' : Model.LogicalKey → Nat) (j : Nat)
    (st : TPRoute)
    (hbits : ∀ B ∈ st.main, ∀ r ∈ B.recs, (w r.key).testBit j = (w' r.key).testBit j) :
    runTPOps rule g w (tpStageOps g j) st = runTPOps rule g w' (tpStageOps g j) st := by
  unfold runTPOps
  rw [stageOps_foldl, stageOps_foldl]
  apply run_eq rule hv g w w' j st hbits
  · exact (List.nodup_range).filter _
  · intro i hi; simpa using (List.mem_filter.1 hi).2
  · intros; exact ⟨rfl, rfl⟩

/-- The route invariant. -/
structure Inv (g : TPGeom) (A : List Rec) (s : TPRoute) : Prop where
  len : s.main.length = g.T
  lanes : ∀ B ∈ s.main, B.length = g.C
  recs : ∀ B ∈ s.main, ∀ r ∈ B.recs, r ∈ A

theorem Inv.step {rule : CapRule} (hv : rule.Valid) {g : TPGeom} {A : List Rec} {w : Model.LogicalKey → Nat}
    {j i : Nat} {s : TPRoute} (h : Inv g A s) (hj : j + 1 ≤ g.k) (hi : i < g.T)
    (hb : i.testBit j = false) : Inv g A (tpPairStep rule g w j i s) := by
  have hi3 : i + 2 ^ j < g.T := by
    obtain ⟨k', hk'⟩ : ∃ k', g.k = k' + 1 := ⟨g.k - 1, by omega⟩
    have : i < 2 ^ (k' + 1) := by simpa [TPGeom.T, hk'] using hi
    simpa [TPGeom.T, hk'] using D5.pow_add_lt (by omega) this hb
  have h' := RouteCore.coreMain_inv (rule := rule) (w := w) hv h.len h.lanes hi3 s.stash h.recs
  exact ⟨h'.1, h'.2.1, h'.2.2⟩

theorem Inv.run {rule : CapRule} (hv : rule.Valid) {g : TPGeom} {A : List Rec} {w : Model.LogicalKey → Nat}
    {j : Nat} (hj : j + 1 ≤ g.k) :
    ∀ (I : List Nat) (s : TPRoute), Inv g A s → (∀ i ∈ I, i < g.T ∧ i.testBit j = false) →
    Inv g A (I.foldl (fun s i => tpPairStep rule g w j i s) s)
  | [], s, h, _ => h
  | i :: I, s, h, hI => by
    simp only [List.foldl_cons]
    exact Inv.run hv hj I _ (Inv.step hv h hj (hI i List.mem_cons_self).1
      (hI i List.mem_cons_self).2) (fun i' hi' => hI i' (List.mem_cons_of_mem _ hi'))

theorem Inv.stage {rule : CapRule} (hv : rule.Valid) {g : TPGeom} {A : List Rec} {w : Model.LogicalKey → Nat}
    {j : Nat} (hj : j + 1 ≤ g.k) {s : TPRoute} (h : Inv g A s) :
    Inv g A (runTPOps rule g w (tpStageOps g j) s) := by
  unfold runTPOps
  rw [stageOps_foldl]
  apply Inv.run hv hj _ _ h
  intro i hi
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hi
  exact ⟨List.mem_range.1 h1, by simpa using h2⟩

theorem copyMain_recs_sub (unsh : Rec → Bool) (aMain : List Bucket) :
    ∀ B ∈ copyMain unsh aMain, ∀ r ∈ B.recs, r ∈ aMain.flatMap Bucket.recs := by
  intro B hB r hr
  simp only [copyMain, List.mem_map] at hB
  obtain ⟨B0, hB0, rfl⟩ := hB
  refine List.mem_flatMap.2 ⟨B0, hB0, ?_⟩
  simp only [Bucket.recs, List.mem_filterMap, List.mem_map, id] at hr ⊢
  obtain ⟨s, hs, hsr⟩ := hr
  obtain ⟨s0, hs0, rfl⟩ := hs
  cases s0 with
  | none => simp at hsr
  | some r0 =>
    simp only [Option.filter] at hsr
    split at hsr <;> simp_all

theorem filter_flatMap (F : Nat → List (Nat × Nat)) (hF : ∀ j, ∀ o ∈ F j, o.1 = j) (n : Nat) :
    ∀ m, ((List.range m).flatMap F).filter (fun o => decide (o.1 < n)) =
      (List.range (min n m)).flatMap F
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.flatMap_append, List.filter_append, filter_flatMap F hF n m]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    by_cases h : n ≤ m
    · have : (F m).filter (fun o => decide (o.1 < n)) = [] := by
        apply List.filter_eq_nil_iff.2
        intro o ho; have := hF m o ho; simp; omega
      rw [this, List.append_nil, Nat.min_eq_left h, Nat.min_eq_left (by omega)]
    · have : (F m).filter (fun o => decide (o.1 < n)) = F m := by
        apply List.filter_eq_self.2
        intro o ho; have := hF m o ho; simp; omega
      rw [this, Nat.min_eq_right (by omega), Nat.min_eq_right (by omega), List.range_succ,
        List.flatMap_append]
      simp

theorem upTo_succ (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (w : Model.LogicalKey → Nat)
    (aMain : List Bucket) (n : Nat) (hn : n + 1 ≤ g.k - 1) :
    tpRouteUpTo rule g unsh w aMain (n + 1) =
      runTPOps rule g w (tpStageOps g n) (tpRouteUpTo rule g unsh w aMain n) := by
  have hF : ∀ j, ∀ o ∈ (((List.range g.T).filter fun i => !i.testBit j).map fun i => (j, i)),
      o.1 = j := by
    intro j o ho; obtain ⟨i, _, rfl⟩ := List.mem_map.1 ho; rfl
  have key : ∀ n', n' ≤ g.k - 1 → g.canonicalOps.filter (fun o => o.1 < n') =
      (List.range n').flatMap fun j => ((List.range g.T).filter fun i => !i.testBit j).map
        fun i => (j, i) := by
    intro n' hn'
    unfold TPGeom.canonicalOps
    rw [filter_flatMap _ hF n' (g.k - 1), Nat.min_eq_left hn']
  unfold tpRouteUpTo runTPOps
  rw [key _ hn, key n (by omega), List.range_succ, List.flatMap_append, List.foldl_append]
  simp only [List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil, tpStageOps]

theorem routeUpTo_eq (rule : CapRule) (hv : rule.Valid) (g : TPGeom) (unsh : Rec → Bool)
    (w w' : Model.LogicalKey → Nat) (aMain : List Bucket) (hlen : aMain.length = g.T)
    (hl : ∀ B ∈ aMain, B.length = g.C)
    (N : Nat) (hkeys : ∀ r ∈ aMain.flatMap Bucket.recs, ∀ i < N, (w r.key).testBit i = (w' r.key).testBit i) :
    ∀ n, n ≤ N → n ≤ g.k - 1 →
      Inv g (aMain.flatMap Bucket.recs) (tpRouteUpTo rule g unsh w aMain n) ∧
      tpRouteUpTo rule g unsh w aMain n = tpRouteUpTo rule g unsh w' aMain n := by
  intro n
  induction n with
  | zero =>
    intros
    have h0 : Inv g (aMain.flatMap Bucket.recs) (tpRouteInit g (copyMain unsh aMain)) :=
      { len := by simp [tpRouteInit, copyMain, hlen]
        lanes := by
          intro B hB
          simp only [tpRouteInit, copyMain, List.mem_map] at hB
          obtain ⟨B0, hB0, rfl⟩ := hB
          simp [hl B0 hB0]
        recs := copyMain_recs_sub unsh aMain }
    have : g.canonicalOps.filter (fun o => decide (o.1 < 0)) = [] := by simp
    simp only [tpRouteUpTo, this, runTPOps, List.foldl_nil]
    exact ⟨h0, by trivial⟩
  | succ n ih =>
    intro hN hn
    obtain ⟨ih1, ih2⟩ := ih (by omega) (by omega)
    rw [upTo_succ _ _ _ _ _ _ hn, upTo_succ _ _ _ _ _ _ hn]
    refine ⟨Inv.stage hv (by omega) ih1, ?_⟩
    rw [← ih2]
    apply stage_eq rule hv
    intro B hB r hr
    exact hkeys r (ih1.recs B hB r hr) n (by omega)

end TP5

theorem TP5_step : RebuildBound.Spec.TP5_step_statement := by
  intro rule g w w' j st hv hbits
  exact TP5.stage_eq rule hv g w w' j st hbits

theorem TP5_route : RebuildBound.Spec.TP5_route_statement := by
  intro rule g unsh w w' aMain n hv hn hlen hl hkeys
  exact (TP5.routeUpTo_eq rule hv g unsh w w' aMain hlen hl n hkeys n le_rfl hn).2

end RebuildBound
