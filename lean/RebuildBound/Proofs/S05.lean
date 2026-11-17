import Mathlib
import RebuildBound.Spec.SepT
import RebuildBound.Proofs.D1
import RebuildBound.Proofs.ListAux.Pairs
import RebuildBound.Proofs.RouteCore.Basic

/-!
# S05: ST0 and ST5 (the general-digit job and blindness)

ST0 is definitional. ST5: (1) the pairs of one stage touch disjoint buckets, so
each split reads only bit `j` of the records present (`CapRule.Valid.local_dir`);
(2) induction over the stages with the invariant "main has `N` buckets of `C`
lanes, holding only records of A's main"; (3) the radix tuples touch disjoint
buckets and each reads only the class of its records.
-/

namespace RebuildBound.S05

open RebuildBound.Model RebuildBound.Spec

/-! ### Stage operations -/

/-- The operations of stage `j` of the stage-by-stage schedule (for `j < k`). -/
def stageL (g : SepGeom) (j : Nat) : List (Nat × Nat) :=
  ((List.range g.N).filter fun i => !i.testBit j && decide (g.U ≤ i + 2 ^ j)).map fun i => (j, i)

theorem canon_filter (g : SepGeom) (p : Nat → Bool) :
    g.canonicalOps.filter (fun o => p o.1) =
      (List.range g.k).flatMap fun j => if p j = true then stageL g j else [] := by
  unfold SepGeom.canonicalOps
  rw [List.filter_flatMap]
  congr 1
  funext j
  by_cases h : p j = true
  · simp [stageL, List.filter_map, h]
  · simp [stageL, List.filter_map, h]

theorem flatMap_ite_lt (L : Nat → List (Nat × Nat)) (n : Nat) :
    ∀ m, ((List.range m).flatMap fun j => if decide (j < n) = true then L j else []) =
      (List.range (min m n)).flatMap L
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.flatMap_append]
    rw [flatMap_ite_lt L n m]
    by_cases h : m < n
    · have : min (m + 1) n = m + 1 := by omega
      have h2 : min m n = m := by omega
      rw [this, h2, List.range_succ, List.flatMap_append]; simp [h]
    · have : min (m + 1) n = n := by omega
      have h2 : min m n = n := by omega
      rw [this, h2]; simp [h]

theorem flatMap_ite_eq (L : Nat → List (Nat × Nat)) (n : Nat) :
    ∀ m, ((List.range m).flatMap fun j => if decide (j = n) = true then L j else []) =
      if n < m then L n else []
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_ite_eq L n m]
    by_cases h : m = n
    · subst h; simp
    · by_cases h2 : n < m
      · simp [h, h2, show n < m + 1 by omega]
      · simp [h, h2, show ¬ n < m + 1 by omega]

theorem sStageOps_eq (g : SepGeom) (j : Nat) :
    sStageOps g j = if j < g.k then stageL g j else [] := by
  unfold sStageOps
  have := canon_filter g (fun j' => decide (j' = j))
  rw [this, flatMap_ite_eq]

theorem routeUpTo_ops (g : SepGeom) (n : Nat) (hn : n ≤ g.k) :
    g.canonicalOps.filter (fun o => decide (o.1 < n)) =
      (List.range n).flatMap (stageL g) := by
  have := canon_filter g (fun j' => decide (j' < n))
  rw [this, flatMap_ite_lt, min_eq_right hn]

theorem mem_stageL {g : SepGeom} {j : Nat} {o : Nat × Nat} (h : o ∈ stageL g j) :
    o.1 = j ∧ o.2 < g.N ∧ o.2.testBit j = false := by
  unfold stageL at h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hi
  refine ⟨rfl, List.mem_range.1 h1, ?_⟩
  simpa using (by simpa using h2 : _ ∧ _).1

theorem nodup_stageL (g : SepGeom) (j : Nat) : ((stageL g j).map Prod.snd).Nodup := by
  unfold stageL
  rw [List.map_map]
  have : (Prod.snd ∘ fun i : Nat => ((j, i) : Nat × Nat)) = id := rfl
  rw [this, List.map_id]
  exact List.nodup_range.filter _

/-! ### Part 1: one stage -/

theorem run_eq (rule : CapRule) (hv : rule.Valid) (g : SepGeom) (w w' : Model.LogicalKey → Nat) (j : Nat)
    (st : SRoute)
    (hbits : ∀ B ∈ st.main, ∀ r ∈ B.recs, (w r.key).testBit j = (w' r.key).testBit j) :
    ∀ (I : List Nat), I.Nodup → (∀ i ∈ I, i.testBit j = false) → ∀ s : SRoute,
    (∀ i ∈ I, s.main.getD i [] = st.main.getD i [] ∧
      s.main.getD (i + 2 ^ j) [] = st.main.getD (i + 2 ^ j) []) →
    (I.foldl (fun s i => sPairStep rule g w j i s) s) =
      (I.foldl (fun s i => sPairStep rule g w' j i s) s) :=
  RouteCore.fold_eq_of_split hv (fun s => s.main) (fun i s => sPairStep rule g w j i s)
    (fun i s => sPairStep rule g w' j i s)
    (fun i s h => by unfold sPairStep; simp only [RouteCore.split] at h ⊢; rw [h])
    (fun _ s _ h1 h2 => RouteCore.core_getD_ne (rule := rule) (C := g.C) (s.main, s.stash) h1 h2)
    st.main hbits

/-- A stage list (all operations on bit `j`, distinct first indices with bit `j`
clear) depends only on bit `j` of the records present. -/
theorem stage_eq (rule : CapRule) (hv : rule.Valid) (g : SepGeom) (w w' : Model.LogicalKey → Nat) (j : Nat)
    (st : SRoute) (ops : List (Nat × Nat)) (hops : ∀ o ∈ ops, o.1 = j ∧ o.2.testBit j = false)
    (hnd : (ops.map Prod.snd).Nodup)
    (hbits : ∀ B ∈ st.main, ∀ r ∈ B.recs, (w r.key).testBit j = (w' r.key).testBit j) :
    runSOps rule g w ops st = runSOps rule g w' ops st := by
  have key : ∀ w'' : Model.LogicalKey → Nat, runSOps rule g w'' ops st =
      (ops.map Prod.snd).foldl (fun s i => sPairStep rule g w'' j i s) st := by
    intro w''
    unfold runSOps
    rw [List.foldl_map]
    apply foldl_congr_mem
    intro s o ho
    rw [(hops o ho).1]
  rw [key, key]
  apply run_eq rule hv g w w' j st hbits _ hnd
  · intro i hi
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hi
    exact (hops o ho).2
  · intros; exact ⟨rfl, rfl⟩
where
  foldl_congr_mem {α β : Type} (l : List β) (f f' : α → β → α) (a : α)
      (H : ∀ s, ∀ b ∈ l, f s b = f' s b) : l.foldl f a = l.foldl f' a :=
    List.foldl_ext f f' a H

theorem stageL_eq (rule : CapRule) (hv : rule.Valid) (g : SepGeom) (w w' : Model.LogicalKey → Nat) (j : Nat)
    (st : SRoute)
    (hbits : ∀ B ∈ st.main, ∀ r ∈ B.recs, (w r.key).testBit j = (w' r.key).testBit j) :
    runSOps rule g w (stageL g j) st = runSOps rule g w' (stageL g j) st :=
  stage_eq rule hv g w w' j st _ (fun o ho => ⟨(mem_stageL ho).1, (mem_stageL ho).2.2⟩)
    (nodup_stageL g j) hbits

theorem part1 : ∀ (rule : CapRule) (g : SepGeom) (w w' : Model.LogicalKey → Nat) (j : Nat) (st : SRoute),
    rule.Valid →
    (∀ B ∈ st.main, ∀ x ∈ B.recs, (w x.key).testBit j = (w' x.key).testBit j) →
    runSOps rule g w (sStageOps g j) st = runSOps rule g w' (sStageOps g j) st := by
  intro rule g w w' j st hv hbits
  rw [sStageOps_eq]
  split_ifs
  · exact stageL_eq rule hv g w w' j st hbits
  · rfl

/-! ### Part 2: the route -/

theorem N_eq (g : SepGeom) : g.N = g.d * g.U := by
  simp [SepGeom.N, SepGeom.d, SepGeom.U, SepGeom.k, pow_add]; ring

theorem add_pow_lt (g : SepGeom) {i j : Nat} (hj : j < g.k) (hi : i < g.N)
    (hb : i.testBit j = false) : i + 2 ^ j < g.N := by
  have hP : 0 < 2 ^ j := Nat.two_pow_pos j
  have hbt : i / 2 ^ j % 2 = 0 := by
    rw [Nat.testBit_eq_decide_div_mod_eq] at hb
    have := Nat.mod_two_eq_zero_or_one (i / 2 ^ j)
    simp at hb; omega
  obtain ⟨e, he⟩ : ∃ e, g.k = j + 1 + e := ⟨g.k - j - 1, by omega⟩
  have hpow : g.N = 2 ^ j * (2 * (g.r * 2 ^ e)) := by
    unfold SepGeom.N; rw [he, Nat.pow_add, Nat.pow_add]; ring
  generalize hX : g.r * 2 ^ e = X at hpow
  have hm : i / 2 ^ j < 2 * X := by
    rw [Nat.div_lt_iff_lt_mul hP]; rw [hpow] at hi; linarith
  have h1 : i < 2 ^ j * (i / 2 ^ j + 1) := by
    have := Nat.lt_mul_div_succ i hP; linarith
  have h2 : i / 2 ^ j + 2 ≤ 2 * X := by omega
  rw [hpow]
  calc i + 2 ^ j < 2 ^ j * (i / 2 ^ j + 1) + 2 ^ j := by omega
    _ = 2 ^ j * (i / 2 ^ j + 2) := by ring
    _ ≤ 2 ^ j * (2 * X) := Nat.mul_le_mul_left _ h2

structure Inv (g : SepGeom) (A : List Rec) (s : SRoute) : Prop where
  len : s.main.length = g.N
  lanes : ∀ B ∈ s.main, B.length = g.C
  recs : ∀ B ∈ s.main, ∀ r ∈ B.recs, r ∈ A

theorem Inv.step {rule : CapRule} (hv : rule.Valid) {g : SepGeom} {A : List Rec} {w : Model.LogicalKey → Nat}
    {j i : Nat} {s : SRoute} (h : Inv g A s) (_hi : i < g.N) (hi3 : i + 2 ^ j < g.N) :
    Inv g A (sPairStep rule g w j i s) := by
  have h' := RouteCore.coreMain_inv (rule := rule) (w := w) hv h.len h.lanes hi3 s.stash h.recs
  exact ⟨h'.1, h'.2.1, h'.2.2⟩

theorem Inv.stage {rule : CapRule} (hv : rule.Valid) {g : SepGeom} {A : List Rec} {w : Model.LogicalKey → Nat}
    {j : Nat} (hj : j < g.k) {s : SRoute} (h : Inv g A s) :
    Inv g A (runSOps rule g w (stageL g j) s) := by
  unfold runSOps
  have : ∀ (L : List (Nat × Nat)), (∀ o ∈ L, o.1 = j ∧ o.2 < g.N ∧ o.2.testBit j = false) →
      ∀ s, Inv g A s → Inv g A (L.foldl (fun s o => sPairStep rule g w o.1 o.2 s) s) := by
    intro L
    induction L with
    | nil => intro _ s hs; exact hs
    | cons o L ih =>
      intro hL s hs
      simp only [List.foldl_cons]
      apply ih (fun o' ho' => hL o' (List.mem_cons_of_mem _ ho'))
      obtain ⟨h1, h2, h3⟩ := hL o List.mem_cons_self
      rw [h1]
      exact Inv.step hv hs h2 (add_pow_lt g hj h2 h3)
  exact this _ (fun o ho => mem_stageL ho) s h

theorem Inv.init {g : SepGeom} {wOld w : Model.LogicalKey → Nat} {inp : SInputs} (hg : g.Valid)
    (hI : SInputShape g wOld w inp) :
    Inv g (inp.aMain.flatMap Bucket.recs) (sRouteInit g inp.aMain) where
  len := by
    have h2 := hg.2.1
    have : (g.d - 1) * g.U + g.U = g.d * g.U := by
      obtain ⟨d', hd'⟩ : ∃ d', g.d = d' + 1 := ⟨g.d - 1, by omega⟩
      rw [hd']; simp [Nat.add_mul]
    simp [sRouteInit, hI.aLen, N_eq]; omega
  lanes := by
    intro B hB
    simp only [sRouteInit, List.mem_append, List.mem_replicate] at hB
    rcases hB with hB | hB
    · rw [hB.2]; simp [Bucket.empty]
    · exact hI.aLanes B hB
  recs := by
    intro B hB r hr
    simp only [sRouteInit, List.mem_append, List.mem_replicate] at hB
    rcases hB with hB | hB
    · rw [hB.2] at hr; simp [Bucket.recs, Bucket.empty] at hr
    · exact List.mem_flatMap.2 ⟨B, hB, hr⟩

theorem sRouteUpTo_ops (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → Nat) (aMain : List Bucket)
    (n : Nat) (hn : n ≤ g.k) :
    sRouteUpTo rule g w aMain n =
      runSOps rule g w ((List.range n).flatMap (stageL g)) (sRouteInit g aMain) := by
  unfold sRouteUpTo
  rw [← routeUpTo_ops g n hn]

theorem sRouteUpTo_succ (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → Nat) (aMain : List Bucket)
    (n : Nat) (hn : n + 1 ≤ g.k) :
    sRouteUpTo rule g w aMain (n + 1) =
      runSOps rule g w (stageL g n) (sRouteUpTo rule g w aMain n) := by
  rw [sRouteUpTo_ops _ _ _ _ _ hn, sRouteUpTo_ops _ _ _ _ _ (by omega), List.range_succ,
    List.flatMap_append]
  unfold runSOps
  rw [List.foldl_append]
  simp

theorem part2 : ∀ (rule : CapRule) (g : SepGeom) (wOld w w' : Model.LogicalKey → Nat) (inp : SInputs) (n : Nat),
    rule.Valid → g.Valid → SInputShape g wOld w inp → n ≤ g.k →
    (∀ x ∈ inp.aMain.flatMap Bucket.recs, ∀ i < n, (w x.key).testBit i = (w' x.key).testBit i) →
    sRouteUpTo rule g w inp.aMain n = sRouteUpTo rule g w' inp.aMain n := by
  intro rule g wOld w w' inp n hv hg hI hn hkeys
  have : ∀ n, n ≤ g.k →
      (∀ x ∈ inp.aMain.flatMap Bucket.recs, ∀ i < n, (w x.key).testBit i = (w' x.key).testBit i) →
      Inv g (inp.aMain.flatMap Bucket.recs) (sRouteUpTo rule g w inp.aMain n) ∧
      sRouteUpTo rule g w inp.aMain n = sRouteUpTo rule g w' inp.aMain n := by
    intro n
    induction n with
    | zero =>
      intro _ _
      have h0 : sRouteUpTo rule g w inp.aMain 0 = sRouteInit g inp.aMain := by
        rw [sRouteUpTo_ops _ _ _ _ _ (by omega)]; rfl
      have h0' : sRouteUpTo rule g w' inp.aMain 0 = sRouteInit g inp.aMain := by
        rw [sRouteUpTo_ops _ _ _ _ _ (by omega)]; rfl
      rw [h0, h0']
      exact ⟨Inv.init hg hI, rfl⟩
    | succ n ih =>
      intro hn hk
      obtain ⟨ih1, ih2⟩ := ih (by omega) (fun x hx i hi => hk x hx i (by omega))
      rw [sRouteUpTo_succ _ _ _ _ _ hn, sRouteUpTo_succ _ _ _ _ _ hn, ← ih2]
      exact ⟨Inv.stage hv (by omega) ih1, stageL_eq rule hv g w w' n _ (fun B hB r hr =>
        hk r (ih1.recs B hB r hr) n (by omega))⟩
  exact (this n hn hkeys).2

/-! ### Part 3: the radix pass -/

theorem mem_recs_of_mem {B : Bucket} {x : Rec} (h : some x ∈ B) : x ∈ B.recs :=
  D1Lemmas.mem_recs.2 h

theorem pickClass_congr (cls cls' : Rec → Nat) :
    ∀ (S : List Rec) (n : Nat → Nat), (∀ x ∈ S, cls x = cls' x) →
      pickClass cls n S = pickClass cls' n S
  | [], n, _ => rfl
  | x :: S, n, h => by
    have hx : cls x = cls' x := h x List.mem_cons_self
    have ih : ∀ n, pickClass cls n S = pickClass cls' n S :=
      fun n => pickClass_congr cls cls' S n (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [pickClass, hx, ih]

theorem radixOutput_congr (cls cls' : Rec → Nat) (X : List Bucket)
    (hX : ∀ B ∈ X, ∀ x ∈ B.recs, cls x = cls' x) (a : Nat) :
    radixOutput cls X a = radixOutput cls' X a := by
  have hX' : ∀ i, ∀ x ∈ (X.getD i []).recs, cls x = cls' x := by
    intro i x hx
    rcases D5.recs_getD_sub X i with h | h
    · rw [h] at hx; simp at hx
    · exact hX _ h x hx
  unfold radixOutput
  have h0 : (X.getD a []).map (fun s => s.filter fun x => cls x == a) =
      (X.getD a []).map (fun s => s.filter fun x => cls' x == a) := by
    apply List.map_congr_left
    intro s hs
    cases s with
    | none => rfl
    | some x =>
      have := hX' a x (mem_recs_of_mem hs)
      simp [Option.filter, this]
  rw [h0]
  apply List.foldl_ext
  intro acc i _
  have hc : ((X.getD i []).recs.filter fun x => cls x == a) =
      ((X.getD i []).recs.filter fun x => cls' x == a) :=
    List.filter_congr (fun x hx => by simp [hX' i x hx])
  dsimp only
  simp only [hc]

theorem radixSplit_congr (cls cls' : Rec → Nat) (X : List Bucket)
    (hX : ∀ B ∈ X, ∀ x ∈ B.recs, cls x = cls' x) :
    radixSplit cls X = radixSplit cls' X := by
  have hX' : ∀ i, ∀ x ∈ (X.getD i []).recs, cls x = cls' x := by
    intro i x hx
    rcases D5.recs_getD_sub X i with h | h
    · rw [h] at hx; simp at hx
    · exact hX _ h x hx
  have hout : (List.range X.length).map (radixOutput cls X) =
      (List.range X.length).map (radixOutput cls' X) :=
    List.map_congr_left (fun a _ => radixOutput_congr cls cls' X hX a)
  have hshed : ∀ i n, pickClass cls n (X.getD i []).recs = pickClass cls' n (X.getD i []).recs :=
    fun i n => pickClass_congr cls cls' _ n (hX' i)
  unfold radixSplit
  simp only [hout, hshed]

theorem blk_pos (g : SepGeom) : 0 < g.blk := Nat.two_pow_pos _

theorem idx_mod (g : SepGeom) {a p : Nat} (hp : p < g.blk) : (a * g.blk + p) % g.blk = p := by
  rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hp

theorem fold_set_getD (q : Nat) :
    ∀ (L : List (Nat × Bucket)) (m : List Bucket), (∀ e ∈ L, e.1 ≠ q) →
      (L.foldl (fun m e => m.set e.1 e.2) m).getD q [] = m.getD q []
  | [], m, _ => rfl
  | e :: L, m, h => by
    simp only [List.foldl_cons]
    rw [fold_set_getD q L _ (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]
    exact D5.getD_set_ne _ (h e List.mem_cons_self) _

theorem radixStep_getD_ne (g : SepGeom) (w : Model.LogicalKey → Nat) (p : Nat) (s : SRoute) (q : Nat)
    (hq : ∀ a < g.r, q ≠ a * g.blk + p) :
    (radixStep g w p s).main.getD q [] = s.main.getD q [] := by
  unfold radixStep
  simp only
  apply fold_set_getD
  intro e he
  have := (List.of_mem_zip he).1
  obtain ⟨a, ha, hae⟩ := List.mem_map.1 this
  exact fun h => hq a (List.mem_range.1 ha) (h.symm.trans hae.symm)

theorem radixStep_congr (g : SepGeom) (w w' : Model.LogicalKey → Nat) (p : Nat) (s : SRoute)
    (h : ∀ a < g.r, ∀ x ∈ (s.main.getD (a * g.blk + p) []).recs,
      g.cls (w x.key) = g.cls (w' x.key)) :
    radixStep g w p s = radixStep g w' p s := by
  have hs : radixSplit (fun x => g.cls (w x.key))
      ((List.range g.r).map (fun a => a * g.blk + p) |>.map fun j => s.main.getD j []) =
      radixSplit (fun x => g.cls (w' x.key))
      ((List.range g.r).map (fun a => a * g.blk + p) |>.map fun j => s.main.getD j []) := by
    apply radixSplit_congr
    intro B hB x hx
    obtain ⟨_, ha, rfl⟩ := List.mem_map.1 hB
    obtain ⟨a, ha', rfl⟩ := List.mem_map.1 ha
    exact h a (List.mem_range.1 ha') x hx
  unfold radixStep
  simp only [hs]

theorem radix_fold (g : SepGeom) (w w' : Model.LogicalKey → Nat) :
    ∀ (P : List Nat) (s : SRoute), P.Nodup → (∀ p ∈ P, p < g.blk) →
      (∀ p ∈ P, ∀ a < g.r, ∀ x ∈ (s.main.getD (a * g.blk + p) []).recs,
        g.cls (w x.key) = g.cls (w' x.key)) →
      P.foldl (fun st p => radixStep g w p st) s = P.foldl (fun st p => radixStep g w' p st) s
  | [], s, _, _, _ => rfl
  | p :: P, s, hnd, hlt, h => by
    simp only [List.foldl_cons]
    rw [radixStep_congr g w w' p s (h p List.mem_cons_self)]
    apply radix_fold g w w' P
    · exact (List.nodup_cons.1 hnd).2
    · exact fun p' hp' => hlt p' (List.mem_cons_of_mem _ hp')
    · intro p' hp' a ha x hx
      have hne : p' ≠ p := fun e => (List.nodup_cons.1 hnd).1 (e ▸ hp')
      rw [radixStep_getD_ne g w' p s _ (by
        intro a' _ e
        apply hne
        have h1 := idx_mod g (a := a) (hlt p' (List.mem_cons_of_mem _ hp'))
        have h2 := idx_mod g (a := a') (hlt p List.mem_cons_self)
        rw [e] at h1; omega)] at hx
      exact h p' (List.mem_cons_of_mem _ hp') a ha x hx

theorem part3 : ∀ (g : SepGeom) (w w' : Model.LogicalKey → Nat) (st : SRoute),
    (∀ B ∈ st.main, ∀ x ∈ B.recs, g.cls (w x.key) = g.cls (w' x.key)) →
    radixPass g w st = radixPass g w' st := by
  intro g w w' st h
  unfold radixPass
  split_ifs
  · apply radix_fold g w w' _ st List.nodup_range (fun p hp => List.mem_range.1 hp)
    intro p _ a _ x hx
    rcases D5.recs_getD_sub st.main (a * g.blk + p) with h0 | h0
    · rw [h0] at hx; simp at hx
    · exact h _ h0 x hx
  · rfl

end RebuildBound.S05

theorem RebuildBound.ST0 : RebuildBound.Spec.ST0_statement := by
  intro rule g w inp ops out
  unfold RebuildBound.Model.sJobWith
  cases h : RebuildBound.Model.sFirstFailure g
      (RebuildBound.Model.sReferenceWith rule g w inp ops).trace with
  | some t => simp [h]
  | none => simp [h, eq_comm]

theorem RebuildBound.ST5 : RebuildBound.Spec.ST5_statement :=
  ⟨RebuildBound.S05.part1, RebuildBound.S05.part2, RebuildBound.S05.part3⟩
