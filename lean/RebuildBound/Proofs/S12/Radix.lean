import RebuildBound.Proofs.S12.Lists
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# S12: the radix split

`radixSplit cls X` is a permutation of its inputs onto outputs and shed
(`radixSplit_perm`); output `a` keeps the lanes of input `a`
(`radixSplit_lanes`) and holds only class-`a` records (`radixSplit_cls`).
The proof is class by class: in class `c`, input `i` keeps the first `n_i`
records of the class (`pickClass_filter`) and output `c` takes exactly those
(`ro_fold`). Over inputs of `C` lanes the split sheds exactly
`(Σ_i (class-a records of input i) - C)₊` records of class `a`
(`radixSplit_countP`): output `a` fills `min (free lanes) (candidates)` lanes
(`racc_inv`).
-/

namespace RebuildBound.S12

open RebuildBound.Model RebuildBound.D23 RebuildBound.D1Lemmas

/-! ### `pickClass` -/

theorem pickClass_filter (cls : Rec → Nat) : ∀ (n : Nat → Nat) (S : List Rec) (c : Nat),
    (pickClass cls n S).1.filter (fun x => cls x == c) = (S.filter fun x => cls x == c).take (n c) ∧
    (pickClass cls n S).2.filter (fun x => cls x == c) = (S.filter fun x => cls x == c).drop (n c)
  | n, [], c => by simp [pickClass]
  | n, x :: S, c => by
    by_cases h0 : n (cls x) = 0
    · have ih := pickClass_filter cls n S c
      rw [pickClass, ite_eq_left h0]
      by_cases hc : cls x = c
      · subst hc
        rw [h0] at ih
        simp only [List.filter_cons, beq_self_eq_true, ite_true, h0, List.take_zero,
          List.drop_zero] at ih ⊢
        exact ⟨ih.1, by rw [ih.2]⟩
      · have hc' : (cls x == c) = false := by simpa using hc
        simp only [List.filter_cons, hc', Bool.false_eq_true, ite_false]
        exact ih
    · have ih := pickClass_filter cls (fun c => if c = cls x then n c - 1 else n c) S c
      rw [pickClass, ite_eq_right h0]
      by_cases hc : cls x = c
      · subst hc
        simp only [ite_true] at ih
        simp only [List.filter_cons, beq_self_eq_true, ite_true]
        obtain ⟨m, hm⟩ : ∃ m, n (cls x) = m + 1 := ⟨n (cls x) - 1, by omega⟩
        rw [hm, List.take_succ_cons, List.drop_succ_cons]
        rw [hm] at ih
        simp only [Nat.add_sub_cancel] at ih
        exact ⟨by rw [ih.1], ih.2⟩
      · have hc' : (cls x == c) = false := by simpa using hc
        have hc2 : (c = cls x) = False := by simp [Ne.symm hc]
        simp only [hc2, ite_false] at ih
        simp only [List.filter_cons, hc', Bool.false_eq_true, ite_false]
        exact ih

theorem pickClass_snd_sub (cls : Rec → Nat) : ∀ (n : Nat → Nat) (S : List Rec),
    ∀ x ∈ (pickClass cls n S).2, x ∈ S
  | n, [], x, h => by simp [pickClass] at h
  | n, y :: S, x, h => by
    unfold pickClass at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (pickClass_snd_sub cls n S x h)
    · exact List.mem_cons_of_mem _ (pickClass_snd_sub cls _ S x h)

/-! ### `radixOutput` -/

/-- One step of `radixOutput`'s fold. -/
def roStep (cls : Rec → Nat) (X : List Bucket) (a : Nat) (acc : Bucket × List Nat) (i : Nat) :
    Bucket × List Nat :=
  if i = a then (acc.1, acc.2 ++ [0])
  else
    let cand := (X.getD i []).recs.filter fun x => cls x == a
    let f := fill acc.1 cand
    (f.1, acc.2 ++ [cand.length - f.2.length])

/-- The initial bucket of output `a`: input `a`'s class-`a` records in their lanes. -/
def roInit (cls : Rec → Nat) (X : List Bucket) (a : Nat) : Bucket :=
  (X.getD a []).map fun s => s.filter fun x => cls x == a

theorem radixOutput_eq (cls : Rec → Nat) (X : List Bucket) (a : Nat) :
    radixOutput cls X a = (List.range X.length).foldl (roStep cls X a) (roInit cls X a, []) := rfl

/-- The class-`a` records of input `i`. -/
def candOf (cls : Rec → Nat) (X : List Bucket) (a i : Nat) : List Rec :=
  (X.getD i []).recs.filter fun x => cls x == a

theorem ro_fold (cls : Rec → Nat) (X : List Bucket) (a : Nat) : ∀ n : Nat,
    ((List.range n).foldl (roStep cls X a) (roInit cls X a, [])).2.length = n ∧
    ((List.range n).foldl (roStep cls X a) (roInit cls X a, [])).1.length = (X.getD a []).length ∧
    List.Perm ((List.range n).foldl (roStep cls X a) (roInit cls X a, [])).1.recs
      (candOf cls X a a ++ (List.range n).flatMap (fun i => if i = a then [] else
        (candOf cls X a i).take
          (((List.range n).foldl (roStep cls X a) (roInit cls X a, [])).2.getD i 0)))
  | 0 => by
    refine ⟨rfl, by simp [roInit], ?_⟩
    simp only [List.range_zero, List.foldl_nil, List.flatMap_nil, List.append_nil]
    rw [roInit, D1Lemmas.recs_map_filter]; rfl
  | n + 1 => by
    obtain ⟨h1, h2, h3⟩ := ro_fold cls X a n
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set o := (List.range n).foldl (roStep cls X a) (roInit cls X a, []) with ho
    have hcongr : ∀ (y : Nat), (List.range n).flatMap (fun i => if i = a then [] else
        (candOf cls X a i).take ((o.2 ++ [y]).getD i 0)) =
        (List.range n).flatMap (fun i => if i = a then [] else
        (candOf cls X a i).take (o.2.getD i 0)) := by
      intro y
      apply List.flatMap_congr
      intro i hi
      rw [List.getD_append _ _ _ _ (by rw [h1]; exact List.mem_range.1 hi)]
    unfold roStep
    by_cases hna : n = a
    · rw [ite_eq_left hna]
      refine ⟨by simp [h1], h2, ?_⟩
      simp only
      rw [List.flatMap_append, List.flatMap_singleton, ite_eq_left hna, List.append_nil, hcongr]
      exact h3
    · rw [ite_eq_right hna]
      simp only
      refine ⟨by simp [h1], by rw [D1Lemmas.fill_length, h2], ?_⟩
      rw [List.flatMap_append, List.flatMap_singleton, ite_eq_right hna, hcongr]
      have hg : (o.2 ++ [(candOf cls X a n).length - (fill o.1 (candOf cls X a n)).2.length]).getD n 0
          = min (nfree o.1) (candOf cls X a n).length := by
        rw [List.getD_append_right _ _ _ _ (by rw [h1]), h1, Nat.sub_self]
        simp only [List.getD_cons_zero]
        rw [fill_snd, List.length_drop]
        have := Nat.min_le_right (nfree o.1) (candOf cls X a n).length
        omega
      have hf := fill_recs o.1 (candOf cls X a n)
      unfold candOf at hg hf ⊢
      rw [hg]
      refine hf.trans ?_
      rw [← List.append_assoc]
      exact h3.append_right _

theorem radixOutput_spec (cls : Rec → Nat) (X : List Bucket) (a : Nat) :
    (radixOutput cls X a).2.length = X.length ∧
    (radixOutput cls X a).1.length = (X.getD a []).length ∧
    List.Perm (radixOutput cls X a).1.recs
      (candOf cls X a a ++ (List.range X.length).flatMap (fun i => if i = a then [] else
        (candOf cls X a i).take ((radixOutput cls X a).2.getD i 0))) := by
  rw [radixOutput_eq]; exact ro_fold cls X a X.length

theorem radixOutput_cls (cls : Rec → Nat) (X : List Bucket) (a : Nat) :
    ∀ x ∈ (radixOutput cls X a).1.recs, cls x = a := by
  intro x hx
  have := (radixOutput_spec cls X a).2.2.mem_iff.1 hx
  rcases List.mem_append.1 this with h | h
  · simpa using (List.mem_filter.1 h).2
  · obtain ⟨i, _, hi⟩ := List.mem_flatMap.1 h
    split at hi
    · simp at hi
    · simpa using (List.mem_filter.1 (List.mem_of_mem_take hi)).2

/-! ### `radixSplit` -/

theorem radixSplit_fst (cls : Rec → Nat) (X : List Bucket) :
    (radixSplit cls X).1 = (List.range X.length).map fun a => (radixOutput cls X a).1 := by
  simp [radixSplit, List.map_map, Function.comp_def]

theorem radixSplit_length (cls : Rec → Nat) (X : List Bucket) :
    (radixSplit cls X).1.length = X.length := by
  simp [radixSplit_fst]

theorem radixSplit_getD (cls : Rec → Nat) (X : List Bucket) {a : Nat} (ha : a < X.length) :
    (radixSplit cls X).1.getD a [] = (radixOutput cls X a).1 := by
  rw [radixSplit_fst]
  simp [List.getD_eq_getElem?_getD, ha]

theorem radixSplit_lanes (cls : Rec → Nat) (X : List Bucket) (C : Nat)
    (h : ∀ B ∈ X, B.length = C) : ∀ B ∈ (radixSplit cls X).1, B.length = C := by
  intro B hB
  rw [radixSplit_fst] at hB
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hB
  rw [(radixOutput_spec cls X a).2.1]
  exact h _ (getD_mem _ _ _ (List.mem_range.1 ha))

theorem radixSplit_cls (cls : Rec → Nat) (X : List Bucket) {a : Nat} (ha : a < X.length) :
    ∀ x ∈ ((radixSplit cls X).1.getD a []).recs, cls x = a := by
  rw [radixSplit_getD cls X ha]; exact radixOutput_cls cls X a

theorem count_filter_cls (cls : Rec → Nat) (L : List Rec) (y : Rec) :
    L.count y = (L.filter fun x => cls x == cls y).count y := by
  rw [List.count_filter]; simp

theorem perm_of_filter_cls (cls : Rec → Nat) {L L' : List Rec}
    (h : ∀ c, List.Perm (L.filter fun x => cls x == c) (L'.filter fun x => cls x == c)) :
    List.Perm L L' := by
  rw [List.perm_iff_count]; intro y
  rw [count_filter_cls cls L y, count_filter_cls cls L' y]
  exact (h (cls y)).count_eq y

theorem recs_length_le (B : Bucket) : B.recs.length ≤ B.length := by
  have := recs_length_add_nfree B
  unfold Bucket.recs; omega

theorem radixSplit_perm (cls : Rec → Nat) (X : List Bucket) :
    List.Perm ((radixSplit cls X).1.flatMap Bucket.recs ++ (radixSplit cls X).2)
      (X.flatMap Bucket.recs) := by
  apply perm_of_filter_cls cls
  intro c
  set R := X.length with hR
  -- the right side
  have hX : (X.flatMap Bucket.recs).filter (fun x => cls x == c) =
      (List.range R).flatMap (candOf cls X c) := by
    rw [flatMap_eq_range Bucket.recs [] X, List.filter_flatMap]; rfl
  -- the outputs
  have hO : ((radixSplit cls X).1.flatMap Bucket.recs).filter (fun x => cls x == c) =
      (List.range R).flatMap (fun a => if a = c then (radixOutput cls X c).1.recs else []) := by
    rw [radixSplit_fst, List.flatMap_map, List.filter_flatMap]
    apply List.flatMap_congr
    intro a _
    by_cases hac : a = c
    · subst hac
      rw [ite_eq_left rfl, List.filter_eq_self]
      intro x hx; simp [radixOutput_cls cls X a x hx]
    · rw [ite_eq_right hac, List.filter_eq_nil_iff]
      intro x hx; simp [radixOutput_cls cls X a x hx, hac]
  -- the shed
  have hS : (radixSplit cls X).2.filter (fun x => cls x == c) =
      (List.range R).flatMap (fun i => (candOf cls X c i).drop
        (if c = i then (X.getD i []).length else
          ((((List.range R).map (radixOutput cls X)).getD c ([], [])).2.getD i 0))) := by
    simp only [radixSplit, List.filter_flatMap]
    apply List.flatMap_congr
    intro i _
    exact (pickClass_filter cls _ _ c).2
  rw [List.filter_append, hO, hS, hX, range_flatMap_ite]
  by_cases hc : c < R
  · rw [ite_eq_left hc]
    have hout : ((List.range R).map (radixOutput cls X)).getD c ([], []) = radixOutput cls X c := by
      simp [List.getD_eq_getElem?_getD, hc]
    rw [hout]
    have e1 : (List.range R).flatMap (fun i => (candOf cls X c i).drop
        (if c = i then (X.getD i []).length else (radixOutput cls X c).2.getD i 0)) =
        (List.range R).flatMap (fun i => if i = c then [] else
          (candOf cls X c i).drop ((radixOutput cls X c).2.getD i 0)) := by
      apply List.flatMap_congr
      intro i _
      by_cases hic : i = c
      · subst hic
        rw [ite_eq_left rfl, ite_eq_left rfl]
        apply List.drop_of_length_le
        exact (List.length_filter_le _ _).trans (recs_length_le _)
      · rw [ite_eq_right (Ne.symm hic), ite_eq_right hic]
    rw [e1]
    have hsp := (radixOutput_spec cls X c).2.2
    rw [← hR] at hsp
    refine (hsp.append_right _).trans ?_
    rw [List.append_assoc]
    refine (List.Perm.append_left _ (range_flatMap_append _ _ R)).trans ?_
    have e2 : (List.range R).flatMap (fun i =>
        (if i = c then [] else (candOf cls X c i).take ((radixOutput cls X c).2.getD i 0)) ++
        (if i = c then [] else (candOf cls X c i).drop ((radixOutput cls X c).2.getD i 0))) =
        (List.range R).flatMap (fun i => if i = c then [] else candOf cls X c i) := by
      apply List.flatMap_congr
      intro i _
      by_cases hic : i = c
      · rw [ite_eq_left hic, ite_eq_left hic, ite_eq_left hic]; rfl
      · rw [ite_eq_right hic, ite_eq_right hic, ite_eq_right hic, List.take_append_drop]
    rw [e2]
    exact (range_flatMap_single _ R hc).symm
  · rw [ite_eq_right hc, List.nil_append]
    apply List.Perm.of_eq
    apply List.flatMap_congr
    intro i hi
    have hi' := List.mem_range.1 hi
    rw [ite_eq_right (show ¬ (c = i) by omega)]
    have : ((List.range R).map (radixOutput cls X)).getD c ([], []) = ([], []) := by
      simp [List.getD_eq_getElem?_getD, show ¬ c < R from hc]
    rw [this]
    simp

/-! ### Per-class shed counts -/

theorem pickClass_snd_countP (cls : Rec → Nat) (a : Nat) (S : List Rec) (n : Nat → Nat) :
    (pickClass cls n S).2.countP (fun x => cls x == a) = S.countP (fun x => cls x == a) - n a := by
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter, (pickClass_filter cls n S a).2,
    List.length_drop]

theorem radixSplit_mem (cls : Rec → Nat) (X : List Bucket) {x : Rec}
    (hx : x ∈ (radixSplit cls X).2) : ∃ i < X.length, x ∈ (X.getD i []).recs := by
  unfold radixSplit at hx
  obtain ⟨i, hi, hx⟩ := List.mem_flatMap.1 hx
  exact ⟨i, List.mem_range.1 hi, pickClass_snd_sub cls _ _ x hx⟩

theorem list_sum_range (f : Nat → Nat) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := rfl

/-- Output `a`'s state after inputs `0, …, m - 1`. -/
def racc (cls : Rec → Nat) (X : List Bucket) (a m : Nat) : Bucket × List Nat :=
  (List.range m).foldl (roStep cls X a) (roInit cls X a, [])

/-- The class-`a` candidates of input `i`, none for `i = a`. -/
def cnd (cls : Rec → Nat) (X : List Bucket) (a i : Nat) : Nat :=
  if i = a then 0 else (candOf cls X a i).length

theorem racc_inv (cls : Rec → Nat) (X : List Bucket) (a : Nat) : ∀ m,
    (racc cls X a m).2.length = m ∧
    nfree (racc cls X a m).1 = nfree (roInit cls X a) -
      min (nfree (roInit cls X a)) (∑ i ∈ Finset.range m, cnd cls X a i) ∧
    ∑ i ∈ Finset.range m, (racc cls X a m).2.getD i 0 =
      min (nfree (roInit cls X a)) (∑ i ∈ Finset.range m, cnd cls X a i) ∧
    ∀ i < m, (racc cls X a m).2.getD i 0 ≤ cnd cls X a i
  | 0 => by simp [racc]
  | m + 1 => by
    obtain ⟨h1, h2, h3, h4⟩ := racc_inv cls X a m
    have hstep : racc cls X a (m + 1) = roStep cls X a (racc cls X a m) m := by
      unfold racc; rw [List.range_succ, List.foldl_append]; rfl
    rw [hstep]
    set acc := racc cls X a m
    have hget : ∀ (x : Nat), ∀ i < m, (acc.2 ++ [x]).getD i 0 = acc.2.getD i 0 :=
      fun x i hi => List.getD_append _ _ _ _ (by omega)
    have hlast : ∀ (x : Nat), (acc.2 ++ [x]).getD m 0 = x := by
      intro x; rw [List.getD_append_right _ _ _ _ (by omega), h1, Nat.sub_self]; rfl
    have hsum : ∀ x : Nat, ∑ i ∈ Finset.range (m + 1), (acc.2 ++ [x]).getD i 0 =
        ∑ i ∈ Finset.range m, acc.2.getD i 0 + x := by
      intro x
      rw [Finset.sum_range_succ, hlast]
      congr 1
      exact Finset.sum_congr rfl fun i hi => hget x i (Finset.mem_range.1 hi)
    rw [Finset.sum_range_succ]
    unfold roStep
    by_cases hm : m = a
    · subst hm
      have hc : cnd cls X m m = 0 := by simp [cnd]
      simp only [ite_true, hc, Nat.add_zero]
      refine ⟨by simp [h1], h2, ?_, ?_⟩
      · rw [hsum, h3, Nat.add_zero]
      · intro i hi
        by_cases him : i < m
        · rw [hget 0 i him]; exact h4 i him
        · have : i = m := by omega
          rw [this, hlast, hc]
    · simp only [hm, ite_false]
      have hc : cnd cls X a m = (candOf cls X a m).length := by simp [cnd, hm]
      have hpl : (candOf cls X a m).length - (fill acc.1 (candOf cls X a m)).2.length =
          min (nfree acc.1) (candOf cls X a m).length := by
        rw [fill_snd, List.length_drop]; omega
      have hnn := fill_nfree acc.1 (candOf cls X a m)
      unfold candOf at hc hpl hnn
      rw [hc]
      refine ⟨by simp [h1], ?_, ?_, ?_⟩
      · rw [hnn, h2]; omega
      · rw [hsum, h3, hpl, h2]; omega
      · intro i hi
        by_cases him : i < m
        · rw [hget _ i him]; exact h4 i him
        · have : i = m := by omega
          rw [this, hlast, hc, hpl]; exact min_le_right _ _

/-- One radix split over inputs of `C` lanes sheds `(Σ_i (class-a records of input i) - C)₊`
records of class `a`. -/
theorem radixSplit_countP (cls : Rec → Nat) (X : List Bucket) (C : Nat)
    (hX : ∀ B ∈ X, B.length = C) {a : Nat} (ha : a < X.length) :
    (radixSplit cls X).2.countP (fun x => cls x == a) =
      (∑ i ∈ Finset.range X.length, (X.getD i []).recs.countP (fun x => cls x == a)) - C := by
  have hXa : (X.getD a []).length = C := hX _ (getD_mem _ _ _ ha)
  have houts : ((List.range X.length).map (radixOutput cls X)).getD a ([], []) =
      racc cls X a X.length := by
    rw [List.getD_eq_getElem _ _ (by simpa using ha), List.getElem_map, List.getElem_range]
    rfl
  unfold radixSplit
  rw [List.countP_flatMap, list_sum_range]
  set cnt : Nat → Nat := fun i => (X.getD i []).recs.countP (fun x => cls x == a)
  set pl : Nat → Nat := fun i => (racc cls X a X.length).2.getD i 0
  obtain ⟨_, _, hsum, hle⟩ := racc_inv cls X a X.length
  have hterm : ∀ i ∈ Finset.range X.length,
      (List.countP (fun x => cls x == a) ∘ fun i =>
        (pickClass cls (fun a' => if a' = i then (X.getD i []).length else
          (((List.range X.length).map (radixOutput cls X)).getD a' ([], [])).2.getD i 0)
          (X.getD i []).recs).2) i = cnd cls X a i - pl i := by
    intro i hi
    simp only [Function.comp]
    rw [pickClass_snd_countP]
    by_cases hia : a = i
    · subst hia
      have h1 : cnd cls X a a = 0 := by simp [cnd]
      simp only [ite_true, h1, Nat.zero_sub]
      have := (List.countP_le_length (p := fun x => cls x == a) (l := (X.getD a []).recs)).trans
        (recs_length_le _)
      omega
    · simp only [hia, ite_false, houts]
      have h1 : cnd cls X a i = cnt i := by
        simp [cnd, Ne.symm hia, cnt, candOf, List.countP_eq_length_filter]
      rw [h1]
  rw [Finset.sum_congr rfl hterm, Finset.sum_tsub_distrib _ (fun i hi =>
    hle i (Finset.mem_range.1 hi)), hsum]
  -- the free lanes of output `a` and the class-`a` total
  have hF : nfree (roInit cls X a) + cnt a = C := by
    have := recs_length_add_nfree (roInit cls X a)
    unfold roInit at this ⊢
    rw [← Bucket.recs, recs_map_filter, List.length_map, hXa, ← List.countP_eq_length_filter]
      at this
    rw [Nat.add_comm]; exact this
  have htot : ∑ i ∈ Finset.range X.length, cnt i =
      cnt a + ∑ i ∈ Finset.range X.length, cnd cls X a i := by
    have : ∀ i ∈ Finset.range X.length, cnt i = (if a = i then cnt a else 0) + cnd cls X a i := by
      intro i _
      by_cases hia : a = i
      · subst hia; simp [cnd]
      · simp [hia, cnd, Ne.symm hia, cnt, candOf, List.countP_eq_length_filter]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq,
      ite_eq_left (Finset.mem_range.2 ha)]
  rw [htot]
  omega

end RebuildBound.S12
