import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import RebuildBound.Spec.TopPrepT
import RebuildBound.Proofs.ListAux.Route
import RebuildBound.Proofs.S12.Lists

/-!
# TP12 basics: the top preparation's geometry, `eraseFirst`, and list lemmas
-/

namespace RebuildBound.TP12

open RebuildBound.Model RebuildBound.D23 RebuildBound.S12

/-! ### Geometry -/

theorem half_pos (g : TPGeom) : 0 < g.half := Nat.two_pow_pos _

theorem T_eq (g : TPGeom) (hg : g.Valid) : g.T = 2 * g.half := by
  have hk := hg.1
  unfold TPGeom.T TPGeom.half
  obtain ⟨m, hm⟩ : ∃ m, g.k = m + 1 := ⟨g.k - 1, by omega⟩
  rw [hm, Nat.add_sub_cancel, Nat.pow_succ]; omega

theorem T_eq_pow (g : TPGeom) (hg : g.Valid) : g.T = 2 ^ (g.k - 1 + 1) := by
  have hk := hg.1
  unfold TPGeom.T
  congr 1; omega

theorem home_lt (g : TPGeom) (w : Model.LogicalKey → Nat) (r : Rec) : tpHome g w r < g.T :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

theorem range_lt (g : TPGeom) (hg : g.Valid) (w : Model.LogicalKey → Nat) (r : Rec) :
    tpRange g w r < g.ranges := by
  unfold tpRange TPGeom.ranges
  have h := home_lt g w r
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, hg.2.1]
  exact h

/-- Bits `0 … k - 2` of `x` agree with `i < half` and the last bit is `b`: the home. -/
theorem home_eq (g : TPGeom) (hg : g.Valid) (x : Nat) :
    x % g.T = x % g.half + g.half * (if x.testBit (g.k - 1) then 1 else 0) := by
  rw [T_eq_pow g hg, Nat.mod_pow_succ]
  unfold TPGeom.half
  have := Nat.testBit_eq_decide_div_mod_eq (x := x) (i := g.k - 1)
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ (g.k - 1)) with h | h
  · rw [h]; rw [this]; simp [h]
  · rw [h]; rw [this]; simp [h]

/-! ### `eraseFirst` -/

theorem eraseFirst_perm (p : Rec → Bool) :
    ∀ (n : Nat) (L : List Rec), List.Perm L (eraseFirst p n L ++ (L.filter p).take n)
  | 0, L => by simp [eraseFirst]
  | n + 1, [] => by simp [eraseFirst]
  | n + 1, x :: L => by
    by_cases hp : p x = true
    · have ih := eraseFirst_perm p n L
      simp only [eraseFirst, hp, ite_true, List.filter_cons_of_pos hp, List.take_succ_cons]
      exact (ih.cons x).trans List.perm_middle.symm
    · have ih := eraseFirst_perm p (n + 1) L
      have hp' : p x = false := by simpa using hp
      simp only [eraseFirst, hp', Bool.false_eq_true, ite_false, List.filter_cons_of_neg hp,
        List.cons_append]
      exact ih.cons x

theorem eraseFirst_sublist (p : Rec → Bool) :
    ∀ (n : Nat) (L : List Rec), List.Sublist (eraseFirst p n L) L
  | 0, L => by simp [eraseFirst]
  | n + 1, [] => by simp [eraseFirst]
  | n + 1, x :: L => by
    by_cases hp : p x = true
    · simp only [eraseFirst, hp, ite_true]
      exact (eraseFirst_sublist p n L).cons _
    · simp only [eraseFirst, hp, ite_false]
      exact (eraseFirst_sublist p (n + 1) L).cons₂ _

theorem eraseFirst_countP_ne (p q : Rec → Bool) (h : ∀ x, q x = true → p x = false)
    (n : Nat) (L : List Rec) : (eraseFirst p n L).countP q = L.countP q := by
  have h1 := (eraseFirst_perm p n L).countP_eq q
  rw [List.countP_append] at h1
  have h2 : ((L.filter p).take n).countP q = 0 := by
    rw [List.countP_eq_zero]
    intro a ha
    have := (List.mem_filter.1 ((List.take_subset _ _) ha)).2
    intro hq; rw [h a hq] at this; simp at this
  omega

theorem eraseFirst_countP_self (p : Rec → Bool) (n : Nat) (L : List Rec)
    (hn : n ≤ L.countP p) : (eraseFirst p n L).countP p = L.countP p - n := by
  have h1 := (eraseFirst_perm p n L).countP_eq p
  rw [List.countP_append] at h1
  have h2 : ((L.filter p).take n).countP p = n := by
    rw [List.countP_eq_length.2 (fun a ha => (List.mem_filter.1 ((List.take_subset _ _) ha)).2),
      List.length_take, ← List.countP_eq_length_filter]
    omega
  omega

theorem mem_eraseFirst (p : Rec → Bool) (n : Nat) (L : List Rec) {x : Rec}
    (h : x ∈ eraseFirst p n L) : x ∈ L := (eraseFirst_sublist p n L).subset h

/-! ### Lists -/

theorem getD_nil_of_ge {α : Type} (l : List (List α)) (i : Nat) (h : l.length ≤ i) :
    l.getD i [] = [] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem mem_flatten_getD {α : Type} (l : List (List α)) {x : α} (h : x ∈ l.flatten) :
    ∃ i < l.length, x ∈ l.getD i [] := by
  obtain ⟨L, hL, hx⟩ := List.mem_flatten.1 h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL
  exact ⟨i, hi, by rw [getD_eq_getElem' _ _ _ hi]; exact hx⟩

theorem mem_getD_flatten {α : Type} (l : List (List α)) (i : Nat) {x : α}
    (h : x ∈ l.getD i []) : x ∈ l.flatten := by
  by_cases hi : i < l.length
  · rw [getD_eq_getElem' _ _ _ hi] at h
    exact List.mem_flatten.2 ⟨_, List.getElem_mem hi, h⟩
  · rw [getD_nil_of_ge _ _ (by omega)] at h; simp at h

theorem flatMap_recs_mem {m : List Bucket} {r : Rec} (h : r ∈ m.flatMap Bucket.recs) :
    ∃ i < m.length, r ∈ (m.getD i []).recs := by
  obtain ⟨B, hB, hr⟩ := List.mem_flatMap.1 h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hB
  exact ⟨i, hi, by rw [getD_eq_getElem' _ _ _ hi]; exact hr⟩

theorem getD_recs_mem {m : List Bucket} {i : Nat} {r : Rec} (h : r ∈ (m.getD i []).recs) :
    r ∈ m.flatMap Bucket.recs := by
  by_cases hi : i < m.length
  · rw [getD_eq_getElem' _ _ _ hi] at h
    exact List.mem_flatMap.2 ⟨_, List.getElem_mem hi, h⟩
  · rw [getD_nil_of_ge _ _ (by omega)] at h; simp [Bucket.recs] at h

/-- Counting over a bucket list in which only two buckets can hold a counted record. -/
theorem countP_flatMap_two (q : Rec → Bool) (m : List Bucket) (i j : Nat) (hij : i ≠ j)
    (hi : i < m.length) (hj : j < m.length)
    (h0 : ∀ b < m.length, b ≠ i → b ≠ j → ∀ r ∈ (m.getD b []).recs, q r = false) :
    (m.flatMap Bucket.recs).countP q =
      (m.getD i []).recs.countP q + (m.getD j []).recs.countP q := by
  rw [flatMap_eq_range Bucket.recs [] m, List.countP_flatMap]
  rw [← List.sum_toFinset _ List.nodup_range]
  apply Finset.sum_eq_add_of_mem i j (by simpa using hi) (by simpa using hj) hij
  intro b hb hne
  exact List.countP_eq_zero.2 (fun r hr => by
    simp [h0 b (List.mem_range.1 (List.mem_toFinset.1 hb)) hne.1 hne.2 r hr])

end RebuildBound.TP12
