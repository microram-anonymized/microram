import Mathlib
import RebuildBound.Proofs.D1
import RebuildBound.Proofs.ListAux.Pairs

/-!
# ListAux: bucket, `fill` and `getD` lemmas (from D4b)

Keys, `fill` and `List.set`/`getD` facts on buckets, the subpermutation
helpers and `not_mem_keys_clear`. Moved from the binary d = 2 chain
(`D4b.Basic`, `D4b.Route`, `D4b.Offers`, `D4b.Finish`); namespace
`RebuildBound.D4b` kept.
-/

namespace RebuildBound.D4b
open RebuildBound.Model
theorem nodup_of_subperm {α : Type} {l₁ l₂ : List α} (h : l₁.Subperm l₂) (hn : l₂.Nodup) :
    l₁.Nodup := by
  obtain ⟨l, hp, hs⟩ := h
  exact hp.nodup_iff.mp (hn.sublist hs)

theorem getD_set_self {α : Type} (l : List α) {i : Nat} (h : i < l.length) (x d : α) :
    (l.set i x).getD i d = x := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_set_of_ne {α : Type} (l : List α) {i j : Nat} (h : i ≠ j) (x d : α) :
    (l.set i x).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_sublist_flatten {α : Type} (l : List (List α)) (i : Nat) :
    List.Sublist (l.getD i []) l.flatten := by
  by_cases h : i < l.length
  · rw [List.getD_eq_getElem _ _ h]; exact List.sublist_flatten_of_mem (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]; exact List.nil_sublist _

theorem mem_flatten_getD {α : Type} {l : List (List α)} {r : α} (h : r ∈ l.flatten) :
    ∃ i, r ∈ l.getD i [] := by
  obtain ⟨m, hm, hr⟩ := List.mem_flatten.1 h
  obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 hm
  exact ⟨i, by rw [List.getD_eq_getElem _ _ hi, e]; exact hr⟩

theorem flatten_set_sublist {α : Type} : ∀ (l : List (List α)) (i : Nat) (x : List α),
    List.Sublist x (l.getD i []) → List.Sublist (l.set i x).flatten l.flatten
  | [], _, _, _ => by simp
  | y :: l, 0, x, h => by
    simp only [List.set_cons_zero, List.flatten_cons]
    simp only [List.getD_cons_zero] at h
    exact h.append (List.Sublist.refl _)
  | y :: l, i + 1, x, h => by
    simp only [List.set_cons_succ, List.flatten_cons]
    simp only [List.getD_cons_succ] at h
    exact (List.Sublist.refl y).append (flatten_set_sublist l i x h)

theorem fill_snd {α : Type} : ∀ (B : List (Option α)) (L : List α),
    (fill B L).2 = L.drop (min L.length (B.countP (·.isNone)))
  | [], L => by simp [fill]
  | some r :: B, L => by simp [fill, fill_snd B L]
  | none :: B, [] => by simp [fill]
  | none :: B, a :: L => by
    simp only [fill, fill_snd B L, List.length_cons]
    simp [Nat.add_min_add_right]

theorem fill_some {α : Type} : ∀ (B : List (Option α)) (L : List α),
    (fill B L).1.countP (·.isSome) = B.countP (·.isSome) + min L.length (B.countP (·.isNone))
  | [], L => by simp [fill]
  | some r :: B, L => by simp [fill, fill_some B L]; omega
  | none :: B, [] => by simp [fill]
  | none :: B, a :: L => by
    simp only [fill, List.countP_cons, fill_some B L, List.length_cons]
    simp [Nat.add_min_add_right]; omega

theorem fill_filterMap {α : Type} : ∀ (B : List (Option α)) (L : List α),
    ((fill B L).1.filterMap id).Perm
      (B.filterMap id ++ L.take (min L.length (B.countP (·.isNone))))
  | [], L => by simp [fill]
  | some r :: B, L => by
    simp only [fill, List.filterMap_cons, id, List.countP_cons]
    simpa using (fill_filterMap B L).cons r
  | none :: B, [] => by simp [fill]
  | none :: B, a :: L => by
    simp only [fill, List.filterMap_cons, id, List.countP_cons, List.length_cons]
    simp only [Option.isNone_none, ite_true, Nat.add_min_add_right, List.take_succ_cons]
    exact ((fill_filterMap B L).cons a).trans List.perm_middle.symm

theorem fill_of_full {α : Type} : ∀ (B : List (Option α)) (L : List α),
    B.countP (·.isNone) = 0 → fill B L = (B, L)
  | [], L, _ => by simp [fill]
  | some r :: B, L, h => by
    simp only [List.countP_cons, Option.isNone_some] at h
    simp [fill, fill_of_full B L (by simpa using h)]
  | none :: B, _, h => by simp at h

theorem countP_none_add_some {α : Type} (B : List (Option α)) :
    B.countP (·.isNone) + B.countP (·.isSome) = B.length := by
  simpa only [decide_not, Bool.decide_eq_true, Option.not_isNone] using
    (B.length_eq_countP_add_countP (·.isNone)).symm

theorem fill_recs_perm (B : Bucket) (L : List Rec) :
    (Bucket.recs (fill B L).1).Perm (B.recs ++ L.take (min L.length (B.countP (·.isNone)))) :=
  fill_filterMap B L

/-- A bucket with every lane occupied has no free lane. -/
theorem free_zero_of_full (B : Bucket) (h : B.recs.length = B.length) :
    B.countP (·.isNone) = 0 := by
  have := D1Lemmas.countP_isNone_add B
  omega

theorem keys_eq (B : Bucket) : B.keys = B.recs.map Rec.key := rfl

theorem mem_keys {B : Bucket} {x : Model.LogicalKey} : x ∈ B.keys ↔ ∃ r ∈ B.recs, r.key = x := by
  simp [Bucket.keys]

theorem countP_lt_succ {α : Type} (f : α → Nat) (n : Nat) : ∀ L : List α,
    L.countP (fun x => decide (f x < n + 1)) =
      L.countP (fun x => decide (f x < n)) + L.countP (fun x => f x == n)
  | [] => by simp
  | a :: L => by
    have ih := countP_lt_succ f n L
    simp only [List.countP_cons, ih]
    by_cases h1 : f a < n
    · have h3 : f a ≠ n := by omega
      simp [h1, h3, show f a < n + 1 by omega]; omega
    · by_cases h3 : f a = n
      · simp [h3]; omega
      · simp [h1, h3, show ¬ f a < n + 1 by omega]

theorem sum_countP_eq {α : Type} (f : α → Nat) (L : List α) : ∀ n,
    ((List.range n).map fun v => L.countP fun x => f x == v).sum =
      L.countP fun x => decide (f x < n)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_countP_eq f L n,
      countP_lt_succ]
    simp

variable (g : Geom) (w : Model.LogicalKey → Nat) (inp : Inputs)
variable {g w inp}
end RebuildBound.D4b

namespace RebuildBound.D4b
open RebuildBound.Model
theorem subperm_map {α β : Type} (f : α → β) {l₁ l₂ : List α} (h : l₁.Subperm l₂) :
    (l₁.map f).Subperm (l₂.map f) := by
  obtain ⟨l, hp, hs⟩ := h
  exact ⟨l.map f, hp.map f, hs.map f⟩

theorem recs_sublist_flatMap {l : List Bucket} {B : Bucket} (h : B ∈ l) :
    List.Sublist B.recs (l.flatMap Bucket.recs) := by
  rw [List.flatMap_def]
  exact List.sublist_flatten_of_mem (List.mem_map.2 ⟨B, h, rfl⟩)

end RebuildBound.D4b

namespace RebuildBound.D4b
open RebuildBound.Model
theorem mem_getD_set_self' {α : Type} {l : List (List α)} {R : Nat} {x : List α} {r : α}
    (h : r ∈ (l.set R x).getD R []) : r ∈ x := by
  by_cases hR : R < l.length
  · rwa [getD_set_self _ hR] at h
  · rw [List.set_eq_of_length_le (by omega), List.getD_eq_default _ _ (by omega)] at h
    simp at h

theorem mem_getD_set' {α : Type} {l : List (List α)} {R R' : Nat} {x : List α} {r : α}
    (h : r ∈ (l.set R x).getD R' []) : (R' = R ∧ r ∈ x) ∨ r ∈ l.getD R' [] := by
  by_cases e : R' = R
  · subst e; exact Or.inl ⟨rfl, mem_getD_set_self' h⟩
  · rw [getD_set_of_ne _ (Ne.symm e)] at h; exact Or.inr h

section
variable {g : Geom} {w : Model.LogicalKey → Nat} {inp : Inputs}
theorem fill_placed_eq (B : Bucket) (L : List Rec) :
    L.take (L.length - (fill B L).2.length) = L.take (min L.length (B.countP (·.isNone))) := by
  rw [fill_snd, List.length_drop]
  congr 1
  have := Nat.min_le_left L.length (B.countP (·.isNone))
  omega

theorem length_filter_split {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter fun a => !p a).length = l.length := by
  exact (List.length_eq_length_filter_add p).symm

end
end RebuildBound.D4b

namespace RebuildBound.D4b
open RebuildBound.Model
theorem not_mem_keys_clear {B : Bucket} {p : Model.LogicalKey → Bool} {x : Model.LogicalKey} (hx : p x = true) :
    x ∉ (B.clear p).keys := by
  intro hk
  rw [keys_eq, D1Lemmas.clear_recs] at hk
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hk
  have := (List.mem_filter.1 hr).2
  rw [hx] at this
  simp at this

end RebuildBound.D4b
