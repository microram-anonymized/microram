import Mathlib
import RebuildBound.Proofs.LaneDrain
import RebuildBound.Spec.T
import RebuildBound.Proofs.ListAux.GetD
import RebuildBound.Proofs.D1

/-!
# D6: list helpers and the allocation primitives

Lemmas about `List.set`/`List.getD`, `fill`, `appendFill`, `Bucket.clear` and
lane counts, used by the schedule-independence proof (package D6).
-/

namespace RebuildBound.D6

open RebuildBound.Model

/-! ### `List.set` and `List.getD` -/

/-- Setting an entry to a function of itself, when the function fixes the
default. -/
theorem getD_set_self {α : Type*} (l : List α) (i : Nat) (d : α) (f : α → α)
    (hf : f d = d) : (l.set i (f (l.getD i d))).getD i d = f (l.getD i d) := by
  rw [getD_set_eq]
  by_cases h : i < l.length
  · simp [h]
  · simp only [h, and_false, ite_false]
    have : l.getD i d = d := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt h)]
    rw [this, hf]

theorem getD_mem {α : Type*} {l : List α} {i : Nat} {d : α} (h : i < l.length) :
    l.getD i d ∈ l := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- Two lists of equal length whose entries are related at every index are
`Forall₂`-related. -/
theorem forall₂_of_getD {α β : Type*} (P : α → β → Prop) (da : α) (db : β) :
    ∀ (l1 : List α) (l2 : List β), l1.length = l2.length →
      (∀ i, P (l1.getD i da) (l2.getD i db)) → List.Forall₂ P l1 l2
  := by
    intro l1 l2 hlen hP
    apply List.forall₂_of_length_eq_of_get hlen
    intro i h1 h2
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem h2, Option.getD_some, List.get_eq_getElem] using hP i

theorem map_eq_of_getD {α β : Type*} (f : α → β) (d : α) (l1 l2 : List α)
    (hlen : l1.length = l2.length) (h : ∀ i, f (l1.getD i d) = f (l2.getD i d)) :
    l1.map f = l2.map f := by
  simpa only [← List.forall₂_eq_eq_eq, List.forall₂_map_left_iff,
    List.forall₂_map_right_iff] using
      forall₂_of_getD (fun a b => f a = f b) d d l1 l2 hlen h

theorem flatten_perm_of_forall₂ {α : Type*} {l1 l2 : List (List α)}
    (h : List.Forall₂ List.Perm l1 l2) : l1.flatten.Perm l2.flatten := by
  exact List.Perm.flatten_congr h

/-! ### Append order (from D6/Route) -/

theorem perm_append_swap {α : Type*} (x y z : List α) : (x ++ y ++ z).Perm (x ++ z ++ y) := by
  rw [List.append_assoc, List.append_assoc]
  exact List.Perm.append_left _ List.perm_append_comm

/-! ### Lane counts and `fill` -/

/-- The number of free lanes. -/
def nNone {α : Type*} (B : List (Option α)) : Nat := B.countP (·.isNone)

@[simp] theorem nNone_nil {α : Type*} : nNone ([] : List (Option α)) = 0 := rfl

@[simp] theorem nNone_cons_some {α : Type*} (a : α) (B : List (Option α)) :
    nNone (some a :: B) = nNone B := by simp [nNone]

@[simp] theorem nNone_cons_none {α : Type*} (B : List (Option α)) :
    nNone (none :: B) = nNone B + 1 := by simp [nNone]

theorem occupied_eq {α : Type} (B : List (Option α)) : occupied B = (B.filterMap id).length := by
  exact List.length_filterMap_eq_countP.symm

/-- The four facts about `fill`: lane count, leftover, free lanes, records. -/
theorem fill_spec {α : Type} (B : List (Option α)) (L : List α) :
    (fill B L).1.length = B.length ∧
    (fill B L).2 = L.drop (min (nNone B) L.length) ∧
    nNone (fill B L).1 = nNone B - min (nNone B) L.length ∧
    ((fill B L).1.filterMap id).Perm (B.filterMap id ++ L.take (min (nNone B) L.length)) := by
  induction B generalizing L with
  | nil => simp [fill]
  | cons s B ih =>
    cases s with
    | some r =>
      obtain ⟨h1, h2, h3, h4⟩ := ih L
      refine ⟨by simp [fill, h1], by simp [fill, h2], by simp [fill, h3], ?_⟩
      simpa [fill] using h4
    | none =>
      cases L with
      | nil => simp [fill]
      | cons r L =>
        obtain ⟨h1, h2, h3, h4⟩ := ih L
        have hm : min (nNone B + 1) (L.length + 1) = min (nNone B) L.length + 1 := by omega
        refine ⟨by simp [fill, h1], ?_, ?_, ?_⟩
        · simp [fill, h2, hm]
        · simp [fill, h3, hm]
        · simp only [fill, nNone_cons_none, List.length_cons, hm, List.take_succ_cons,
            List.filterMap_cons, id]
          exact (h4.cons r).trans List.perm_middle.symm

theorem fill_snd {α : Type} (B : List (Option α)) (L : List α) :
    (fill B L).2 = L.drop (min (nNone B) L.length) := (fill_spec B L).2.1

theorem fill_nNone {α : Type} (B : List (Option α)) (L : List α) :
    nNone (fill B L).1 = nNone B - min (nNone B) L.length := (fill_spec B L).2.2.1

theorem fill_recs {α : Type} (B : List (Option α)) (L : List α) :
    ((fill B L).1.filterMap id).Perm (B.filterMap id ++ L.take (min (nNone B) L.length)) :=
  (fill_spec B L).2.2.2

theorem fill_snd_length {α : Type} (B : List (Option α)) (L : List α) :
    (fill B L).2.length = L.length - min (nNone B) L.length := by
  simp [fill_snd]

/-- A nonempty leftover means the filled bucket is full. -/
theorem fill_full {α : Type} (B : List (Option α)) (L : List α) (h : (fill B L).2 ≠ []) :
    nNone (fill B L).1 = 0 := by
  rw [fill_nNone]
  have : (fill B L).2.length ≠ 0 := by simpa using h
  rw [fill_snd_length] at this
  omega

theorem mem_fill_snd {α : Type} {B : List (Option α)} {L : List α} {x : α}
    (h : x ∈ (fill B L).2) : x ∈ L := by
  rw [fill_snd] at h
  exact List.mem_of_mem_drop h

/-- The number of records `fill` places. -/
theorem fill_placed {α : Type} (B : List (Option α)) (L : List α) :
    L.length - (fill B L).2.length = min (nNone B) L.length := by
  rw [fill_snd_length]; omega

theorem fill_nil {α : Type} (L : List α) : fill ([] : List (Option α)) L = ([], L) := by
  cases L <;> rfl

/-! ### `appendFill` -/

theorem appendFill_recs {α : Type} (t : List (Option α)) (L : List α) :
    ((appendFill t L).filterMap id).Perm (t.filterMap id ++ L) := by
  unfold appendFill
  rw [List.filterMap_append]
  have hmap : ((fill t L).2.map some).filterMap id = (fill t L).2 := by
    simp only [List.filterMap_map, Function.comp_def, id, List.filterMap_some]
  rw [hmap, fill_snd]
  have := (fill_recs t L).append_right (L.drop (min (nNone t) L.length))
  refine this.trans ?_
  rw [List.append_assoc, List.take_append_drop]

theorem occupied_appendFill {α : Type} (t : List (Option α)) (L : List α) :
    occupied (appendFill t L) = occupied t + L.length := by
  rw [occupied_eq, occupied_eq, (appendFill_recs t L).length_eq, List.length_append]

/-! ### `Option.filter` over lanes and `Bucket.clear` -/

theorem filterMap_map_filter {α : Type*} (p : α → Bool) (B : List (Option α)) :
    (B.map fun s => s.filter p).filterMap id = (B.filterMap id).filter p :=
  RebuildBound.LaneDrain.filterMap_map_filter p B

theorem nNone_map_filter {α : Type*} (p : α → Bool) (B : List (Option α)) :
    nNone (B.map fun s => s.filter p) = nNone B + (B.filterMap id).countP (fun a => !p a) := by
  induction B with
  | nil => rfl
  | cons s B ih =>
    cases s with
    | none => simp [ih]; omega
    | some a =>
      by_cases h : p a
      · simp [Option.filter_some, h, ih]
      · simp [Option.filter_some, h, ih]; omega

theorem nNone_clear (p : Model.LogicalKey → Bool) (B : Bucket) :
    nNone (B.clear p) = nNone B + B.recs.countP (fun r => p r.key) := by
  unfold Bucket.clear Bucket.recs
  rw [nNone_map_filter]
  simp

theorem clear_length (p : Model.LogicalKey → Bool) (B : Bucket) : (B.clear p).length = B.length := by
  simp [Bucket.clear]

theorem contains_iff {α : Type} [BEq α] [LawfulBEq α] {l : List α} {x : α} : l.contains x = true ↔ x ∈ l := by simp

end RebuildBound.D6
