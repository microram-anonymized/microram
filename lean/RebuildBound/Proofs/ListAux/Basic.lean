import RebuildBound.Spec.T
import RebuildBound.Proofs.LaneDrain
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.Nat.Bitwise
import RebuildBound.Proofs.ListAux.GetD
import RebuildBound.Proofs.D1

/-!
# D23 basics: list, lane and `fill` lemmas

Generic facts about the model's lane primitives (`fill`, `appendFill`,
`Bucket.clear`), `List.set`/`List.getD`, and a `LawfulBEq` instance for the
derived `BEq Rec`, so that `List.count` on records is available.
-/

namespace RebuildBound.D23

open RebuildBound.Model

theorem rec_beq_iff (a b : Rec) : (a == b) = true ↔ a = b := by
  cases a; cases b
  show (RebuildBound.Model.instBEqRec.beq _ _) = true ↔ _
  simp [RebuildBound.Model.instBEqRec.beq]

instance : LawfulBEq Rec where
  eq_of_beq h := (rec_beq_iff _ _).1 h
  rfl := (rec_beq_iff _ _).2 rfl

/-! ### Free lanes and `fill` -/

/-- The number of free lanes. -/
def nfree {α : Type} (B : List (Option α)) : Nat := B.countP (·.isNone)

@[simp] theorem nfree_nil {α : Type} : nfree ([] : List (Option α)) = 0 := rfl
@[simp] theorem nfree_cons_some {α : Type} (r : α) (B : List (Option α)) :
    nfree (some r :: B) = nfree B := by simp [nfree]
@[simp] theorem nfree_cons_none {α : Type} (B : List (Option α)) :
    nfree (none :: B) = nfree B + 1 := by simp [nfree]

theorem fill_snd {α : Type} : ∀ (B : List (Option α)) (L : List α),
    (fill B L).2 = L.drop (min (nfree B) L.length)
  | [], L => by simp [fill]
  | some _ :: B, L => by simp [fill, fill_snd B L]
  | none :: _, [] => by simp [fill]
  | none :: B, _ :: L => by
    simp only [fill, fill_snd B L, nfree_cons_none, List.length_cons]
    rw [Nat.add_min_add_right, List.drop_succ_cons]

theorem fill_recs {α : Type} : ∀ (B : List (Option α)) (L : List α),
    List.Perm ((fill B L).1.filterMap id) (B.filterMap id ++ L.take (min (nfree B) L.length))
  | [], L => by simp [fill]
  | some r :: B, L => by
    simp only [fill, List.filterMap_cons, id, nfree_cons_some, List.cons_append]
    exact (fill_recs B L).cons r
  | none :: B, [] => by simp [fill]
  | none :: B, r :: L => by
    simp only [fill, List.filterMap_cons, id, nfree_cons_none, List.length_cons]
    rw [Nat.add_min_add_right, List.take_succ_cons]
    exact ((fill_recs B L).cons r).trans List.perm_middle.symm

theorem fill_nfree {α : Type} : ∀ (B : List (Option α)) (L : List α),
    nfree (fill B L).1 = nfree B - L.length
  | [], _ => by simp [fill]
  | some _ :: B, L => by simp [fill, fill_nfree B L]
  | none :: _, [] => by simp [fill]
  | none :: B, _ :: L => by
    simp only [fill, nfree_cons_some, fill_nfree B L, nfree_cons_none, List.length_cons]
    omega

theorem recs_length_add_nfree {α : Type} (B : List (Option α)) :
    (B.filterMap id).length + nfree B = B.length := by
  simpa only [List.length_filterMap_eq_countP, nfree, id, decide_not,
    Bool.decide_coe, Option.not_isSome] using
    (B.length_eq_countP_add_countP Option.isSome).symm

/-- The number of records `fill` places. -/
theorem fill_placed_le {α : Type} (B : List (Option α)) (L : List α) :
    min (nfree B) L.length ≤ L.length := Nat.min_le_right _ _

/-- A nonempty rest means no free lane is left. -/
theorem fill_full {α : Type} (B : List (Option α)) (L : List α) (h : (fill B L).2 ≠ []) :
    nfree (fill B L).1 = 0 := by
  rw [fill_nfree]
  rw [fill_snd] at h
  have : ¬ L.length ≤ min (nfree B) L.length := fun h' => h (List.drop_of_length_le h')
  omega

theorem appendFill_recs {α : Type} (B : List (Option α)) (L : List α) :
    List.Perm ((appendFill B L).filterMap id) (B.filterMap id ++ L) := by
  unfold appendFill
  rw [List.filterMap_append, List.filterMap_map]
  have : List.filterMap (id ∘ some) (fill B L).2 = (fill B L).2 := by
    simp
  rw [this, fill_snd]
  refine ((fill_recs B L).append_right _).trans ?_
  rw [List.append_assoc, List.take_append_drop]

/-! ### `Bucket.clear` and records -/

theorem clear_length (p : Model.LogicalKey → Bool) (B : Bucket) : (B.clear p).length = B.length := by
  simp [Bucket.clear]

/-! ### `List.set` and `List.getD` -/

theorem getD_set_self {α : Type} (l : List α) (i : Nat) (x d : α) (h : i < l.length) :
    (l.set i x).getD i d = x := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_eq_getElem' {α : Type} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_mem {α : Type} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    l.getD i d ∈ l := by
  rw [getD_eq_getElem' l i d h]; exact List.getElem_mem h

/-- Replacing one entry of a list, seen through `flatMap`. -/
theorem perm_flatMap_set {α β : Type} (f : α → List β) :
    ∀ (l : List α) (i : Nat) (x d : α), i < l.length →
      List.Perm ((l.set i x).flatMap f ++ f (l.getD i d)) (l.flatMap f ++ f x)
  | [], _, _, _, h => by simp at h
  | a :: l, 0, x, d, _ => by
    simp only [List.set_cons_zero, List.flatMap_cons, List.getD_cons_zero]
    have h1 : List.Perm (f x ++ l.flatMap f ++ f a) (f a ++ (f x ++ l.flatMap f)) :=
      List.perm_append_comm
    refine h1.trans ?_
    rw [List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm
  | a :: l, i + 1, x, d, h => by
    simp only [List.set_cons_succ, List.flatMap_cons, List.getD_cons_succ, List.append_assoc]
    exact List.Perm.append_left _ (perm_flatMap_set f l i x d (by simpa using h))

theorem sublist_flatMap_getD {α β : Type} (f : α → List β) (l : List α) (i : Nat) (d : α)
    (h : i < l.length) : List.Sublist (f (l.getD i d)) (l.flatMap f) := by
  exact List.sublist_flatten_of_mem (List.mem_map_of_mem (getD_mem l i d h))

end RebuildBound.D23
