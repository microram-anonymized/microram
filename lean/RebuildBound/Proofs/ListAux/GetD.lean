import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.Nat.Bitwise

/-!
# ListAux: `List.set` read back through `List.getD` (from D6.Basic)

`getD_set_eq` and the canonical `getD_set_ne` (the copies `D23.getD_set_ne`
was merged into it). Kept with the light imports of `ListAux.Basic` so that
importing it does not pull in all of Mathlib. Namespace `RebuildBound.D6` kept.
-/

namespace RebuildBound.D6

theorem getD_set_eq {α : Type*} (l : List α) (i j : Nat) (a d : α) :
    (l.set i a).getD j d = if i = j ∧ i < l.length then a else l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = j
  · subst h
    by_cases h' : i < l.length
    · simp [h']
    · simp [h']
  · simp [h]

theorem getD_set_ne {α : Type*} (l : List α) {i j : Nat} (a d : α) (h : i ≠ j) :
    (l.set i a).getD j d = l.getD j d := by
  rw [getD_set_eq]; simp [h]

end RebuildBound.D6
