import RebuildBound.Spec.Model.Key
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Finset.Basic

/-! # DirectJobUniformCycle: coordinate splits of a product tape. -/

namespace RebuildBound.DirectJobUniformCycleProof

/-- Rename the key set of a word block along a key-set equality. -/
def keyCast {K K' : Finset Model.LogicalKey} (h : K = K') (γ : Type) : (K → γ) ≃ (K' → γ) :=
  Equiv.arrowCongr (Equiv.subtypeEquivRight fun x => by rw [h]) (Equiv.refl γ)

/-- Split a product into the coordinates satisfying `P`, two further
coordinates `a` and `b`, and the rest. -/
def split3 {α : Type} [DecidableEq α] (β : α → Type) (P : α → Prop) [DecidablePred P]
    (a b : α) (ha : ¬ P a) (hb : ¬ P b) (hab : a ≠ b) :
    (∀ j, β j) ≃ (((∀ j : {j // P j}, β j) × β a) × β b) ×
      (∀ j : {j // ¬ P j ∧ j ≠ a ∧ j ≠ b}, β j) where
  toFun f := (((fun j => f j, f a), f b), fun j => f j)
  invFun x j :=
    if h : P j then x.1.1.1 ⟨j, h⟩
    else if h1 : j = a then h1.symm.rec x.1.1.2
    else if h2 : j = b then h2.symm.rec x.1.2
    else x.2 ⟨j, h, h1, h2⟩
  left_inv f := by
    funext j
    by_cases h : P j
    · simp [h]
    · by_cases h1 : j = a
      · subst h1; simp [h]
      · by_cases h2 : j = b
        · subst h2; simp [h, h1]
        · simp [h, h1, h2]
  right_inv x := by
    obtain ⟨⟨⟨x1, x2⟩, x3⟩, x4⟩ := x
    have hba : b ≠ a := fun h => hab h.symm
    refine Prod.ext (Prod.ext (Prod.ext ?_ ?_) ?_) ?_
    · funext j
      simp [j.2]
    · simp [ha]
    · simp [hb, hba]
    · funext j
      simp [j.2.1, j.2.2.1, j.2.2.2]

end RebuildBound.DirectJobUniformCycleProof
