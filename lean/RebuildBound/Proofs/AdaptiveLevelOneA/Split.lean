import RebuildBound.Proofs.AdaptiveLevelOneA.GeometryLaw

/-! # AdaptiveLevelOneA: the fresh blocks as the law's outcomes

The two fresh blocks (the previous family `(1, o - 1)` and the current family
of `o`), each a word per key below `N`, are split into their parts on A's keys
and off them: the parts off `KA` are the law's base, the previous block on
`KA` its previous-family words and the current block on `KA` its current
words. Both evaluations are definitional: the previous block on `KA` at
`⟨k, hk⟩` is the first fresh block at `k`, and the current words at `k` are
the second fresh block at `k`. -/

namespace RebuildBound.AdaptiveLevelOneAProof
open Model Spec

/-- Functions on a two-element subtype. -/
def twoSplit {α : Type} [DecidableEq α] (P : α → Prop) (a b : α) (ha : P a) (hb : P b)
    (hab : a ≠ b) (hP : ∀ x, P x → x = a ∨ x = b) (X : Type) : ({x // P x} → X) ≃ X × X where
  toFun f := (f ⟨a, ha⟩, f ⟨b, hb⟩)
  invFun p x := if x.1 = a then p.1 else p.2
  left_inv f := by
    funext ⟨x, hx⟩
    rcases hP x hx with rfl | rfl
    · simp
    · simp [Ne.symm hab]
  right_inv p := by simp [Ne.symm hab]

/-- A block of words on the keys below `N`, split on and off a key set below `N`. -/
def keySplit (N : Nat) (K : Finset LogicalKey) (hK : ∀ k ∈ K, k.toNat < N) (X : Type) :
    (KeyIndex N → X) ≃ (K → X) × ({k : KeyIndex N // k.val ∉ K} → X) where
  toFun g := (fun x => g ⟨x.1, hK x.1 x.2⟩, fun k => g k.1)
  invFun p k := if hk : k.val ∈ K then p.1 ⟨k.val, hk⟩ else p.2 ⟨k, hk⟩
  left_inv g := by
    funext k
    by_cases hk : k.val ∈ K <;> simp [hk]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · funext x
      simp [x.2]
    · funext k
      simp [k.2]

/-- A key set and its union with the empty set. -/
def unionEmpty (K : Finset LogicalKey) (X : Type) : (K → X) ≃ ((K ∪ ∅ : Finset LogicalKey) → X) where
  toFun g x := g ⟨x.1, by simpa using x.2⟩
  invFun g x := g ⟨x.1, by simp [x.2]⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Regroup two split blocks as (base, previous words on `K`), current words. -/
def regroup {A1 B1 A2 B2 A2' : Type} (e : A2 ≃ A2') :
    ((A1 × B1) × (A2 × B2)) ≃ (((B1 × B2) × A1) × A2') where
  toFun x := (((x.1.2, x.2.2), x.1.1), e x.2.1)
  invFun y := ((y.1.2, y.1.1.1), (e.symm y.2, y.1.1.2))
  left_inv x := by simp
  right_inv y := by simp

/-- The cell's split of the fresh blocks. -/
def cellSplit {α : Type} [DecidableEq α] (P : α → Prop) (a b : α) (ha : P a) (hb : P b)
    (hab : a ≠ b) (hP : ∀ x, P x → x = a ∨ x = b) (N : Nat) (K : Finset LogicalKey)
    (hK : ∀ k ∈ K, k.toNat < N) :
    ({x // P x} → KeyIndex N → Fin (2 ^ 64)) ≃
      ((OffBlock N K × OffBlock N K) × (K → Fin (2 ^ 64))) ×
        ((K ∪ ∅ : Finset LogicalKey) → Fin (2 ^ 64)) :=
  (twoSplit P a b ha hb hab hP _).trans
    ((Equiv.prodCongr (keySplit N K hK _) (keySplit N K hK _)).trans
      (regroup (unionEmpty K _)))

end RebuildBound.AdaptiveLevelOneAProof
