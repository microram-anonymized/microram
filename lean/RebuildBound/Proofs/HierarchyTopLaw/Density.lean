import RebuildBound.Proofs.HierarchyTopLaw.Tape
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.ENNReal.Inv

/-! # HierarchyTopLaw: the starting buckets of a preparation are uniform.

The starting bucket of a key is its previous top family's 64-bit word
modulo `T = 2^b`, for any `b ≤ 64`. Splitting low and high bits separates
the starting-bucket vector from the rest of the history, so each vector has
mass exactly `T^-|K|` (`density_bound_bits`). The original 22-bit interfaces
remain specializations. -/

open scoped ENNReal

namespace RebuildBound.HierarchyTopLawProof
open Model Model.Hierarchy Spec

/-- Split a word into its low `b` bits and its remaining bits. -/
def divmodBits (b : Nat) (hb : b ≤ 64) :
    Fin (2 ^ 64) ≃ Fin (2 ^ b) × Fin (2 ^ (64 - b)) :=
  (finCongr (by rw [← Nat.pow_add, Nat.sub_add_cancel hb] :
    2 ^ 64 = 2 ^ (64 - b) * 2 ^ b)).trans
    (finProdFinEquiv.symm.trans (Equiv.prodComm _ _))

/-- The first projection is precisely the low bits. -/
theorem divmodBits_fst (b : Nat) (hb : b ≤ 64) (x : Fin (2 ^ 64)) :
    ((divmodBits b hb x).1 : Nat) = x.val % 2 ^ b := rfl

/-- The original 22-bit split. -/
def divmod : Fin (2 ^ 64) ≃ Fin (2 ^ 22) × Fin (2 ^ 42) :=
  divmodBits 22 (by omega)

/-- The history mass of one fibre of a split is the inverse size of the
split's first factor. -/
theorem fiber_sum {H O R : Type} [Fintype H] [Fintype O] [Fintype R] [Nonempty R]
    [DecidableEq O] (e : H ≃ O × R) (o : O) :
    ∑ _h ∈ Finset.univ.filter (fun h => (e h).1 = o), (Fintype.card H : ℝ≥0∞)⁻¹ =
      (Fintype.card O : ℝ≥0∞)⁻¹ := by
  classical
  have hfib : (Finset.univ.filter fun h => (e h).1 = o).card = Fintype.card R := by
    let f : {h // (e h).1 = o} ≃ R :=
      { toFun := fun h => (e h.val).2
        invFun := fun r => ⟨e.symm (o, r), by simp⟩
        left_inv := by
          intro h
          apply Subtype.ext
          apply e.injective
          simp only [Equiv.apply_symm_apply]
          exact Prod.ext h.2.symm rfl
        right_inv := fun r => by simp }
    simpa only [Fintype.card_subtype] using Fintype.card_congr f
  rw [Finset.sum_const, hfib, nsmul_eq_mul, Fintype.card_congr e, Fintype.card_prod,
    Nat.cast_mul, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _)), mul_comm, mul_assoc,
    ENNReal.inv_mul_cancel (by simp [Fintype.card_ne_zero]) (ENNReal.natCast_ne_top _), mul_one]

variable {cfg : Config} {N : Nat}

/-- The split of a history into the starting-bucket vector (the low bits of
the coordinate `c'`'s block on `K`) and the rest. -/
def posSplitBits (b : Nat) (hb : b ≤ 64) (pc : Coord cfg) (K : Finset LogicalKey) (hK : ∀ k ∈ K, k.toNat < N) (c' : {q : Coord cfg // q ≠ pc}) :
    Hist cfg N pc K ≃ ({x // x ∈ K} → Fin (2 ^ b)) ×
      ((({x // x ∈ K} → Fin (2 ^ (64 - b))) × ({k : KeyIndex N // k.val ∉ K} → Fin (2 ^ 64))) ×
        (({q : {q : Coord cfg // q ≠ pc} // q ≠ c'} → KeyIndex N → Fin (2 ^ 64)) ×
          ({k : KeyIndex N // k.val ∉ K} → Fin (2 ^ 64)))) :=
  let eK : {k : KeyIndex N // k.val ∈ K} ≃ {x // x ∈ K} :=
    { toFun := fun k => ⟨k.1.val, k.2⟩
      invFun := fun x => ⟨⟨x.1, hK _ x.2⟩, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E : (KeyIndex N → Fin (2 ^ 64)) ≃ ({x // x ∈ K} → Fin (2 ^ b)) ×
      (({x // x ∈ K} → Fin (2 ^ (64 - b))) × ({k : KeyIndex N // k.val ∉ K} → Fin (2 ^ 64))) :=
    ((Equiv.piEquivPiSubtypeProd (fun k : KeyIndex N => k.val ∈ K) fun _ => Fin (2 ^ 64)).trans
      (Equiv.prodCongr
        (((Equiv.arrowCongr eK (Equiv.refl _)).trans (Equiv.arrowCongr (Equiv.refl _) (divmodBits b hb))).trans
          (Equiv.arrowProdEquivProdArrow _ _ _))
        (Equiv.refl _))).trans (Equiv.prodAssoc _ _ _)
  ((Equiv.prodCongr (Equiv.piSplitAt c' fun _ => KeyIndex N → Fin (2 ^ 64)) (Equiv.refl _)).trans
    (Equiv.prodAssoc _ _ _)).trans
    ((Equiv.prodCongr E (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _))

theorem posSplitBits_fst (b : Nat) (hb : b ≤ 64) (pc : Coord cfg) (K : Finset LogicalKey) (hK : ∀ k ∈ K, k.toNat < N)
    (c' : {q : Coord cfg // q ≠ pc}) (hist : Hist cfg N pc K) (x : {x // x ∈ K}) :
    ((posSplitBits b hb pc K hK c' hist).1 x : Nat) = (hist.1 c' ⟨x.1, hK _ x.2⟩ : Nat) % 2 ^ b := rfl

/-- The starting-bucket vector of a uniform history is uniform. -/
theorem density_bound_bits (b : Nat) (hb : b ≤ 64) (pc : Coord cfg) (K : Finset LogicalKey) (hK : ∀ k ∈ K, k.toNat < N)
    (c' : {q : Coord cfg // q ≠ pc}) (o : {x // x ∈ K} → Fin (2 ^ b)) :
    ∑ _hist ∈ Finset.univ.filter (fun hist : Hist cfg N pc K =>
        ∀ x : {x // x ∈ K}, (hist.1 c' ⟨x.1, hK _ x.2⟩ : Nat) % 2 ^ b = o x),
      (Fintype.card (Hist cfg N pc K) : ℝ≥0∞)⁻¹ = ((2 ^ b : ℝ≥0∞) ^ K.card)⁻¹ := by
  classical
  have hset : (Finset.univ.filter fun hist : Hist cfg N pc K =>
        ∀ x : {x // x ∈ K}, (hist.1 c' ⟨x.1, hK _ x.2⟩ : Nat) % 2 ^ b = o x) =
      Finset.univ.filter fun hist => (posSplitBits b hb pc K hK c' hist).1 = o := by
    ext hist
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, funext_iff, Fin.ext_iff,
      posSplitBits_fst]
  rw [hset, fiber_sum]
  simp

/-- Compatibility specialization at 22 bits. -/
def posSplit (pc : Coord cfg) (K : Finset LogicalKey) (hK : ∀ k ∈ K, k.toNat < N)
    (c' : {q : Coord cfg // q ≠ pc}) := posSplitBits 22 (by omega) pc K hK c'

theorem posSplit_fst (pc : Coord cfg) (K : Finset LogicalKey) (hK : ∀ k ∈ K, k.toNat < N)
    (c' : {q : Coord cfg // q ≠ pc}) (hist : Hist cfg N pc K) (x : {x // x ∈ K}) :
    ((posSplit pc K hK c' hist).1 x : Nat) =
      (hist.1 c' ⟨x.1, hK _ x.2⟩ : Nat) % 2 ^ 22 := rfl

/-- Compatibility specialization at 22 bits. -/
theorem density_bound (pc : Coord cfg) (K : Finset LogicalKey) (hK : ∀ k ∈ K, k.toNat < N)
    (c' : {q : Coord cfg // q ≠ pc}) (o : {x // x ∈ K} → Fin (2 ^ 22)) :
    ∑ _hist ∈ Finset.univ.filter (fun hist : Hist cfg N pc K =>
        ∀ x : {x // x ∈ K}, (hist.1 c' ⟨x.1, hK _ x.2⟩ : Nat) % 2 ^ 22 = o x),
      (Fintype.card (Hist cfg N pc K) : ℝ≥0∞)⁻¹ = ((2 ^ 22 : ℝ≥0∞) ^ K.card)⁻¹ :=
  density_bound_bits 22 (by omega) pc K hK c' o
