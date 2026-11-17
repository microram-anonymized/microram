import RebuildBound.Proofs.FiniteCoupling.Prob
import RebuildBound.Spec.G3
import RebuildBound.Proofs.ShadowLaw.Unit
import RebuildBound.Proofs.BlindBits.Bits

/-!
# G3: the law of the homes

The average over the words of a function of the home-count vector of a
fixed key set is the integral against `convList (replicate n (unitLaw (1/T)))`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.G3Proof

open RebuildBound.Model RebuildBound.Spec

variable {g : TopGeom} (L : TopJobLaw g)

theorem wordFn_val (h : L.Key → Fin (2 ^ L.W)) (y : L.Key) : L.wordFn h y = (h y : ℕ) := by
  unfold TopJobLaw.wordFn; simp [y.2]

/-! ### Bridge to `convList` over an arbitrary index type -/

section Bridge

open RebuildBound.P11dProof

variable {m W : ℕ}

/-- The home of a word. -/
def dHome (m W : ℕ) (a : Fin (2 ^ W)) : Fin (2 ^ m) :=
  ⟨(a : ℕ) % 2 ^ m, Nat.mod_lt _ (by positivity)⟩

theorem law_dHome (hm : m ≤ W) (v : Fin (2 ^ m)) :
    law (dHome m W) v = 1 / 2 ^ m := by
  unfold law
  have h1 : (Finset.univ.filter (fun a : Fin (2 ^ W) => dHome m W a = v)).card =
      2 ^ (W - m) := by
    rw [← RebuildBound.G2.card_mod_fiber hm v.isLt]
    congr 1
    ext a
    simp [dHome, Fin.ext_iff]
  rw [h1]
  have : (2 : ℝ≥0) ^ W = 2 ^ m * 2 ^ (W - m) := by rw [← pow_add]; congr 1; omega
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  rw [this]
  field_simp

theorem bridgeG (hm : m ≤ W) {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : (Fin (2 ^ m) → ℕ) → ℝ≥0∞) :
    ∫⁻ y, F y ∂(convList (List.replicate (Fintype.card ι)
        (unitLaw (fun _ : Fin (2 ^ m) => (1 / 2 ^ m : ℝ≥0))))) =
      ((Fintype.card (Fin (2 ^ W)) : ℝ≥0∞) ^ Fintype.card ι)⁻¹ *
        ∑ g : ι → Fin (2 ^ W), F (∑ i, unitVec (dHome m W (g i))) := by
  have hlaw : law (dHome m W) = fun _ => 1 / 2 ^ m := funext (law_dHome hm)
  have := bridge (dHome m W) (Fintype.card ι) F
  rw [hlaw] at this
  rw [this]
  congr 1
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl _)) _ _ ?_
  intro g'
  congr 1
  simp only [Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.refl_apply, Function.comp_apply]
  exact (Equiv.sum_comp e (fun j => unitVec (dHome m W (g' j)))).symm

theorem avg_restrict {Y A : Type} [Fintype Y] [DecidableEq Y] [Fintype A] [Nonempty A] (p : Y → Prop)
    [DecidablePred p] (G : ({y // p y} → A) → ℝ≥0∞) :
    (Fintype.card (Y → A) : ℝ≥0∞)⁻¹ * ∑ h : Y → A, G (fun y => h y.1) =
      (Fintype.card ({y // p y} → A) : ℝ≥0∞)⁻¹ * ∑ g, G g := by
  let e := Equiv.piEquivPiSubtypeProd p (fun _ : Y => A)
  have h1 : ∑ h : Y → A, G (fun y => h y.1) =
      ∑ pr : ({y // p y} → A) × ({y // ¬ p y} → A), G pr.1 :=
    Fintype.sum_equiv e _ _ (fun h => rfl)
  have hc : Fintype.card (Y → A) =
      Fintype.card ({y // p y} → A) * Fintype.card ({y // ¬ p y} → A) := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  rw [h1, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, hc, Nat.cast_mul]
  have h0 : (Fintype.card ({y // ¬ p y} → A) : ℝ≥0∞) ≠ 0 := by
    have : 0 < Fintype.card ({y // ¬ p y} → A) := Fintype.card_pos
    exact_mod_cast this.ne'
  have hT : (Fintype.card ({y // ¬ p y} → A) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.mul_inv (Or.inr hT) (Or.inr h0)]
  calc _ = ((Fintype.card ({y // ¬ p y} → A) : ℝ≥0∞)⁻¹ * Fintype.card ({y // ¬ p y} → A)) *
        ((Fintype.card ({y // p y} → A) : ℝ≥0∞)⁻¹ * ∑ g, G g) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel h0 hT, one_mul]

/-- The index type of a key subset. -/
abbrev SubKey (K : Finset Model.LogicalKey) : Type := {y : L.Key // y.1 ∈ K}

def subKeyEquiv (K : Finset Model.LogicalKey) (hK : K ⊆ L.KA ∪ L.KB) : SubKey L K ≃ K where
  toFun y := ⟨y.1.1, y.2⟩
  invFun x := ⟨⟨x.1, hK x.2⟩, x.2⟩
  left_inv y := rfl
  right_inv x := rfl

theorem cnt_eq (K : Finset Model.LogicalKey) (hK : K ⊆ L.KA ∪ L.KB) (h : L.Key → Fin (2 ^ L.W)) :
    (fun v : Fin (2 ^ m) => (K.filter fun x => L.wordFn h x % 2 ^ m = v.val).card) =
      ∑ i : SubKey L K, unitVec (dHome m L.W (h i.1)) := by
  funext v
  rw [Finset.sum_apply, Finset.card_filter]
  have : ∀ i : SubKey L K, (unitVec (dHome m L.W (h i.1))) v =
      (fun x => if L.wordFn h x % 2 ^ m = v.val then 1 else 0) i.1.1 := by
    intro i
    simp only [unitVec, Pi.single_apply, dHome, Fin.ext_iff]
    rw [wordFn_val]
    simp only [eq_comm]
  rw [Finset.sum_congr rfl fun i _ => this i]
  rw [← Finset.sum_coe_sort K]
  exact (Fintype.sum_equiv (subKeyEquiv L K hK) _ _ (fun i => rfl)).symm

theorem avg_cnt (hm : m ≤ L.W) (K : Finset Model.LogicalKey) (hK : K ⊆ L.KA ∪ L.KB)
    (F : (Fin (2 ^ m) → ℕ) → ℝ≥0∞) :
    (Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
      ∑ h : L.Key → Fin (2 ^ L.W),
        F (fun v : Fin (2 ^ m) => (K.filter fun x => L.wordFn h x % 2 ^ m = v.val).card) =
    ∫⁻ y, F y ∂(convList (List.replicate K.card
        (unitLaw (fun _ : Fin (2 ^ m) => (1 / 2 ^ m : ℝ≥0))))) := by
  classical
  have hι : Fintype.card (SubKey L K) = K.card := by
    rw [Fintype.card_congr (subKeyEquiv L K hK), Fintype.card_coe]
  rw [← hι, bridgeG hm]
  simp_rw [cnt_eq L K hK]
  rw [avg_restrict (fun y : L.Key => y.1 ∈ K)
    (fun g => F (∑ i : SubKey L K, unitVec (dHome m L.W (g i))))]
  rw [Fintype.card_fun, Nat.cast_pow]

end Bridge

end RebuildBound.G3Proof
