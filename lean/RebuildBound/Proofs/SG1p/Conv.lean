import RebuildBound.Proofs.G3
import RebuildBound.Proofs.SG1

/-!
# SG1p: comparison of unit-vector convolutions and the bridge over a finite index type
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.SG1pProof

open RebuildBound.Spec RebuildBound.P11dProof

/-- If the masses of `p` are at most `c` times those of `q`, the `n`-fold convolution of
`unitLaw p` is dominated by `c ^ n` times that of `unitLaw q` on every test. -/
theorem conv_compare {κ : Type} [Fintype κ] [DecidableEq κ] (p q : κ → ℝ≥0) (c : ℝ≥0)
    (hp : ∑ v, p v = 1) (hq : ∑ v, q v = 1) (hpq : ∀ v, p v ≤ c * q v) (n : ℕ) :
    ∀ F : (κ → ℕ) → ℝ≥0∞,
      ∫⁻ y, F y ∂(convList (List.replicate n (unitLaw p))) ≤
        (c : ℝ≥0∞) ^ n * ∫⁻ y, F y ∂(convList (List.replicate n (unitLaw q))) := by
  have hUp := unitLaw_prob p hp
  have hUq := unitLaw_prob q hq
  induction n with
  | zero => intro F; simp [convList, lintegral_dirac]
  | succ n ih =>
    intro F
    have hTp := convList_replicate_prob (unitLaw p) n
    have hTq := convList_replicate_prob (unitLaw q) n
    rw [List.replicate_succ, convList, Measure.lintegral_conv Measurable.of_discrete,
      lintegral_unitLaw, List.replicate_succ, convList, Measure.lintegral_conv Measurable.of_discrete,
      lintegral_unitLaw, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    calc (p k : ℝ≥0∞) * ∫⁻ y, F (unitVec k + y) ∂(convList (List.replicate n (unitLaw p)))
        ≤ (c * q k : ℝ≥0) * ((c : ℝ≥0∞) ^ n *
            ∫⁻ y, F (unitVec k + y) ∂(convList (List.replicate n (unitLaw q)))) := by
          gcongr
          · exact_mod_cast hpq k
          · exact ih _
      _ = _ := by push_cast; ring

/-- The bridge over an arbitrary finite index type. -/
theorem bridge_fin {κ ι A : Type} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    [Fintype A] [Nonempty A] (d : A → κ) (F : (κ → ℕ) → ℝ≥0∞) :
    ∫⁻ y, F y ∂(convList (List.replicate (Fintype.card ι) (unitLaw (law d)))) =
      ((Fintype.card A : ℝ≥0∞) ^ Fintype.card ι)⁻¹ *
        ∑ γ : ι → A, F (∑ i, unitVec (d (γ i))) := by
  rw [bridge d (Fintype.card ι) F]
  congr 1
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl _)) _ _ ?_
  intro g'
  congr 1
  simp only [Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.refl_apply, Function.comp_apply]
  exact (Equiv.sum_comp e (fun j => unitVec (d (g' j)))).symm

end RebuildBound.SG1pProof
