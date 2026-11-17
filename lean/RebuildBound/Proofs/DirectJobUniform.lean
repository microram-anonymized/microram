import RebuildBound.Spec.DirectJobUniform
import RebuildBound.Proofs.DirectJobLawTransport
import RebuildBound.Proofs.FiniteCoupling
import RebuildBound.Proofs.BlindBits.Words

open MeasureTheory
open scoped ENNReal

namespace RebuildBound
open Model Model.DirectJob Spec

namespace DirectJobUniformProof

/-- Control: genuinely separate observed coordinates retain their joint mass
when unused coordinates are present. -/
example : ProbabilityTheory.uniformOn (Set.univ : Set ((Fin 2 × Fin 2) × Fin 3))
    {ω | ω.1 = (0, 0)} = (4 : ℝ≥0∞)⁻¹ := by
  simpa using uniform_projection (Equiv.refl ((Fin 2 × Fin 2) × Fin 3)) (0, 0)

/-- Control: an empty set of observed coordinates has one assignment. -/
example : ProbabilityTheory.uniformOn (Set.univ : Set (Unit × Fin 2))
    {ω | ω.1 = ()} = 1 := by
  simpa only [Fintype.card_unique, Nat.cast_one, inv_one] using
    uniform_projection (Equiv.refl (Unit × Fin 2)) ()

/-- Reusing one uniform coordinate twice does not give the joint independent
law, despite each individual coordinate being uniform. Such a sample cannot
be justified by the product split required above. -/
example : ¬ ProbabilityTheory.uniformOn (Set.univ : Set (Fin 2))
    {ω | (ω, ω) = (0, 0)} ≤ (4 : ℝ≥0∞)⁻¹ := by
  have hs : {ω : Fin 2 | (ω, ω) = (0, 0)} = {0} := by ext ω; simp
  rw [hs, ProbabilityTheory.uniformOn_univ]
  norm_num

end DirectJobUniformProof

theorem DirectJobUniformCoupling : DirectJobUniformCoupling_statement := by
  intro Ω _ _ _ g L Unused _ _ split hw
  exact FiniteCouplingProof.finite_uniform_coupling L.toFinite Unused split hw

theorem DirectJobUniformDigitOneProbability : DirectJobUniformDigitOneProbability_statement := by
  intro Ω _ _ _ g L _ direct Unused _ _ split hw hW hkeys hload
  have hnorm : ∑ hist, L.weight hist = 1 := by
    simp only [hw, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_pos.ne')
      (ENNReal.natCast_ne_top _)
  exact (DirectJobLawTransport _ L (fun ω => (split ω).1)
    (DirectJobUniformCoupling L Unused split hw) _).trans
      (DirectJobDigitOneFiniteWords L direct hnorm hW hkeys hload)

theorem DirectJobUniformHistoryProbability : DirectJobUniformHistoryProbability_statement := by
  intro Ω _ _ _ d hl hu data hv hw Unused _ _ split
  apply DirectJobHistoryTransport _ d hl hu data hv (fun ω => (split ω).1)
  apply DirectJobUniformCoupling _ Unused split
  intro hist
  change data.weight hist.1 * (Fintype.card data.Words : ℝ≥0∞)⁻¹ =
    (Fintype.card (data.Base × data.Words) : ℝ≥0∞)⁻¹
  rw [hw, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]

end RebuildBound
