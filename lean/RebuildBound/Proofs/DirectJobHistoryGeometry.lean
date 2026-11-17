import RebuildBound.Spec.DirectJobHistoryGeometry
import RebuildBound.Proofs.DirectJobReferenceInputs
import RebuildBound.Proofs.OldWordDensity

open scoped ENNReal NNReal
namespace RebuildBound
open Model Model.DirectJob Spec

namespace DirectJobHistoryGeometryProof

theorem weight_sum (data : DirectHistoryData) (prior : Geometry) (s : SepGeom)
    (hw : ∑ base, data.weight base = 1) :
    ∑ hist, (data.lawFor prior s).weight hist = 1 := by
  classical
  have hc : (Fintype.card data.Words : ℝ≥0∞) ≠ 0 := by
    rw [ne_eq, Nat.cast_eq_zero, Fintype.card_eq_zero_iff]
    exact not_isEmpty_of_nonempty _
  change ∑ hist : data.Base × data.Words,
    data.weight hist.1 * (Fintype.card data.Words : ℝ≥0∞)⁻¹ = 1
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ENNReal.mul_inv_cancel hc (ENNReal.natCast_ne_top _), mul_one]
  exact hw

theorem density (data : DirectHistoryData) (prior : Geometry) (s : SepGeom)
    (hd : 2 ≤ s.d) (hk : s.K + val2 (s.d - 1) ≤ 64)
    (hw : ∑ base, data.weight base = 1)
    (target : data.KA → Fin ((s.d - 1) * s.U)) :
    (∑ hist ∈ Finset.univ.filter (fun hist : data.Hist => ∀ x : data.KA,
      s.oldHome (data.word hist.2 x) = target x),
      (data.lawFor prior s).weight hist) ≤
      (s.oldDensity 64 data.KA.card : ℝ≥0∞) /
        (((s.d - 1) * s.U : Nat) : ℝ≥0∞) ^ data.KA.card := by
  classical
  simp only [Finset.sum_filter, DirectHistoryData.lawFor, Fintype.sum_prod_type]
  have he : (∑ base : data.Base, ∑ h : data.Words,
      if ∀ x : data.KA, s.oldHome (data.word h x) = target x
        then data.weight base * (Fintype.card data.Words : ℝ≥0∞)⁻¹ else 0) =
      (∑ base, data.weight base) * ((Fintype.card data.Words : ℝ≥0∞)⁻¹ *
        ∑ h : data.Words, if ∀ x : data.KA,
          s.oldHome (data.word h x) = target x then 1 else 0) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro base _
    simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [he, hw, one_mul]
  have hword (h : data.Words) (x : data.KA) : data.word h x = (h x : Nat) := by
    simp [DirectHistoryData.word, x.property]
  simpa only [hword] using OldWordDensity s data.KA target (by omega) hk

end DirectJobHistoryGeometryProof

open DirectJobHistoryGeometryProof in
theorem DirectJobHistoryInputLawFor : DirectJobHistoryInputLawFor_statement := by
  intro prior s hg hd hk hprev load data hv
  constructor
  · exact weight_sum data prior s hv.weight_sum
  · intro hist h
    exact DirectJobReferenceInputShapeFor prior s hg
      (data.olderWord hist.1) (data.word hist.2) ((data.lawFor prior s).wordFn h)
      (data.before hist.1) (data.priorUnits hist.1 (data.word hist.2))
      (data.freshUnits hist ((data.lawFor prior s).wordFn h)) (data.chronology hist.1)
      (hv.before_history hist.1)
  · intro hist
    have hp := (DirectJobReferenceStep (data.olderWord hist.1) (data.before hist.1)
      ⟨prior, data.word hist.2, data.priorUnits hist.1 (data.word hist.2)⟩
      (data.chronology hist.1) (hv.before_history hist.1)).1
    change ((data.stateFor prior hist).records.map Rec.key).toFinset = data.KA
    rw [← hv.prior_keys hist.1 hist.2]
    ext key
    simp only [List.mem_toFinset]
    exact (hp.map Rec.key).mem_iff.trans (DirectPrefixKeys _ key)
  · intro hist h
    change ((referenceSepInputs s (data.stateFor prior hist)
      (data.freshUnits hist ((data.lawFor prior s).wordFn h))).bAll.map Rec.key).toFinset = data.KB
    rw [(DirectJobReferenceInputMatch _ _ _).2.2]
    exact hv.fresh_keys hist _
  · exact hk
  · exact_mod_cast hv.aLoad
  · exact_mod_cast hv.bLoad
  · intro target
    exact density data prior s hd hprev hv.weight_sum target

theorem DirectJobHistoryInputMatchFor : DirectJobHistoryInputMatchFor_statement := by
  intro prior s load data hv
  constructor
  · intro hist h
    exact ⟨rfl, rfl⟩
  · intro hist h
    exact hv.fresh_keys hist _

end RebuildBound
