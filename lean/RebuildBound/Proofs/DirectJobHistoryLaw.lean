import RebuildBound.Spec.DirectJobHistoryLaw
import RebuildBound.Proofs.DirectJobOldWordDensity
import RebuildBound.Proofs.DirectJobHistoryGeometry
import RebuildBound.Proofs.DirectJobFiniteWords

open scoped ENNReal NNReal
namespace RebuildBound
open Model Model.DirectJob Spec

namespace DirectJobHistoryLawLemmas

theorem word_val (data : DirectHistoryData) (h : data.Words) (x : data.KA) :
    data.word h x = (h x : Nat) := by
  simp [DirectHistoryData.word, x.property]

theorem shared_inputs (data : DirectHistoryData) (d : Nat) (hist : data.Hist)
    (word : Model.LogicalKey → Nat) :
    (data.law d).inputs hist word =
      referenceSepInputs (selectedDirectSep d) (data.state d hist) (data.freshUnits hist word) := rfl

/-- The selected source premises are an instance of the actual-width contract. -/
theorem validFor (data : DirectHistoryData) (d : Nat) (hl : 2 ≤ d) (hu : d ≤ 8)
    (hv : data.Valid d) : data.ValidFor (selectedDirectSep d) 32 := by
  have hd := (DirectJobSelectedGeometry.2 d hl hu).2.2.1
  refine ⟨hv.weight_sum, hv.before_history, hv.prior_keys, hv.fresh_keys, ?_, hv.bLoad⟩
  change data.KA.card ≤ 32 * (((selectedDirectSep d).d - 1) * 16)
  simpa only [hd] using hv.aLoad

theorem weight_sum (data : DirectHistoryData) (d : Nat) (hv : data.Valid d) :
    ∑ hist, (data.law d).weight hist = 1 :=
  DirectJobHistoryGeometryProof.weight_sum data (selectedDirectGeometry (d - 1))
    (selectedDirectSep d) hv.weight_sum

theorem density (data : DirectHistoryData) (d : Nat) (hl : 2 ≤ d) (hu : d ≤ 8)
    (hv : data.Valid d)
    (target : data.KA → Fin (((selectedDirectSep d).d - 1) * (selectedDirectSep d).U)) :
    (∑ hist ∈ Finset.univ.filter (fun hist : data.Hist => ∀ x : data.KA,
      (selectedDirectSep d).oldHome (data.word hist.2 x) = target x),
      (data.law d).weight hist) ≤
      ((selectedDirectSep d).oldDensity 64 data.KA.card : ℝ≥0∞) /
        ((((selectedDirectSep d).d - 1) * (selectedDirectSep d).U : Nat) : ℝ≥0∞) ^ data.KA.card := by
  apply DirectJobHistoryGeometryProof.density data (selectedDirectGeometry (d - 1))
    (selectedDirectSep d) _ _ hv.weight_sum target
  · rw [(DirectJobSelectedGeometry.2 d hl hu).2.2.1]; exact hl
  · interval_cases d <;> decide

end DirectJobHistoryLawLemmas

open DirectJobHistoryLawLemmas

theorem DirectJobHistoryInputLaw : DirectJobHistoryInputLaw_statement := by
  intro d hl hu data hv
  apply DirectJobHistoryInputLawFor (selectedDirectGeometry (d - 1)) (selectedDirectSep d)
    _ _ _ _ 32 data (validFor data d hl hu hv)
  all_goals interval_cases d <;> decide

theorem DirectJobHistoryInputMatch : DirectJobHistoryInputMatch_statement := by
  intro d data hv
  constructor
  · intro hist h
    exact ⟨rfl, rfl⟩
  · intro hist h
    exact hv.fresh_keys hist _

theorem DirectJobHistoryProbability : DirectJobHistoryProbability_statement := by
  intro d hl hu data hv
  apply DirectJobFiniteWordProbability d hl hu (data.law d)
    ((selectedDirectSep d).oldDensity 64 data.KA.card)
    (DirectJobHistoryInputLaw d hl hu data hv) rfl
  · apply selected_oldDensity_mono d hl hu
    have hd := (DirectJobSelectedGeometry.2 d hl hu).2.2.1
    change data.KA.card ≤ 32 * (((selectedDirectSep d).d - 1) * 16)
    rw [hd]
    exact hv.aLoad
  · exact DirectJobHistoryInputMatch d data hv

end RebuildBound
