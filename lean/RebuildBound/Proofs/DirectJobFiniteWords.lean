import RebuildBound.Proofs.DirectJobFiniteWords.Generic
import RebuildBound.Spec.DirectJobFiniteWords
import RebuildBound.Proofs.DirectJobAProbability
import RebuildBound.Proofs.SG1p.Terms
import RebuildBound.Proofs.SelRest.Sound

/-! Reuse the shared fixed-key count, current-home and positive-excess proofs.
No new convolution, independence, tail, or density inequality is proved here. -/
open scoped ENNReal NNReal
namespace RebuildBound
open Model Model.DirectJob Spec

private theorem selected_density_check (d : Nat) (hlo : 1 ≤ d) (hhi : d ≤ 8) :
    let s := selectedDirectSep d
    SelRest.dens 64 (s.r * ((2 ^ (64 - s.k) + s.r - 1) / s.r))
      (64 - s.k) (32 * s.N) ≤ 2 * 2 ^ 64 := by
  interval_cases d <;> decide +kernel

theorem DirectJobSelectedWordDensity : DirectJobSelectedWordDensity_statement := by
  intro d hlo hhi n hn
  let s := selectedDirectSep d
  have hr : 1 ≤ s.r := by
    dsimp [s]
    interval_cases d <;> decide
  have hsize : 32 * s.N < 2 ^ 64 := by
    dsimp [s]
    interval_cases d <;> decide
  have hpow := SelRest.dens_le 64 (s.r * ((2 ^ (64 - s.k) + s.r - 1) / s.r))
    (64 - s.k) (32 * s.N) hsize
  have hcheck := selected_density_check d hlo hhi
  have hreal : (SelRest.dens 64 (s.r * ((2 ^ (64 - s.k) + s.r - 1) / s.r))
      (64 - s.k) (32 * s.N) : ℝ) ≤ 2 * 2 ^ 64 := by exact_mod_cast hcheck
  calc s.curDensity 64 n ≤ s.curDensity 64 (32 * s.N) := SelJobAux.curDensity_mono s 64 hr hn
    _ ≤ _ := hpow
    _ ≤ 2 := (div_le_iff₀ (by positivity)).2 hreal

private theorem selected_constants (d : Nat) (hlo : 2 ≤ d) (hhi : d ≤ 8) :
    (selectedDirectGeometry d).K = 4 ∧
    (selectedDirectGeometry d).U = 16 ∧
    (selectedDirectGeometry d).bCapacity = 64 ∧
    (selectedDirectGeometry d).outputCapacity = 64 ∧
    (selectedDirectGeometry d).outputHomes = d * 16 := by
  interval_cases d <;> decide

theorem DirectJobFiniteWordProbability : DirectJobFiniteWordProbability_statement := by
  intro d hlo hhi L D hL hW hD direct hm
  let s := selectedDirectSep d
  let g := selectedDirectGeometry d
  obtain ⟨hs, _, _, hN, _⟩ := DirectJobSelectedGeometry.2 d hlo hhi
  obtain ⟨hK, hU, hBcap, hOcap, hHomes⟩ := selected_constants d hlo hhi
  have hhome (word : Nat) : g.home word = s.homeOf word := by
    have hc := DirectJobSelectedAAdapter d hlo hhi
    change (selectedDirectGeometry d).home word = (selectedDirectSep d).homeOf word
    simp [Geometry.home, digitHome, SepGeom.homeOf, SepGeom.cls, SepGeom.k,
      hc.K, hc.e, hc.r]
  have hb := DirectJobBFiniteWords L g 32 direct 256 hL.weight_sum
    (by change (selectedDirectGeometry d).K ≤ L.W; rw [hK, hW]; omega)
    hm.bKeys (by simpa only [g, hU, selectedDirectSep, SepGeom.U] using hL.bLoad) (by rw [hBcap]; decide)
  have hu := DirectJobUnionFiniteWords L g 32 D direct 256 hs hL hm rfl hN.symm
    hhome (by rw [hOcap]; decide)
  have hcard : (L.KA ∪ L.KB).card ≤ 32 * s.N := by
    exact_mod_cast SG1Proof.KAB_card_le L hL hs
  have hden := DirectJobSelectedWordDensity d (by omega) hhi _ hcard
  have hden0 := SelJobAux.curDensity_nonneg s 64 (L.KA ∪ L.KB).card
  have hnum := DirectJobSelectedDensity d (s.curDensity 64 (L.KA ∪ L.KB).card)
    (by omega) hhi hden0 hden
  have ha := DirectJobSelectedAProbability d hlo hhi L D hL hW hD direct hm.a
  apply DirectJobFailureProbability L.weight L.wordFn g L.wOld direct
    (ENNReal.ofReal (1 / (2 : ℝ) ^ 117)) (selectedDirectABudget d)
    (ENNReal.ofReal (1 / (2 : ℝ) ^ 111))
  -- `L.prob`'s indicators are classical, the statement's use the standard instances.
  · refine le_trans (le_of_eq (by unfold SJobLaw.prob; congr!)) (hb.trans ?_)
    simpa only [g, hU, hBcap, NNReal.coe_ofNat] using ENNReal.ofReal_le_ofReal DirectJobSelectedExcess.1
  · exact le_trans (le_of_eq (by unfold SJobLaw.prob; congr!)) ha
  · refine le_trans (le_of_eq (by unfold SJobLaw.prob; congr!)) (hu.trans ?_)
    simpa only [g, s, hW, hHomes, hOcap, NNReal.coe_ofNat] using ENNReal.ofReal_le_ofReal hnum

theorem DirectJobDigitOneFiniteWords : DirectJobDigitOneFiniteWords_statement := by
  intro s L direct hw hW hk hload
  refine (DirectJobDigitOneFiniteWordsFor L (selectedDirectGeometry 1) 32 direct 256
    (DirectJobSelectedGeometry.1 1 (by decide) (by decide)) rfl hw hW hk ?_ (by decide)).trans
    (ENNReal.ofReal_le_ofReal DirectJobSelectedExcess.1)
  change (L.KB.card : ℝ≥0) ≤ 32 * 16
  norm_num
  exact_mod_cast hload

end RebuildBound
