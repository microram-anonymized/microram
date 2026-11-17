import RebuildBound.Proofs.DirectJobFiniteWords
import RebuildBound.Proofs.AdaptiveLevelOneBU.Cell
import RebuildBound.Proofs.AdaptiveLevelOneBU.Laws
import RebuildBound.Proofs.AdaptiveLevelOneBU.Generic

/-! The selected 31 endpoints specialize the shared arbitrary-geometry causal
cell proof and its local finite-word laws. -/

open MeasureTheory
open scoped ENNReal NNReal
namespace RebuildBound.AdaptiveLevelOneBUProof
open Model Model.DirectJob Model.Hierarchy Spec

section
variable (h : Nat) {N n m : Nat}
variable {T : FamilyTape (cfg31 h) N × DummyTape n m → Trace}

theorem term_B (hTP : TracePrefix_statement) (hCell : CausalCell_statement)
    (hT : CausalSetting (geometry31.chunk h) N n m T) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (tape : Ω → FamilyTape (cfg31 h) N)
    (dtape : Ω → DummyTape n m) (words : Ω → Words)
    (hP : OnlineTapePremises (cfg31 h) N n m μ tape dtape words) (o : Nat)
    (ho : JobId.ordinary 1 o ∈ (cfg31 h).potentialJobs) (hd : 2 ≤ (cfg31 h).digitAt 1 o) :
    μ {ω | levelOneTerm (cfg31 h) (sh31 h) (T (tape ω, dtape ω)) (words ω) o levelOneB} ≤
      ENNReal.ofReal (1 / (2 : ℝ) ^ 117) := by
  have hhi : (cfg31 h).digitAt 1 o ≤ 8 := (digit_le31 h o).trans (by omega)
  obtain ⟨hK, hU, hB, -, -⟩ := selected_constants _ hd hhi
  refine (term_BFor (geometry31.chunk h) (causalGeometry31 h) hTP hCell hT
    μ tape dtape words hP o ho 256 (by change (selectedDirectGeometry ((cfg31 h).digitAt 1 o)).K ≤ 64; rw [hK]; decide)
    (by change (selectedDirectGeometry _).U = 16; exact hU)
    (by change (selectedDirectGeometry ((cfg31 h).digitAt 1 o)).bCapacity < 256; rw [hB]; decide)).trans ?_
  change ENNReal.ofReal (Phi 256 (selectedDirectGeometry ((cfg31 h).digitAt 1 o)).U 64 32
    (selectedDirectGeometry ((cfg31 h).digitAt 1 o)).bCapacity) ≤ _
  simpa only [hU, hB] using ENNReal.ofReal_le_ofReal DirectJobSelectedExcess.1


theorem term_U (hTP : TracePrefix_statement) (hCell : CausalCell_statement)
    (hT : CausalSetting (geometry31.chunk h) N n m T) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (tape : Ω → FamilyTape (cfg31 h) N)
    (dtape : Ω → DummyTape n m) (words : Ω → Words)
    (hP : OnlineTapePremises (cfg31 h) N n m μ tape dtape words) (o : Nat)
    (ho : JobId.ordinary 1 o ∈ (cfg31 h).potentialJobs) (hd : 2 ≤ (cfg31 h).digitAt 1 o) :
    μ {ω | levelOneTerm (cfg31 h) (sh31 h) (T (tape ω, dtape ω)) (words ω) o levelOneU} ≤
      ENNReal.ofReal (1 / (2 : ℝ) ^ 111) := by
  let d := (cfg31 h).digitAt 1 o
  have hhi : d ≤ 8 := (digit_le31 h o).trans (by omega)
  have hlo : 2 ≤ d := hd
  have hdigit := (DirectJobSelectedGeometry.2 d hlo hhi).2.2.1
  obtain ⟨-, -, -, hHomes, -⟩ := DirectJobSelectedGeometry.2 d hlo hhi
  obtain ⟨-, -, -, hCap, hN⟩ := selected_constants d hlo hhi
  refine (term_UFor (geometry31.chunk h) (causalGeometry31 h)
    (by rw [fanout31]; omega) (seed_mod31 h) hTP hCell hT μ tape dtape words hP o ho hd
    (selectedDirectSep d) 256 (selected_referenceCompatible d hlo hhi)
    (DirectJobSelectedGeometry.2 d hlo hhi).1 (by interval_cases d <;> decide)
    hdigit rfl hHomes.symm (selected_home d hlo hhi) (by change (selectedDirectGeometry d).outputCapacity < 256; omega)).trans ?_
  have hden := DirectJobSelectedWordDensity d (by omega) hhi
    (32 * (selectedDirectSep d).N) le_rfl
  have hnum := DirectJobSelectedDensity d _ (by omega) hhi
    (SelJobAux.curDensity_nonneg (selectedDirectSep d) 64 _) hden
  change ENNReal.ofReal ((selectedDirectSep d).curDensity 64 (32 * (selectedDirectSep d).N) *
    Phi 256 (selectedDirectGeometry d).outputHomes 64 32 (selectedDirectGeometry d).outputCapacity) ≤ _
  simpa only [hN, hCap] using ENNReal.ofReal_le_ofReal hnum


theorem term_digitOne (hTP : TracePrefix_statement) (hCell : CausalCell_statement)
    (hT : CausalSetting (geometry31.chunk h) N n m T) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (tape : Ω → FamilyTape (cfg31 h) N)
    (dtape : Ω → DummyTape n m) (words : Ω → Words)
    (hP : OnlineTapePremises (cfg31 h) N n m μ tape dtape words) (o : Nat)
    (ho : JobId.ordinary 1 o ∈ (cfg31 h).potentialJobs) (hd : (cfg31 h).digitAt 1 o = 1) :
    μ {ω | JobFailsFirst (cfg31 h) (sh31 h) (T (tape ω, dtape ω)) (words ω) (.ordinary 1 o)} ≤
      ENNReal.ofReal (1 / (2 : ℝ) ^ 117) := by
  exact (term_digitOneFor (geometry31.chunk h) (causalGeometry31 h) hTP hCell hT
    μ tape dtape words hP o ho hd 256
    (DirectJobSelectedGeometry.1 1 (by decide) (by decide)) rfl
    (by change 4 ≤ 64; decide) rfl (by change 64 < 256; decide)).trans
      (ENNReal.ofReal_le_ofReal DirectJobSelectedExcess.1)

end
end RebuildBound.AdaptiveLevelOneBUProof

open RebuildBound.AdaptiveLevelOneBUProof in
theorem RebuildBound.CausalLevelOneBUStep : RebuildBound.Spec.CausalLevelOneBUStep_statement := by
  intro hTP hCell h _ N n m T hT Ω _ μ _ tape dtape words hP o ho
  exact ⟨fun hd => ⟨term_B h hTP hCell hT μ tape dtape words hP o ho hd,
      term_U h hTP hCell hT μ tape dtape words hP o ho hd⟩,
    fun hd => term_digitOne h hTP hCell hT μ tape dtape words hP o ho hd⟩
