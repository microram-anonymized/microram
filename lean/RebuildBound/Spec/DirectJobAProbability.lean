import RebuildBound.Spec.DirectJobANumerics
import RebuildBound.Spec.DirectJobProbability
import RebuildBound.Spec.DirectJobBudget
import RebuildBound.Spec.SelTotal

open scoped ENNReal NNReal
namespace RebuildBound.Spec
open Model Model.DirectJob

/-- Digit one has no A phase. Later selected rows use the checked conservative
A budget. This definition asserts no input-law or native applicability fact. -/
noncomputable def selectedDirectABudget (d : Nat) : ℝ≥0∞ :=
  if d = 1 then 0 else ENNReal.ofReal (1 / (2 : ℝ) ^ 102)

/-- Instantiate the shared A law on its original unconditional history/word
space. Only A main/tier inputs are matched; B production success is not assumed. -/
def DirectJobSelectedAProbability_statement : Prop :=
  ∀ d, 2 ≤ d → d ≤ 8 →
    ∀ (L : SJobLaw (selectedDirectSep d)) (D : ℝ≥0),
    SInputLaw L 32 D → L.W = 64 →
    D ≤ (selectedDirectSep d).oldDensity 64 (32 * (((selectedDirectSep d).d - 1) *
      (selectedDirectSep d).U)) →
    ∀ direct : L.Hist → (LogicalKey → Nat) → DirectJob.Inputs,
    (∀ hist hw, (direct hist (L.wordFn hw)).aMain = (L.inputs hist (L.wordFn hw)).aMain ∧
      (direct hist (L.wordFn hw)).aTier = (L.inputs hist (L.wordFn hw)).aTier) →
    L.prob (fun hist word =>
      (direct hist word).aTier.length ≤ (selectedDirectGeometry d).aTierCapacity ∧
      (aRouteWitness (selectedDirectGeometry d) word (direct hist word) ∨
        aRangeWitness (selectedDirectGeometry d) word (direct hist word))) ≤ selectedDirectABudget d

/-- SelTotal's right-hand side with level one's per-digit budget
`selectedDirectBound selectedDirectABudget` (the bound `DirectJobHierarchy`
closes). Source/history, event transport and coverage are not asserted here. -/
noncomputable def selectedDirectLifetimeBudget (cfg : Config) : ℝ≥0∞ :=
  ENNReal.ofReal (129 / (100 * 2 ^ 70)) + 258 * ENNReal.ofReal (1 / 2 ^ 115) +
    ((List.range (cfg.fanout 1)).map fun i =>
      (cfg.ordinaryCount 1 (i + 1) : ℝ≥0∞) *
        selectedDirectBound selectedDirectABudget (i + 1)).sum

def DirectJobSelectedLifetimeNumerics_statement : Prop :=
  selectedDirectLifetimeBudget uniformConfig ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 69) ∧
  selectedDirectLifetimeBudget halfFanoutConfig ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 69)

end RebuildBound.Spec
