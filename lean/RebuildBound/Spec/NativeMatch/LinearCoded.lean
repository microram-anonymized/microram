import RebuildBound.Spec.NativeMatch.LocalBound

/-! Complete-message ideal endpoints with one actual-access normalization
allowance. The existing birthday endpoints remain available; their comparison
uses the same failure/observation events and does not add error allowances. -/
namespace RebuildBound.Spec.NativeMatchLinearCoded
open NativeMatchProduction NativeMatchEndpoint
open scoped ENNReal

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

noncomputable def normalizeCost (ctx : Context member initialized h) : KeyModel → ℝ≥0∞
  | .sixteen => 0
  | .longer => NativeMatchLocalBound.normalizeCost ctx

noncomputable def error (ctx : Context member initialized h) (model : KeyModel) : ℝ≥0∞ :=
  (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ)^64) + normalizeCost ctx model +
    NativeMatchCoded.ringCost ctx

noncomputable def bestError (ctx : Context member initialized h) (model : KeyModel) : ℝ≥0∞ :=
  (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ)^64) +
    min (NativeMatchEndpoint.normalizeCost ctx model) (normalizeCost ctx model) +
      NativeMatchCoded.ringCost ctx

end RebuildBound.Spec.NativeMatchLinearCoded

namespace RebuildBound.Spec
open Model NativeMatchProduction NativeMatchApi NativeMatchEndpoint NativeRoutingActual
open NativeMatchRoutingBudget MeasureTheory
open scoped ENNReal

def NativeMatchLinearCodedFailure_statement : Prop :=
  ∀ member initialized, member ∈ ConfigurationFamily.members → ∀ h, 1 ≤ h →
  ∀ (ctx : Context member initialized h), ctx.Valid →
  ∀ model width, Width model width → InputWidth ctx.client width →
  FieldsFit ctx → CounterFit ctx → ∀ policy,
  NativeMatchCoded.law model {p | NativeMatchCoded.failure ctx policy model p} ≤
    min 1 (NativeMatchLinearCoded.error ctx model)

def NativeMatchLinearCodedObservation_statement : Prop :=
  ∀ member initialized, member ∈ ConfigurationFamily.members → ∀ h, 1 ≤ h →
  ∀ (ctx : Context member initialized h), ctx.Valid →
  ∀ model width, Width model width → InputWidth ctx.client width →
  FieldsFit ctx → CounterFit ctx → ∀ policy (event : Set (View ctx)), MeasurableSet event →
  NativeMatchCoded.law model ((NativeMatchCoded.observed ctx policy model) ⁻¹' event) ≤
    min 1 (simulator ctx event + NativeMatchLinearCoded.error ctx model) ∧
  simulator ctx event ≤
    min 1 (NativeMatchCoded.law model ((NativeMatchCoded.observed ctx policy model) ⁻¹' event) +
      NativeMatchLinearCoded.error ctx model)

/-- Both certified endpoints concern the identical complete-message event. -/
def NativeMatchBestCodedFailure_statement : Prop :=
  ∀ member initialized, member ∈ ConfigurationFamily.members → ∀ h, 1 ≤ h →
  ∀ (ctx : Context member initialized h), ctx.Valid →
  ∀ model width, Width model width → InputWidth ctx.client width →
  FieldsFit ctx → CounterFit ctx → ∀ policy,
  NativeMatchCoded.law model {p | NativeMatchCoded.failure ctx policy model p} ≤
    min 1 (NativeMatchLinearCoded.bestError ctx model)

/-- Each observation direction uses the better normalization allowance once. -/
def NativeMatchBestCodedObservation_statement : Prop :=
  ∀ member initialized, member ∈ ConfigurationFamily.members → ∀ h, 1 ≤ h →
  ∀ (ctx : Context member initialized h), ctx.Valid →
  ∀ model width, Width model width → InputWidth ctx.client width →
  FieldsFit ctx → CounterFit ctx → ∀ policy (event : Set (View ctx)), MeasurableSet event →
  NativeMatchCoded.law model ((NativeMatchCoded.observed ctx policy model) ⁻¹' event) ≤
    min 1 (simulator ctx event + NativeMatchLinearCoded.bestError ctx model) ∧
  simulator ctx event ≤
    min 1 (NativeMatchCoded.law model ((NativeMatchCoded.observed ctx policy model) ⁻¹' event) +
      NativeMatchLinearCoded.bestError ctx model)

end RebuildBound.Spec
