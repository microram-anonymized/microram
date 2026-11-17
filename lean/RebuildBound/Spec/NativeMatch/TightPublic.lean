import RebuildBound.Spec.NativeMatch.Public
import RebuildBound.Spec.NativeMatch.TightBudget

/-! Additive complete-message bounds with the refined, unrounded allocation.
The all-window endpoints retain their existing birthday normalization term.
The finite-window corollary includes initialization in its public run limit;
it is not a proof of an arbitrary-horizon linear collision allowance. -/
namespace RebuildBound.Spec.NativeMatchTightPublic
open NativeMatchProduction NativeMatchEndpoint
open scoped ENNReal

noncomputable def allocation (member : ConfigurationFamily.Member) (initialized : Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (NativeMatchTightBudget.exposureBudget member : ℝ) +
    (NativeMatchInventory.weight member initialized : ℝ≥0∞) / (2 : ℝ≥0∞)^128

noncomputable def error {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (model : KeyModel) : ℝ≥0∞ :=
  (h : ℝ≥0∞) * allocation member initialized + normalizeCost ctx model

end RebuildBound.Spec.NativeMatchTightPublic

namespace RebuildBound.Spec
open Model NativeMatchProduction NativeMatchApi NativeMatchEndpoint NativeRoutingActual
open MeasureTheory
open scoped ENNReal

def NativeMatchTightAdaptiveCapacity_statement : Prop :=
  ∀ member initialized, member ∈ ConfigurationFamily.members → ∀ h, 1 ≤ h →
  ∀ ctx : Context member initialized h, ctx.Valid →
    IdealKey.tapeLaw {tape | ctx.capacityBad tape} ≤
      (h : ℝ≥0∞) * ENNReal.ofReal (NativeMatchTightBudget.exposureBudget member : ℝ)

/-- The refined exact rational export is the endpoint's capacity-plus-matching
allocation, with no normalization charge included. -/
def NativeMatchTightPublicAllocation_statement : Prop :=
  ∀ member, member ∈ ConfigurationFamily.members → ∀ initialized,
    NativeMatchTightPublic.allocation member initialized =
      ENNReal.ofReal (NativeMatchTightBudget.allocation member initialized : ℝ)

def NativeMatchTightPublicFailure_statement : Prop :=
  ∀ member initialized, member ∈ ConfigurationFamily.members → ∀ h, 1 ≤ h →
  ∀ (ctx : Context member initialized h), ctx.Valid →
  ∀ model width, Width model width → InputWidth ctx.client width →
  NativeMatchPublic.check ctx = true → ∀ policy,
  NativeMatchCoded.law model {p | NativeMatchCoded.failure ctx policy model p} ≤
    min 1 (NativeMatchTightPublic.error ctx model)

def NativeMatchTightPublicObservation_statement : Prop :=
  ∀ member initialized, member ∈ ConfigurationFamily.members → ∀ h, 1 ≤ h →
  ∀ (ctx : Context member initialized h), ctx.Valid →
  ∀ model width, Width model width → InputWidth ctx.client width →
  NativeMatchPublic.check ctx = true → ∀ policy (event : Set (View ctx)), MeasurableSet event →
  NativeMatchCoded.law model ((NativeMatchCoded.observed ctx policy model) ⁻¹' event) ≤
    min 1 (simulator ctx event + NativeMatchTightPublic.error ctx model) ∧
  simulator ctx event ≤
    min 1 (NativeMatchCoded.law model ((NativeMatchCoded.observed ctx policy model) ⁻¹' event) +
      NativeMatchTightPublic.error ctx model)

/-- For one through four half-size windows, the original birthday term still
fits the strict per-window target. Initialization consumes the same run limit. -/
def NativeMatchTightWindowError_statement : Prop :=
  ∀ member, member ∈ ConfigurationFamily.members → ∀ initialized h,
    1 ≤ h → h ≤ 4 → ∀ (ctx : Context member initialized h),
    ctx.init.length + ctx.accesses ≤ h * 2 ^ 31 → ∀ model,
    NativeMatchTightPublic.error ctx model <
      (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ)^64)

end RebuildBound.Spec
