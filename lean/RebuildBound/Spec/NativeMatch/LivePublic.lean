import RebuildBound.Spec.NativeMatch.Semantic
import RebuildBound.Spec.NativeMatch.TightPublic
import RebuildBound.Spec.NativeMatch.LivePairs

/-! Additive long-key guarantees with a linear live-key collision allowance.
The semantic endpoint retains logical replies and prefix maps. Physical
addresses retain a separate distributional observation guarantee. Initial
aliases are charged in both guarantees because native initialization does not
collapse repeated stored keys. Initialization consumes the run allowance. -/
namespace RebuildBound.Spec.NativeMatchLivePublic
open NativeMatchProduction NativeNormalizePairs
open scoped ENNReal

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

noncomputable def failureError (ctx : Context member initialized h) : ℝ≥0∞ :=
  (h : ℝ≥0∞) * NativeMatchTightPublic.allocation member initialized +
    pairBound 128 (ctx.init.length.choose 2 + ctx.accesses * ctx.geo.keyCapacity)

noncomputable def observationError (ctx : Context member initialized h) : ℝ≥0∞ :=
  (h : ℝ≥0∞) * NativeMatchTightPublic.allocation member initialized +
    pairBound 128 (ctx.init.length.choose 2)

end RebuildBound.Spec.NativeMatchLivePublic

namespace RebuildBound.Spec
open Model NativeMatchProduction NativeMatchApi NativeMatchEndpoint NativeRoutingActual
open MeasureTheory
open scoped ENNReal

def NativeMatchLivePublicFailure_statement : Prop :=
  ∀ member initialized, member ∈ ConfigurationFamily.members → ∀ h, 1 ≤ h →
  ∀ (ctx : Context member initialized h), ctx.Valid →
  ∀ width, Width .longer width → InputWidth ctx.client width →
  NativeMatchPublic.check ctx = true → ∀ policy,
  NativeMatchCoded.law .longer {p | NativeMatchSemantic.failure ctx policy .longer p} ≤
    min 1 (NativeMatchLivePublic.failureError ctx)

def NativeMatchLivePublicObservation_statement : Prop :=
  ∀ member initialized, member ∈ ConfigurationFamily.members → ∀ h, 1 ≤ h →
  ∀ (ctx : Context member initialized h), ctx.Valid →
  ∀ width, Width .longer width → InputWidth ctx.client width →
  NativeMatchPublic.check ctx = true → ∀ policy (event : Set (View ctx)), MeasurableSet event →
  NativeMatchCoded.law .longer ((NativeMatchCoded.observed ctx policy .longer) ⁻¹' event) ≤
    min 1 (simulator ctx event + NativeMatchLivePublic.observationError ctx) ∧
  simulator ctx event ≤
    min 1 (NativeMatchCoded.law .longer ((NativeMatchCoded.observed ctx policy .longer) ⁻¹' event) +
      NativeMatchLivePublic.observationError ctx)

/-- Every h is covered; there is no upper bound on the number of windows.
The additional capacity premise is the paper's N ≤ 2^31 limit. -/
def NativeMatchLiveWindowError_statement : Prop :=
  ∀ member, member ∈ ConfigurationFamily.members → ∀ initialized h, 1 ≤ h →
  ∀ (ctx : Context member initialized h), ctx.Valid → ctx.geo.keyCapacity ≤ 2^31 →
  ctx.init.length + ctx.accesses ≤ h * 2^31 →
    NativeMatchLivePublic.failureError ctx <
      (h : ℝ≥0∞) * ENNReal.ofReal (3 / (4 * (2 : ℝ)^64)) ∧
    NativeMatchLivePublic.failureError ctx <
      (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ)^64) ∧
    NativeMatchLivePublic.observationError ctx ≤ NativeMatchLivePublic.failureError ctx

end RebuildBound.Spec
