import RebuildBound.Spec.NativeMatch.PublicFit
import RebuildBound.Spec.NativeMatch.Ring

/-! Complete-message endpoints with one finite public check. The check uses
only geometry, access shape and publication snapshots. It certifies the model's
family encoding, dummy reservations and ring readiness; native scheduler and
compiled-execution correspondence remain separate obligations. -/
namespace RebuildBound.Spec.NativeMatchPublic
open Model Model.Hierarchy NativeMatchProduction NativeMatchPublicFit NativeMatchPhysical
open NativeMatchEndpoint
open scoped ENNReal

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

/-- A sufficient public check, with no routing words, stored keys or logical
requests as inputs. The family-time and reservation bounds are conservative;
failure of this check alone does not imply an encoding error. Ring readiness
is checked at every probing position in the supplied public shape. -/
def check (ctx : Context member initialized h) : Bool :=
  (List.range ctx.geo.cfg.levels).all (fun i =>
    decide (time ctx.geo.cfg (i + 1)
      (ctx.geo.cfg.seed (i + 1) + ctx.geo.cfg.ordinals (i + 1)) < 2^48)) &&
  decide (ctx.accesses * maxStride member initialized < 2^64) &&
  publicReady ctx.unit ctx.snapshots (ApiAdaptive.shape ctx.frames) ctx.accesses

noncomputable def error (ctx : Context member initialized h) (model : KeyModel) : ℝ≥0∞ :=
  (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ)^64) +
    min (NativeMatchEndpoint.normalizeCost ctx model)
      (NativeMatchLinearCoded.normalizeCost ctx model)

end RebuildBound.Spec.NativeMatchPublic

namespace RebuildBound.Spec
open Model NativeMatchProduction NativeMatchApi NativeMatchEndpoint NativeRoutingActual
open NativeMatchRoutingBudget MeasureTheory
open scoped ENNReal

/-- Public check soundness is separate from the probabilistic endpoint. -/
def NativeMatchPublicChecks_statement : Prop :=
  ∀ member initialized h (ctx : Context member initialized h),
    member ∈ ConfigurationFamily.members → ctx.Valid → NativeMatchPublic.check ctx = true →
    FieldsFit ctx ∧ CounterFit ctx ∧ NativeMatchCoded.ringCost ctx = 0

def NativeMatchPublicFailure_statement : Prop :=
  ∀ member initialized, member ∈ ConfigurationFamily.members → ∀ h, 1 ≤ h →
  ∀ (ctx : Context member initialized h), ctx.Valid →
  ∀ model width, Width model width → InputWidth ctx.client width →
  NativeMatchPublic.check ctx = true → ∀ policy,
  NativeMatchCoded.law model {p | NativeMatchCoded.failure ctx policy model p} ≤
    min 1 (NativeMatchPublic.error ctx model)

def NativeMatchPublicObservation_statement : Prop :=
  ∀ member initialized, member ∈ ConfigurationFamily.members → ∀ h, 1 ≤ h →
  ∀ (ctx : Context member initialized h), ctx.Valid →
  ∀ model width, Width model width → InputWidth ctx.client width →
  NativeMatchPublic.check ctx = true → ∀ policy (event : Set (View ctx)), MeasurableSet event →
  NativeMatchCoded.law model ((NativeMatchCoded.observed ctx policy model) ⁻¹' event) ≤
    min 1 (simulator ctx event + NativeMatchPublic.error ctx model) ∧
  simulator ctx event ≤
    min 1 (NativeMatchCoded.law model ((NativeMatchCoded.observed ctx policy model) ⁻¹' event) +
      NativeMatchPublic.error ctx model)

end RebuildBound.Spec
