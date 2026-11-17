import RebuildBound.Spec.NativeMatch.TightPublic

/-! Sixteen-byte keys over any number of windows. The error term of
`NativeMatchTightPublicFailure_statement` and
`NativeMatchTightPublicObservation_statement` is `h` times the allocation plus
the normalization cost, and that cost is zero for sixteen-byte keys. -/
namespace RebuildBound.Spec
open NativeMatchProduction NativeMatchEndpoint
open scoped ENNReal

/-- For sixteen-byte keys the error term is below `h * 2^-65`, and so below
`h * 2^-64`, for every number of windows `h ≥ 1`. The statement has no premise
on the run. The two endpoints limit a run to `h` windows through `ctx.Valid`. -/
def NativeMatchSixteenWindowError_statement : Prop :=
  ∀ member, member ∈ ConfigurationFamily.members → ∀ initialized h, 1 ≤ h →
  ∀ (ctx : Context member initialized h),
    NativeMatchTightPublic.error ctx .sixteen <
      (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ)^65) ∧
    NativeMatchTightPublic.error ctx .sixteen <
      (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ)^64)

end RebuildBound.Spec
