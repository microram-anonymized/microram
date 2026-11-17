import RebuildBound.Proofs.NativeMatchSixteenWindow

/-! Sixteen-byte keys at every number of windows: the error bound composes in
one step with the refined failure and observation endpoints, at every
`h ≥ 1`. The context is a hypothesis; no concrete context is built here. -/
namespace NativeMatchSixteenWindowTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Online
open NativeMatchProduction NativeMatchEndpoint NativeMatchApi NativeRoutingActual
open scoped ENNReal

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

/-- With sixteen-byte keys, the failure probability of the complete-message
law is below `h * 2^-64` for every number of windows `h ≥ 1`. -/
theorem failure_lt (hm : member ∈ ConfigurationFamily.members) (hh : 1 ≤ h)
    (ctx : Context member initialized h) (hv : ctx.Valid) (hw : InputWidth ctx.client 16)
    (hc : NativeMatchPublic.check ctx = true) (policy : Policy) :
    NativeMatchCoded.law .sixteen {p | NativeMatchCoded.failure ctx policy .sixteen p} <
      (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ)^64) :=
  (NativeMatchTightPublicFailure member initialized hm h hh ctx hv .sixteen 16 rfl hw hc
    policy).trans_lt ((min_le_right _ _).trans_lt
      (NativeMatchSixteenWindowError member hm initialized h hh ctx).2)

/-- With sixteen-byte keys, the observed view and the simulator differ by at
most `h * 2^-64` on every measurable event, in both directions, for every
number of windows `h ≥ 1`. -/
theorem observation_le (hm : member ∈ ConfigurationFamily.members) (hh : 1 ≤ h)
    (ctx : Context member initialized h) (hv : ctx.Valid) (hw : InputWidth ctx.client 16)
    (hc : NativeMatchPublic.check ctx = true) (policy : Policy)
    (event : Set (View ctx)) (he : MeasurableSet event) :
    NativeMatchCoded.law .sixteen ((NativeMatchCoded.observed ctx policy .sixteen) ⁻¹' event) ≤
      simulator ctx event + (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ)^64) ∧
    simulator ctx event ≤
      NativeMatchCoded.law .sixteen ((NativeMatchCoded.observed ctx policy .sixteen) ⁻¹' event) +
        (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ)^64) := by
  have ho := NativeMatchTightPublicObservation member initialized hm h hh ctx hv .sixteen 16 rfl
    hw hc policy event he
  have he64 := (NativeMatchSixteenWindowError member hm initialized h hh ctx).2.le
  exact ⟨ho.1.trans ((min_le_right _ _).trans (add_le_add le_rfl he64)),
    ho.2.trans ((min_le_right _ _).trans (add_le_add le_rfl he64))⟩

end NativeMatchSixteenWindowTests
