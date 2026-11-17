import RebuildBound.Proofs.NativeMatchPublic

/-! Public preflight boundaries and integration with the unchanged native
failure/observation events. All computations use kernel evaluation. -/
namespace RebuildBound.NativeMatchPublicTests
open Model Model.Online Model.Adaptive Spec NativeMatchPhysical NativeMatchProduction
open NativeMatchPublicFit NativeMatchEndpoint NativeMatchApi NativeRoutingActual
open scoped ENNReal

private def unit : OnlineGeom := ⟨64, 2⟩
private def snapshots (consumed : Nat) : Nat → Snapshot 0 := fun _ => ⟨[], consumed⟩

example : publicReady unit (snapshots 0) [] 0 = true := by decide +kernel

/-- A snapshot cannot consume a future prefix before the first probe. -/
example : publicReady unit (snapshots 1) [.probe] 1 = false := by decide +kernel

/-- Blind lanes need no ring plan, even for an otherwise invalid snapshot. -/
example : publicReady unit (snapshots 100) [.blind] 1 = true := by decide +kernel

/-- Exactly two unconsumed prefixes fit; the next unit closes the third. -/
example : publicReady unit (snapshots 0) (List.replicate 384 .probe) 384 = true ∧
    publicReady unit (snapshots 0) (List.replicate 385 .probe) 385 = false := by
  decide +kernel

/-- Chunk lanes retain the starting snapshot across a unit boundary. This
checks the generic model, not a claim that public lowering emits this shape. -/
example : publicReady unit (snapshots 0) (List.replicate 383 .blind ++ [.chunk 2]) 385 = true ∧
    publicReady unit (snapshots 0) (List.replicate 383 .blind ++ [.probe, .probe]) 385 = false := by
  decide +kernel

/- Every certified geometry and both starts pass the arithmetic bounds for
one full certificate window. No context or logical records are enumerated. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
example : ∀ member ∈ ConfigurationFamily.members, ∀ initialized ∈ [false, true],
    let cfg := ((member.geometry initialized).chunk 1).cfg
    (List.range cfg.levels).all (fun i => decide (Model.Hierarchy.time cfg (i + 1)
      (cfg.seed (i + 1) + cfg.ordinals (i + 1)) < 2^48)) = true ∧
    (2^32 : Nat) * maxStride member initialized < 2^64 := by
  decide +kernel

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

/-- Exact exhaustion is rejected: the next finite counter would wrap. -/
example (ctx : Context member initialized h)
    (hb : ctx.accesses * maxStride member initialized = 2^64) :
    ¬ReservationFit ctx := by
  simp [ReservationFit, hb]

/-- Public checking does not inspect initialization keys or values. -/
example (ctx : Context member initialized h) (init : List Rec) :
    NativeMatchPublic.check {ctx with init := init} = NativeMatchPublic.check ctx := rfl

/-- Public checking also does not inspect the adaptive client's choices. -/
example (ctx : Context member initialized h) (choose : ApiLegal.Chooser ctx.geo.cfg
    (ApiAdaptive.shape ctx.frames) ctx.schedule ctx.transcriptWidth) :
    NativeMatchPublic.check {ctx with choose := choose} = NativeMatchPublic.check ctx := rfl

/-- The new endpoint introduces no normalization or ring charge at width 16. -/
example (ctx : Context member initialized h) :
    NativeMatchPublic.error ctx .sixteen =
      (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ)^64) := by
  simp [NativeMatchPublic.error, NativeMatchEndpoint.normalizeCost,
    NativeMatchLinearCoded.normalizeCost]

/-- Width seventeen uses the original complete-message law and failure event,
with one public check in place of separate field/counter/ring assumptions. -/
example (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hh : 1 ≤ h) (hv : ctx.Valid) (hw : InputWidth ctx.client 17)
    (hc : NativeMatchPublic.check ctx = true) (policy : Policy) :
    NativeMatchCoded.law .longer {p | NativeMatchCoded.failure ctx policy .longer p} ≤
      min 1 (NativeMatchPublic.error ctx .longer) :=
  NativeMatchPublicFailure member initialized hm h hh ctx hv .longer 17
    (by simp [Width]) hw hc policy

/-- Both observation directions retain the same law, simulator and single
error allowance at the other supported wide-key boundary. -/
example (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hh : 1 ≤ h) (hv : ctx.Valid) (hw : InputWidth ctx.client 64)
    (hc : NativeMatchPublic.check ctx = true) (policy : Policy)
    (event : Set (View ctx)) (he : MeasurableSet event) :
    NativeMatchCoded.law .longer ((NativeMatchCoded.observed ctx policy .longer) ⁻¹' event) ≤
      min 1 (simulator ctx event + NativeMatchPublic.error ctx .longer) ∧
    simulator ctx event ≤
      min 1 (NativeMatchCoded.law .longer
        ((NativeMatchCoded.observed ctx policy .longer) ⁻¹' event) +
          NativeMatchPublic.error ctx .longer) :=
  NativeMatchPublicObservation member initialized hm h hh ctx hv .longer 64
    (by simp [Width]) hw hc policy event he

end RebuildBound.NativeMatchPublicTests
