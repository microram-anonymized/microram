import RebuildBound.Proofs.NativeMatchLivePublic.NativeLiveSummary
import RebuildBound.Proofs.NativeMatchLivePublic.NativeLiveFailureGuard
import RebuildBound.Spec.NativeMatch.LivePublic

namespace RebuildBound.NativeLiveFailureProbability
open Model Model.Api Spec MeasureTheory
open Spec.NativeMatchProduction Spec.NativeMatch Spec.NativeNormalize Spec.NativeNormalizePairs Spec.NativeMatchLivePairs
open NativeCollapsedLiveBound NativeCollapsedTotal NativeLiveSummary NativeLiveSampleTransport NativeNormalizeEncode16Proof
open scoped ENNReal
local instance (α : Type) : MeasurableSpace (List α) := ⊤
attribute [local irreducible] NativeCollapsedLiveBound.logicalRequests
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

def failureEvent (ctx : Context member initialized h) : Set (Joint ctx) :=
  {p | p.2.2.1=true ∨ PairBad p.1 (pairs (stateOf ctx.codec ctx.init) (ctx.init.map Rec.key)
    (logicalRequests ctx p.2.2.2))}

lemma failureEvent_measurable (ctx : Context member initialized h) : MeasurableSet (failureEvent ctx) := by
  have hb : MeasurableSet {p : Joint ctx | p.2.2.1=true} :=
    measurable_snd.snd.fst (measurableSet_singleton true)
  have hp : MeasurableSet {p : (Fin ctx.accesses → Fin ctx.transcriptWidth → Nat) × Tape 128 |
      PairBad p.2 (pairs (stateOf ctx.codec ctx.init) (ctx.init.map Rec.key) (logicalRequests ctx p.1))} :=
    NativeNormalizePairsMeasurable 128 _ (fun ps =>
      (measurable_of_countable (fun rows=>pairs (stateOf ctx.codec ctx.init) (ctx.init.map Rec.key)
        (logicalRequests ctx rows))) (measurableSet_singleton ps))
  have hd : Measurable (fun p : Joint ctx=>(p.2.2.2,p.1)) := measurable_snd.snd.snd.prodMk measurable_fst
  have hm := hp.preimage hd
  exact hb.union hm

lemma failureEvent_bound (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (hc : NativeMatchPublic.check ctx=true) :
    augLaw (actualJoint ctx ⁻¹' failureEvent ctx) ≤ NativeMatchLivePublic.failureError ctx := by
  rw [summary_event ctx hm hv hc _ (failureEvent_measurable ctx)]
  have hf : NativeLiveSummary.keyMap = (fun seed key=>encode16 (seed key)) := rfl
  have he : idealJoint ctx ⁻¹' failureEvent ctx = {p | totalBad ctx encode16 p} := by
    ext p
    simp only [Set.mem_preimage, failureEvent, Set.mem_setOf_eq, idealJoint, summary,
      decide_eq_true_eq, totalBad, liveBad, hf]
  rw [he]
  exact totalBad_bound ctx hm hh hv encode16 encode16_length

lemma failure (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (hc : NativeMatchPublic.check ctx=true)
    (policy : NativeMatchApi.Policy) :
    NativeMatchCoded.law .longer {p | NativeMatchSemantic.failure ctx policy .longer p} ≤
      min 1 (NativeMatchLivePublic.failureError ctx) := by
  letI : IsProbabilityMeasure (NativeMatchCoded.law .longer) := by
    unfold NativeMatchCoded.law NativeMatchEndpoint.noiseLaw
    infer_instance
  apply le_min prob_le_one
  rw [←nativeSample_event {p | NativeMatchSemantic.failure ctx policy .longer p}]
  apply (measure_mono ?_).trans (failureEvent_bound ctx hm hh hv hc)
  intro p hp
  exact NativeLiveFailureGuard.failure_envelope ctx hm hv hc policy p hp

end RebuildBound.NativeLiveFailureProbability


namespace RebuildBound
 theorem NativeMatchLivePublicFailure : Spec.NativeMatchLivePublicFailure_statement := by
  intro member initialized hm h hh ctx hv width hwidth hw hc policy
  exact NativeLiveFailureProbability.failure ctx hm hh hv hc policy
end RebuildBound
