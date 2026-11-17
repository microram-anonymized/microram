import RebuildBound.Proofs.NativeMatchLivePublic.NativeLiveSummary
import RebuildBound.Proofs.NativeMatchLivePublic.NativeCollapsedObservation
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyObservationGuard
import RebuildBound.Spec.NativeMatch.LivePublic

namespace RebuildBound.NativeLiveObservationPublic
open Model Spec MeasureTheory NativeMatchProduction NativeMatchEndpoint NativeNormalize NativeNormalizePairs
open NativeMatchLivePairs NativeNormalizeEncode16Proof NativeLiveSampleTransport NativeLiveSummary
open scoped ENNReal
set_option maxHeartbeats 400000
attribute [local irreducible] NativeCollapsedMeasurable.referenceTranscript summary
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

def badEvent (ctx : Context member initialized h) : Set (Joint ctx) :=
  {p | p.2.2.1=true ∨ PairBad p.1 (initialPairs (ctx.init.map Rec.key))}

def proxyView (ctx : Context member initialized h) (p : Joint ctx) : View ctx := some p.2.2.2

lemma badEvent_measurable (ctx : Context member initialized h) : MeasurableSet (badEvent ctx) :=
  (measurableSet_eq_fun measurable_snd.snd.fst measurable_const).union
    ((NativeNormalizePairsProof.section_measurable 128 _).preimage measurable_fst)

lemma proxyView_measurable (ctx : Context member initialized h) : Measurable (proxyView ctx) :=
  (measurable_of_countable some).comp measurable_snd.snd.snd

lemma bad_bound (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (hc : NativeMatchPublic.check ctx=true) :
    augLaw (actualJoint ctx ⁻¹' badEvent ctx) ≤ NativeMatchLivePublic.observationError ctx := by
  rw [summary_event ctx hm hv hc _ (badEvent_measurable ctx)]
  have he : idealJoint ctx ⁻¹' badEvent ctx =
      {p | NativeCollapsedObservation.observationBad ctx encode16 p} := by
    ext p
    simp only [Set.mem_preimage,Set.mem_setOf_eq,badEvent,idealJoint,summary,
      decide_eq_true_eq,NativeCollapsedObservation.observationBad,NativeCollapsedObservation.initialBad,
      Function.comp_def]
    rw [show NativeLiveSummary.keyMap = (fun seed key=>encode16 (seed key)) from rfl]
  rw [he]
  exact NativeCollapsedObservation.observationBad_bound ctx hm hh hv encode16 encode16_length

lemma proxy_law (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (hc : NativeMatchPublic.check ctx=true)
    (event : Set (View ctx)) (hevent : MeasurableSet event) :
    augLaw ((proxyView ctx ∘ actualJoint ctx) ⁻¹' event) = simulator ctx event := by
  have he := summary_event ctx hm hv hc ((proxyView ctx) ⁻¹' event)
    (hevent.preimage (proxyView_measurable ctx))
  change augLaw ((proxyView ctx ∘ actualJoint ctx) ⁻¹' event) =
    NativeCollapsedTotal.law ((proxyView ctx ∘ idealJoint ctx) ⁻¹' event) at he
  rw [he,←Measure.map_apply ((proxyView_measurable ctx).comp (idealJoint_measurable ctx)) hevent]
  simp only [Function.comp_def,proxyView,idealJoint,summary]
  rw [show NativeLiveSummary.keyMap = (fun seed key=>encode16 (seed key)) from rfl]
  exact congrArg (fun μ=>μ event) (NativeCollapsedObservation.view_law ctx hm hv encode16)

lemma observation (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (hc : NativeMatchPublic.check ctx=true)
    (policy : NativeMatchApi.Policy) (event : Set (View ctx)) (hevent : MeasurableSet event)
    (hguard : ∀ p : AugSample,p ∉ actualJoint ctx ⁻¹' badEvent ctx →
      NativeMatchCoded.observed ctx policy .longer (nativeSample p) = proxyView ctx (actualJoint ctx p)) :
    NativeMatchCoded.law .longer ((NativeMatchCoded.observed ctx policy .longer) ⁻¹' event) ≤
      min 1 (simulator ctx event + NativeMatchLivePublic.observationError ctx) ∧
    simulator ctx event ≤ min 1
      (NativeMatchCoded.law .longer ((NativeMatchCoded.observed ctx policy .longer) ⁻¹' event) +
        NativeMatchLivePublic.observationError ctx) := by
  let actual := fun p : AugSample => NativeMatchCoded.observed ctx policy .longer (nativeSample p)
  let proxy := proxyView ctx ∘ actualJoint ctx
  let bad := actualJoint ctx ⁻¹' badEvent ctx
  have hleft : actual ⁻¹' event ⊆ proxy ⁻¹' event ∪ bad := by
    intro p hp
    by_cases hb : p∈bad
    · exact Or.inr hb
    · left
      change proxyView ctx (actualJoint ctx p) ∈ event
      rwa [←hguard p hb]
  have hright : proxy ⁻¹' event ⊆ actual ⁻¹' event ∪ bad := by
    intro p hp
    by_cases hb : p∈bad
    · exact Or.inr hb
    · left
      change NativeMatchCoded.observed ctx policy .longer (nativeSample p) ∈ event
      rwa [hguard p hb]
  have hn : augLaw (actual ⁻¹' event) =
      NativeMatchCoded.law .longer ((NativeMatchCoded.observed ctx policy .longer) ⁻¹' event) :=
    nativeSample_event ((NativeMatchCoded.observed ctx policy .longer) ⁻¹' event)
  have hp : augLaw (proxy ⁻¹' event)=simulator ctx event := proxy_law ctx hm hv hc event hevent
  have hb : augLaw bad ≤ NativeMatchLivePublic.observationError ctx := bad_bound ctx hm hh hv hc
  letI : IsProbabilityMeasure augLaw := by unfold augLaw; infer_instance
  rw [←hn,←hp]
  exact ⟨le_min prob_le_one ((measure_mono hleft).trans
    ((measure_union_le _ _).trans (add_le_add le_rfl hb))),
    le_min prob_le_one ((measure_mono hright).trans
    ((measure_union_le _ _).trans (add_le_add le_rfl hb)))⟩

end RebuildBound.NativeLiveObservationPublic

namespace RebuildBound
open Spec NativeMatchProduction NativeMatchEndpoint NativeNormalize NativeNormalizePairs NativeMatchLivePairs
open NativeCollapsedBudget NativeNormalizeEncode16Proof NativeLiveSampleTransport NativeLiveSummary
open NativeLiveObservationPublic

theorem NativeMatchLivePublicObservation : Spec.NativeMatchLivePublicObservation_statement := by
  intro member initialized hm h hh ctx hv width _ _ hc policy event hevent
  apply observation ctx hm hh hv hc policy event hevent
  intro p hb
  change ¬((summary ctx p.1 p.2.1 (routed ctx p.2.1 p.2.2)).1=true ∨
    PairBad p.1 (initialPairs (ctx.init.map Model.Rec.key))) at hb
  simp only [summary,decide_eq_true_eq] at hb
  exact NativeRekeyObservationGuard.observed_off_bad ctx hm hv hc policy p.1 p.2.1 p.2.2
    (fun hi=>hb (Or.inr hi)) (fun hc=>hb (Or.inl hc))

end RebuildBound
