import RebuildBound.Proofs.NativeMatchLivePublic.NativeCollapsedTotal
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyCodedGuard

namespace RebuildBound.NativeRekeyObservationGuard
open Model Spec NativeMatchProduction NativeNormalize NativeNormalizePairs NativeMatchLivePairs
open NativeNormalizeLiveApi NativeNormalizeCollapsed NativeCollapsedMeasurable NativeCollapsedBudget
open NativeNormalizeEncode16Proof NativeRekeyCodedGuard

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

lemma initial_nodup (ctx : Context member initialized h) (hv : ctx.Valid) (f : Tape 128)
    (hi : ¬PairBad f (initialPairs (ctx.init.map Rec.key))) :
    ((ctx.init.map (mapRec (encode16 ∘ f))).map Rec.key).Nodup := by
  have hn := NativeCollapsedLiveBound.initial_mapped_nodup f (ctx.init.map Rec.key) hv.1.1 hi
  have he := hn.map encode16_injective
  simpa only [List.map_map,Function.comp_def,mapRec] using he

lemma observed_off_bad (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (hc : NativeMatchPublic.check ctx=true) (policy : NativeMatchApi.Policy)
    (f : Tape 128) (σ : Equiv.Perm (Fingerprint 128)) (routing : Tape 64)
    (hi : ¬PairBad f (initialPairs (ctx.init.map Rec.key)))
    (hb : ¬canonicalBad ctx (fun f=>encode16 ∘ f) f σ
      (NativeMatchCoded.routing ctx .sixteen (((),σ),routing))) :
    NativeMatchCoded.observed ctx policy .longer (((),σ ∘ f),routing) =
      some (referenceTranscript ctx (fun f=>encode16 ∘ f) f
        (NativeMatchCoded.routing ctx .sixteen (((),σ),routing))) := by
  have hn := initial_nodup ctx hv f hi
  have he := collapsed_eq ctx (encode16 ∘ f) hn
  have hbad : ¬((rekey ctx (encode16 ∘ f)).capacityBad
        (NativeMatchCoded.routing (rekey ctx (encode16 ∘ f)) .sixteen (((),σ),routing)) ∨
      ∃ e∈(rekey ctx (encode16 ∘ f)).inventory
        (NativeMatchCoded.routing (rekey ctx (encode16 ∘ f)) .sixteen (((),σ),routing)),
        e.bad (fun key=>σ (NativeMatchTrace.block16 key))) := by
    unfold canonicalBad at hb
    rw [he] at hb
    exact hb
  have ho := coded_observed_off_bad ctx hm hv f σ routing hn hc policy hbad
  refine ho.trans ?_
  have hinit : (collapsedRekey ctx (encode16 ∘ f)).init=(rekey ctx (encode16 ∘ f)).init :=
    congrArg Context.init he
  have hclient : (collapsedRekey ctx (encode16 ∘ f)).client=(rekey ctx (encode16 ∘ f)).client := by
    change ApiAdaptive.run _ _ _ _ _ (DirectPrefix.winners _) _ _ = ApiAdaptive.run _ _ _ _ _ _ _ _
    rw [show DirectPrefix.winners (ctx.init.map (mapRec (encode16 ∘ f)))=
      ctx.init.map (mapRec (encode16 ∘ f)) from hinit]
    rfl
  unfold referenceTranscript
  rw [hclient]
  rfl

end RebuildBound.NativeRekeyObservationGuard
