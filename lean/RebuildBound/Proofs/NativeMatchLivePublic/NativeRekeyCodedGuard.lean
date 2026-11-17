import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyApiGuard
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeySummaryGuards
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyCodedRouting
import RebuildBound.Proofs.NativeMatchEndpoint

set_option maxHeartbeats 2000000

namespace RebuildBound.NativeRekeyCodedGuard
open Model Spec NativeMatchProduction NativeMatchApi NativeNormalize NativeRoutingActual NativeRoutingCoupling
open NativeMatch NativeMatchTrace NativeNormalizeLiveApi NativeRekeyHierarchyBase NativeNormalizeLiveApiProof NativeRekeySummaryGuards

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

lemma production_off_bad (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (f : LogicalKey→LogicalKey) (hwidth : ∀ key,(f key).length=16)
    (hi : ((ctx.init.map (mapRec f)).map Rec.key).Nodup)
    (hc : NativeMatchPublic.check ctx=true) (policy : Policy)
    (s : LogicalKey→NativeMatch.Lanes.Stored) (σ : Equiv.Perm (Fingerprint 128))
    (hs : ∀ key,NativeMatchCoded.stored .sixteen σ (f key)=s key)
    (tape tape' : IdealKey.Tape) (hw : WordsRel f (IdealHierarchy.words tape) (IdealHierarchy.words tape'))
    (hd : IdealHierarchy.dummy tape=IdealHierarchy.dummy tape')
    (hbad : ¬((rekey ctx f).capacityBad tape' ∨
      ∃ e∈(rekey ctx f).inventory tape',e.bad (fun key=>σ (block16 key)))) :
    ∃ out, production ctx policy s tape=.ok out ∧
      NativeRekeyApi.state f out=reference (rekey ctx f) tape' ∧
      out.requests=(ApiAdaptive.requestGroups ctx.compiled (NativeMatchApiReference.rows (rekey ctx f) tape')
        ctx.frames).flatMap PublicApi.Group.lanes := by
  let cc := rekey ctx f
  have hv' : cc.Valid := valid_rekey ctx f hv hi
  have hc' : NativeMatchPublic.check cc=true := (check_rekey ctx f).trans hc
  have hW : InputWidth cc.client 16 := inputWidth_rekey ctx f 16 hwidth
  have hcap : ¬cc.capacityBad tape' := fun hb => hbad (Or.inl hb)
  have hn : ¬normalizationBad cc (NativeMatchCoded.stored .sixteen σ) tape' :=
    NativeMatchCanonicalNormalizeProof.context_sixteen cc hm hv' hW tape' σ
  apply NativeRekeyApiGuard.production_coupled ctx hm f hv' policy s
    (NativeMatchCoded.stored .sixteen σ) hs tape tape' hw hd hcap hn
  intro e he hb
  have hei : e∈cc.inventory tape' := by
    rw [inventory_reference cc hc' tape' hcap]
    exact he
  exact hbad (Or.inr ⟨e,hei,(NativeMatchRoutingBudget16Proof.event_stored cc hm hv' hW tape' σ e hei).mp hb⟩)


open NativeNormalizeEncode16Proof NativeRekeyCodedRouting

lemma coded_production_off_bad (ctx : Context member initialized h)
    (hm : member∈ConfigurationFamily.members) (hv : ctx.Valid)
    (f : Tape 128) (σ : Equiv.Perm (Fingerprint 128)) (routing : Tape 64)
    (hi : ((ctx.init.map (mapRec (encode16 ∘ f))).map Rec.key).Nodup)
    (hc : NativeMatchPublic.check ctx=true) (policy : Policy)
    (hbad : ¬((rekey ctx (encode16 ∘ f)).capacityBad
        (NativeMatchCoded.routing (rekey ctx (encode16 ∘ f)) .sixteen (((),σ),routing)) ∨
      ∃ e∈(rekey ctx (encode16 ∘ f)).inventory
        (NativeMatchCoded.routing (rekey ctx (encode16 ∘ f)) .sixteen (((),σ),routing)),
        e.bad (fun key=>σ (block16 key)))) :
    ∃ out, production ctx policy (σ ∘ f)
        (NativeMatchCoded.routing ctx .longer (((),σ ∘ f),routing))=.ok out ∧
      NativeRekeyApi.state (encode16 ∘ f) out=reference (rekey ctx (encode16 ∘ f))
        (NativeMatchCoded.routing (rekey ctx (encode16 ∘ f)) .sixteen (((),σ),routing)) ∧
      out.requests=(ApiAdaptive.requestGroups ctx.compiled
        (NativeMatchApiReference.rows (rekey ctx (encode16 ∘ f))
          (NativeMatchCoded.routing (rekey ctx (encode16 ∘ f)) .sixteen (((),σ),routing)))
        ctx.frames).flatMap PublicApi.Group.lanes :=
  production_off_bad ctx hm hv (encode16 ∘ f) (fun k=>encode16_length (f k)) hi hc policy
    (σ ∘ f) σ (stored_compat f σ) _ _
    (words_rekey ctx (encode16 ∘ f) (σ ∘ f) (NativeMatchCoded.stored .sixteen σ) (stored_compat f σ) routing)
    (dummy_rekey ctx (encode16 ∘ f) (σ ∘ f) (NativeMatchCoded.stored .sixteen σ) (stored_compat f σ) routing).symm hbad

lemma coded_observed_off_bad (ctx : Context member initialized h)
    (hm : member∈ConfigurationFamily.members) (hv : ctx.Valid)
    (f : Tape 128) (σ : Equiv.Perm (Fingerprint 128)) (routing : Tape 64)
    (hi : ((ctx.init.map (mapRec (encode16 ∘ f))).map Rec.key).Nodup)
    (hc : NativeMatchPublic.check ctx=true) (policy : Policy)
    (hbad : ¬((rekey ctx (encode16 ∘ f)).capacityBad
        (NativeMatchCoded.routing (rekey ctx (encode16 ∘ f)) .sixteen (((),σ),routing)) ∨
      ∃ e∈(rekey ctx (encode16 ∘ f)).inventory
        (NativeMatchCoded.routing (rekey ctx (encode16 ∘ f)) .sixteen (((),σ),routing)),
        e.bad (fun key=>σ (block16 key)))) :
    NativeMatchCoded.observed ctx policy .longer (((),σ ∘ f),routing) =
      NativeMatchEndpoint.referenceView (rekey ctx (encode16 ∘ f))
        (NativeMatchCoded.routing (rekey ctx (encode16 ∘ f)) .sixteen (((),σ),routing)) := by
  obtain ⟨out,he,hmapped,_⟩ := coded_production_off_bad ctx hm hv f σ routing hi hc policy hbad
  have hr := congrArg (fun st : State ctx.transcriptWidth=>st.rows) hmapped
  simp only [NativeRekeyApi.state] at hr
  change (production ctx policy (σ ∘ f) _).toOption.map (NativeMatchEndpoint.rows ctx)=_
  rw [he]
  change some (NativeMatchEndpoint.rows ctx out)=some _
  congr 1
  funext t i
  exact congrArg (fun rows : List (Fin ctx.transcriptWidth→Nat)=>rows.getD t.val (fun _=>0) i) hr

end RebuildBound.NativeRekeyCodedGuard
