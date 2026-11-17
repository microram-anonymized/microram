import RebuildBound.Proofs.NativeMatchLivePublic.NativeLiveSummary
import RebuildBound.Proofs.NativeMatchLivePublic.NativeSemanticSuccess
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyCodedGuard

set_option maxHeartbeats 400000
namespace RebuildBound.NativeLiveFailureGuard
open Model Spec NativeMatchProduction NativeMatchApi NativeNormalize NativeNormalizePairs
open NativeMatchLivePairs NativeNormalizeLiveApi NativeLiveSummary NativeLiveSampleTransport
open NativeCollapsedLiveBound NativeCollapsedMeasurable NativeCollapsedBudget NativeNormalizeCollapsed
open NativeNormalizeEncode16Proof

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

lemma live_safe_of_no_pairs (f : LogicalKey→LogicalKey) (initial : Api.State)
    (keys : List LogicalKey) (qs : List Api.Request) (hs : ApiCapacity.Supports initial keys)
    (hb : ¬PairBad f (pairs initial keys qs)) :
    ∀ t q,qs[t]?=some q → ¬liveAlias f (Api.stateAt initial qs t) q.key := by
  intro t q hq ⟨other,hne,hlive,he⟩
  apply hb
  refine ⟨(q.key,other),?_,Ne.symm hne,he.symm⟩
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨t,List.mem_range.mpr (List.getElem?_eq_some_iff.mp hq).1,?_⟩
  rw [hq]
  exact List.mem_map_of_mem (((ApiFiniteSupport initial keys qs hs t).2 other).mpr hlive)

lemma failure_envelope (ctx : Context member initialized h)
    (hm : member∈ConfigurationFamily.members) (hv : ctx.Valid)
    (hc : NativeMatchPublic.check ctx=true) (policy : Policy) (p : AugSample)
    (hfail : NativeMatchSemantic.failure ctx policy .longer (nativeSample p)) :
    (summary ctx p.1 p.2.1 (routed ctx p.2.1 p.2.2)).1=true ∨
      PairBad p.1 (pairs (Api.stateOf ctx.codec ctx.init) (ctx.init.map Rec.key)
        (logicalRequests ctx (summary ctx p.1 p.2.1 (routed ctx p.2.1 p.2.2)).2)) := by
  classical
  by_contra hn
  obtain ⟨hgood,hpairs⟩ := not_or.mp hn
  let f := keyMap p.1
  let tape := routed ctx p.2.1 p.2.2
  let qs := logicalRequests ctx (summary ctx p.1 p.2.1 tape).2
  have hbad : ¬canonicalBad ctx keyMap p.1 p.2.1 tape := by
    intro hb
    apply hgood
    simp only [summary,decide_eq_true_eq]
    exact hb
  have hp : ¬PairBad f (pairs (Api.stateOf ctx.codec ctx.init) (ctx.init.map Rec.key) qs) := by
    intro he
    apply hpairs
    exact (pairBad_encode_iff encode16 encode16_injective p.1 _).mp he
  have hpi : ¬PairBad f (initialPairs (ctx.init.map Rec.key)) := by
    rintro ⟨pair,hmem,hne,he⟩
    exact hp ⟨pair,List.mem_append_left _ hmem,hne,he⟩
  have hi : ((ctx.init.map (mapRec f)).map Rec.key).Nodup := by
    have hh := initial_mapped_nodup f (ctx.init.map Rec.key) hv.1.1 hpi
    simpa only [List.map_map,Function.comp_def,mapRec] using hh
  have hcollapse := collapsed_eq ctx f hi
  have hclient : (collapsedRekey ctx f).client=(rekey ctx f).client := by
    have hi' := congrArg Context.init hcollapse
    change ApiAdaptive.run ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule
      (collapsedRekey ctx f).init ctx.frames (rekey ctx f).compiled =
      ApiAdaptive.run ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule
      (rekey ctx f).init ctx.frames (rekey ctx f).compiled
    rw [hi']
  have hq : qs=(ApiAdaptive.requestGroups ctx.compiled
      (NativeMatchApiReference.rows (rekey ctx f) tape) ctx.frames).flatMap PublicApi.Group.lanes := by
    change (ApiAdaptive.requestGroups ctx.compiled
      (Adaptive.rowsOf (referenceTranscript ctx keyMap p.1 tape) ctx.accesses) ctx.frames).flatMap _ = _
    apply congrArg (fun rows : List (Fin ctx.transcriptWidth→Nat) =>
      (ApiAdaptive.requestGroups ctx.compiled rows ctx.frames).flatMap PublicApi.Group.lanes)
    have hr := congrArg (fun client : Adaptive.AdaptiveRun ctx.transcriptWidth =>
      Adaptive.rowsOf (Adaptive.transcript ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule
        client ctx.accesses (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)) ctx.accesses) hclient
    exact hr.trans (NativeMatchApiReference.transcript_rows (rekey ctx f) tape)
  have hs := live_safe_of_no_pairs f _ _ qs
    (ApiCapacityProof.records_support ctx.codec ctx.init hv.1.1 hv.1.2.2.1) hp
  have htarget : ¬((rekey ctx f).capacityBad tape ∨
      ∃ e∈(rekey ctx f).inventory tape,e.bad (fun key=>p.2.1 (NativeMatchTrace.block16 key))) := by
    have hh : ¬((collapsedRekey ctx f).capacityBad tape ∨
        ∃ e∈(collapsedRekey ctx f).inventory tape,e.bad (fun key=>p.2.1 (NativeMatchTrace.block16 key))) := hbad
    rwa [hcollapse] at hh
  obtain ⟨out,hprod,he,hreq⟩ := NativeRekeyCodedGuard.coded_production_off_bad
    ctx hm hv p.1 p.2.1 p.2.2 hi hc policy htarget
  have hsource : ∀ t q,out.requests[t]?=some q →
      ¬liveAlias f (Api.stateAt (Api.stateOf ctx.codec ctx.init) out.requests t) q.key := by
    have heq : out.requests=qs := hreq.trans hq.symm
    simpa only [heq] using hs
  have hresult := NativeMatchSemanticSuccess.semantic_of_rekey_reference ctx hm hv f hi policy
    (p.2.1 ∘ p.1) _ tape out hprod he hsource
  change (match production ctx policy (p.2.1 ∘ p.1)
    (NativeMatchCoded.routing ctx .longer (((),p.2.1 ∘ p.1),p.2.2)) with
    | .error _ => True
    | .ok state => ¬NativeMatchSemantic.ResultsCorrect ctx state) at hfail
  rw [hprod] at hfail
  exact hfail hresult

end RebuildBound.NativeLiveFailureGuard
