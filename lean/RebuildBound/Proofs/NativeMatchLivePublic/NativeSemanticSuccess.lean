import RebuildBound.Proofs.NativeMatchLivePublic.NativeSemanticCoherence
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyApiGuard
import RebuildBound.Proofs.NativeMatchEndpoint

namespace RebuildBound.NativeMatchSemanticSuccess
open Model Model.Online Spec Spec.NativeMatchProduction Spec.NativeMatchApi Spec.NativeNormalizeLiveApi
open NativeMatchSemanticProof

set_option maxHeartbeats 0
set_option maxRecDepth 100000

 def slot (f : LogicalKey → LogicalKey) (s : OnlineBatch.Slot) : OnlineBatch.Slot :=
   {s with record:=NativeRekeyLocal.rec f s.record}
 def batchRun (f : LogicalKey → LogicalKey) (run : OnlineBatch.BatchRun) : OnlineBatch.BatchRun :=
   ⟨run.ops.map (NativeRekeyApi.op f),run.init.map (mapRec f),run.unsh⟩

 lemma op_lanes (f : LogicalKey → LogicalKey) (o : OnlineBatch.Op) :
    (NativeRekeyApi.op f o).lanes = o.lanes.map (fun rb=>(NativeRekeyLocal.rec f rb.1,rb.2)) := by
  cases o <;> simp [NativeRekeyApi.op,OnlineBatch.Op.lanes,List.map_map,Function.comp_def]

 lemma slots_map (f : LogicalKey → LogicalKey) (run : OnlineBatch.BatchRun) :
    OnlineBatch.slots (batchRun f run) = (OnlineBatch.slots run).map (slot f) := by
  simp [OnlineBatch.slots,batchRun,List.zipIdx_map,List.flatMap_map,
    List.map_flatMap,List.map_map,Function.comp_def,op_lanes,slot]

 lemma widths_map (f : LogicalKey → LogicalKey) (run : OnlineBatch.BatchRun) :
    OnlineBatch.widths (batchRun f run) = OnlineBatch.widths run := by
  simp only [OnlineBatch.widths,batchRun,List.map_map,Function.comp_def,op_lanes,List.length_map]

 lemma selected_map (f : LogicalKey → LogicalKey) {m} (st : State m) (t : Nat) :
    (NativeRekeyApi.state f st).selected.getD t ⟨none,[]⟩ =
      NativeRekeyApi.result f (st.selected.getD t ⟨none,[]⟩) :=
  List.getD_map st.selected ⟨none,[]⟩ (NativeRekeyApi.result f)

 lemma semantic_of_rekey_reference {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members) (hv : ctx.Valid)
    (f : LogicalKey → LogicalKey) (hinit : ((ctx.init.map (mapRec f)).map Rec.key).Nodup)
    (policy : Policy) (stored : LogicalKey → NativeMatch.Lanes.Stored)
    (sourceTape targetTape : IdealKey.Tape) (st : State ctx.transcriptWidth)
    (hprod : production ctx policy stored sourceTape=.ok st)
    (he : NativeRekeyApi.state f st=reference (rekey ctx f) targetTape)
    (hsafe : ∀ t q, st.requests[t]?=some q →
      ¬liveAlias f (Api.stateAt (Api.stateOf ctx.codec ctx.init) st.requests t) q.key) :
    NativeMatchSemantic.ResultsCorrect ctx st := by
  let source : OnlineBatch.BatchRun := ⟨st.ops,ctx.init,fun r=>ctx.codec.flag r.val⟩
  have hv' := NativeNormalizeLiveApiProof.valid_rekey ctx f hv hinit
  have hc := NativeMatchEndpointProof.reference_correct (rekey ctx f) hm hv' targetTape
  rw [←he] at hc
  have hapi : ApiResultsCorrect ctx.geo ctx.codec ctx.unit (batchRun f source) ctx.schedule ctx.accesses
      (IdealHierarchy.words targetTape) (IdealHierarchy.dummy targetTape)
      (st.requests.map (mapRequest f))
      (fun t=>NativeRekeyApi.result f (st.selected.getD t ⟨none,[]⟩)) := by
    have hh := hc.1
    simp only [selected_map] at hh
    change ApiResultsCorrect ctx.geo ctx.codec ctx.unit
      ⟨st.ops.map (NativeRekeyApi.op f),ctx.init.map (mapRec f),fun r=>ctx.codec.flag r.val⟩
      ctx.schedule ctx.accesses (IdealHierarchy.words targetTape) (IdealHierarchy.dummy targetTape)
      (st.requests.map (mapRequest f))
      (fun t=>NativeRekeyApi.result f (st.selected.getD t ⟨none,[]⟩)) at hh
    exact hh
  have hrep := NativeNormalizeLiveApiProof.represents_init f ctx.codec ctx.init hv.1.1 hinit
  have hrequests : st.requests.length=ctx.accesses := by
    simpa only [List.length_map] using hapi.1
  have hslots : st.requests.length=(OnlineBatch.slots source).length := by
    simpa only [slots_map,List.length_map] using hapi.2.1
  have hsels : st.selected.length=ctx.accesses := by
    simpa only [NativeRekeyApi.state,List.length_map,rekey,Context.accesses,Context.frames] using hc.2.1
  have hrows : st.rows.length=ctx.accesses := hc.2.2
  have hreply : ∀ t q, st.requests[t]?=some q →
      Api.reply q (Api.value ctx.codec (st.selected.getD t ⟨none,[]⟩).found) =
        Api.reply q (Api.stateAt (Api.stateOf ctx.codec ctx.init) st.requests t q.key) := by
    apply replies_of_normalized f ctx.codec _ _ hrep st.requests _ hsafe
    intro t q hq
    have hlt := (List.getElem?_eq_some_iff.mp hq).1
    have hltS : t < (OnlineBatch.slots source).length := by rw [←hslots]; exact hlt
    let sl := (OnlineBatch.slots source)[t]
    have hsl : (OnlineBatch.slots source)[t]?=some sl := List.getElem?_eq_getElem hltS
    have hq' : (st.requests.map (mapRequest f))[t]?=some (mapRequest f q) := by simp [hq]
    have hsl' : (OnlineBatch.slots (batchRun f source))[t]?=some (slot f sl) := by
      simp only [slots_map,List.getElem?_map,hsl,Option.map_some]
    have hr := (hapi.2.2.2 t (mapRequest f q) (slot f sl) hq' hsl').1
    simpa only [NativeRekeyApi.result,NativeRekeyApi.value_map,mapRequest,batchRun,source] using hr
  have haddress : ∀ t q sl, st.requests[t]?=some q → (OnlineBatch.slots source)[t]?=some sl →
      (st.selected.getD t ⟨none,[]⟩).addresses.length =
        (if sl.probes then (OnlineBatch.slotSchedule (OnlineBatch.widths source) ctx.schedule t).tables.length else 0) := by
    intro t q sl hq hsl
    have hq' : (st.requests.map (mapRequest f))[t]?=some (mapRequest f q) := by simp [hq]
    have hsl' : (OnlineBatch.slots (batchRun f source))[t]?=some (slot f sl) := by
      simp only [slots_map,List.getElem?_map,hsl,Option.map_some]
    have hr := (hapi.2.2.2 t (mapRequest f q) (slot f sl) hq' hsl').2.2.1
    simpa only [NativeRekeyApi.result,slot,widths_map] using hr
  exact ⟨api_of_replies ctx.codec source ctx.schedule ctx.accesses st.requests _ hrequests
    (NativeMatchSemanticCoherence.production_coherent ctx policy stored sourceTape st hprod) hreply haddress,
    hsels,hrows⟩

/-- All success guards concern the certified normalized reference run. The live
alias guard concerns the original adaptive chooser requests reconstructed from
those rows, so no injectivity or source-execution correctness is assumed. -/
lemma production_semantic {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members) (hv : ctx.Valid)
    (f : LogicalKey → LogicalKey) (hinit : ((ctx.init.map (mapRec f)).map Rec.key).Nodup)
    (policy : Policy) (stored targetStored : LogicalKey → NativeMatch.Lanes.Stored)
    (hs : ∀ key,targetStored (f key)=stored key) (sourceTape targetTape : IdealKey.Tape)
    (hw : NativeRekeyHierarchyBase.WordsRel f
      (IdealHierarchy.words sourceTape) (IdealHierarchy.words targetTape))
    (hd : IdealHierarchy.dummy sourceTape=IdealHierarchy.dummy targetTape)
    (hcap : ¬(rekey ctx f).capacityBad targetTape)
    (hn : ¬normalizationBad (rekey ctx f) targetStored targetTape)
    (hoff : ∀ e∈NativeMatchHierarchy.referenceEvents ctx.geo.cfg ctx.geo.shapes ctx.unit ((rekey ctx f).run targetTape)
      ctx.schedule (IdealHierarchy.words targetTape) ctx.accesses,¬e.bad targetStored)
    (hsafe : ∀ t q,
      ((ApiAdaptive.requestGroups ctx.compiled (NativeMatchApiReference.rows (rekey ctx f) targetTape)
        ctx.frames).flatMap PublicApi.Group.lanes)[t]?=some q →
      ¬liveAlias f (Api.stateAt (Api.stateOf ctx.codec ctx.init)
        ((ApiAdaptive.requestGroups ctx.compiled (NativeMatchApiReference.rows (rekey ctx f) targetTape)
          ctx.frames).flatMap PublicApi.Group.lanes) t) q.key) :
    ∃ st, production ctx policy stored sourceTape=.ok st ∧ NativeMatchSemantic.ResultsCorrect ctx st := by
  rcases NativeRekeyApiGuard.production_coupled ctx hm f
    (NativeNormalizeLiveApiProof.valid_rekey ctx f hv hinit) policy stored targetStored hs
    sourceTape targetTape hw hd hcap hn hoff with ⟨st,hprod,he,hreq⟩
  refine ⟨st,hprod,semantic_of_rekey_reference ctx hm hv f hinit policy stored sourceTape targetTape
    st hprod he ?_⟩
  simpa only [hreq] using hsafe

end RebuildBound.NativeMatchSemanticSuccess
