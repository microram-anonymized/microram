import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyApi
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyRange
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyHierarchyBase
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyHierarchy
import RebuildBound.Proofs.NativeMatchApi

namespace RebuildBound.NativeRekeyApiGuard
open Model Model.Hierarchy Model.Online Model.OnlineBatch Spec
open NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchHierarchy NativeMatchApi
open NativeRekeyLocal NativeRekeyHierarchyBase BatchFreshProof OnlineCorrectnessProof

noncomputable def keySection (f : LogicalKey → LogicalKey) (key : LogicalKey) : LogicalKey := by
  classical
  exact if h : key ∈ Set.range f then Classical.choose h else []

lemma keySection_spec (f : LogicalKey → LogicalKey) (key : LogicalKey) (h : key∈Set.range f) :
    f (keySection f key)=key := by
  rw [keySection,dite_eq_left h]
  exact Classical.choose_spec h

noncomputable def liftRec (f : LogicalKey → LogicalKey) (r : Rec) : Rec :=
  ⟨keySection f r.key,r.val,r.tomb⟩

noncomputable def liftBucket (f : LogicalKey → LogicalKey) (b : Bucket) : Bucket :=
  b.map (Option.map (liftRec f))

lemma rec_lift (f : LogicalKey → LogicalKey) (r : Rec) (h : r.key∈Set.range f) :
    rec f (liftRec f r)=r := by
  cases r
  simp only [rec,liftRec,keySection_spec f _ h]

lemma bucket_lift (f : LogicalKey → LogicalKey) (b : Bucket)
    (h : ∀ r ∈ b.recs,r.key∈Set.range f) : bucket f (liftBucket f b)=b := by
  induction b with
  | nil => rfl
  | cons x xs ih =>
    have ht : ∀ r ∈ Bucket.recs xs,r.key∈Set.range f := by
      intro r hr
      exact h r (by cases x <;> simp_all [Bucket.recs])
    cases x with
    | none => simpa only [NativeRekeyLocal.bucket,liftBucket,List.map_cons,Option.map_none] using congrArg (none::·) (ih ht)
    | some r =>
      have hr : r.key∈Set.range f := h r (by simp [Bucket.recs])
      simp only [NativeRekeyLocal.bucket,liftBucket,List.map_cons,Option.map_some,rec_lift f r hr]
      exact congrArg (some r::·) (ih ht)

lemma buckets_lift (f : LogicalKey → LogicalKey) (bs : List Bucket)
    (h : ∀ r ∈ DirectMasks.records bs,r.key∈Set.range f) :
    (bs.map (liftBucket f)).map (bucket f)=bs := by
  rw [List.map_map]
  calc
    _ = bs.map id := by
      apply List.map_congr_left
      intro b hb
      apply bucket_lift
      intro r hr
      exact h r (List.mem_flatMap.mpr ⟨b,hb,hr⟩)
    _ = bs := List.map_id bs

noncomputable def complete (f : LogicalKey → LogicalKey) (source target : Trace) (n : Nat) : Trace :=
  ⟨fun i => if i<n then source.units i else (target.units i).map (liftBucket f),source.init,source.unsh⟩

lemma complete_rel (f : LogicalKey → LogicalKey) (source target : Trace) (n : Nat)
    (hi : target.init=NativeRekeyRouting.records f source.init)
    (hu : ∀ r,target.unsh (NativeRekeyRouting.rec f r)=source.unsh r)
    (hp : ∀ i<n,target.units i=NativeRekeyRouting.buckets f (source.units i))
    (hrange : ∀ i,∀ r∈DirectMasks.records (target.units i),r.key∈Set.range f) :
    TraceRel f (complete f source target n) target := by
  refine ⟨hi,?_,hu⟩
  intro i
  dsimp only [complete]
  split
  · exact hp i ‹i<n›
  · exact (buckets_lift f (target.units i) (hrange i)).symm

lemma complete_prefix (f : LogicalKey → LogicalKey) (source target : Trace) (n i : Nat) (hi : i<n) :
    (complete f source target n).units i=source.units i := by simp [complete,hi]

lemma traceFromState_rel (f : LogicalKey → LogicalKey) (g : OnlineGeom) (init : List Rec)
    (codec : Api.Codec) (st : Requester.State) :
    TraceRel f (traceFromState g init (fun r=>codec.flag r.val) st)
      (traceFromState g (init.map (rec f)) (fun r=>codec.flag r.val) (NativeRekeyApi.requester f st)) := by
  constructor
  · rfl
  · intro i
    simp only [traceFromState,NativeRekeyApi.requester,NativeRekeyRouting.buckets,
      List.map_drop,List.map_take]
    rfl
  · intro r
    rfl


lemma units_at_state (geo : HierarchyGeometry) (g : OnlineGeom)
    (hg : g.unitEntries*g.unitsPerPrefix=geo.cfg.carryPositions 1) (hE : 0<g.unitEntries)
    (run : BatchRun) (S : Schedule) (n m : Nat) (hS : SchedulePremises geo.cfg S n m)
    (j : Nat) (hjn : fs run j<n) (c : Nat × Nat) (hc : c∈(S (fs run j)).tables)
    (i : Nat) (hi : i<unitEnd geo.cfg c.1 c.2) :
    (traceFromState g run.init run.unsh (stateAt g run j)).units i = (traceOf g run).units i := by
  rw [NativeMatchApiProof.traceFromState_prefix]
  have hitime : geo.cfg.seed 1+i+1≤time geo.cfg c.1 c.2 := by
    unfold unitEnd at hi
    omega
  apply TraceUnitsPrefix geo.cfg g run j i hg hE
  have hwe := (OnlineFreshProof.tiles_bounds (hS.tile _ hjn) c hc).2.2
  change (window geo.cfg c.1 c.2).2 ≤ _ at hwe
  rw [OnlineFreshProof.window_snd,←OnlineCorrectnessProof.time_cp] at hwe
  have hcons := (hS.consumed _ hjn).2
  unfold pos at hcons
  have hmul : (i+1)*geo.cfg.carryPositions 1+geo.cfg.seed 1*geo.cfg.carryPositions 1 ≤
      time geo.cfg c.1 c.2*geo.cfg.carryPositions 1 := by
    rw [←Nat.add_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  show (i+1)*geo.cfg.carryPositions 1≤fs run j
  omega


set_option maxHeartbeats 1200000 in
lemma tables_map (f : LogicalKey → LogicalKey) (codec : Api.Codec)
    (member : ConfigurationFamily.Member) (initialized : Bool)
    (hm : member∈ConfigurationFamily.members) (h : Nat) (run : BatchRun)
    (hready : RunReady member initialized h run)
    (init : List Rec) (hinit : run.init=init.map (rec f))
    (hunsh : run.unsh=(fun r=>codec.flag r.val)) (S : Schedule) (n m : Nat)
    (hS : SchedulePremises ((member.geometry initialized).chunk h).cfg S n m)
    (hN : n≤((member.geometry initialized).chunk h).cfg.horizon)
    (s s' : LogicalKey → Stored) (hs : ∀ key,s' (f key)=s key)
    (words words' : Words) (hw : WordsRel f words words')
    (hno : ¬Fails ((member.geometry initialized).chunk h).cfg
      ((member.geometry initialized).chunk h).shapes (traceOf ⟨64,member.r0⟩ run) words')
    (hoff : OffEvents s' ((member.geometry initialized).chunk h).cfg
      ((member.geometry initialized).chunk h).shapes (traceOf ⟨64,member.r0⟩ run) words')
    (hrange : ∀ key∈NativeRoutingActual.usedKeys run,key∈Set.range f)
    (st : Requester.State) (j : Nat)
    (hst : NativeRekeyApi.requester f st=stateAt ⟨64,member.r0⟩ run j)
    (hjn : fs run j<n) :
    NativeRekeyApi.TablesMap f s s' codec ((member.geometry initialized).chunk h).cfg
      ((member.geometry initialized).chunk h).shapes ⟨64,member.r0⟩ S init words words' st (fs run j) := by
  let geo := (member.geometry initialized).chunk h
  let g : OnlineGeom := ⟨64,member.r0⟩
  let source := traceFromState g init (fun r=>codec.flag r.val) st
  let target := traceOf g run
  let targetPrefix := traceFromState g (init.map (rec f)) (fun r=>codec.flag r.val) (NativeRekeyApi.requester f st)
  have hgeo := ConfigurationFamilyProbabilityProof.structural initialized member hm h
  have hgeom := NativeMatchProductionProof.alignment member hm initialized h
  have hE : 0<g.unitEntries := by change 0<64; decide
  have hkeys := NativeRoutingActualProof.used_trace geo.cfg g run hgeom hE hready.1
  have hRange : ∀ i,∀ r∈DirectMasks.records (target.units i),r.key∈Set.range f := by
    intro i r hr
    exact hrange _ (List.mem_toFinset.mp (hkeys.keys i r hr))
  have htPrefix := traceFromState_rel f g init codec st
  have hPrefixEq : targetPrefix=traceFromState g run.init run.unsh (stateAt g run j) := by
    dsimp only [targetPrefix]
    rw [hst,←hinit,←hunsh]
  intro c hc
  have hb := NativeMatchApiScheduledReplay.coordinate_bounds (HierarchySemanticsProof.lower hgeo.1)
    S n m hS hN (fs run j) hjn c hc
  let completed := complete f source target (unitEnd geo.cfg c.1 c.2)
  have hprefix : ∀ i<unitEnd geo.cfg c.1 c.2,
      target.units i=NativeRekeyRouting.buckets f (source.units i) := by
    intro i hi
    calc
      _ = targetPrefix.units i := by
        rw [hPrefixEq]
        exact (units_at_state geo g hgeom hE run S n m hS j hjn c hc i hi).symm
      _ = _ := htPrefix.units i
  have hcompRel : TraceRel f completed target := complete_rel f source target _ hinit
    (fun r => by simp only [target,OnlineBatch.traceOf,hunsh,source,traceFromState,NativeRekeyRouting.rec]) hprefix hRange
  have hfamily := NativeRekeyHierarchy.family_map member initialized hm h run hready
    hcompRel hw s s' hs hno hoff c.1 c.2 hb.2.2.2
  have hsource : nativeTable s geo.cfg geo.shapes source words c.1 c.2 =
      nativeTable s geo.cfg geo.shapes completed words c.1 c.2 :=
    NativeMatchHierarchyTracePrefix.table_trace_congr (HierarchySemanticsProof.lower hgeo.1)
      s source completed rfl rfl words c.1 hb.1 hb.2.1 c.2
      (fun i hi => (complete_prefix f source target _ i hi).symm)
  have htarget := NativeMatchApiProof.nativeTable_at_state geo hgeo.1 g hgeom hE run S n m hS
    s' words' j hjn c hc hb.1 hb.2.1
  change nativeTable s' geo.cfg geo.shapes targetPrefix words' c.1 c.2 =
    (nativeTable s geo.cfg geo.shapes source words c.1 c.2).map (NativeRekeyApi.output f)
  rw [hPrefixEq,htarget,hfamily,←hsource]
  rfl


open NativeMatchProduction NativeNormalizeLiveApi

lemma causal_width (frames : List ApiAdaptive.Frame) (start j : Nat) (frame : ApiAdaptive.Frame)
    (hc : ApiAdaptive.Causal start frames) (hf : frames[j]?=some frame) :
    0<frame.kind.width := by
  induction frames generalizing start j with
  | nil => simp at hf
  | cons head tail ih =>
    cases j with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at hf; subst frame; exact hc.2.1
    | succ j => exact ih _ j hc.2.2 hf

lemma frame_fs_lt {member initialized h} (ctx : Context member initialized h) (tape : IdealKey.Tape)
    (j : Nat) (frame : ApiAdaptive.Frame) (hf : ctx.frames[j]?=some frame) :
    fs (ctx.run tape) j<ctx.accesses := by
  rw [NativeMatchApiReference.prefix_slots]
  have hp := causal_width ctx.frames 0 j frame (ApiAdaptiveFrames ctx.batchWidth 64 ctx.batches).1 hf
  have hlen := (List.getElem?_eq_some_iff.mp hf).1
  have hsplit : ctx.frames = ctx.frames.take j ++ frame :: ctx.frames.drop (j+1) := by
    have he := List.take_append_drop (j+1) ctx.frames
    rw [List.take_add_one,hf] at he
    simpa only [Option.toList_some,List.append_assoc,List.singleton_append] using he.symm
  change Adaptive.slotCount (ApiAdaptive.shape (ctx.frames.take j))<
    Adaptive.slotCount (ApiAdaptive.shape ctx.frames)
  conv_rhs => rw [hsplit,ApiAdaptiveProof.count_append,ApiAdaptiveProof.count_cons]
  omega

lemma issue_requests {m} (policy : Policy) (s : LogicalKey→Stored) (codec : Api.Codec)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (init : List Rec)
    (words : Words) (dummy) (choose : ApiAdaptive.Chooser m) (st next : State m)
    (frame : ApiAdaptive.Frame)
    (he : issueFrame policy s codec cfg sh g S init words dummy choose st frame=.ok next) :
    next.requests=st.requests++(ApiAdaptive.requests choose st.rows frame).lanes := by
  unfold issueFrame at he
  cases ho : operation policy s codec cfg sh g S init words dummy st
    (ApiAdaptive.requests choose st.rows frame) with
  | error e => simp only [ho] at he; cases he
  | ok answer =>
    simp only [ho] at he
    exact congrArg State.requests (Except.ok.inj he).symm


set_option maxHeartbeats 2400000 in
lemma production_coupled {member initialized h} (ctx : Context member initialized h)
    (hm : member∈ConfigurationFamily.members) (f : LogicalKey→LogicalKey)
    (hv : (rekey ctx f).Valid) (policy : Policy) (s s' : LogicalKey→Stored)
    (hs : ∀ key,s' (f key)=s key) (tape tape' : IdealKey.Tape)
    (hw : WordsRel f (IdealHierarchy.words tape) (IdealHierarchy.words tape'))
    (hd : IdealHierarchy.dummy tape=IdealHierarchy.dummy tape')
    (hcap : ¬(rekey ctx f).capacityBad tape')
    (hn : ¬normalizationBad (rekey ctx f) s' tape')
    (hoff : ∀ e∈referenceEvents ctx.geo.cfg ctx.geo.shapes ctx.unit ((rekey ctx f).run tape')
      ctx.schedule (IdealHierarchy.words tape') ctx.accesses,¬e.bad s') :
    ∃ out, production ctx policy s tape=.ok out ∧
      NativeRekeyApi.state f out=reference (rekey ctx f) tape' ∧
      out.requests=(ApiAdaptive.requestGroups ctx.compiled (NativeMatchApiReference.rows (rekey ctx f) tape')
        ctx.frames).flatMap PublicApi.Group.lanes := by
  let cc := rekey ctx f
  let run := cc.run tape'
  let ref := fun j => referenceState ctx.geo.cfg ctx.geo.shapes ctx.unit run ctx.schedule
    (IdealHierarchy.words tape') (IdealHierarchy.dummy tape')
    (NativeMatchApiReference.requests cc tape') j ctx.transcriptWidth
  let rows := NativeMatchApiReference.rows cc tape'
  let reqs := fun j => (ApiAdaptive.requestGroups ctx.compiled rows (ctx.frames.take j)).flatMap PublicApi.Group.lanes
  have hc := NativeMatchApiReference.contracts cc hm hv tape'
  have hready : RunReady member initialized h run :=
    ⟨hv.1.1,NativeMatchProductionProof.init_bound cc hm hv tape',hc.1.2.1⟩
  have hoffR : OffEvents s' ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit run)
      (IdealHierarchy.words tape') := by
    intro job hj hwithin e he
    apply hoff e
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨job,List.mem_filter.mpr ⟨hj,by simpa using hwithin⟩,he⟩
  have htables : ∀ j frame, ctx.frames[j]?=some frame → ∀ st : State ctx.transcriptWidth,
      NativeRekeyApi.state f st=ref j →
      NativeRekeyApi.TablesMap f s s' ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule
        ctx.init (IdealHierarchy.words tape) (IdealHierarchy.words tape') st.requester st.rows.length := by
    intro j frame hf st heq
    have hre : NativeRekeyApi.requester f st.requester=OnlineBatch.stateAt ctx.unit run j :=
      congrArg State.requester heq
    have hrl : st.rows.length=fs run j := by
      have hh := congrArg (fun x:State ctx.transcriptWidth=>x.rows.length) heq
      simpa only [NativeRekeyApi.state,ref,referenceState,List.length_map,List.length_range,fs] using hh
    rw [hrl]
    exact tables_map f ctx.codec member initialized hm h run hready ctx.init rfl rfl ctx.schedule
      ctx.accesses ctx.transcriptWidth hv.2.2.1 hv.2.1 s s' hs (IdealHierarchy.words tape)
      (IdealHierarchy.words tape') hw hcap hoffR (NativeRekeyRange.run_used ctx f tape') st.requester j hre
      (frame_fs_lt cc tape' j frame hf)
  have hchoice : ∀ j frame, ctx.frames[j]?=some frame → ∀ st : State ctx.transcriptWidth,
      NativeRekeyApi.state f st=ref j → ApiAdaptive.requests ctx.compiled st.rows frame=
        ApiAdaptive.requests ctx.compiled rows frame := by
    intro j frame hf st heq
    have hr : st.rows=rows.take (fs run j) := by
      have hh : st.rows=(ref j).rows := by
        simpa only [NativeRekeyApi.state] using congrArg (fun x:State ctx.transcriptWidth=>x.rows) heq
      exact hh.trans (NativeMatchApiProjection.reference_rows cc hm hv tape' j)
    rw [hr]
    apply ApiAdaptiveProof.requests_take
    rw [NativeMatchApiReference.prefix_slots]
    change frame.start≤Adaptive.slotCount (ApiAdaptive.shape (ctx.frames.take j))
    simpa only [Nat.zero_add] using NativeMatchApiReference.causal_start ctx.frames 0 j frame
      (ApiAdaptiveFrames ctx.batchWidth 64 ctx.batches).1 hf
  have hchain : ∀ remaining j (st : State ctx.transcriptWidth), remaining=ctx.frames.drop j →
      j≤ctx.frames.length → NativeRekeyApi.state f st=ref j → st.requests=reqs j →
      ∃ out, execute policy s ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.init
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) ctx.compiled st remaining=.ok out ∧
        NativeRekeyApi.state f out=ref ctx.frames.length ∧ out.requests=reqs ctx.frames.length := by
    intro remaining
    induction remaining with
    | nil =>
      intro j st hdrop hj heq hreq
      have hjlen : j=ctx.frames.length := by
        have hnil := List.drop_eq_nil_iff.mp hdrop.symm
        omega
      subst j
      exact ⟨st,rfl,heq,hreq⟩
    | cons frame rest ih =>
      intro j st hdrop hj heq hreq
      have hf : ctx.frames[j]?=some frame := by
        have hh := congrArg (fun fs : List ApiAdaptive.Frame=>fs[0]?) hdrop
        simpa only [List.getElem?_cons_zero,List.getElem?_drop,Nat.add_zero] using hh.symm
      have hrest : rest=ctx.frames.drop (j+1) := by
        have hh := congrArg (List.drop 1) hdrop
        simpa only [List.drop_succ_cons,List.drop_zero,List.drop_drop] using hh
      have hjnext : j+1≤ctx.frames.length := (List.getElem?_eq_some_iff.mp hf).1
      have hmapped := NativeRekeyApi.issue_frame_map f policy s s' hs ctx.codec ctx.geo.cfg ctx.geo.shapes
        ctx.unit ctx.schedule ctx.init (IdealHierarchy.words tape) (IdealHierarchy.words tape') hw
        (IdealHierarchy.dummy tape) ctx.compiled st (htables j frame hf st heq) frame
      have htarget := NativeMatchApiProjection.frame_agreement cc hm hv policy s' tape' hcap hn hoff j frame hf
      rw [hd,heq] at hmapped
      change issueFrame policy s' ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule
        (ctx.init.map (rec f)) (IdealHierarchy.words tape') (IdealHierarchy.dummy tape')
        (NativeRekeyApi.chooseMap f ctx.compiled) (ref j) frame = .ok (ref (j+1)) at htarget
      rw [htarget] at hmapped
      cases hnxt : issueFrame policy s ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.init
          (IdealHierarchy.words tape) (IdealHierarchy.dummy tape') ctx.compiled st frame with
      | error e => simp only [hnxt,Except.map] at hmapped; cases hmapped
      | ok next =>
        have heqnext : NativeRekeyApi.state f next=ref (j+1) := by
          simpa only [hnxt,Except.map,Except.ok.injEq] using hmapped.symm
        have hnxt' : issueFrame policy s ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.init
            (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) ctx.compiled st frame=.ok next := by
          rw [hd]; exact hnxt
        have hreqnext : next.requests=reqs (j+1) := by
          rw [issue_requests policy s ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.init
            (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) ctx.compiled st next frame hnxt',
            hreq,hchoice j frame hf st heq]
          simp only [reqs,ApiAdaptive.requestGroups,List.take_add_one,hf,Option.toList_some,
            List.map_append,List.map_cons,List.map_nil,List.flatMap_append,List.flatMap_cons,
            List.flatMap_nil,List.append_nil]
        obtain ⟨out,hout,hmap,hrequests⟩ := ih (j+1) next hrest hjnext heqnext hreqnext
        refine ⟨out,?_,hmap,hrequests⟩
        rw [execute,hnxt']
        exact hout
  have hzero : NativeRekeyApi.state f (empty : State ctx.transcriptWidth)=ref 0 := by
    rw [show ref 0=empty from NativeMatchApiProof.referenceState_zero _ _ _ _ _ _ _ _ _]
    rfl
  obtain ⟨out,hout,hmap,hreq⟩ := hchain ctx.frames 0 empty (by simp) (Nat.zero_le _) hzero rfl
  refine ⟨out,hout,?_,?_⟩
  · exact hmap.trans (NativeMatchApiProjection.referenceState_full cc hm hv tape')
  · simpa only [reqs,List.take_length] using hreq

end RebuildBound.NativeRekeyApiGuard
