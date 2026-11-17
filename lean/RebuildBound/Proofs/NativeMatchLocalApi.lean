import RebuildBound.Spec.NativeMatch.LocalApi
import RebuildBound.Proofs.NativeMatchApi

/-! Local exact-byte normalization agreement. The existing semantic replay is
reused below the two former global-collision discharge sites. A pair inventory
chosen from the canonical routing experiment covers both probes and requester
updates; no stored-fingerprint value controls its construction. -/
namespace RebuildBound.NativeMatchLocalApiProof
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch
open Spec NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchHierarchy NativeMatchDispatch
open NativeMatchApi NativeRoutingActual NativeMatchProduction NativeMatchExactPairs
open NativeNormalizePairs NativeMatchLocalApi
open NativeMatchApiProof NativeMatchApiProjection BatchFreshProof
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

lemma requesterStep_off (checked : NativeMatchExactPairsRun_statement)
    (mode : Nat → Mode) (stored : LogicalKey → Stored)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun) (S : Schedule) (words : Words)
    (j : Nat) (op : OnlineBatch.Op) (ho : run.ops[j]? = some op)
    (hn : ¬PairBad stored (runPairs cfg sh g run S words))
    (hoff : ∀ e ∈ batchPrefixEvents cfg sh g run S words (slots run).length, ¬e.bad stored) :
    requesterStep mode stored g.unitEntries (OnlineBatch.stateAt g run j) op.requester =
      Requester.step g.unitEntries (OnlineBatch.stateAt g run j) op.requester := by
  apply NativeMatchDispatchProof.requesterStep_agreement mode stored g.unitEntries _ op.requester
    (NativeMatchDenseTraceProof.requester_unique g run j)
    (fun hb => hn ((checked stored cfg sh g run S words).mpr (Or.inr ⟨j, op, ho, hb⟩)))
  cases op with
  | probe r => simp [OnlineBatch.Op.requester]
  | blind r => simp [OnlineBatch.Op.requester]
  | batch lanes =>
    intro _ e he
    exact hoff e (batchRemoval_in_query cfg sh g run S words j lanes ho e he)

lemma query_context (checked : NativeMatchExactPairsRun_statement) (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (policy : Policy) (stored : LogicalKey→Stored) (tape : IdealKey.Tape)
    (hcap : ¬ctx.capacityBad tape)
    (hn : ¬PairBad stored (exactPairs ctx tape))
    (hoff : ∀ e∈referenceEvents ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
      (IdealHierarchy.words tape) ctx.accesses, ¬e.bad stored)
    (t : Nat) (s : OnlineBatch.Slot) (hs : (slots (ctx.run tape))[t]?=some s) (hp : s.probes=true) :
    query policy stored ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.init
      (fun r=>ctx.codec.flag r.val) (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)
      s.op (fs (ctx.run tape) s.op) s.lane (OnlineBatch.stateAt ctx.unit (ctx.run tape) s.op)
      (Probe.earlier (ctx.run tape) s) s.record.key =
        .ok (Probe.batch ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
          (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) t) := by
  have htn : t<ctx.accesses := by
    rw [←slots_length ctx tape]
    exact (List.getElem?_eq_some_iff.mp hs).1
  have hc := NativeMatchApiReference.contracts ctx hm hv tape
  have hstruct := NativeMatchProductionProof.structural ctx hm
  have hgeom := NativeMatchProductionProof.alignment member hm initialized h
  have hi : ((ctx.run tape).init.map Rec.key).Nodup := hv.1.1
  have hready : RunReady member initialized h (ctx.run tape) :=
    ⟨hi,NativeMatchProductionProof.init_bound ctx hm hv tape,hc.1.2.1⟩
  have hoffR : OffEvents stored ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape))
      (IdealHierarchy.words tape) := by
    intro job hj hwithin e he
    apply hoff e
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨job,List.mem_filter.mpr ⟨hj,by simpa using hwithin⟩,he⟩
  have ht := NativeMatchApiScheduledReplay.tables member initialized hm h (ctx.run tape) hready
    ctx.schedule ctx.accesses ctx.transcriptWidth hv.2.2.1 hv.2.1 stored (IdealHierarchy.words tape)
    hcap hoffR t s hs htn
  apply query_batch_of_tables policy stored ctx.geo hstruct ctx.unit (ctx.run tape) hc.1.1
    (NativeMatchProductionProof.init_bound ctx hm hv tape) hc.1.2.1 ctx.schedule
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) t s hs hp
  · intro c hcm
    exact (ht c (by simpa only [slotSchedule,chunkStart_slot _ hs] using hcm)).1
  · intro c hcm
    obtain ⟨bounds,out,he,heq⟩ := ht c hcm
    refine ⟨out,?_,heq⟩
    rw [nativeTable_at_state ctx.geo hstruct.1 ctx.unit hgeom (by change 0<64; decide) (ctx.run tape)
      ctx.schedule ctx.accesses ctx.transcriptWidth hv.2.2.1 stored (IdealHierarchy.words tape)
      s.op (lt_of_le_of_lt (fs_le _ hs) htn) c hcm bounds.1 bounds.2.1]
    exact he
  · intro hb
    exact hn ((checked stored ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
      (IdealHierarchy.words tape)).mpr (Or.inl ⟨t, by simpa only [slots_length ctx tape] using htn, hb⟩))
  · intro e he
    apply hoff e
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨t,List.mem_range.mpr htn,he⟩)


lemma frame_agreement (checked : NativeMatchExactPairsRun_statement) (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (policy : Policy) (stored : LogicalKey→Stored) (tape : IdealKey.Tape)
    (hcap : ¬ctx.capacityBad tape)
    (hn : ¬PairBad stored (exactPairs ctx tape))
    (hoff : ∀ e∈referenceEvents ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
      (IdealHierarchy.words tape) ctx.accesses, ¬e.bad stored)
    (j : Nat) (frame : ApiAdaptive.Frame) (hf : ctx.frames[j]?=some frame) :
    issueFrame policy stored ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.init
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) ctx.compiled
      (referenceState ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (NativeMatchApiReference.requests ctx tape)
        j ctx.transcriptWidth) frame =
      .ok (referenceState ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (NativeMatchApiReference.requests ctx tape)
        (j+1) ctx.transcriptWidth) := by
  let state := referenceState ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (NativeMatchApiReference.requests ctx tape) j ctx.transcriptWidth
  let group := ApiAdaptive.requests ctx.compiled (NativeMatchApiReference.rows ctx tape) frame
  obtain ⟨op,ho,hkind⟩ := NativeMatchApiReference.frame_operation ctx tape j frame hf
  have hlen := NativeMatchApiReference.sameKind_length _ _ hkind
  have hslice := NativeMatchApiReference.frame_request_slice ctx tape j frame hf
  rw [←hlen] at hslice
  have hchoice : ApiAdaptive.requests ctx.compiled state.rows frame=group := by
    rw [reference_rows ctx hm hv tape j]
    exact NativeMatchApiReference.frame_requests ctx tape j frame hf
  have hoplen : state.ops.length=j := by
    simp only [state,referenceState,List.length_take,Nat.min_eq_left (Nat.le_of_lt (List.getElem?_eq_some_iff.mp ho).1)]
  have hrowlen : state.rows.length=fs (ctx.run tape) j := by
    simp only [state,referenceState,List.length_map,List.length_range,fs]
  have hquery := query_context checked ctx hm hv policy stored tape hcap hn hoff
  have himpl := NativeMatchApiReference.implements ctx hm hv tape
  have heval : operation policy stored ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.init
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) state group =
      .ok (op,(List.range op.lanes.length).map (fun i => Probe.batch ctx.geo.cfg ctx.geo.shapes ctx.unit
        (ctx.run tape) ctx.schedule (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (fs (ctx.run tape) j+i))) := by
    cases hg : group with
    | blind q =>
      have hk : NativeMatchApiReference.SameKind (.blind q) op := by rw [←hg]; exact hkind
      cases op with
      | probe r => exact False.elim hk
      | batch rs => exact False.elim hk
      | blind r =>
        have hreq := NativeMatchApiReference.frame_request_slot ctx tape j 0 frame q hf
          (show (ApiAdaptive.requests ctx.compiled (NativeMatchApiReference.rows ctx tape) frame).lanes[0]?=some q by
            change group.lanes[0]?=some q
            simp [hg,PublicApi.Group.lanes])
        have hslot := slot_at (ctx.run tape) ho (show (OnlineBatch.Op.blind r).lanes[0]?=some (r,false) from rfl)
        simp only [Nat.add_zero] at hreq hslot
        have hi := himpl.slot (fs (ctx.run tape) j) q ⟨j,0,r,false⟩ hreq hslot
        have hp : Probe.batch ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
            (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (fs (ctx.run tape) j)=⟨none,[]⟩ := by
          simp only [Probe.batch,hslot,Bool.false_eq_true,↓reduceIte]
        have hr : r=Api.postRecord ctx.codec q none := by simpa only [hp] using hi.2.2
        simp [operation,hr,OnlineBatch.Op.lanes,hp]
    | chunk qs =>
      have hk : NativeMatchApiReference.SameKind (.chunk qs) op := by rw [←hg]; exact hkind
      cases op with
      | probe r => exact False.elim hk
      | blind r => exact False.elim hk
      | batch records =>
        simp only [OnlineBatch.Op.lanes,List.length_map]
        apply operation_chunk_reference policy stored ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule
          (ctx.run tape) (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) j ctx.transcriptWidth state
          hoplen hrowlen rfl rfl records qs ho hk.symm
        · intro i q r hq hr
          have hreq := NativeMatchApiReference.frame_request_slot ctx tape j i frame q hf
            (show (ApiAdaptive.requests ctx.compiled (NativeMatchApiReference.rows ctx tape) frame).lanes[i]?=some q by
              change group.lanes[i]?=some q
              simpa only [hg,PublicApi.Group.lanes] using hq)
          have hslot := slot_at (ctx.run tape) ho (show (OnlineBatch.Op.batch records).lanes[i]?=some (r,true) by
            simp only [OnlineBatch.Op.lanes,List.getElem?_map,hr,Option.map_some])
          have hi := himpl.slot (fs (ctx.run tape) j+i) q ⟨j,i,r,true⟩ hreq hslot
          exact ⟨hi.1,hi.2.2⟩
        · exact hquery
  have hstep := requesterStep_off checked (policy state.ops.length (.unit state.requester.frozen.length)) stored
    ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule (IdealHierarchy.words tape) j op ho hn
    (fun e he => hoff e (List.mem_append_right _ (by simpa only [slots_length ctx tape] using he)))
  have hh := issueFrame_from_operation policy stored ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule
    ctx.init (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) ctx.compiled state frame group op _ hchoice heval hstep
  rw [referenceState_succ ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (NativeMatchApiReference.requests ctx tape)
    j ctx.transcriptWidth op ho group.lanes hslice]
  exact hh


lemma projection_raw (checked : NativeMatchExactPairsRun_statement) (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (policy : Policy) (stored : LogicalKey→Stored) (tape : IdealKey.Tape)
    (hcap : ¬ctx.capacityBad tape)
    (hn : ¬PairBad stored (exactPairs ctx tape))
    (hoff : ∀ e∈referenceEvents ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
      (IdealHierarchy.words tape) ctx.accesses, ¬e.bad stored) :
    production ctx policy stored tape=.ok (reference ctx tape) := by
  have hh := execute_chain policy stored ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.init
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) ctx.compiled
    (fun j=>referenceState ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (NativeMatchApiReference.requests ctx tape)
      j ctx.transcriptWidth) ctx.frames 0 (by
        intro i frame hf
        simpa only [Nat.zero_add] using frame_agreement checked ctx hm hv policy stored tape hcap hn hoff i frame hf)
  rw [referenceState_zero,Nat.zero_add,referenceState_full ctx hm hv tape] at hh
  exact hh

lemma reference_events_off (ctx : Context member initialized h)
    (stored : LogicalKey → Stored) (tape : IdealKey.Tape)
    (hcap : ¬ctx.capacityBad tape)
    (hready : NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true)
    (hoff : ∀ e ∈ ctx.inventory tape, ¬e.bad stored) :
    ∀ e ∈ referenceEvents ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
      (IdealHierarchy.words tape) ctx.accesses, ¬e.bad stored := by
  classical
  have hi : ctx.inventory tape = referenceEvents ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape)
      ctx.schedule (IdealHierarchy.words tape) ctx.accesses := by
    change (if Fails ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape)) (IdealHierarchy.words tape) ∨
      NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = false then [] else _) = _
    rw [ite_eq_right (fun hbad => hbad.elim hcap (fun hb => by rw [hready] at hb; contradiction))]
    rfl
  simpa only [hi] using hoff

lemma cascadePairs_finiteRead (cfg : Config) (sh : Shapes) (tr : Trace)
    (key : LogicalKey) (cs : List (Nat × Nat)) :
    IdealKey.FiniteRead (fun tape => cascadePairs key
      (fun c => table cfg sh tr (IdealHierarchy.words tape) c.1 c.2) cs) := by
  induction cs with
  | nil => exact IdealKey.FiniteRead.const []
  | cons c cs ih =>
    have here := (IdealTableFiniteRead cfg sh tr c.1 c.2).comp
      (fun out => scanPairs out key)
    exact (here.pair ih).comp (fun p => p.1 ++ p.2)

lemma batchPairs_finiteRead (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : BatchRun) (S : Schedule) (t : Nat) :
    IdealKey.FiniteRead (fun tape => batchPairs cfg sh g run S (IdealHierarchy.words tape) t) := by
  cases hs : (slots run)[t]? with
  | none => simpa only [batchPairs, hs] using (IdealKey.FiniteRead.const ([] : Pairs LogicalKey))
  | some slot =>
    by_cases hp : slot.probes = true
    · simpa only [batchPairs, hs, hp, ite_true] using
        (cascadePairs_finiteRead cfg sh (OnlineBatch.traceOf g run) slot.record.key
          (slotSchedule (widths run) S t).tables).comp
          (fun pairs => listPairs (Probe.earlier run slot) slot.record.key ++
            pagesPairs (batchPages cfg g run S t) slot.record.key ++ pairs)
    · simpa [batchPairs, hs, hp] using (IdealKey.FiniteRead.const ([] : Pairs LogicalKey))

lemma runPairs_finiteRead (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : BatchRun) (S : Schedule) :
    IdealKey.FiniteRead (fun tape => runPairs cfg sh g run S (IdealHierarchy.words tape)) := by
  have hr := IdealKey.FiniteRead.list_map (List.range (slots run).length)
    (fun t tape => batchPairs cfg sh g run S (IdealHierarchy.words tape) t)
    (fun t => batchPairs_finiteRead cfg sh g run S t)
  simpa only [runPairs, batchPrefixPairs, List.flatMap_map, Function.comp_def, id_eq] using
    hr.comp (fun xs => xs.flatMap id ++ (run.ops.zipIdx).flatMap fun oj =>
      requesterPairs (OnlineBatch.stateAt g run oj.2) oj.1.requester)

lemma exactPairs_finiteRead (ctx : Context member initialized h) :
    IdealKey.FiniteRead (exactPairs ctx) := by
  have hr := (IdealAdaptiveFiniteRead ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule
    ctx.transcriptWidth ctx.client).comp
    (fun result => (⟨result.1, ctx.client.init, ctx.client.unsh⟩ : BatchRun))
  exact hr.bind (fun run tape => runPairs ctx.geo.cfg ctx.geo.shapes ctx.unit run ctx.schedule
    (IdealHierarchy.words tape)) (fun run => runPairs_finiteRead _ _ _ run _)

end RebuildBound.NativeMatchLocalApiProof

namespace RebuildBound
open Spec NativeMatchLocalApiProof

theorem NativeMatchLocalApiFiniteRead : Spec.NativeMatchLocalApiFiniteRead_statement := by
  intro member initialized h ctx
  exact exactPairs_finiteRead ctx

theorem NativeMatchLocalApiFrame : Spec.NativeMatchLocalApiFrame_statement := by
  intro checked member initialized h ctx hm hv policy stored tape hcap hready hn hoff j frame hf
  exact frame_agreement checked ctx hm hv policy stored tape hcap hn
    (reference_events_off ctx stored tape hcap hready hoff) j frame hf

theorem NativeMatchLocalApiProjection : Spec.NativeMatchLocalApiProjection_statement := by
  intro checked member initialized h ctx hm hv policy stored tape hcap hready hn hoff
  exact projection_raw checked ctx hm hv policy stored tape hcap hn
    (reference_events_off ctx stored tape hcap hready hoff)

end RebuildBound
