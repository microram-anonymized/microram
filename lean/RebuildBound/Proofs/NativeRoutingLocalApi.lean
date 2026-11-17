import RebuildBound.Spec.NativeRouting.LocalApi
import RebuildBound.Proofs.NativeRoutingLocalNative
import RebuildBound.Proofs.NativeMatchLocalBound

namespace RebuildBound.NativeRoutingLocalApiProof
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch
open Spec NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchHierarchy NativeMatchDispatch
open NativeMatchApi NativeRoutingActual NativeMatchProduction NativeMatchExactPairs
open NativeNormalizePairs NativeMatchLocalApi NativeRoutingLocalApi
open NativeMatchApiProof NativeMatchApiProjection BatchFreshProof
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

lemma diagnostic_mem (ctx : Context member initialized h) (tape : IdealKey.Tape)
    (t : Nat) (ht : t < ctx.accesses) (s : OnlineBatch.Slot)
    (hs : (slots (ctx.run tape))[t]? = some s) (hp : s.probes = true)
    (c : Nat × Nat) (hc : c ∈ (slotSchedule (widths (ctx.run tape)) ctx.schedule t).tables)
    (d : NativeRoutingLocalDiagnostics.Diagnostic)
    (hd : d ∈ (ReadTree.evaluate tape
      (NativeRoutingLocalDiagnostics.tableProgram ctx.geo.cfg ctx.geo.shapes
        (traceOf ctx.unit (ctx.run tape)) c.1 c.2)).diagnostics) :
    d ∈ diagnostics ctx tape := by
  apply List.mem_flatMap.mpr
  refine ⟨t, List.mem_range.mpr ht, ?_⟩
  simp only [hs, hp, ite_true]
  exact List.mem_flatMap.mpr ⟨c, hc, hd⟩

lemma query_context (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (policy : Policy) (stored : LogicalKey → Stored) (tape : IdealKey.Tape)
    (hsafe : Safe ctx stored tape)
    (t : Nat) (s : OnlineBatch.Slot) (hs : (slots (ctx.run tape))[t]? = some s) (hp : s.probes = true) :
    query policy stored ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.init
      (fun r => ctx.codec.flag r.val) (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)
      s.op (fs (ctx.run tape) s.op) s.lane (stateAt ctx.unit (ctx.run tape) s.op)
      (Probe.earlier (ctx.run tape) s) s.record.key =
        .ok (Probe.batch ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
          (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) t) := by
  have htn : t < ctx.accesses := by
    rw [← slots_length ctx tape]
    exact (List.getElem?_eq_some_iff.mp hs).1
  have hc := NativeMatchApiReference.contracts ctx hm hv tape
  have hstruct := NativeMatchProductionProof.structural ctx hm
  have hgeom := NativeMatchProductionProof.alignment member hm initialized h
  have hready : RunReady member initialized h (ctx.run tape) :=
    ⟨hv.1.1, NativeMatchProductionProof.init_bound ctx hm hv tape, hc.1.2.1⟩
  have hbounds := NativeMatchApiScheduledReplay.coordinate_bounds
    (HierarchySemanticsProof.lower hstruct.1) ctx.schedule ctx.accesses ctx.transcriptWidth
    hv.2.2.1 hv.2.1 (fs (ctx.run tape) s.op) ((fs_le _ hs).trans_lt htn)
  apply query_batch_of_tables policy stored ctx.geo hstruct ctx.unit (ctx.run tape) hc.1.1
    (NativeMatchProductionProof.init_bound ctx hm hv tape) hc.1.2.1 ctx.schedule
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) t s hs hp
  · intro c hcm
    have hb := hbounds c (by simpa only [slotSchedule, chunkStart_slot _ hs] using hcm)
    exact ⟨hb.1, hb.2.1, hb.2.2.1⟩
  · intro c hcm
    have hb := hbounds c hcm
    obtain ⟨out, he, heq⟩ := NativeRoutingLocalNativeTable member initialized hm h
      (ctx.run tape) hready stored tape c.1 c.2 hb.2.2.2 (by
        intro d hd
        exact hsafe.2.2.2 d (diagnostic_mem ctx tape t htn s hs hp c
          (by simpa only [slotSchedule, chunkStart_slot _ hs] using hcm) d hd))
    refine ⟨out, ?_, heq⟩
    rw [nativeTable_at_state ctx.geo hstruct.1 ctx.unit hgeom (by change 0 < 64; decide)
      (ctx.run tape) ctx.schedule ctx.accesses ctx.transcriptWidth hv.2.2.1 stored
      (IdealHierarchy.words tape) s.op ((fs_le _ hs).trans_lt htn) c hcm hb.1 hb.2.1]
    exact he
  · intro hbad
    exact hsafe.2.1 ((NativeMatchExactPairsRun stored ctx.geo.cfg ctx.geo.shapes ctx.unit
      (ctx.run tape) ctx.schedule (IdealHierarchy.words tape)).mpr
        (Or.inl ⟨t, by simpa only [slots_length ctx tape] using htn, hbad⟩))
  · intro e he
    exact hsafe.2.2.1 e (List.mem_flatMap.mpr ⟨t, List.mem_range.mpr htn, he⟩)

lemma frame_agreement (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (policy : Policy) (stored : LogicalKey→Stored) (tape : IdealKey.Tape)
    (hsafe : Safe ctx stored tape)
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
  have hquery := query_context ctx hm hv policy stored tape hsafe
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
  have hstep := NativeMatchLocalApiProof.requesterStep_off NativeMatchExactPairsRun (policy state.ops.length (.unit state.requester.frozen.length)) stored
    ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule (IdealHierarchy.words tape) j op ho hsafe.2.1
    (by simpa only [slots_length ctx tape] using hsafe.2.2.1)
  have hh := issueFrame_from_operation policy stored ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule
    ctx.init (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) ctx.compiled state frame group op _ hchoice heval hstep
  rw [referenceState_succ ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (NativeMatchApiReference.requests ctx tape)
    j ctx.transcriptWidth op ho group.lanes hslice]
  exact hh


lemma projection_raw (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (policy : Policy) (stored : LogicalKey→Stored) (tape : IdealKey.Tape)
    (hsafe : Safe ctx stored tape) :
    production ctx policy stored tape=.ok (reference ctx tape) := by
  have hh := execute_chain policy stored ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.init
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) ctx.compiled
    (fun j=>referenceState ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (NativeMatchApiReference.requests ctx tape)
      j ctx.transcriptWidth) ctx.frames 0 (by
        intro i frame hf
        simpa only [Nat.zero_add] using frame_agreement ctx hm hv policy stored tape hsafe i frame hf)
  rw [referenceState_zero,Nat.zero_add,referenceState_full ctx hm hv tape] at hh
  exact hh

lemma guard (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) (stored : NativeNormalize.Tape 128)
    (hoff : ¬NativeMatchLocalBound.bad ctx (tape, stored)) : Safe ctx stored tape := by
  have hcap : ¬ctx.capacityBad tape := fun hb => hoff (Or.inl (Or.inl hb))
  have hevents : ∀ e ∈ ctx.inventory tape, ¬e.bad stored :=
    fun e he hb => hoff (Or.inl (Or.inr ⟨e, he, hb⟩))
  have hr : NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true := by
    cases he : NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses with
    | false => exact (hoff (Or.inr (Or.inr he))).elim
    | true => rfl
  have hexact : ¬PairBad stored (exactPairs ctx tape) := by
    intro hb
    apply hoff
    apply Or.inr ∘ Or.inl
    simp only [NativeMatchLocalBound.normalizationPairs, hr, ite_true]
    exact (NativeNormalizePairsEvent.1 stored _ _).mpr (Or.inl hb)
  have hreference := NativeMatchLocalApiProof.reference_events_off ctx stored tape hcap hr hevents
  refine ⟨hr, hexact, ?_, ?_⟩
  · intro e he
    exact hreference e (List.mem_append_right _ he)
  · intro d hd
    obtain ⟨t, ht, hd⟩ := List.mem_flatMap.mp hd
    have htn := List.mem_range.mp ht
    cases hs : (slots (ctx.run tape))[t]? with
    | none => simp only [hs, List.not_mem_nil] at hd
    | some slot =>
      by_cases hp : slot.probes = true
      · simp only [hs, hp, ite_true] at hd
        obtain ⟨c, hc, hd⟩ := List.mem_flatMap.mp hd
        have hcompleted := NativeRoutingLocalPairsProof.scheduled_completed ctx hm hv tape t htn c hc
        have hbounds := (NativeRoutingBuildSupportProof.mem_completed _ _ _).mp hcompleted
        have hlocal := NativeRoutingLocalDiagnosticsContained member initialized h ctx hm hv tape
          c.1 c.2 hbounds.1 hbounds.2.1 hbounds.2.2.2 d hd
        constructor
        · apply Bool.eq_false_iff.mpr
          exact fun hb => hcap (hlocal.2.2.1 hb)
        · intro e he
          exact hreference e (List.mem_append_left _ (hlocal.2.2.2 e he))
      · simp [hs, hp] at hd


lemma reads_reply {Q α : Type} (tree : ReadTree Q α) (tape : Q → Word64) :
    ∀ e ∈ ReadTree.reads tape tree, tape e.1 = e.2 := by
  induction tree with
  | done result => simp [ReadTree.reads]
  | read query next ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · rfl
    · exact ih (tape query) e he

lemma memo_safe (logEvaluate : NativeRoutingLocalLogEvaluate_statement)
    (logMemo : NativeRoutingLocalLogMemo_statement)
    (logCongruence : NativeRoutingLocalLogCongruence_statement)
    (tableReads : NativeRoutingLocalLoggedTableReads_statement)
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (stored : LogicalKey → Stored) (tape : IdealKey.Tape) :
    Safe ctx stored (memoTape (ReadTree.reads tape
      (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))) ↔
      Safe ctx stored tape := by
  let tree := NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
  let memo := ReadTree.reads tape tree
  let other := memoTape memo
  have hlog := logMemo tree tape
  rw [logEvaluate] at hlog
  have hrun : ctx.run other = ctx.run tape := by
    unfold Context.run Adaptive.realized
    congr 1
    rw [← NativeRoutingLocalReplayEvaluate ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client other,
      ← NativeRoutingLocalReplayEvaluate ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client tape]
    exact congrArg Prod.fst hlog.1
  have hquery : ∀ q ∈ memo.map Prod.fst, other q = tape q := by
    intro q hq
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
    exact (hlog.2.2 e he).trans (reads_reply tree tape e he).symm
  have hlocal : ∀ t, t < ctx.accesses → ∀ s, (slots (ctx.run tape))[t]? = some s →
      s.probes = true → ∀ c ∈ (slotSchedule (widths (ctx.run tape)) ctx.schedule t).tables,
      ReadTree.evaluate other (NativeRoutingLocalDiagnostics.tableProgram ctx.geo.cfg ctx.geo.shapes
        (traceOf ctx.unit (ctx.run tape)) c.1 c.2) =
      ReadTree.evaluate tape (NativeRoutingLocalDiagnostics.tableProgram ctx.geo.cfg ctx.geo.shapes
        (traceOf ctx.unit (ctx.run tape)) c.1 c.2) := by
    intro t ht s hs hp c hc
    apply (logCongruence _ tape other ?_).1
    intro e he
    rw [NativeRoutingLocalDiagnosticsReads] at he
    have hq := tableReads member initialized h ctx hm hv tape t ht s hs hp c hc
      (List.mem_map.mpr ⟨e, he, rfl⟩)
    exact (hquery e.1 hq).trans (reads_reply _ tape e he)
  have htable : ∀ t, t < ctx.accesses → ∀ s, (slots (ctx.run tape))[t]? = some s →
      s.probes = true → ∀ c ∈ (slotSchedule (widths (ctx.run tape)) ctx.schedule t).tables,
      table ctx.geo.cfg ctx.geo.shapes (traceOf ctx.unit (ctx.run tape))
        (IdealHierarchy.words other) c.1 c.2 =
      table ctx.geo.cfg ctx.geo.shapes (traceOf ctx.unit (ctx.run tape))
        (IdealHierarchy.words tape) c.1 c.2 := by
    intro t ht s hs hp c hc
    have he := congrArg NativeRoutingLocalDiagnostics.Result.output (hlocal t ht s hs hp c hc)
    rw [NativeRoutingLocalDiagnosticsOutput ctx.geo.cfg ctx.geo.shapes
      (traceOf ctx.unit (ctx.run tape)) other c.1 c.2,
      NativeRoutingLocalDiagnosticsOutput ctx.geo.cfg ctx.geo.shapes
        (traceOf ctx.unit (ctx.run tape)) tape c.1 c.2] at he
    exact he
  have hdiag : diagnostics ctx other = diagnostics ctx tape := by
    unfold diagnostics
    rw [hrun]
    apply List.flatMap_congr
    intro t ht
    cases hs : (slots (ctx.run tape))[t]? with
    | none => rfl
    | some s =>
      by_cases hp : s.probes = true
      · simp only [hp, ite_true]
        apply List.flatMap_congr
        intro c hc
        exact congrArg NativeRoutingLocalDiagnostics.Result.diagnostics
          (hlocal t (List.mem_range.mp ht) s hs hp c hc)
      · simp [hp]
  have hpairs : exactPairs ctx other = exactPairs ctx tape := by
    unfold exactPairs runPairs
    rw [hrun]
    congr 1
    unfold batchPrefixPairs
    apply List.flatMap_congr
    intro t ht
    have htn : t < ctx.accesses := by simpa only [slots_length ctx tape] using List.mem_range.mp ht
    unfold batchPairs
    cases hs : (slots (ctx.run tape))[t]? with
    | none => rfl
    | some s =>
      by_cases hp : s.probes = true
      · simp only [hp, ite_true]
        congr 1
        unfold cascadePairs
        apply List.flatMap_congr
        intro c hc
        exact congrArg (fun out => scanPairs out s.record.key) (htable t htn s hs hp c hc)
      · simp [hp]
  have hevents : batchPrefixEvents ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run other)
      ctx.schedule (IdealHierarchy.words other) ctx.accesses =
      batchPrefixEvents ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape)
        ctx.schedule (IdealHierarchy.words tape) ctx.accesses := by
    rw [hrun]
    unfold batchPrefixEvents
    apply List.flatMap_congr
    intro t ht
    cases hs : (slots (ctx.run tape))[t]? with
    | none => simp only [batchEvents, hs]
    | some s =>
      by_cases hp : s.probes = true
      · exact NativeMatchDenseLocality.batch_congr _ _ _ _ _ _ _ _
          (htable t (List.mem_range.mp ht) s hs hp)
      · simp [batchEvents, hs, hp]
  change Safe ctx stored other ↔ Safe ctx stored tape
  unfold Safe
  rw [hpairs, hevents, hdiag, hrun]


end RebuildBound.NativeRoutingLocalApiProof

namespace RebuildBound
open Spec NativeRoutingLocalApiProof

theorem NativeRoutingLocalApiProjection : NativeRoutingLocalApiProjection_statement := by
  intro member initialized h ctx hm hv policy stored tape hsafe
  exact projection_raw ctx hm hv policy stored tape hsafe

theorem NativeRoutingLocalApiGuard : NativeRoutingLocalApiGuard_statement := by
  intro member initialized h ctx hm hv tape stored hoff
  exact guard ctx hm hv tape stored hoff

theorem NativeRoutingLocalApiMemoSafe : NativeRoutingLocalApiMemoSafe_statement := by
  intro logEvaluate logMemo logCongruence tableReads member initialized h ctx hm hv stored tape
  exact memo_safe logEvaluate logMemo logCongruence tableReads ctx hm hv stored tape

end RebuildBound
