import RebuildBound.Proofs.NativeMatchLivePublic.NativeSemanticFailure

namespace RebuildBound.NativeMatchSemanticCoherence
open Model Model.Online Spec Spec.NativeMatchApi
open NativeMatchSemanticProof

set_option maxHeartbeats 0

 def post (c : Api.Codec) (q : Api.Request) (r : Probe.Result) : Rec := Api.postRecord c q r.found
 def opRecords (o : OnlineBatch.Op) : List Rec := o.lanes.map Prod.fst
 def records (ops : List OnlineBatch.Op) : List Rec := ops.flatMap opRecords
 def Consistent (c : Api.Codec) {m} (st : State m) : Prop :=
   st.selected.length=st.requests.length ∧ records st.ops=List.zipWith (post c) st.requests st.selected

 lemma chunk_post (policy : Policy) (stored : LogicalKey → NativeMatch.Lanes.Stored) (c : Api.Codec)
    (cfg : Config) (sh : Hierarchy.Shapes) (g : OnlineGeom) (S : Schedule) (init : List Rec)
    (words : Hierarchy.Words) (dummy : Nat → Nat → Nat) (operation start : Nat)
    (st : Requester.State) (qs : List Api.Request) (earlier rs : List Rec) (selected : List Probe.Result)
    (h : chunk policy stored c cfg sh g S init words dummy operation start st earlier qs = .ok (rs,selected)) :
    selected.length=qs.length ∧ rs=List.zipWith (post c) qs selected := by
  induction qs generalizing earlier rs selected with
  | nil =>
    simp only [chunk,Except.ok.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact ⟨rfl,rfl⟩
  | cons q qs ih =>
    cases hq : query policy stored cfg sh g S init (fun r=>c.flag r.val) words dummy
      operation start earlier.length st earlier q.key with
    | error err => simp [chunk,hq,Bind.bind,Except.bind] at h
    | ok answer =>
      cases hr : chunk policy stored c cfg sh g S init words dummy operation start st
        (earlier++[Api.postRecord c q answer.found]) qs with
      | error err => simp [chunk,hq,Bind.bind,Except.bind,hr] at h
      | ok rest =>
        simp only [chunk,hq,Bind.bind,Except.bind,Pure.pure,Except.pure,hr,Except.ok.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        have hi := ih _ _ _ hr
        exact ⟨congrArg Nat.succ hi.1,by simp only [List.zipWith_cons_cons,←hi.2,post]⟩

 lemma operation_post (policy : Policy) (stored : LogicalKey → NativeMatch.Lanes.Stored) (c : Api.Codec)
    (cfg : Config) (sh : Hierarchy.Shapes) (g : OnlineGeom) (S : Schedule) (init : List Rec)
    (words : Hierarchy.Words) (dummy : Nat → Nat → Nat) {m} (st : State m)
    (group : PublicApi.Group Api.Request) (result : OnlineBatch.Op × List Probe.Result)
    (h : operation policy stored c cfg sh g S init words dummy st group = .ok result) :
    result.2.length=group.lanes.length ∧ opRecords result.1=List.zipWith (post c) group.lanes result.2 := by
  cases group with
  | blind q =>
    simp only [operation,Except.ok.injEq] at h
    subst result
    exact ⟨rfl,rfl⟩
  | chunk qs =>
    cases hr : chunk policy stored c cfg sh g S init words dummy st.ops.length st.rows.length st.requester [] qs with
    | error err => simp [operation,hr,Bind.bind,Except.bind] at h
    | ok res =>
      simp only [operation,hr,Bind.bind,Except.bind,Pure.pure,Except.pure,Except.ok.injEq] at h
      subst result
      obtain ⟨hlen,hpost⟩ := chunk_post policy stored c cfg sh g S init words dummy _ _ _ qs [] _ _ hr
      refine ⟨hlen,?_⟩
      simp only [opRecords,OnlineBatch.Op.lanes,List.map_map,Function.comp_def,PublicApi.Group.lanes]
      change res.1.map id = _
      rw [List.map_id]
      exact hpost

 lemma issue_consistent (policy : Policy) (stored : LogicalKey → NativeMatch.Lanes.Stored) (c : Api.Codec)
    (cfg : Config) (sh : Hierarchy.Shapes) (g : OnlineGeom) (S : Schedule) (init : List Rec)
    (words : Hierarchy.Words) (dummy : Nat → Nat → Nat) {m} (choose : ApiAdaptive.Chooser m)
    (st next : State m) (frame : ApiAdaptive.Frame) (hc : Consistent c st)
    (h : issueFrame policy stored c cfg sh g S init words dummy choose st frame = .ok next) :
    Consistent c next := by
  cases ho : operation policy stored c cfg sh g S init words dummy st
    (ApiAdaptive.requests choose st.rows frame) with
  | error err => simp [issueFrame,ho,Bind.bind,Except.bind] at h
  | ok result =>
    simp only [issueFrame,ho,Bind.bind,Except.bind,Pure.pure,Except.pure,Except.ok.injEq] at h
    subst next
    have hr := operation_post policy stored c cfg sh g S init words dummy st _ result ho
    constructor
    · simp only [List.length_append,hc.1,hr.1]
    · change records (st.ops++[result.1]) = _
      simp only [records,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
      rw [show st.ops.flatMap opRecords=List.zipWith (post c) st.requests st.selected from hc.2,
        hr.2,List.zipWith_append hc.1.symm]

 lemma execute_consistent (policy : Policy) (stored : LogicalKey → NativeMatch.Lanes.Stored) (c : Api.Codec)
    (cfg : Config) (sh : Hierarchy.Shapes) (g : OnlineGeom) (S : Schedule) (init : List Rec)
    (words : Hierarchy.Words) (dummy : Nat → Nat → Nat) {m} (choose : ApiAdaptive.Chooser m)
    (frames : List ApiAdaptive.Frame) (st next : State m) (hc : Consistent c st)
    (h : execute policy stored c cfg sh g S init words dummy choose st frames = .ok next) :
    Consistent c next := by
  induction frames generalizing st with
  | nil => simp only [execute,Except.ok.injEq] at h; exact h ▸ hc
  | cons frame rest ih =>
    cases hf : issueFrame policy stored c cfg sh g S init words dummy choose st frame with
    | error err => simp [execute,hf,Bind.bind,Except.bind] at h
    | ok mid =>
      simp only [execute,hf,Bind.bind,Except.bind] at h
      exact ih mid (issue_consistent policy stored c cfg sh g S init words dummy choose st mid frame hc hf) h

 lemma run_consistent (policy : Policy) (stored : LogicalKey → NativeMatch.Lanes.Stored) (c : Api.Codec)
    (cfg : Config) (sh : Hierarchy.Shapes) (g : OnlineGeom) (S : Schedule) (init : List Rec)
    (words : Hierarchy.Words) (dummy : Nat → Nat → Nat) {m} (choose : ApiAdaptive.Chooser m)
    (frames : List ApiAdaptive.Frame) (next : State m)
    (h : run policy stored c cfg sh g S init words dummy choose frames = .ok next) :
    Consistent c next :=
  execute_consistent policy stored c cfg sh g S init words dummy choose frames empty next ⟨rfl,rfl⟩ h

 lemma slots_records (run : OnlineBatch.BatchRun) :
    (OnlineBatch.slots run).map OnlineBatch.Slot.record = records run.ops := by
  have inner (op : OnlineBatch.Op) (i : Nat) :
      ((op.lanes.zipIdx).map (fun rl : (Rec×Bool)×Nat =>
        (⟨i,rl.2,rl.1.1,rl.1.2⟩ : OnlineBatch.Slot))).map OnlineBatch.Slot.record = opRecords op := by
    simp only [List.map_map,Function.comp_def,opRecords]
    change (op.lanes.zipIdx.map (Prod.fst ∘ Prod.fst)) = _
    rw [←List.map_map,List.zipIdx_map_fst]
  simp only [OnlineBatch.slots,List.map_flatMap,inner,records]
  have he := congrArg (List.flatMap opRecords) (List.zipIdx_map_fst 0 run.ops)
  simpa only [List.flatMap_map,Function.comp_def] using he

 lemma coherent_of_consistent (c : Api.Codec) {m} (st : State m) (init : List Rec) (unsh : Rec → Bool)
    (hc : Consistent c st) :
    Coherent c ⟨st.ops,init,unsh⟩ st.requests (fun t=>st.selected.getD t ⟨none,[]⟩) := by
  let r : OnlineBatch.BatchRun := ⟨st.ops,init,unsh⟩
  have hs : (OnlineBatch.slots r).map OnlineBatch.Slot.record = List.zipWith (post c) st.requests st.selected :=
    (slots_records r).trans hc.2
  have hlen : st.requests.length=(OnlineBatch.slots r).length := by
    have he := congrArg List.length hs
    simpa only [List.length_map,List.length_zipWith,hc.1,Nat.min_self] using he.symm
  refine ⟨hlen,?_⟩
  intro t q slot hq hslot
  have ht := (List.getElem?_eq_some_iff.mp hq).1
  have htsel : t<st.selected.length := by rw [hc.1]; exact ht
  have hr : st.selected[t]?=some st.selected[t] := List.getElem?_eq_getElem htsel
  change (OnlineBatch.slots r)[t]?=some slot at hslot
  have he := congrArg (fun xs => xs[t]?) hs
  simp only [List.getElem?_map,hslot,Option.map_some,List.getElem?_zipWith,hq,hr,Option.some.injEq] at he
  change slot.record=post c q (st.selected.getD t ⟨none,[]⟩)
  rw [List.getD_eq_getElem st.selected _ htsel]
  exact he

 lemma run_coherent (policy : Policy) (stored : LogicalKey → NativeMatch.Lanes.Stored) (c : Api.Codec)
    (cfg : Config) (sh : Hierarchy.Shapes) (g : OnlineGeom) (S : Schedule) (init : List Rec)
    (words : Hierarchy.Words) (dummy : Nat → Nat → Nat) {m} (choose : ApiAdaptive.Chooser m)
    (frames : List ApiAdaptive.Frame) (next : State m)
    (h : run policy stored c cfg sh g S init words dummy choose frames = .ok next) :
    Coherent c ⟨next.ops,init,fun r=>c.flag r.val⟩ next.requests
      (fun t=>next.selected.getD t ⟨none,[]⟩) :=
  coherent_of_consistent c next init _
    (run_consistent policy stored c cfg sh g S init words dummy choose frames next h)

 lemma production_coherent {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : NativeMatchProduction.Context member initialized h) (policy : Policy)
    (stored : LogicalKey → NativeMatch.Lanes.Stored) (tape : IdealKey.Tape)
    (st : State ctx.transcriptWidth) (hs : production ctx policy stored tape=.ok st) :
    Coherent ctx.codec ⟨st.ops,ctx.init,fun r=>ctx.codec.flag r.val⟩ st.requests
      (fun t=>st.selected.getD t ⟨none,[]⟩) :=
  run_coherent policy stored ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.init
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) ctx.compiled ctx.frames st hs

end RebuildBound.NativeMatchSemanticCoherence
