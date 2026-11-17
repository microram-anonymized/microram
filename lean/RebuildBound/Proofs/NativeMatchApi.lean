import RebuildBound.Spec.NativeMatch.Api
import RebuildBound.Proofs.NativeMatchProduction
import RebuildBound.Proofs.ApiBounded
import RebuildBound.Proofs.NativeMatchHierarchy
import RebuildBound.Proofs.NativeRoutingActual
import RebuildBound.Proofs.AdaptiveFound.Causal
import RebuildBound.Proofs.AdaptiveFoundMem
import RebuildBound.Proofs.ApiLegal
import RebuildBound.Proofs.IdealGeometryFamily
import RebuildBound.Proofs.IdealGeometry.Arithmetic
import RebuildBound.Proofs.IdealProbe
import RebuildBound.Proofs.ApiAdaptive
import Mathlib.Tactic

namespace RebuildBound.NativeMatchApiReference
open Model Model.Hierarchy Model.Online Spec Spec.NativeMatchProduction
open NativeMatchProductionProof
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

def rows (ctx : Context member initialized h) (tape : IdealKey.Tape) :=
  (Adaptive.interact ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)).2

def requests (ctx : Context member initialized h) (tape : IdealKey.Tape) :=
  (ApiAdaptive.requestGroups ctx.compiled (rows ctx tape) ctx.frames).flatMap PublicApi.Group.lanes

theorem rows_length (ctx : Context member initialized h) (tape : IdealKey.Tape) :
    (rows ctx tape).length = ctx.accesses :=
  AdaptiveReplayProof.interact_rows_length _ _ _ _ _ _ _

theorem transcript_rows (ctx : Context member initialized h) (tape : IdealKey.Tape) :
    Adaptive.rowsOf (Adaptive.transcript ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
      ctx.accesses (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)) ctx.accesses = rows ctx tape := by
  have hr := AdaptiveReplayProof.rowsOf_transcript ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule
    ctx.client ctx.accesses rfl (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (rows ctx tape)
    (List.prefix_refl _)
  rw [rows_length] at hr
  exact hr.symm

theorem constructed (ctx : Context member initialized h) (tape : IdealKey.Tape) :
    ctx.run tape = ApiExecution.run ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.init
      (ApiAdaptive.requestGroups ctx.compiled (rows ctx tape) ctx.frames) := by
  have hi := ApiAdaptiveInteraction ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.init
    ctx.transcriptWidth ctx.frames ctx.compiled (ApiAdaptiveFrames ctx.batchWidth 64 ctx.batches).1
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)
  change ctx.run tape = ApiExecution.run ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.init
    (ApiAdaptive.requestGroups ctx.compiled (Adaptive.rowsOf
      (Adaptive.transcript ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client ctx.accesses
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)) ctx.accesses) ctx.frames) at hi
  rw [transcript_rows ctx tape] at hi
  exact hi

theorem contracts (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) :
    ApiRunCorrect ctx.geo ctx.codec ctx.unit (ctx.run tape) ctx.schedule (requests ctx tape) ∧
      ApiTopPopulations ctx.geo ctx.unit (ctx.run tape) := by
  have hc := ApiLegalLive ctx.geo (structural ctx hm) ctx.codec ctx.unit ctx.schedule ctx.init
    ctx.transcriptWidth ctx.batchWidth ctx.batches ctx.choose hv.1 (alignment member hm initialized h)
    (by change 0 < 64; decide) hv.2.1 hv.2.2.1 hv.2.2.2 (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)
  have hc' : ApiRunCorrect ctx.geo ctx.codec ctx.unit (ctx.run tape) ctx.schedule
      ((ApiAdaptive.requestGroups ctx.compiled (Adaptive.rowsOf
        (Adaptive.transcript ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client ctx.accesses
          (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)) ctx.accesses) ctx.frames).flatMap PublicApi.Group.lanes) ∧
      ApiTopPopulations ctx.geo ctx.unit (ctx.run tape) := ⟨hc.1,hc.2.1⟩
  rw [transcript_rows ctx tape] at hc'
  exact hc'

theorem implements (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) :
    Api.Implements ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (requests ctx tape) :=
  ((contracts ctx hm hv tape).1.2.2 (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)).1

theorem requests_length (ctx : Context member initialized h) (tape : IdealKey.Tape) :
    (requests ctx tape).length = ctx.accesses :=
  ApiAdaptiveCorrectnessProof.requests_length ctx.compiled _ ctx.frames

theorem batch_addresses (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) (t : Nat) (ht : t < ctx.accesses) (i : Nat) :
    (Probe.batch ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) t).addresses.getD i 0 =
        OnlineBatch.touched ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
          (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) t i := by
  have hi := implements ctx hm hv tape
  have hlen := requests_length ctx tape
  let q := (requests ctx tape)[t]
  have hq : (requests ctx tape)[t]? = some q := List.getElem?_eq_getElem (by omega)
  have hslot : t < (OnlineBatch.slots (ctx.run tape)).length := by rw [← hi.length,hlen]; exact ht
  let slot := (OnlineBatch.slots (ctx.run tape))[t]
  have hs : (OnlineBatch.slots (ctx.run tape))[t]? = some slot := List.getElem?_eq_getElem hslot
  by_cases hp : slot.probes = true
  · exact ((((contracts ctx hm hv tape).1.2.2 (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)).2.2
      t q slot hq hs).2.2 hp) i
  · simp only [Probe.batch,hs,hp]
    unfold OnlineBatch.touched
    cases hc : (OnlineBatch.slotSchedule (OnlineBatch.widths (ctx.run tape)) ctx.schedule t).tables[i]? <;>
      simp [hs,hp]
end RebuildBound.NativeMatchApiReference
namespace RebuildBound.NativeMatchApiReference
open Model Model.Hierarchy Model.Online Spec Spec.NativeMatchProduction
open NativeMatchProductionProof
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

theorem rows_eq_probes (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) :
    rows ctx tape = (List.range ctx.accesses).map (fun t (i : Fin ctx.transcriptWidth) =>
      (Probe.batch ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) t).addresses.getD i.val 0) := by
  rw [← transcript_rows ctx tape]
  rw [AdaptiveReplayProof.transcript_eq_view (RowCausalityStep TracePrefix TraceUnitsPrefix)
    ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client ctx.accesses rfl
    (alignment member hm initialized h) (by change 0 < 64; decide) hv.2.2.1]
  unfold Adaptive.rowsOf
  apply List.map_congr_left
  intro t ht
  have htn := List.mem_range.mp ht
  funext i
  simp only [htn,dite_true,OnlineBatch.view]
  exact (batch_addresses ctx hm hv tape t htn i.val).symm

theorem frame_requests_prefix {m : Nat} (choose : ApiAdaptive.Chooser m)
    (rows : List (Fin m→Nat)) (frame : ApiAdaptive.Frame) (cut : Nat)
    (hcut : frame.start ≤ cut) :
    ApiAdaptive.requests choose (rows.take cut) frame = ApiAdaptive.requests choose rows frame := by
  unfold ApiAdaptive.requests PublicApi.chosenLane
  simp only [List.take_take,Nat.min_eq_left hcut]
end RebuildBound.NativeMatchApiReference
namespace RebuildBound.NativeMatchApiReference
open Model Model.Hierarchy Model.Online Spec Spec.NativeMatchProduction
open NativeMatchProductionProof
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

theorem causal_start (frames : List ApiAdaptive.Frame) (start j : Nat) (frame : ApiAdaptive.Frame)
    (hc : ApiAdaptive.Causal start frames) (hf : frames[j]? = some frame) :
    frame.start ≤ start + Adaptive.slotCount (ApiAdaptive.shape (frames.take j)) := by
  induction frames generalizing start j with
  | nil => simp at hf
  | cons first rest ih =>
    cases j with
    | zero =>
      have he : first = frame := by simpa using hf
      subst frame
      simpa [List.take_zero,ApiAdaptive.shape,Adaptive.slotCount,Adaptive.shapeWidths] using hc.1
    | succ j =>
      have hr := ih (start+first.kind.width) j hc.2.2 (by simpa using hf)
      simpa only [List.take_succ_cons,ApiAdaptiveProof.count_cons,Nat.add_assoc] using hr

theorem prefix_slots (ctx : Context member initialized h) (tape : IdealKey.Tape) (j : Nat) :
    BatchFreshProof.fs (ctx.run tape) j = Adaptive.slotCount (ApiAdaptive.shape (ctx.frames.take j)) := by
  unfold BatchFreshProof.fs Context.run
  rw [AdaptiveCausalProof.realized_widths]
  simp [Context.client,ApiAdaptive.run,Adaptive.slotCount,Adaptive.shapeWidths,ApiAdaptive.shape,List.map_take]

theorem frame_requests (ctx : Context member initialized h) (tape : IdealKey.Tape)
    (j : Nat) (frame : ApiAdaptive.Frame) (hf : ctx.frames[j]? = some frame) :
    ApiAdaptive.requests ctx.compiled ((rows ctx tape).take (BatchFreshProof.fs (ctx.run tape) j)) frame =
      ApiAdaptive.requests ctx.compiled (rows ctx tape) frame := by
  apply ApiAdaptiveProof.requests_take
  rw [prefix_slots]
  simpa only [Nat.zero_add] using causal_start ctx.frames 0 j frame
    (ApiAdaptiveFrames ctx.batchWidth 64 ctx.batches).1 hf
end RebuildBound.NativeMatchApiReference
namespace RebuildBound.NativeMatchApiReference
open Model Model.Hierarchy Model.Online Model.PublicApi Spec Spec.NativeMatchProduction
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

def SameKind : PublicApi.Group Api.Request → OnlineBatch.Op → Prop
  | .blind _, .blind _ => True
  | .chunk qs, .batch rs => qs.length = rs.length
  | _, _ => False

theorem operation_kind (codec : Api.Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (schedule : Schedule) (init : List Rec) (pre : List OnlineBatch.Op) (group : PublicApi.Group Api.Request) :
    SameKind group (ApiExecution.operation codec cfg sh g schedule init pre group) := by
  cases group <;> simp [SameKind,ApiExecution.operation,ApiExecutionProof.chunkRecords_length]

theorem operations_at (codec : Api.Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (schedule : Schedule) (init : List Rec) (groups : List (PublicApi.Group Api.Request))
    (pre : List OnlineBatch.Op) (j : Nat) (group : PublicApi.Group Api.Request) (hg : groups[j]? = some group) :
    ∃ op, (ApiExecution.operations codec cfg sh g schedule init pre groups)[j]? = some op ∧ SameKind group op := by
  induction groups generalizing pre j with
  | nil => simp at hg
  | cons first rest ih =>
    cases j with
    | zero =>
      have he : first = group := by simpa using hg
      subst group
      exact ⟨_,rfl,operation_kind codec cfg sh g schedule init pre first⟩
    | succ j =>
      exact ih _ j (by simpa using hg)

theorem frame_operation (ctx : Context member initialized h) (tape : IdealKey.Tape)
    (j : Nat) (frame : ApiAdaptive.Frame) (hf : ctx.frames[j]? = some frame) :
    ∃ op, (ctx.run tape).ops[j]? = some op ∧
      SameKind (ApiAdaptive.requests ctx.compiled (rows ctx tape) frame) op := by
  rw [constructed ctx tape]
  apply operations_at
  simpa only [ApiAdaptive.requestGroups,List.getElem?_map,hf,Option.map_some]

theorem flatMap_slot {A B : Type} (items : List A) (f : A → List B) (j i : Nat) (item : A) (value : B)
    (hi : items[j]? = some item) (hv : (f item)[i]? = some value) :
    (items.flatMap f)[((items.take j).map fun x => (f x).length).sum+i]? = some value := by
  induction items generalizing j with
  | nil => simp at hi
  | cons head rest ih =>
    cases j with
    | zero =>
      have he : head = item := by simpa using hi
      subst item
      simpa only [List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add,List.flatMap_cons,
        List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1] using hv
    | succ j =>
      have hr := ih j (by simpa using hi)
      simpa only [List.take_succ_cons,List.map_cons,List.sum_cons,Nat.add_assoc,List.flatMap_cons,
        List.getElem?_append_right (Nat.le_add_right _ _),Nat.add_sub_cancel_left] using hr

theorem frame_request_slot (ctx : Context member initialized h) (tape : IdealKey.Tape)
    (j i : Nat) (frame : ApiAdaptive.Frame) (q : Api.Request)
    (hf : ctx.frames[j]? = some frame)
    (hq : (ApiAdaptive.requests ctx.compiled (rows ctx tape) frame).lanes[i]? = some q) :
    (requests ctx tape)[BatchFreshProof.fs (ctx.run tape) j+i]? = some q := by
  have hh := flatMap_slot ctx.frames (fun f => (ApiAdaptive.requests ctx.compiled (rows ctx tape) f).lanes)
    j i frame q hf hq
  rw [prefix_slots]
  simpa only [requests,ApiAdaptive.requestGroups,List.flatMap_map,Function.comp_def,
    ApiAdaptiveProof.request_width_replay,Adaptive.slotCount,Adaptive.shapeWidths,ApiAdaptive.shape,List.map_map] using hh
end RebuildBound.NativeMatchApiReference
namespace RebuildBound.NativeMatchApiReference
open Model Model.Hierarchy Model.Online Spec Spec.NativeMatchProduction
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

theorem flatMap_slice {A B : Type} (items : List A) (f : A → List B) (j : Nat) (item : A)
    (hi : items[j]? = some item) :
    ((items.flatMap f).drop ((items.take j).map fun x => (f x).length).sum).take (f item).length = f item := by
  induction items generalizing j with
  | nil => simp at hi
  | cons head rest ih =>
    cases j with
    | zero =>
      have he : head = item := by simpa using hi
      subst item
      simp
    | succ j =>
      have hr := ih j (by simpa using hi)
      simpa only [List.take_succ_cons,List.map_cons,List.sum_cons,List.flatMap_cons,List.drop_append,
        List.drop_eq_nil_of_le (Nat.le_add_right _ _),List.nil_append,Nat.add_sub_cancel_left] using hr

theorem frame_request_slice (ctx : Context member initialized h) (tape : IdealKey.Tape)
    (j : Nat) (frame : ApiAdaptive.Frame) (hf : ctx.frames[j]? = some frame) :
    ((requests ctx tape).drop (BatchFreshProof.fs (ctx.run tape) j)).take
      (ApiAdaptive.requests ctx.compiled (rows ctx tape) frame).lanes.length =
        (ApiAdaptive.requests ctx.compiled (rows ctx tape) frame).lanes := by
  have hh := flatMap_slice ctx.frames (fun f => (ApiAdaptive.requests ctx.compiled (rows ctx tape) f).lanes)
    j frame hf
  rw [prefix_slots]
  simpa only [requests,ApiAdaptive.requestGroups,List.flatMap_map,Function.comp_def,
    ApiAdaptiveProof.request_width_replay,Adaptive.slotCount,Adaptive.shapeWidths,ApiAdaptive.shape,List.map_map] using hh

theorem sameKind_length (group : PublicApi.Group Api.Request) (op : OnlineBatch.Op)
    (h : SameKind group op) : op.lanes.length = group.lanes.length := by
  cases group <;> cases op <;> simp_all [SameKind,OnlineBatch.Op.lanes,PublicApi.Group.lanes]
end RebuildBound.NativeMatchApiReference
namespace RebuildBound.NativeMatchQueryTransportProof
open Model Model.Hierarchy Spec NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchHierarchy
open NativeMatchDenseTraceProof NativeMatchHierarchyLayoutProof

lemma empty_page_live (i : Fin 64) : (Page.ofBucket []).live i = false := by
  change (maskOfBits (fun _ : Fin 64 => false)).getLsbD i.val = false
  rw [NativeMatchLanesProof.maskOfBits_get]

lemma empty_page_record (stored : LogicalKey → Stored) (key : LogicalKey) :
    denseRecord stored (Page.ofBucket []) key true = none := by
  have hh : denseHit stored (Page.ofBucket []) key true = false := by
    cases he : denseHit stored (Page.ofBucket []) key true
    · rfl
    · obtain ⟨_, hl, _⟩ := NativeMatchDenseSound (stored ∘ (Page.ofBucket []).keys)
        (Page.ofBucket []).live (stored key) true he
      simp only [empty_page_live, Bool.false_eq_true] at hl
  simp [denseRecord, hh]

lemma empty_page_events (key : LogicalKey) : denseEvents (Page.ofBucket []) key true = [] := by
  have hi : exactIndex (Page.ofBucket []) key = none := by
    simp [exactIndex, empty_page_live]
  simp [denseEvents, hi]

lemma empty_page_normalize (stored : LogicalKey → Stored) (key : LogicalKey) :
    ¬ denseNormalizeBad stored (Page.ofBucket []) key := by
  rintro ⟨i, hi, _, _⟩
  simp only [empty_page_live, Bool.false_eq_true] at hi

lemma bucketPages_add (n m : Nat) (b : Bucket) :
    bucketPages (n + m) b = bucketPages n b ++ bucketPages m (b.drop (64*n)) := by
  induction n generalizing b with
  | zero => simp [bucketPages]
  | succ n ih =>
    simp only [Nat.succ_add, bucketPages, List.cons_append, ih]
    simp only [List.drop_drop, Nat.mul_succ, Nat.add_comm (64*n) 64]

lemma bucketPages_empty (n : Nat) : bucketPages n [] = List.replicate n (Page.ofBucket []) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bucketPages, List.replicate_succ, ih]

lemma allBucketPages_extend (b : Bucket) (n : Nat) (hn : b.length ≤ 64*n) :
    bucketPages n b = allBucketPages b ++ List.replicate (n - (b.length+63)/64) (Page.ofBucket []) := by
  have hc : (b.length+63)/64 ≤ n := by omega
  have hn' : n = (b.length+63)/64 + (n - (b.length+63)/64) := by omega
  conv_lhs => rw [hn']
  rw [bucketPages_add, List.drop_eq_nil_iff.mpr (by omega), bucketPages_empty]
  rfl

lemma denseScan_append_empty (stored : LogicalKey → Stored) (pages : List Page) (key : LogicalKey) (n : Nat) :
    denseScan stored (pages ++ List.replicate n (Page.ofBucket [])) key = denseScan stored pages key := by
  unfold denseScan
  rw [List.foldl_append]
  generalize pages.foldl _ none = found
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, empty_page_record] using ih

lemma denseEvents_append_empty (pages : List Page) (key : LogicalKey) (n : Nat) :
    denseScanEvents (pages ++ List.replicate n (Page.ofBucket [])) key = denseScanEvents pages key := by
  simp [denseScanEvents, empty_page_events]

lemma denseNormalize_append_empty (stored : LogicalKey → Stored) (pages : List Page) (key : LogicalKey) (n : Nat) :
    denseScanNormalizeBad stored (pages ++ List.replicate n (Page.ofBucket [])) key ↔
      denseScanNormalizeBad stored pages key := by
  constructor
  · rintro ⟨p, hp, hb⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact ⟨p, hp, hb⟩
    · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hp
      exact (empty_page_normalize stored key hb).elim
  · rintro ⟨p, hp, hb⟩
    exact ⟨p, List.mem_append_left _ hp, hb⟩

lemma denseScan_laneEq (stored : LogicalKey → Stored) (key : LogicalKey) {a b : Bucket} (h : LaneEq a b) :
    denseScan stored (allBucketPages a) key = denseScan stored (allBucketPages b) key := by
  let n := max ((a.length+63)/64) ((b.length+63)/64)
  have ha : a.length ≤ 64*n := by dsimp [n]; omega
  have hb : b.length ≤ 64*n := by dsimp [n]; omega
  have he := congrArg (fun pages => denseScan stored pages key) (bucketPages_equal h n)
  rw [allBucketPages_extend a n ha, allBucketPages_extend b n hb,
    denseScan_append_empty, denseScan_append_empty] at he
  exact he

lemma denseEvents_laneEq (key : LogicalKey) {a b : Bucket} (h : LaneEq a b) :
    denseScanEvents (allBucketPages a) key = denseScanEvents (allBucketPages b) key := by
  let n := max ((a.length+63)/64) ((b.length+63)/64)
  have ha : a.length ≤ 64*n := by dsimp [n]; omega
  have hb : b.length ≤ 64*n := by dsimp [n]; omega
  have he := congrArg (fun pages => denseScanEvents pages key) (bucketPages_equal h n)
  rw [allBucketPages_extend a n ha, allBucketPages_extend b n hb,
    denseEvents_append_empty, denseEvents_append_empty] at he
  exact he

lemma denseNormalize_laneEq (stored : LogicalKey → Stored) (key : LogicalKey) {a b : Bucket} (h : LaneEq a b) :
    denseScanNormalizeBad stored (allBucketPages a) key ↔
      denseScanNormalizeBad stored (allBucketPages b) key := by
  let n := max ((a.length+63)/64) ((b.length+63)/64)
  have ha : a.length ≤ 64*n := by dsimp [n]; omega
  have hb : b.length ≤ 64*n := by dsimp [n]; omega
  have he := congrArg (fun pages => denseScanNormalizeBad stored pages key) (bucketPages_equal h n)
  rw [allBucketPages_extend a n ha, allBucketPages_extend b n hb] at he
  apply Iff.of_eq
  simpa only [denseNormalize_append_empty] using he

lemma output_records {a b : Output} (h : OutputEq a b) : a.records = b.records := by
  simp only [Output.records, h.1, recs_equal h.2]

lemma nativeScan_outputEq (stored : LogicalKey → Stored) (key : LogicalKey) (address : Nat)
    {a b : Output} (h : OutputEq a b) : nativeScan stored key a address = nativeScan stored key b address := by
  simp only [nativeScan, h.1, denseScan_laneEq stored key h.2]

lemma exactScan_outputEq (key : LogicalKey) (address : Nat) {a b : Output} (h : OutputEq a b) :
    Probe.scan key a address = Probe.scan key b address := by
  simp only [Probe.scan, h.1, recs_equal h.2]

lemma scanNormalize_outputEq (stored : LogicalKey → Stored) (key : LogicalKey)
    {a b : Output} (h : OutputEq a b) : scanNormalizeBad stored a key ↔ scanNormalizeBad stored b key := by
  simp only [scanNormalizeBad, denseNormalize_laneEq stored key h.2, output_records h]

lemma nativeCascade_outputEq (stored : LogicalKey → Stored) (key : LogicalKey)
    (native exact : Nat × Nat → Output) (real : Nat × Nat → Nat)
    (dummy : Nat → Nat × Nat → Nat) (cs : List (Nat × Nat))
    (h : ∀ c ∈ cs, OutputEq (native c) (exact c)) (initial : Option Rec) (offset : Nat) :
    nativeCascade stored key native real dummy cs initial offset =
      nativeCascade stored key exact real dummy cs initial offset := by
  induction cs generalizing initial offset with
  | nil => rfl
  | cons c cs ih =>
    have hs := nativeScan_outputEq stored key (if initial.isSome then dummy offset c else real c) (h c (by simp))
    simp only [nativeCascade, Probe.cascadeWith, hs]
    exact congrArg (fun r : Probe.Result => (⟨r.found,
      (if initial.isSome then dummy offset c else real c) :: r.addresses⟩ : Probe.Result))
      (ih (fun c hc => h c (by simp [hc])) _ _)

end RebuildBound.NativeMatchQueryTransportProof
namespace RebuildBound.NativeMatchDispatchProof
open Model Spec NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchDispatch
open NativeMatchDenseTraceProof OnlineCorrectnessProof

lemma storedFirst_agreement (stored : LogicalKey → Stored) (key : LogicalKey) (records : List Rec)
    (hu : (records.map Rec.key).Nodup) (hn : ¬listNormalizeBad stored records key) :
    storedFirst stored key records = DirectPrefix.latest key records := by
  unfold storedFirst
  cases hf : records.find? (fun r => stored r.key == stored key) with
  | none =>
    symm
    apply (latest_none_iff key records).mpr
    intro hk
    obtain ⟨r, hr, hrk⟩ := List.mem_map.mp hk
    have hf' := (List.find?_eq_none.mp hf) r hr
    simp [hrk] at hf'
  | some r =>
    symm
    apply latest_of_unique_mem hu (List.mem_of_find?_eq_some hf)
    have he : stored r.key = stored key := by simpa using List.find?_some hf
    by_contra hne
    exact hn ⟨r, List.mem_of_find?_eq_some hf, hne, he⟩

lemma storedFirst_eq_storedLatest (stored : LogicalKey → Stored) (key : LogicalKey) (records : List Rec)
    (hu : (records.map Rec.key).Nodup) (hn : ¬listNormalizeBad stored records key) :
    storedFirst stored key records = storedLatest stored key records :=
  (storedFirst_agreement stored key records hu hn).trans (storedLatest_agreement stored key records hn).symm

end RebuildBound.NativeMatchDispatchProof
namespace RebuildBound.NativeMatchDispatchFirstTests
open Model Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchDispatch
private def firstRecord : Rec := ⟨[1],17,false⟩
private def lastRecord : Rec := ⟨[2],23,true⟩
private def collide (_ : LogicalKey) : Stored := 0

-- A collision witnesses why physical fallback and chronological forwarding
-- must remain separate even though the no-collision theorem identifies them.
example : storedFirst collide [1] [firstRecord,lastRecord] = some firstRecord := by decide +kernel
example : storedLatest collide [1] [firstRecord,lastRecord] = some lastRecord := by decide +kernel
example : storedFirst collide [1] (Bucket.recs [none,some firstRecord,none,some lastRecord]) =
    some firstRecord := by decide +kernel
example : (([firstRecord,lastRecord] : List Rec).map Rec.key).Nodup := by decide +kernel
example : listNormalizeBad collide [firstRecord,lastRecord] [1] := by
  exact ⟨lastRecord,by simp,by decide,by decide⟩
end RebuildBound.NativeMatchDispatchFirstTests
namespace RebuildBound.NativeMatchDispatchProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchDispatch
open NativeMatchDenseTraceProof

lemma stored_any_agreement (stored : LogicalKey → Stored) (unit : Model.Bucket)
    (keys : List LogicalKey) (record : Rec) (hr : record ∈ unit.recs)
    (hn : ∀ key ∈ keys, ¬ listNormalizeBad stored unit.recs key) :
    (keys.any fun key => stored record.key == stored key) = (keys.any fun key => record.key == key) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨key, hk, he⟩
    refine ⟨key, hk, ?_⟩
    by_contra hne
    exact hn key hk ⟨record, hr, hne, he⟩
  · rintro ⟨key, hk, he⟩
    exact ⟨key, hk, by rw [he]⟩

lemma stored_clear_agreement (stored : LogicalKey → Stored) (unit : Model.Bucket)
    (keys : List LogicalKey) (hn : ∀ key ∈ keys, ¬ listNormalizeBad stored unit.recs key) :
    storedClear stored unit keys = keys.foldl (fun unit key => Requester.clearKey key unit) unit := by
  rw [clearKeys_fold]
  apply List.map_congr_left
  intro lane hl
  cases lane with
  | none => rfl
  | some record =>
    have hr : record ∈ unit.recs := List.mem_filterMap.mpr ⟨some record, hl, rfl⟩
    simp only [Option.filter]
    simp only [stored_any_agreement stored unit keys record hr hn]


lemma exact_page_mask (stored : LogicalKey → Stored) (page : Page) (key : LogicalKey)
    (hn : ¬ denseNormalizeBad stored page key) (slot : Fin 64) :
    (exactPageMask stored page key).getLsbD slot.val = true ↔
      page.live slot = true ∧ page.keys slot = key := by
  rw [exactPageMask, NativeMatchLanesProof.maskOfBits_get]
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hl, he⟩
    refine ⟨hl, ?_⟩
    by_contra hne
    exact hn ⟨slot, hl, hne, he⟩
  · rintro ⟨hl, he⟩
    exact ⟨hl, by rw [he]⟩

/-- Dispatch agreement is proved for either selector result. The comparison
inventory remains the reference potential-event inventory, so the actual
public work threshold may remove events without adding any charge. -/
lemma page_dispatch_agreement (cross : Bool) (stored : LogicalKey → Stored) (page : Page) (key : LogicalKey)
    (hu : (page.bucket.recs.map Rec.key).Nodup) (hn : ¬ denseNormalizeBad stored page key)
    (hoff : cross = true → ∀ e ∈ denseEvents page key true, ¬ e.bad stored) (slot : Fin 64) :
    (pageMask cross stored page key).getLsbD slot.val = true ↔
      page.live slot = true ∧ page.keys slot = key := by
  cases cross with
  | false => exact exact_page_mask stored page key hn slot
  | true => exact denseMask_exact stored page key hu hn (hoff rfl) slot

lemma page_record_dispatch_agreement (cross : Bool) (stored : LogicalKey → Stored)
    (page : Page) (key : LogicalKey) (hu : (page.bucket.recs.map Rec.key).Nodup)
    (hn : ¬ denseNormalizeBad stored page key)
    (hoff : cross = true → ∀ e ∈ denseEvents page key true, ¬ e.bad stored) :
    pageRecord cross stored page key = DirectPrefix.latest key page.bucket.recs := by
  cases cross with
  | true => exact record_agreement stored page key hu hn (hoff rfl)
  | false =>
    apply storedFirst_agreement stored key page.bucket.recs hu
    rintro ⟨r, hr, hne, he⟩
    rw [page_records] at hr
    simp only [realKeys, List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hr
    obtain ⟨i, hi, rfl⟩ := hr
    exact hn ⟨i, hi, hne, he⟩

lemma scalar_clear_agreement (stored : LogicalKey → Stored) (entries : Nat)
    (st : Requester.State) (record : Rec) (real : Bool)
    (hn : ¬ listNormalizeBad stored st.current.recs record.key) :
    scalarRequesterStep stored entries st record real = Requester.step entries st (.access record real) := by
  have h := stored_clear_agreement stored st.current [record.key]
    (fun key hk => by simpa only [List.mem_singleton.mp hk] using hn)
  simpa [scalarRequesterStep, Requester.step] using congrArg
    (fun unit => Requester.insert entries ⟨st.frozen, unit⟩ (if real then some record else none)) h

end RebuildBound.NativeMatchDispatchProof
namespace RebuildBound.NativeMatchDispatchProof
open Model Spec NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchDispatch
open NativeMatchDenseTraceProof

lemma pageMask_agrees_dense (cross : Bool) (stored : LogicalKey → Stored) (p : Page) (key : LogicalKey)
    (hu : (p.bucket.recs.map Rec.key).Nodup) (hn : ¬ denseNormalizeBad stored p key)
    (hoff : ∀ e ∈ denseEvents p key true, ¬ e.bad stored) :
    pageMask cross stored p key = denseMask stored p key true := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  apply Bool.eq_iff_iff.mpr
  exact (page_dispatch_agreement cross stored p key hu hn (fun _ => hoff) ⟨i, hi⟩).trans
    (denseMask_exact stored p key hu hn hoff ⟨i, hi⟩).symm

lemma pageRecord_agrees_dense (cross : Bool) (stored : LogicalKey → Stored) (p : Page) (key : LogicalKey)
    (hu : (p.bucket.recs.map Rec.key).Nodup) (hn : ¬ denseNormalizeBad stored p key)
    (hoff : ∀ e ∈ denseEvents p key true, ¬ e.bad stored) :
    pageRecord cross stored p key = denseRecord stored p key true :=
  (page_record_dispatch_agreement cross stored p key hu hn (fun _ => hoff)).trans
    (record_agreement stored p key hu hn hoff).symm

lemma scanPages_agrees_dense (mode : Nat → Mode) (stored : LogicalKey → Stored)
    (pages : List Page) (key : LogicalKey)
    (hu : ∀ p ∈ pages, (p.bucket.recs.map Rec.key).Nodup)
    (hn : ¬ denseScanNormalizeBad stored pages key)
    (hoff : ∀ e ∈ denseScanEvents pages key, ¬ e.bad stored) :
    scanPages mode stored pages key = denseScan stored pages key := by
  unfold scanPages
  rw [foldl_congr_mem pages.zipIdx _
    (fun found pi => (denseRecord stored pi.1 key true).orElse (fun _ => found)) none (by
      intro found pi hpi
      have hp : pi.1 ∈ pages := by
        have hm : pi.1 ∈ pages.zipIdx.map Prod.fst := List.mem_map.mpr ⟨pi, hpi, rfl⟩
        simpa only [List.zipIdx_map_fst] using hm
      rw [pageRecord_agrees_dense _ stored pi.1 key (hu pi.1 hp)
        (fun h => hn ⟨pi.1, hp, h⟩) (fun e he => hoff e (List.mem_flatMap.mpr ⟨pi.1, hp, he⟩))])]
  change pages.zipIdx.foldl (fun found pi => (denseRecord stored pi.1 key true).orElse (fun _ => found)) none = _
  simpa only [List.foldl_map, denseScan] using
    congrArg (fun ps : List Page => ps.foldl (fun found p => (denseRecord stored p key true).orElse (fun _ => found)) none)
      (List.zipIdx_map_fst 0 pages)

lemma deferredClear_agrees_dense (cross : Bool) (stored : LogicalKey → Stored)
    (p : Page) (keys : List LogicalKey) (hu : (p.bucket.recs.map Rec.key).Nodup)
    (hn : ∀ key ∈ keys, ¬ denseNormalizeBad stored p key)
    (hoff : ∀ e ∈ denseBatchEvents p keys, ¬ e.bad stored) :
    deferredClear cross stored p keys = denseDeferredClear stored p keys := by
  unfold deferredClear denseDeferredClear
  congr 2
  unfold deferredMask denseDeferredMask
  congr 1
  apply foldl_congr_mem
  intro state key hk
  rw [pageMask_agrees_dense cross stored p key hu (hn key hk)
    (fun e he => hoff e (List.mem_flatMap.mpr ⟨key, hk, he⟩))]

lemma clearUnit_agrees_dense (mode : Nat → Mode) (stored : LogicalKey → Stored)
    (unit : Model.Bucket) (keys : List LogicalKey) (hu : (unit.recs.map Rec.key).Nodup)
    (hn : ¬ unitNormalizeBad stored unit keys)
    (hoff : ∀ e ∈ unitBatchEvents unit keys, ¬ e.bad stored) :
    clearUnit mode stored unit keys = denseClearUnit stored unit keys := by
  unfold clearUnit denseClearUnit
  congr 2
  have he : (allBucketPages unit).zipIdx.map (fun pi => deferredClear (mode pi.2).cross stored pi.1 keys) =
      (allBucketPages unit).zipIdx.map (fun pi => denseDeferredClear stored pi.1 keys) := by
    apply List.map_congr_left
    intro pi hpi
    have hp : pi.1 ∈ allBucketPages unit := by
      have hm : pi.1 ∈ (allBucketPages unit).zipIdx.map Prod.fst := List.mem_map.mpr ⟨pi, hpi, rfl⟩
      simpa only [List.zipIdx_map_fst] using hm
    exact deferredClear_agrees_dense _ stored pi.1 keys (bucketPages_unique _ unit hu _ hp)
      (fun key hk h => hn ⟨pi.1, hp, key, hk, h⟩)
      (fun e he => hoff e (List.mem_flatMap.mpr ⟨pi.1, hp, he⟩))
  rw [he]
  simpa only [List.map_map, Function.comp_def] using
    congrArg (fun ps : List Page => ps.map (fun p => denseDeferredClear stored p keys))
      (List.zipIdx_map_fst 0 (allBucketPages unit))

lemma requesterStep_agreement (mode : Nat → Mode) (stored : LogicalKey → Stored)
    (entries : Nat) (st : Requester.State) (op : Requester.Op) (hu : Requester.Unique st)
    (hn : ¬ requesterNormalizeBad stored st op)
    (hoff : (∃ lanes, op = .batch lanes) → ∀ e ∈ requesterEvents st op, ¬ e.bad stored) :
    requesterStep mode stored entries st op = Requester.step entries st op := by
  cases op with
  | access record real =>
    apply scalar_clear_agreement
    intro hb
    exact hn (Or.inl (unit_normalization_bad_of_list stored st.current [record.key] record.key (by simp) hb))
  | batch lanes =>
    have he := clearUnit_agrees_dense mode stored st.current (lanes.map Rec.key) hu.2
      (fun h => hn (Or.inl h)) (hoff ⟨lanes, rfl⟩)
    rw [requesterStep, he]
    exact requester_step_agreement stored entries st (.batch lanes) hu hn (hoff ⟨lanes, rfl⟩)

end RebuildBound.NativeMatchDispatchProof
namespace RebuildBound.NativeMatchApiProof
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch
open Spec NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchHierarchy NativeMatchDispatch NativeMatchApi
open NativeMatchDenseTraceProof NativeMatchDispatchProof NativeMatchQueryTransportProof
open OnlineCorrectnessProof

lemma scanPages_exact (mode : Nat → Mode) (stored : LogicalKey → Stored) (pages : List Page) (key : LogicalKey)
    (hu : ∀ p ∈ pages, (p.bucket.recs.map Rec.key).Nodup)
    (hn : ¬ denseScanNormalizeBad stored pages key)
    (hoff : ∀ e ∈ denseScanEvents pages key, ¬ e.bad stored) :
    scanPages mode stored pages key = DirectPrefix.latest key (pageRecords pages) := by
  rw [scanPages_agrees_dense mode stored pages key hu hn hoff]
  exact denseScan_agreement stored pages key hu hn hoff

lemma latest_fold {A : Type} (xs : List A) (records : A → List Rec) (key : LogicalKey) (pre : List Rec) :
    xs.foldl (fun found x => (DirectPrefix.latest key (records x)).orElse (fun _ => found))
      (DirectPrefix.latest key pre) = DirectPrefix.latest key (pre ++ xs.flatMap records) := by
  induction xs generalizing pre with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ← latest_append, ih]
    simp only [List.flatMap_cons, List.append_assoc]

lemma scanRequester_agreement (policy : Policy) (operation : Nat) (stored : LogicalKey → Stored)
    (st : Requester.State) (consumed : Nat) (key : LogicalKey) (hu : Requester.Unique st)
    (hn : ¬ denseScanNormalizeBad stored (requesterPages st consumed) key)
    (hoff : ∀ e ∈ denseScanEvents (requesterPages st consumed) key, ¬ e.bad stored) :
    scanRequester policy operation stored st consumed key =
      DirectPrefix.latest key ((st.frozen.drop consumed).flatMap Bucket.recs ++ st.current.recs) := by
  have hs (b : Model.Bucket) (hb : b ∈ st.frozen.drop consumed ∨ b = st.current) (mode : Nat → Mode) :
      scanPages mode stored (allBucketPages b) key = DirectPrefix.latest key b.recs := by
    have hp : ∀ p ∈ allBucketPages b, p ∈ requesterPages st consumed := by
      intro p hp
      rcases hb with hb | rfl
      · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨b,hb,hp⟩)
      · exact List.mem_append_right _ hp
    rw [scanPages_exact mode stored _ key
      (fun p h => requesterPages_unique st consumed hu p (hp p h))
      (fun ⟨p,hp',h⟩ => hn ⟨p,hp p hp',h⟩)
      (fun e he => by
        obtain ⟨p,hp',he⟩ := List.mem_flatMap.mp he
        exact hoff e (List.mem_flatMap.mpr ⟨p,hp p hp',he⟩)), allBucketPages_records]
  unfold scanRequester
  rw [hs st.current (Or.inr rfl)]
  have hf := foldl_congr_mem ((st.frozen.drop consumed).zipIdx consumed)
    (fun found ui => (scanPages (policy operation (.unit ui.2)) stored (allBucketPages ui.1) key).orElse (fun _ => found))
    (fun found ui => (DirectPrefix.latest key ui.1.recs).orElse (fun _ => found)) none (by
      intro found ui hui
      have hb : ui.1 ∈ st.frozen.drop consumed := by
        have hmem : ui.1 ∈ ((st.frozen.drop consumed).zipIdx consumed).map Prod.fst := List.mem_map.mpr ⟨ui,hui,rfl⟩
        simpa only [List.zipIdx_map_fst] using (show ui.1 ∈ ((st.frozen.drop consumed).zipIdx consumed).map Prod.fst from hmem)
      rw [hs ui.1 (Or.inl hb)])
  rw [hf]
  have hl := latest_fold ((st.frozen.drop consumed).zipIdx consumed) (fun ui => ui.1.recs) key []
  change _ = DirectPrefix.latest key ([] ++ _) at hl
  simp only [List.nil_append, show DirectPrefix.latest key [] = none from rfl] at hl
  rw [hl]
  have he : ((st.frozen.drop consumed).zipIdx consumed).flatMap (fun ui => ui.1.recs) =
      (st.frozen.drop consumed).flatMap Bucket.recs := by
    simpa only [List.flatMap_map, Function.comp_def] using
      congrArg (fun bs : List Model.Bucket => bs.flatMap Bucket.recs)
        (List.zipIdx_map_fst consumed (st.frozen.drop consumed))
  rw [he, ← latest_append]

lemma requireTables_ok (lookup : Nat × Nat → Option Output) (cs : List (Nat × Nat))
    (h : ∀ c ∈ cs, (lookup c).isSome = true) : requireTables lookup cs = .ok () := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc := h c (by simp)
    cases he : lookup c with
    | none => simp [he] at hc
    | some out => simpa [requireTables,he] using ih (fun c hc => h c (by simp [hc]))

lemma scanOutput_agreement (policy : Policy) (operation : Nat) (stored : LogicalKey → Stored)
    (coordinate : Nat × Nat) (native exact : Output) (key : LogicalKey) (address : Nat)
    (he : OutputEq native exact) (hu : (exact.records.map Rec.key).Nodup)
    (hn : ¬ scanNormalizeBad stored exact key)
    (hoff : ∀ e ∈ denseScanEvents (allBucketPages exact.tier) key, ¬ e.bad stored) :
    scanOutput policy operation stored coordinate native key address = Probe.scan key exact address := by
  have hu' : (native.records.map Rec.key).Nodup := by rwa [output_records he]
  have ht : ((Bucket.recs native.tier).map Rec.key).Nodup := by
    unfold Output.records at hu'
    rw [List.map_append, List.nodup_append] at hu'
    exact hu'.2.1
  have hn' : ¬ scanNormalizeBad stored native key := fun hb => hn ((scanNormalize_outputEq stored key he).mp hb)
  have hoff' : ∀ e ∈ denseScanEvents (allBucketPages native.tier) key, ¬ e.bad stored := by
    rw [denseEvents_laneEq key he.2]
    exact hoff
  have hs := scanPages_agrees_dense (policy operation (.tier coordinate)) stored (allBucketPages native.tier) key
    (bucketPages_unique _ _ ht) (fun h => hn' (Or.inl h)) hoff'
  change (storedFirst stored key (native.main.getD address []).recs).orElse _ = _
  have hmain : (((native.main.getD address []).recs).map Rec.key).Nodup :=
    hu'.sublist (((List.sublist_append_left _ _).trans (scan_records_sublist native address)).map Rec.key)
  have hnorm : ¬listNormalizeBad stored (native.main.getD address []).recs key := by
    rintro ⟨r,hr,hne,heq⟩
    exact hn' (Or.inr ⟨r,(scan_records_sublist native address).subset (List.mem_append_left _ hr),hne,heq⟩)
  rw [storedFirst_eq_storedLatest stored key _ hmain hnorm,hs]
  change nativeScan stored key native address = _
  rw [nativeScan_outputEq stored key address he]
  exact nativeScan_agreement stored key exact address hu hn hoff

lemma cascadeWith_congr (scan scan' : Nat × Nat → Nat → Option Rec)
    (real : Nat × Nat → Nat) (dummy : Nat → Nat × Nat → Nat) (cs : List (Nat × Nat))
    (h : ∀ c ∈ cs, ∀ a, scan c a = scan' c a) (initial : Option Rec) (offset : Nat) :
    Probe.cascadeWith scan real dummy cs initial offset = Probe.cascadeWith scan' real dummy cs initial offset := by
  induction cs generalizing initial offset with
  | nil => rfl
  | cons c cs ih =>
    simp only [Probe.cascadeWith, h c (by simp)]
    rw [ih (fun c hc => h c (by simp [hc]))]

end RebuildBound.NativeMatchApiProof
namespace RebuildBound.NativeMatchApiProof
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch
open Spec NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchHierarchy NativeMatchDispatch NativeMatchApi
open NativeMatchDenseTraceProof NativeMatchDispatchProof NativeMatchQueryTransportProof OnlineCorrectnessProof

lemma query_reference (policy : Policy) (stored : LogicalKey → Stored) (cfg : Config) (sh : Shapes)
    (g : OnlineGeom) (schedule : Schedule) (init : List Rec) (unsh : Rec → Bool)
    (words : Words) (dummy : Nat → Nat → Nat) (operation start lane : Nat)
    (st : Requester.State) (earlier : List Rec) (key : LogicalKey) (tableAt : Nat × Nat → Output)
    (ht : ∀ c ∈ (schedule start).tables, ∃ out,
      nativeTable stored cfg sh (traceFromState g init unsh st) words c.1 c.2 = some out ∧ OutputEq out (tableAt c))
    (hu : Requester.Unique st)
    (hut : ∀ c ∈ (schedule start).tables, ((tableAt c).records.map Rec.key).Nodup)
    (hnf : ¬ listNormalizeBad stored earlier key)
    (hnr : ¬ denseScanNormalizeBad stored
      (requesterPages st (((schedule start).consumed-cfg.seed 1)*g.unitsPerPrefix)) key)
    (hnt : ¬ cascadeNormalizeBad stored key tableAt (schedule start).tables)
    (hoffr : ∀ e ∈ denseScanEvents
      (requesterPages st (((schedule start).consumed-cfg.seed 1)*g.unitsPerPrefix)) key, ¬ e.bad stored)
    (hofft : ∀ e ∈ cascadeEvents key tableAt (schedule start).tables, ¬ e.bad stored) :
    query policy stored cfg sh g schedule init unsh words dummy operation start lane st earlier key =
      .ok (Probe.cascade key tableAt
        (fun c => bucket cfg c.1 c.2 (jobWord cfg words c.1 c.2 key))
        (fun i c => bucket cfg c.1 c.2 (dummy (start+lane) i)) (schedule start).tables
        ((DirectPrefix.latest key earlier).orElse fun _ => DirectPrefix.latest key
          ((st.frozen.drop (((schedule start).consumed-cfg.seed 1)*g.unitsPerPrefix)).flatMap Bucket.recs ++
            st.current.recs)) 0) := by
  let lookup := fun c : Nat × Nat => nativeTable stored cfg sh (traceFromState g init unsh st) words c.1 c.2
  have hr : requireTables lookup (schedule start).tables = .ok () := by
    apply requireTables_ok
    intro c hc
    obtain ⟨out,ho,_⟩ := ht c hc
    simp only [lookup,ho,Option.isSome_some]
  unfold query
  change (do requireTables lookup (schedule start).tables; pure _) = _
  rw [hr]
  change Except.ok (Probe.cascadeWith _ _ _ _ _ _) = _
  rw [storedLatest_agreement stored key earlier hnf,
    scanRequester_agreement policy operation stored st _ key hu hnr hoffr]
  congr 1
  apply cascadeWith_congr
  intro c hc address
  obtain ⟨out,ho,he⟩ := ht c hc
  change scanOutput policy operation stored c ((lookup c).getD emptyOutput) key address = _
  change lookup c = some out at ho
  rw [ho]
  exact scanOutput_agreement policy operation stored c out (tableAt c) key address he (hut c hc)
    (fun hb => hnt ⟨c,hc,hb⟩)
    (fun e he => hofft e (List.mem_flatMap.mpr ⟨c,hc,he⟩))

end RebuildBound.NativeMatchApiProof
namespace RebuildBound.NativeMatchApiProof
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch
open Spec NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchHierarchy NativeMatchDispatch NativeMatchApi
open NativeMatchDenseTraceProof NativeMatchDispatchProof NativeMatchQueryTransportProof OnlineCorrectnessProof BatchFreshProof

lemma query_batch_of_tables (policy : Policy) (stored : LogicalKey → Stored)
    (geo : HierarchyGeometry) (hgeo : geo.Structural) (g : OnlineGeom) (run : BatchRun)
    (hT : TraceStructural geo.cfg (traceOf g run)) (hInit : run.init.length ≤ geo.init.C/2*geo.init.T)
    (hUnsh : UnshPromise geo.cfg geo.shapes (traceOf g run)) (S : Schedule)
    (words : Words) (dummy : Nat → Nat → Nat) (t : Nat) (s : OnlineBatch.Slot)
    (hs : (slots run)[t]? = some s) (hp : s.probes = true)
    (hc : ∀ c ∈ (slotSchedule (widths run) S t).tables,
      1 ≤ c.1 ∧ c.1 ≤ geo.cfg.levels ∧ c.2 ≤ geo.cfg.seed c.1+geo.cfg.ordinals c.1)
    (ht : ∀ c ∈ (S (fs run s.op)).tables, ∃ out,
      nativeTable stored geo.cfg geo.shapes
        (traceFromState g run.init run.unsh (stateAt g run s.op)) words c.1 c.2 = some out ∧
      OutputEq out (table geo.cfg geo.shapes (traceOf g run) words c.1 c.2))
    (hn : ¬ batchNormalizeBad stored geo.cfg geo.shapes g run S words t)
    (hoff : ∀ e ∈ batchEvents geo.cfg geo.shapes g run S words t, ¬ e.bad stored) :
    query policy stored geo.cfg geo.shapes g S run.init run.unsh words dummy s.op (fs run s.op) s.lane
      (stateAt g run s.op) (Probe.earlier run s) s.record.key =
        .ok (Probe.batch geo.cfg geo.shapes g run S words dummy t) := by
  have hplan : slotSchedule (widths run) S t = S (fs run s.op) := by
    simp only [slotSchedule,chunkStart_slot run hs]
  obtain ⟨_,_,_,hindex⟩ := slot_inv run hs
  have hn' : ¬ listNormalizeBad stored (Probe.earlier run s) s.record.key ∧
      ¬ denseScanNormalizeBad stored (requesterPages (stateAt g run s.op)
        (((S (fs run s.op)).consumed-geo.cfg.seed 1)*g.unitsPerPrefix)) s.record.key ∧
      ¬ cascadeNormalizeBad stored s.record.key
        (fun c => table geo.cfg geo.shapes (traceOf g run) words c.1 c.2) (S (fs run s.op)).tables := by
    simpa only [batchNormalizeBad,hs,hp,true_and,not_or,batchPages,hs,hplan] using hn
  have hoff' := hoff
  simp only [batchEvents,hs,hp,↓reduceIte,batchPages,hs,hplan,List.mem_append,or_imp,forall_and] at hoff'
  have hh := query_reference policy stored geo.cfg geo.shapes g S run.init run.unsh words dummy
    s.op (fs run s.op) s.lane (stateAt g run s.op) (Probe.earlier run s) s.record.key
    (fun c => table geo.cfg geo.shapes (traceOf g run) words c.1 c.2) ht (requester_unique g run s.op)
    (fun c hcm => by
      obtain ⟨h1,hL,hv⟩ := hc c (by simpa only [hplan] using hcm)
      exact table_unique geo hgeo (traceOf g run) hT hInit hUnsh words c.1 c.2 h1 hL hv)
    hn'.1 hn'.2.1 hn'.2.2 hoff'.1 hoff'.2
  rw [← hindex] at hh
  simpa only [Probe.batch,hs,hp,↓reduceIte,Probe.hierarchy,OnlineBatch.denseRecords,hs,hplan] using hh

lemma traceFromState_prefix (g : OnlineGeom) (run : BatchRun) (j : Nat) :
    traceFromState g run.init run.unsh (stateAt g run j) =
      traceOf g (AdaptiveRowCausalityProof.prefixRun run j) := by
  unfold traceFromState OnlineBatch.traceOf OnlineBatch.stateAt AdaptiveRowCausalityProof.prefixRun
  simp only [List.take_length]

/-- Planned native producers depend only on the frozen prefix available at
this operation, including after a bad match. No execution agreement is assumed. -/
lemma nativeTable_at_state (geo : HierarchyGeometry) (hgeo : geo.LowerCompatible)
    (g : OnlineGeom) (hg : g.unitEntries*g.unitsPerPrefix=geo.cfg.carryPositions 1)
    (hE : 0<g.unitEntries) (run : BatchRun) (S : Schedule) (n m : Nat)
    (hS : SchedulePremises geo.cfg S n m) (stored : LogicalKey → Stored) (words : Words)
    (j : Nat) (hjn : fs run j<n) (c : Nat × Nat) (hc : c∈(S (fs run j)).tables)
    (h1 : 1≤c.1) (hL : c.1≤geo.cfg.levels) :
    nativeTable stored geo.cfg geo.shapes
      (traceFromState g run.init run.unsh (stateAt g run j)) words c.1 c.2 =
    nativeTable stored geo.cfg geo.shapes (traceOf g run) words c.1 c.2 := by
  rw [traceFromState_prefix]
  apply NativeMatchHierarchyTracePrefix.table_trace_congr (HierarchySemanticsProof.lower hgeo)
    stored (OnlineBatch.traceOf g (AdaptiveRowCausalityProof.prefixRun run j))
    (OnlineBatch.traceOf g run) rfl rfl words c.1 h1 hL c.2
  intro i hi
  have hitime : geo.cfg.seed 1+i+1≤time geo.cfg c.1 c.2 := by
    unfold unitEnd at hi
    omega
  apply TraceUnitsPrefix geo.cfg g run j i hg hE
  have hwe := (OnlineFreshProof.tiles_bounds (hS.tile _ hjn) c hc).2.2
  change (window geo.cfg c.1 c.2).2 ≤ _ at hwe
  rw [OnlineFreshProof.window_snd,←time_cp] at hwe
  have hcons := (hS.consumed _ hjn).2
  unfold pos at hcons
  have hmul : (i+1)*geo.cfg.carryPositions 1 + geo.cfg.seed 1*geo.cfg.carryPositions 1 ≤
      time geo.cfg c.1 c.2*geo.cfg.carryPositions 1 := by
    rw [←Nat.add_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  show (i+1)*geo.cfg.carryPositions 1≤fs run j
  omega

end RebuildBound.NativeMatchApiProof
namespace RebuildBound.NativeMatchApiProof
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch
open Spec NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchHierarchy NativeMatchDispatch NativeMatchApi

lemma chunk_by_lanes (policy : Policy) (stored : LogicalKey → Stored) (codec : Api.Codec)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (init : List Rec)
    (words : Words) (dummy : Nat → Nat → Nat) (operation start : Nat) (st : Requester.State)
    (earlier records : List Rec) (requests : List Api.Request) (results : List Probe.Result)
    (hr : records.length=requests.length) (hs : results.length=requests.length)
    (h : ∀ i q r result, requests[i]?=some q → records[i]?=some r → results[i]?=some result →
      r=Api.postRecord codec q result.found ∧
      query policy stored cfg sh g S init (fun r => codec.flag r.val) words dummy operation start
        (earlier.length+i) st (earlier++records.take i) q.key = .ok result) :
    chunk policy stored codec cfg sh g S init words dummy operation start st earlier requests =
      .ok (records,results) := by
  induction requests generalizing records results earlier with
  | nil =>
    have hrecords : records=[] := List.length_eq_zero_iff.mp (by simpa using hr)
    have hresults : results=[] := List.length_eq_zero_iff.mp (by simpa using hs)
    subst records results
    rfl
  | cons q qs ih =>
    cases records with
    | nil => simp at hr
    | cons r rs =>
      cases results with
      | nil => simp at hs
      | cons result rest =>
        obtain ⟨hpost,hquery⟩ := h 0 q r result (by simp) (by simp) (by simp)
        simp only [Nat.add_zero,List.take_zero,List.append_nil] at hquery
        have hr' : rs.length=qs.length := by simpa using hr
        have hs' : rest.length=qs.length := by simpa using hs
        have hrec := ih (earlier++[r]) rs rest hr' hs' (by
          intro i q' r' result' hq' hr' hs'
          have hi := h (i+1) q' r' result' (by simpa using hq') (by simpa using hr') (by simpa using hs')
          refine ⟨hi.1,?_⟩
          simpa only [List.length_append,List.length_singleton,List.take_succ_cons,List.append_assoc,
            List.singleton_append,Nat.add_assoc,Nat.add_comm 1 i] using hi.2)
        rw [chunk,hquery]
        change (do
          let rest ← chunk policy stored codec cfg sh g S init words dummy operation start st
            (earlier++[Api.postRecord codec q result.found]) qs
          pure (Api.postRecord codec q result.found::rest.1,result::rest.2)) = _
        rw [←hpost,hrec]
        rfl

end RebuildBound.NativeMatchApiProof
namespace RebuildBound.NativeMatchApiProof
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch
open Spec NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchHierarchy NativeMatchDispatch NativeMatchApi NativeRoutingActual
open NativeMatchDenseTraceProof NativeRoutingActualProof BatchFreshProof AdaptiveFoundMemProof BatchCorrectnessProof OnlineCorrectnessProof

lemma requester_key_used (g : OnlineGeom) (run : BatchRun) (j : Nat) (r : Rec)
    (hr : r ∈ requesterRecords (OnlineBatch.stateAt g run j)) : r.key ∈ usedKeys run := by
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp (requester_sub g run j r hr)
  exact used_slot run s (List.mem_of_mem_take hs)

lemma op_key_used (run : BatchRun) (j : Nat) (op : OnlineBatch.Op) (ho : run.ops[j]?=some op)
    (r : Rec) (real : Bool) (hr : (r,real)∈op.lanes) : r.key∈usedKeys run := by
  obtain ⟨lane,hl,he⟩ := List.mem_iff_getElem.mp hr
  have hs := slot_at run ho (show op.lanes[lane]?=some (r,real) by
    rw [List.getElem?_eq_getElem hl,he])
  exact used_slot run _ (List.mem_of_getElem? hs)

lemma earlier_key_used (run : BatchRun) (s : OnlineBatch.Slot) (r : Rec)
    (hr : r ∈ Probe.earlier run s) : r.key∈usedKeys run := by
  unfold Probe.earlier at hr
  cases ho : run.ops[s.op]? with
  | none => simp [ho] at hr
  | some op =>
    simp only [ho,Option.map_some,Option.getD_some] at hr
    obtain ⟨rp,hrp,rfl⟩ := List.mem_map.mp hr
    exact op_key_used run s.op op ho rp.1 rp.2 (List.mem_of_mem_take hrp)

lemma batchNormalize_collision (geo : HierarchyGeometry) (hgeo : geo.LowerCompatible)
    (g : OnlineGeom) (hg : g.unitEntries*g.unitsPerPrefix=geo.cfg.carryPositions 1)
    (hE : 0<g.unitEntries) (run : BatchRun) (hi : (run.init.map Rec.key).Nodup)
    (S : Schedule) (words : Words) (stored : LogicalKey → Stored) (t : Nat)
    (hb : batchNormalizeBad stored geo.cfg geo.shapes g run S words t) :
    NativeNormalize.collision ((usedKeys run).map fun key => (key,stored key)) := by
  cases hs : (slots run)[t]? with
  | none => simp [batchNormalizeBad,hs] at hb
  | some s =>
    have hk := used_slot run s (List.mem_of_getElem? hs)
    obtain ⟨_,hb⟩ : s.probes=true ∧ _ := by simpa only [batchNormalizeBad,hs] using hb
    rcases hb with hf | hd | ht
    · exact list_normalization_collision stored _ s.record.key _ hk (earlier_key_used run s) hf
    · apply denseScan_normalization_collision stored _ s.record.key _ hk _ hd
      intro r hr
      rw [batchPages_records] at hr
      simp only [OnlineBatch.denseRecords,hs] at hr
      apply requester_key_used g run s.op r
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨unit,hu,hr⟩ := List.mem_flatMap.mp hr
        exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨unit,List.mem_of_mem_drop hu,hr⟩)
      · exact List.mem_append_right _ hr
    · apply cascade_normalization_collision stored _ _ s.record.key _ hk _ ht
      intro c _ r hr
      exact List.mem_toFinset.mp (table_used geo (HierarchySemanticsProof.lower hgeo)
        (used_trace geo.cfg g run hg hE hi) words c.1 c.2 r hr)

lemma requesterNormalize_collision (g : OnlineGeom) (run : BatchRun) (j : Nat)
    (op : OnlineBatch.Op) (ho : run.ops[j]?=some op) (stored : LogicalKey → Stored)
    (hb : requesterNormalizeBad stored (OnlineBatch.stateAt g run j) op.requester) :
    NativeNormalize.collision ((usedKeys run).map fun key => (key,stored key)) := by
  have hkey : ∀ key∈requesterKeys op.requester, key∈usedKeys run := by
    cases op with
    | probe r =>
      intro key hk
      have he : key=r.key := by simpa [OnlineBatch.Op.requester,requesterKeys] using hk
      subst key
      exact op_key_used run j (.probe r) ho r true (by simp [OnlineBatch.Op.lanes])
    | blind r =>
      intro key hk
      have he : key=r.key := by simpa [OnlineBatch.Op.requester,requesterKeys] using hk
      subst key
      exact op_key_used run j (.blind r) ho r false (by simp [OnlineBatch.Op.lanes])
    | batch lanes =>
      intro key hk
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hk
      exact op_key_used run j (.batch lanes) ho r true (List.mem_map.mpr ⟨r,hr,rfl⟩)
  rcases hb with hu | hd
  · obtain ⟨page,hp,key,hk,hb⟩ := hu
    apply dense_normalization_collision stored page key _ (hkey key hk) _ hb
    intro r hr
    apply requester_key_used g run j r
    apply List.mem_append_right
    rw [←allBucketPages_records (OnlineBatch.stateAt g run j).current]
    exact List.mem_flatMap.mpr ⟨page,hp,hr⟩
  · cases op with
    | probe r => exact False.elim hd
    | blind r => exact False.elim hd
    | batch lanes =>
      obtain ⟨r,hr,hb⟩ := hd
      apply list_normalization_collision stored lanes r.key _
        (hkey r.key (List.mem_map.mpr ⟨r,hr,rfl⟩)) _ hb
      intro q hq
      exact hkey q.key (List.mem_map.mpr ⟨q,hq,rfl⟩)

end RebuildBound.NativeMatchApiProof
namespace RebuildBound.NativeMatchApiProof
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch
open Spec NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchHierarchy NativeMatchDispatch NativeMatchApi
open BatchFreshProof

lemma referenceState_zero (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun)
    (S : Schedule) (words : Words) (dummy : Nat → Nat → Nat) (requests : List Api.Request) (m : Nat) :
    referenceState cfg sh g run S words dummy requests 0 m = empty := by
  simp [referenceState,empty,OnlineBatch.stateAt,Requester.run]

lemma referenceState_succ (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun)
    (S : Schedule) (words : Words) (dummy : Nat → Nat → Nat) (requests : List Api.Request)
    (j m : Nat) (op : OnlineBatch.Op) (ho : run.ops[j]?=some op) (group : List Api.Request)
    (hgroup : (requests.drop (fs run j)).take op.lanes.length=group) :
    referenceState cfg sh g run S words dummy requests (j+1) m =
      let before := referenceState cfg sh g run S words dummy requests j m
      let results := (List.range op.lanes.length).map (fun i => Probe.batch cfg sh g run S words dummy (fs run j+i))
      ⟨before.ops++[op],before.requests++group,before.selected++results,
        before.rows++results.map (fun result i => result.addresses.getD i.val 0),
        Requester.step g.unitEntries before.requester op.requester⟩ := by
  have hop : run.ops.take (j+1) = run.ops.take j++[op] := by
    rw [List.take_add_one,ho]
    rfl
  have hfs := fs_succ run ho
  have hrs : (List.range (fs run (j+1))).map (Probe.batch cfg sh g run S words dummy) =
      (List.range (fs run j)).map (Probe.batch cfg sh g run S words dummy) ++
        (List.range op.lanes.length).map (fun i => Probe.batch cfg sh g run S words dummy (fs run j+i)) := by
    rw [hfs,List.range_add,List.map_append,List.map_map]
    rfl
  have hreq : requests.take (fs run (j+1))=requests.take (fs run j)++group := by
    rw [hfs,List.take_add,hgroup]
  simp only [fs] at hrs hreq
  simp only [referenceState,hop,hrs,hreq,List.map_append,BatchFreshProof.stateAt_succ g run ho,fs]

end RebuildBound.NativeMatchApiProof
namespace RebuildBound.NativeMatchApiProof
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch
open Spec NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchHierarchy NativeMatchDispatch NativeMatchApi
open BatchFreshProof

lemma operation_chunk_reference (policy : Policy) (stored : LogicalKey → Stored) (codec : Api.Codec)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (run : BatchRun)
    (words : Words) (dummy : Nat → Nat → Nat) (j m : Nat) (state : State m)
    (hop : state.ops.length=j) (hrow : state.rows.length=fs run j)
    (hst : state.requester=OnlineBatch.stateAt g run j) (hunsh : run.unsh=fun r => codec.flag r.val)
    (records : List Rec) (qs : List Api.Request) (ho : run.ops[j]?=some (.batch records))
    (hlen : records.length=qs.length)
    (hp : ∀ i q r, qs[i]?=some q → records[i]?=some r →
      r.key=q.key ∧ r=Api.postRecord codec q (Probe.batch cfg sh g run S words dummy (fs run j+i)).found)
    (hq : ∀ t s, (slots run)[t]?=some s → s.probes=true →
      query policy stored cfg sh g S run.init run.unsh words dummy s.op (fs run s.op) s.lane
        (OnlineBatch.stateAt g run s.op) (Probe.earlier run s) s.record.key =
      .ok (Probe.batch cfg sh g run S words dummy t)) :
    operation policy stored codec cfg sh g S run.init words dummy state (.chunk qs) =
      .ok (.batch records,(List.range records.length).map
        (fun i => Probe.batch cfg sh g run S words dummy (fs run j+i))) := by
  let results := (List.range records.length).map fun i => Probe.batch cfg sh g run S words dummy (fs run j+i)
  have hc := chunk_by_lanes policy stored codec cfg sh g S run.init words dummy j (fs run j)
    (OnlineBatch.stateAt g run j) [] records qs results hlen (by simp [results,hlen]) (by
      intro i q r result hi hr hresult
      have hii := (List.getElem?_eq_some_iff.mp hr).1
      have he : result=Probe.batch cfg sh g run S words dummy (fs run j+i) := by
        simpa [results,List.getElem?_map,List.getElem?_range,hii] using hresult.symm
      obtain ⟨hk,hp⟩ := hp i q r hi hr
      refine ⟨by simpa only [he] using hp,?_⟩
      have hslot := slot_at run ho (show (OnlineBatch.Op.batch records).lanes[i]?=some (r,true) by
        simp only [OnlineBatch.Op.lanes,List.getElem?_map,hr,Option.map_some])
      have hlocal := hq (fs run j+i) ⟨j,i,r,true⟩ hslot rfl
      have hear : Probe.earlier run ⟨j,i,r,true⟩ = records.take i := by
        simp only [Probe.earlier,ho,Option.map_some,Option.getD_some,OnlineBatch.Op.lanes,
          ←List.map_take,List.map_map,Function.comp_def]
        change List.map id _ = _
        rw [List.map_id]
      rw [hear,hk,hunsh] at hlocal
      simpa only [List.length_nil,Nat.zero_add,List.nil_append,he] using hlocal)
  simp only [operation]
  rw [hop,hrow,hst,hc]
  rfl

lemma issueFrame_from_operation (policy : Policy) (stored : LogicalKey → Stored) (codec : Api.Codec)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (init : List Rec)
    (words : Words) (dummy : Nat → Nat → Nat) {m : Nat} (choose : ApiAdaptive.Chooser m)
    (state : State m) (frame : ApiAdaptive.Frame) (group : PublicApi.Group Api.Request)
    (op : OnlineBatch.Op) (results : List Probe.Result)
    (hg : ApiAdaptive.requests choose state.rows frame=group)
    (ho : operation policy stored codec cfg sh g S init words dummy state group=.ok (op,results))
    (hs : requesterStep (policy state.ops.length (.unit state.requester.frozen.length)) stored
      g.unitEntries state.requester op.requester=Requester.step g.unitEntries state.requester op.requester) :
    issueFrame policy stored codec cfg sh g S init words dummy choose state frame = .ok
      ⟨state.ops++[op],state.requests++group.lanes,state.selected++results,
        state.rows++results.map (fun result i=>result.addresses.getD i.val 0),
        Requester.step g.unitEntries state.requester op.requester⟩ := by
  simp only [issueFrame,hg]
  rw [ho]
  change Except.ok _ = _
  rw [hs]

end RebuildBound.NativeMatchApiProof
namespace RebuildBound.NativeMatchApiProof
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch
open Spec NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchHierarchy NativeMatchDispatch NativeMatchApi NativeRoutingActual
open NativeMatchDenseTraceProof NativeMatchDispatchProof BatchFreshProof

lemma batchRemoval_in_query (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : BatchRun) (S : Schedule) (words : Words) (j : Nat) (lanes : List Rec)
    (ho : run.ops[j]?=some (.batch lanes)) (e : Event)
    (he : e∈unitBatchEvents (OnlineBatch.stateAt g run j).current (lanes.map Rec.key)) :
    e∈batchPrefixEvents cfg sh g run S words (slots run).length := by
  obtain ⟨page,hpage,key,hkey,he⟩ : ∃ page∈allBucketPages (OnlineBatch.stateAt g run j).current,
      ∃ key∈lanes.map Rec.key, e∈denseEvents page key true := by
    simpa only [unitBatchEvents,denseBatchEvents,List.mem_flatMap] using he
  obtain ⟨record,hr,rfl⟩ := List.mem_map.mp hkey
  obtain ⟨lane,hl,hrec⟩ := List.mem_iff_getElem.mp hr
  have hs := slot_at run ho (show (OnlineBatch.Op.batch lanes).lanes[lane]?=some (record,true) by
    simp only [OnlineBatch.Op.lanes,List.getElem?_map,List.getElem?_eq_getElem hl,Option.map_some,hrec])
  apply List.mem_flatMap.mpr
  refine ⟨fs run j+lane,List.mem_range.mpr (List.getElem?_eq_some_iff.mp hs).1,?_⟩
  simp only [batchEvents,hs,↓reduceIte]
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨page,?_,he⟩
  simp only [batchPages,hs,requesterPages]
  exact List.mem_append_right _ hpage

lemma requesterStep_off (mode : Nat → Mode) (stored : LogicalKey → Stored)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun) (S : Schedule) (words : Words)
    (j : Nat) (op : OnlineBatch.Op) (ho : run.ops[j]?=some op)
    (hn : ¬ NativeNormalize.collision ((usedKeys run).map fun key => (key,stored key)))
    (hoff : ∀ e∈batchPrefixEvents cfg sh g run S words (slots run).length, ¬ e.bad stored) :
    requesterStep mode stored g.unitEntries (OnlineBatch.stateAt g run j) op.requester =
      Requester.step g.unitEntries (OnlineBatch.stateAt g run j) op.requester := by
  apply requesterStep_agreement mode stored g.unitEntries _ op.requester (requester_unique g run j)
    (fun hb => hn (requesterNormalize_collision g run j op ho stored hb))
  cases op with
  | probe r => simp [OnlineBatch.Op.requester]
  | blind r => simp [OnlineBatch.Op.requester]
  | batch lanes =>
    intro _ e he
    exact hoff e (batchRemoval_in_query cfg sh g run S words j lanes ho e he)

end RebuildBound.NativeMatchApiProof
namespace RebuildBound.NativeMatchApiScheduledReplay
open Model Model.Hierarchy Model.Online Model.OnlineBatch Spec
open Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchHierarchy
open HierarchyInvariantProof OnlineCorrectnessProof OnlineFreshProof BatchFreshProof

theorem coordinate_bounds {geo : HierarchyGeometry}
    (F : LowFacts geo.cfg geo.rows geo.direct) (S : Schedule) (n m : Nat)
    (hS : SchedulePremises geo.cfg S n m) (hN : n ≤ geo.cfg.horizon)
    (j : Nat) (hj : j<n) (c : Nat × Nat) (hc : c∈(S j).tables) :
    1≤c.1 ∧ c.1≤geo.cfg.levels ∧ c.2≤geo.cfg.seed c.1+geo.cfg.ordinals c.1 ∧
      time geo.cfg c.1 c.2≤geo.cfg.seed 1+geo.cfg.ordinals 1 := by
  have hpub := hS.coords j hj c hc
  have hend := (tiles_bounds (hS.tile j hj) c hc).2.2
  have hcons := (hS.consumed j hj).2
  have hEnd : (window geo.cfg c.1 c.2).2 ≤ geo.cfg.seed 1*geo.cfg.carryPositions 1+geo.cfg.horizon :=
    le_trans hend (le_trans hcons (by unfold pos; omega))
  refine ⟨hpub.1,hpub.2.1,coordinate_horizon F hpub hEnd,?_⟩
  have hP := cp_pos F (ℓ:=1) (by omega) (by omega)
  rw [window_snd,←time_cp] at hEnd
  have hsub : (time geo.cfg c.1 c.2-geo.cfg.seed 1)*geo.cfg.carryPositions 1≤geo.cfg.horizon := by
    rw [Nat.sub_mul]
    omega
  have hdiv := (Nat.le_div_iff_mul_le hP).mpr hsub
  unfold Config.ordinals
  omega

theorem tables (member : ConfigurationFamily.Member) (initialized : Bool)
    (hmember : member∈ConfigurationFamily.members) (h : Nat) (run : BatchRun)
    (hready : RunReady member initialized h run) (S : Schedule) (n m : Nat)
    (hS : SchedulePremises ((member.geometry initialized).chunk h).cfg S n m)
    (hN : n ≤ ((member.geometry initialized).chunk h).cfg.horizon)
    (stored : LogicalKey → Stored) (words : Words)
    (hno : ¬Fails ((member.geometry initialized).chunk h).cfg
      ((member.geometry initialized).chunk h).shapes (traceOf ⟨64,member.r0⟩ run) words)
    (hoff : OffEvents stored ((member.geometry initialized).chunk h).cfg
      ((member.geometry initialized).chunk h).shapes (traceOf ⟨64,member.r0⟩ run) words)
    (t : Nat) (slot : OnlineBatch.Slot) (hs : (slots run)[t]?=some slot) (ht : t<n) :
    ∀ c∈(S (fs run slot.op)).tables,
      (1≤c.1 ∧ c.1≤((member.geometry initialized).chunk h).cfg.levels ∧
        c.2≤((member.geometry initialized).chunk h).cfg.seed c.1+
          ((member.geometry initialized).chunk h).cfg.ordinals c.1) ∧
      ∃ out, nativeTable stored ((member.geometry initialized).chunk h).cfg
        ((member.geometry initialized).chunk h).shapes (traceOf ⟨64,member.r0⟩ run) words c.1 c.2=some out ∧
        OutputEq out (table ((member.geometry initialized).chunk h).cfg
          ((member.geometry initialized).chunk h).shapes (traceOf ⟨64,member.r0⟩ run) words c.1 c.2) := by
  intro c hc
  have hgeo := ConfigurationFamilyProbabilityProof.structural initialized member hmember h
  have hb := coordinate_bounds (HierarchySemanticsProof.lower hgeo.1) S n m hS hN
    (fs run slot.op) (lt_of_le_of_lt (fs_le run hs) ht) c hc
  exact ⟨⟨hb.1,hb.2.1,hb.2.2.1⟩,
    RebuildBound.NativeMatchHierarchyReplay member initialized hmember h run hready stored words
      hno hoff c.1 c.2 hb.2.2.2⟩

end RebuildBound.NativeMatchApiScheduledReplay
namespace RebuildBound.NativeMatchApiProjection
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch
open Spec NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchHierarchy NativeMatchDispatch NativeMatchApi NativeRoutingActual NativeMatchProduction
open NativeMatchApiProof BatchFreshProof
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

lemma slots_length (ctx : Context member initialized h) (tape : IdealKey.Tape) :
    (slots (ctx.run tape)).length=ctx.accesses := by
  rw [AdaptiveCausalProof.slots_length]
  unfold Context.run
  rw [AdaptiveCausalProof.realized_widths]
  rfl

lemma query_context (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (policy : Policy) (stored : LogicalKey→Stored) (tape : IdealKey.Tape)
    (hcap : ¬ctx.capacityBad tape)
    (hn : ¬NativeNormalize.collision ((usedKeys (ctx.run tape)).map fun key=>(key,stored key)))
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
    exact hn (batchNormalize_collision ctx.geo hstruct.1 ctx.unit hgeom (by change 0<64; decide)
      (ctx.run tape) hi ctx.schedule (IdealHierarchy.words tape) stored t hb)
  · intro e he
    apply hoff e
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨t,List.mem_range.mpr htn,he⟩)

lemma reference_rows (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) (j : Nat) :
    (referenceState ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (NativeMatchApiReference.requests ctx tape)
      j ctx.transcriptWidth).rows =
    (NativeMatchApiReference.rows ctx tape).take (fs (ctx.run tape) j) := by
  have hle : fs (ctx.run tape) j≤ctx.accesses := by
    rw [←slots_length ctx tape,AdaptiveCausalProof.slots_length]
    unfold fs
    calc
      _ ≤ ((widths (ctx.run tape)).take j).sum+((widths (ctx.run tape)).drop j).sum := Nat.le_add_right _ _
      _ = _ := by rw [←List.sum_append,List.take_append_drop]
  rw [NativeMatchApiReference.rows_eq_probes ctx hm hv tape]
  unfold fs at hle
  simp only [referenceState,fs,List.map_map,Function.comp_def,←List.map_take,List.take_range,Nat.min_eq_left hle]

end RebuildBound.NativeMatchApiProjection
namespace RebuildBound.NativeMatchApiProjection
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch
open Spec NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchHierarchy NativeMatchDispatch NativeMatchApi NativeRoutingActual NativeMatchProduction
open NativeMatchApiProof BatchFreshProof
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

lemma frame_agreement (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (policy : Policy) (stored : LogicalKey→Stored) (tape : IdealKey.Tape)
    (hcap : ¬ctx.capacityBad tape)
    (hn : ¬NativeNormalize.collision ((usedKeys (ctx.run tape)).map fun key=>(key,stored key)))
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
  have hquery := query_context ctx hm hv policy stored tape hcap hn hoff
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
  have hstep := requesterStep_off (policy state.ops.length (.unit state.requester.frozen.length)) stored
    ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule (IdealHierarchy.words tape) j op ho hn
    (fun e he => hoff e (List.mem_append_right _ (by simpa only [slots_length ctx tape] using he)))
  have hh := issueFrame_from_operation policy stored ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule
    ctx.init (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) ctx.compiled state frame group op _ hchoice heval hstep
  rw [referenceState_succ ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (NativeMatchApiReference.requests ctx tape)
    j ctx.transcriptWidth op ho group.lanes hslice]
  exact hh

end RebuildBound.NativeMatchApiProjection
namespace RebuildBound.NativeMatchApiProof
open Model Model.Hierarchy Model.Online Spec NativeMatch NativeMatch.Lanes NativeMatchApi

lemma execute_chain (policy : Policy) (stored : LogicalKey→Stored) (codec : Api.Codec)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (init : List Rec)
    (words : Words) (dummy : Nat→Nat→Nat) {m : Nat} (choose : ApiAdaptive.Chooser m)
    (states : Nat→State m) (frames : List ApiAdaptive.Frame) (j : Nat)
    (hstep : ∀ i frame, frames[i]?=some frame →
      issueFrame policy stored codec cfg sh g S init words dummy choose (states (j+i)) frame =
        .ok (states (j+i+1))) :
    execute policy stored codec cfg sh g S init words dummy choose (states j) frames =
      .ok (states (j+frames.length)) := by
  induction frames generalizing j with
  | nil => simp [execute]
  | cons frame frames ih =>
    have hh := hstep 0 frame (by simp)
    simp only [Nat.add_zero] at hh
    rw [execute,hh]
    change execute policy stored codec cfg sh g S init words dummy choose (states (j+1)) frames = _
    have hi := ih (j+1) (by
      intro i frame hframe
      have hh := hstep (i+1) frame (by simpa using hframe)
      simpa only [Nat.add_assoc,Nat.add_comm 1 i] using hh)
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1 frames.length] using hi
end RebuildBound.NativeMatchApiProof
namespace RebuildBound.NativeMatchApiProjection
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch
open Spec NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchHierarchy NativeMatchDispatch NativeMatchApi NativeRoutingActual NativeMatchProduction
open NativeMatchApiProof BatchFreshProof
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

lemma operations_length (ctx : Context member initialized h) (tape : IdealKey.Tape) :
    (ctx.run tape).ops.length=ctx.frames.length := by
  have hh := congrArg List.length (AdaptiveCausalProof.realized_widths ctx.geo.cfg ctx.geo.shapes ctx.unit
    ctx.schedule ctx.client (IdealHierarchy.words tape) (IdealHierarchy.dummy tape))
  simpa only [OnlineBatch.widths,List.length_map,Adaptive.shapeWidths,Context.client,ApiAdaptive.run,
    ApiAdaptive.shape,Context.run] using hh

lemma state_ext {m : Nat} {a b : State m} (hops : a.ops=b.ops) (hreq : a.requests=b.requests)
    (hselected : a.selected=b.selected) (hrows : a.rows=b.rows) (hst : a.requester=b.requester) : a=b := by
  cases a
  cases b
  cases hops
  cases hreq
  cases hselected
  cases hrows
  cases hst
  rfl

lemma referenceState_full (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) :
    referenceState ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (NativeMatchApiReference.requests ctx tape)
      ctx.frames.length ctx.transcriptWidth = reference ctx tape := by
  have hlen := operations_length ctx tape
  have hfs : fs (ctx.run tape) ctx.frames.length=ctx.accesses := by
    rw [←hlen,fs_length,slots_length]
  apply state_ext
  · change (ctx.run tape).ops.take ctx.frames.length=(ctx.run tape).ops
    rw [←hlen,List.take_length]
  · change (NativeMatchApiReference.requests ctx tape).take (fs (ctx.run tape) ctx.frames.length)=
      NativeMatchApiReference.requests ctx tape
    rw [hfs,←NativeMatchApiReference.requests_length ctx tape,List.take_length]
  · change (List.range (fs (ctx.run tape) ctx.frames.length)).map _=(List.range ctx.accesses).map _
    rw [hfs]
  · have hr := reference_rows ctx hm hv tape ctx.frames.length
    rw [hfs,←NativeMatchApiReference.rows_length ctx tape,List.take_length] at hr
    exact hr
  · change OnlineBatch.stateAt ctx.unit (ctx.run tape) ctx.frames.length=
      OnlineBatch.stateAt ctx.unit (ctx.run tape) (ctx.run tape).ops.length
    rw [hlen]

lemma projection_raw (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (policy : Policy) (stored : LogicalKey→Stored) (tape : IdealKey.Tape)
    (hcap : ¬ctx.capacityBad tape)
    (hn : ¬NativeNormalize.collision ((usedKeys (ctx.run tape)).map fun key=>(key,stored key)))
    (hoff : ∀ e∈referenceEvents ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
      (IdealHierarchy.words tape) ctx.accesses, ¬e.bad stored) :
    production ctx policy stored tape=.ok (reference ctx tape) := by
  have hh := execute_chain policy stored ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.init
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) ctx.compiled
    (fun j=>referenceState ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (NativeMatchApiReference.requests ctx tape)
      j ctx.transcriptWidth) ctx.frames 0 (by
        intro i frame hf
        simpa only [Nat.zero_add] using frame_agreement ctx hm hv policy stored tape hcap hn hoff i frame hf)
  rw [referenceState_zero,Nat.zero_add,referenceState_full ctx hm hv tape] at hh
  exact hh
end RebuildBound.NativeMatchApiProjection
namespace RebuildBound.NativeMatchApiProjection
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch
open Spec NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchHierarchy NativeMatchDispatch NativeMatchApi NativeRoutingActual NativeMatchProduction
open NativeMatchApiProof BatchFreshProof
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

lemma projection (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (policy : Policy) (stored : LogicalKey→Stored) (tape : IdealKey.Tape)
    (hcap : ¬ctx.capacityBad tape)
    (hready : NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses=true)
    (hn : ¬normalizationBad ctx stored tape)
    (hoff : ∀ e∈ctx.inventory tape, ¬e.bad stored) :
    production ctx policy stored tape=.ok (reference ctx tape) := by
  classical
  have hi : ctx.inventory tape=referenceEvents ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape)
      ctx.schedule (IdealHierarchy.words tape) ctx.accesses := by
    change (if Fails ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape)) (IdealHierarchy.words tape) ∨
      NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses=false then [] else _)=_
    rw [ite_eq_right (fun hbad => hbad.elim hcap (fun hb => by rw [hready] at hb; contradiction))]
    rfl
  apply projection_raw ctx hm hv policy stored tape hcap hn
  simpa only [hi] using hoff

lemma divergence (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (policy : Policy) (stored : LogicalKey→Stored) (tape : IdealKey.Tape)
    (hd : mismatch ctx policy stored tape) :
    ctx.capacityBad tape ∨ ringStopped ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.snapshots ctx.client ctx.accesses tape ∨
      normalizationBad ctx stored tape ∨ ∃ e∈ctx.inventory tape, e.bad stored := by
  by_contra hbad
  push Not at hbad
  have hr : NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses=true := by
    cases he : NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses with
    | false => exact (hbad.2.1 he).elim
    | true => rfl
  exact hd (projection ctx hm hv policy stored tape hbad.1 hr hbad.2.2.1 hbad.2.2.2)

end RebuildBound.NativeMatchApiProjection
namespace RebuildBound

theorem NativeMatchApiFallback : Spec.NativeMatchApiFallback_statement :=
  NativeMatchDispatchProof.storedFirst_agreement

theorem NativeMatchApiDispatch : Spec.NativeMatchApiDispatch_statement := by
  intro mode stored page key hu hn hoff
  exact ⟨NativeMatchDispatchProof.page_record_dispatch_agreement mode.cross stored page key hu hn hoff,
    NativeMatchDispatchProof.page_dispatch_agreement mode.cross stored page key hu hn hoff⟩

theorem NativeMatchApiRemoval : Spec.NativeMatchApiRemoval_statement := NativeMatchApiProof.requesterStep_off

theorem NativeMatchApiProjection : Spec.NativeMatchApiProjection_statement := by
  intro member initialized h ctx hm hv
  exact NativeMatchApiProjection.projection ctx hm hv

theorem NativeMatchApiDivergence : Spec.NativeMatchApiDivergence_statement := by
  intro member initialized h ctx hm hv
  exact NativeMatchApiProjection.divergence ctx hm hv
end RebuildBound
namespace RebuildBound.NativeMatchApiResultsProof
open Model Model.Hierarchy Model.Online Spec NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchHierarchy NativeMatchDispatch NativeMatchApi NativeRoutingActual NativeMatchProduction
open MeasureTheory
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

lemma selected_at (ctx : Context member initialized h) (tape : IdealKey.Tape) (t : Nat) (ht : t<ctx.accesses) :
    (reference ctx tape).selected.getD t ⟨none,[]⟩ =
      Probe.batch ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) t := by
  simp only [NativeMatchApi.reference,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,ht,↓reduceIte,
    Option.map_some,Option.getD_some]

lemma reference_results (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) :
    ApiResultsCorrect ctx.geo ctx.codec ctx.unit
      ⟨(reference ctx tape).ops,ctx.init,fun r=>ctx.codec.flag r.val⟩ ctx.schedule ctx.accesses
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (reference ctx tape).requests
      (fun t=>(reference ctx tape).selected.getD t ⟨none,[]⟩) := by
  apply ApiBoundedProof.results ctx.geo ctx.codec ctx.unit (ctx.run tape) ctx.schedule ctx.accesses
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (NativeMatchApiReference.requests ctx tape)
  · exact NativeMatchApiReference.requests_length ctx tape
  · exact (NativeMatchApiReference.contracts ctx hm hv tape).1
  · intro t ht
    rw [NativeMatchApiReference.requests_length] at ht
    exact selected_at ctx tape t ht

lemma native_results (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (policy : Policy) (stored : LogicalKey→Stored) (tape : IdealKey.Tape)
    (hcap : ¬ctx.capacityBad tape)
    (hready : NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses=true)
    (hn : ¬normalizationBad ctx stored tape) (hoff : ∀ e∈ctx.inventory tape, ¬e.bad stored)
    (state : State ctx.transcriptWidth) (hs : production ctx policy stored tape=.ok state) :
    ApiResultsCorrect ctx.geo ctx.codec ctx.unit
      ⟨state.ops,ctx.init,fun r=>ctx.codec.flag r.val⟩ ctx.schedule ctx.accesses
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) state.requests
      (fun t=>state.selected.getD t ⟨none,[]⟩) := by
  have he := hs.symm.trans (NativeMatchApiProjection.projection ctx hm hv policy stored tape hcap hready hn hoff)
  cases Except.ok.inj he
  exact reference_results ctx hm hv tape

lemma reference_transcript (ctx : Context member initialized h) (tape : IdealKey.Tape) :
    (fun (t : Fin ctx.accesses) (i : Fin ctx.transcriptWidth)=>(reference ctx tape).rows.getD t.val (fun _=>0) i)=
      Adaptive.transcript ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client ctx.accesses
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) := rfl

lemma reference_transcript_law (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) :
    Measurable (fun tape (t : Fin ctx.accesses) (i : Fin ctx.transcriptWidth)=>
      (reference ctx tape).rows.getD t.val (fun _=>0) i) ∧
    IdealKey.tapeLaw.map (fun tape (t : Fin ctx.accesses) (i : Fin ctx.transcriptWidth)=>
      (reference ctx tape).rows.getD t.val (fun _=>0) i)=
      simLaw ctx.geo.cfg (OnlineBatch.slotSchedule (Adaptive.shapeWidths (ApiAdaptive.shape ctx.frames)) ctx.schedule)
        (Adaptive.shapePattern (ApiAdaptive.shape ctx.frames)) ctx.accesses ctx.transcriptWidth := by
  exact IdealApiExact ctx.geo (NativeMatchProductionProof.structural ctx hm) ctx.codec ctx.unit ctx.schedule
    ctx.init ctx.transcriptWidth ctx.batchWidth ctx.batches ctx.choose hv.1.2.2.2 hv.1.1
    (NativeMatchProductionProof.init_bound ctx hm hv (fun _=>0))
    (NativeMatchProductionProof.alignment member hm initialized h) (by change 0<64;decide) hv.2.1 hv.2.2.1
end RebuildBound.NativeMatchApiResultsProof
