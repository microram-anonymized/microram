import RebuildBound.Spec.NativeNormalize.LiveApi
import RebuildBound.Proofs.ApiCapacity
import RebuildBound.Proofs.ApiAdaptive.Correctness
import Mathlib.Tactic


namespace RebuildBound.NativeNormalizeLiveApiProof
open Model Model.Api Spec.NativeNormalizeLiveApi

lemma supportImage_step (f : LogicalKey → LogicalKey) (logical stored : State)
    (h : SupportImage f logical stored) (q : Request) :
    SupportImage f (step q logical) (step (mapRequest f q) stored) := by
  intro hash hh
  by_cases he : hash = f q.key
  · subst hash
    simp only [step, mapRequest, ↓reduceIte] at hh
    cases ha : q.action with
    | write v | blindWrite v =>
      exact ⟨q.key, by simp [step, nextValue, ha], rfl⟩
    | erase => simp [nextValue, ha] at hh
    | read =>
      obtain ⟨key, hk, he⟩ := h _ (by simpa [nextValue, ha] using hh)
      refine ⟨key, ?_, he⟩
      by_cases hkq : key = q.key <;> simp_all [step, nextValue]
    | exchange v insert =>
      cases insert with
      | true => exact ⟨q.key, by simp [step, nextValue, ha], rfl⟩
      | false =>
        have hs : (stored (f q.key)).isSome = true := by
          simpa [nextValue, ha] using hh
        obtain ⟨key, hk, he⟩ := h _ hs
        refine ⟨key, ?_, he⟩
        by_cases hkq : key = q.key
        · subst key; simp [step, nextValue, ha, hk]
        · simpa [step, hkq] using hk
  · simp only [step, mapRequest, he, ↓reduceIte] at hh
    obtain ⟨key, hk, hkey⟩ := h hash hh
    have hkq : key ≠ q.key := by
      intro heq; subst key; exact he hkey.symm
    exact ⟨key, by simpa [step, hkq] using hk, hkey⟩

lemma queried_value (f : LogicalKey → LogicalKey) (logical stored : State)
    (h : Represents f logical stored) (key : LogicalKey)
    (hs : ¬liveAlias f logical key) : stored (f key) = logical key := by
  cases hl : logical key with
  | some value => exact h.1 key value hl
  | none =>
    cases he : stored (f key) with
    | none => rfl
    | some value =>
      obtain ⟨other, ho, hf⟩ := h.2 _ value he
      have hne : other ≠ key := by intro heq; subst other; simp [hl] at ho
      exact False.elim (hs ⟨other, hne, by simp [ho], hf⟩)

lemma represents_step (f : LogicalKey → LogicalKey) (logical stored : State)
    (h : Represents f logical stored) (q : Request)
    (hs : ¬liveAlias f logical q.key) :
    Represents f (step q logical) (step (mapRequest f q) stored) := by
  have hq := queried_value f logical stored h q.key hs
  constructor
  · intro key value hv
    by_cases he : key = q.key
    · subst key
      simpa [step, mapRequest, nextValue, hq] using hv
    · have hl : logical key = some value := by simpa [step, he] using hv
      have hf : f key ≠ f q.key := by
        intro hf
        exact hs ⟨key, he, by simp [hl], hf⟩
      simpa [step, mapRequest, hf] using h.1 key value hl
  · intro hash value hv
    by_cases he : hash = f q.key
    · subst hash
      refine ⟨q.key, ?_, rfl⟩
      simpa [step, mapRequest, nextValue, hq] using hv
    · have hh : stored hash = some value := by simpa [step, mapRequest, he] using hv
      obtain ⟨key, hk, hf⟩ := h.2 hash value hh
      have hkq : key ≠ q.key := by intro hh; subst key; exact he hf.symm
      exact ⟨key, by simpa [step, hkq] using hk, hf⟩

lemma repliesAgree (f : LogicalKey → LogicalKey) (logical stored : State)
    (h : Represents f logical stored) (qs : List Request) (hs : Safe f logical qs) :
    RepliesAgree f logical stored qs := by
  induction qs generalizing logical stored with
  | nil => trivial
  | cons q qs ih =>
    obtain ⟨hq, hrest⟩ := hs
    constructor
    · rw [queried_value f logical stored h q.key hq]
      rfl
    · exact ih (step q logical) (step (mapRequest f q) stored)
        (represents_step f logical stored h q hq) hrest

lemma supportImage_fold (f : LogicalKey → LogicalKey) (logical stored : State)
    (h : SupportImage f logical stored) (qs : List Request) :
    SupportImage f (qs.foldl (fun state q => step q state) logical)
      ((qs.map (mapRequest f)).foldl (fun state q => step q state) stored) := by
  induction qs generalizing logical stored with
  | nil => exact h
  | cons q qs ih =>
    exact ih (step q logical) (step (mapRequest f q) stored)
      (supportImage_step f logical stored h q)

lemma supportImage_stateAt (f : LogicalKey → LogicalKey) (logical stored : State)
    (h : SupportImage f logical stored) (qs : List Request) (t : Nat) :
    SupportImage f (stateAt logical qs t) (stateAt stored (qs.map (mapRequest f)) t) := by
  simpa only [stateAt, ← List.map_take] using supportImage_fold f logical stored h (qs.take t)

lemma support_count (f : LogicalKey → LogicalKey) (logical stored : State)
    (h : SupportImage f logical stored) (logicalKeys storedKeys : List LogicalKey)
    (hl : ApiCapacity.Supports logical logicalKeys) (hs : ApiCapacity.Supports stored storedKeys) :
    storedKeys.length ≤ logicalKeys.length := by
  have hsub : storedKeys.toFinset ⊆ logicalKeys.toFinset.image f := by
    intro hash hh
    obtain ⟨key, hk, he⟩ := h hash ((hs.2 hash).mp (List.mem_toFinset.mp hh))
    exact Finset.mem_image.mpr ⟨key, List.mem_toFinset.mpr ((hl.2 key).mpr hk), he⟩
  calc
    storedKeys.length = storedKeys.toFinset.card := (List.toFinset_card_of_nodup hs.1).symm
    _ ≤ (logicalKeys.toFinset.image f).card := Finset.card_le_card hsub
    _ ≤ logicalKeys.toFinset.card := Finset.card_image_le
    _ = logicalKeys.length := List.toFinset_card_of_nodup hl.1

/-- Capacity contracts under arbitrary stored-key collisions. No success,
matching, collision-free history, or fixed request assumption is needed. -/
lemma liveCapacity (f : LogicalKey → LogicalKey) (logical stored : State)
    (h : SupportImage f logical stored) (logicalKeys storedKeys : List LogicalKey)
    (hs : ApiCapacity.Supports stored storedKeys) (qs : List Request) (capacity : Nat)
    (hc : ApiCapacity.LiveCapacity capacity logical logicalKeys qs) :
    ApiCapacity.LiveCapacity capacity stored storedKeys (qs.map (mapRequest f)) := by
  refine ⟨hs, ?_⟩
  intro t ht
  exact (support_count f _ _ (supportImage_stateAt f logical stored h qs t) _ _
    (ApiFiniteSupport logical logicalKeys qs hc.1 t)
    (ApiFiniteSupport stored storedKeys (qs.map (mapRequest f)) hs t)).trans
    (hc.2 t (by simpa only [List.length_map] using ht))

lemma represents_init (f : LogicalKey → LogicalKey) (c : Codec) (init : List Rec)
    (hl : (init.map Rec.key).Nodup)
    (hs : ((init.map (mapRec f)).map Rec.key).Nodup) :
    Represents f (stateOf c init) (stateOf c (init.map (mapRec f))) := by
  constructor
  · intro key value hv
    cases he : DirectPrefix.latest key init with
    | none => simp [stateOf, he, Api.value, Probe.decode] at hv
    | some r =>
      have hr := OnlineCorrectnessProof.latest_some_mem he
      have hk := OnlineCorrectnessProof.latest_some_key he
      have hmap := OnlineCorrectnessProof.latest_of_unique_mem hs
        (List.mem_map_of_mem (f := mapRec f) hr) (congrArg f hk)
      simpa only [stateOf, he, hmap, Api.value, Probe.decode, mapRec] using hv
  · intro hash value hv
    cases he : DirectPrefix.latest hash (init.map (mapRec f)) with
    | none => simp [stateOf, he, Api.value, Probe.decode] at hv
    | some mapped =>
      have hr := OnlineCorrectnessProof.latest_some_mem he
      have hk := OnlineCorrectnessProof.latest_some_key he
      obtain ⟨r, hmem, rfl⟩ := List.mem_map.mp hr
      have hlog := OnlineCorrectnessProof.latest_of_unique_mem hl hmem rfl
      refine ⟨r.key, ?_, hk⟩
      simpa only [stateOf, he, hlog, Api.value, Probe.decode, mapRec] using hv

lemma represents_supportImage (f : LogicalKey → LogicalKey) (logical stored : State)
    (h : Represents f logical stored) : SupportImage f logical stored := by
  intro hash hh
  cases he : stored hash with
  | none => simp [he] at hh
  | some value =>
    obtain ⟨key, hk, hf⟩ := h.2 hash value he
    exact ⟨key, by simp [hk], hf⟩

lemma safe_of_prefix (f : LogicalKey → LogicalKey) (initial : State) (qs : List Request)
    (hs : ∀ t q, qs[t]? = some q → ¬liveAlias f (stateAt initial qs t) q.key) :
    Safe f initial qs := by
  induction qs generalizing initial with
  | nil => trivial
  | cons q qs ih =>
    refine ⟨?_, ?_⟩
    · simpa [stateAt] using hs 0 q (by rfl)
    · apply ih (step q initial)
      intro t r hr
      simpa [stateAt] using hs (t + 1) r (by simpa using hr)

lemma represents_fold (f : LogicalKey → LogicalKey) (logical stored : State)
    (h : Represents f logical stored) (qs : List Request) (hs : Safe f logical qs) :
    Represents f (qs.foldl (fun state q => step q state) logical)
      ((qs.map (mapRequest f)).foldl (fun state q => step q state) stored) := by
  induction qs generalizing logical stored with
  | nil => exact h
  | cons q qs ih =>
    exact ih (step q logical) (step (mapRequest f q) stored)
      (represents_step f logical stored h q hs.1) hs.2

end RebuildBound.NativeNormalizeLiveApiProof



namespace RebuildBound.NativeNormalizeLiveApiProof
open Model Model.Api Spec Spec.NativeNormalizeLiveApi Spec.NativeMatchProduction

lemma requests_map (f : LogicalKey → LogicalKey) {m} (choose : ApiAdaptive.Chooser m)
    (rows : List (Fin m → Nat)) (frame : ApiAdaptive.Frame) :
    ApiAdaptive.requests (mapRawChooser f choose) rows frame =
      (ApiAdaptive.requests choose rows frame).map (mapRequest f) := by
  rcases frame with ⟨batch, start, found, group⟩
  cases group <;>
    simp [ApiAdaptive.requests, PublicApi.Group.map, List.map_map, Function.comp_def,
      PublicApi.chosenLane, PublicApi.request, mapRawChooser, mapRequest] <;> intros <;> rfl

lemma groups_map (f : LogicalKey → LogicalKey) {m} (choose : ApiAdaptive.Chooser m)
    (rows : List (Fin m → Nat)) (frames : List ApiAdaptive.Frame) :
    (ApiAdaptive.requestGroups (mapRawChooser f choose) rows frames).flatMap PublicApi.Group.lanes =
      ((ApiAdaptive.requestGroups choose rows frames).flatMap PublicApi.Group.lanes).map (mapRequest f) := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
    simp only [ApiAdaptive.requestGroups, List.map_cons, List.flatMap_cons] at ih ⊢
    rw [requests_map, List.map_append, ih]
    congr 1
    cases ApiAdaptive.requests choose rows frame <;> rfl

lemma groups_rekey {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (f : LogicalKey → LogicalKey)
    (rows : List (Fin ctx.transcriptWidth → Nat)) :
    (ApiAdaptive.requestGroups (rekey ctx f).compiled rows (rekey ctx f).frames).flatMap PublicApi.Group.lanes =
      ((ApiAdaptive.requestGroups ctx.compiled rows ctx.frames).flatMap PublicApi.Group.lanes).map (mapRequest f) :=
  groups_map f ctx.compiled rows ctx.frames

lemma valid_rekey {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (f : LogicalKey → LogicalKey) (hv : ctx.Valid)
    (hinit : ((ctx.init.map (mapRec f)).map Rec.key).Nodup) : (rekey ctx f).Valid := by
  have hrec : ∀ r ∈ ctx.init.map (mapRec f), r.tomb = false := by
    intro r hr
    obtain ⟨r, hmem, rfl⟩ := List.mem_map.mp hr
    exact hv.1.2.2.1 r hmem
  refine ⟨⟨hinit, ?_, hrec, ?_⟩, hv.2.1, hv.2.2.1, ?_⟩
  · change (ctx.init.map (mapRec f)).length ≤ ctx.geo.keyCapacity
    simpa only [List.length_map] using hv.1.2.1
  · intro hempty
    change ctx.init.map (mapRec f) = []
    rw [hv.1.2.2.2 hempty]
    rfl
  · intro t
    have hi := represents_supportImage f _ _ (represents_init f ctx.codec ctx.init hv.1.1 hinit)
    have hs := ApiCapacityProof.records_support ctx.codec (ctx.init.map (mapRec f)) hinit hrec
    have hc := liveCapacity f _ _ hi (ctx.init.map Rec.key) ((ctx.init.map (mapRec f)).map Rec.key)
      hs _ ctx.geo.keyCapacity (hv.2.2.2 t)
    change ApiCapacity.LiveCapacity ctx.geo.keyCapacity (stateOf ctx.codec (ctx.init.map (mapRec f)))
      ((ctx.init.map (mapRec f)).map Rec.key)
      ((ApiAdaptive.requestGroups (rekey ctx f).compiled
        (Adaptive.rowsOf (ApiLegal.erase t) ctx.accesses) (rekey ctx f).frames).flatMap PublicApi.Group.lanes)
    exact (groups_rekey ctx f (Adaptive.rowsOf (ApiLegal.erase t) ctx.accesses)).symm ▸ hc

lemma check_rekey {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (f : LogicalKey → LogicalKey) :
    NativeMatchPublic.check (rekey ctx f) = NativeMatchPublic.check ctx := rfl

end RebuildBound.NativeNormalizeLiveApiProof


namespace RebuildBound
open Model Model.Api Spec NativeNormalizeLiveApi NativeNormalizeLiveApiProof

theorem NativeNormalizeLiveCapacity : Spec.NativeNormalizeLiveCapacity_statement := by
  intro f logical stored h logicalKeys storedKeys hs requests capacity hc
  exact liveCapacity f logical stored h logicalKeys storedKeys hs requests capacity hc

theorem NativeNormalizeLiveReplies : Spec.NativeNormalizeLiveReplies_statement := by
  intro f logical stored h requests hs
  have hsafe := safe_of_prefix f logical requests hs
  refine ⟨repliesAgree f logical stored h requests hsafe, ?_⟩
  simpa only [stateAt, List.take_length, ← List.map_take] using
    represents_fold f logical stored h requests hsafe

theorem NativeNormalizeLiveContext : Spec.NativeNormalizeLiveContext_statement := by
  intro member initialized h ctx f hv hi
  exact ⟨valid_rekey ctx f hv hi, check_rekey ctx f⟩

end RebuildBound

namespace RebuildBound.NativeNormalizeLiveApiProof
open Model Model.Api Spec Spec.NativeNormalizeLiveApi Spec.NativeMatchProduction

lemma constructed_keys (c : Codec) (cfg : Config) (sh : Hierarchy.Shapes) (g : Online.OnlineGeom)
    (S : Online.Schedule) (init : List Rec) (groups : List (PublicApi.Group Request))
    (hv : ∀ group ∈ groups, ApiExecution.Valid group) :
    (ApiAdaptive.records (ApiExecution.run c cfg sh g S init groups).ops).map Rec.key =
      (groups.flatMap PublicApi.Group.lanes).map Request.key := by
  have hk := congrArg (List.map Prod.fst)
    (ApiExecutionProof.operations_keys c cfg sh g S init [] groups hv)
  simpa only [ApiAdaptive.records, ApiExecution.run, List.map_flatMap, List.map_map, Function.comp_def] using hk

/-- Constant-width encoding applies to every generated client record, not
only to keys that happened to occur on one successful execution. -/
lemma inputWidth_rekey {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (f : LogicalKey → LogicalKey) (width : Nat)
    (hw : ∀ key, (f key).length = width) : NativeRoutingActual.InputWidth (rekey ctx f).client width := by
  constructor
  · intro r hr
    obtain ⟨r, hmem, rfl⟩ := List.mem_map.mp hr
    exact hw r.key
  · intro before kind after hshape rows hrows lane hlane
    let cc := rekey ctx f
    let groups := ApiAdaptive.requestGroups cc.compiled rows cc.frames
    let records := ApiAdaptive.records (ApiExecution.run cc.codec cc.geo.cfg cc.geo.shapes cc.unit cc.schedule cc.init groups).ops
    have hv : ∀ group ∈ groups, ApiExecution.Valid group :=
      ((ApiAdaptiveFrames cc.batchWidth 64 cc.batches).2.2 cc.transcriptWidth cc.compiled rows).1
    have hk : records.map Rec.key = (groups.flatMap PublicApi.Group.lanes).map Request.key :=
      constructed_keys cc.codec cc.geo.cfg cc.geo.shapes cc.unit cc.schedule cc.init groups hv
    have hlen : records.length = Adaptive.slotCount (ApiAdaptive.shape cc.frames) := by
      have he := congrArg List.length hk
      simp only [List.length_map] at he
      exact he.trans (ApiAdaptiveCorrectnessProof.requests_length cc.compiled rows cc.frames)
    have hi : rows.length + lane < records.length := by
      rw [hlen]
      change rows.length + lane < Adaptive.slotCount cc.client.shape
      rw [hshape]
      simp only [Adaptive.slotCount, Adaptive.shapeWidths, List.map_append, List.map_cons,
        List.sum_append, List.sum_cons] at hrows ⊢
      omega
    have hm : records.getD (rows.length + lane) default ∈ records := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem _
    have hkey : (records.getD (rows.length + lane) default).key ∈
        (groups.flatMap PublicApi.Group.lanes).map Request.key :=
      hk ▸ List.mem_map_of_mem (f := Rec.key) hm
    obtain ⟨q, hq, hqkey⟩ := List.mem_map.mp hkey
    have hqs : groups.flatMap PublicApi.Group.lanes =
        ((ApiAdaptive.requestGroups ctx.compiled rows ctx.frames).flatMap PublicApi.Group.lanes).map (mapRequest f) :=
      groups_rekey ctx f rows
    rw [hqs] at hq
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp hq
    change (records.getD (rows.length + lane) default).key.length = width
    rw [← hqkey]
    exact hw original.key

end RebuildBound.NativeNormalizeLiveApiProof
