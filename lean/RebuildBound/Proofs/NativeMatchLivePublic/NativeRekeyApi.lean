import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyLocal
import RebuildBound.Proofs.NativeMatchApi
import RebuildBound.Proofs.KeyRelabel.Core

namespace RebuildBound.NativeRekeyApi
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchDispatch Spec.NativeMatchApi NativeRekeyLocal

 def requester (f : LogicalKey → LogicalKey) (st : Requester.State) : Requester.State :=
  ⟨st.frozen.map (bucket f), bucket f st.current⟩
 def output (f : LogicalKey → LogicalKey) (out : Output) : Output :=
  ⟨out.main.map (bucket f), bucket f out.tier⟩
 def result (f : LogicalKey → LogicalKey) (r : Probe.Result) : Probe.Result :=
  ⟨r.found.map (rec f), r.addresses⟩
 def request (f : LogicalKey → LogicalKey) (q : Api.Request) : Api.Request :=
  ⟨f q.key, q.action⟩

 theorem value_map (f : LogicalKey → LogicalKey) (c : Api.Codec) (r : Option Rec) :
    Api.value c (r.map (rec f)) = Api.value c r := by cases r <;> rfl

 theorem postRecord_map (f : LogicalKey → LogicalKey) (c : Api.Codec) (q : Api.Request)
    (r : Option Rec) :
    Api.postRecord c (request f q) (r.map (rec f)) = rec f (Api.postRecord c q r) := by
  cases r <;> rfl

 theorem first_map (f : LogicalKey → LogicalKey) (s s' : LogicalKey → Stored)
    (h : ∀ key, s' (f key) = s key) (key : LogicalKey) (rs : List Rec) :
    storedFirst s' (f key) (rs.map (rec f)) = (storedFirst s key rs).map (rec f) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [storedFirst, rec, h, List.find?_cons]

 theorem latest_map (f : LogicalKey → LogicalKey) (s s' : LogicalKey → Stored)
    (h : ∀ key, s' (f key) = s key) (key : LogicalKey) (rs : List Rec) :
    storedLatest s' (f key) (rs.map (rec f)) = (storedLatest s key rs).map (rec f) := by
  simpa only [storedLatest, storedFirst, ← List.map_reverse] using first_map f s s' h key rs.reverse

 theorem clear_map (f : LogicalKey → LogicalKey) (s s' : LogicalKey → Stored)
    (h : ∀ key, s' (f key) = s key) (b : Model.Bucket) (keys : List LogicalKey) :
    storedClear s' (bucket f b) (keys.map f) = bucket f (storedClear s b keys) := by
  unfold storedClear bucket
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro lane _
  cases lane with
  | none => rfl
  | some r =>
    simp only [Option.map_some, Option.filter_some, rec, List.any_map, Function.comp_def, h]
    split <;> rfl

 theorem dense_selected_congr (a b : NativeMatchDense.Bucket) (live : NativeMatchDense.Live)
    (key : NativeMatchDense.Key) (h : ∀ i, live i = true → a i = b i) :
    NativeMatchDense.selected a live key = NativeMatchDense.selected b live key := by
  have hp (column : Bool) (subset : Fin 8) :
      NativeMatchDense.partners a live column subset = NativeMatchDense.partners b live column subset := by
    apply List.map_congr_left
    intro i hi
    exact h _ (List.mem_filter.mp hi).2
  have hm (column : Bool) (subset : Fin 8) :
      NativeMatchDense.subsetMatch a live key column subset = NativeMatchDense.subsetMatch b live key column subset := by
    apply Bool.eq_iff_iff.mpr
    rw [NativeMatchDenseProof.subsetMatch_iff, NativeMatchDenseProof.subsetMatch_iff, hp]
  unfold NativeMatchDense.selected
  congr 1 <;> apply congrArg NativeMatchDense.lastIndex <;> funext i <;> exact hm _ i

 theorem dense_hit_congr (a b : NativeMatchDense.Bucket) (live : NativeMatchDense.Live)
    (key : NativeMatchDense.Key) (active : Bool) (h : ∀ i, live i = true → a i = b i) :
    NativeMatchDense.hit a live key active = NativeMatchDense.hit b live key active := by
  have hp (column : Bool) (subset : Fin 8) :
      NativeMatchDense.partners a live column subset = NativeMatchDense.partners b live column subset := by
    apply List.map_congr_left
    intro i hi
    exact h _ (List.mem_filter.mp hi).2
  have hm : NativeMatchDense.subsetMatch a live key false = NativeMatchDense.subsetMatch b live key false := by
    funext subset
    apply Bool.eq_iff_iff.mpr
    rw [NativeMatchDenseProof.subsetMatch_iff, NativeMatchDenseProof.subsetMatch_iff, hp]
  unfold NativeMatchDense.hit
  rw [dense_selected_congr a b live key h, hm]
  dsimp only
  by_cases hl : live (NativeMatchDense.selected b live key) = true
  · rw [h _ hl]
  · simp [hl]

 theorem page_live {f : LogicalKey → LogicalKey} {p q : Page} (hp : PageRel f p q) : q.live = p.live := by
  funext i
  exact congrArg (fun mask : Mask => mask.getLsbD i.val) hp.mask

 theorem page_keys {f : LogicalKey → LogicalKey} {p q : Page} (hp : PageRel f p q)
    (s s' : LogicalKey → Stored) (hs : ∀ key, s' (f key) = s key) :
    ∀ i, p.live i = true → s' (q.keys i) = s (p.keys i) := by
  intro i hi
  change s' (q.1 i.val).key = s (p.1 i.val).key
  rw [hp.payload i hi]
  exact hs _

 theorem dense_mask_rel {f : LogicalKey → LogicalKey} {p q : Page} (hp : PageRel f p q)
    (s s' : LogicalKey → Stored) (hs : ∀ key, s' (f key) = s key) (key : LogicalKey) (active : Bool) :
    denseMask s' q (f key) active = denseMask s p key active := by
  have hk := page_keys hp s s' hs
  unfold denseMask denseHit denseSelected
  rw [page_live hp, hs key, dense_hit_congr (s' ∘ q.keys) (s ∘ p.keys) p.live (s key) active hk,
    dense_selected_congr (s' ∘ q.keys) (s ∘ p.keys) p.live (s key) hk]

 theorem dense_record_rel {f : LogicalKey → LogicalKey} {p q : Page} (hp : PageRel f p q)
    (s s' : LogicalKey → Stored) (hs : ∀ key, s' (f key) = s key) (key : LogicalKey) (active : Bool) :
    denseRecord s' q (f key) active = (denseRecord s p key active).map (rec f) := by
  have hk := page_keys hp s s' hs
  unfold denseRecord denseHit denseSelected
  rw [page_live hp, hs key, dense_hit_congr (s' ∘ q.keys) (s ∘ p.keys) p.live (s key) active hk,
    dense_selected_congr (s' ∘ q.keys) (s ∘ p.keys) p.live (s key) hk]
  by_cases hh : NativeMatchDense.hit (s ∘ p.keys) p.live (s key) active = true
  · have hl := (NativeMatchDenseProof.hit_sound _ _ _ _ hh).2.1
    simp only [hh, ↓reduceIte, Option.map_some, hp.payload _ hl]
  · simp [hh]

 theorem exact_mask_rel {f : LogicalKey → LogicalKey} {p q : Page} (hp : PageRel f p q)
    (s s' : LogicalKey → Stored) (hs : ∀ key, s' (f key) = s key) (key : LogicalKey) :
    exactPageMask s' q (f key) = exactPageMask s p key := by
  unfold exactPageMask
  congr 1
  funext i
  rw [page_live hp, hs key]
  by_cases hl : p.live i = true
  · rw [page_keys hp s s' hs i hl]
  · simp [hl]

 theorem page_mask_rel {f : LogicalKey → LogicalKey} {p q : Page} (hp : PageRel f p q)
    (s s' : LogicalKey → Stored) (hs : ∀ key, s' (f key) = s key) (key : LogicalKey) (cross : Bool) :
    pageMask cross s' q (f key) = pageMask cross s p key := by
  cases cross
  · exact exact_mask_rel hp s s' hs key
  · exact dense_mask_rel hp s s' hs key true

 theorem page_record_rel {f : LogicalKey → LogicalKey} {p q : Page} (hp : PageRel f p q)
    (s s' : LogicalKey → Stored) (hs : ∀ key, s' (f key) = s key) (key : LogicalKey) (cross : Bool) :
    pageRecord cross s' q (f key) = (pageRecord cross s p key).map (rec f) := by
  cases cross
  · change storedFirst s' (f key) q.bucket.recs = (storedFirst s key p.bucket.recs).map (rec f)
    rw [rel_bucket hp, bucket_recs]
    exact first_map f s s' hs key _
  · exact dense_record_rel hp s s' hs key true



 theorem orElse_map (f : LogicalKey → LogicalKey) (a b : Option Rec) :
    (a.map (rec f)).orElse (fun _ => b.map (rec f)) =
      (a.orElse (fun _ => b)).map (rec f) := by cases a <;> rfl

 theorem zipIdx_rel {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (n : Nat) :
    List.Forall₂ (fun a b => R a.1 b.1 ∧ a.2=b.2) (xs.zipIdx n) (ys.zipIdx n) := by
  induction h generalizing n with
  | nil => exact .nil
  | cons hab htail ih =>
    simpa only [List.zipIdx_cons] using List.Forall₂.cons ⟨hab, rfl⟩ (ih (n+1))

 theorem fold_map_rel {α β γ : Type} {R : α → β → Prop}
    (f : γ → γ) (a : γ → α → γ) (b : γ → β → γ)
    (hab : ∀ x y, R x y → ∀ z, b (f z) y = f (a z x))
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) (z : γ) :
    ys.foldl b (f z) = f (xs.foldl a z) := by
  induction h generalizing z with
  | nil => rfl
  | cons hxy htail ih => simp only [List.foldl_cons, hab _ _ hxy, ih]

 theorem scan_pages_rel {f : LogicalKey → LogicalKey} {ps qs : List Page}
    (hp : List.Forall₂ (PageRel f) ps qs) (mode : Nat → Mode)
    (s s' : LogicalKey → Stored) (hs : ∀ key, s' (f key) = s key) (key : LogicalKey) :
    scanPages mode s' qs (f key) = (scanPages mode s ps key).map (rec f) := by
  unfold scanPages
  apply fold_map_rel (Option.map (rec f)) _ _ ?_ (zipIdx_rel hp 0) none
  intro p q hp found
  rw [page_record_rel hp.1 s s' hs key, ←hp.2, orElse_map]

 theorem bucket_pages_rel (f : LogicalKey → LogicalKey) (n : Nat) (b : Model.Bucket) :
    List.Forall₂ (PageRel f) (bucketPages n b) (bucketPages n (bucket f b)) := by
  induction n generalizing b with
  | zero => exact .nil
  | succ n ih =>
    simp only [bucketPages]
    apply List.Forall₂.cons (rel_ofBucket f b)
    simpa only [bucket, List.map_drop] using ih (b.drop 64)

 theorem all_pages_rel (f : LogicalKey → LogicalKey) (b : Model.Bucket) :
    List.Forall₂ (PageRel f) (allBucketPages b) (allBucketPages (bucket f b)) := by
  simpa only [allBucketPages, bucket, List.length_map] using bucket_pages_rel f ((b.length+63)/64) b

 theorem scan_all_pages (f : LogicalKey → LogicalKey) (b : Model.Bucket) (mode : Nat → Mode)
    (s s' : LogicalKey → Stored) (hs : ∀ key, s' (f key) = s key) (key : LogicalKey) :
    scanPages mode s' (allBucketPages (bucket f b)) (f key) =
      (scanPages mode s (allBucketPages b) key).map (rec f) :=
  scan_pages_rel (all_pages_rel f b) mode s s' hs key

 theorem scan_requester (f : LogicalKey → LogicalKey) (st : Requester.State)
    (policy : Policy) (operation consumed : Nat)
    (s s' : LogicalKey → Stored) (hs : ∀ key, s' (f key) = s key) (key : LogicalKey) :
    scanRequester policy operation s' (requester f st) consumed (f key) =
      (scanRequester policy operation s st consumed key).map (rec f) := by
  have hb : List.Forall₂ (fun b c => c=bucket f b) (st.frozen.drop consumed)
      ((st.frozen.drop consumed).map (bucket f)) := by
    induction (st.frozen.drop consumed) with
    | nil => exact .nil
    | cons b bs ih => exact .cons rfl ih
  have ho := fold_map_rel (Option.map (rec f))
    (fun found (ui : Model.Bucket × Nat) =>
      (scanPages (policy operation (.unit ui.2)) s (allBucketPages ui.1) key).orElse (fun _=>found))
    (fun found (ui : Model.Bucket × Nat) =>
      (scanPages (policy operation (.unit ui.2)) s' (allBucketPages ui.1) (f key)).orElse (fun _=>found))
    (by
      intro a b h found
      rw [h.1, ←h.2, scan_all_pages f _ _ s s' hs key, orElse_map])
    (zipIdx_rel hb consumed) none
  simp only [scanRequester, requester, List.length_map, ←List.map_drop,
    scan_all_pages f _ _ s s' hs key]
  simp only [Option.map_none] at ho
  rw [ho]
  exact orElse_map f _ _

 theorem scan_output (f : LogicalKey → LogicalKey) (out : Output)
    (policy : Policy) (operation : Nat) (coordinate : Nat × Nat) (address : Nat)
    (s s' : LogicalKey → Stored) (hs : ∀ key, s' (f key) = s key) (key : LogicalKey) :
    scanOutput policy operation s' coordinate (output f out) (f key) address =
      (scanOutput policy operation s coordinate out key address).map (rec f) := by
  have hg : (out.main.map (bucket f)).getD address [] = bucket f (out.main.getD address []) :=
    List.getD_map out.main [] (bucket f)
  simp only [scanOutput, output, hg, bucket_recs, first_map f s s' hs key,
    scan_all_pages f _ _ s s' hs key, orElse_map]



 theorem cascade_map (f : LogicalKey → LogicalKey)
    (scan scan' : Nat × Nat → Nat → Option Rec)
    (real : Nat × Nat → Nat) (dummy : Nat → Nat × Nat → Nat)
    (cs : List (Nat × Nat)) (hs : ∀ c ∈ cs, ∀ a, scan' c a = (scan c a).map (rec f))
    (found : Option Rec) (offset : Nat) :
    Probe.cascadeWith scan' real dummy cs (found.map (rec f)) offset =
      result f (Probe.cascadeWith scan real dummy cs found offset) := by
  induction cs generalizing found offset with
  | nil => rfl
  | cons c cs ih =>
    have ht := ih (fun d hd => hs d (List.mem_cons_of_mem c hd))
    simp only [Probe.cascadeWith, Option.isSome_map, hs c (List.mem_cons_self), orElse_map, ht, result]

 theorem require_tables_map (f : LogicalKey → LogicalKey)
    (lookup lookup' : Nat × Nat → Option Output) (cs : List (Nat × Nat))
    (h : ∀ c ∈ cs, lookup' c = (lookup c).map (output f)) :
    requireTables lookup' cs = requireTables lookup cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have ht := ih (fun d hd => h d (List.mem_cons_of_mem c hd))
    simp only [requireTables, h c List.mem_cons_self]
    cases lookup c <;> simp_all

 theorem query_map (f : LogicalKey → LogicalKey) (policy : Policy)
    (s s' : LogicalKey → Stored) (hs : ∀ key, s' (f key) = s key)
    (cfg : Model.Config) (sh : Model.Hierarchy.Shapes) (g : Model.Online.OnlineGeom)
    (schedule : Model.Online.Schedule) (init : List Rec) (unsh unsh' : Rec → Bool)
    (words words' : Model.Hierarchy.Words)
    (hw : ∀ l v key, words' l v (f key) = words l v key)
    (dummy : Nat → Nat → Nat) (operation start lane : Nat)
    (st : Requester.State) (earlier : List Rec) (key : LogicalKey)
    (ht : ∀ c ∈ (schedule start).tables,
      NativeMatchHierarchy.nativeTable s' cfg sh
        (traceFromState g (init.map (rec f)) unsh' (requester f st)) words' c.1 c.2 =
      (NativeMatchHierarchy.nativeTable s cfg sh
        (traceFromState g init unsh st) words c.1 c.2).map (output f)) :
    query policy s' cfg sh g schedule (init.map (rec f)) unsh' words' dummy operation start lane
      (requester f st) (earlier.map (rec f)) (f key) =
      (query policy s cfg sh g schedule init unsh words dummy operation start lane st earlier key).map (result f) := by
  let lookup := fun c : Nat × Nat => NativeMatchHierarchy.nativeTable s cfg sh
      (traceFromState g init unsh st) words c.1 c.2
  let lookup' := fun c : Nat × Nat => NativeMatchHierarchy.nativeTable s' cfg sh
      (traceFromState g (init.map (rec f)) unsh' (requester f st)) words' c.1 c.2
  have hr := require_tables_map f lookup lookup' (schedule start).tables ht
  have hg (c : Nat × Nat) (hc : c ∈ (schedule start).tables) : (lookup' c).getD Model.DirectJob.emptyOutput =
      output f ((lookup c).getD Model.DirectJob.emptyOutput) := by
    have htc : lookup' c = (lookup c).map (output f) := ht c hc
    rw [htc]
    cases lookup c <;> rfl
  have hscan (c : Nat × Nat) (hc : c ∈ (schedule start).tables) (address : Nat) :
      scanOutput policy operation s' c ((lookup' c).getD Model.DirectJob.emptyOutput) (f key) address =
      (scanOutput policy operation s c ((lookup c).getD Model.DirectJob.emptyOutput) key address).map (rec f) := by
    rw [hg c hc]
    exact scan_output f _ policy operation c address s s' hs key
  unfold query
  change (do requireTables lookup' (schedule start).tables; pure _) =
    (do requireTables lookup (schedule start).tables; pure _).map (result f)
  rw [hr]
  cases he : requireTables lookup (schedule start).tables with
  | error e => rfl
  | ok u =>
    cases u
    change Except.ok _ = Except.ok _
    rw [latest_map f s s' hs key, scan_requester f st policy operation _ s s' hs key, orElse_map]
    have hw' (c : Nat × Nat) : Model.Hierarchy.jobWord cfg words' c.1 c.2 (f key) =
        Model.Hierarchy.jobWord cfg words c.1 c.2 key := hw _ _ key
    simp only [hw']
    congr 1
    exact cascade_map f _ _ _ _ _ hscan _ _



 theorem deferred_mask_rel {f : LogicalKey → LogicalKey} {p q : Page} (hp : PageRel f p q)
    (s s' : LogicalKey → Stored) (hs : ∀ key, s' (f key) = s key)
    (keys : List LogicalKey) (cross : Bool) :
    deferredMask cross s' q (keys.map f) = deferredMask cross s p keys := by
  unfold deferredMask
  rw [List.foldl_map]
  have hf : (fun mask key => mask ||| pageMask cross s' q (f key)) =
      (fun (mask : Mask) key => mask ||| pageMask cross s p key) := by
    funext mask key
    rw [page_mask_rel hp s s' hs key]
  rw [hf]

 theorem deferred_clear_rel {f : LogicalKey → LogicalKey} {p q : Page} (hp : PageRel f p q)
    (s s' : LogicalKey → Stored) (hs : ∀ key, s' (f key) = s key)
    (keys : List LogicalKey) (cross : Bool) :
    PageRel f (deferredClear cross s p keys) (deferredClear cross s' q (keys.map f)) := by
  constructor
  · simp only [deferredClear, deferred_mask_rel hp s s' hs keys, hp.mask]
  · intro i hi
    change (p.2 &&& ~~~deferredMask cross s p keys).getLsbD i.val=true at hi
    rw [BitVec.getLsbD_and] at hi
    exact hp.payload i (Bool.and_eq_true_iff.mp hi).1

 theorem flat_map_rel {α β γ δ : Type} {R : α → β → Prop}
    (f : γ → δ) (a : α → List γ) (b : β → List δ)
    (hab : ∀ x y, R x y → b y = (a x).map f)
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) :
    ys.flatMap b = (xs.flatMap a).map f := by
  induction h with
  | nil => rfl
  | cons hxy htail ih => simp only [List.flatMap_cons, hab _ _ hxy, ih, List.map_append]

 theorem clear_unit_map (f : LogicalKey → LogicalKey) (b : Model.Bucket) (mode : Nat → Mode)
    (s s' : LogicalKey → Stored) (hs : ∀ key, s' (f key) = s key) (keys : List LogicalKey) :
    clearUnit mode s' (bucket f b) (keys.map f) = bucket f (clearUnit mode s b keys) := by
  have hh := flat_map_rel (Option.map (rec f))
    (fun (pi : Page × Nat) => (deferredClear (mode pi.2).cross s pi.1 keys).bucket)
    (fun (pi : Page × Nat) => (deferredClear (mode pi.2).cross s' pi.1 (keys.map f)).bucket)
    (by
      intro p q hp
      rw [←hp.2]
      exact rel_bucket (deferred_clear_rel hp.1 s s' hs keys _))
    (zipIdx_rel (all_pages_rel f b) 0)
  simpa only [clearUnit, List.flatMap_map, Function.comp_def, bucket, List.length_map,
    ←List.map_take] using congrArg (List.take b.length) hh

 theorem insert_map (f : LogicalKey → LogicalKey) (entries : Nat) (st : Requester.State)
    (lane : Option Rec) :
    Requester.insert entries (requester f st) (lane.map (rec f)) =
      requester f (Requester.insert entries st lane) := by
  unfold Requester.insert requester bucket
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
  split <;> simp only [List.map_append, List.map_cons, List.map_nil]

 theorem scalar_step_map (f : LogicalKey → LogicalKey) (entries : Nat) (st : Requester.State)
    (s s' : LogicalKey → Stored) (hs : ∀ key, s' (f key) = s key) (r : Rec) (real : Bool) :
    scalarRequesterStep s' entries (requester f st) (rec f r) real =
      requester f (scalarRequesterStep s entries st r real) := by
  unfold scalarRequesterStep
  have hc := clear_map f s s' hs st.current [r.key]
  simp only [List.map_cons, List.map_nil] at hc
  change Requester.insert entries ⟨_, storedClear s' (bucket f st.current) [f r.key]⟩ _ = _
  rw [hc]
  have hi := insert_map f entries ⟨st.frozen, storedClear s st.current [r.key]⟩
    (if real then some r else none)
  cases real <;> exact hi

 theorem superseded_map (f : LogicalKey → LogicalKey) (s s' : LogicalKey → Stored)
    (hs : ∀ key, s' (f key) = s key) (rs : List Rec) (i : Nat) (r : Rec) :
    storedSuperseded s' (rs.map (rec f)) i (rec f r) = storedSuperseded s rs i r := by
  simp only [storedSuperseded, ←List.map_drop, List.any_map, Function.comp_def, rec, hs]

 def requesterOp (f : LogicalKey → LogicalKey) : Requester.Op → Requester.Op
  | .access r real => .access (rec f r) real
  | .batch rs => .batch (rs.map (rec f))

 theorem requester_step_map (f : LogicalKey → LogicalKey) (mode : Nat → Mode)
    (s s' : LogicalKey → Stored) (hs : ∀ key, s' (f key) = s key)
    (entries : Nat) (st : Requester.State) (op : Requester.Op) :
    requesterStep mode s' entries (requester f st) (requesterOp f op) =
      requester f (requesterStep mode s entries st op) := by
  cases op with
  | access r real => exact scalar_step_map f entries st s s' hs r real
  | batch rs =>
    have hrel : List.Forall₂ (fun r r' => r'=rec f r) rs (rs.map (rec f)) := by
      induction rs with
      | nil => exact .nil
      | cons r rs ih => exact .cons rfl ih
    have hf := fold_map_rel (requester f)
      (fun st (ri : Rec × Nat) => Requester.insert entries st
        (if storedSuperseded s rs ri.2 ri.1 then none else some ri.1))
      (fun st (ri : Rec × Nat) => Requester.insert entries st
        (if storedSuperseded s' (rs.map (rec f)) ri.2 ri.1 then none else some ri.1))
      (by
        intro a b hab state
        rw [hab.1, ←hab.2, superseded_map f s s' hs]
        split
        · exact insert_map f entries state none
        · exact insert_map f entries state (some a.1))
      (zipIdx_rel hrel 0) ⟨st.frozen, clearUnit mode s st.current (rs.map Rec.key)⟩
    have hk : (rs.map (rec f)).map Rec.key = (rs.map Rec.key).map f := by
      simp only [List.map_map]; rfl
    simpa only [requesterStep, requesterOp, requester, hk, clear_unit_map f _ _ s s' hs] using hf



 def chunkResult (f : LogicalKey → LogicalKey) (r : List Rec × List Probe.Result) :=
  (r.1.map (rec f), r.2.map (result f))

 def op (f : LogicalKey → LogicalKey) : Model.OnlineBatch.Op → Model.OnlineBatch.Op
  | .probe r => .probe (rec f r)
  | .blind r => .blind (rec f r)
  | .batch rs => .batch (rs.map (rec f))

 def state (f : LogicalKey → LogicalKey) {m : Nat} (st : State m) : State m :=
  ⟨st.ops.map (op f), st.requests.map (request f), st.selected.map (result f), st.rows,
    requester f st.requester⟩

 def operationResult (f : LogicalKey → LogicalKey) (r : Model.OnlineBatch.Op × List Probe.Result) :=
  (op f r.1, r.2.map (result f))

 def chooseMap (f : LogicalKey → LogicalKey) {m} (choose : ApiAdaptive.Chooser m) : ApiAdaptive.Chooser m :=
  fun batch rows lane => (f (choose batch rows lane).1, (choose batch rows lane).2)

 theorem chosen_requests_map (f : LogicalKey → LogicalKey) {m} (choose : ApiAdaptive.Chooser m)
    (rows : List (Fin m → Nat)) (frame : ApiAdaptive.Frame) :
    ApiAdaptive.requests (chooseMap f choose) rows frame =
      (ApiAdaptive.requests choose rows frame).map (request f) := by
  rcases frame with ⟨batch, start, found, group⟩
  cases group <;>
    simp [ApiAdaptive.requests, PublicApi.Group.map, List.map_map, Function.comp_def,
      PublicApi.chosenLane, PublicApi.request, chooseMap, request] <;> intros <;> rfl

 section ApiLifts
 variable (f : LogicalKey → LogicalKey) (policy : Policy)
    (s s' : LogicalKey → Stored) (hs : ∀ key, s' (f key) = s key)
    (codec : Api.Codec) (cfg : Model.Config) (sh : Model.Hierarchy.Shapes) (g : Model.Online.OnlineGeom)
    (schedule : Model.Online.Schedule) (init : List Rec)
    (words words' : Model.Hierarchy.Words)
    (hw : ∀ l v key, words' l v (f key) = words l v key)
    (dummy : Nat → Nat → Nat)

 def TablesMap (st : Requester.State) (start : Nat) : Prop := ∀ c ∈ (schedule start).tables,
      NativeMatchHierarchy.nativeTable s' cfg sh
        (traceFromState g (init.map (rec f)) (fun r=>codec.flag r.val) (requester f st)) words' c.1 c.2 =
      (NativeMatchHierarchy.nativeTable s cfg sh
        (traceFromState g init (fun r=>codec.flag r.val) st) words c.1 c.2).map (output f)

 include hs hw in
 theorem chunk_map (operation start : Nat) (st : Requester.State)
    (ht : TablesMap f s s' codec cfg sh g schedule init words words' st start)
    (earlier : List Rec) (qs : List Api.Request) :
    chunk policy s' codec cfg sh g schedule (init.map (rec f)) words' dummy operation start
      (requester f st) (earlier.map (rec f)) (qs.map (request f)) =
      (chunk policy s codec cfg sh g schedule init words dummy operation start st earlier qs).map (chunkResult f) := by
  induction qs generalizing earlier with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.map_cons, chunk, request, List.length_map]
    rw [query_map f policy s s' hs cfg sh g schedule init _ _ words words' hw dummy operation start
      earlier.length st earlier q.key ht]
    cases hq : query policy s cfg sh g schedule init (fun r=>codec.flag r.val) words dummy operation start
      earlier.length st earlier q.key with
    | error e => rfl
    | ok selected =>
      change (do
        let rest ← chunk policy s' codec cfg sh g schedule (init.map (rec f)) words' dummy operation start
          (requester f st) (earlier.map (rec f) ++ [Api.postRecord codec (request f q) (result f selected).found])
          (qs.map (request f))
        pure (Api.postRecord codec (request f q) (result f selected).found :: rest.1,
          result f selected :: rest.2)) = _
      have hp := postRecord_map f codec q selected.found
      change Api.postRecord codec (request f q) (result f selected).found = _ at hp
      rw [hp, ←List.map_singleton, ←List.map_append, ih]
      dsimp only [Bind.bind, Except.bind]
      cases chunk policy s codec cfg sh g schedule init words dummy operation start st
        (earlier ++ [Api.postRecord codec q selected.found]) qs <;> rfl

 include hs hw in
 theorem operation_map {m : Nat} (st : State m)
    (ht : TablesMap f s s' codec cfg sh g schedule init words words' st.requester st.rows.length)
    (group : PublicApi.Group Api.Request) :
    operation policy s' codec cfg sh g schedule (init.map (rec f)) words' dummy (state f st)
      (group.map (request f)) =
      (operation policy s codec cfg sh g schedule init words dummy st group).map (operationResult f) := by
  cases group with
  | blind q => rfl
  | chunk qs =>
    have hc := chunk_map f policy s s' hs codec cfg sh g schedule init words words' hw dummy
      st.ops.length st.rows.length st.requester ht [] qs
    simp only [List.map_nil] at hc
    simp only [operation, PublicApi.Group.map, state, List.length_map]
    rw [hc]
    cases chunk policy s codec cfg sh g schedule init words dummy st.ops.length st.rows.length
      st.requester [] qs <;> rfl

 theorem op_requester (o : Model.OnlineBatch.Op) : (op f o).requester = requesterOp f o.requester := by
    cases o <;> rfl

 include hs hw in
 theorem issue_frame_map {m : Nat} (choose : ApiAdaptive.Chooser m) (st : State m)
    (ht : TablesMap f s s' codec cfg sh g schedule init words words' st.requester st.rows.length)
    (frame : ApiAdaptive.Frame) :
    issueFrame policy s' codec cfg sh g schedule (init.map (rec f)) words' dummy (chooseMap f choose)
      (state f st) frame =
      (issueFrame policy s codec cfg sh g schedule init words dummy choose st frame).map (state f) := by
  unfold issueFrame
  simp only [state, chosen_requests_map]
  have hop := operation_map f policy s s' hs codec cfg sh g schedule init words words' hw dummy st ht
    (ApiAdaptive.requests choose st.rows frame)
  simp only [state] at hop
  rw [hop]
  cases ho : operation policy s codec cfg sh g schedule init words dummy st
    (ApiAdaptive.requests choose st.rows frame) with
  | error e => rfl
  | ok r =>
    change Except.ok _ = Except.ok _
    have hreq := requester_step_map f
      (policy st.ops.length (.unit st.requester.frozen.length)) s s' hs
      g.unitEntries st.requester r.1.requester
    simp only [operationResult, op_requester, requester, List.length_map] at hreq ⊢
    rw [hreq]
    congr 1
    have hlanes : ((ApiAdaptive.requests choose st.rows frame).map (request f)).lanes =
        (ApiAdaptive.requests choose st.rows frame).lanes.map (request f) := by
      cases ApiAdaptive.requests choose st.rows frame <;> rfl
    simp only [state, List.map_append, List.map_cons, List.map_nil, hlanes,
      List.map_map, Function.comp_def, result]
    rfl


 include hs hw in
 theorem execute_map {m : Nat} (choose : ApiAdaptive.Chooser m)
    (Inv : State m → Prop)
    (ht : ∀ st, Inv st → TablesMap f s s' codec cfg sh g schedule init words words' st.requester st.rows.length)
    (hstep : ∀ st frame next, Inv st →
      issueFrame policy s codec cfg sh g schedule init words dummy choose st frame = .ok next → Inv next)
    (st : State m) (hinv : Inv st) (frames : List ApiAdaptive.Frame) :
    execute policy s' codec cfg sh g schedule (init.map (rec f)) words' dummy (chooseMap f choose)
      (state f st) frames =
      (execute policy s codec cfg sh g schedule init words dummy choose st frames).map (state f) := by
  induction frames generalizing st with
  | nil => rfl
  | cons frame frames ih =>
    rw [execute, execute, issue_frame_map f policy s s' hs codec cfg sh g schedule init words words' hw
      dummy choose st (ht st hinv)]
    cases hn : issueFrame policy s codec cfg sh g schedule init words dummy choose st frame with
    | error e => rfl
    | ok next =>
      change execute policy s' codec cfg sh g schedule (init.map (rec f)) words' dummy
        (chooseMap f choose) (state f next) frames =
        (execute policy s codec cfg sh g schedule init words dummy choose next frames).map (state f)
      exact ih next (hstep st frame next hinv hn)

 include hs hw in
 theorem run_map {m : Nat} (choose : ApiAdaptive.Chooser m)
    (Inv : State m → Prop) (hempty : Inv empty)
    (ht : ∀ st, Inv st → TablesMap f s s' codec cfg sh g schedule init words words' st.requester st.rows.length)
    (hstep : ∀ st frame next, Inv st →
      issueFrame policy s codec cfg sh g schedule init words dummy choose st frame = .ok next → Inv next)
    (frames : List ApiAdaptive.Frame) :
    run policy s' codec cfg sh g schedule (init.map (rec f)) words' dummy (chooseMap f choose) frames =
      (run policy s codec cfg sh g schedule init words dummy choose frames).map (state f) :=
    execute_map f policy s s' hs codec cfg sh g schedule init words words' hw dummy choose Inv ht hstep
      empty hempty frames


 include hs hw in
 theorem execute_map_indexed {m : Nat} (choose : ApiAdaptive.Chooser m)
    (Inv : List ApiAdaptive.Frame → State m → Prop)
    (ht : ∀ st frame rest, Inv (frame::rest) st →
      TablesMap f s s' codec cfg sh g schedule init words words' st.requester st.rows.length)
    (hstep : ∀ st frame rest next, Inv (frame::rest) st →
      issueFrame policy s codec cfg sh g schedule init words dummy choose st frame = .ok next → Inv rest next)
    (st : State m) (frames : List ApiAdaptive.Frame) (hinv : Inv frames st) :
    execute policy s' codec cfg sh g schedule (init.map (rec f)) words' dummy (chooseMap f choose)
      (state f st) frames =
      (execute policy s codec cfg sh g schedule init words dummy choose st frames).map (state f) := by
  induction frames generalizing st with
  | nil => rfl
  | cons frame frames ih =>
    rw [execute, execute, issue_frame_map f policy s s' hs codec cfg sh g schedule init words words' hw
      dummy choose st (ht st frame frames hinv)]
    cases hn : issueFrame policy s codec cfg sh g schedule init words dummy choose st frame with
    | error e => rfl
    | ok next =>
      change execute policy s' codec cfg sh g schedule (init.map (rec f)) words' dummy
        (chooseMap f choose) (state f next) frames =
        (execute policy s codec cfg sh g schedule init words dummy choose next frames).map (state f)
      exact ih next (hstep st frame frames next hinv hn)

 end ApiLifts
end RebuildBound.NativeRekeyApi
