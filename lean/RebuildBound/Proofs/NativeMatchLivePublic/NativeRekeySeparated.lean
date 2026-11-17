import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyDrain
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyRouting
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyTop
import RebuildBound.Proofs.NativeMatchJobs

namespace RebuildBound.NativeRekeySeparated
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeMatchJobTrace NativeRekeyLocal NativeRekeyFinish
open NativeRekeyRouting (Word word sInputs sRoute sRouteWith_relabel sLeaves_relabel)

theorem append_rel {α β : Type} {R : α → β → Prop} {as bs : List α} {cs ds : List β}
    (h : List.Forall₂ R as cs) (h' : List.Forall₂ R bs ds) : List.Forall₂ R (as++bs) (cs++ds) := by
  induction h with
  | nil => exact h'
  | cons hxy hrest ih => exact .cons hxy ih

theorem records_pages (f : LogicalKey → LogicalKey) (n : Nat) (rs : List Rec) :
    List.Forall₂ (PageRel f) (bucketPages n (rs.map some))
      (bucketPages n ((rs.map (rec f)).map some)) := by
  simpa only [bucket,List.map_map,Function.comp_def,Option.map_some] using
    NativeRekeyDrain.bucket_pages_rel f n (rs.map some)

theorem stash_pages (f : LogicalKey → LogicalKey) (n : Nat) (rs : List (List Rec)) :
    List.Forall₂ (PageRel f) (rs.flatMap (fun r => bucketPages n (r.map some)))
      ((rs.map (List.map (rec f))).flatMap (fun r => bucketPages n (r.map some))) := by
  induction rs with
  | nil => exact .nil
  | cons r rs ih => exact append_rel (records_pages f n r) ih

theorem raw_rel {f : LogicalKey → LogicalKey} {ps qs : List Page}
    (hp : List.Forall₂ (PageRel f) ps qs) (g : SepGeom) (route : SRoute) :
    List.Forall₂ (PageRel f) (rawPoolPages g route ps)
      (rawPoolPages g (sRoute f route) qs) := by
  have hm : NativeRekeyRouting.records f = List.map (rec f) := rfl
  by_cases h : 1 < g.r
  · simpa only [rawPoolPages,sRoute,hm,h,ite_true] using
      append_rel (append_rel (stash_pages f g.stashPages route.stash)
        (records_pages f g.stashPages route.radix)) hp
  · simpa only [rawPoolPages,sRoute,hm,h,ite_false,List.append_nil] using
      append_rel (stash_pages f g.stashPages route.stash) hp

theorem carry_rel (f : LogicalKey → LogicalKey) (inp : SInputs) :
    List.Forall₂ (PageRel f) (carryTierPages inp) (carryTierPages (sInputs f inp)) := by
  change List.Forall₂ (PageRel f) (inp.bTier.map Page.ofRecords)
    ((inp.bTier.map (List.map (rec f))).map Page.ofRecords)
  induction inp.bTier with
  | nil => exact .nil
  | cons r rs ih => exact .cons (rel_ofRecords f r) ih

theorem onePage_rel (f : LogicalKey → LogicalKey) (leaves : List (List Rec)) :
    List.Forall₂ (List.Forall₂ (PageRel f)) (onePageLeaves leaves)
      (onePageLeaves (leaves.map (List.map (rec f)))) := by
  induction leaves with
  | nil => exact .nil
  | cons rs rest ih => exact .cons (.cons (rel_ofRecords f rs) .nil) ih


theorem initial_rel {f : LogicalKey → LogicalKey} {ps qs : List Page}
    (hp : List.Forall₂ (PageRel f) ps qs) (s s' : LogicalKey → Stored)
    (hs : ∀ key,s' (f key)=s key) (g : SepGeom) (w w' : LogicalKey → Nat)
    (hw : ∀ key,w' (f key)=w key) (inp : SInputs) (ops : List (Nat × Nat)) :
    GhostRel f (separatedInitialNative s engineRule g w inp ops ps)
      (separatedInitialNative s' engineRule g w' (sInputs f inp) ops qs) := by
  let route := sRouteWith engineRule g w inp.aMain ops
  have hr : sRouteWith engineRule g w' (NativeRekeyRouting.buckets f inp.aMain) ops = sRoute f route :=
    sRouteWith_relabel f g ⟨w,w',hw⟩ inp.aMain ops
  have hl (rs : List Rec) : sLeaves g w' (rs.map (rec f)) =
      (sLeaves g w rs).map (List.map (rec f)) := sLeaves_relabel f g ⟨w,w',hw⟩ rs
  have hpool := rel_pool (carry_rel f inp) (raw_rel hp g route) s s' hs
  have hrecords := rel_pageRecords hpool
  constructor
  · simp only [separatedInitialNative,NativeRekeyRouting.sInputs_aMain]
    rw [hr,hrecords,hl]
    rfl
  · simp only [separatedInitialNative,NativeRekeyRouting.sInputs_aMain]
    rw [hr,hrecords,hl]
    exact onePage_rel f _

theorem separated_map {f : LogicalKey → LogicalKey} {ps qs : List Page}
    (hp : List.Forall₂ (PageRel f) ps qs) (s s' : LogicalKey → Stored)
    (hs : ∀ key,s' (f key)=s key) (g : SepGeom) (w w' : LogicalKey → Nat)
    (hw : ∀ key,w' (f key)=w key) (inp : SInputs) (ops : List (Nat × Nat))
    (hg : Good (separatedInitialNative s' engineRule g w' (sInputs f inp) ops qs)) :
    separatedNative s' engineRule g w' (sInputs f inp) ops qs =
      NativeRekeyRouting.output f (separatedNative s engineRule g w inp ops ps) := by
  have hf := finish_rel (initial_rel hp s s' hs g w w' hw inp ops) hg s s' hs g w w' hw inp.bMain
  simp only [separatedNative]
  change Output.mk
    (finishNative s' g w' (inp.bMain.map (bucket f))
      (separatedInitialNative s' engineRule g w' (sInputs f inp) ops qs)).state.main
    (drainNative s' g.stashPages g.tierPages
      (finishNative s' g w' (inp.bMain.map (bucket f))
        (separatedInitialNative s' engineRule g w' (sInputs f inp) ops qs)).state) = _
  rw [hf.state,NativeRekeyDrain.drain_map f s s' hs]
  rfl


theorem flatMap_sublist {α β : Type} {xs : List α} {x : α} (hx : x ∈ xs) (f : α → List β) :
    List.Sublist (f x) (xs.flatMap f) := by
  have h : List.Sublist [x] xs := List.singleton_sublist.mpr hx
  simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil] using h.flatMap f

theorem good_of_ready (g : SepGeom) (ghost : FinishGhost)
    (hready : NativeMatchFinishInvariantProof.Ready g ghost)
    (hb : ∀ rs ∈ ghost.state.bcopy, (rs.map Rec.key).Nodup) : Good ghost := by
  refine ⟨hb,?_⟩
  intro ps hps p hp
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hps
  have hget : ghost.groups.getD i [] = ps := by
    rw [List.getD_eq_getElem _ _ hi]
    exact he
  have hn := hready.leaves_unique i
  rw [←NativeMatchFinishLocalProof.layout_getD ghost hready.layout i,hget] at hn
  exact hn.sublist ((flatMap_sublist hp (fun q => q.bucket.recs)).map Rec.key)

theorem initial_good (bridge : NativeMatchLanesBridge_statement) (s : LogicalKey → Stored)
    (g : SepGeom) (wOld w : LogicalKey → Nat) (inp : SInputs)
    (ops : List (Nat × Nat)) (pages : List Page) (hg : g.Valid) (hC : g.C=64)
    (hshape : SInputShape g wOld w inp) (hops : List.Perm ops g.canonicalOps)
    (hno : sFirstFailure g (sReferenceWith engineRule g w inp ops).trace=none)
    (ha : pageRecords pages=inp.aTier) (hb : ∀ rs ∈ inp.bTier,rs.length≤64)
    (hoff : ∀ e ∈ poolEvents g (sReferenceWith engineRule g w inp ops).route inp pages,
      ¬ e.bad s) :
    Good (separatedInitialNative s engineRule g w inp ops pages) := by
  rw [NativeMatchSeparatedFullProof.initial_agreement bridge s engineRule g w inp ops pages hC hno ha hb hoff]
  apply good_of_ready g
  · exact NativeMatchSeparatedReadyProof.canonical_ready engineRule g wOld w inp ops
      D1Lemmas.engine_valid hg hC hshape hops hno (by simpa only [hC] using hb)
  · intro rs hrs
    change rs ∈ inp.bTier at hrs
    have hn : (inp.bTier.flatten.map Rec.key).Nodup :=
      hshape.bNodup.sublist ((List.sublist_append_right (inp.bMain.flatMap Bucket.recs) inp.bTier.flatten).map Rec.key)
    have hsub : List.Sublist rs inp.bTier.flatten := by
      simpa only [List.flatMap_id,id_eq] using flatMap_sublist hrs id
    exact hn.sublist (hsub.map Rec.key)


theorem separated_guarded_map {f : LogicalKey → LogicalKey} {ps qs : List Page}
    (hp : List.Forall₂ (PageRel f) ps qs) (bridge : NativeMatchLanesBridge_statement)
    (s s' : LogicalKey → Stored) (hs : ∀ key,s' (f key)=s key)
    (g : SepGeom) (w wOld' w' : LogicalKey → Nat) (hw : ∀ key,w' (f key)=w key)
    (inp : SInputs) (ops : List (Nat × Nat)) (hg : g.Valid) (hC : g.C=64)
    (hshape : SInputShape g wOld' w' (sInputs f inp)) (hops : List.Perm ops g.canonicalOps)
    (hno : sFirstFailure g (sReferenceWith engineRule g w' (sInputs f inp) ops).trace=none)
    (ha : pageRecords qs=(sInputs f inp).aTier)
    (hb : ∀ rs ∈ (sInputs f inp).bTier,rs.length≤64)
    (hoff : ∀ e ∈ poolEvents g (sReferenceWith engineRule g w' (sInputs f inp) ops).route
      (sInputs f inp) qs, ¬ e.bad s') :
    separatedNative s' engineRule g w' (sInputs f inp) ops qs =
      NativeRekeyRouting.output f (separatedNative s engineRule g w inp ops ps) :=
  separated_map hp s s' hs g w w' hw inp ops
    (initial_good bridge s' g wOld' w' (sInputs f inp) ops qs hg hC hshape hops hno ha hb hoff)


theorem packedPages_sub (n : Nat) (rs : List Rec) :
    List.Sublist (pageRecords (bucketPages n (rs.map some))) rs := by
  rw [NativeMatchDenseTraceProof.bucketPages_records]
  have h := (List.take_sublist (64*n) (rs.map some)).filterMap id
  simpa only [Bucket.recs,List.filterMap_map,Function.comp_def,Option.map_some,
    Option.bind_some,List.filterMap_some,id_eq] using h

theorem stashPages_sub (n : Nat) (stashes : List (List Rec)) :
    List.Sublist (pageRecords (stashes.flatMap (fun rs => bucketPages n (rs.map some))))
      stashes.flatten := by
  induction stashes with
  | nil => exact .refl _
  | cons rs rest ih =>
    simp only [List.flatMap_cons,List.flatten_cons,NativeMatchRawPoolProof.pageRecords_append]
    exact (packedPages_sub n rs).append ih

theorem raw_sub (g : SepGeom) (route : SRoute) (pages : List Page) :
    List.Sublist (pageRecords (rawPoolPages g route pages))
      (route.stash.flatten ++ route.radix ++ pageRecords pages) := by
  unfold rawPoolPages
  rw [NativeMatchRawPoolProof.pageRecords_append,NativeMatchRawPoolProof.pageRecords_append]
  by_cases hr : 1 < g.r
  · rw [ite_eq_left hr]
    exact ((stashPages_sub g.stashPages route.stash).append
      (packedPages_sub g.stashPages route.radix)).append (.refl _)
  · rw [ite_eq_right hr]
    exact ((stashPages_sub g.stashPages route.stash).append
      (List.nil_sublist route.radix)).append (.refl _)

theorem onePage_good (leaves : List (List Rec))
    (hu : ∀ rs ∈ leaves,(rs.map Rec.key).Nodup) :
    ∀ ps ∈ onePageLeaves leaves, ∀ p ∈ ps,(p.bucket.recs.map Rec.key).Nodup := by
  intro ps hps p hp
  obtain ⟨rs,hrs,rfl⟩ := List.mem_map.mp hps
  have he : p=Page.ofRecords rs := List.mem_singleton.mp hp
  rw [he]
  exact (hu rs hrs).sublist ((NativeRekeyTop.ofRecords_sub rs).map Rec.key)

theorem initial_good_shape (s : LogicalKey → Stored) (g : SepGeom)
    (wOld w : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat)) (pages : List Page)
    (hg : g.Valid) (hshape : SInputShape g wOld w inp)
    (hops : List.Perm ops g.canonicalOps) (ha : pageRecords pages=inp.aTier) :
    Good (separatedInitialNative s engineRule g w inp ops pages) := by
  let route := sRouteWith engineRule g w inp.aMain ops
  let pool := pageRecords (poolNative s (carryTierPages inp) (rawPoolPages g route pages))
  have hinv : S12.SRInv g inp.aMain route := S12.srt_inv D1Lemmas.engine_valid hg hshape hops
  have hp : ((route.main.flatMap Bucket.recs) ++
      (route.stash.flatten ++ route.radix ++ inp.aTier)).Perm inp.aAll := by
    simpa only [SInputs.aAll,List.append_assoc] using hinv.perm.append_right inp.aTier
  have hraw : ((route.stash.flatten ++ route.radix ++ inp.aTier).map Rec.key).Nodup :=
    ((hp.map Rec.key).nodup_iff.mpr hshape.aNodup).sublist ((List.sublist_append_right _ _).map Rec.key)
  have hrawsub := raw_sub g route pages
  rw [ha] at hrawsub
  have hpool : (pool.map Rec.key).Nodup := hraw.sublist
    (((NativeRekeyTop.pool_sublist s (carryTierPages inp) (rawPoolPages g route pages)).trans hrawsub).map Rec.key)
  constructor
  · intro rs hrs
    change rs ∈ inp.bTier at hrs
    have hn : (inp.bTier.flatten.map Rec.key).Nodup :=
      hshape.bNodup.sublist ((List.sublist_append_right (inp.bMain.flatMap Bucket.recs) inp.bTier.flatten).map Rec.key)
    have hsub : List.Sublist rs inp.bTier.flatten := by
      simpa only [List.flatMap_id,id_eq] using flatMap_sublist hrs id
    exact hn.sublist (hsub.map Rec.key)
  · apply onePage_good
    intro rs hrs
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hrs
    exact hpool.sublist (List.filter_sublist.map Rec.key)


theorem separated_map_shape {f : LogicalKey → LogicalKey} {ps qs : List Page}
    (hp : List.Forall₂ (PageRel f) ps qs) (s s' : LogicalKey → Stored)
    (hs : ∀ key,s' (f key)=s key) (g : SepGeom) (w wOld' w' : LogicalKey → Nat)
    (hw : ∀ key,w' (f key)=w key) (inp : SInputs) (ops : List (Nat × Nat))
    (hg : g.Valid) (hshape : SInputShape g wOld' w' (sInputs f inp))
    (hops : List.Perm ops g.canonicalOps) (ha : pageRecords qs=(sInputs f inp).aTier) :
    separatedNative s' engineRule g w' (sInputs f inp) ops qs =
      NativeRekeyRouting.output f (separatedNative s engineRule g w inp ops ps) :=
  separated_map hp s s' hs g w w' hw inp ops
    (initial_good_shape s' g wOld' w' (sInputs f inp) ops qs hg hshape hops ha)

end RebuildBound.NativeRekeySeparated
