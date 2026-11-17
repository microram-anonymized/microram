import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyDrain
import RebuildBound.Proofs.NativeMatchJobs
import RebuildBound.Proofs.NativeMatchDenseTrace

namespace RebuildBound.NativeRekeyTop
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeRekeyLocal

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fin (f : LogicalKey → LogicalKey) (st : FinState) : FinState :=
  ⟨st.main.map (bucket f),st.ins.map (rec f),st.leaves.map (List.map (rec f)),
    st.bcopy.map (rec f),st.trace⟩

structure GhostRel (f : LogicalKey → LogicalKey)
    (a b : NativeMatchTopJobTrace.Ghost) : Prop where
  state : b.state = fin f a.state
  pages : List.Forall₂ (PageRel f) a.bpages b.bpages

lemma rel_getD {f : LogicalKey → LogicalKey} {ps qs : List Page}
    (h : List.Forall₂ (PageRel f) ps qs) {d d' : Page} (hd : PageRel f d d') (i : Nat) :
    PageRel f (ps.getD i d) (qs.getD i d') := by
  induction h generalizing i with
  | nil => simpa using hd
  | cons hp htail ih =>
    cases i with
    | zero => simpa using hp
    | succ i => simpa using ih i

lemma rel_filter_pages {f : LogicalKey → LogicalKey} {ps qs : List Page}
    (h : List.Forall₂ (PageRel f) ps qs) (p p' : Rec → Bool)
    (hp : ∀ r, p' (rec f r) = p r) :
    List.Forall₂ (PageRel f) (ps.map (Page.filter p)) (qs.map (Page.filter p')) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hab htail ih => exact List.Forall₂.cons (rel_filter hab p p' hp) ih

lemma dropTombs_map (f : LogicalKey → LogicalKey) (b : Bucket) :
    dropTombs (bucket f b) = bucket f (dropTombs b) := by
  simp only [dropTombs,bucket,List.map_map]
  apply List.map_congr_left
  intro lane _
  exact KeyRelabel.option_filter (rec f) _ _ (fun _ => rfl) lane

lemma rel_clear_candidates {f : LogicalKey → LogicalKey} {a a' b b' : Page}
    (ha : PageRel f a a') (hb : PageRel f b b')
    (s s' : LogicalKey → Stored) (hs : ∀ k, s' (f k) = s k)
    (p p' : Rec → Bool) (hp : ∀ r, p' (rec f r) = p r) :
    PageRel f (clearCandidatesNative s a b p) (clearCandidatesNative s' a' b' p') := by
  have hm := rel_wide ha (rel_filter hb p p' hp) s s' hs
  change wideMatch (storedKeys s' a'.1) a'.2 (storedKeys s' b'.1) (Page.filter p' b').2 =
    wideMatch (storedKeys s a.1) a.2 (storedKeys s b.1) (Page.filter p b).2 at hm
  constructor
  · change b'.2 &&& _ = b.2 &&& _
    rw [hb.mask,hm]
  · intro i hi
    change (b.2 &&& _).getLsbD i.val = true at hi
    rw [BitVec.getLsbD_and] at hi
    exact hb.payload i (Bool.and_eq_true_iff.mp hi).1

lemma resolve_state {f : LogicalKey → LogicalKey} {direction direction' : Page}
    {bpages bpages' : List Page} (hd : PageRel f direction direction')
    (hb : List.Forall₂ (PageRel f) bpages bpages')
    (s s' : LogicalKey → Stored) (hs : ∀ k, s' (f k) = s k)
    (g : TopGeom) (w w' : LogicalKey → Nat) (hw : ∀ k, w' (f k) = w k)
    (ci : Nat) (st : FinState) :
    topResolveNative s' g w' ci direction' (fin f st) bpages' =
      fin f (topResolveNative s g w ci direction st bpages) := by
  let home := fun r : Rec => topHome g w r == ci
  let home' := fun r : Rec => topHome g w' r == ci
  let keep := fun r : Rec => !(topHome g w r == ci && r.tomb)
  let keep' := fun r : Rec => !(topHome g w' r == ci && r.tomb)
  have hh : ∀ r, home' (rec f r) = home r := by intro r; simp only [home,home',topHome,rec,hw]
  have hk : ∀ r, keep' (rec f r) = keep r := by intro r; simp only [keep,keep',topHome,rec,hw]
  let R := ci / 2 ^ g.I
  let p := clearCandidatesNative s direction (Page.ofRecords (st.leaves.getD R [])) home
  let p' := clearCandidatesNative s' direction' (Page.ofRecords ((st.leaves.getD R []).map (rec f))) home'
  have hp : PageRel f p p' := rel_clear_candidates hd (rel_ofRecords f _) s s' hs home home' hh
  have hl : p'.bucket.recs.filter keep' = (p.bucket.recs.filter keep).map (rec f) := by
    rw [rel_bucket hp,bucket_recs]
    exact KeyRelabel.map_filter (rec f) keep keep' hk _
  let target := Page.ofBucket (dropTombs (st.main.getD ci []))
  let target' := Page.ofBucket (dropTombs (bucket f (st.main.getD ci [])))
  have ht : PageRel f target target' := by
    dsimp only [target,target']
    rw [dropTombs_map]
    exact rel_ofBucket f _
  have hpools := rel_pool (rel_filter_pages hb home home' hh)
    (List.Forall₂.cons ht List.Forall₂.nil) s s' hs
  have hm := rel_bucket (rel_getD hpools ht 0)
  have hc := KeyRelabel.map_filter (rec f) keep keep' hk st.bcopy
  simp only [topResolveNative,fin,buckets_getD,records_getD]
  change _ = FinState.mk _ _ _ _ _
  change FinState.mk
    (((st.main.map (bucket f)).set ci
      (((poolNative s' (bpages'.map (Page.filter home')) [target']).getD 0 target').bucket)))
    (st.ins.map (rec f))
    (((st.leaves.map (List.map (rec f))).set R (p'.bucket.recs.filter keep')))
    ((st.bcopy.map (rec f)).filter keep') st.trace = _
  rw [hl,hm,hc]
  simp only [List.map_set]
  rfl

lemma resolve_ghost {f : LogicalKey → LogicalKey} {a b : NativeMatchTopJobTrace.Ghost}
    (h : GhostRel f a b) {direction direction' : Page} (hd : PageRel f direction direction')
    (s s' : LogicalKey → Stored) (hs : ∀ k, s' (f k) = s k)
    (g : TopGeom) (w w' : LogicalKey → Nat) (hw : ∀ k, w' (f k) = w k) (ci : Nat) :
    GhostRel f (NativeMatchTopJobTrace.resolveNative s g w ci direction a)
      (NativeMatchTopJobTrace.resolveNative s' g w' ci direction' b) := by
  constructor
  · simp only [NativeMatchTopJobTrace.resolveNative,h.state]
    exact resolve_state hd h.pages s s' hs g w w' hw ci a.state
  · apply rel_filter_pages h.pages
    intro r
    simp only [topHome,rec,hw]

lemma offer_state (f : LogicalKey → LogicalKey) (g : TopGeom)
    (w w' : LogicalKey → Nat) (hw : ∀ k, w' (f k) = w k) (ci : Nat) (st : FinState)
    (ha : Set.InjOn f {k | k ∈ (st.leaves.getD (ci / 2 ^ g.I) []).map Rec.key})
    (hb : Set.InjOn f {k | k ∈ st.bcopy.map Rec.key}) :
    topOffer g w' ci (fin f st) = fin f (topOffer g w ci st) := by
  let R := ci / 2 ^ g.I
  let leaf := st.leaves.getD R []
  let ca := leaf.filter fun r => topHome g w r == ci
  let cb := st.bcopy.filter fun r => topHome g w r == ci
  let fa := fill (st.main.getD ci []) ca
  let fb := fill fa.1 cb
  let ga := (ca.take (ca.length - fa.2.length)).map Rec.key
  let gb := (cb.take (cb.length - fb.2.length)).map Rec.key
  have hh : ∀ r, (topHome g w' (rec f r) == ci) = (topHome g w r == ci) := by
    intro r; simp only [topHome,rec,hw]
  have hca : (leaf.map (rec f)).filter (fun r => topHome g w' r == ci) = ca.map (rec f) :=
    KeyRelabel.map_filter (rec f) _ _ hh leaf
  have hcb : (st.bcopy.map (rec f)).filter (fun r => topHome g w' r == ci) = cb.map (rec f) :=
    KeyRelabel.map_filter (rec f) _ _ hh st.bcopy
  have hfa : fill (bucket f (st.main.getD ci [])) (ca.map (rec f)) =
      (bucket f fa.1,fa.2.map (rec f)) := KeyRelabel.fill_map (rec f) _ _
  have hfb : fill (bucket f fa.1) (cb.map (rec f)) =
      (bucket f fb.1,fb.2.map (rec f)) := KeyRelabel.fill_map (rec f) _ _
  have hga : ((ca.map (rec f)).take ((ca.map (rec f)).length -
      (fa.2.map (rec f)).length)).map Rec.key = ga.map f := by
    simp only [List.length_map,←List.map_take,List.map_map,ga]
    rfl
  have hgb : ((cb.map (rec f)).take ((cb.map (rec f)).length -
      (fb.2.map (rec f)).length)).map Rec.key = gb.map f := by
    simp only [List.length_map,←List.map_take,List.map_map,gb]
    rfl
  have hgas : ga ⊆ leaf.map Rec.key := by
    intro k hk
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hk
    exact List.mem_map.mpr ⟨r,List.mem_of_mem_filter (List.mem_of_mem_take hr),rfl⟩
  have hgbs : gb ⊆ st.bcopy.map Rec.key := by
    intro k hk
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hk
    exact List.mem_map.mpr ⟨r,List.mem_of_mem_filter (List.mem_of_mem_take hr),rfl⟩
  have hra := records_remove f leaf ga ha hgas
  have hrb := records_remove f st.bcopy gb hb hgbs
  simp only [topOffer,fin,buckets_getD,records_getD]
  rw [hca,hcb,hfa,hfb]
  simp only []
  rw [hga,hgb,hra,hrb]
  simp only [List.map_set]
  rfl

lemma placedB_map (f : LogicalKey → LogicalKey) (g : TopGeom)
    (w w' : LogicalKey → Nat) (hw : ∀ k, w' (f k) = w k) (ci : Nat) (st : FinState) :
    NativeMatchTopJobTrace.placedB g w' ci (fin f st) =
      (NativeMatchTopJobTrace.placedB g w ci st).map f := by
  have hh : ∀ r, (topHome g w' (rec f r) == ci) = (topHome g w r == ci) := by
    intro r; simp only [topHome,rec,hw]
  have hm (rs : List Rec) : (rs.map (rec f)).filter (fun r => topHome g w' r == ci) =
      (rs.filter (fun r => topHome g w r == ci)).map (rec f) :=
    KeyRelabel.map_filter (rec f) _ _ hh rs
  simp only [NativeMatchTopJobTrace.placedB,fin,records_getD,buckets_getD,hm,
    bucket,KeyRelabel.fill_map,List.length_map,←List.map_take,List.map_map]
  rfl

lemma placedB_sub (g : TopGeom) (w : LogicalKey → Nat) (ci : Nat) (st : FinState) :
    NativeMatchTopJobTrace.placedB g w ci st ⊆ st.bcopy.map Rec.key := by
  intro k hk
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hk
  exact List.mem_map.mpr ⟨r,List.mem_of_mem_filter (List.mem_of_mem_take hr),rfl⟩

lemma rel_remove_pages {f : LogicalKey → LogicalKey} {ps qs : List Page}
    (h : List.Forall₂ (PageRel f) ps qs) (keys gone : List LogicalKey)
    (hi : Set.InjOn f {k | k ∈ keys}) (hg : gone ⊆ keys)
    (hk : ∀ p ∈ ps, p.bucket.recs.map Rec.key ⊆ keys) :
    List.Forall₂ (PageRel f) (ps.map (Page.filter fun r => !gone.contains r.key))
      (qs.map (Page.filter fun r => !(gone.map f).contains r.key)) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons p q ps qs hp htail ih =>
    apply List.Forall₂.cons
    · apply rel_filter_active hp
      intro i hmask
      rw [hp.payload i hmask]
      change (!(gone.map f).contains (f (p.1 i.val).key)) = (!gone.contains (p.1 i.val).key)
      rw [contains_local f keys gone hi hg _ (hk p List.mem_cons_self
        (List.mem_map.mpr ⟨p.1 i.val,(mem_page _ _).mpr ⟨i,hmask,rfl⟩,rfl⟩))]
    · exact ih (fun p hp => hk p (List.mem_cons_of_mem _ hp))

lemma offer_ghost {f : LogicalKey → LogicalKey} {a b : NativeMatchTopJobTrace.Ghost}
    (h : GhostRel f a b) (g : TopGeom) (w w' : LogicalKey → Nat)
    (hw : ∀ k, w' (f k) = w k) (ci : Nat)
    (ha : Set.InjOn f {k | k ∈ (a.state.leaves.getD (ci / 2 ^ g.I) []).map Rec.key})
    (hb : Set.InjOn f {k | k ∈ a.state.bcopy.map Rec.key})
    (hlayout : pageRecords a.bpages = a.state.bcopy) :
    GhostRel f (NativeMatchTopJobTrace.offer g w ci a)
      (NativeMatchTopJobTrace.offer g w' ci b) := by
  constructor
  · simp only [NativeMatchTopJobTrace.offer,h.state]
    exact offer_state f g w w' hw ci a.state ha hb
  · simp only [NativeMatchTopJobTrace.offer,h.state,placedB_map f g w w' hw]
    apply rel_remove_pages h.pages (a.state.bcopy.map Rec.key) _ hb (placedB_sub g w ci a.state)
    intro p hp k hk
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hk
    apply List.mem_map.mpr
    refine ⟨r,?_,rfl⟩
    rw [←hlayout]
    exact List.mem_flatMap.mpr ⟨p,hp,hr⟩

lemma resolve_layout (s : LogicalKey → Stored) (g : TopGeom) (w : LogicalKey → Nat)
    (ci : Nat) (direction : Page) (a : NativeMatchTopJobTrace.Ghost)
    (h : pageRecords a.bpages = a.state.bcopy) :
    pageRecords (NativeMatchTopJobTrace.resolveNative s g w ci direction a).bpages =
      (NativeMatchTopJobTrace.resolveNative s g w ci direction a).state.bcopy := by
  simp only [NativeMatchTopJobTrace.resolveNative,topResolveNative,
    NativeMatchTopResolveProof.pageRecords_filter,h]

lemma offer_layout (g : TopGeom) (w : LogicalKey → Nat) (ci : Nat)
    (a : NativeMatchTopJobTrace.Ghost) (h : pageRecords a.bpages = a.state.bcopy) :
    pageRecords (NativeMatchTopJobTrace.offer g w ci a).bpages =
      (NativeMatchTopJobTrace.offer g w ci a).state.bcopy := by
  simp only [NativeMatchTopJobTrace.offer,topOffer,NativeMatchTopJobTrace.placedB,
    NativeMatchTopResolveProof.pageRecords_filter,h]

lemma rel_buckets {f : LogicalKey → LogicalKey} {ps qs : List Page}
    (h : List.Forall₂ (PageRel f) ps qs) :
    qs.map Page.bucket = (ps.map Page.bucket).map (bucket f) := by
  induction h with
  | nil => rfl
  | cons hp htail ih => simp only [List.map_cons,rel_bucket hp,ih]

lemma clear_ghost {f : LogicalKey → LogicalKey} {a b : NativeMatchTopJobTrace.Ghost}
    (h : GhostRel f a b) (s s' : LogicalKey → Stored) (hs : ∀ k, s' (f k) = s k)
    (g : TopGeom) (Bi : Bucket) (i : Nat) :
    GhostRel f (NativeMatchTopJobTrace.clearNative s g Bi i a)
      (NativeMatchTopJobTrace.clearNative s' g (bucket f Bi) i b) := by
  have hp : List.Forall₂ (PageRel f) (a.state.main.map Page.ofBucket)
      ((a.state.main.map (bucket f)).map Page.ofBucket) := by
    induction a.state.main with
    | nil => exact List.Forall₂.nil
    | cons B bs ih => exact List.Forall₂.cons (rel_ofBucket f B) ih
  have hf := NativeRekeyFinish.rel_fixed (rel_ofBucket f Bi) hp s s' hs
    ((List.range g.D).map (fun q => i + q * g.U))
  have he : (fixedNative s' (Page.ofBucket (bucket f Bi))
      ((a.state.main.map (bucket f)).map Page.ofBucket)
      ((List.range g.D).map (fun q => i + q * g.U))).map Page.bucket =
      ((fixedNative s (Page.ofBucket Bi) (a.state.main.map Page.ofBucket)
      ((List.range g.D).map (fun q => i + q * g.U))).map Page.bucket).map (bucket f) := by
    exact rel_buckets hf
  constructor
  · simp only [NativeMatchTopJobTrace.clearNative,h.state,fin,he]
  · exact h.pages

lemma page_mask_sublist (p : Page) (mask : Mask)
    (hm : ∀ i : Lanes.Slot, mask.getLsbD i.val = true → p.2.getLsbD i.val = true) :
    (Page.bucket (p.1,mask)).recs.Sublist p.bucket.recs := by
  simp only [Page.bucket,DirectMask64.bucket,Bucket.recs,List.filterMap_map,Function.comp_apply,id_eq]
  have aux (xs : List Nat) (hx : ∀ i ∈ xs, i < 64) :
      (xs.filterMap (fun i => if mask.getLsbD i then some (p.1 i) else none)).Sublist
        (xs.filterMap (fun i => if p.2.getLsbD i then some (p.1 i) else none)) := by
    induction xs with
    | nil => exact List.Sublist.slnil
    | cons i rest ih =>
      have hrest := ih (fun j hj => hx j (List.mem_cons_of_mem _ hj))
      by_cases hb : mask.getLsbD i = true
      · have ha := hm ⟨i,hx i List.mem_cons_self⟩ hb
        simpa [hb,ha] using List.Sublist.cons_cons (p.1 i) hrest
      · by_cases ha : p.2.getLsbD i = true
        · simpa [hb,ha] using List.Sublist.cons (p.1 i) hrest
        · simpa [hb,ha] using hrest
  exact aux (List.range 64) (fun i hi => List.mem_range.mp hi)

lemma clear_candidates_sub (s : LogicalKey → Stored) (a b : Page) (p : Rec → Bool) :
    (clearCandidatesNative s a b p).bucket.recs.Sublist b.bucket.recs := by
  apply page_mask_sublist
  intro i hi
  rw [BitVec.getLsbD_and] at hi
  exact (Bool.and_eq_true_iff.mp hi).1

lemma ofRecords_sub (rs : List Rec) : (Page.ofRecords rs).bucket.recs.Sublist rs := by
  rw [Page.ofRecords,NativeMatchDenseTraceProof.pageOfBucket_records]
  have h := (List.take_sublist 64 (rs.map some ++ List.replicate (64-rs.length) none)).filterMap id
  simpa [Bucket.recs,List.filterMap_append,List.filterMap_map,List.filterMap_replicate] using h

def Layout (a : NativeMatchTopJobTrace.Ghost) : Prop := pageRecords a.bpages = a.state.bcopy

def Good (a : NativeMatchTopJobTrace.Ghost) : Prop :=
  (∀ rs ∈ a.state.leaves, (rs.map Rec.key).Nodup) ∧ (a.state.bcopy.map Rec.key).Nodup

lemma resolve_good (a : NativeMatchTopJobTrace.Ghost) (ha : Good a)
    (s : LogicalKey → Stored) (g : TopGeom) (w : LogicalKey → Nat)
    (ci : Nat) (direction : Page) :
    Good (NativeMatchTopJobTrace.resolveNative s g w ci direction a) := by
  constructor
  · apply NativeRekeyFinish.all_set ha.1
    have h := NativeRekeyFinish.all_getD ha.1 [] (by simp) (ci / 2 ^ g.I)
    exact h.sublist ((List.filter_sublist.trans
      ((clear_candidates_sub s direction _ _).trans (ofRecords_sub _))).map Rec.key)
  · exact ha.2.sublist (List.filter_sublist.map Rec.key)

lemma offer_good (a : NativeMatchTopJobTrace.Ghost) (ha : Good a)
    (g : TopGeom) (w : LogicalKey → Nat) (ci : Nat) :
    Good (NativeMatchTopJobTrace.offer g w ci a) := by
  constructor
  · apply NativeRekeyFinish.all_set ha.1
    exact (NativeRekeyFinish.all_getD ha.1 [] (by simp) (ci / 2 ^ g.I)).sublist
      (List.filter_sublist.map Rec.key)
  · exact ha.2.sublist (List.filter_sublist.map Rec.key)

lemma offer_rel {f : LogicalKey → LogicalKey} {a b : NativeMatchTopJobTrace.Ghost}
    (h : GhostRel f a b) (hb : Good b) (hl : Layout a)
    (g : TopGeom) (w w' : LogicalKey → Nat) (hw : ∀ k, w' (f k) = w k) (ci : Nat) :
    GhostRel f (NativeMatchTopJobTrace.offer g w ci a)
      (NativeMatchTopJobTrace.offer g w' ci b) := by
  have ha := NativeRekeyFinish.all_getD hb.1 [] (by simp) (ci / 2 ^ g.I)
  have hbc := hb.2
  rw [h.state] at ha hbc
  simp only [fin,records_getD,List.map_map] at ha hbc
  have hai : Set.InjOn f {k | k ∈ (a.state.leaves.getD (ci / 2 ^ g.I) []).map Rec.key} := by
    apply List.inj_on_of_nodup_map
    simpa only [List.map_map,Function.comp_def,rec] using ha
  have hbi : Set.InjOn f {k | k ∈ a.state.bcopy.map Rec.key} := by
    apply List.inj_on_of_nodup_map
    simpa only [List.map_map,Function.comp_def,rec] using hbc
  exact offer_ghost h g w w' hw ci hai hbi hl

lemma direction_rel (f : LogicalKey → LogicalKey) (g : TopGeom)
    (w w' : LogicalKey → Nat) (hw : ∀ k, w' (f k) = w k) (Bi : Bucket) (q : Nat) :
    PageRel f (NativeMatchTopJobTrace.direction g w Bi q)
      (NativeMatchTopJobTrace.direction g w' (bucket f Bi) q) := by
  apply rel_filter (rel_ofBucket f Bi)
  intro r
  simp only [topWay,topHome,rec,hw]

lemma main_set_rel {f : LogicalKey → LogicalKey} {a b : NativeMatchTopJobTrace.Ghost}
    (h : GhostRel f a b) (ci : Nat) (B : Bucket) :
    GhostRel f ⟨{a.state with main := a.state.main.set ci B},a.bpages⟩
      ⟨{b.state with main := b.state.main.set ci (bucket f B)},b.bpages⟩ := by
  constructor
  · rw [h.state]
    simp only [fin,List.map_set]
  · exact h.pages

lemma dest_rel {f : LogicalKey → LogicalKey} {a b : NativeMatchTopJobTrace.Ghost}
    (h : GhostRel f a b) (hb : Good b) (hl : Layout a)
    (s s' : LogicalKey → Stored) (hs : ∀ k, s' (f k) = s k)
    (g : TopGeom) (w w' : LogicalKey → Nat) (hw : ∀ k, w' (f k) = w k)
    (Bi : Bucket) (i q : Nat) :
    GhostRel f (NativeMatchTopJobTrace.destNative s g w Bi i q a).1
      (NativeMatchTopJobTrace.destNative s' g w' (bucket f Bi) i q b).1 ∧
    (NativeMatchTopJobTrace.destNative s' g w' (bucket f Bi) i q b).2 =
      (NativeMatchTopJobTrace.destNative s g w Bi i q a).2.map (rec f) := by
  let ci := i + q * g.U
  let ar := NativeMatchTopJobTrace.resolveNative s g w ci
    (NativeMatchTopJobTrace.direction g w Bi q) a
  let br := NativeMatchTopJobTrace.resolveNative s' g w' ci
    (NativeMatchTopJobTrace.direction g w' (bucket f Bi) q) b
  have hr : GhostRel f ar br := resolve_ghost h (direction_rel f g w w' hw Bi q)
    s s' hs g w w' hw ci
  have hg : Good br := resolve_good b hb s' g w' ci _
  have hlr : Layout ar := resolve_layout s g w ci _ a hl
  have hc : (((bucket f Bi).recs.filter (fun r => topWay g w' r == q)).filter
      (fun r => !r.tomb)) =
      ((Bi.recs.filter (fun r => topWay g w r == q)).filter (fun r => !r.tomb)).map (rec f) := by
    rw [bucket_recs]
    rw [KeyRelabel.map_filter (rec f) (fun r => topWay g w r == q)
      (fun r => topWay g w' r == q) (by intro r; simp only [topWay,topHome,rec,hw])]
    exact KeyRelabel.map_filter (rec f) _ _ (by intro r; rfl) _
  have hm : br.state.main.getD ci [] = bucket f (ar.state.main.getD ci []) := by
    rw [hr.state]
    exact buckets_getD f ar.state.main ci
  let filled := fill (ar.state.main.getD ci [])
    ((Bi.recs.filter fun r => topWay g w r == q).filter fun r => !r.tomb)
  have hf : fill (br.state.main.getD ci [])
      (((bucket f Bi).recs.filter fun r => topWay g w' r == q).filter fun r => !r.tomb) =
      (bucket f filled.1, filled.2.map (rec f)) := by
    rw [hm,hc]
    exact KeyRelabel.fill_map (rec f) _ _
  change GhostRel f (NativeMatchTopJobTrace.offer g w ci
    ⟨{ar.state with main := ar.state.main.set ci filled.1},ar.bpages⟩) _ ∧ _
  simp only [NativeMatchTopJobTrace.destNative]
  change GhostRel f (NativeMatchTopJobTrace.offer g w ci
    ⟨{ar.state with main := ar.state.main.set ci filled.1},ar.bpages⟩)
    (NativeMatchTopJobTrace.offer g w' ci
    ⟨{br.state with main := br.state.main.set ci (fill (br.state.main.getD ci []) _).1},br.bpages⟩) ∧ _
  rw [hf]
  exact ⟨offer_rel (main_set_rel hr ci filled.1) hg hlr g w w' hw ci,rfl⟩

lemma dest_good (a : NativeMatchTopJobTrace.Ghost) (ha : Good a)
    (s : LogicalKey → Stored) (g : TopGeom) (w : LogicalKey → Nat) (Bi : Bucket) (i q : Nat) :
    Good (NativeMatchTopJobTrace.destNative s g w Bi i q a).1 := by
  unfold NativeMatchTopJobTrace.destNative
  dsimp only
  apply offer_good
  exact resolve_good a ha s g w (i+q*g.U) (NativeMatchTopJobTrace.direction g w Bi q)

lemma dest_layout (a : NativeMatchTopJobTrace.Ghost) (ha : Layout a)
    (s : LogicalKey → Stored) (g : TopGeom) (w : LogicalKey → Nat) (Bi : Bucket) (i q : Nat) :
    Layout (NativeMatchTopJobTrace.destNative s g w Bi i q a).1 := by
  unfold NativeMatchTopJobTrace.destNative Layout
  dsimp only
  apply offer_layout
  exact resolve_layout s g w (i+q*g.U) (NativeMatchTopJobTrace.direction g w Bi q) a ha

def Strong (f : LogicalKey → LogicalKey) (a b : NativeMatchTopJobTrace.Ghost) : Prop :=
  GhostRel f a b ∧ Layout a ∧ Good b

def AccRel (f : LogicalKey → LogicalKey)
    (a b : NativeMatchTopJobTrace.Ghost × List Rec) : Prop :=
  Strong f a.1 b.1 ∧ b.2 = a.2.map (rec f)

lemma way_rel {f : LogicalKey → LogicalKey} {a b : NativeMatchTopJobTrace.Ghost × List Rec}
    (h : AccRel f a b) (s s' : LogicalKey → Stored) (hs : ∀ k, s' (f k) = s k)
    (g : TopGeom) (w w' : LogicalKey → Nat) (hw : ∀ k, w' (f k) = w k)
    (Bi : Bucket) (i q : Nat) :
    AccRel f (NativeMatchTopJobTrace.wayNative s g w Bi i a q)
      (NativeMatchTopJobTrace.wayNative s' g w' (bucket f Bi) i b q) := by
  have hd := dest_rel h.1.1 h.1.2.2 h.1.2.1 s s' hs g w w' hw Bi i q
  refine ⟨⟨hd.1,dest_layout a.1 h.1.2.1 s g w Bi i q,
    dest_good b.1 h.1.2.2 s' g w' (bucket f Bi) i q⟩,?_⟩
  change b.2 ++ _ = (a.2 ++ _).map (rec f)
  rw [h.2,hd.2,List.map_append]

lemma clear_strong {f : LogicalKey → LogicalKey} {a b : NativeMatchTopJobTrace.Ghost}
    (h : Strong f a b) (s s' : LogicalKey → Stored) (hs : ∀ k, s' (f k) = s k)
    (g : TopGeom) (Bi : Bucket) (i : Nat) :
    Strong f (NativeMatchTopJobTrace.clearNative s g Bi i a)
      (NativeMatchTopJobTrace.clearNative s' g (bucket f Bi) i b) :=
  ⟨clear_ghost h.1 s s' hs g Bi i,h.2.1,h.2.2⟩

lemma appendSheds_rel {f : LogicalKey → LogicalKey}
    {a b : NativeMatchTopJobTrace.Ghost × List Rec} (h : AccRel f a b) :
    Strong f (NativeMatchTopJobTrace.appendSheds a) (NativeMatchTopJobTrace.appendSheds b) := by
  refine ⟨⟨?_,h.1.1.pages⟩,h.1.2.1,h.1.2.2⟩
  simp only [NativeMatchTopJobTrace.appendSheds,h.1.1.state,h.2,fin,List.map_append,List.length_append,List.length_map]

lemma bucket_rel {f : LogicalKey → LogicalKey} {a b : NativeMatchTopJobTrace.Ghost}
    (h : Strong f a b) (s s' : LogicalKey → Stored) (hs : ∀ k, s' (f k) = s k)
    (g : TopGeom) (w w' : LogicalKey → Nat) (hw : ∀ k, w' (f k) = w k)
    (bMain : List Bucket) (i : Nat) :
    Strong f (NativeMatchTopJobTrace.bucketNative s g w bMain a i)
      (NativeMatchTopJobTrace.bucketNative s' g w' (bMain.map (bucket f)) b i) := by
  let Bi := bMain.getD i []
  have hc := clear_strong h s s' hs g Bi i
  have hstart : AccRel f (NativeMatchTopJobTrace.clearNative s g Bi i a,[])
      (NativeMatchTopJobTrace.clearNative s' g (bucket f Bi) i b,[]) := ⟨hc,rfl⟩
  have hf := NativeRekeyFinish.fold_guarded (AccRel f) (fun _ => True)
    (NativeMatchTopJobTrace.wayNative s g w Bi i)
    (NativeMatchTopJobTrace.wayNative s' g w' (bucket f Bi) i)
    (fun a b q hab _ => way_rel hab s s' hs g w w' hw Bi i q)
    (fun _ _ _ => True.intro) (List.range g.D) _ _ hstart True.intro
  simpa only [NativeMatchTopJobTrace.bucketNative,buckets_getD] using appendSheds_rel hf.1

lemma finish_strong {f : LogicalKey → LogicalKey} {a b : NativeMatchTopJobTrace.Ghost}
    (h : Strong f a b) (s s' : LogicalKey → Stored) (hs : ∀ k, s' (f k) = s k)
    (g : TopGeom) (w w' : LogicalKey → Nat) (hw : ∀ k, w' (f k) = w k)
    (bMain : List Bucket) :
    Strong f (NativeMatchTopJobTrace.finishNative s g w bMain a)
      (NativeMatchTopJobTrace.finishNative s' g w' (bMain.map (bucket f)) b) :=
  (NativeRekeyFinish.fold_guarded (Strong f) (fun _ => True)
    (NativeMatchTopJobTrace.bucketNative s g w bMain)
    (NativeMatchTopJobTrace.bucketNative s' g w' (bMain.map (bucket f)))
    (fun _ _ i hab _ => bucket_rel hab s s' hs g w w' hw bMain i)
    (fun _ _ _ => True.intro) (List.range g.U) a b h True.intro).1

lemma finish_rel {f : LogicalKey → LogicalKey} {a b : NativeMatchTopJobTrace.Ghost}
    (h : GhostRel f a b) (ha : Layout a) (hb : Good b)
    (s s' : LogicalKey → Stored) (hs : ∀ k, s' (f k) = s k)
    (g : TopGeom) (w w' : LogicalKey → Nat) (hw : ∀ k, w' (f k) = w k)
    (bMain : List Bucket) :
    GhostRel f (NativeMatchTopJobTrace.finishNative s g w bMain a)
      (NativeMatchTopJobTrace.finishNative s' g w' (bMain.map (bucket f)) b) :=
  (finish_strong ⟨h,ha,hb⟩ s s' hs g w w' hw bMain).1

lemma native_page_sublist (s : LogicalKey → Stored) (a b : Page) :
    (nativePage s a b).bucket.recs.Sublist b.bucket.recs := by
  apply page_mask_sublist
  intro i hi
  rw [BitVec.getLsbD_and] at hi
  exact (Bool.and_eq_true_iff.mp hi).1

lemma pool_sublist (s : LogicalKey → Stored) (sources targets : List Page) :
    (pageRecords (poolNative s sources targets)).Sublist (pageRecords targets) := by
  induction sources generalizing targets with
  | nil => exact List.Sublist.refl _
  | cons a sources ih =>
    apply (ih (targets.map (nativePage s a))).trans
    induction targets with
    | nil => exact List.Sublist.slnil
    | cons b targets iht =>
      simp only [List.map_cons,pageRecords,List.flatMap_cons]
      exact (native_page_sublist s a b).append iht

lemma initial_good (s : LogicalKey → Stored) (g : TopGeom) (u : Rec → Bool)
    (w : LogicalKey → Nat) (inp : TopInputs) (carryPages bpages : List Page)
    (ha : (inp.carry.map Rec.key).Nodup) (hb : (inp.bTier.map Rec.key).Nodup)
    (hc : pageRecords carryPages = inp.carry) :
    Good (NativeMatchTopJobTrace.initialNative s g u w inp carryPages bpages) := by
  constructor
  · intro rs hrs
    change rs ∈ leavesOf g.toGeom w _ at hrs
    obtain ⟨R,hR,rfl⟩ := List.mem_map.mp hrs
    have hp := pool_sublist s bpages carryPages
    rw [hc] at hp
    exact ha.sublist ((List.filter_sublist.trans (List.filter_sublist.trans hp)).map Rec.key)
  · exact hb.sublist (List.filter_sublist.map Rec.key)

lemma initial_good_shape (s : LogicalKey → Stored) (g : TopGeom) (u : Rec → Bool)
    (w : LogicalKey → Nat) (inp : TopInputs) (carryPages bpages : List Page)
    (hshape : TopShape g u w inp) (hc : pageRecords carryPages = inp.carry) :
    Good (NativeMatchTopJobTrace.initialNative s g u w inp carryPages bpages) := by
  have ha := hshape.aNodup
  have hb := hshape.bNodup
  simp only [TopInputs.aAll,TopInputs.bAll,List.map_append] at ha hb
  exact initial_good s g u w inp carryPages bpages ha.of_append_right hb.of_append_right hc

lemma initial_layout (s : LogicalKey → Stored) (g : TopGeom) (u : Rec → Bool)
    (w : LogicalKey → Nat) (inp : TopInputs) (carryPages bpages : List Page)
    (hb : pageRecords bpages = inp.bTier) :
    Layout (NativeMatchTopJobTrace.initialNative s g u w inp carryPages bpages) := by
  simp only [Layout,NativeMatchTopJobTrace.initialNative,
    NativeMatchTopResolveProof.pageRecords_filter,hb,topTierCopy]

def inputs (f : LogicalKey → LogicalKey) (inp : TopInputs) : TopInputs :=
  ⟨inp.cMain.map (bucket f),inp.carry.map (rec f),inp.bMain.map (bucket f),inp.bTier.map (rec f)⟩

lemma leaves_map (f : LogicalKey → LogicalKey) (g : Geom)
    (w w' : LogicalKey → Nat) (hw : ∀ k, w' (f k) = w k) (rs : List Rec) :
    leavesOf g w' (rs.map (rec f)) = (leavesOf g w rs).map (List.map (rec f)) := by
  simp only [leavesOf,List.map_map]
  apply List.map_congr_left
  intro R hR
  exact KeyRelabel.map_filter (rec f) _ _ (by intro r; simp [rangeOf,home,rec,hw]) _

lemma initial_rel {f : LogicalKey → LogicalKey}
    {carryPages carryPages' bpages bpages' : List Page}
    (hc : List.Forall₂ (PageRel f) carryPages carryPages')
    (hb : List.Forall₂ (PageRel f) bpages bpages')
    (s s' : LogicalKey → Stored) (hs : ∀ k, s' (f k) = s k)
    (g : TopGeom) (u u' : Rec → Bool) (hu : ∀ r, u' (rec f r) = u r)
    (w w' : LogicalKey → Nat) (hw : ∀ k, w' (f k) = w k) (inp : TopInputs) :
    GhostRel f (NativeMatchTopJobTrace.initialNative s g u w inp carryPages bpages)
      (NativeMatchTopJobTrace.initialNative s' g u' w' (inputs f inp) carryPages' bpages') := by
  have hkeep : ∀ r, (!earlyDrop u' (rec f r)) = (!earlyDrop u r) := by
    intro r
    change (!(r.tomb && u' (rec f r))) = !(r.tomb && u r)
    rw [hu]
  have hp := rel_pageRecords (rel_pool hb hc s s' hs)
  have hfilter (rs : List Rec) := KeyRelabel.map_filter (rec f)
    (fun r => !earlyDrop u r) (fun r => !earlyDrop u' r) hkeep rs
  constructor
  · simp only [NativeMatchTopJobTrace.initialNative,hp,leaves_map f g.toGeom w w' hw,
      inputs,fin,topTierCopy,hfilter,List.map_nil]
  · exact rel_filter_pages hb _ _ hkeep

lemma toSFin_map (f : LogicalKey → LogicalKey) (st : FinState) :
    NativeMatchTopJobTrace.toSFin (fin f st) = sfin f (NativeMatchTopJobTrace.toSFin st) := rfl

lemma native_map {f : LogicalKey → LogicalKey}
    {carryPages carryPages' bpages bpages' : List Page}
    (hc : List.Forall₂ (PageRel f) carryPages carryPages')
    (hb : List.Forall₂ (PageRel f) bpages bpages')
    (s s' : LogicalKey → Stored) (hs : ∀ k, s' (f k) = s k)
    (g : TopGeom) (u u' : Rec → Bool) (hu : ∀ r, u' (rec f r) = u r)
    (w w' : LogicalKey → Nat) (hw : ∀ k, w' (f k) = w k) (inp : TopInputs)
    (hl : pageRecords bpages = inp.bTier)
    (hg : Good (NativeMatchTopJobTrace.initialNative s' g u' w' (inputs f inp) carryPages' bpages')) :
    NativeMatchTopJobTrace.native s' g u' w' (inputs f inp) carryPages' bpages' =
      let out := NativeMatchTopJobTrace.native s g u w inp carryPages bpages
      ⟨out.main.map (bucket f),bucket f out.tier⟩ := by
  have hi := initial_rel hc hb s s' hs g u u' hu w w' hw inp
  have hl' := initial_layout s g u w inp carryPages bpages hl
  have hf := finish_rel hi hl' hg s s' hs g w w' hw inp.bMain
  have hm : (inputs f inp).bMain = inp.bMain.map (bucket f) := rfl
  simp only [NativeMatchTopJobTrace.native,hm,hf.state,toSFin_map,
    NativeRekeyDrain.drain_map f s s' hs,dropTombs_map]
  simp only [fin,List.map_map]
  congr 1
  apply List.map_congr_left
  intro B hB
  exact dropTombs_map f B

lemma native_map_unique {f : LogicalKey → LogicalKey}
    {carryPages carryPages' bpages bpages' : List Page}
    (hc : List.Forall₂ (PageRel f) carryPages carryPages')
    (hb : List.Forall₂ (PageRel f) bpages bpages')
    (s s' : LogicalKey → Stored) (hs : ∀ k, s' (f k) = s k)
    (g : TopGeom) (u u' : Rec → Bool) (hu : ∀ r, u' (rec f r) = u r)
    (w w' : LogicalKey → Nat) (hw : ∀ k, w' (f k) = w k) (inp : TopInputs)
    (hlc : pageRecords carryPages = inp.carry) (hlb : pageRecords bpages = inp.bTier)
    (ha : ((inp.carry.map (rec f)).map Rec.key).Nodup)
    (ht : ((inp.bTier.map (rec f)).map Rec.key).Nodup) :
    NativeMatchTopJobTrace.native s' g u' w' (inputs f inp) carryPages' bpages' =
      let out := NativeMatchTopJobTrace.native s g u w inp carryPages bpages
      ⟨out.main.map (bucket f),bucket f out.tier⟩ := by
  apply native_map hc hb s s' hs g u u' hu w w' hw inp hlb
  apply initial_good s' g u' w' (inputs f inp) carryPages' bpages' ha ht
  rw [rel_pageRecords hc,hlc]
  rfl

lemma native_map_shape {f : LogicalKey → LogicalKey}
    {carryPages carryPages' bpages bpages' : List Page}
    (hc : List.Forall₂ (PageRel f) carryPages carryPages')
    (hb : List.Forall₂ (PageRel f) bpages bpages')
    (s s' : LogicalKey → Stored) (hs : ∀ k, s' (f k) = s k)
    (g : TopGeom) (u u' : Rec → Bool) (hu : ∀ r, u' (rec f r) = u r)
    (w w' : LogicalKey → Nat) (hw : ∀ k, w' (f k) = w k) (inp : TopInputs)
    (hlc : pageRecords carryPages = inp.carry) (hlb : pageRecords bpages = inp.bTier)
    (hshape : TopShape g u' w' (inputs f inp)) :
    NativeMatchTopJobTrace.native s' g u' w' (inputs f inp) carryPages' bpages' =
      let out := NativeMatchTopJobTrace.native s g u w inp carryPages bpages
      ⟨out.main.map (bucket f),bucket f out.tier⟩ := by
  apply native_map hc hb s s' hs g u u' hu w w' hw inp hlb
  apply initial_good_shape s' g u' w' (inputs f inp) carryPages' bpages' hshape
  rw [rel_pageRecords hc,hlc]
  rfl

end RebuildBound.NativeRekeyTop
