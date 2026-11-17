import RebuildBound.Proofs.NativeMatchLanes
import RebuildBound.Proofs.NativeMatchTrace
import RebuildBound.Proofs.KeyRelabel.Core

namespace RebuildBound.NativeRekeyLocal
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeMatchLanesProof

 def rec (f : LogicalKey → LogicalKey) (r : Rec) : Rec := {r with key := f r.key}
 def bucket (f : LogicalKey → LogicalKey) (b : Bucket) : Bucket := b.map (Option.map (rec f))
 def page (f : LogicalKey → LogicalKey) (p : Page) : Page := (rec f ∘ p.1,p.2)

 theorem wide_congr (s s' t t' : Keys) (sm tm : Mask)
    (hs : ∀ i : Slot, sm.getLsbD i.val = true → s i = s' i)
    (ht : ∀ i : Slot, tm.getLsbD i.val = true → t i = t' i) :
    wideMatch s sm t tm = wideMatch s' sm t' tm := by
  have hr : realKeys s sm = realKeys s' sm := by
    apply List.map_congr_left
    intro i hi
    exact hs i (List.mem_filter.mp hi).2
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  apply Bool.eq_iff_iff.mpr
  rw [wide_lanes s t sm tm ⟨i,hi⟩,wide_lanes s' t' sm tm ⟨i,hi⟩]
  constructor <;> rintro ⟨hm,h⟩
  · exact ⟨hm, by simpa only [ht ⟨i,hi⟩ hm,hr] using h⟩
  · exact ⟨hm, by simpa only [ht ⟨i,hi⟩ hm,hr] using h⟩

 theorem page_bucket (f : LogicalKey → LogicalKey) (p : Page) :
    (page f p).bucket = bucket f p.bucket := by
  simp only [Page.bucket,DirectMask64.bucket,page,bucket,List.map_map,Function.comp_apply]
  apply List.map_congr_left
  intro i hi
  by_cases hm : p.2.getLsbD i = true <;> simp [hm]

 theorem bucket_recs (f : LogicalKey → LogicalKey) (b : Bucket) :
    (bucket f b).recs = b.recs.map (rec f) := by
  induction b with
  | nil => rfl
  | cons lane rest ih => cases lane <;> simp_all [bucket,Bucket.recs]

 theorem page_filter (f : LogicalKey → LogicalKey) (p : Page) (h h' : Rec → Bool)
    (hh : ∀ r, h' (rec f r) = h r) :
    (page f p).filter h' = page f (p.filter h) := by
  simp only [Page.filter,page,Function.comp_apply,hh]

 theorem native_page (f : LogicalKey → LogicalKey) (s s' : LogicalKey → Stored)
    (h : ∀ key, s' (f key) = s key) (a b : Page) :
    nativePage s' (page f a) (page f b) = page f (nativePage s a b) := by
  have hk (p : Page) : storedKeys s' (page f p).1 = storedKeys s p.1 := by
    funext i
    exact h (p.1 i.val).key
  unfold nativePage
  rw [hk a,hk b]
  rfl

 theorem native_matched (f : LogicalKey → LogicalKey) (s s' : LogicalKey → Stored)
    (h : ∀ key, s' (f key) = s key) (a b : Page) :
    nativeMatchedPage s' (page f a) (page f b) = page f (nativeMatchedPage s a b) := by
  have hk (p : Page) : storedKeys s' (page f p).1 = storedKeys s p.1 := by
    funext i
    exact h (p.1 i.val).key
  unfold nativeMatchedPage
  rw [hk a,hk b]
  rfl

 theorem bucket_getD (f : LogicalKey → LogicalKey) (b : Bucket) (i : Nat) :
    (bucket f b).getD i none = (b.getD i none).map (rec f) := by
  cases he : b[i]? <;> simp [bucket,List.getD_eq_getElem?_getD,List.getElem?_map,he]

 theorem bucket_mask (f : LogicalKey → LogicalKey) (b : Bucket) :
    (Page.ofBucket (bucket f b)).2 = (Page.ofBucket b).2 := by
  change maskOfBits (fun i => ((bucket f b).getD i.val none).isSome) =
    maskOfBits (fun i => (b.getD i.val none).isSome)
  congr 1
  funext i
  rw [bucket_getD]
  simp only [Option.isSome_map]

 theorem bucket_live (f : LogicalKey → LogicalKey) (b : Bucket) (i : Slot)
    (hi : (Page.ofBucket b).2.getLsbD i.val = true) :
    (Page.ofBucket (bucket f b)).1 i.val = rec f ((Page.ofBucket b).1 i.val) := by
  have hi' : (b.getD i.val none).isSome = true := by
    change (maskOfBits (fun j => (b.getD j.val none).isSome)).getLsbD i.val = true at hi
    rw [maskOfBits_get] at hi
    exact hi
  simp only [Page.ofBucket,bucket_getD]
  cases he : b.getD i.val none with
  | none =>
      change (b.getD i.val none).isSome = true at hi'
      rw [he] at hi'
      contradiction
  | some r => rfl

 theorem source_mask (f : LogicalKey → LogicalKey) (s s' : LogicalKey → Stored)
    (h : ∀ key, s' (f key) = s key) (a : Bucket) (b : Page) :
    wideMatch (storedKeys s' (Page.ofBucket (bucket f a)).1)
      (Page.ofBucket (bucket f a)).2 (storedKeys s' (page f b).1) (page f b).2 =
    wideMatch (storedKeys s (Page.ofBucket a).1)
      (Page.ofBucket a).2 (storedKeys s b.1) b.2 := by
  rw [bucket_mask]
  apply wide_congr
  · intro i hi
    simp only [storedKeys,bucket_live f a i hi,rec]
    exact h _
  · intro i hi
    exact h _

 theorem mem_page (p : Page) (r : Rec) : r ∈ p.bucket.recs ↔
    ∃ i : Slot, p.2.getLsbD i.val = true ∧ p.1 i.val = r := by
  simp only [Page.bucket,DirectMask64.bucket,Bucket.recs,List.mem_filterMap,List.mem_map]
  constructor
  · rintro ⟨_,⟨i,hi,rfl⟩,hr⟩
    by_cases hm : p.2.getLsbD i = true
    · simp only [hm,ite_true,id_eq,Option.some.injEq] at hr
      exact ⟨⟨i,List.mem_range.mp hi⟩,hm,hr⟩
    · simp [hm] at hr
  · rintro ⟨i,hm,hr⟩
    exact ⟨some r,⟨i.val,List.mem_range.mpr i.isLt,by simp [hm,hr]⟩,rfl⟩

 theorem page_filter_active (f : LogicalKey → LogicalKey) (p : Page) (h h' : Rec → Bool)
    (hh : ∀ i : Slot, p.2.getLsbD i.val = true → h' (rec f (p.1 i.val)) = h (p.1 i.val)) :
    (page f p).filter h' = page f (p.filter h) := by
  apply Prod.ext
  · rfl
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    change (p.2 &&& maskOfBits (fun j => h' (rec f (p.1 j.val)))).getLsbD i =
      (p.2 &&& maskOfBits (fun j => h (p.1 j.val))).getLsbD i
    rw [BitVec.getLsbD_and,BitVec.getLsbD_and,maskOfBits_get _ ⟨i,hi⟩,maskOfBits_get _ ⟨i,hi⟩]
    by_cases hm : p.2.getLsbD i = true
    · simp [hm,hh ⟨i,hi⟩ hm]
    · simp [hm]

 theorem contains_local (f : LogicalKey → LogicalKey) (keys gone : List LogicalKey)
    (h : Set.InjOn f {k | k ∈ keys}) (hg : gone ⊆ keys) (k : LogicalKey) (hk : k ∈ keys) :
    (gone.map f).contains (f k) = gone.contains k := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem,List.mem_map]
  constructor
  · rintro ⟨j,hj,hjk⟩
    exact (h (hg hj) hk hjk) ▸ hj
  · intro hm
    exact ⟨k,hm,rfl⟩

 theorem page_remove (f : LogicalKey → LogicalKey) (p : Page) (gone : List LogicalKey)
    (h : Set.InjOn f {k | k ∈ p.bucket.recs.map Rec.key})
    (hg : gone ⊆ p.bucket.recs.map Rec.key) :
    (page f p).filter (fun r => !(gone.map f).contains r.key) =
      page f (p.filter fun r => !gone.contains r.key) := by
  apply page_filter_active
  intro i hi
  dsimp only [rec]
  rw [contains_local f _ gone h hg _ (List.mem_map.mpr ⟨p.1 i.val,
    (mem_page _ _).mpr ⟨i,hi,rfl⟩,rfl⟩)]


 theorem native_bucket_page (f : LogicalKey → LogicalKey) (s s' : LogicalKey → Stored)
    (h : ∀ key, s' (f key) = s key) (a : Bucket) (b : Page) :
    nativePage s' (Page.ofBucket (bucket f a)) (page f b) =
      page f (nativePage s (Page.ofBucket a) b) := by
  unfold nativePage
  rw [source_mask f s s' h]
  rfl

 theorem native_bucket_matched (f : LogicalKey → LogicalKey) (s s' : LogicalKey → Stored)
    (h : ∀ key, s' (f key) = s key) (a : Bucket) (b : Page) :
    nativeMatchedPage s' (Page.ofBucket (bucket f a)) (page f b) =
      page f (nativeMatchedPage s (Page.ofBucket a) b) := by
  unfold nativeMatchedPage
  rw [source_mask f s s' h]
  rfl

 theorem filter_sub (p : Page) (h : Rec → Bool) :
    (p.filter h).bucket.recs ⊆ p.bucket.recs := by
  intro r hr
  obtain ⟨i,hi,hkey⟩ := (mem_page _ _).mp hr
  apply (mem_page _ _).mpr
  refine ⟨i,?_,hkey⟩
  change (p.2 &&& _).getLsbD i.val = true at hi
  rw [BitVec.getLsbD_and] at hi
  exact (Bool.and_eq_true_iff.mp hi).1

 theorem native_page_sub (s : LogicalKey → Stored) (a b : Page) :
    (nativePage s a b).bucket.recs ⊆ b.bucket.recs := by
  intro r hr
  obtain ⟨i,hi,hkey⟩ := (mem_page _ _).mp hr
  apply (mem_page _ _).mpr
  refine ⟨i,?_,hkey⟩
  change (b.2 &&& _).getLsbD i.val = true at hi
  rw [BitVec.getLsbD_and] at hi
  exact (Bool.and_eq_true_iff.mp hi).1

 theorem native_matched_sub (s : LogicalKey → Stored) (a b : Page) :
    (nativeMatchedPage s a b).bucket.recs ⊆ b.bucket.recs := by
  intro r hr
  obtain ⟨i,hi,hkey⟩ := (mem_page _ _).mp hr
  apply (mem_page _ _).mpr
  refine ⟨i,?_,hkey⟩
  exact ((wide_lanes _ _ _ _ i).mp hi).1

 def offerCore (a : Bucket) (p : Page) (drop stale : List Rec) : Bucket × Page :=
  let result := fill a stale
  let gone := (drop ++ stale.take (stale.length - result.2.length)).map Rec.key
  (result.1,p.filter fun r => !gone.contains r.key)

 theorem offer_core (f : LogicalKey → LogicalKey) (a : Bucket) (p : Page) (drop stale : List Rec)
    (hinj : Set.InjOn f {k | k ∈ p.bucket.recs.map Rec.key})
    (hdrop : drop ⊆ p.bucket.recs) (hstale : stale ⊆ p.bucket.recs) :
    offerCore (bucket f a) (page f p) (drop.map (rec f)) (stale.map (rec f)) =
      (bucket f (offerCore a p drop stale).1,page f (offerCore a p drop stale).2) := by
  let result := fill a stale
  let gone := (drop ++ stale.take (stale.length - result.2.length)).map Rec.key
  have hg : gone ⊆ p.bucket.recs.map Rec.key := by
    intro k hk
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hk
    apply List.mem_map.mpr
    refine ⟨r,?_,rfl⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact hdrop hr
    · exact hstale (List.mem_of_mem_take hr)
  have hremove := page_remove f p gone hinj hg
  unfold offerCore
  have hf := KeyRelabel.fill_map (rec f) a stale
  change fill (bucket f a) (stale.map (rec f)) = (bucket f result.1,result.2.map (rec f)) at hf
  rw [hf]
  simp only [List.length_map,← List.map_take,← List.map_append,List.map_map]
  have hgone : (gone.map f) =
      (drop ++ stale.take (stale.length - result.2.length)).map (Rec.key ∘ rec f) := by
    simp only [gone,List.map_map]
    rfl
  rw [← hgone]
  change (bucket f result.1, (page f p).filter (fun r => !(gone.map f).contains r.key)) = _
  rw [hremove]

 theorem group_offer (f : LogicalKey → LogicalKey) (s s' : LogicalKey → Stored)
    (h : ∀ key, s' (f key) = s key) (a : Bucket) (p : Page) (home home' : Rec → Bool)
    (hh : ∀ r, home' (rec f r) = home r)
    (hinj : Set.InjOn f {k | k ∈ p.bucket.recs.map Rec.key}) :
    groupOfferNative s' (bucket f a) home' (page f p) =
      (bucket f (groupOfferNative s a home p).1,page f (groupOfferNative s a home p).2) := by
  let target := p.filter home
  let drop := (nativeMatchedPage s (Page.ofBucket a) target).bucket.recs
  let stale := (nativePage s (Page.ofBucket a) target).bucket.recs
  have ht : (page f p).filter home' = page f target := page_filter f p home home' hh
  have hd : (nativeMatchedPage s' (Page.ofBucket (bucket f a)) ((page f p).filter home')).bucket.recs =
      drop.map (rec f) := by
    rw [ht,native_bucket_matched f s s' h,page_bucket,bucket_recs]
  have hs : (nativePage s' (Page.ofBucket (bucket f a)) ((page f p).filter home')).bucket.recs =
      stale.map (rec f) := by
    rw [ht,native_bucket_page f s s' h,page_bucket,bucket_recs]
  change offerCore (bucket f a) (page f p)
    (nativeMatchedPage s' (Page.ofBucket (bucket f a)) ((page f p).filter home')).bucket.recs
    (nativePage s' (Page.ofBucket (bucket f a)) ((page f p).filter home')).bucket.recs =
    (bucket f (offerCore a p drop stale).1,page f (offerCore a p drop stale).2)
  rw [hd,hs]
  exact offer_core f a p drop stale hinj
    (fun _ hr => filter_sub p home (native_matched_sub s (Page.ofBucket a) target hr))
    (fun _ hr => filter_sub p home (native_page_sub s (Page.ofBucket a) target hr))

 theorem group_offer_nodup (f : LogicalKey → LogicalKey) (s s' : LogicalKey → Stored)
    (h : ∀ key, s' (f key) = s key) (a : Bucket) (p : Page) (home home' : Rec → Bool)
    (hh : ∀ r, home' (rec f r) = home r)
    (hu : (p.bucket.recs.map (fun r => f r.key)).Nodup) :
    groupOfferNative s' (bucket f a) home' (page f p) =
      (bucket f (groupOfferNative s a home p).1,page f (groupOfferNative s a home p).2) := by
  apply group_offer f s s' h a p home home' hh
  have hu' : ((p.bucket.recs.map Rec.key).map f).Nodup := by
    simpa only [List.map_map,Function.comp_def] using hu
  exact List.inj_on_of_nodup_map hu'

 theorem grouped_offer (f : LogicalKey → LogicalKey) (s s' : LogicalKey → Stored)
    (h : ∀ key, s' (f key) = s key) (a : Bucket) (pages : List Page) (home home' : Rec → Bool)
    (hh : ∀ r, home' (rec f r) = home r)
    (hu : ∀ p ∈ pages, (p.bucket.recs.map (fun r => f r.key)).Nodup) :
    groupedOfferNative s' (bucket f a) home' (pages.map (page f)) =
      (bucket f (groupedOfferNative s a home pages).1,
        (groupedOfferNative s a home pages).2.map (page f)) := by
  induction pages generalizing a with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,groupedOfferNative]
    rw [group_offer_nodup f s s' h a p home home' hh (hu p List.mem_cons_self)]
    rw [ih _ (fun q hq => hu q (List.mem_cons_of_mem _ hq))]

/-- Raw ghost payloads may differ in dummy lanes. Only occupied lanes are used. -/
structure PageRel (f : LogicalKey → LogicalKey) (p q : Page) : Prop where
  mask : q.2 = p.2
  payload : ∀ i : Slot, p.2.getLsbD i.val = true → q.1 i.val = rec f (p.1 i.val)

 theorem rel_bucket {f : LogicalKey → LogicalKey} {p q : Page} (h : PageRel f p q) :
    q.bucket = bucket f p.bucket := by
  simp only [Page.bucket,DirectMask64.bucket,bucket,List.map_map]
  apply List.map_congr_left
  intro i hi
  rw [h.mask]
  by_cases hm : p.2.getLsbD i = true
  · simp [hm,h.payload ⟨i,List.mem_range.mp hi⟩ hm]
  · simp [hm]

 theorem rel_ofBucket (f : LogicalKey → LogicalKey) (b : Bucket) :
    PageRel f (Page.ofBucket b) (Page.ofBucket (bucket f b)) :=
  ⟨bucket_mask f b,bucket_live f b⟩

 theorem rel_ofRecords (f : LogicalKey → LogicalKey) (rs : List Rec) :
    PageRel f (Page.ofRecords rs) (Page.ofRecords (rs.map (rec f))) := by
  have h := rel_ofBucket f (rs.map some ++ List.replicate (64-rs.length) none)
  simpa only [Page.ofRecords,bucket,List.map_append,List.map_map,List.map_replicate,
    Option.map_none,List.length_map,Function.comp_def,Option.map_some] using h

 theorem rel_filter_active {f : LogicalKey → LogicalKey} {p q : Page} (h : PageRel f p q)
    (home home' : Rec → Bool)
    (hh : ∀ i : Slot, p.2.getLsbD i.val=true → home' (q.1 i.val)=home (p.1 i.val)) :
    PageRel f (p.filter home) (q.filter home') := by
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    change (q.2 &&& maskOfBits _).getLsbD i = (p.2 &&& maskOfBits _).getLsbD i
    rw [BitVec.getLsbD_and,BitVec.getLsbD_and,maskOfBits_get _ ⟨i,hi⟩,
      maskOfBits_get _ ⟨i,hi⟩,h.mask]
    by_cases hm : p.2.getLsbD i = true
    · rw [hh ⟨i,hi⟩ hm]
    · simp [hm]
  · intro i hi
    change (p.2 &&& _).getLsbD i.val = true at hi
    rw [BitVec.getLsbD_and] at hi
    exact h.payload i (Bool.and_eq_true_iff.mp hi).1

 theorem rel_filter {f : LogicalKey → LogicalKey} {p q : Page} (h : PageRel f p q)
    (home home' : Rec → Bool) (hh : ∀ r, home' (rec f r) = home r) :
    PageRel f (p.filter home) (q.filter home') := by
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    change (q.2 &&& maskOfBits _).getLsbD i = (p.2 &&& maskOfBits _).getLsbD i
    rw [BitVec.getLsbD_and,BitVec.getLsbD_and,maskOfBits_get _ ⟨i,hi⟩,
      maskOfBits_get _ ⟨i,hi⟩,h.mask]
    by_cases hm : p.2.getLsbD i = true
    · rw [h.payload ⟨i,hi⟩ hm,hh]
    · simp [hm]
  · intro i hi
    change (p.2 &&& _).getLsbD i.val = true at hi
    rw [BitVec.getLsbD_and] at hi
    exact h.payload i (Bool.and_eq_true_iff.mp hi).1

 theorem rel_wide {f : LogicalKey → LogicalKey} {a a' b b' : Page}
    (ha : PageRel f a a') (hb : PageRel f b b') (s s' : LogicalKey → Stored)
    (hs : ∀ k, s' (f k) = s k) :
    wideMatch (storedKeys s' a'.1) a'.2 (storedKeys s' b'.1) b'.2 =
      wideMatch (storedKeys s a.1) a.2 (storedKeys s b.1) b.2 := by
  rw [ha.mask,hb.mask]
  apply wide_congr
  · intro i hi
    change s' (a'.1 i.val).key = s (a.1 i.val).key
    rw [ha.payload i hi]
    exact hs _
  · intro i hi
    change s' (b'.1 i.val).key = s (b.1 i.val).key
    rw [hb.payload i hi]
    exact hs _

 theorem rel_native_page {f : LogicalKey → LogicalKey} {a a' b b' : Page}
    (ha : PageRel f a a') (hb : PageRel f b b') (s s' : LogicalKey → Stored)
    (hs : ∀ k, s' (f k) = s k) :
    PageRel f (nativePage s a b) (nativePage s' a' b') := by
  constructor
  · change b'.2 &&& _ = b.2 &&& _
    rw [rel_wide ha hb s s' hs,hb.mask]
  · intro i hi
    change (b.2 &&& _).getLsbD i.val = true at hi
    rw [BitVec.getLsbD_and] at hi
    exact hb.payload i (Bool.and_eq_true_iff.mp hi).1

 theorem rel_native_matched {f : LogicalKey → LogicalKey} {a a' b b' : Page}
    (ha : PageRel f a a') (hb : PageRel f b b') (s s' : LogicalKey → Stored)
    (hs : ∀ k, s' (f k) = s k) :
    PageRel f (nativeMatchedPage s a b) (nativeMatchedPage s' a' b') := by
  constructor
  · exact rel_wide ha hb s s' hs
  · intro i hi
    exact hb.payload i ((wide_lanes _ _ _ _ i).mp hi).1

 theorem rel_pool {f : LogicalKey → LogicalKey} {sources sources' targets targets' : List Page}
    (hsources : List.Forall₂ (PageRel f) sources sources')
    (htargets : List.Forall₂ (PageRel f) targets targets') (s s' : LogicalKey → Stored)
    (hs : ∀ k, s' (f k) = s k) :
    List.Forall₂ (PageRel f) (poolNative s sources targets) (poolNative s' sources' targets') := by
  induction hsources generalizing targets targets' with
  | nil => exact htargets
  | cons ha hrest ih =>
    apply ih
    induction htargets with
    | nil => exact List.Forall₂.nil
    | cons hb htail ih => exact List.Forall₂.cons (rel_native_page ha hb s s' hs) ih

 theorem rel_remove {f : LogicalKey → LogicalKey} {p q : Page} (hp : PageRel f p q)
    (gone : List LogicalKey) (hinj : Set.InjOn f {k | k ∈ p.bucket.recs.map Rec.key})
    (hg : gone ⊆ p.bucket.recs.map Rec.key) :
    PageRel f (p.filter (fun r => !gone.contains r.key))
      (q.filter (fun r => !(gone.map f).contains r.key)) := by
  apply rel_filter_active hp
  intro i hi
  rw [hp.payload i hi]
  dsimp only [rec]
  rw [contains_local f _ gone hinj hg _ (List.mem_map.mpr ⟨p.1 i.val,
    (mem_page _ _).mpr ⟨i,hi,rfl⟩,rfl⟩)]

 theorem rel_offer_core {f : LogicalKey → LogicalKey} {p q : Page} (hp : PageRel f p q)
    (a : Bucket) (drop stale : List Rec)
    (hinj : Set.InjOn f {k | k ∈ p.bucket.recs.map Rec.key})
    (hdrop : drop ⊆ p.bucket.recs) (hstale : stale ⊆ p.bucket.recs) :
    (offerCore (bucket f a) q (drop.map (rec f)) (stale.map (rec f))).1 =
        bucket f (offerCore a p drop stale).1 ∧
      PageRel f (offerCore a p drop stale).2
        (offerCore (bucket f a) q (drop.map (rec f)) (stale.map (rec f))).2 := by
  let result := fill a stale
  let gone := (drop ++ stale.take (stale.length - result.2.length)).map Rec.key
  have hg : gone ⊆ p.bucket.recs.map Rec.key := by
    intro k hk
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hk
    apply List.mem_map.mpr
    refine ⟨r,?_,rfl⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact hdrop hr
    · exact hstale (List.mem_of_mem_take hr)
  have hremove := rel_remove hp gone hinj hg
  unfold offerCore
  have hf := KeyRelabel.fill_map (rec f) a stale
  change fill (bucket f a) (stale.map (rec f)) = (bucket f result.1,result.2.map (rec f)) at hf
  rw [hf]
  simp only [List.length_map,← List.map_take,← List.map_append,List.map_map]
  have hgone : (gone.map f) =
      (drop ++ stale.take (stale.length - result.2.length)).map (Rec.key ∘ rec f) := by
    simp only [gone,List.map_map]
    rfl
  rw [← hgone]
  exact ⟨rfl,hremove⟩

 theorem rel_group_offer {f : LogicalKey → LogicalKey} {p q : Page} (hp : PageRel f p q)
    (s s' : LogicalKey → Stored) (hs : ∀ key, s' (f key) = s key)
    (a : Bucket) (home home' : Rec → Bool) (hh : ∀ r, home' (rec f r) = home r)
    (hu : (p.bucket.recs.map (fun r => f r.key)).Nodup) :
    (groupOfferNative s' (bucket f a) home' q).1 = bucket f (groupOfferNative s a home p).1 ∧
      PageRel f (groupOfferNative s a home p).2 (groupOfferNative s' (bucket f a) home' q).2 := by
  let target := p.filter home
  let drop := (nativeMatchedPage s (Page.ofBucket a) target).bucket.recs
  let stale := (nativePage s (Page.ofBucket a) target).bucket.recs
  have ht := rel_filter hp home home' hh
  have hd : (nativeMatchedPage s' (Page.ofBucket (bucket f a)) (q.filter home')).bucket.recs =
      drop.map (rec f) := by
    rw [rel_bucket (rel_native_matched (rel_ofBucket f a) ht s s' hs),bucket_recs]
  have hst : (nativePage s' (Page.ofBucket (bucket f a)) (q.filter home')).bucket.recs =
      stale.map (rec f) := by
    rw [rel_bucket (rel_native_page (rel_ofBucket f a) ht s s' hs),bucket_recs]
  change (offerCore (bucket f a) q
    (nativeMatchedPage s' (Page.ofBucket (bucket f a)) (q.filter home')).bucket.recs
    (nativePage s' (Page.ofBucket (bucket f a)) (q.filter home')).bucket.recs).1 =
    bucket f (offerCore a p drop stale).1 ∧ PageRel f (offerCore a p drop stale).2
      (offerCore (bucket f a) q
      (nativeMatchedPage s' (Page.ofBucket (bucket f a)) (q.filter home')).bucket.recs
      (nativePage s' (Page.ofBucket (bucket f a)) (q.filter home')).bucket.recs).2
  rw [hd,hst]
  apply rel_offer_core hp a drop stale
  · have hu' : ((p.bucket.recs.map Rec.key).map f).Nodup := by
      simpa only [List.map_map,Function.comp_def] using hu
    exact List.inj_on_of_nodup_map hu'
  · exact fun _ hr => filter_sub p home (native_matched_sub s (Page.ofBucket a) target hr)
  · exact fun _ hr => filter_sub p home (native_page_sub s (Page.ofBucket a) target hr)


 theorem rel_grouped_offer {f : LogicalKey → LogicalKey} {pages pages' : List Page}
    (hpages : List.Forall₂ (PageRel f) pages pages')
    (s s' : LogicalKey → Stored) (hs : ∀ key, s' (f key) = s key)
    (a : Bucket) (home home' : Rec → Bool) (hh : ∀ r, home' (rec f r) = home r)
    (hu : ∀ p ∈ pages, (p.bucket.recs.map (fun r => f r.key)).Nodup) :
    (groupedOfferNative s' (bucket f a) home' pages').1 =
        bucket f (groupedOfferNative s a home pages).1 ∧
      List.Forall₂ (PageRel f) (groupedOfferNative s a home pages).2
        (groupedOfferNative s' (bucket f a) home' pages').2 := by
  induction hpages generalizing a with
  | nil => exact ⟨rfl,List.Forall₂.nil⟩
  | @cons p q ps qs hp hrest ih =>
    have hfirst := rel_group_offer hp s s' hs a home home' hh (hu p List.mem_cons_self)
    have hremaining := ih (groupOfferNative s a home p).1
      (fun pg hpg => hu pg (List.mem_cons_of_mem p hpg))
    simp only [groupedOfferNative]
    rw [hfirst.1]
    exact ⟨hremaining.1,List.Forall₂.cons hfirst.2 hremaining.2⟩

 theorem records_remove (f : LogicalKey → LogicalKey) (rs : List Rec) (gone : List LogicalKey)
    (hinj : Set.InjOn f {k | k ∈ rs.map Rec.key}) (hg : gone ⊆ rs.map Rec.key) :
    (rs.map (rec f)).filter (fun r => !(gone.map f).contains r.key) =
      (rs.filter (fun r => !gone.contains r.key)).map (rec f) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro r hr
  change (!(gone.map f).contains (f r.key)) = (!gone.contains r.key)
  rw [contains_local f _ gone hinj hg _ (List.mem_map.mpr ⟨r,hr,rfl⟩)]

 def sfin (f : LogicalKey → LogicalKey) (st : SFin) : SFin :=
  ⟨st.main.map (bucket f),st.ins.map (rec f),st.leaves.map (List.map (rec f)),
    st.bcopy.map (List.map (rec f)),st.trace⟩

 theorem records_getD (f : LogicalKey → LogicalKey) (rs : List (List Rec)) (i : Nat) :
    (rs.map (List.map (rec f))).getD i [] = (rs.getD i []).map (rec f) :=
  List.getD_map rs [] (List.map (rec f))

 theorem buckets_getD (f : LogicalKey → LogicalKey) (bs : List Bucket) (i : Nat) :
    (bs.map (bucket f)).getD i [] = bucket f (bs.getD i []) :=
  List.getD_map bs [] (bucket f)

 theorem rel_pageRecords {f : LogicalKey → LogicalKey} {ps qs : List Page}
    (h : List.Forall₂ (PageRel f) ps qs) : pageRecords qs = (pageRecords ps).map (rec f) := by
  induction h with
  | nil => rfl
  | cons hp hrest ih =>
    simp only [pageRecords,List.flatMap_cons,List.map_append] at *
    rw [rel_bucket hp,bucket_recs,ih]

 theorem rel_offerAGroups {f : LogicalKey → LogicalKey} {ps qs : List Page}
    (hp : List.Forall₂ (PageRel f) ps qs)
    (s s' : LogicalKey → Stored) (hs : ∀ key, s' (f key) = s key)
    (g : SepGeom) (w w' : LogicalKey → Nat) (hw : ∀ key, w' (f key)=w key)
    (ci : Nat) (st : SFin)
    (hu : ∀ p ∈ ps, (p.bucket.recs.map (fun r => f r.key)).Nodup) :
    (offerAGroupsNative s' g w' ci (sfin f st) qs).1 =
        sfin f (offerAGroupsNative s g w ci st ps).1 ∧
      List.Forall₂ (PageRel f) (offerAGroupsNative s g w ci st ps).2
        (offerAGroupsNative s' g w' ci (sfin f st) qs).2 := by
  have hh : ∀ r, (sHome g w' (rec f r)==ci) = (sHome g w r==ci) := by
    intro r
    simp only [sHome,rec,hw]
  have hr := rel_grouped_offer hp s s' hs (st.main.getD ci [])
    (fun r => sHome g w r==ci) (fun r => sHome g w' r==ci) hh hu
  constructor
  · simp only [offerAGroupsNative,sfin,buckets_getD,hr.1,rel_pageRecords hr.2,List.map_set]
  · simpa only [offerAGroupsNative,sfin,buckets_getD] using hr.2


 theorem offerB (f : LogicalKey → LogicalKey) (s s' : LogicalKey → Stored)
    (hs : ∀ key, s' (f key) = s key) (g : SepGeom)
    (w w' : LogicalKey → Nat) (hw : ∀ key, w' (f key)=w key)
    (ci : Nat) (st : SFin) (pg : Nat)
    (hu : ((st.bcopy.getD pg []).map (fun r => f r.key)).Nodup) :
    offerBNative s' g w' ci (sfin f st) pg = sfin f (offerBNative s g w ci st pg) := by
  let records := st.bcopy.getD pg []
  let fc := records.filter (fun r => sHome g w r==ci)
  let B := (nativePage s (Page.ofRecords fc) (Page.ofBucket (st.main.getD ci []))).bucket
  let result := fill B fc
  let gone := (fc.take (fc.length-result.2.length)).map Rec.key
  have hh : ∀ r, (sHome g w' (rec f r)==ci) = (sHome g w r==ci) := by
    intro r
    simp only [sHome,rec,hw]
  have hfc : (records.map (rec f)).filter (fun r => sHome g w' r==ci) = fc.map (rec f) :=
    KeyRelabel.map_filter _ _ _ hh records
  have hb : (nativePage s' (Page.ofRecords (fc.map (rec f)))
      (Page.ofBucket (bucket f (st.main.getD ci [])))).bucket = bucket f B :=
    rel_bucket (rel_native_page (rel_ofRecords f fc) (rel_ofBucket f (st.main.getD ci [])) s s' hs)
  have hf : fill (bucket f B) (fc.map (rec f)) =
      (bucket f result.1,result.2.map (rec f)) := KeyRelabel.fill_map (rec f) B fc
  have hinj : Set.InjOn f {k | k ∈ records.map Rec.key} := by
    have hu' : ((records.map Rec.key).map f).Nodup := by
      simpa only [records,List.map_map,Function.comp_def] using hu
    exact List.inj_on_of_nodup_map hu'
  have hg : gone ⊆ records.map Rec.key := by
    intro k hk
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hk
    exact List.mem_map.mpr ⟨r,List.mem_of_mem_filter (List.mem_of_mem_take hr),rfl⟩
  have hr := records_remove f records gone hinj hg
  have hgone : ((fc.map (rec f)).take ((fc.map (rec f)).length -
      (result.2.map (rec f)).length)).map Rec.key = gone.map f := by
    simp only [List.length_map,←List.map_take,List.map_map,gone]
    rfl
  simp only [offerBNative,sfin,records_getD,buckets_getD]
  rw [hfc,hb,hf]
  simp only [hgone]
  rw [hr]
  simp only [List.map_set]
  rfl

end RebuildBound.NativeRekeyLocal
