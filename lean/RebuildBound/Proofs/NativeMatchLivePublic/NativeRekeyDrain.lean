import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyFinish

namespace RebuildBound.NativeRekeyDrain
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeMatchJobTrace NativeRekeyLocal NativeRekeyFinish NativeMatchLanesProof

theorem class_wide (first second : Keys) (firstReal carry tier : Mask) :
    classMatch first firstReal second carry tier =
      (wideMatch second tier first firstReal,wideMatch first firstReal second carry) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    apply Bool.eq_iff_iff.mpr
    exact ((class_lanes first second firstReal carry tier ⟨i,hi⟩).1).trans
      (wide_lanes second first tier firstReal ⟨i,hi⟩).symm
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    apply Bool.eq_iff_iff.mpr
    exact ((class_lanes first second firstReal carry tier ⟨i,hi⟩).2).trans
      (wide_lanes first second firstReal carry ⟨i,hi⟩).symm

theorem rel_and {f : LogicalKey → LogicalKey} {p q : Page} (h : PageRel f p q) (mask : Mask) :
    PageRel f (p.1,p.2 &&& mask) (q.1,q.2 &&& mask) := by
  constructor
  · rw [h.mask]
  · intro i hi
    change (p.2 &&& mask).getLsbD i.val = true at hi
    rw [BitVec.getLsbD_and] at hi
    exact h.payload i (Bool.and_eq_true_iff.mp hi).1

theorem rel_class {f : LogicalKey → LogicalKey} {p p' q q' : Page}
    (hp : PageRel f p p') (hq : PageRel f q q')
    (s s' : LogicalKey → Stored) (hs : ∀ key,s' (f key)=s key) (mask : Mask) :
    PageRel f (classNative s p q (q.2 &&& ~~~mask) (q.2 &&& mask)).1
        (classNative s' p' q' (q'.2 &&& ~~~mask) (q'.2 &&& mask)).1 ∧
      PageRel f (classNative s p q (q.2 &&& ~~~mask) (q.2 &&& mask)).2
        (classNative s' p' q' (q'.2 &&& ~~~mask) (q'.2 &&& mask)).2 := by
  have hfirst := rel_wide (rel_and hq mask) hp s s' hs
  have hsecond := rel_wide hp (rel_and hq (~~~mask)) s s' hs
  simp only [classNative,class_wide]
  change wideMatch (storedKeys s' q'.1) (q'.2 &&& mask) (storedKeys s' p'.1) p'.2 =
    wideMatch (storedKeys s q.1) (q.2 &&& mask) (storedKeys s p.1) p.2 at hfirst
  change wideMatch (storedKeys s' p'.1) p'.2 (storedKeys s' q'.1) (q'.2 &&& ~~~mask) =
    wideMatch (storedKeys s p.1) p.2 (storedKeys s q.1) (q.2 &&& ~~~mask) at hsecond
  rw [hfirst,hsecond]
  exact ⟨rel_and hp _,rel_and hq _⟩

def LeftRel (f : LogicalKey → LogicalKey) (p q : Leftovers) : Prop :=
  List.Forall₂ (PageRel f) p.1 q.1 ∧ List.Forall₂ (PageRel f) p.2 q.2

theorem leftover_step {f : LogicalKey → LogicalKey} {p q : Leftovers} (h : LeftRel f p q)
    (s s' : LogicalKey → Stored) (hs : ∀ key,s' (f key)=s key)
    (classMask : Nat → Mask) (op : Nat × Nat) :
    LeftRel f (leftoverNativeStep s classMask p op) (leftoverNativeStep s' classMask q op) := by
  have hp := forall₂_getD h.1 default default (default_rel f) op.2
  have hq := forall₂_getD h.2 default default (default_rel f) op.1
  have hc := rel_class hp hq s s' hs (classMask op.1)
  exact ⟨forall₂_set h.1 _ _ hc.1 op.2,forall₂_set h.2 _ _ hc.2 op.1⟩

theorem leftover_fold {f : LogicalKey → LogicalKey} {p q : Leftovers} (h : LeftRel f p q)
    (s s' : LogicalKey → Stored) (hs : ∀ key,s' (f key)=s key)
    (classMask : Nat → Mask) (ops : List (Nat × Nat)) :
    LeftRel f (ops.foldl (leftoverNativeStep s classMask) p)
      (ops.foldl (leftoverNativeStep s' classMask) q) := by
  induction ops generalizing p q with
  | nil => exact h
  | cons op ops ih => exact ih (leftover_step h s s' hs classMask op)


def tag (f : LogicalKey → LogicalKey) (r : Rec × Bool) : Rec × Bool := (rec f r.1,r.2)

def taggedTier (f : LogicalKey → LogicalKey) (xs : List (Option (Rec × Bool))) :=
  xs.map (Option.map (tag f))

theorem tag_step (f : LogicalKey → LogicalKey)
    (acc : List (Option (Rec × Bool)) × List (STest × Nat)) (rs : List (Rec × Bool)) :
    sDrainStep (taggedTier f acc.1,acc.2) (rs.map (tag f)) =
      (taggedTier f (sDrainStep acc rs).1,(sDrainStep acc rs).2) := by
  simp only [sDrainStep,taggedTier,KeyRelabel.appendFill_map,KeyRelabel.occupied_map]

theorem tag_fold (f : LogicalKey → LogicalKey) (rs : List (List (Rec × Bool)))
    (acc : List (Option (Rec × Bool)) × List (STest × Nat)) :
    (rs.map (List.map (tag f))).foldl sDrainStep (taggedTier f acc.1,acc.2) =
      (taggedTier f (rs.foldl sDrainStep acc).1,(rs.foldl sDrainStep acc).2) := by
  induction rs generalizing acc with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons,List.foldl_cons,tag_step]
    exact ih _

theorem firstDrain_map (f : LogicalKey → LogicalKey) (st : SFin) :
    firstDrain (sfin f st) = taggedTier f (firstDrain st) := by
  have h := congrArg Prod.fst (tag_fold f
    (st.leaves.map (fun rs => rs.map (fun r => (r,true))) ++
      st.bcopy.map (fun rs => rs.map (fun r => (r,false)))) ([],[]))
  simpa only [firstDrain,sfin,taggedTier,List.map_nil,List.map_append,List.map_map,
    Function.comp_def,tag] using h

theorem eraseTags_map (f : LogicalKey → LogicalKey) (xs : List (Option (Rec × Bool))) :
    eraseTags (taggedTier f xs) = bucket f (eraseTags xs) := by
  simp only [eraseTags,taggedTier,bucket,List.map_map]
  apply List.map_congr_left
  intro x hx
  cases x <;> rfl

theorem bClassTags_map (f : LogicalKey → LogicalKey) (xs : List (Option (Rec × Bool))) :
    bClassTags (taggedTier f xs) = bucket f (bClassTags xs) := by
  simp only [bClassTags,taggedTier,bucket,List.map_map]
  apply List.map_congr_left
  intro x hx
  cases x with
  | none => rfl
  | some x => cases h : x.2 <;> simp [tag,h]

theorem drainClasses_map (f : LogicalKey → LogicalKey) (st : SFin) :
    drainClasses (firstDrain (sfin f st)) = drainClasses (firstDrain st) := by
  funext i
  simp only [firstDrain_map,drainClasses]
  rw [show (taggedTier f (firstDrain st)).drop (64*i) =
      taggedTier f ((firstDrain st).drop (64*i)) from List.map_drop.symm,bClassTags_map]
  exact bucket_mask f _


theorem bucket_pages_rel (f : LogicalKey → LogicalKey) (n : Nat) (b : Model.Bucket) :
    List.Forall₂ (PageRel f) (bucketPages n b) (bucketPages n (bucket f b)) := by
  induction n generalizing b with
  | zero => exact .nil
  | succ n ih =>
    simp only [bucketPages]
    apply List.Forall₂.cons (rel_ofBucket f b)
    simpa only [bucket,List.map_drop] using ih (b.drop 64)

theorem initial_rel (f : LogicalKey → LogicalKey) (st : SFin) (shedPages tierPages : Nat) :
    LeftRel f (drainInitial shedPages tierPages st) (drainInitial shedPages tierPages (sfin f st)) := by
  constructor
  · have h := bucket_pages_rel f shedPages (st.ins.map some)
    simpa only [drainInitial,sfin,bucket,List.map_map,Function.comp_def,Option.map_some] using h
  · simpa only [drainInitial,firstDrain_map,eraseTags_map] using
      bucket_pages_rel f tierPages (eraseTags (firstDrain st))

theorem flat_buckets_rel {f : LogicalKey → LogicalKey} {ps qs : List Page}
    (h : List.Forall₂ (PageRel f) ps qs) :
    qs.flatMap Page.bucket = bucket f (ps.flatMap Page.bucket) := by
  induction h with
  | nil => rfl
  | cons hp hrest ih =>
    simp only [List.flatMap_cons,rel_bucket hp,ih,bucket,List.map_append]

theorem drain_map (f : LogicalKey → LogicalKey) (s s' : LogicalKey → Stored)
    (hs : ∀ key,s' (f key)=s key) (shedPages tierPages : Nat) (st : SFin) :
    drainNative s' shedPages tierPages (sfin f st) =
      bucket f (drainNative s shedPages tierPages st) := by
  have h := leftover_fold (initial_rel f st shedPages tierPages) s s' hs
    (drainClasses (firstDrain st)) (leftoverPairs shedPages tierPages)
  simp only [drainNative,drainClasses_map]
  rw [flat_buckets_rel h.2,rel_pageRecords h.1]
  exact congrArg Prod.fst (KeyRelabel.fill_map (rec f) _ _)

end RebuildBound.NativeRekeyDrain
