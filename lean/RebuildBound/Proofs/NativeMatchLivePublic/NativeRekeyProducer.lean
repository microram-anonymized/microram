import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyLocal
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyRouting
import RebuildBound.Proofs.KeyRelabel.Direct
import RebuildBound.Spec.NativeMatch.Hierarchy
set_option maxHeartbeats 1600000
namespace RebuildBound.NativeRekeyProducer
open Model Spec NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchPrefixProducer
open NativeRekeyLocal

def ActiveRel (f : LogicalKey → LogicalKey) (d d' : Nat → DirectMask64.Payload)
    (m : List Mask) : Prop :=
  ∀ i j, (m.getD i 0).getLsbD j = true → d' i j = rec f (d i j)

theorem prefix_step_eq (f : LogicalKey → LogicalKey) (s s' : LogicalKey → Stored)
    (hs : ∀ k, s' (f k) = s k) (d d' : Nat → DirectMask64.Payload)
    (unit : Nat) (m : List Mask) (hr : ActiveRel f d d' m) (p : Nat) :
    prefixStep s' d' unit m p = prefixStep s d unit m p := by
  let pair := DirectMaskIndex.decode unit p
  have he : wideMatch (storedKeys s' (d' pair.2)) (m.getD pair.2 0)
        (storedKeys s' (d' pair.1)) (m.getD pair.1 0) =
      wideMatch (storedKeys s (d pair.2)) (m.getD pair.2 0)
        (storedKeys s (d pair.1)) (m.getD pair.1 0) := by
    apply wide_congr
    · intro i hi
      simp only [storedKeys, hr _ _ hi, rec]
      exact hs _
    · intro i hi
      simp only [storedKeys, hr _ _ hi, rec]
      exact hs _
  exact congrArg (fun w => m.set pair.1 (m.getD pair.1 0 &&& ~~~w)) he

theorem prefix_step_rel (f : LogicalKey → LogicalKey) (s : LogicalKey → Stored)
    (d d' : Nat → DirectMask64.Payload) (unit : Nat) (m : List Mask)
    (hr : ActiveRel f d d' m) (p : Nat) :
    ActiveRel f d d' (prefixStep s d unit m p) := by
  intro i j hij
  apply hr i j
  simp only [prefixStep, D6.getD_set_eq] at hij
  split at hij
  · rename_i hh
    rcases hh with ⟨rfl,_⟩
    exact (Bool.and_eq_true_iff.mp (by simpa only [BitVec.getLsbD_and] using hij)).1
  · exact hij

theorem prefix_run_eq (f : LogicalKey → LogicalKey) (s s' : LogicalKey → Stored)
    (hs : ∀ k, s' (f k) = s k) (d d' : Nat → DirectMask64.Payload)
    (unit : Nat) (m : List Mask) (hr : ActiveRel f d d' m) (ops : List Nat) :
    prefixRun s' d' unit m ops = prefixRun s d unit m ops ∧
      ActiveRel f d d' (prefixRun s d unit m ops) := by
  induction ops generalizing m with
  | nil =>
    simp only [prefixRun,List.foldl_nil]
    exact ⟨trivial,hr⟩
  | cons p ops ih =>
    simp only [prefixRun,List.foldl_cons]
    have he := prefix_step_eq f s s' hs d d' unit m hr p
    have H := ih (prefixStep s d unit m p) (prefix_step_rel f s d d' unit m hr p)
    constructor
    · exact (congrArg (fun ms => ops.foldl (prefixStep s' d' unit) ms) he).trans H.1
    · exact H.2

theorem masks_rekey (f : LogicalKey → LogicalKey) (units : List Bucket) :
    masks (units.map (bucket f)) = masks units := by
  simp only [masks,pages,List.map_map]
  apply List.map_congr_left
  intro b hb
  exact bucket_mask f b

theorem initial_active (f : LogicalKey → LogicalKey) (units : List Bucket) :
    ActiveRel f (data units) (data (units.map (bucket f))) (masks units) := by
  intro i j hij
  have hj : j < 64 := by
    by_contra hn
    rw [BitVec.getLsbD_of_ge _ _ (by omega)] at hij
    contradiction
  have H : PageRel f ((pages units).getD i default)
      ((pages (units.map (bucket f))).getD i default) := by
    simp only [pages,List.getD,List.getElem?_map]
    cases he : units[i]? with
    | none =>
      constructor
      · rfl
      · intro k hk
        change (0 : Mask).getLsbD k.val = true at hk
        simp [BitVec.getLsbD] at hk
    | some b => exact rel_ofBucket f b
  apply H.payload ⟨j,hj⟩
  have hm : (masks units).getD i 0 = ((pages units).getD i default).2 :=
    List.getD_map (pages units) (default : Page) Prod.snd
  rw [hm] at hij
  exact hij

theorem buckets_active (f : LogicalKey → LogicalKey) (d d' : Nat → DirectMask64.Payload)
    (m : List Mask) (hr : ActiveRel f d d' m) :
    DirectMask64.buckets d' m = (DirectMask64.buckets d m).map (bucket f) := by
  apply List.ext_getElem
  · simp [DirectMask64.buckets]
  · intro i hi hi'
    have hm : i < m.length := by simpa [DirectMask64.buckets] using hi
    simp only [DirectMask64.buckets,List.getElem_map,List.getElem_mapIdx]
    change Page.bucket (d' i,m[i]) = bucket f (Page.bucket (d i,m[i]))
    apply rel_bucket
    refine ⟨rfl,?_⟩
    intro j hj
    exact hr i j.val (by simpa only [List.getD_eq_getElem m 0 hm] using hj)

theorem masked_rekey (f : LogicalKey → LogicalKey) (s s' : LogicalKey → Stored)
    (hs : ∀ k, s' (f k) = s k) (units : List Bucket) :
    masked s' (units.map (bucket f)) = (masked s units).map (bucket f) := by
  unfold masked
  rw [masks_rekey,List.length_map]
  have H := prefix_run_eq f s s' hs (data units) (data (units.map (bucket f))) 1
    (masks units) (initial_active f units) (List.range (DirectMaskIndex.pairs 1 units.length))
  rw [H.1]
  exact buckets_active f _ _ _ H.2


open Model.DirectJob

theorem records_buckets (f : LogicalKey → LogicalKey) (bs : List Bucket) :
    DirectMasks.records (bs.map (bucket f)) = (DirectMasks.records bs).map (rec f) := by
  simp only [DirectMasks.records,List.flatMap_map,List.map_flatMap]
  apply List.flatMap_congr
  intro b hb
  exact bucket_recs f b

theorem chunks_buckets (f : LogicalKey → LogicalKey) (bs : List Bucket) :
    DirectMaskedRecords.chunks (bs.map (bucket f)) = DirectMaskedRecords.chunks bs := by
  simp only [DirectMaskedRecords.chunks,List.map_map]
  congr 1
  apply List.map_congr_left
  intro b hb
  simp only [bucket_recs,List.length_map,Function.comp_apply]

theorem chunks_flatten (bs : List Bucket) :
    (DirectMaskedRecords.chunks bs).flatten = List.range (DirectMasks.records bs).length := by
  rw [DirectMaskedRecords.chunks,DirectMaskedRecordsIndexFlatten]
  simp [DirectMasks.records,List.length_flatMap,←List.range_eq_range']

theorem records_get (f : LogicalKey → LogicalKey) (rs : List Rec) (i : Nat)
    (hi : i < rs.length) : (rs.map (rec f))[i]! = rec f rs[i]! := by
  simp only [getElem!_pos (rs.map (rec f)) i (by simpa only [List.length_map] using hi),
    List.getElem_map,getElem!_pos rs i hi]

theorem groups_rekey (f : LogicalKey → LogicalKey) (w w' : LogicalKey → Nat)
    (hw : ∀ k, w' (f k) = w k) (U : Nat) (rs : List Rec) (xs : List Nat)
    (hv : ∀ i∈xs, i < rs.length) :
    DirectGroups.groups U (fun i => DirectPrefix.cachedHome w' U (rs.map (rec f))[i]!) xs =
      DirectGroups.groups U (fun i => DirectPrefix.cachedHome w U rs[i]!) xs := by
  unfold DirectGroups.groups
  apply List.map_congr_left
  intro j hj
  apply List.filter_congr
  intro i hi
  dsimp only
  rw [records_get f rs i (hv i hi)]
  simp only [DirectPrefix.cachedHome,rec,hw]

theorem nativeBuildB_rekey (f : LogicalKey → LogicalKey) (s s' : LogicalKey → Stored)
    (hs : ∀ k, s' (f k) = s k) (g : Geometry) (w w' : LogicalKey → Nat)
    (hw : ∀ k, w' (f k) = w k) (inp : DirectJob.Inputs) :
    nativeBuildB s' g w' (NativeRekeyRouting.inputs f inp) = (nativeBuildB s g w inp).map (NativeRekeyRouting.table f) := by
  let bs := masked s inp.units
  let rs := DirectMasks.records bs
  let cs := DirectMaskedRecords.chunks bs
  let homes := DirectGroups.groups g.U (fun i => DirectPrefix.cachedHome w g.U rs[i]!) cs.flatten
  have hindex (i : Nat) (hi : i∈cs.flatten) : i < rs.length := by
    exact List.mem_range.mp (by simpa only [cs,rs,chunks_flatten] using hi)
  have hm : DirectGroups.groups g.U
      (fun i => DirectPrefix.cachedHome w' g.U (rs.map (rec f))[i]!) cs.flatten = homes :=
    groups_rekey f w w' hw g.U rs cs.flatten hindex
  change nativeBuildB s' g w' ⟨_,_,inp.units.map (bucket f)⟩ = _
  simp only [nativeBuildB,masked_rekey f s s' hs,records_buckets,chunks_buckets]
  change ((match drainBounded Phase.produceB (bSite g) g.bCapacity 0 []
        (cs.map fun source => DirectRemaining.run 64 source _ ) with
      | .error e => .error e
      | .ok tier => .ok ⟨(DirectB.main 64 _).map (fun xs => xs.map (fun i => (rs.map (rec f))[i]!)),
          tier.map (fun i => (rs.map (rec f))[i]!)⟩) : Except CheckEvent Table) = _
  rw [hm]
  cases hd : drainBounded Phase.produceB (bSite g) g.bCapacity 0 []
      (cs.map fun source => DirectRemaining.run 64 source homes) with
  | error e => rfl
  | ok tier =>
    have hmain : ∀ xs∈DirectB.main 64 homes, ∀ i∈xs, i < rs.length := by
      intro xs hxs i hi
      obtain ⟨ys,hys,rfl⟩ := List.mem_map.mp hxs
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hys
      exact hindex i (List.mem_filter.mp (List.mem_of_mem_take hi)).1
    have htier : ∀ i∈tier, i < rs.length := by
      intro i hi
      have he := KeyRelabel.drainBounded_ok_records Phase.produceB (bSite g) g.bCapacity 0 [] _ tier hd
      simp only [List.nil_append] at he
      rw [he] at hi
      obtain ⟨xs,hxs,hi⟩ := List.mem_flatten.mp hi
      obtain ⟨source,hsource,rfl⟩ := List.mem_map.mp hxs
      rw [DirectRemainingFold] at hi
      exact hindex i (List.mem_flatten.mpr ⟨source,hsource,(List.mem_filter.mp hi).1⟩)
    change Except.ok (⟨_,_⟩ : Table) = Except.ok (NativeRekeyRouting.table f ⟨_,_⟩)
    congr 2
    · simp only [List.map_map]
      apply List.map_congr_left
      intro xs hxs
      simp only [Function.comp_apply,NativeRekeyRouting.records,List.map_map]
      apply List.map_congr_left
      intro i hi
      exact records_get f rs i (hmain xs hxs i hi)
    · simp only [NativeRekeyRouting.records,List.map_map]
      apply List.map_congr_left
      intro i hi
      exact records_get f rs i (htier i hi)

end RebuildBound.NativeRekeyProducer
