import RebuildBound.Spec.DirectMask64

/-! 64-lane mask-word form of the prefix dedup comparison: lane bits of
`duplicateMask`, then the native task refines the flat lane-list task. -/
namespace RebuildBound
open Model Model.DirectMask64

private theorem duplicateMask_lane (compare : DirectMasks.Comparison)
    (freshData olderData : Payload) (freshMask olderMask : BitVec 64)
    (lane : Nat) (hl : lane < 64) :
    (duplicateMask compare freshData freshMask olderData olderMask).getLsbD lane =
      (olderMask.getLsbD lane && (List.range 64).any fun j =>
        freshMask.getLsbD j && compare (freshData j).key (olderData lane).key) := by
  simp only [duplicateMask, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl,
    Option.map_some, Option.getD_some, hl, decide_true, Bool.true_and]

private theorem bucket_recs_any (data : Payload) (mask : BitVec 64) (p : Rec → Bool) :
    (bucket data mask).recs.any p =
      (List.range 64).any fun j => mask.getLsbD j && p (data j) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bucket, Bucket.recs, List.filterMap_map, List.any_filterMap, List.any_eq_true,
    List.mem_range, Function.comp, id, Bool.and_eq_true]
  refine exists_congr fun j => and_congr_right fun _ => ?_
  by_cases h : mask.getLsbD j <;> simp [h]

theorem DirectMask64Pair : Spec.DirectMask64Pair_statement := by
  intro compare freshData olderData freshMask olderMask
  simp only [DirectMasks.pair, bucket_recs_any]
  simp only [bucket, List.map_map]
  apply List.map_congr_left
  intro lane hlane
  have hl : lane < 64 := List.mem_range.mp hlane
  simp only [Function.comp, pairMask, BitVec.getLsbD_and, BitVec.getLsbD_not, hl,
    decide_true, Bool.true_and, duplicateMask_lane compare freshData olderData freshMask
      olderMask lane hl]
  by_cases h : olderMask.getLsbD lane <;> simp [h, Option.filter]

private theorem mapIdx_modify {α β : Type} (F : Nat → α → β) (o : Nat) (g : α → α)
    (h : β → β) (hF : ∀ x, F o (g x) = h (F o x)) (l : List α) :
    (l.modify o g).mapIdx F = (l.mapIdx F).modify o h := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_mapIdx, List.getElem_modify]
  split
  · subst o; exact hF _
  · rfl

private theorem buckets_getD_recs (data : Nat → Payload) (masks : List (BitVec 64)) (f : Nat) :
    ((buckets data masks).getD f []).recs = (bucket (data f) (masks.getD f 0)).recs := by
  by_cases hf : f < masks.length
  · simp [buckets, List.getD_eq_getElem?_getD, hf]
  · simp [buckets, List.getD_eq_getElem?_getD, hf, bucket, Bucket.recs]

private theorem step_buckets (compare : DirectMasks.Comparison) (data : Nat → Payload)
    (unit : Nat) (masks : List (BitVec 64)) (p : Nat) :
    buckets data (step compare data unit masks p) =
      DirectMaskIndex.step compare unit (buckets data masks) p := by
  have hpair :
      DirectMasks.pair compare ((buckets data masks).getD (DirectMaskIndex.decode unit p).2 []) =
      DirectMasks.pair compare (bucket (data (DirectMaskIndex.decode unit p).2)
        (masks.getD (DirectMaskIndex.decode unit p).2 0)) := by
    funext older
    simp only [DirectMasks.pair, buckets_getD_recs]
  rw [step, DirectMaskIndex.step, hpair, buckets]
  exact mapIdx_modify _ _ _ _ (fun x => DirectMask64Pair ..) masks

theorem DirectMask64Run : Spec.DirectMask64Run_statement := by
  intro compare data unit masks begin stop
  simp only [runRange, DirectMaskIndex.runRange]
  induction List.range' begin (stop - begin) generalizing masks with
  | nil => rfl
  | cons p ps ih => simp only [List.foldl_cons, ← step_buckets, ih]

end RebuildBound
