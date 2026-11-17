import RebuildBound.Spec.DirectMaskBuckets
import RebuildBound.Proofs.DirectMasks

/-! Physical bucket comparisons refine grouped chronological mask semantics.
The proofs need exact comparison only when invoking the existing winner law.
Native indexed scheduling, SIMD masks and layout remain separate obligations. -/
namespace RebuildBound
open Model Model.DirectMaskBuckets

private theorem pair_compose (compare : DirectMasks.Comparison)
    (first second older : Bucket) :
    DirectMasks.pair compare second (DirectMasks.pair compare first older) =
      DirectMasks.pair compare (first ++ second) older := by
  simp only [DirectMasks.pair, List.map_map, Bucket.recs,
    List.filterMap_append, List.any_append]
  congr 1
  funext lane
  simp

private theorem fold_pair (compare : DirectMasks.Comparison)
    (fresh : FlushUnit) (older : Bucket) :
    fresh.foldl (fun masked bucket => DirectMasks.pair compare bucket masked) older =
      DirectMasks.pair compare fresh.flatten older := by
  induction fresh generalizing older with
  | nil =>
    have hid : ∀ lane : Option Rec, lane.filter (fun _ => true) = lane := by
      intro lane
      cases lane <;> rfl
    simp [DirectMasks.pair, Bucket.recs, hid]
  | cons bucket fresh ih =>
    rw [List.foldl_cons, ih, List.flatten_cons, pair_compose]

theorem DirectMaskBucketsPair : Spec.DirectMaskBucketsPair_statement := by
  intro compare fresh older
  unfold pair
  simp_rw [fold_pair]
  simp only [DirectMasks.pair, List.map_flatten]

private theorem step_flatten (compare : DirectMasks.Comparison)
    (state : List FlushUnit) (fresh : FlushUnit) :
    (step compare state fresh).map List.flatten =
      DirectMasks.step compare (state.map List.flatten) fresh.flatten := by
  simp only [step, DirectMasks.step, List.map_append, List.map_cons,
    List.map_nil, List.map_map]
  congr 1
  exact List.map_congr_left (fun older _ => DirectMaskBucketsPair compare fresh older)

theorem DirectMaskBucketsRun : Spec.DirectMaskBucketsRun_statement := by
  intro compare state units
  unfold run DirectMasks.run
  rw [List.foldl_map]
  exact (List.foldl_hom (List.map List.flatten)
    (fun older fresh => (step_flatten compare older fresh).symm)).symm

private theorem fold_length (compare : DirectMasks.Comparison)
    (fresh : FlushUnit) (older : Bucket) :
    (fresh.foldl (fun masked bucket => DirectMasks.pair compare bucket masked) older).length =
      older.length := by
  rw [fold_pair, DirectMasksLanes]

private theorem pair_shape (compare : DirectMasks.Comparison)
    (fresh older : FlushUnit) :
    (pair compare fresh older).map List.length = older.map List.length := by
  simp only [pair, List.map_map]
  exact List.map_congr_left (fun bucket _ => fold_length compare fresh bucket)

theorem DirectMaskBucketsShape : Spec.DirectMaskBucketsShape_statement := by
  intro compare state units
  induction units generalizing state with
  | nil => simp [run]
  | cons fresh units ih =>
    change (run compare (step compare state fresh) units).map _ = _
    rw [ih]
    simp [step, List.map_map, pair_shape, List.append_assoc]

theorem DirectMaskBucketsWinners : Spec.DirectMaskBucketsWinners_statement := by
  intro compare units he hu
  rw [DirectMaskBucketsRun]
  apply DirectMasksWinners compare (units.map List.flatten) he
  intro bucket hb
  obtain ⟨unit, hm, rfl⟩ := List.mem_map.mp hb
  exact hu unit hm

-- Cross-bucket tombstones clear the full older record while retaining holes,
-- empty physical buckets, empty units and the newer record's complete payload.
private def old : Rec := ⟨LogicalKey.ofNat 7, 10, false⟩
private def tomb : Rec := ⟨LogicalKey.ofNat 7, 20, true⟩
private def other : Rec := ⟨LogicalKey.ofNat 8, 30, false⟩
private def exactCompare : DirectMasks.Comparison := fun a b => a == b
private def sample : List FlushUnit :=
  [[[some old, none], [], [some other]], [], [[], [none, some tomb]]]
example : DirectMasks.ExactComparison exactCompare := by intro a b; rfl
example : run exactCompare [] sample =
    [[[none, none], [], [some other]], [], [[], [none, some tomb]]] := by decide +kernel
example : DirectMasks.records ((run exactCompare [] sample).map List.flatten) =
    [other, tomb] := by decide +kernel
-- Grouped correspondence does not require exact comparison or valid units.
example : (pair (fun _ _ => true) [[none], [some tomb]] [[some other], []]).flatten =
    DirectMasks.pair (fun _ _ => true) [none, some tomb] [some other] := by
  exact DirectMaskBucketsPair _ _ _
-- Uniqueness within each physical bucket does not ensure flush-unit uniqueness.
private def malformed : FlushUnit := [[some old], [], [some tomb]]
example : ∀ bucket ∈ malformed, (bucket.recs.map Rec.key).Nodup := by decide +kernel
example : ¬ ((Bucket.recs malformed.flatten).map Rec.key).Nodup := by decide +kernel
example : DirectMasks.records ((run exactCompare [] [malformed]).map List.flatten) ≠
    DirectPrefix.winners (DirectMasks.records [malformed.flatten]) := by decide +kernel
end RebuildBound
