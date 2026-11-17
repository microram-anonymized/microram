import RebuildBound.Spec.DirectNative
import RebuildBound.Proofs.DirectMask64
import RebuildBound.Proofs.DirectMaskIndex
import RebuildBound.Proofs.DirectMaskSweep
import RebuildBound.Proofs.DirectMaskBuckets
import RebuildBound.Proofs.DirectSelect64
import RebuildBound.Proofs.DirectScan
import RebuildBound.Proofs.DirectMaskedRecords
import RebuildBound.Proofs.DirectTierOrder
import RebuildBound.Proofs.DirectDrain
import Mathlib.Tactic

/-! The native flat-prefix build is the logical masked-record build.

Both sides are brought to one closed form in the chronological winners `W`:
main is, per home, the first 64 winners with that home, and the tier is the
other winners in source order; the build fails iff the tier exceeds the
capacity. The logical side gets this from `DirectMaskedRecordsMain`,
`DirectRecordsTierOrder` and `DirectMaskedRecordsFailure`/`Success`. On the
native side the surviving addresses, read through `payloadAt`, are `W`
(`DirectNativeDedup`, `DirectMaskBucketsRun`, `DirectMasksWinners`). Winner keys
are unique, so address membership in the selection is key membership in main;
no explicit index-to-address bijection is needed. -/
namespace RebuildBound
open Model Model.DirectNative Model.DirectSelect64

theorem DirectNativeDedup : Spec.DirectNativeDedup_statement := by
  intro compare unit data masks units hu hb
  rw [DirectMask64Run, hb, DirectMaskIndexComplete compare unit units hu,
    DirectMaskSweepComplete]

/-! ### The closed form -/

/-- Per home, the first 64 winners with that home. -/
private def winnersMain (U : Nat) (word : Model.LogicalKey → Nat) (W : List Rec) : List (List Rec) :=
  (List.range U).map fun h => (W.filter fun r => DirectPrefix.cachedHome word U r == h).take 64

/-- The winners outside main, in source order. -/
private def winnersTier (U : Nat) (word : Model.LogicalKey → Nat) (W : List Rec) : List Rec :=
  W.filter fun r => r.key ∉ (winnersMain U word W).flatten.map Rec.key

/-- The closed form shared by both builds. -/
private def closed (capacity U : Nat) (word : Model.LogicalKey → Nat) (W : List Rec) :
    Option (List (List Rec) × List Rec) :=
  if (winnersTier U word W).length ≤ capacity
  then some (winnersMain U word W, winnersTier U word W) else none

/-! ### Logical side -/

private theorem logical_closed (compare : DirectMasks.Comparison) (digit output U : Nat)
    (word : Model.LogicalKey → Nat) (us : List Bucket) (hU : 0 < U)
    (he : DirectMasks.ExactComparison compare) (hu : ∀ u ∈ us, (u.recs.map Rec.key).Nodup) :
    DirectMaskedRecords.build compare digit output U word us =
      closed (DirectDrain.tierCapacity digit output) U word
        (DirectPrefix.winners (DirectMasks.records us)) := by
  -- Any successful build has the closed-form main and tier.
  have shape : ∀ d o m t, DirectMaskedRecords.build compare d o U word us = some (m, t) →
      m = winnersMain U word (DirectPrefix.winners (DirectMasks.records us)) ∧
      t = winnersTier U word (DirectPrefix.winners (DirectMasks.records us)) := by
    intro d o m t hs
    have hm := DirectMaskedRecordsMain compare d o U word us m t hU he hu hs
    refine ⟨hm, ?_⟩
    rw [DirectRecordsTierOrder d o U word _ _ m t hU
      (DirectMaskedRecordsValid compare us he hu) hs, hm]
    rfl
  -- The tier length is the excess, read off a build with exactly that capacity.
  set E := DirectB.excess 64 (DirectGroups.groups U
    (DirectRecords.home (DirectMasks.records us) word U)
    (DirectRecords.source (DirectMasks.records us)))
  have hE : (winnersTier U word (DirectPrefix.winners (DirectMasks.records us))).length = E := by
    obtain ⟨⟨m, t⟩, hs⟩ : ∃ p, DirectMaskedRecords.build compare 1 E U word us = some p := by
      refine Option.ne_none_iff_exists'.mp fun h => ?_
      have := (DirectMaskedRecordsFailure compare 1 E U word us hU he hu).mp h
      simp [DirectDrain.tierCapacity, DirectCapacity.producerCapacity] at this
      exact Nat.lt_irrefl E this
    obtain ⟨-, rfl⟩ := shape _ _ _ _ hs
    exact (DirectMaskedRecordsSuccess compare 1 E U word us _ _ hU he hu hs).2.2.2.1
  unfold closed
  cases hb : DirectMaskedRecords.build compare digit output U word us with
  | none =>
    have := (DirectMaskedRecordsFailure compare digit output U word us hU he hu).mp hb
    rw [ite_eq_right (by omega)]
  | some p =>
    obtain ⟨m, t⟩ := p
    have hle := (DirectMaskedRecordsSuccess compare digit output U word us m t hU he hu hb).2.2.2.2
    obtain ⟨rfl, rfl⟩ := shape _ _ _ _ hb
    rw [ite_eq_left hle]

/-! ### Lanes and addresses -/

private theorem lanes_and_ofLanes (m : BitVec 64) (f : Nat → Bool) :
    lanes (m &&& ofLanes f) = (lanes m).filter f := by
  unfold lanes
  rw [List.filter_filter]
  refine List.filter_congr fun l hl => ?_
  have hl : l < 64 := List.mem_range.mp hl
  rw [BitVec.getLsbD_and, getLsbD_ofLanes]
  simp [hl, Bool.and_comm]

/-- Masking every source with a lane predicate filters its addresses. -/
private theorem addresses_and (masks : List (BitVec 64)) (f : Nat → Nat → Bool) :
    addresses (masks.mapIdx fun s m => m &&& ofLanes (f s)) =
      (addresses masks).map (List.filter fun a => f a.1 a.2) := by
  refine List.ext_getElem (by simp [addresses]) fun i h1 h2 => ?_
  simp [addresses, lanes_and_ofLanes, List.filter_map, Function.comp_def]

private theorem filterMap_ite {α β : Type} (p : α → Bool) (f : α → β) (l : List α) :
    l.filterMap (fun a => if p a then some (f a) else none) = (l.filter p).map f := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases hp : p a <;> simp [hp, ih]

/-- Addresses read through the payloads are the lane lists' records. -/
private theorem addresses_recs (data : Nat → DirectMask64.Payload) (masks : List (BitVec 64)) :
    (addresses masks).map (List.map (payloadAt data)) =
      (DirectMask64.buckets data masks).map Bucket.recs := by
  refine List.ext_getElem (by simp [addresses, DirectMask64.buckets]) fun i h1 h2 => ?_
  simp only [addresses, DirectMask64.buckets, DirectMask64.bucket, List.getElem_map,
    List.getElem_mapIdx, Bucket.recs, lanes, List.map_map, List.filterMap_map]
  exact (filterMap_ite _ _ _).symm

/-- A flat array's records are its units' records. -/
private theorem records_flatten (X : List (List Bucket)) :
    DirectMasks.records X.flatten = DirectMasks.records (X.map List.flatten) := by
  unfold DirectMasks.records
  induction X with
  | nil => rfl
  | cons u X ih =>
    simp only [List.flatten_cons, List.flatMap_append, List.map_cons, List.flatMap_cons, ih]
    simp only [List.flatMap_def, Bucket.recs, List.filterMap_flatten]
    rfl

/-- A destination holding a short list in its lowest lanes reads back that list. -/
private theorem dest_recs {α β : Type} (l : List α) (f : α → β) (hl : l.length ≤ 64) :
    ((List.range 64).map fun d => l[d]?).filterMap (Option.map f) = l.map f := by
  have hd : (List.range 64).map (fun d => l[d]?) =
      l.map some ++ List.replicate (64 - l.length) none := by
    refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_range, List.getElem_append, List.length_map]
    split_ifs with hi
    · simp [hi]
    · simp [Nat.le_of_not_lt hi]
  rw [hd, List.filterMap_append, List.filterMap_map]
  simp

/-- Filtering out a selection by address is filtering out its records by key,
when the records of `A` have unique keys. -/
private theorem filter_not_mem_map {α : Type} [BEq α] [LawfulBEq α] (f : α → Rec) (A S : List α)
    (hS : ∀ a ∈ S, a ∈ A) (hk : ((A.map f).map Rec.key).Nodup) :
    (A.filter fun a => a ∉ S).map f =
      (A.map f).filter fun r => r.key ∉ (S.map f).map Rec.key := by
  rw [List.filter_map]
  congr 1
  refine List.filter_congr fun a ha => ?_
  rw [List.map_map] at hk
  simp only [Function.comp_apply, List.map_map, decide_eq_decide]
  constructor
  · intro h hmem
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hmem
    exact h (List.inj_on_of_nodup_map hk (hS b hb) ha he ▸ hb)
  · intro h hmem
    exact h (List.mem_map.mpr ⟨a, hmem, rfl⟩)

/-! ### Native side -/

private theorem native_closed (digit output U : Nat) (word : Model.LogicalKey → Nat)
    (data : Nat → DirectMask64.Payload) (D : List (BitVec 64))
    (hk : ((DirectMasks.records (DirectMask64.buckets data D)).map Rec.key).Nodup) :
    (drainCount (DirectDrain.tierCapacity digit output)
        (selectHomes (homeMask U word data) D (List.range U)).1).map (fun _ =>
      ((selectHomes (homeMask U word data) D (List.range U)).2.map
          (fun out => out.1.filterMap (Option.map (payloadAt data))),
        (addresses (selectHomes (homeMask U word data) D (List.range U)).1).flatten.map
          (payloadAt data))) =
      closed (DirectDrain.tierCapacity digit output) U word
        (DirectMasks.records (DirectMask64.buckets data D)) := by
  set hm := homeMask U word data with hhm
  set W := DirectMasks.records (DirectMask64.buckets data D) with hWdef
  set A := (addresses D).flatten with hAdef
  have hA : A.map (payloadAt data) = W := by
    rw [hAdef, List.map_flatten, addresses_recs]
    rfl
  -- One home's selection: the first 64 surviving addresses with that home.
  have hsel : ∀ h, selected hm D h =
      (A.filter fun a => DirectPrefix.cachedHome word U (payloadAt data a) == h).take 64 := by
    intro h
    unfold selected
    rw [DirectScanSelected, show (D.mapIdx fun s m => m &&& hm s h) =
      D.mapIdx fun s m => m &&& ofLanes
        ((fun s lane => DirectPrefix.cachedHome word U (data s lane) == h) s) from rfl,
      addresses_and, ← List.filter_flatten]
    rfl
  have hmain : ∀ h, (selected hm D h).map (payloadAt data) =
      (W.filter fun r => DirectPrefix.cachedHome word U r == h).take 64 := by
    intro h
    rw [hsel, List.map_take, ← hA, List.filter_map]
    rfl
  have hlen : ∀ h, (selected hm D h).length ≤ 64 := fun h => by
    rw [hsel]; exact List.length_take_le _ _
  -- Distinct homes have disjoint lane masks.
  have hdisj : ∀ s h h', h ∈ List.range U → h' ∈ List.range U → h ≠ h' →
      hm s h &&& hm s h' = 0 := by
    intro s h h' _ _ hne
    apply BitVec.eq_of_getLsbD_eq
    intro l _
    simp only [hhm, homeMask, BitVec.getLsbD_and, getLsbD_ofLanes]
    by_cases hc : DirectPrefix.cachedHome word U (data s l) = h
    · simp [hc, hne]
    · simp [hc]
  obtain ⟨h2, h1⟩ := DirectSelect64Homes hm D (List.range U) List.nodup_range hdisj
  set S := (List.range U).flatMap (selected hm D) with hSdef
  have hmainEq : (selectHomes hm D (List.range U)).2.map
      (fun out => out.1.filterMap (Option.map (payloadAt data))) = winnersMain U word W := by
    rw [h2, List.map_map]
    refine List.map_congr_left fun h _ => ?_
    simp only [Function.comp_apply]
    rw [(DirectSelect64Home hm D h).1, dest_recs _ _ (hlen h), hmain]
  have hSA : ∀ a ∈ S, a ∈ A := by
    intro a ha
    obtain ⟨h, _, ha⟩ := List.mem_flatMap.mp ha
    rw [hsel] at ha
    exact (List.mem_filter.mp (List.mem_of_mem_take ha)).1
  have hS : S.map (payloadAt data) = (winnersMain U word W).flatten := by
    rw [hSdef, List.map_flatMap]
    unfold winnersMain
    simp only [hmain]
    rfl
  have htier : (addresses (selectHomes hm D (List.range U)).1).flatten.map (payloadAt data) =
      winnersTier U word W := by
    rw [h1, ← List.filter_flatten]
    unfold winnersTier
    rw [← hS, ← hA]
    exact filter_not_mem_map _ A S hSA (by rw [hA]; exact hk)
  have hl : (addresses (selectHomes hm D (List.range U)).1).flatten.length =
      (winnersTier U word W).length := by
    rw [← htier, List.length_map]
  rw [DirectSelect64Drain, DirectDrainRunExact _ _ [] (Nat.zero_le _), List.nil_append, hl,
    hmainEq, htier]
  unfold closed
  split_ifs <;> rfl

theorem DirectNativeBuild : Spec.DirectNativeBuild_statement := by
  intro compare digit output U unit word data masks units hU he hu hk hb
  have hus : ∀ u ∈ units.map List.flatten, ((Bucket.recs u).map Rec.key).Nodup := by
    simpa using hk
  have hW : DirectMasks.records (DirectMask64.buckets data
      (DirectMask64.runRange compare data unit masks 0
        (DirectMaskIndex.pairs unit units.length))) =
      DirectPrefix.winners (DirectMasks.records (units.map List.flatten)) := by
    rw [DirectNativeDedup compare unit data masks units hu hb, records_flatten,
      DirectMaskBucketsRun]
    exact DirectMasksWinners compare _ he hus
  rw [logical_closed compare digit output U word _ hU he hus, ← hW]
  exact native_closed digit output U word data _ (by rw [hW]; exact DirectPrefixUnique _)

end RebuildBound
