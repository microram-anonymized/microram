import RebuildBound.Spec.DirectTierOrder
import RebuildBound.Proofs.DirectRecords
import RebuildBound.Proofs.DirectRemaining
import RebuildBound.Proofs.DirectMaskedRecords
import RebuildBound.Proofs.DirectJobB

namespace RebuildBound
open Model Model.DirectRecords

theorem DirectRecordsTierOrder : Spec.DirectRecordsTierOrder_statement := by
  intro digit output U word rs chunks main tier hU hc hs
  change chunks.flatten = source rs at hc
  obtain ⟨⟨mi, ti⟩, hp, hr⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
  have hnd : chunks.flatten.Nodup := by rw [hc]; exact List.nodup_range
  have hlt : ∀ i ∈ chunks.flatten, home rs word U i < U := fun _ _ => Nat.mod_lt _ hU
  -- Main indices are source indices.
  have hsub : ∀ j ∈ mi.flatten, j ∈ source rs := fun j hj => by
    rw [← hc]
    exact (DirectProducerSuccess digit output U _ chunks mi ti hnd hlt hp).1.subset
      (List.mem_append_left _ hj)
  rw [DirectProducerExact digit output U _ chunks hnd hlt] at hp
  split_ifs at hp
  obtain ⟨hm, rfl⟩ := Prod.mk.inj (Option.some.inj hp)
  -- A record's key determines its source index, since winners have unique keys.
  have hinj : ((source rs).map (fun i => (record rs i).key)).Nodup := by
    have h := DirectPrefixUnique rs
    rwa [← DirectRecordsSource rs, List.map_map] at h
  rw [hc] at hm
  rw [DirectRemainingFold, hc, hm, ← DirectRecordsSource rs, List.filter_map,
    ← List.map_flatten, List.map_map]
  unfold DirectRemaining.clear
  congr 1
  apply List.filter_congr
  intro i hi
  simp only [Function.comp_apply, decide_eq_decide, not_iff_not, List.mem_map]
  constructor
  · exact fun h => ⟨i, h, rfl⟩
  · rintro ⟨j, hj, he⟩
    rwa [← List.inj_on_of_nodup_map hinj (hsub j hj) hi he]

theorem DirectJobBTierOrder : Spec.DirectJobBTierOrder_statement := by
  intro g word inp t hu hs
  have he := DirectJobBRefinement g word inp
  rw [hs] at he
  exact DirectRecordsTierOrder g.digit g.outputCapacity g.U word _ _ t.main t.tier
    (Nat.two_pow_pos _)
    (DirectMaskedRecordsValid DirectJob.exactCompare inp.units (fun _ _ => rfl) hu) he.symm

/-! Non-vacuity. Two homes (`U = 2`, `word = id`) each receive 64 records first;
then key 129 (home 1) arrives before key 128 (home 0). An older tombstone for key
129 opens the chronology and is superseded. Main is full and the tier holds two
records whose source order (home 1, then home 0) is not home order, which is the
order `DirectB.residual` would give; a permutation alone cannot tell them apart. -/
private def rec' (k : Nat) : Rec := ⟨LogicalKey.ofNat k, k, false⟩
private def oldTomb : Rec := ⟨LogicalKey.ofNat 129, 0, true⟩
private def fresh : List Rec :=
  (List.range 64).map (fun i => rec' (2 * i)) ++
    (List.range 64).map (fun i => rec' (2 * i + 1)) ++ [rec' 129, rec' 128]
private def sample : List Rec := oldTomb :: fresh

set_option maxRecDepth 8192 in
example : (build 1 2 2 LogicalKey.toNat sample [source sample]).map (fun p => (p.1.map List.length, p.2)) =
    some ([64, 64], [rec' 129, rec' 128]) := by decide +kernel
example : [rec' 129, rec' 128].map (DirectPrefix.cachedHome LogicalKey.toNat 2) = [1, 0] := by decide +kernel
-- The home-order residual of the same producer run lists the two records the other way.
set_option maxRecDepth 8192 in
example : (DirectB.residual 64 (DirectGroups.groups 2 (home sample LogicalKey.toNat 2) (source sample))).map
    (record sample) = [rec' 128, rec' 129] := by decide +kernel

/-- The job adapter on the same records, the tombstone in its own older unit. -/
private def sampleGeometry : DirectJob.Geometry :=
  { K := 1, digit := 1, outputHomes := 2, outputCapacity := 2, aTierCapacity := 0,
    routeCapacity := 0, radixCapacity := 0, insertionCapacity := 2, copyCapacity := 2,
    ranges := .direct }
private def sampleInputs : DirectJob.Inputs :=
  { aMain := [], aTier := [], units := [[some oldTomb], fresh.map some] }

set_option maxRecDepth 8192 in
example : ∀ u ∈ sampleInputs.units, (u.recs.map Rec.key).Nodup := by decide +kernel
set_option maxRecDepth 8192 in
example : (DirectJob.buildB sampleGeometry LogicalKey.toNat sampleInputs).toOption.map
    (fun t => (t.main.map List.length, t.tier)) = some ([64, 64], [rec' 129, rec' 128]) := by
  decide +kernel

end RebuildBound
