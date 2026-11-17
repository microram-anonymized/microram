import RebuildBound.Spec.DirectAddresses
import RebuildBound.Proofs.DirectMaskedRecords

namespace RebuildBound
open Model Model.DirectAddresses

private theorem map_range_lookup {α : Type*} [Inhabited α] (xs : List α) :
    (List.range xs.length).map (fun i => xs[i]!) = xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range]
    exact getElem!_pos xs i hj

/-- Reading occupied lane addresses recovers full records in lane order. -/
private theorem lanes_restore (unit : Nat) (bucket : Bucket) (read : Address → Option Rec)
    (hread : ∀ lane, lane < bucket.length → bucket[lane]! ≠ none →
      read (unit, lane) = bucket[lane]!) :
    (lanes unit bucket).map read = bucket.recs.map some := by
  unfold lanes Bucket.recs
  rw [List.map_map, List.map_filterMap_some_eq_filter_map_isSome]
  calc
    _ = ((List.range bucket.length).filter (fun lane => bucket[lane]!.isSome)).map
        (fun lane => bucket[lane]!) := by
      apply List.map_congr_left
      intro lane hl
      have hp := List.mem_filter.mp hl
      apply hread lane (List.mem_range.mp hp.1)
      exact Option.isSome_iff_ne_none.mp hp.2
    _ = bucket.filter (fun lane => lane.isSome) := by
      change ((List.range bucket.length).filter ((fun lane : Option Rec => lane.isSome) ∘
        (fun lane => bucket[lane]!))).map (fun lane => bucket[lane]!) = _
      rw [← List.filter_map, map_range_lookup]
    _ = _ := by simp

private theorem chunks_restore (masked : List Bucket) (start : Nat)
    (read : Address → Option Rec)
    (hread : ∀ unit (hu : unit < masked.length) lane,
      lane < masked[unit].length → masked[unit][lane]! ≠ none →
      read (start + unit, lane) = masked[unit][lane]!) :
    (chunksFrom start masked).map (List.map read) =
      masked.map (fun bucket => bucket.recs.map some) := by
  induction masked generalizing start with
  | nil => rfl
  | cons bucket rest ih =>
    simp only [chunksFrom, List.map_cons]
    congr 1
    · apply lanes_restore
      intro lane hl hp
      have h := hread 0 (by simp) lane hl hp
      change read (start + 0, lane) = bucket[lane]! at h
      simpa only [Nat.add_zero] using h
    · apply ih
      intro unit hu lane hl hp
      have h := hread (unit + 1) (by simpa using hu) lane hl hp
      change read (start + (unit + 1), lane) = rest[unit][lane]! at h
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem DirectAddressesRestore : Spec.DirectAddressesRestore_statement := by
  intro compare state units
  apply chunks_restore
  intro unit hu lane hl hp
  have hrel := DirectMasksRunLaneRelation compare state units
  have hs : unit < (state ++ units).length := by rwa [← hrel.length_eq]
  have hunit := hrel.get hu hs
  have hls : lane < (state ++ units)[unit].length := by simpa only [List.get_eq_getElem] using hunit.length_eq ▸ hl
  have he := hunit.get hl hls
  have ho : (DirectMasks.run compare state units)[unit][lane]! =
      (state ++ units)[unit][lane]! := by
    rw [getElem!_pos (DirectMasks.run compare state units)[unit] lane hl, getElem!_pos (state ++ units)[unit] lane hls]
    simp only [List.get_eq_getElem] at he
    rcases he with he | he
    · exact False.elim (hp ((getElem!_pos (DirectMasks.run compare state units)[unit] lane hl).trans he))
    · exact he
  simpa [lookup, List.getElem?_eq_getElem hs, List.getElem?_eq_getElem hls,
    getElem!_pos] using ho.symm

private theorem lanes_length (unit : Nat) (bucket : Bucket) :
    (lanes unit bucket).length = bucket.recs.length := by
  have h := congrArg List.length
    (lanes_restore unit bucket (fun a => bucket[a.2]!) (by intros; rfl))
  simpa only [List.length_map] using h

private theorem chunks_lengths (start : Nat) (masked : List Bucket) :
    (chunksFrom start masked).map List.length = masked.map (fun b => b.recs.length) := by
  induction masked generalizing start with
  | nil => rfl
  | cons b bs ih => simp only [chunksFrom, List.map_cons, lanes_length, ih]

theorem DirectAddressesChunks : Spec.DirectAddressesChunks_statement := by
  intro masked
  refine List.eq_iff_flatten_eq.mpr ⟨?_, ?_⟩
  · rw [← List.map_flatten]
    unfold DirectMaskedRecords.chunks
    rw [DirectMaskedRecordsIndexFlatten]
    have hlen : (masked.map (fun b => b.recs.length)).sum =
        (chunks masked).flatten.length := by
      rw [List.length_flatten, chunks, chunks_lengths]
    rw [hlen, ← List.range_eq_range']
    exact map_range_lookup _
  · simp only [List.map_map, List.length_map, Function.comp_def]
    rw [DirectMaskedRecords.chunks, DirectMaskedRecordsIndexLengths,
      chunks, chunks_lengths]

private theorem lanes_first {start : Nat} {bucket : Bucket} {a : Address}
    (h : a ∈ lanes start bucket) : a.1 = start := by
  obtain ⟨lane, _, rfl⟩ := List.mem_map.mp h
  rfl

/-- Distinct source units occupy disjoint ranges of first coordinates. -/
private theorem chunks_first {start : Nat} {masked : List Bucket} {a : Address}
    (h : a ∈ (chunksFrom start masked).flatten) : start ≤ a.1 := by
  induction masked generalizing start with
  | nil => simp [chunksFrom] at h
  | cons b bs ih =>
    simp only [chunksFrom, List.flatten_cons, List.mem_append] at h
    rcases h with h | h
    · rw [lanes_first h]
    · have := ih h
      omega

private theorem chunks_nodup (start : Nat) (masked : List Bucket) :
    (chunksFrom start masked).flatten.Nodup := by
  induction masked generalizing start with
  | nil => simp [chunksFrom]
  | cons b bs ih =>
    simp only [chunksFrom, List.flatten_cons, List.nodup_append]
    refine ⟨?_, ih _, ?_⟩
    · exact (List.nodup_range.filter _).map (by intro a b h; exact (Prod.mk.inj h).2)
    · intro a ha c hc he
      have ha := lanes_first ha
      have hc := chunks_first hc
      subst c
      omega

theorem DirectAddressesUnique : Spec.DirectAddressesUnique_statement := by
  intro units
  exact chunks_nodup 0 units

theorem DirectAddressesWinners : Spec.DirectAddressesWinners_statement := by
  intro compare units he hu
  rw [List.map_flatten]
  have hr := DirectAddressesRestore compare [] units
  simp only [List.nil_append] at hr
  rw [hr]
  simpa [DirectMasks.records, List.map_flatten, List.flatMap, Function.comp_def] using
    congrArg (List.map some) (DirectMasksWinners compare units he hu)

theorem DirectAddressesDense : Spec.DirectAddressesDense_statement := by
  intro compare units he hu i hi
  have hrestore := DirectAddressesRestore compare [] units
  have hdense := DirectMaskedRecordsRestore compare units he hu
  have hchunks := DirectAddressesChunks (DirectMasks.run compare [] units)
  have hmap : (DirectMaskedRecords.chunks (DirectMasks.run compare [] units)).map
      (List.map (fun i => lookup units (address (DirectMasks.run compare [] units) i))) =
      (DirectMaskedRecords.chunks (DirectMasks.run compare [] units)).map
        (List.map (fun i => some (DirectRecords.record (DirectMasks.records units) i))) := by
    have hc := congrArg (List.map (List.map (lookup units))) hchunks
    have hd := congrArg (List.map (List.map some)) hdense
    simp only [List.map_map, Function.comp_def, List.nil_append] at hc hd hrestore
    exact hc.trans (hrestore.trans hd.symm)
  have hflat := congrArg List.flatten hmap
  rw [← List.map_flatten, ← List.map_flatten,
    DirectMaskedRecordsValid compare units he hu] at hflat
  have hget := congrArg (fun xs => xs[i]?) hflat
  simpa [List.getElem?_map, List.getElem?_range (by simpa [DirectRecords.source] using hi),
    DirectRecords.source] using hget

theorem DirectAddressesHome : Spec.DirectAddressesHome_statement := by
  intro compare units he hu word U i hi
  rw [DirectAddressesDense compare units he hu i hi]
  rfl

-- Empty and cleared units keep their source positions; tombstones keep payloads.
private def old : Rec := ⟨LogicalKey.ofNat 7, 10, false⟩
private def tomb : Rec := ⟨LogicalKey.ofNat 7, 20, true⟩
private def other : Rec := ⟨LogicalKey.ofNat 8, 30, false⟩
private def exactCompare : DirectMasks.Comparison := fun a b => a == b
private def sample : List Bucket :=
  [[some old, none], [], [none, some other], [some tomb]]
example : chunks (DirectMasks.run exactCompare [] sample) =
    [[], [], [(2, 1)], [(3, 0)]] := by decide +kernel
example : address (DirectMasks.run exactCompare [] sample) 0 = (2, 1) := by decide +kernel
example : lookup sample (address (DirectMasks.run exactCompare [] sample) 1) =
    some tomb := by decide +kernel
-- Resume-state lanes also retain their addresses with arbitrary comparisons.
example : (chunks (DirectMasks.run (fun _ _ => false) [[none, some old]]
    [[some tomb]])).flatten.map (lookup [[none, some old], [some tomb]]) =
      [some old, some tomb] := by decide +kernel

end RebuildBound
