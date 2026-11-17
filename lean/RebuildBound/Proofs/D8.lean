import RebuildBound.Proofs.D8.Tier

/-!
# D8: T3top, resolve before compressing

`prop:top-resolution`, on the reference top finish and under `TopShape`.
Proof outline (the files of `D8/`).

1. `Step.lean`: one home's visit `hvisit` (resolution, merge, offers) as a
   function of the home's share (main bucket, leaf candidates, B-tier
   candidates); fill chain: conservation, `min` count, fullness.
2. `Dest.lean`: the destination lemma. After the clear against B bucket
   `v mod U` and the resolution, C[v], B's live direction records, the
   remaining leaf candidates and the remaining B-tier candidates are, up to
   order, the live winners homed at `v`, with distinct keys (`dest_perm`).
   It uses `TopShape`: C at its homes, B's main at its carry buckets, A and
   B distinct by key, and `tierUnsh` for the flagged B-tier tombstones.
3. `Sweep.lean`, `Bucket.lean`, `Final.lean`: `topDest` acts on the share of
   its destination by `hvisit` and on no other home (a record's home is a
   function of its key); a B bucket clears and visits its ways; after the
   sweep every home holds `Hv v` and the merge stash is the sheds in order.
4. `Home.lean`, `Fin.lean`: the final share of home `v` against the live set
   (conservation, `min(X_v, C)`, leftover count `(X_v - C)₊`).
5. `Tier.lean`: the epilogue. The leftover dedup removes nothing (sheds and
   leftovers of a home have distinct keys), so main and tier hold the live
   set once; every merge-stash and drain test counts a sublist of the
   `topExcess` leftover records.
-/

namespace RebuildBound

open RebuildBound.Model RebuildBound.D23 RebuildBound.D8

namespace D8

section out
variable {g : TopGeom} {unsh : Rec → Bool} {w : Model.LogicalKey → Nat} {inp : TopInputs}
variable (hg : g.Valid) (hs : TopShape g unsh w inp)
include hg hs

theorem out_recs {v : Nat} (hv : v < g.T) :
    (((fin g unsh w inp).main.map dropTombs).getD v []).recs = (Hv g unsh w inp v).1.m.recs := by
  rw [getD_map_dropTombs, fin_main hg hs hv]
  have e : (dropTombs (Hv g unsh w inp v).1.m).recs =
      (Hv g unsh w inp v).1.m.recs.filter (fun r => !r.tomb) := D1Lemmas.recs_map_filter _ _
  rw [e, List.filter_eq_self]
  intro r hr
  have := live_not_tomb (Hv_mem hs hv r (by simp [hr])).1
  simp [this]

theorem out_tier_recs : ((drain (fin g unsh w inp)).1.map (fun s => s.filter fun r => !r.tomb)).filterMap id =
    (drain (fin g unsh w inp)).1.filterMap id := by
  rw [filterMap_id_map_filter, List.filter_eq_self]
  intro r hr
  have := live_not_tomb (leftL_mem hg hs r ((tier_perm hg hs).mem_iff.1 hr))
  simp [this]

end out

end D8

/-- **T3top, resolve before compressing.** -/
theorem T3top : RebuildBound.Spec.T3top_statement := by
  intro g unsh w inp hg hs
  have hmain : (topReference g unsh w inp).output.main = (fin g unsh w inp).main.map dropTombs := rfl
  have htier : (topReference g unsh w inp).output.tier =
      (drain (fin g unsh w inp)).1.map (fun s => s.filter fun r => !r.tomb) := rfl
  have htrace : (topReference g unsh w inp).trace =
      topDfsTrace g w (topPool unsh inp) ++ (fin g unsh w inp).trace ++
        (drain (fin g unsh w inp)).2 := rfl
  have hF := sweep_inv hg hs
  have hlen : ((fin g unsh w inp).main.map dropTombs).length = g.T := by
    rw [List.length_map, hF.good.len]
  rw [hmain, htier, htrace]
  refine ⟨hlen, ?_, ?_, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨B0, hB0, rfl⟩ := List.mem_map.1 hB
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hB0
    have hjT : j < g.T := by rw [← hF.good.len]; exact hj
    have := Hv_lanes hs hjT
    rw [← fin_main hg hs hjT, List.getD_eq_getElem _ _ hj] at this
    simpa [dropTombs] using this
  · intro v hv r hr
    rw [out_recs hg hs hv] at hr
    exact Hv_mem hs hv r (by simp [hr])
  · intro v hv
    rw [out_recs hg hs hv, Hv_count hs hv, Nat.min_comm]
  · rw [List.perm_iff_count]
    intro x
    have hv := home_lt g w x
    rw [count_filter_home g w x, count_filter_home g w x inp.live]
    have hmf : (((fin g unsh w inp).main.map dropTombs).flatMap Bucket.recs).filter
        (fun r => topHome g w r == topHome g w x) =
        (Hv g unsh w inp (topHome g w x)).1.m.recs := by
      rw [main_filter_home _ hlen _ hv, out_recs hg hs hv]
      intro j hj r hr
      rw [out_recs hg hs hj] at hr
      exact (Hv_mem hs hj r (by simp [hr])).2
    rw [List.filter_append, hmf, out_tier_recs hg hs]
    have ht := (tier_perm hg hs).filter (fun r => topHome g w r == topHome g w x)
    rw [leftL_filter hg hs hv] at ht
    have hp := Hv_perm hs hv
    have c1 := ht.count_eq x
    have c2 := hp.count_eq x
    simp only [List.count_append] at c1 c2 ⊢
    omega
  · intro t ht h
    simp only [List.mem_append] at ht
    rcases ht with (ht | ht) | ht
    · -- the DFS tests are neither merge-stash nor drain tests
      exfalso
      unfold topDfsTrace at ht
      split at ht
      · unfold dfsTrace at ht
        obtain ⟨d, _, ht⟩ := List.mem_flatMap.1 ht
        obtain ⟨c, _, rfl⟩ := List.mem_map.1 ht
        rcases h with h | h <;> exact Test.noConfusion h
      · simp at ht
    · have := hF.trace t ht
      have hl := left_length hg hs
      simp only [List.length_append] at hl
      omega
    · have := drain_trace_le hg hs t ht
      exact this.2

end RebuildBound
