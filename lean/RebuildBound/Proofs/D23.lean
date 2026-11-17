import RebuildBound.Proofs.D23.Assembly

/-!
# D23: conservation (T1) and placement/counts (T2)

Both theorems are about the reference execution's output, for any valid
selection rule and inputs meeting `InputValid`.

Proof outline.
1. `Route.lean`: A's route is a permutation of A's main records into main
   and stashes, keeps `2U` buckets of `C` lanes, and leaves every main record
   at its home (`routeA_inv`, `routeA_home`; the stage invariant `SInv`).
2. `Home.lean`: one home's insertion and offers as a function `homeStep` of
   its parts (main bucket, A candidates, B tier candidates, sheds), with
   conservation (`homeStep_perm`), fullness (`homeStep_full`: a home with any
   leftover or shed is full, since offers never lower occupancy) and
   provenance (`homeStep_mem`).
3. `Finish.lean`: `insertBucket i` acts on homes `i` and `i + U` by `homeStep`
   and on no other home, because a record's home is a function of its key;
   so after `finish` every home holds `homeStep` of its initial parts
   (`finish_inv`).
4. `Drain.lean`: the tier is A's leftovers minus B's shed keys, B's tier
   leftovers and B's sheds (`drain_perm`).
5. `Assembly.lean`: per home `v`, output and union agree after filtering by
   home `v` (`tier_filter`, `winners_filter`); T1 follows by counting each
   record in its own home. T2's count follows from T1: home `v` holds
   `|main v| + |tier ∩ v|` union records, and `tier ∩ v ≠ ∅` forces main `v`
   full.
-/

namespace RebuildBound

open RebuildBound.Model RebuildBound.D23

section
variable {rule : CapRule} {g : Geom} {TA TB : Nat} {wOld w : Model.LogicalKey → Nat} {inp : Inputs}
variable (hv : rule.Valid) (hI : InputValid g TA TB wOld w inp)
include hv hI

/-- The output, filtered by home `v`, is the union's share of home `v`. -/
theorem D23.output_filter {v : Nat} (hv' : v < g.homes) :
    List.Perm (((fin rule g w inp).main.flatMap Bucket.recs ++
        (drain (fin rule g w inp)).1.filterMap id).filter (fun r => home g w r == v))
      (inp.winners.filter (fun r => home g w r == v)) := by
  rw [List.filter_append, main_filter_home (fin rule g w inp).main (fin_inv hv hI).len
    (fun j hj => fin_home hv hI hj) hv']
  refine (List.Perm.append_left _ (tier_filter hv hI hv')).trans ?_
  rw [fin_main hv hI hv']
  refine List.Perm.trans ?_ (winners_filter hv hI hv').symm
  have := homeStep_perm (homeOK hv hI hv')
  simp only [List.append_assoc] at this ⊢
  exact this

/-- Every tier record names a full home. -/
theorem D23.tier_full : ∀ r ∈ (drain (fin rule g w inp)).1.filterMap id,
    ((fin rule g w inp).main.getD (home g w r) []).recs.length = g.C := by
  intro r hr
  have hv' := home_lt g w r
  have hmem : r ∈ (((drain (fin rule g w inp)).1.filterMap id).filter
      (fun x => home g w x == home g w r)) := List.mem_filter.2 ⟨hr, by simp⟩
  have h1 := (tier_filter hv hI hv').mem_iff.1 hmem
  have hne : (Hv rule g w inp (home g w r)).P ≠ [] ∨ (Hv rule g w inp (home g w r)).T ≠ [] ∨
      (Hv rule g w inp (home g w r)).I ≠ [] := by
    rcases List.mem_append.1 h1 with h1 | h1
    · rcases List.mem_append.1 h1 with h1 | h1
      · exact Or.inl (List.ne_nil_of_mem (List.mem_filter.1 h1).1)
      · exact Or.inr (Or.inl (List.ne_nil_of_mem h1))
    · exact Or.inr (Or.inr (List.ne_nil_of_mem h1))
  have hf := homeStep_full (homeOK hv hI hv') hne
  rw [← fin_lanes hv hI hv', fin_main hv hI hv']
  exact recs_length_of_nfree hf

end

/-- **T1, conservation.** -/
theorem T1 : RebuildBound.Spec.T1_statement := by
  intro rule g TA TB wOld w inp hv hI
  rw [reference_output]
  rw [List.perm_iff_count]
  intro x
  rw [count_filter_home g w x, count_filter_home g w x inp.winners]
  exact (D23.output_filter hv hI (home_lt g w x)).count_eq x

/-- **T2, placement and counts.** -/
theorem T2 : RebuildBound.Spec.T2_statement := by
  intro rule g TA TB wOld w inp hv hI
  simp only [reference_output]
  refine ⟨(fin_inv hv hI).len, ?_, fun v hv' => fin_home hv hI hv', ?_, D23.tier_full hv hI⟩
  · intro B hB
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hB
    have := fin_lanes hv hI (v := j) (by rw [← (fin_inv hv hI).len]; exact hj)
    rwa [getD_eq_getElem' _ _ _ hj] at this
  · intro v hv'
    have hc := (D23.output_filter hv hI hv').length_eq
    rw [List.filter_append, List.length_append, main_filter_home (fin rule g w inp).main
      (fin_inv hv hI).len (fun j hj => fin_home hv hI hj) hv'] at hc
    unfold homeCount
    rw [List.countP_eq_length_filter, ← hc]
    have hle : ((fin rule g w inp).main.getD v []).recs.length ≤ g.C := by
      rw [← fin_lanes hv hI hv']
      have := recs_length_add_nfree ((fin rule g w inp).main.getD v [])
      unfold Bucket.recs; omega
    by_cases ht : (((drain (fin rule g w inp)).1.filterMap id).filter
        (fun r => home g w r == v)) = []
    · rw [ht, List.length_nil, Nat.add_zero, Nat.min_eq_left hle]
    · obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ ht
      have hrv : home g w r = v := by simpa using (List.mem_filter.1 hr).2
      have hfull := D23.tier_full hv hI r (List.mem_filter.1 hr).1
      rw [hrv] at hfull
      rw [hfull]
      omega

end RebuildBound
