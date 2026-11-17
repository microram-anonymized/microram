import RebuildBound.Proofs.S12.Assembly

/-!
# S12: conservation (ST1) and placement/counts (ST2), conditional on ST6

Both theorems are about the reference execution's output at a general digit
`d = r 2^e`, for any valid selection rule, any geometry in the model's
domain, inputs meeting `SInputShape` and any valid schedule of A's binary
operations. ST6 is used only for the route's placement: under any valid
schedule the route's main is the stage-by-stage schedule's (ST6), whose
records sit at their homes (`canon_route`). Conservation of the route holds
for any schedule directly (`route_SRInv`), so the finish lemmas hold for any
order of the pool.

Proof outline (files under `S12/`).
1. `Route.lean`, `Radix.lean`, `RouteHome.lean`: A's route is a permutation
   of A's main records into main, stage stashes and radix stash, keeps `N`
   buckets of `C` lanes; under the stage-by-stage schedule every record of
   bucket `v` agrees with `v` on the low `k` bits after the binary stages
   (the blank region `[0, U)` stays empty while `n ≤ K`), and the radix split
   (a permutation onto outputs and shed, output `a` of class `a` only) puts
   every main record at its home `(t mod 2^k) + 2^k · class`.
2. `Home.lean`: one home's step `gStep`: D23's insertion and A-leaf offer
   (`homeStep` with no B tier), then one B-tier round per page
   (`pagesRun`). Conservation, fullness (a home with any leftover or shed is
   full), provenance.
3. `Offers.lean`, `Insert.lean`: the offers to home `ci` act on its parts by
   `gOffA`/`gPages` and on no other home; B bucket `i`'s dedup and ways act
   on homes `i + qU` by `gStep` (with the pending sheds passed explicitly);
   so after the finish every home holds `gStep` of its initial parts.
4. `Drain.lean`: the tier is A's leftovers minus B's shed keys, B's tier
   leftovers and B's sheds.
5. `Assembly.lean`, here: per home `v`, output and union agree after
   filtering by home `v`; ST1 by counting each record in its own home; ST2's
   count from it, since a tier record of home `v` forces main `v` full.
-/

namespace RebuildBound

open RebuildBound.Model RebuildBound.D23 RebuildBound.S12

section
variable {rule : CapRule} {g : SepGeom} {wOld w : Model.LogicalKey → Nat} {inp : SInputs}
  {ops : List (Nat × Nat)}
variable (hv : rule.Valid) (hg : g.Valid) (hS : SInputShape g wOld w inp)
  (hops : List.Perm ops g.canonicalOps) (hH : RouteHome rule g w inp ops)
include hv hg hS hops hH

theorem S12.sfin_hfil {v : Nat} (hv' : v < g.N) :
    hfil g w v ((sfin rule g w inp ops).main.flatMap Bucket.recs) =
      (sHv rule g w inp ops v).m.recs := by
  rw [main_hfil g w _ (sfin_inv hv hg hS hops).len (fun j hj => sfin_home hv hg hS hops hH hj) hv',
    sfin_main hv hg hS hops hv']

/-- The output, filtered by home `v`, is the union's share of home `v`. -/
theorem S12.output_hfil {v : Nat} (hv' : v < g.N) :
    List.Perm (hfil g w v ((sfin rule g w inp ops).main.flatMap Bucket.recs ++
        (sDrain (sfin rule g w inp ops)).1.filterMap id))
      (hfil g w v inp.winners) := by
  rw [hfil_append, S12.sfin_hfil hv hg hS hops hH hv']
  refine (List.Perm.append_left _ (tier_hfil hv hg hS hops hv')).trans ?_
  refine List.Perm.trans ?_ (winners_hfil hv hg hS hops hH hv').symm
  have := gStep_perm (homeOK hv hg hS hops hH hv')
  simp only [List.append_assoc] at this ⊢
  exact this

/-- Every tier record names a full home. -/
theorem S12.tier_full : ∀ x ∈ (sDrain (sfin rule g w inp ops)).1.filterMap id,
    ((sfin rule g w inp ops).main.getD (sHome g w x) []).recs.length = g.C := by
  intro x hx
  have hv' := sHome_lt g hg.1 w x
  have hmem : x ∈ hfil g w (sHome g w x) ((sDrain (sfin rule g w inp ops)).1.filterMap id) :=
    mem_hfil.2 ⟨hx, rfl⟩
  have h1 := (tier_hfil hv hg hS hops hv').mem_iff.1 hmem
  have hne : (sHv rule g w inp ops (sHome g w x)).P ≠ [] ∨
      (∃ F ∈ (sHv rule g w inp ops (sHome g w x)).T, F ≠ []) ∨
      (sHv rule g w inp ops (sHome g w x)).I ≠ [] := by
    rcases List.mem_append.1 h1 with h1 | h1
    · rcases List.mem_append.1 h1 with h1 | h1
      · exact Or.inl (List.ne_nil_of_mem (List.mem_filter.1 h1).1)
      · obtain ⟨F, hF, hxF⟩ := List.mem_flatten.1 h1
        exact Or.inr (Or.inl ⟨F, hF, List.ne_nil_of_mem hxF⟩)
    · exact Or.inr (Or.inr (List.ne_nil_of_mem h1))
  have hf := gStep_full (homeOK hv hg hS hops hH hv') hne
  rw [← sfin_lanes hv hg hS hops hv', sfin_main hv hg hS hops hv']
  exact recs_length_of_nfree hf

end

/-- The route's placement under any valid schedule, from ST6. -/
theorem S12.routeHome_of (h6 : RebuildBound.Spec.ST6_statement) {rule : CapRule} {g : SepGeom}
    {wOld w : Model.LogicalKey → Nat} {inp : SInputs} {ops : List (Nat × Nat)} (hv : rule.Valid)
    (hg : g.Valid) (hS : SInputShape g wOld w inp) (hsched : SValidSched g ops) :
    RouteHome rule g w inp ops := by
  intro v hv' x hx
  have e := (h6 rule g wOld w inp ops hv hg hS hsched).1
  unfold srt at hx
  rw [e] at hx
  exact canon_route hv hg w hS.aLen hS.aLanes v hv' x hx

/-- **ST1, conservation**, given ST6. -/
theorem ST1_of (h6 : RebuildBound.Spec.ST6_statement) : RebuildBound.Spec.ST1_statement := by
  intro rule g wOld w inp ops hv hg hS hsched
  have hH := S12.routeHome_of h6 hv hg hS hsched
  rw [sref_output]
  rw [List.perm_iff_count]
  intro x
  rw [count_hfil g w x, count_hfil g w x inp.winners]
  exact (S12.output_hfil hv hg hS hsched.1 hH (sHome_lt g hg.1 w x)).count_eq x

/-- **ST2, placement and counts**, given ST6. -/
theorem ST2_of (h6 : RebuildBound.Spec.ST6_statement) : RebuildBound.Spec.ST2_statement := by
  intro rule g wOld w inp ops hv hg hS hsched
  have hH := S12.routeHome_of h6 hv hg hS hsched
  have hops := hsched.1
  simp only [sref_output]
  refine ⟨(sfin_inv hv hg hS hops).len, ?_, fun v hv' => sfin_home hv hg hS hops hH hv', ?_,
    S12.tier_full hv hg hS hops hH⟩
  · intro B hB
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hB
    have := sfin_lanes hv hg hS hops (v := j) (by rw [← (sfin_inv hv hg hS hops).len]; exact hj)
    rwa [getD_eq_getElem' _ _ _ hj] at this
  · intro v hv'
    have hc := (S12.output_hfil hv hg hS hops hH hv').length_eq
    rw [hfil_append, List.length_append, S12.sfin_hfil hv hg hS hops hH hv',
      ← sfin_main hv hg hS hops hv'] at hc
    unfold sHomeCount
    rw [List.countP_eq_length_filter]
    change _ = min (hfil g w v inp.winners).length g.C
    rw [← hc]
    have hle : ((sfin rule g w inp ops).main.getD v []).recs.length ≤ g.C := by
      rw [← sfin_lanes hv hg hS hops hv']
      exact recs_length_le _
    by_cases ht : hfil g w v ((sDrain (sfin rule g w inp ops)).1.filterMap id) = []
    · rw [ht, List.length_nil, Nat.add_zero, Nat.min_eq_left hle]
    · obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ ht
      have hrv : sHome g w r = v := (mem_hfil.1 hr).2
      have hfull := S12.tier_full hv hg hS hops hH r (mem_hfil.1 hr).1
      rw [hrv] at hfull
      rw [hfull]
      omega

end RebuildBound
