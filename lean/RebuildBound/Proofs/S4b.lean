import RebuildBound.Proofs.S4b.Route
import RebuildBound.Proofs.S4b.Drain

/-!
# S4b: insertion stash and output tier at a general digit (ST4b, conditional on ST6)

Both bounds hold for the reference execution of every valid schedule: every
insertion-trace quantity and every drain-trace quantity is at most
`sHomeExcess = Σ_v (X_v - C)₊` of the complete union. A first failure at
`.insertion` (resp. `.drain`) is a trace entry whose quantity exceeds the
capacity, hence the capacity is below `sHomeExcess`.

* `S4b/Basic`: `HomeOK` (a main bucket in good standing at its home), `Blocks`
  (a key shut out of a full bucket), the counting lemma `count_main`: distinct
  union keys, each absent from its full home, number at most `sHomeExcess`;
  and `RouteOut`, what the rest of the job needs from A's route.
* `S4b/Route`: A's route (under ST6) delivers `RouteOut`: every main record
  sits at its home, buckets have `C` lanes, and main with the stashes and the
  radix stash is a permutation of A's main, so buckets and the swept pool are
  distinct by key.
* `S4b/Offers`, `S4b/Finish`, `S4b/Insert`, `S4b/Whole`: the finish invariant
  `GInv`. A record shed by a fill, or left over by an offer, is shut out of a
  full home; A's offer leaves a full home unchanged, B's tier offer (one round
  per page) keeps it full and adds only B-tier keys. Each of the `d` ways of a
  B bucket is one step of the invariant. Hence the insertion stash is
  distinct B-main records shut out of full homes whenever it is tested.
* `S4b/Drain`: the drain's quantities are prefix sums of the leftovers, then
  the deduplicated leftovers plus the insertion stash; each is a list of
  distinct keys shut out of full homes. This argument does not depend on the
  order of the pool.
-/

theorem RebuildBound.ST4b_of (h6 : RebuildBound.Spec.ST6_statement) :
    RebuildBound.Spec.ST4b_statement := by
  intro rule g wOld w inp ops hv hg hI hs
  dsimp only
  have ro := RebuildBound.S4b.routeOut_of_st6 h6 hv hg hI hs
  obtain ⟨hins, hdr⟩ := RebuildBound.S4b.reference_bounds hg hI ro
  constructor
  · intro hff
    obtain ⟨e, he, het, hex⟩ := RebuildBound.S4b.sFirstFailure_mem hff
    rw [het] at hex
    simp only [RebuildBound.Model.SepGeom.capOf] at hex
    exact Nat.lt_of_lt_of_le hex (hins e he het)
  · intro hff
    obtain ⟨e, he, het, hex⟩ := RebuildBound.S4b.sFirstFailure_mem hff
    rw [het] at hex
    simp only [RebuildBound.Model.SepGeom.capOf] at hex
    exact Nat.lt_of_lt_of_le hex (hdr e he het)
