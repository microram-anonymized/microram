import RebuildBound.Proofs.SG2.Main

/-!
# SG2: the completed-A coarse-range bound at a general digit

`REPORT.tex`, Proposition "Completed-A
coarse-range bound", every odd `r`, form (CA). The conditional
`RebuildBound.SG2_of : P12ab → P12d → P12e → SG2`; package SG2fin assembles it.

Proof (helpers under `Proofs/SG2/`, adapted from `Proofs/G2/`, whose bit and
key lemmas are reused):

* `Route`: the invariants of A's binary route under the stage-by-stage schedule
  for arbitrary words: each stage writes its pairs with the merge-split of the
  stage's start state and leaves the rest alone (the omitted pairs inside the
  blank region hold no record); placement at the flat virtual destination
  `vd`; sheds per stage; the cap count `stage_count`.
* `Blind`: the route on A's keys as an `RRoute` (`sRoute`) from the nodes of the
  flat buckets `U + oldHome` (old homes lie below `(d - 1) U`), and its contract
  (`sRoute_valid`): blindness from ST5's stage lemma, monotone main, cap count.
* `Radix`: one tuple's radix split sheds `(Σ class-a arrivals - C)₊` records of
  class `a`; the radix stash is the tuples' sheds in order.
* `Range`: the reference coarse count of range `a 2^(k - I) + u` is at most
  `rRangeCount` with the truncated early list as early set, which is disjoint
  from main after stage `I`, has at most `P` keys and is fixed by the bits
  below `I` (ST5 through `route_congr`).
* `Words`: the average over the merge family's words is the average over the low
  bits and the classes (`qMass`); the old-home density and the start set.
* `Main`: the union over the `r 2^(k - I)` live ranges, P12ab per range and
  history, the density factor, P12d and P12e.

No obstacle required leaving the measure-based API: the probability space of
the spec (`SJobLaw.prob`) is a finite sum, and P12d/P12e supply the measure side.
-/

open scoped ENNReal NNReal

theorem RebuildBound.SG2_of (hab : RebuildBound.Spec.P12ab_statement)
    (hd : RebuildBound.Spec.P12d_statement) (he : RebuildBound.Spec.P12e_statement) :
    RebuildBound.Spec.SG2_statement := by
  intro g L lam D rule hg hL hv hIK
  have hr : 0 < g.r := hg.1
  have hIk : g.I < g.k := by unfold RebuildBound.Model.SepGeom.k; omega
  set m := 2 ^ (g.k - g.I) with hm
  refine (RebuildBound.FiniteLawProof.prob_le_cover_of L.prob_eq _ (fun a hist w => ∃ u < m, g.C <
    RebuildBound.Model.sRefCoarse g w
      (RebuildBound.Model.sReferenceWith rule g w (L.inputs hist w) g.canonicalOps)
      (L.inputs hist w) g.earlyCap (a * m + u)) g.r
    (fun hist w hE => RebuildBound.SG2.event_cover hr (le_of_lt hIk) hist w hE)).trans ?_
  refine (Finset.sum_le_sum fun a _ => RebuildBound.FiniteLawProof.prob_le_cover_of L.prob_eq _
    (fun u hist w => g.C <
    RebuildBound.Model.sRefCoarse g w
      (RebuildBound.Model.sReferenceWith rule g w (L.inputs hist w) g.canonicalOps)
      (L.inputs hist w) g.earlyCap (a * m + u)) m (fun hist w h => h)).trans ?_
  refine (Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun u hu =>
    RebuildBound.SG2.range_bound hL hv hab hd he hg hIk (Finset.mem_range.1 ha)
      (Finset.mem_range.1 hu)).trans ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Finset.mul_sum]
  refine le_of_eq (Finset.sum_congr rfl fun a _ => ?_)
  rw [Nat.cast_pow, Nat.cast_ofNat]
  ring
