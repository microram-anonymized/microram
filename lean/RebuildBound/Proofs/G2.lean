import RebuildBound.Proofs.G2.Main

/-!
# G2: the completed-A coarse-range bound at d = 2

`REPORT.tex`, Proposition "Completed-A
coarse-range bound", case `r = 1`, form (CA).

Proof (helpers under `Proofs/G2/`):

* `BlindBits.Bits` (package BlindBits): bit vectors of numbers, `Placed`
  (virtual destinations).
* `Route`: the invariants of A's route for arbitrary words: each stage writes
  every pair with the merge-split of the stage's start state; its sheds go to
  its own stash; placement; the cap count `stage_count`.
* `Blind`: A's route on A's key set as a `BlindRoute` (`aRoute`) and its
  contract (`aRoute_valid`): blindness from T5_step, monotone main, cap count.
* `Range`: the reference coarse count `refC` equals the blind route's
  `rangeCount` with the truncated early list as early set, which is disjoint
  from main after stage `lo`, has at most `P` keys and is fixed by the bits
  below `lo`; `refC` reads only the low `b` bits of A's words.
* `Words`: averages pushed forward along maps with fibers of equal size (low
  bits of the merge family's words; low `k` bits of an old home).
* `Main`: the union bound, P11ab per range and history, the old-home density,
  P11d and P11e.

No obstacle required leaving the measure-based API: the probability space of
the spec (`JobLaw.prob`) is a finite sum, and P11d/P11e supply the measure
side.
-/

open scoped ENNReal NNReal

theorem RebuildBound.G2 : RebuildBound.Spec.G2_statement := by
  intro g L TA lam D rule S Lf hL hv hlo
  refine (RebuildBound.FiniteLawProof.prob_le_cover_of L.prob_eq _
    (fun R hist w => Lf < RebuildBound.Model.refCoarse g w
    (RebuildBound.Model.reference rule g w (L.inputs hist w)) (L.inputs hist w)
    (TA + RebuildBound.Model.sumUpTo S g.lo) R) g.ranges (fun hist w h => h)).trans ?_
  refine (Finset.sum_le_sum fun R hR =>
    RebuildBound.G2.range_bound hL hv hlo Lf S (Finset.mem_range.1 hR)).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [RebuildBound.Model.Geom.ranges, RebuildBound.Model.Geom.depth, Nat.cast_pow,
    Nat.cast_ofNat]
  exact le_of_eq (by ring)
