import RebuildBound.Spec.Prob.ShadowTree

/-!
# P11d and P11e: from phantom arrivals to the range law (trusted statements)

The second half of the completed-A comparison for a binary route (`r = 1`),
after P11ab. The network has `b = k + 1` stages; A's embedded old homes are
the buckets with top bit `k` set (the region `[U, 2U)` for `U = 2^k`), and
`[0, U)` is blank.

* **P11d, Poissonization.** Under uniform old homes on the upper half and
  uniform words, with at most `λ U` keys, the phantom arrivals at stage
  `lo + 1 ≤ k` are a sum of independent unit vectors, each uniform on the
  upper half. Replacing each key by a Pois(1) number of copies (P5a),
  splitting (P5b) and padding every coordinate, the blank half included, to
  `λ` (P5b) can only increase the first-arrival test, which is nondecreasing,
  directionally convex and finite (P11c).
* **P11e, the forest identity.** With independent `Po(λ)` arrivals at every
  node, the range's forest is `2^lo` independent binary shadow trees of depth
  `t = b - lo`, so the first-arrival test integrates to the stop-loss of
  `rangeLaw`.

The old-home density factor `D` and the union over the `2^(b-lo)` ranges are
applied in the glue (G2).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RebuildBound.Spec

/-- **P11d, Poissonization.** Averaged over uniform old homes in the upper half
(`o x` with its top bit set) and uniform words, the first-arrival test at the
phantom arrivals of at most `λ 2^k` keys is at most its expectation under
independent `Po(λ)` arrivals at every node. -/
def P11d_statement : Prop :=
  ∀ {K : Type} [Fintype K] [DecidableEq K] {k : ℕ} (C P L lo : ℕ) (R : Bits (k + 1))
    (lam : ℝ≥0), lo < k → (Fintype.card K : ℝ≥0) ≤ lam * 2 ^ k →
    wordAvg (fun o : K → Bits (k + 1) => wordAvg (fun h : K → Bits (k + 1) =>
      firstArrivalTest C P L lo R
        (rawArrivals (fun x => Function.update (o x) (Fin.last k) true) h (lo + 1)))) ≤
      ∫⁻ N, firstArrivalTest C P L lo R N ∂(poissonVec (fun _ => lam))

/-- **P11e, the forest identity.** Under independent `Po(λ)` first arrivals, the
first-arrival test of a range with `2^lo` homes equals the stop-loss of the
early count plus `2^lo` independent depth-`(b - lo)` root losses. -/
def P11e_statement : Prop :=
  ∀ {b : ℕ} (C P L lo : ℕ) (R : Bits b) (lam : ℝ≥0), lo < b →
    ∫⁻ N, firstArrivalTest C P L lo R N ∂(poissonVec (fun _ => lam)) =
      stopLoss (rangeLaw C lam P (halfPow (b - lo)) (2 ^ lo) (b - lo)) L

end RebuildBound.Spec
