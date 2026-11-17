import RebuildBound.Spec.P7
import RebuildBound.Spec.P11de

/-!
# Complete populations with bounded means per home (trusted statements)

`REPORT.tex`,
section `sec:binary-top-preparation` ("Raw stage arrivals", the
initialization's fixed scatter) and section `sec:top-final-ranges`. The top
preparation routes A from every bucket of the top, and the initialization
from a public scatter with at most `λ` records per bucket, so their raw
arrivals are independent categorical trials whose masses need not be
bounded by one `p_*` but whose **means per home** are at most `λ`.

* **P8c**, P8a with per-home means: independent categorical homes with
  `Σ_i p_i v ≤ λ` at every home `v`. The restricted stop-loss of the excess
  is at most its value under independent `Po(λ)` counts. P8a is the case
  `p_i v ≤ p_*`, `|keys| p_* ≤ λ`.
* **P11f**, P11d with A's old homes uniform on **every** bucket (no blank
  half): averaged over uniform old homes and uniform words, the
  first-arrival test at the phantom arrivals of at most `λ 2^b` keys is at
  most its expectation under independent `Po(λ)` arrivals.
* **P11g**, the same from a **fixed** start: if at most `λ` keys start at
  every bucket, the average over uniform words alone is at most the same
  Poisson expectation. The arrivals after stage `lo + 1` are uniform on the
  key's aligned block of `2^(lo + 1)` buckets, so every node's mean is at
  most `λ`.

The first-arrival test is nondecreasing, directionally convex and finite
(P11c), which is what the Poisson replacement (P5a), splitting and padding
(P5b) need.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RebuildBound.Spec

/-- **P8c, one complete population with per-home means at most `λ`.** -/
def P8c_statement : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (J : Finset ι) (C S : ℕ) (lam : ℝ≥0)
    (ps : List (ι → ℝ≥0)),
    (∀ p ∈ ps, ∑ v, p v = 1) → (∀ v, (ps.map fun p => p v).sum ≤ lam) →
    ∫⁻ y, restrictedStopLoss J C S y ∂(convList (ps.map unitLaw)) ≤
      ∫⁻ z, restrictedStopLoss J C S z ∂(poissonVec (fun _ : ι => lam))

/-- **P11f, Poissonization with uniform old homes on every bucket.** -/
def P11f_statement : Prop :=
  ∀ {K : Type} [Fintype K] [DecidableEq K] {b : ℕ} (C P L lo : ℕ) (R : Bits b)
    (lam : ℝ≥0), lo < b → (Fintype.card K : ℝ≥0) ≤ lam * 2 ^ b →
    wordAvg (fun o : K → Bits b => wordAvg (fun h : K → Bits b =>
      firstArrivalTest C P L lo R (rawArrivals o h (lo + 1)))) ≤
      ∫⁻ N, firstArrivalTest C P L lo R N ∂(poissonVec (fun _ => lam))

/-- **P11g, Poissonization from a fixed start with at most `λ` keys per bucket.** -/
def P11g_statement : Prop :=
  ∀ {K : Type} [Fintype K] [DecidableEq K] {b : ℕ} (C P L lo : ℕ) (R : Bits b)
    (lam : ℝ≥0) (pos : K → Bits b), lo < b →
    (∀ v, ((Finset.univ.filter fun x => pos x = v).card : ℝ≥0) ≤ lam) →
    wordAvg (fun h : K → Bits b =>
      firstArrivalTest C P L lo R (rawArrivals pos h (lo + 1))) ≤
      ∫⁻ N, firstArrivalTest C P L lo R N ∂(poissonVec (fun _ => lam))

end RebuildBound.Spec
