import RebuildBound.Spec.Prob.RadixNetwork
import RebuildBound.Spec.Prob.RadixTree

/-!
# P12: the shadow network in `r` blocks with a terminal radix (trusted statements)

The radix generalization of package P11 (`Spec/P11.lean`,
`Spec/P11de.lean`): `REPORT.tex`, Proposition "Completed-A coarse-range
bound", every odd `r`. Definitions in `Spec/Prob/RadixNetwork.lean` and
`Spec/Prob/RadixTree.lean`. Fix the starting nodes `pos` (the old history), a
coarse range `R` with `2^lo` in-block buckets, a class `a` and class masses
`q`. For uniform independent words and independent classes the chain is

  `E (A_{R,a} - L)₊ ≤ E radixTermTest(state after stage b)`        (P12b)
  `                = E rForestTest_{lo+1}(state after stage lo + 1)` (P12a)
  `                ≤ E rFirstArrivalTest(phantom arrivals)`          (P12ab)
  `                ≤ ∫ rFirstArrivalTest dPo(λ)`                     (P12d)
  `                = E (Y_a - L)₊`                                   (P12e)

* **P12a, exactness.** As P11a, in every block: given the words below bit `j`,
  the next bits of all records are uniform and each node keeps `min C
  arrivals`, so averaging a terminal test that reads only the range's buckets
  (in every block) gives the backward forest test of the current node states.
* **P12b, the conditioning order and the classes.** Condition on the words
  below bit `lo`: that fixes the early keys, whose final homes are independent
  of the late sheds; each lies in the range with probability
  `2^-(b - lo) q_a`, so the early range count is `Bin(|early|, q_a 2^-(b-lo))`,
  padded to `Bin(P, ·)`. Averaging the classes of the late sheds and of the
  last main records is the radix node's thinning.
* **P12c, class membership** of the first-arrival test, for P5a.
* **P12ab** composes P12b, P12a and the phantom restoration.
* **P12d, Poissonization.** Starting nodes uniform on any nonempty node set `S`
  with `|K| ≤ λ |S|` give every first-arrival node a mean at most `λ`; replace
  keys by Pois(1) copies (P5a), split (P5b), pad every node to `λ` (P5b).
* **P12e, the forest identity.** Under independent `Po(λ)` first arrivals the
  range's forest is, at each of its `2^lo` buckets, `r` independent depth
  `b - lo` shadow trees (one per block) feeding the radix node: the radix root
  law `radixRoot`, so the test integrates to the stop-loss of `rangeLawR`.

The old-home density, the class masses of the words and the union over the
ranges are applied in the glue (SG2).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.Spec

/-- The uniform average over a finite type. -/
noncomputable def uniformAvg {α : Type*} [Fintype α] (F : α → ℝ≥0∞) : ℝ≥0∞ :=
  (Fintype.card α : ℝ≥0∞)⁻¹ * ∑ a, F a

/-- **P12a, exactness in `r` blocks.** For a terminal test `φ` that reads only
the range's buckets (in every block), and every stage `j` from `lo` to `b`:
averaging `φ` of the final node states over the words that agree with `h`
below bit `j` gives the forest test of the node states after stage `j`. -/
def P12a_statement : Prop :=
  ∀ {K : Type} [Fintype K] [DecidableEq K] {r b : ℕ} (C : ℕ) (pos : K → RNode r b)
    (ρ : RRoute K r b), ρ.Valid C pos →
    ∀ (lo : ℕ) (R : Bits b) (φ : States (RNode r b) → ℝ≥0∞),
    (∀ x y : States (RNode r b),
      (∀ v : RNode r b, InRange lo R v.2 → ∀ s, x (v, s) = y (v, s)) → φ x = φ y) →
    ∀ (j : ℕ), lo ≤ j → j ≤ b → ∀ (h : K → Bits b),
      condAvg j h (fun h' => φ (rnetState ρ pos lo h' b)) =
        rForestTest C R φ j (rnetState ρ pos lo h j)

/-- **P12b, the conditioning order and the class average.** An early list that
is disjoint from main after stage `lo`, has at most `P` keys and is fixed by the
words below bit `lo` adds at most an independent `Bin(P, q_a 2^-(b-lo))` to the
range count; averaging the classes of the rest is the radix terminal test of
the final node states. -/
def P12b_statement : Prop :=
  ∀ {K : Type} [Fintype K] [DecidableEq K] {r b : ℕ} (C : ℕ) (pos : K → RNode r b)
    (ρ : RRoute K r b), ρ.Valid C pos →
    ∀ (lo : ℕ), lo ≤ b → ∀ (early : (K → Bits b) → Finset K) (P L : ℕ) (R : Bits b)
      (q : Fin r → I) (a : Fin r),
    ∑ a, (q a : ℝ) = 1 →
    (∀ h, Disjoint (early h) (ρ.mainAt h lo)) → (∀ h, (early h).card ≤ P) →
    (∀ h h', AgreeBelow lo h h' → early h = early h') →
    wordAvg (fun h => classAvg q (fun c => ((rRangeCount ρ C lo early R a h c - L : ℕ) : ℝ≥0∞))) ≤
      wordAvg (fun h => radixTermTest C P (q a * halfPow (b - lo)) (q a) L lo R
        (rnetState ρ pos lo h b))

/-- **P12c, class membership.** The first-arrival test is nondecreasing,
directionally convex and at most `P + Σ N`. -/
def P12c_statement : Prop :=
  ∀ {r b : ℕ} (C P L lo : ℕ) (R : Bits b) (q : I),
    Monotone (rFirstArrivalTest (r := r) C P L lo R q) ∧
      DirConvex (rFirstArrivalTest (r := r) C P L lo R q) ∧
      ∀ N : RNode r b → ℕ, rFirstArrivalTest C P L lo R q N ≤ P + ∑ v, (N v : ℝ≥0∞)

/-- **P12ab, the shadow comparison for one range and class and a fixed old
history.** The expected stop-loss of the range count is at most that of the
first-arrival test at the phantom arrivals of all keys after stage `lo + 1`. -/
def P12ab_statement : Prop :=
  ∀ {K : Type} [Fintype K] [DecidableEq K] {r b : ℕ} (C : ℕ) (pos : K → RNode r b)
    (ρ : RRoute K r b), ρ.Valid C pos →
    ∀ (lo : ℕ), lo < b → ∀ (early : (K → Bits b) → Finset K) (P L : ℕ) (R : Bits b)
      (q : Fin r → I) (a : Fin r),
    ∑ a, (q a : ℝ) = 1 →
    (∀ h, Disjoint (early h) (ρ.mainAt h lo)) → (∀ h, (early h).card ≤ P) →
    (∀ h h', AgreeBelow lo h h' → early h = early h') →
    wordAvg (fun h => classAvg q (fun c => ((rRangeCount ρ C lo early R a h c - L : ℕ) : ℝ≥0∞))) ≤
      wordAvg (fun h => rFirstArrivalTest C P L lo R (q a) (rrawArrivals pos h (lo + 1)))

/-- **P12d, Poissonization.** Averaged over starting nodes uniform on a nonempty
node set `S` and uniform words, the first-arrival test at the phantom arrivals
of at most `λ |S|` keys is at most its expectation under independent `Po(λ)`
arrivals at every node. -/
def P12d_statement : Prop :=
  ∀ {K : Type} [Fintype K] [DecidableEq K] {r b : ℕ} (C P L lo : ℕ) (R : Bits b) (q : I)
    (lam : ℝ≥0) (S : Finset (RNode r b)), S.Nonempty → lo < b →
    (Fintype.card K : ℝ≥0) ≤ lam * S.card →
    uniformAvg (fun o : K → S => wordAvg (fun h : K → Bits b =>
      rFirstArrivalTest C P L lo R q (rrawArrivals (fun x => (o x : RNode r b)) h (lo + 1)))) ≤
      ∫⁻ N, rFirstArrivalTest (r := r) C P L lo R q N ∂(poissonVec (fun _ => lam))

/-- **P12e, the forest identity.** Under independent `Po(λ)` first arrivals, the
first-arrival test of a range with `2^lo` buckets in `r` blocks equals the
stop-loss of the early count plus `2^lo` independent radix root losses. -/
def P12e_statement : Prop :=
  ∀ {r b : ℕ} (C P L lo : ℕ) (R : Bits b) (q : I) (lam : ℝ≥0), lo < b → 1 ≤ r →
    ∫⁻ N, rFirstArrivalTest (r := r) C P L lo R q N ∂(poissonVec (fun _ => lam)) =
      stopLoss (rangeLawR C lam P (2 ^ lo) (b - lo) r q) L

end RebuildBound.Spec
