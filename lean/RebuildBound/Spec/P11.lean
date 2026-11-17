import RebuildBound.Spec.Prob.Network

/-!
# P11: the shadow network of a blind route (trusted statements)

For a binary route (`r = 1`); definitions in
`Spec/Prob/Network.lean`. Fix the starting buckets `pos` (the old history) and
a coarse range `R` with `g = 2^lo` homes. For uniform independent words the
chain is

  `E (A_R - L)₊ ≤ E termTest(late sheds)`                      (P11b)
  `           = E forestTest_{lo+1}(state after stage lo + 1)`  (P11a)
  `           ≤ E firstArrivalTest(phantom arrivals)`           (P11ab)

* **P11a, exactness of the count recurrence.** Given the words below bit `j`,
  the next bits of all records are still uniform (blindness), and each bucket
  keeps exactly `min C arrivals` (the cap count), so the conditional
  expectation of a terminal test that reads only the range's homes is the
  backward forest test of the current node states.
* **P11b, the conditioning order.** Condition on the words below bit `lo`.
  That fixes the early list and the main keys after stage `lo`; the early
  keys' range bits are independent of the late sheds, which depend only on
  the main keys' words. So the early range count is `Bin(|early|, 2^-(b-lo))`
  given the rest, and `|early| ≤ P` pads it to `Bin(P, 2^-(b-lo))`.
* **P11c_class.** The first-arrival test is nondecreasing, directionally
  convex and at most `P + Σ N`: the hypotheses of the Poisson replacement
  (P5a) and of the phantom restoration.
* **P11ab.** The chain above. The last step restores phantoms: after stage
  `lo + 1` the node states are the capped arrivals of the keys still in main,
  and those arrivals are at most the phantom arrivals of all keys.

`P11ab` is the input of the completed-A glue (G2), which adds the old-home
density, the Poisson replacement and the union over ranges.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RebuildBound.Spec

/-- **P11a, exactness.** For a terminal test `φ` that reads only the homes of the
range, and every stage `j` from `lo` to `b`: averaging `φ` of the final node
states over the words that agree with `h` below bit `j` gives the forest test
of the node states after stage `j`. -/
def P11a_statement : Prop :=
  ∀ {K : Type} [Fintype K] [DecidableEq K] {b : ℕ} (C : ℕ) (pos : K → Bits b)
    (ρ : BlindRoute K b), ρ.Valid C pos →
    ∀ (lo : ℕ) (R : Bits b) (φ : States (Bits b) → ℝ≥0∞),
    (∀ x y : States (Bits b), (∀ v, InRange lo R v → ∀ s, x (v, s) = y (v, s)) → φ x = φ y) →
    ∀ (j : ℕ), lo ≤ j → j ≤ b → ∀ (h : K → Bits b),
      condAvg j h (fun h' => φ (netState ρ pos lo h' b)) =
        forestTest C R φ j (netState ρ pos lo h j)

/-- **P11b, the conditioning order.** An early list that is disjoint from main
after stage `lo`, has at most `P` keys and is fixed by the words below bit
`lo`, adds at most an independent `Bin(P, 2^-(b-lo))` to the range count of
the late sheds. -/
def P11b_statement : Prop :=
  ∀ {K : Type} [Fintype K] [DecidableEq K] {b : ℕ} (C : ℕ) (pos : K → Bits b)
    (ρ : BlindRoute K b), ρ.Valid C pos →
    ∀ (lo : ℕ), lo ≤ b → ∀ (early : (K → Bits b) → Finset K) (P L : ℕ) (R : Bits b),
    (∀ h, Disjoint (early h) (ρ.mainAt h lo)) → (∀ h, (early h).card ≤ P) →
    (∀ h h', AgreeBelow lo h h' → early h = early h') →
    wordAvg (fun h => ((rangeCount ρ lo early R h - L : ℕ) : ℝ≥0∞)) ≤
      wordAvg (fun h => termTest P (halfPow (b - lo)) L lo R (netState ρ pos lo h b))

/-- **P11c, class membership.** The first-arrival test is nondecreasing,
directionally convex and at most `P + Σ N`. -/
def P11c_class_statement : Prop :=
  ∀ {b : ℕ} (C P L lo : ℕ) (R : Bits b),
    Monotone (firstArrivalTest C P L lo R) ∧ DirConvex (firstArrivalTest C P L lo R) ∧
      ∀ N : Bits b → ℕ, firstArrivalTest C P L lo R N ≤ P + ∑ v, (N v : ℝ≥0∞)

/-- **P11ab, the shadow comparison for one range and fixed old history.** The
expected stop-loss of the range count is at most that of the first-arrival
test at the phantom arrivals of all keys after stage `lo + 1`. -/
def P11ab_statement : Prop :=
  ∀ {K : Type} [Fintype K] [DecidableEq K] {b : ℕ} (C : ℕ) (pos : K → Bits b)
    (ρ : BlindRoute K b), ρ.Valid C pos →
    ∀ (lo : ℕ), lo < b → ∀ (early : (K → Bits b) → Finset K) (P L : ℕ) (R : Bits b),
    (∀ h, Disjoint (early h) (ρ.mainAt h lo)) → (∀ h, (early h).card ≤ P) →
    (∀ h h', AgreeBelow lo h h' → early h = early h') →
    wordAvg (fun h => ((rangeCount ρ lo early R h - L : ℕ) : ℝ≥0∞)) ≤
      wordAvg (fun h => firstArrivalTest C P L lo R (rawArrivals pos h (lo + 1)))

end RebuildBound.Spec
