import RebuildBound.Spec.P12

/-!
# P13: the shadow network with a drain-only terminal stage (trusted statements)

`REPORT.tex`, section `sec:top-final-ranges` ("Stages 14–21 give `t = 8`,
`h = 1`, and `g = 2^14` comparison roots"). The top preparation routes A in
two independent halves of `T/2` buckets on bits `0 … k - 2`; its last level,
on bit `k - 1`, merges the two halves, but **its sheds are drain-only**: they
never enter the swept pool, so no coarse range counts them. In the terms of
`Spec/Prob/RadixNetwork.lean` this is a route in `r = 2` blocks (the halves)
of `b = k - 1` binary stages whose terminal radix node (the last level, the
class being the word's bit `k - 1`) does not shed into the range.

The chain is P12's with the radix node's cap removed from the count and from
the terminal test (`rRangeCount0`, `radixTermTest0`, `rFirstArrivalTest0`):

  `E (A_{R,a} - L)₊ ≤ E radixTermTest0(state after stage b)`        (P13b)
  `                = E rForestTest_{lo+1}(state after stage lo + 1)` (P12a)
  `                ≤ E rFirstArrivalTest0(phantom arrivals)`         (P13ab)
  `                ≤ ∫ rFirstArrivalTest0 dPo(λ)`                    (P13d, P13g)
  `                = E (Y - L)₊`                                     (P13e)

P12a is already stated for every terminal test that reads only the range's
buckets. Under independent `Po(λ)` first arrivals the range's forest is, at
each of its `2^lo` buckets and in each of the `r` blocks, one depth-`(b - lo)`
shadow tree; with no cap at the terminal node the range count is the early
count plus the `2^lo r` root losses, each thinned by `q`. That is
`rangeLawR C λ P (2^lo r) (b - lo) 1 q`: at radix one the radix root of a
thinned tree never exceeds `C` in main, so it is the thinned root loss.

* **P13b, P13c, P13ab**: P12b, P12c, P12ab for the cap-free terminal test.
* **P13d**: Poissonization from starting nodes uniform on a node set `S` with
  `|K| ≤ λ |S|` (the top preparation's old homes: uniform on every node).
* **P13g**: Poissonization from a **fixed** start with at most `λ` keys at
  every node (the initialization's scatter).
* **P13e**: the forest identity.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.Spec

variable {K : Type} [DecidableEq K] {r b : ℕ}

/-- The coarse-range count of class `a` and the range of `R` when the terminal
node's sheds drain elsewhere: the early keys and the late binary sheds whose
final home `(c x, h x)` lies in the range. -/
def rRangeCount0 (ρ : RRoute K r b) (lo : ℕ) (early : (K → Bits b) → Finset K) (R : Bits b)
    (a : Fin r) (h : K → Bits b) (c : K → Fin r) : ℕ :=
  ((early h).filter (fun x => InRange lo R (h x) ∧ c x = a)).card +
    ((ρ.mainAt h lo \ ρ.mainAt h b).filter (fun x => InRange lo R (h x) ∧ c x = a)).card

/-- The cap-free terminal test of the range of `R` in a class of mass `q`: thin
every node by `q`, add each block's node `(i, p)` into `p`, then the stop-loss
of the range's shadow counts plus an independent early count `Bin(P, p_e)`. -/
noncomputable def radixTermTest0 (P : ℕ) (pe q : I) (L lo : ℕ) (R : Bits b)
    (x : States (RNode r b)) : ℝ≥0∞ :=
  thinAll (allRNodes r b) (fun _ => q)
    (termTest P pe L lo R ∘ sumAlong (fun V : RNode r b => V.2)) x

/-- The backward test at the first counted arrivals `N` (stage `lo + 1`, before
its cap), with the cap-free terminal test of a class of mass `q` and the early
probability `q 2^-(b - lo)`. -/
noncomputable def rFirstArrivalTest0 (C P L lo : ℕ) (R : Bits b) (q : I) (N : RNode r b → ℕ) :
    ℝ≥0∞ :=
  rForestTest C R (radixTermTest0 P (q * halfPow (b - lo)) q L lo R) (lo + 1)
    (capAll (allRNodes r b) C (mainEmbed N))

/-- **P13b, the conditioning order and the class average** with a drain-only
terminal node. -/
def P13b_statement : Prop :=
  ∀ {K : Type} [Fintype K] [DecidableEq K] {r b : ℕ} (C : ℕ) (pos : K → RNode r b)
    (ρ : RRoute K r b), ρ.Valid C pos →
    ∀ (lo : ℕ), lo ≤ b → ∀ (early : (K → Bits b) → Finset K) (P L : ℕ) (R : Bits b)
      (q : Fin r → I) (a : Fin r),
    ∑ a, (q a : ℝ) = 1 →
    (∀ h, Disjoint (early h) (ρ.mainAt h lo)) → (∀ h, (early h).card ≤ P) →
    (∀ h h', AgreeBelow lo h h' → early h = early h') →
    wordAvg (fun h => classAvg q (fun c => ((rRangeCount0 ρ lo early R a h c - L : ℕ) : ℝ≥0∞))) ≤
      wordAvg (fun h => radixTermTest0 P (q a * halfPow (b - lo)) (q a) L lo R
        (rnetState ρ pos lo h b))

/-- **P13c, class membership.** The cap-free first-arrival test is
nondecreasing, directionally convex and at most `P + Σ N`. -/
def P13c_statement : Prop :=
  ∀ {r b : ℕ} (C P L lo : ℕ) (R : Bits b) (q : I),
    Monotone (rFirstArrivalTest0 (r := r) C P L lo R q) ∧
      DirConvex (rFirstArrivalTest0 (r := r) C P L lo R q) ∧
      ∀ N : RNode r b → ℕ, rFirstArrivalTest0 C P L lo R q N ≤ P + ∑ v, (N v : ℝ≥0∞)

/-- **P13ab, the shadow comparison with a drain-only terminal node**, for one
range and class and a fixed old history. -/
def P13ab_statement : Prop :=
  ∀ {K : Type} [Fintype K] [DecidableEq K] {r b : ℕ} (C : ℕ) (pos : K → RNode r b)
    (ρ : RRoute K r b), ρ.Valid C pos →
    ∀ (lo : ℕ), lo < b → ∀ (early : (K → Bits b) → Finset K) (P L : ℕ) (R : Bits b)
      (q : Fin r → I) (a : Fin r),
    ∑ a, (q a : ℝ) = 1 →
    (∀ h, Disjoint (early h) (ρ.mainAt h lo)) → (∀ h, (early h).card ≤ P) →
    (∀ h h', AgreeBelow lo h h' → early h = early h') →
    wordAvg (fun h => classAvg q (fun c => ((rRangeCount0 ρ lo early R a h c - L : ℕ) : ℝ≥0∞))) ≤
      wordAvg (fun h => rFirstArrivalTest0 C P L lo R (q a) (rrawArrivals pos h (lo + 1)))

/-- **P13d, Poissonization from a uniform start** on a nonempty node set `S` with
at most `λ |S|` keys. -/
def P13d_statement : Prop :=
  ∀ {K : Type} [Fintype K] [DecidableEq K] {r b : ℕ} (C P L lo : ℕ) (R : Bits b) (q : I)
    (lam : ℝ≥0) (S : Finset (RNode r b)), S.Nonempty → lo < b →
    (Fintype.card K : ℝ≥0) ≤ lam * S.card →
    uniformAvg (fun o : K → S => wordAvg (fun h : K → Bits b =>
      rFirstArrivalTest0 C P L lo R q (rrawArrivals (fun x => (o x : RNode r b)) h (lo + 1)))) ≤
      ∫⁻ N, rFirstArrivalTest0 (r := r) C P L lo R q N ∂(poissonVec (fun _ => lam))

/-- **P13g, Poissonization from a fixed start** with at most `λ` keys at every
node. -/
def P13g_statement : Prop :=
  ∀ {K : Type} [Fintype K] [DecidableEq K] {r b : ℕ} (C P L lo : ℕ) (R : Bits b) (q : I)
    (lam : ℝ≥0) (pos : K → RNode r b), lo < b →
    (∀ v, ((Finset.univ.filter fun x => pos x = v).card : ℝ≥0) ≤ lam) →
    wordAvg (fun h : K → Bits b =>
      rFirstArrivalTest0 C P L lo R q (rrawArrivals pos h (lo + 1))) ≤
      ∫⁻ N, rFirstArrivalTest0 (r := r) C P L lo R q N ∂(poissonVec (fun _ => lam))

/-- **P13e, the forest identity with a drain-only terminal node.** Under
independent `Po(λ)` first arrivals the cap-free first-arrival test of a range
with `2^lo` buckets in `r` blocks is the stop-loss of the early count plus
`2^lo r` independent root losses, each thinned by `q`. -/
def P13e_statement : Prop :=
  ∀ {r b : ℕ} (C P L lo : ℕ) (R : Bits b) (q : I) (lam : ℝ≥0), lo < b → 1 ≤ r →
    ∫⁻ N, rFirstArrivalTest0 (r := r) C P L lo R q N ∂(poissonVec (fun _ => lam)) =
      stopLoss (rangeLawR C lam P (2 ^ lo * r) (b - lo) 1 q) L

end RebuildBound.Spec
