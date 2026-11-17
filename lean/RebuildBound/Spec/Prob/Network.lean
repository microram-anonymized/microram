import RebuildBound.Spec.Prob.Poisson

/-!
# An abstract blind binary route and its shadow forest (trusted spec)

Definitions behind package P11 (`REPORT.tex`, Proposition "Completed-A
coarse-range bound", case `r = 1`). Nothing here mentions the rebuild model;
the model's A route is an instance (package G2).

**The route.** A fixed finite key set `K`. Buckets of a network with `b` binary
stages are bit vectors `Bits b`. Key `x` starts at bucket `pos x` (A's
embedded old home) and has the word `h x : Bits b`, uniform and independent
across keys. Stage `j + 1` reads bit `j`: a main record moves to its bucket
with bit `j` replaced by bit `j` of its word, so after stage `j` it sits at
`dest pos h j x` (bits below `j` from the word, the others from `pos`). Each
bucket keeps `min C arrivals` records; the others are shed and leave the route
for good.

`BlindRoute` is the route's data: a transcript state per stage and the main
key set of a state. `BlindRoute.Valid` is its contract:

* **blindness** (non-interference): stage `j + 1` reads only bits `≤ j` of the
  words of the keys present in main;
* main key sets only shrink;
* **the cap count**: after stage `j + 1`, bucket `V` holds exactly
  `min C (arrivals at V)` main keys.

**Counts.** `netState ρ pos lo h j` is the node-state vector after stage `j`:
main counts per bucket, and shadow counts of the keys shed at stages
`lo + 1, …, j`, each placed at its virtual destination `dest pos h j x`.
`rawArrivals pos h j` counts *all* keys of `K` by virtual destination: the
phantom arrivals.

**A coarse range** is the set of final homes (after `b` stages) whose bits
`≥ lo` equal those of `R`. `rangeCount` counts the early list plus the late
sheds (stages `lo + 1 … b`) whose final homes lie in the range.

**The shadow forest of a range.** `forestTest C R φ j` is the backward test
through stages `j + 1, …, b`, applied to the state after stage `j`. One stage
thins every node by `1/2` (a record keeps its route toward the range with
probability `1/2`), adds each node into the node that has bit `j` of `R`, and
caps every node. Nodes off the range's forest carry records that never reach
the range; a terminal test that reads only the range's homes ignores them.
`firstArrivalTest` is that test at the first counted arrivals, stage `lo + 1`,
before their cap; its terminal test is the stop-loss `termTest` of the late
sheds after averaging an independent early count `Bin(P, 2^-(b-lo))`.

**Averages.** Expectations over the ideal words are finite averages:
`wordAvg` over all word assignments, and `condAvg j h` over the assignments
that agree with `h` on every bit below `j`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.Spec

/-- Bucket indices of a network with `b` binary stages, and routing words
restricted to the bits such a network reads. -/
abbrev Bits (b : ℕ) := Fin b → Bool

/-- The virtual destination of key `x` after stage `j`: bits below `j` come from
its word `h x`, the others from its starting bucket `pos x`. -/
def dest {K : Type*} {b : ℕ} (pos : K → Bits b) (h : K → Bits b) (j : ℕ) (x : K) :
    Bits b :=
  fun i => if i.val < j then h x i else pos x i

/-- Two word assignments agree on every bit below `j`. -/
def AgreeBelow {K : Type*} {b : ℕ} (j : ℕ) (h h' : K → Bits b) : Prop :=
  ∀ (x : K) (i : Fin b), i.val < j → h x i = h' x i

instance {K : Type*} [Fintype K] {b : ℕ} (j : ℕ) (h : K → Bits b) :
    DecidablePred (AgreeBelow j h) :=
  fun h' => by unfold AgreeBelow; infer_instance

/-- Bucket `v` lies in the coarse range of `R`: its bits `≥ lo` equal `R`'s. -/
def InRange {b : ℕ} (lo : ℕ) (R v : Bits b) : Prop :=
  ∀ i : Fin b, lo ≤ i.val → v i = R i

instance {b : ℕ} (lo : ℕ) (R : Bits b) : DecidablePred (InRange lo R) :=
  fun v => by unfold InRange; infer_instance

/-- The final homes of the coarse range of `R`. -/
def rangeHomes {b : ℕ} (lo : ℕ) (R : Bits b) : Finset (Bits b) :=
  Finset.univ.filter (InRange lo R)

/-- The data of a route: transcript states, one step per stage, and the main
key set of a state. `step j` is stage `j + 1`, which routes by bit `j`. -/
structure BlindRoute (K : Type) (b : ℕ) where
  St : Type
  init : St
  step : ℕ → St → (K → Bits b) → St
  main : St → Finset K

namespace BlindRoute

variable {K : Type} {b : ℕ}

/-- The transcript state after stage `j` under the words `h`. -/
def state (ρ : BlindRoute K b) (h : K → Bits b) : ℕ → ρ.St
  | 0 => ρ.init
  | j + 1 => ρ.step j (ρ.state h j) h

/-- The main key set after stage `j`. -/
def mainAt (ρ : BlindRoute K b) (h : K → Bits b) (j : ℕ) : Finset K :=
  ρ.main (ρ.state h j)

/-- The contract of a blind capped route with bucket capacity `C` and starting
buckets `pos`. -/
structure Valid [DecidableEq K] (ρ : BlindRoute K b) (C : ℕ) (pos : K → Bits b) :
    Prop where
  /-- Stage `j + 1` reads only bits `≤ j` of the keys present in main. -/
  blind : ∀ (j : ℕ) (s : ρ.St) (h h' : K → Bits b),
    (∀ x ∈ ρ.main s, ∀ i : Fin b, i.val ≤ j → h x i = h' x i) →
    ρ.step j s h = ρ.step j s h'
  /-- Main key sets only shrink. -/
  mono : ∀ (h : K → Bits b) (j : ℕ), ρ.mainAt h (j + 1) ⊆ ρ.mainAt h j
  /-- After stage `j + 1`, bucket `V` keeps `min C (arrivals at V)` keys. -/
  count : ∀ (h : K → Bits b) (j : ℕ) (V : Bits b),
    ((ρ.mainAt h (j + 1)).filter (fun x => dest pos h (j + 1) x = V)).card =
      min C ((ρ.mainAt h j).filter (fun x => dest pos h (j + 1) x = V)).card

end BlindRoute

variable {K : Type} [DecidableEq K] {b : ℕ}

/-- The node states after stage `j`: main counts, and shadow counts of the keys
shed at stages `lo + 1, …, j`, each at its virtual destination. -/
def netState (ρ : BlindRoute K b) (pos : K → Bits b) (lo : ℕ) (h : K → Bits b) (j : ℕ) :
    States (Bits b) := fun q =>
  match q.2 with
  | .main => ((ρ.mainAt h j).filter (fun x => dest pos h j x = q.1)).card
  | .shadow => ((ρ.mainAt h lo \ ρ.mainAt h j).filter (fun x => dest pos h j x = q.1)).card

/-- Phantom arrivals: every key of `K`, counted at its virtual destination
after stage `j`. -/
def rawArrivals [Fintype K] (pos : K → Bits b) (h : K → Bits b) (j : ℕ) : Bits b → ℕ :=
  fun V => (Finset.univ.filter (fun x => dest pos h j x = V)).card

/-- The coarse-range count: early keys plus late sheds (stages `lo + 1 … b`)
whose final homes `h x` lie in the range of `R`. -/
def rangeCount (ρ : BlindRoute K b) (lo : ℕ) (early : (K → Bits b) → Finset K)
    (R : Bits b) (h : K → Bits b) : ℕ :=
  ((early h).filter (fun x => InRange lo R (h x))).card +
    ((ρ.mainAt h lo \ ρ.mainAt h b).filter (fun x => InRange lo R (h x))).card

/-- The survival probability `1/2`. -/
noncomputable def half : I := ⟨1 / 2, by norm_num, by norm_num⟩

/-- The probability `2^-n`. -/
noncomputable def halfPow (n : ℕ) : I :=
  ⟨(1 / 2) ^ n, pow_nonneg (by norm_num) n, pow_le_one₀ (by norm_num) (by norm_num)⟩

/-- Every bucket, as a list. -/
noncomputable def allNodes (b : ℕ) : List (Bits b) :=
  (Finset.univ : Finset (Bits b)).toList

/-- The terminal test: the stop-loss `(E + Σ_{v in range} R_v - L)₊` of the
range's shadow counts, averaged over an independent early count
`E ∼ Bin(P, p)`. -/
noncomputable def termTest (P : ℕ) (p : I) (L lo : ℕ) (R : Bits b)
    (x : States (Bits b)) : ℝ≥0∞ :=
  ∫⁻ e, (((e + ∑ v ∈ rangeHomes lo R, x (v, .shadow)) - L : ℕ) : ℝ≥0∞) ∂(binomial P p)

/-- One backward stage of the range's forest: a test `ψ` on the state after
stage `j + 1` becomes the test on the state after stage `j`. Every node is
thinned by `1/2`, added into the node with bit `j` of `R`, and capped at `C`. -/
noncomputable def backStage (C : ℕ) (R : Bits b) (j : ℕ) (ψ : States (Bits b) → ℝ≥0∞) :
    States (Bits b) → ℝ≥0∞ :=
  if hj : j < b then
    thinAll (allNodes b) (fun _ => half)
      (ψ ∘ capAll (allNodes b) C ∘ sumAlong (fun V => Function.update V ⟨j, hj⟩ (R ⟨j, hj⟩)))
  else ψ

/-- The backward test through stages `j + 1, …, b` of the range's forest, on the
state after stage `j`, for the terminal test `φ`. -/
noncomputable def forestTest (C : ℕ) (R : Bits b) (φ : States (Bits b) → ℝ≥0∞) (j : ℕ) :
    States (Bits b) → ℝ≥0∞ :=
  (List.range (b - j)).foldr (fun i ψ => backStage C R (j + i) ψ) φ

/-- The backward test at the first counted arrivals `N` (stage `lo + 1`, before
its cap), with the averaged stop-loss as terminal test. -/
noncomputable def firstArrivalTest (C P L lo : ℕ) (R : Bits b) (N : Bits b → ℕ) : ℝ≥0∞ :=
  forestTest C R (termTest P (halfPow (b - lo)) L lo R) (lo + 1)
    (capAll (allNodes b) C (mainEmbed N))

/-- The average over all word assignments. -/
noncomputable def wordAvg [Fintype K] (F : (K → Bits b) → ℝ≥0∞) : ℝ≥0∞ :=
  (Fintype.card (K → Bits b) : ℝ≥0∞)⁻¹ * ∑ h, F h

/-- The average over the word assignments that agree with `h` below bit `j`. -/
noncomputable def condAvg [Fintype K] (j : ℕ) (h : K → Bits b)
    (F : (K → Bits b) → ℝ≥0∞) : ℝ≥0∞ :=
  ((Finset.univ.filter (AgreeBelow j h)).card : ℝ≥0∞)⁻¹ *
    ∑ h' ∈ Finset.univ.filter (AgreeBelow j h), F h'

end RebuildBound.Spec
