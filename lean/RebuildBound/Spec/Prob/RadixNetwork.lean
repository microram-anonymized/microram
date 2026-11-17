import RebuildBound.Spec.Prob.Network

/-!
# An abstract blind route in `r` blocks with a terminal radix (trusted spec)

Definitions behind package P12, the radix generalization of P11
(`REPORT.tex`, Proposition "Completed-A coarse-range bound", every odd `r`;
`Spec/Prob/Network.lean` is the case of one block without the radix). Nothing
here mentions the rebuild model; the model's A route is an instance.

**The route.** A fixed finite key set `K`. A node is `(i, V)`: a block
`i < r` and an in-block bucket `V : Bits b`. Key `x` starts at node `pos x`
and has the word `h x : Bits b`, uniform and independent across keys. Binary
stage `j + 1` reads bit `j`: a main record keeps its block and moves to its
in-block bucket with bit `j` replaced by bit `j` of its word, so after stage
`j` it sits at `rdest pos h j x`. Each node keeps `min C arrivals` records;
the others are shed and leave the route for good. `RRoute.Valid` is the
contract, as in `BlindRoute.Valid`.

**The terminal radix.** After the last binary stage, key `x` has the class
`c x < r`, independent of the words and across keys, with law `q`. The radix
node at in-block bucket `p` collects the main records at `(i, p)` of every
block `i`; output `(a, p)` keeps `min C` of those of class `a` and sheds the
others. A record's final home is `(c x, h x)`.

**A coarse range** is a class `a` and the in-block buckets `p` whose bits
`≥ lo` equal those of `R`. `rRangeCount` counts the early keys and the late
binary sheds (stages `lo + 1 … b`) whose final home lies in the range, and
the radix node's sheds at the range's buckets.

**Backward tests.** `radixTermTest` is the radix node backward: thin every
node's counts by `q_a` (a record is of class `a` with probability `q_a`), add
each block's node `(i, p)` into the radix node `p`, cap at `C`, and take the
stop-loss of the range's shadow counts plus an independent early count
`Bin(P, p_e)` (`termTest`). `rForestTest` is the binary forest of the range
in every block, as `forestTest`, with the block index carried along.
`rFirstArrivalTest` is that test at the first counted arrivals, stage
`lo + 1`, before their cap, with `p_e = q_a 2^-(b - lo)`.

**Averages.** `wordAvg` and `condAvg` (`Spec/Prob/Network.lean`) average over
the words; `classAvg q` averages over the classes, each key independently of
class `a` with probability `q a`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.Spec

/-- A node of an `r`-block network with `b` binary stages: a block and an
in-block bucket. -/
abbrev RNode (r b : ℕ) := Fin r × Bits b

/-- The virtual destination of key `x` after binary stage `j`: its starting
block, and in-block bits below `j` from its word, the others from its starting
bucket. -/
def rdest {K : Type*} {r b : ℕ} (pos : K → RNode r b) (h : K → Bits b) (j : ℕ) (x : K) :
    RNode r b :=
  ((pos x).1, fun i => if i.val < j then h x i else (pos x).2 i)

/-- The data of a route in `r` blocks: transcript states, one step per binary
stage, and the main key set of a state. `step j` is stage `j + 1`, which
routes by bit `j`. -/
structure RRoute (K : Type) (r b : ℕ) where
  St : Type
  init : St
  step : ℕ → St → (K → Bits b) → St
  main : St → Finset K

namespace RRoute

variable {K : Type} {r b : ℕ}

/-- The transcript state after stage `j` under the words `h`. -/
def state (ρ : RRoute K r b) (h : K → Bits b) : ℕ → ρ.St
  | 0 => ρ.init
  | j + 1 => ρ.step j (ρ.state h j) h

/-- The main key set after stage `j`. -/
def mainAt (ρ : RRoute K r b) (h : K → Bits b) (j : ℕ) : Finset K :=
  ρ.main (ρ.state h j)

/-- The contract of a blind capped route in `r` blocks with node capacity `C`
and starting nodes `pos`. -/
structure Valid [DecidableEq K] (ρ : RRoute K r b) (C : ℕ) (pos : K → RNode r b) : Prop where
  /-- Stage `j + 1` reads only bits `≤ j` of the keys present in main. -/
  blind : ∀ (j : ℕ) (s : ρ.St) (h h' : K → Bits b),
    (∀ x ∈ ρ.main s, ∀ i : Fin b, i.val ≤ j → h x i = h' x i) →
    ρ.step j s h = ρ.step j s h'
  /-- Main key sets only shrink. -/
  mono : ∀ (h : K → Bits b) (j : ℕ), ρ.mainAt h (j + 1) ⊆ ρ.mainAt h j
  /-- After stage `j + 1`, node `V` keeps `min C (arrivals at V)` keys. -/
  count : ∀ (h : K → Bits b) (j : ℕ) (V : RNode r b),
    ((ρ.mainAt h (j + 1)).filter (fun x => rdest pos h (j + 1) x = V)).card =
      min C ((ρ.mainAt h j).filter (fun x => rdest pos h (j + 1) x = V)).card

end RRoute

variable {K : Type} [DecidableEq K] {r b : ℕ}

/-- The node states after stage `j`: main counts, and shadow counts of the keys
shed at stages `lo + 1, …, j`, each at its virtual destination. -/
def rnetState (ρ : RRoute K r b) (pos : K → RNode r b) (lo : ℕ) (h : K → Bits b) (j : ℕ) :
    States (RNode r b) := fun q =>
  match q.2 with
  | .main => ((ρ.mainAt h j).filter (fun x => rdest pos h j x = q.1)).card
  | .shadow => ((ρ.mainAt h lo \ ρ.mainAt h j).filter (fun x => rdest pos h j x = q.1)).card

/-- Phantom arrivals: every key of `K`, counted at its virtual destination
after stage `j`. -/
def rrawArrivals [Fintype K] (pos : K → RNode r b) (h : K → Bits b) (j : ℕ) : RNode r b → ℕ :=
  fun V => (Finset.univ.filter (fun x => rdest pos h j x = V)).card

/-- The coarse-range count of class `a` and the range of `R` (in-block bits
`≥ lo`), under words `h` and classes `c`: the early keys and the late binary
sheds whose final home `(c x, h x)` lies in the range, plus the radix node's
sheds at each bucket `p` of the range (the main keys after the last binary
stage at bucket `p` of class `a`, beyond the first `C`). -/
def rRangeCount (ρ : RRoute K r b) (C lo : ℕ) (early : (K → Bits b) → Finset K) (R : Bits b)
    (a : Fin r) (h : K → Bits b) (c : K → Fin r) : ℕ :=
  ((early h).filter (fun x => InRange lo R (h x) ∧ c x = a)).card +
    ((ρ.mainAt h lo \ ρ.mainAt h b).filter (fun x => InRange lo R (h x) ∧ c x = a)).card +
    ∑ p ∈ rangeHomes lo R, (((ρ.mainAt h b).filter (fun x => h x = p ∧ c x = a)).card - C)

/-- The average over the classes: key `x` is of class `c x` with probability
`q (c x)`, independently across keys. -/
noncomputable def classAvg [Fintype K] (q : Fin r → I) (F : (K → Fin r) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ c : K → Fin r, (∏ x, ENNReal.ofReal (q (c x))) * F c

/-- Every node, as a list. -/
noncomputable def allRNodes (r b : ℕ) : List (RNode r b) :=
  (Finset.univ : Finset (RNode r b)).toList

/-- The terminal radix test of the range of `R` in a class of mass `q`: thin
every node by `q`, add each block's node `(i, p)` into the radix node `p`, cap
at `C`, then the stop-loss of the range's shadow counts plus an independent
early count `Bin(P, p_e)`. -/
noncomputable def radixTermTest (C P : ℕ) (pe q : I) (L lo : ℕ) (R : Bits b)
    (x : States (RNode r b)) : ℝ≥0∞ :=
  thinAll (allRNodes r b) (fun _ => q)
    (termTest P pe L lo R ∘ capAll (allNodes b) C ∘ sumAlong (fun V : RNode r b => V.2)) x

/-- One backward binary stage of the range's forest in every block: every node
is thinned by `1/2`, added into the node of its block with bit `j` of `R`, and
capped at `C`. -/
noncomputable def rBackStage (C : ℕ) (R : Bits b) (j : ℕ) (ψ : States (RNode r b) → ℝ≥0∞) :
    States (RNode r b) → ℝ≥0∞ :=
  if hj : j < b then
    thinAll (allRNodes r b) (fun _ => half)
      (ψ ∘ capAll (allRNodes r b) C ∘
        sumAlong (fun V : RNode r b => (V.1, Function.update V.2 ⟨j, hj⟩ (R ⟨j, hj⟩))))
  else ψ

/-- The backward test through binary stages `j + 1, …, b` of the range's forest
in every block, on the state after stage `j`, for the terminal test `φ`. -/
noncomputable def rForestTest (C : ℕ) (R : Bits b) (φ : States (RNode r b) → ℝ≥0∞) (j : ℕ) :
    States (RNode r b) → ℝ≥0∞ :=
  (List.range (b - j)).foldr (fun i ψ => rBackStage C R (j + i) ψ) φ

/-- The backward test at the first counted arrivals `N` (stage `lo + 1`, before
its cap), with the radix terminal test of a class of mass `q` and the early
probability `q 2^-(b - lo)`. -/
noncomputable def rFirstArrivalTest (C P L lo : ℕ) (R : Bits b) (q : I) (N : RNode r b → ℕ) :
    ℝ≥0∞ :=
  rForestTest C R (radixTermTest C P (q * halfPow (b - lo)) q L lo R) (lo + 1)
    (capAll (allRNodes r b) C (mainEmbed N))

end RebuildBound.Spec
