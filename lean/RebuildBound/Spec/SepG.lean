import RebuildBound.Spec.Model.SepLaw
import RebuildBound.Spec.Prob.Subset
import RebuildBound.Spec.Prob.RadixTree

/-!
# Glue at a general digit: the pilot theorem (trusted)

The counterpart of G1 (`Spec/G.lean`) at a general digit `d = r 2^e`, for the model
`Spec/Model/Sep.lean`. Under `SInputLaw` (one job, ideal merge-family words,
A's old history with density factor `D`):

* **The pilot inventory** (stated as SG1p in `Spec/SepBound.lean`, which
  replaces each `B_sub` below by `min(B_sub, D Φ_K)`): the job's first-failure
  contribution, the probability that A's tier fits its public capacity and the
  job (under the engine's schedule) fails, is at most
  - `k · D B_sub(N, S)` for the `k` stage stashes (raw excess of the complete
    A population at its raw destinations, whose old positions have density
    `D`), plus
  - when `r > 1`, `D_cur(|A|) B_sub(N, S)` for the radix stash (the complete A
    population's current-home excess), plus
  - `a_range`, the coarse-range event (a hypothesis here), plus
  - `D_cur(|A ∪ B|) B_sub(N, min(S_insert, S_output))` for the insertion stash
    and the output tier (the complete union's current-home excess).

  Every stash has `S = stashPages · C` records and the output tier
  `tierPages · C`. `D_cur` is `SepGeom.curDensity`, the density of current
  homes at an odd radix; it is 1 at `r = 1`.

The range event is stated for the stage-by-stage schedule, whose early list
is fixed by the words below bit `I` (ST5); ST6 transfers the engine
schedule's DFS failure to it. The inventory follows from ST4a, ST4b, ST6,
SEngine, P3 and the union bound.

* **SG2, the completed-A coarse-range bound** (Proposition "Completed-A
  coarse-range bound", form (CA), every odd `r`): for `I < K`, the probability
  of the range event is at most `D 2^(k - I) Σ_{a < r} E (Y_a - C)₊`, where
  `Y_a ∼ rangeLawR C λ P 2^I (k - I) r q_a`, `P = T_A + I S` and `q_a` the class
  masses of `W`-bit words (`qMass W k r a`). Each class has `2^(k - I)` coarse
  ranges. SG2 follows from P12ab, P12d and P12e, with the model's
  stage-by-stage route and terminal radix as an `RRoute` (ST5), the old-home
  density `D` and the union over the ranges.
-/

open scoped ENNReal NNReal

namespace RebuildBound.Spec

open RebuildBound.Model

/-- The reference coarse-range event under the stage-by-stage schedule: some
coarse range's reference count exceeds a leaf's capacity `C`, with the early
list truncated to `P = T_A + I S`. -/
def sRangeEvent (g : SepGeom) (L : SJobLaw g) (rule : CapRule) (hist : L.Hist)
    (w : LogicalKey → Nat) : Prop :=
  ∃ v < g.ranges, g.C < sRefCoarse g w (sReferenceWith rule g w (L.inputs hist w) g.canonicalOps)
    (L.inputs hist w) g.earlyCap v

/-- **SG2, the completed-A coarse-range bound at a general digit** (form (CA)). -/
def SG2_statement : Prop :=
  ∀ (g : SepGeom) (L : SJobLaw g) (lam D : ℝ≥0) (rule : CapRule),
    g.Valid → SInputLaw L lam D → rule.Valid → g.I < g.K →
    L.prob (sRangeEvent g L rule) ≤
      (D : ℝ≥0∞) * 2 ^ (g.k - g.I) *
        ∑ a ∈ Finset.range g.r,
          stopLoss (rangeLawR g.C lam g.earlyCap (2 ^ g.I) (g.k - g.I) g.r (qMass L.W g.k g.r a)) g.C

end RebuildBound.Spec
