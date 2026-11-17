import RebuildBound.Spec.Model.Law
import RebuildBound.Spec.Prob.Subset
import RebuildBound.Spec.Prob.ShadowTree

/-!
# Glue: the pilot theorem and the completed-A bound at d = 2 (trusted)

Packages G1 and G2. Under `InputLaw` (one job, ideal
merge-family words, A's old history with density factor `D`):

* **G2, completed-A coarse ranges** (Proposition "Completed-A coarse-range
  bound", case `r = 1`, form (CA)): the probability that some reference
  coarse count exceeds the leaf capacity `L` is at most
  `D 2^(b - lo) E (Y - L)₊`, where `Y` is `Bin(P, 2^-(b - lo))` plus `2^lo`
  independent root losses of the depth-`(b - lo)` shadow tree at load `λ`,
  and `P = T_A + Σ_{j < lo} S_j` bounds the early list. It needs `lo < k`.
* **G1, the pilot theorem**: the job's first-failure contribution, the
  probability that its input tiers fit their public capacities and it fails,
  is at most
  `Σ_j D B_sub(2U, S_j)` (stage stashes, raw excess of the complete A
  population) `+ a_range` (the coarse-range event, a hypothesis here and
  discharged by G2) `+ B_sub(2U, min(S_insert, S_output))` (the complete
  union's home excess, at density 1 since the merge family's homes are
  uniform at d = 2).

G1 follows from T4a, T4b, P3 and the union bound; G2 from P11ab, P11d, P11e
and the model's route as a `BlindRoute` (T5).

The event of G1 and `Pilot` is a first-failure contribution, not a
conditional probability. On outcomes where a producer failed earlier, the
inputs are reference outputs whose tiers may overflow, and the job's failure
there is charged to the producer. Every event "no earlier job failed"
implies `TiersFit`, so these bounds are the job's terms in the composition
theorem. The reference events of the bounds themselves are defined, and
bounded, on the whole ideal-word space.
-/

open scoped ENNReal NNReal

namespace RebuildBound.Spec

open RebuildBound.Model

/-- The reference coarse-range event: some coarse range's reference count
exceeds the leaf capacity `Lf`, with the early list truncated to
`T_A + Σ_{j < lo} S_j`. -/
def rangeEvent (g : Geom) (L : JobLaw g) (rule : CapRule) (TA : Nat) (S : Nat → Nat)
    (Lf : Nat) (hist : L.Hist) (w : LogicalKey → Nat) : Prop :=
  ∃ R < g.ranges, Lf < refCoarse g w (reference rule g w (L.inputs hist w))
    (L.inputs hist w) (TA + sumUpTo S g.lo) R

/-- **G1, the pilot theorem at d = 2.** -/
def G1_statement : Prop :=
  ∀ (g : Geom) (L : JobLaw g) (TA TB : Nat) (lam D : ℝ≥0) (rule : CapRule) (caps : Caps)
    (S : Nat → Nat) (Lf Si So : Nat) (aRange : ℝ≥0∞),
    InputLaw L lam D → rule.Valid → 0 < lam → (lam : ℝ) ≤ g.C →
    (∀ j < g.stages, caps.stash j = some (S j)) → caps.leaf = some Lf →
    caps.ins = some Si → caps.out = some So →
    TA + sumUpTo S g.stages ≤ g.poolSlots →
    L.prob (rangeEvent g L rule TA S Lf) ≤ aRange →
    L.prob (fun hist w =>
        TiersFit TA TB (L.inputs hist w) ∧ (job rule g caps w (L.inputs hist w)).toBool = false) ≤
      (∑ j ∈ Finset.range g.stages, ENNReal.ofReal (Bsub g.homes g.C lam (S j) D)) +
        aRange + ENNReal.ofReal (Bsub g.homes g.C lam (min Si So) 1)

/-- **G2, the completed-A coarse-range bound at d = 2** (form (CA), `r = 1`). -/
def G2_statement : Prop :=
  ∀ (g : Geom) (L : JobLaw g) (TA : Nat) (lam D : ℝ≥0) (rule : CapRule)
    (S : Nat → Nat) (Lf : Nat),
    InputLaw L lam D → rule.Valid → g.lo < g.k →
    L.prob (rangeEvent g L rule TA S Lf) ≤
      (D : ℝ≥0∞) * 2 ^ (g.k + 1 - g.lo) *
        stopLoss (rangeLaw g.C lam (TA + sumUpTo S g.lo) (halfPow (g.k + 1 - g.lo))
          (2 ^ g.lo) (g.k + 1 - g.lo)) Lf

/-- **The d = 2 pilot bound**, G1 with the range term discharged by G2: the
first-failure contribution of one separated-sources merge at digit 2 under
`InputLaw` (its tiers fit and it fails) is at most the stage-stash subset bounds, plus the completed-A
range term (CA), plus the insertion/output subset bound. -/
def Pilot_statement : Prop :=
  ∀ (g : Geom) (L : JobLaw g) (TA TB : Nat) (lam D : ℝ≥0) (rule : CapRule) (caps : Caps)
    (S : Nat → Nat) (Lf Si So : Nat),
    InputLaw L lam D → rule.Valid → 0 < lam → (lam : ℝ) ≤ g.C → g.lo < g.k →
    (∀ j < g.stages, caps.stash j = some (S j)) → caps.leaf = some Lf →
    caps.ins = some Si → caps.out = some So →
    TA + sumUpTo S g.stages ≤ g.poolSlots →
    L.prob (fun hist w =>
        TiersFit TA TB (L.inputs hist w) ∧ (job rule g caps w (L.inputs hist w)).toBool = false) ≤
      (∑ j ∈ Finset.range g.stages, ENNReal.ofReal (Bsub g.homes g.C lam (S j) D)) +
        (D : ℝ≥0∞) * 2 ^ (g.k + 1 - g.lo) *
          stopLoss (rangeLaw g.C lam (TA + sumUpTo S g.lo) (halfPow (g.k + 1 - g.lo))
            (2 ^ g.lo) (g.k + 1 - g.lo)) Lf +
        ENNReal.ofReal (Bsub g.homes g.C lam (min Si So) 1)

end RebuildBound.Spec
