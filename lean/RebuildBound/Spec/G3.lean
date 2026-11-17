import RebuildBound.Spec.Model.TopLaw
import RebuildBound.Spec.TopBound

/-!
# Glue: the top finish's first-failure bound (trusted)

`REPORT.tex`, Corollary
`cor:top-finish-separated` with Proposition `prop:top-excess` at a binary
top (`p_* = 1/T`, so `Γ = 1`).

* **G3**, for every geometry in the model's domain, every unshadowed flag,
  every law meeting `TopLaw` and every pair of cutoffs `K₁ > C`,
  `K₂ > min(S_merge, S_tier)`: the finish's first-failure contribution, the
  probability that its retained carry and B's tier fit (`TopTiersFit`) and it
  fails, is at most `topFinishBound`:
  `[S_R > C] 2^ρ Φ_{K₁}(2^I, C, λ, C) + Φ_{K₂}(T, C, λ, min(S_merge, S_tier))`.
  For a direct plan the first term is not needed (there is no range event),
  but the bound stays valid.
  It follows from T4top, P8a and P7: `R_r` is the restricted excess of the
  fixed set A under uniform homes, and `E_f` the excess of the fixed set W.
* `selectedTop`: both selected configurations share this top-finish row;
  TopSel2 (`Spec/Subtotal.lean`) applies G3 at cutoffs 256 and TopNum2 to it.

As in G1, the event is a first-failure contribution, not a conditional
probability: every "no earlier failure" event implies `TopTiersFit`.
-/

open scoped ENNReal NNReal

namespace RebuildBound.Spec

open RebuildBound.Model

/-- The first-failure event of one top finish. -/
def topFailEvent {g : TopGeom} (L : TopJobLaw g) (unsh : Rec → Bool) (hist : L.Hist)
    (w : LogicalKey → Nat) : Prop :=
  TopTiersFit g (L.inputs hist w) ∧ (topJob g unsh w (L.inputs hist w)).toBool = false

/-- **G3, the top finish's first-failure bound.** -/
def G3_statement : Prop :=
  ∀ (g : TopGeom) (L : TopJobLaw g) (unsh : Rec → Bool) (lam : ℝ≥0) (K1 K2 : ℕ),
    TopLaw L unsh lam → g.Valid → g.C < K1 → min g.SMerge g.STier < K2 →
    L.prob (topFailEvent L unsh) ≤
      ENNReal.ofReal (topFinishBound g.C g.SR g.rho g.I g.T (min g.SMerge g.STier) K1 K2 lam)

/-- The top-finish row of both selected configurations: `T = 2^22` homes
(`D = 8`, `U = 2^19`), a two-page retained carry, two direct B-tier pages, a
two-page merge stash and tier, and 16 coarse ranges of `2^18` homes. -/
def selectedTop : TopGeom :=
  { C := 64, k := 19, e := 3, rho := 4, I := 18, dfs := true,
    rPages := 2, bPages := 2, mergePages := 2, tierPages := 2 }

end RebuildBound.Spec
