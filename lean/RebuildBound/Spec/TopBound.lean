import RebuildBound.Spec.Prob.Series

/-!
# The top finish's bound and its selected instance (trusted)

`REPORT.tex`, Corollary `cor:top-finish-separated` with
Proposition `prop:top-excess` at a binary top (`p_* = 1/T`, `Γ = 1`), in the
form

  `b_fin = [S_R > C] · 2^ρ · Φ_{K₁}(2^I, C, λ, C) + Φ_{K₂}(T, C, λ, S)`,

with `S = min(S_merge, S_tier)` and cutoffs `K₁ > C`, `K₂ > S`. The first term
is the union over the `2^ρ` coarse ranges of A's restricted excess above one
page; it vanishes when the retained carry fits one page. The second is the
resolved live set's excess above the merge stash or the tier, charged once.
G3 proves that a finish's first-failure contribution is at most
`topFinishBound`; TopNum2 (`Spec/Subtotal.lean`) checks its value at the
selected shape.

The arguments are plain numbers, so the bound does not depend on the model's
geometry record.
-/

namespace RebuildBound.Spec

/-- `[S_R > C] · 2^ρ · Φ_{K₁}(2^I, C, λ, C) + Φ_{K₂}(T, C, λ, S)`. -/
noncomputable def topFinishBound (C SR rho I T S K1 K2 : ℕ) (lam : ℝ) : ℝ :=
  (if C < SR then (2 : ℝ) ^ rho * Phi K1 (2 ^ I) C lam C else 0) + Phi K2 T C lam S

end RebuildBound.Spec
