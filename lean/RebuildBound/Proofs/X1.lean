import RebuildBound.Proofs.X1.Cap
import RebuildBound.Proofs.X1.Thin
import RebuildBound.Proofs.X1.AddTerminal

/-!
# X1: closure of class 𝒯 under the backward operations

The four registered theorems of package X1 live in the submodules:

* `RebuildBound.X1_cap` in `X1/Cap.lean`;
* `RebuildBound.X1_thin` in `X1/Thin.lean`;
* `RebuildBound.X1_add` and `RebuildBound.X1_terminal` in `X1/AddTerminal.lean`.

Probability API: measure-based throughout (`ProbabilityTheory.binomial` and
`lintegral`); there is no fallback to `PMF` or to finite sums.

Obstacle recorded: Mathlib has no recurrence in `n` for `binomial n p`.
`X1/Binomial.lean` derives `Bin(n + 1, p) = (1 - p) • Bin(n, p) + p • Bin(n, p).map (· + 1)`
from `binomial_singleton` and Pascal's rule (`Nat.choose_succ_succ'`), then its
`lintegral` form, stochastic monotonicity in `n`, and the support bound `m ≤ n`.
-/
