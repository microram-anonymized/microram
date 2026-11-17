import RebuildBound.Proofs.D8
import RebuildBound.Proofs.D8b

/-!
# D8bfin: the top finish's first-failure inventory, assembled

`RebuildBound.T4top_of` (package D8b) applied to T3top (package D8).
-/

/-- **T4top, the finish's first-failure inventory.** -/
theorem RebuildBound.T4top : RebuildBound.Spec.T4top_statement :=
  RebuildBound.T4top_of RebuildBound.T3top
