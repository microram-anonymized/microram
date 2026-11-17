import RebuildBound.Proofs.G3
import RebuildBound.Proofs.D8bfin

/-!
# G3fin: the top finish's first-failure bound, assembled

`RebuildBound.G3_of` (package G3) applied to T4top (D8bfin).
-/

/-- **G3, the top finish's first-failure bound.** -/
theorem RebuildBound.G3 : RebuildBound.Spec.G3_statement :=
  RebuildBound.G3_of RebuildBound.T4top
