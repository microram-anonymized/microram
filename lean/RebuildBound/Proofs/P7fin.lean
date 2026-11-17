import RebuildBound.Proofs.P7
import RebuildBound.Proofs.P7alg

/-!
# P7fin: the positive series, assembled

`P7_of` (package P7) applied to P7alg.
-/

theorem RebuildBound.P7 : RebuildBound.Spec.P7_statement :=
  RebuildBound.P7_of RebuildBound.P7alg
