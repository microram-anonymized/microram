import RebuildBound.Proofs.G1
import RebuildBound.Proofs.D4a
import RebuildBound.Proofs.D4b
import RebuildBound.Proofs.P3

/-!
# G1fin: assembly of the pilot theorem

`RebuildBound.G1_of` (package G1) proves the pilot theorem from the
statements of T4a, T4b and P3; this file applies it to their proofs.
-/

/-- **G1, the pilot theorem at d = 2.** -/
theorem RebuildBound.G1 : RebuildBound.Spec.G1_statement :=
  RebuildBound.G1_of RebuildBound.T4a RebuildBound.T4b RebuildBound.P3
