import RebuildBound.Proofs.AdaptiveFlagSound
import RebuildBound.Proofs.AdaptiveFlagAdmissible.Semantics
import RebuildBound.Proofs.Adaptive.Semantics

/-!
# Admissibility with unshadowed flags

The composition for `AdaptiveFlagAdmissible31`: a client whose unshadowed
flags follow the engine's rule on every branch meets the adaptive setting,
the unshadowed promise included (`FlagSoundness31`). It imports only the
deterministic flag and replay proofs, independently of numerical capacity bounds.
-/

namespace RebuildBound
open Spec

/-- **AdaptiveFlagAdmissible31**: every client whose flags follow the engine's
rule on every branch meets the adaptive setting. -/
theorem AdaptiveFlagAdmissible31 : AdaptiveFlagAdmissible31_statement :=
  AdaptiveFlagAdmissibleStep FlagSoundness31 RequesterTrace ReplayShape

end RebuildBound
