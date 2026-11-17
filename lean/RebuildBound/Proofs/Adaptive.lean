import RebuildBound.Proofs.Adaptive.Semantics
import RebuildBound.Proofs.AdaptiveCausal
import RebuildBound.Proofs.AdaptiveCell
import RebuildBound.Proofs.AdaptiveSepA
import RebuildBound.Proofs.AdaptiveSepU
import RebuildBound.Proofs.AdaptiveLevelOneA
import RebuildBound.Proofs.AdaptiveLevelOneBU
import RebuildBound.Proofs.AdaptiveTop
import RebuildBound.Proofs.AdaptiveCompose
import RebuildBound.Proofs.AdaptiveAssembly

/-!
# The adaptive capacity and observation headlines

The composition of the adaptive packages. The
deterministic steps give row causality and the replay identity, so the exact
law lifts from the fixed-run one, and the realized trace is a causal function
of the joint tape (`AdaptiveCausal31`). The per-job cells bound every
first-failure event by its class budget on such a trace, and G4a per chunk
gives `h · 2^-64` (`CausalWindows31`); the key-universe transport and the
failure transfer finish the capacity and observation bounds.
`Proofs/Adaptive/Flags.lean` extends admissibility to clients whose
unshadowed flags follow the engine's rule (`Spec/AdaptiveNative.lean`).
-/

namespace RebuildBound
open Spec

namespace AdaptiveProof

theorem adaptiveCausal31 : AdaptiveCausal31_statement :=
  AdaptiveCausalStep rowCausality TraceUnitsPrefix ReplayShape adaptiveReplay

theorem causalSep31 : CausalSep31_statement :=
  CausalSepStep (CausalSepAStep TracePrefix CausalCell) (CausalSepUStep TracePrefix CausalCell)

theorem causalLevelOne31 : CausalLevelOne31_statement :=
  CausalLevelOneStep (CausalLevelOneAStep TracePrefix CausalCell)
    (CausalLevelOneBUStep TracePrefix CausalCell)

theorem causalWindows31 : CausalWindows31_statement :=
  CausalWindowsStep AdaptiveCovering31 causalSep31 causalLevelOne31 (CausalTopStep TracePrefix CausalCell)

end AdaptiveProof

/-- **AdaptiveWindows31**: the realized run fails within `h` chunks with
probability at most `h · 2^-64`. -/
theorem AdaptiveWindows31 : AdaptiveWindows31_statement :=
  AdaptiveWindowsUniverse _ _
    (AdaptiveNumericWindowsStep AdaptiveProof.adaptiveCausal31 AdaptiveProof.causalWindows31)

/-- **AdaptiveOblivious31**: every observation that agrees with the transcript
off the adaptive failure is within `h · 2^-64` of the simulator. -/
theorem AdaptiveOblivious31 : AdaptiveOblivious31_statement :=
  AdaptiveObliviousAssembly _ _ AdaptiveExact31 AdaptiveWindows31

end RebuildBound
