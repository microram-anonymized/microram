import RebuildBound.Proofs.AdaptiveTracePrefix
import RebuildBound.Proofs.AdaptiveRequester
import RebuildBound.Proofs.AdaptiveRowCausality
import RebuildBound.Proofs.AdaptiveReplay
import RebuildBound.Proofs.AdaptiveAssembly.Exact

/-!
# Adaptive replay and exact transcript semantics

The deterministic replay and admissibility results, and the exact ideal-tape
law, do not use a capacity-failure bound. Numerical adaptive bounds are
assembled separately in `Proofs.Adaptive`.
-/

namespace RebuildBound
open Spec

namespace AdaptiveProof

theorem rowCausality : RowCausality_statement := RowCausalityStep TracePrefix TraceUnitsPrefix

theorem adaptiveReplay : AdaptiveReplay_statement := AdaptiveReplayStep rowCausality ReplayShape

end AdaptiveProof

/-- **AdaptiveExact31**: the transcript of every adaptive client is
measurable and has exactly the public simulator's law. -/
theorem AdaptiveExact31 : AdaptiveExact31_statement :=
  AdaptiveExactStep ReplayShape AdaptiveProof.adaptiveReplay

/-- **AdaptiveConstant**: the adaptive model specializes to the fixed-run one. -/
theorem AdaptiveConstant : AdaptiveConstant_statement :=
  AdaptiveConstantStep AdaptiveProof.rowCausality ReplayShape

/-- **AdaptiveAdmissible**: every client whose records have keys in `U` meets
the adaptive setting. -/
theorem AdaptiveAdmissible : AdaptiveAdmissible_statement :=
  AdaptiveAdmissibleStep RequesterTrace ReplayShape

end RebuildBound
