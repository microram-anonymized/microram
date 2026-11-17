import RebuildBound.Spec.AdaptiveSteps

/-! Exact adaptive replay assembly, independent of causal job-capacity
interfaces and numerical assembly. -/

namespace RebuildBound.Spec

def AdaptiveExactStep_statement : Prop :=
  ReplayShape_statement → AdaptiveReplay_statement → AdaptiveExact31_statement

end RebuildBound.Spec
