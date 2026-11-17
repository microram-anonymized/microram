import RebuildBound.Spec.Configuration31
import RebuildBound.Spec.Adaptive.Semantics
import RebuildBound.Spec.KeyUniverse
import RebuildBound.Spec.Model.Adaptive

/-!
# Adaptive clients (trusted statements)

The fixed-universe batch statements
(`Spec/KeyRelabel.lean`) for a client whose keys and values depend on every
bucket it has observed (`Model.Adaptive`). The public shape and the schedule
are fixed by the program, never by the client, so the simulator is
the existing `simLaw` of the public shape. The tapes are jointly uniform: the
realized run depends on the dummy words the client sees. That the engine's
observation agrees with the transcript off failure is a hypothesis (a
native-correspondence premise), argued outside Lean. `Spec/AdaptiveCheck.lean` checks the model against fixed runs.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.Adaptive

/-- **AdaptiveExact31**: the exact law at every positive chunk horizon of
`geometry31`. -/
def AdaptiveExact31_statement : Prop :=
  ∀ h, 1 ≤ h → AdaptiveExactFor (geometry31.chunk h)

/-- **AdaptiveWindows31**: at most `h · 2^-64` over `h` chunks of `2^32`
accesses, for every adaptive client whose keys, on every candidate
transcript, lie in one universe of at most `2^31` keys fixed before the tapes. -/
def AdaptiveWindows31_statement : Prop :=
  AdaptiveWindowsFor geometry31 (ENNReal.ofReal (1 / (2 : ℝ) ^ 64))

/-- **AdaptiveOblivious31**: distance at most `h · 2^-64` from the public
simulator. -/
def AdaptiveOblivious31_statement : Prop :=
  AdaptiveObliviousFor geometry31 (ENNReal.ofReal (1 / (2 : ℝ) ^ 64))

end RebuildBound.Spec
