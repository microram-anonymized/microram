import RebuildBound.Spec.AdaptiveApi.Semantics
import RebuildBound.Spec.Adaptive
import RebuildBound.Spec.ApiCorrectness

/-!
# API correctness on realized adaptive runs

The adaptive setting quantifies over every candidate transcript. Replay
transfers it to the run actually issued under arbitrary routing and dummy
words. This deterministic bridge needs no probability or capacity-success
assumption.
-/

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.Adaptive

/-- API requests may depend on the interaction. For each actual tape, local
post-record construction implies all-prefix map and returned-answer correctness
for the realized run. No capacity-success or uniform-tape premise is needed. -/
def AdaptiveApiCorrectness31_statement : Prop :=
  ∀ h, 1 ≤ h → ∀ (U : Finset LogicalKey) (g : OnlineGeom) (m : Nat)
    (a : AdaptiveRun m) (S : Schedule) (n : Nat),
    AdaptiveSetting (geometry31.chunk h) U g a S n →
    ∀ (c : Api.Codec) (words : Words) (dummy : Nat → Nat → Nat)
      (requests : List Api.Request),
      let geo := geometry31.chunk h
      let run := realized geo.cfg geo.shapes g S a words dummy
      Api.Implements c geo.cfg geo.shapes g run S words dummy requests →
      ApiCorrect c geo.cfg geo.shapes g run S words dummy requests

end RebuildBound.Spec
