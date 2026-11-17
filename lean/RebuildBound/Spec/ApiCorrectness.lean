import RebuildBound.Spec.ApiCorrectness.Semantics
import RebuildBound.Spec.Model.Api
import RebuildBound.Spec.AdaptiveNative

/-!
# API correctness of the serialized reference execution

The local implementation relation supplies the requested action and constructs
its post-operation record from the effective probe result. The theorem derives
all prefix maps and actual answers, including duplicate batch lanes. It has no
capacity-success or probabilistic premise. Native byte encoding, key hashing,
input/output buffer behavior, and bounded execution remain refinement duties.
-/
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online

/-- Logical keys with 64-bit fixture identifiers, mixed scalar and chunk operations, all routing
and dummy tapes: the supplied local post-record implementation realizes API semantics. -/
def BatchApiCorrectness31_statement : Prop :=
  ∀ h, 1 ≤ h → ∀ U g run S m,
    UniverseBatchSetting (geometry31.chunk h) U g run S (OnlineBatch.slots run).length m →
    ∀ (c : Api.Codec) (words : Words) (dummy : Nat → Nat → Nat) (requests : List Api.Request),
      Api.Implements c (geometry31.chunk h).cfg (geometry31.chunk h).shapes
        g run S words dummy requests →
      ApiCorrect c (geometry31.chunk h).cfg (geometry31.chunk h).shapes
        g run S words dummy requests

/-- Structural caller premises and local API construction imply all hierarchy
setting obligations, including the unshadowed promise. In particular callers do
not separately assume flag soundness, lookup correctness, or API correctness. -/
def ApiAdmissible31_statement : Prop :=
  ∀ h, 1 ≤ h → ∀ (U : Finset LogicalKey) (g : OnlineGeom) (run : OnlineBatch.BatchRun)
    (S : Schedule) (m : Nat) (c : Api.Codec) (words : Words)
    (dummy : Nat → Nat → Nat) (requests : List Api.Request),
    (∀ k ∈ U, k.toNat < 2 ^ 64) → U.card ≤ keyCapacity31 →
    g.unitEntries * g.unitsPerPrefix = (geometry31.chunk h).cfg.carryPositions 1 →
    0 < g.unitEntries → (OnlineBatch.slots run).length ≤ (geometry31.chunk h).cfg.horizon →
    (run.init.map Rec.key).Nodup → (∀ r ∈ run.init, r.key ∈ U) →
    (∀ q ∈ requests, q.key ∈ U) →
    SchedulePremises (geometry31.chunk h).cfg S (OnlineBatch.slots run).length m →
    (∀ r, run.unsh r = c.flag r.val) →
    Api.Implements c (geometry31.chunk h).cfg (geometry31.chunk h).shapes
      g run S words dummy requests →
    UniverseBatchSetting (geometry31.chunk h) U g run S (OnlineBatch.slots run).length m

end RebuildBound.Spec
