import RebuildBound.Spec.AdaptiveApi
import RebuildBound.Spec.NativeAdapter

/-!
# Local API obligations of the abstract native adapter

The selected entry, inserted postrecord, and normalized confidential response
are separate interface components. Their local equations imply API correctness;
no equality to a complete logical execution is assumed. Responses are separate
from the attacker's `Machine.observe`: exposing confidential API values there
would require a different leakage claim. Optional output buffers are projections
of these normalized answers; native byte encoding and aliasing remain outside.
-/
namespace RebuildBound.Model.NativeApi
open Hierarchy Online Adaptive NativeAdapter

/-- A normalized confidential response: scalar Write returns unit, while batch
Write can return the previous presence and value. `none` means absent, with a
false presence bit and zero payload when an output buffer is supplied. -/
inductive Response where
  | scalar (answer : Api.ScalarReply)
  | batch (previous : Option Nat)
  deriving DecidableEq, BEq, Repr

/-- The return convention is determined by the enclosing public operation. -/
def response (run : OnlineBatch.BatchRun) (s : OnlineBatch.Slot)
    (q : Api.Request) (old : Option Nat) : Response :=
  match run.ops[s.op]? with
  | some (.batch _) => .batch (Api.reply q old)
  | _ => .scalar (Api.scalarReply q old)

/-- The records actually issued by the abstract native machine. -/
def machineRun {State View : Type} (M : Machine State View) (p : Program View) :
    OnlineBatch.BatchRun :=
  ⟨(M.prefix p p.shape).1, p.init, p.unsh⟩

/-- Per-slot refinement obligations. `selected` is the effective selected entry
after batch forwarding. The equations concern selection, construction, and
response decoding separately, without assuming prefix or final-map correctness. -/
structure Local (c : Api.Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (words : Words)
    (dummy : Nat → Nat → Nat) (requests : List Api.Request)
    (selected : Nat → Option Rec) (returned : Nat → Response) : Prop where
  length : requests.length = (OnlineBatch.slots run).length
  slot : ∀ t q s, requests[t]? = some q → (OnlineBatch.slots run)[t]? = some s →
    s.record.key = q.key ∧ s.probes = q.probes ∧
      selected t = (Probe.batch cfg sh g run S words dummy t).found ∧
      s.record = Api.postRecord c q (selected t) ∧
      returned t = response run s q (Api.value c (selected t))

/-- Every prefix implements the independent logical map, and the normalized
native responses are its prior values with the appropriate scalar/batch convention. -/
def Correct (c : Api.Codec) (run : OnlineBatch.BatchRun) (requests : List Api.Request)
    (returned : Nat → Response) : Prop :=
  (∀ t, t ≤ requests.length →
    Api.stateOf c (Api.historyAt run t) = Api.stateAt (Api.stateOf c run.init) requests t) ∧
    ∀ t q s, requests[t]? = some q → (OnlineBatch.slots run)[t]? = some s →
      returned t = response run s q
        (Api.stateAt (Api.stateOf c run.init) requests t q.key)

end RebuildBound.Model.NativeApi

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.Adaptive Model.NativeAdapter

/-- Local selected-entry, insertion, and response equations suffice for complete
API behavior of a fixed mixed scalar/batch run. -/
def NativeApiCorrectness31_statement : Prop :=
  ∀ h, 1 ≤ h → ∀ U g run S m,
    UniverseBatchSetting (geometry31.chunk h) U g run S (OnlineBatch.slots run).length m →
    ∀ (c : Api.Codec) (words : Words) (dummy : Nat → Nat → Nat)
      (requests : List Api.Request) selected returned,
      NativeApi.Local c (geometry31.chunk h).cfg (geometry31.chunk h).shapes
        g run S words dummy requests selected returned →
      NativeApi.Correct c run requests returned

/-- The same API conclusion for the operations actually issued by an abstract
native machine. Local observation simulation derives equality to the folded
adaptive run; local API equations then derive map and response correctness.
The all-branch adaptive setting is still an explicit premise. -/
def NativeAdapterApiCorrectness31_statement : Prop :=
  ∀ h, 1 ≤ h → ∀ (U : Finset LogicalKey) (g : OnlineGeom) (m : Nat)
    (Public View State : Type) (p : Program View) (encode : Encoding m Public View)
    metadata (S : Schedule) (n : Nat),
    AdaptiveSetting (geometry31.chunk h) U g (p.folded encode metadata) S n →
    ∀ (M : Machine State View) (words : Words) (dummy : Nat → Nat → Nat) R,
      NativeLocalAgreement (geometry31.chunk h).cfg (geometry31.chunk h).shapes
        g S p encode metadata M words dummy R →
      ∀ (c : Api.Codec) (requests : List Api.Request) selected returned,
        NativeApi.Local c (geometry31.chunk h).cfg (geometry31.chunk h).shapes
          g (NativeApi.machineRun M p) S words dummy requests selected returned →
        NativeApi.Correct c (NativeApi.machineRun M p) requests returned

end RebuildBound.Spec
