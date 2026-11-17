import RebuildBound.Spec.Model.ApiAccess
import RebuildBound.Spec.ApiCorrectness

/-! The hierarchy callback API reduces to existing API correctness using the
actual effective probe selection. Callback inputs are proved correct, never
assumed to equal a logical-map lookup. The contract concerns normalized pure
callbacks; it asserts no confidentiality of arbitrary callback effects. -/
namespace RebuildBound.Model.ApiAccess
open Hierarchy Online

/-- Local execution obligations for one callback operation embedded anywhere in
a mixed run. `selected` is the actual source probe; the emitted requests and
actual response follow the callback on that selection. Existing `Implements`
checks all inserted records, including inherited tombstone flags. -/
structure Local (c : Api.Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (words : Words)
    (dummy : Nat → Nat → Nat) (requests pre suffix : List Api.Request)
    (q : Request) (selected : Option Rec) (returned : Response) : Prop where
  selected_eq : selected = (Probe.batch cfg sh g run S words dummy pre.length).found
  requests_eq : requests = pre ++ lower q (Api.value c selected) ++ suffix
  implements : Api.Implements c cfg sh g run S words dummy requests
  response_eq : returned = response q (Api.value c selected)

/-- Correct callback input, original-presence return (or exception), and the
whole map after the operation. The independent map update preserves every other
key, overwrites the destination, and restores the source if the callback throws. -/
def Correct (c : Api.Codec) (run : OnlineBatch.BatchRun) (requests pre : List Api.Request)
    (q : Request) (selected : Option Rec) (returned : Response) : Prop :=
  let before := Api.stateAt (Api.stateOf c run.init) requests pre.length
  Api.value c selected = before q.key ∧
    returned = response q (before q.key) ∧
    Api.stateOf c (Api.historyAt run
      (pre.length + (lower q (before q.key)).length)) = step q before

end RebuildBound.Model.ApiAccess

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online

/-- Pure semantic lowering, with no hierarchy or lookup premise. -/
def ApiAccessLowering_statement : Prop :=
  ∀ (q : ApiAccess.Request) (state : Api.State),
    Api.stateAt state (ApiAccess.lower q (state q.key))
      (ApiAccess.lower q (state q.key)).length = ApiAccess.step q state

/-- Generic reduction: existing API correctness and local callback execution
imply the independent callback contract, including correctness of callback inputs. -/
def ApiAccessCorrectness_statement : Prop :=
  ∀ (c : Api.Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (words : Words)
    (dummy : Nat → Nat → Nat) (requests pre suffix : List Api.Request)
    (q : ApiAccess.Request) (selected : Option Rec) (returned : ApiAccess.Response),
    ApiCorrect c cfg sh g run S words dummy requests →
    ApiAccess.Local c cfg sh g run S words dummy requests pre suffix q selected returned →
    ApiAccess.Correct c run requests pre q selected returned

/-- Fixed hierarchy headline; no selected-value correctness, callback-input
correctness, final-map equality, success-event, or probability premise is assumed. -/
def BatchApiAccessCorrectness31_statement : Prop :=
  ∀ h, 1 ≤ h → ∀ U g run S m,
    UniverseBatchSetting (geometry31.chunk h) U g run S (OnlineBatch.slots run).length m →
    ∀ (c : Api.Codec) (words : Words) (dummy : Nat → Nat → Nat)
      (requests pre suffix : List Api.Request) (q : ApiAccess.Request)
      (selected : Option Rec) (returned : ApiAccess.Response),
      ApiAccess.Local c (geometry31.chunk h).cfg (geometry31.chunk h).shapes
        g run S words dummy requests pre suffix q selected returned →
      ApiAccess.Correct c run requests pre q selected returned

end RebuildBound.Spec
