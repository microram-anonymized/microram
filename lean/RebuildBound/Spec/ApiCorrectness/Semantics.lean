import RebuildBound.Spec.ApiCorrectness.Core
import RebuildBound.Spec.AdaptiveNative.Semantics

/-! Generic API correctness and local flag construction. Native agreement remains an explicit refinement obligation. -/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online

/-- Generated post-record flags satisfy the existing native flag contract.
Only local construction and agreement of the run's flag reader with the codec
are required; no unshadowed promise or API correctness is assumed. -/
def ApiFlagRule_statement : Prop :=
  ∀ (c : Api.Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (words : Words) (dummy : Nat → Nat → Nat)
    (requests : List Api.Request),
    (∀ r, run.unsh r = c.flag r.val) →
    Api.Implements c cfg sh g run S words dummy requests →
    FlagRule cfg sh g run S words

/-- The explicit sequential construction realizes the same map for every prefix,
without any hierarchy or tape premise. This also witnesses the API history model. -/
def ApiReferenceCorrectness_statement : Prop :=
  ∀ (c : Api.Codec) (init : List Rec) (requests : List Api.Request) t,
    t ≤ requests.length →
    Api.stateOf c (init ++ (Api.referenceRecords c init requests).take t) =
      Api.stateAt (Api.stateOf c init) requests t

end RebuildBound.Spec
