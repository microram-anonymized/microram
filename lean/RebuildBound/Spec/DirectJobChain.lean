import RebuildBound.Spec.Model.DirectJobChain
import RebuildBound.Spec.DirectPrefix
import Mathlib.Data.Finset.Dedup

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- Physical reordering of the unique old winners does not change freshness.
Every B unit is newer than A; within B the existing chronological rule applies. -/
def DirectJobHistoryStep_statement : Prop :=
  ∀ (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (out : Output) (history : List Rec),
    inp.aRecords.Perm (DirectPrefix.winners history) →
    runJob g oldWord word inp = .published out →
    (outputRecords out).Perm (DirectPrefix.winners (history ++ inp.bRecords))

end RebuildBound.Spec
