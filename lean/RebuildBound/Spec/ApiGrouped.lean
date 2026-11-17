import RebuildBound.Spec.Model.ApiGrouped

namespace RebuildBound.Spec
open Model Model.PublicApi

/-- Invoking the adapter at every internal group, after arbitrary intervening
observations, gives exactly the lowering of the batch chosen before any of
those observations. Its public shape and schedule include every boundary cut.
The hypothesis is ordinary prefix extension, independent of secret tapes. -/
def ApiGroupedChoices_statement : Prop :=
  ∀ (Row : Type) (choose : Chooser Row) width entries position found descriptors
    (before : List Row) (observations : Nat → List Row),
    (∀ j, j < (indexedGroups width entries position found descriptors).length →
      (observations j).take before.length = before) →
    let emitted := dispatch choose before.length observations 0
      (indexedGroups width entries position found descriptors)
    emitted = groups width entries position found (chosenLanes choose before descriptors) ∧
    emitted.flatMap Group.lanes = chosenLanes choose before descriptors ∧
    emitted.map Group.shape = publicShape width entries position found descriptors ∧
    GroupsFit entries position emitted ∧
    ∀ schedule, groupSchedule emitted schedule =
      OnlineBatch.slotSchedule
        ((publicShape width entries position found descriptors).map Prod.snd) schedule

/-- Exact chronological reference records, including encoded flags, are
unchanged by lowering. No bound on keys, live population or successful capacity
execution is assumed. Physical selection correspondence remains separate. -/
def ApiGroupedReference_statement : Prop :=
  ∀ (c : Api.Codec) found history width entries position lanes,
    referenceGroups c found history (groups width entries position found lanes) =
      Api.referenceRecords c history (lanes.map (request found))

end RebuildBound.Spec
