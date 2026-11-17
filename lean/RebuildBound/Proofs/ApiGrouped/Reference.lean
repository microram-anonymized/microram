import RebuildBound.Spec.ApiGrouped
import RebuildBound.Proofs.ApiLowering

/-! Reference execution continues from each completed group's whole record
history. In particular, chunking preserves tombstones and encoded flags, not
only the decoded final map. These are chronological reference statements;
they do not assert equality of physical selections under different schedules. -/
namespace RebuildBound.ApiGroupedProof
open Model Model.PublicApi

/-- A continuation reads the complete records produced by its preceding input. -/
theorem referenceRecords_append (c : Api.Codec) (history : List Rec)
    (xs ys : List Api.Request) :
    Api.referenceRecords c history (xs ++ ys) =
      Api.referenceRecords c history xs ++
        Api.referenceRecords c (history ++ Api.referenceRecords c history xs) ys := by
  induction xs generalizing history with
  | nil => simp [Api.referenceRecords]
  | cons q xs ih =>
    simp only [List.cons_append, Api.referenceRecords]
    rw [ih]
    simp only [List.cons_append, List.append_assoc, List.nil_append]

/-- Group execution retains every generated record before entering its continuation. -/
theorem referenceGroups_flatten (c : Api.Codec) (found : Bool) (history : List Rec)
    (gs : List (PublicApi.Group Lane)) :
    referenceGroups c found history gs =
      Api.referenceRecords c history ((gs.flatMap Group.lanes).map (request found)) := by
  induction gs generalizing history with
  | nil => rfl
  | cons group rest ih =>
    simp only [referenceGroups, List.flatMap_cons, List.map_append]
    rw [referenceRecords_append, ih]

end RebuildBound.ApiGroupedProof

namespace RebuildBound
open Spec Model Model.PublicApi ApiGroupedProof

/-- The whole encoded reference trace is independent of the public internal cuts. -/
theorem ApiGroupedReference : ApiGroupedReference_statement := by
  intro c found history width entries position lanes
  rw [referenceGroups_flatten,
    (ApiLoweringStructure width entries position found lanes).1]

end RebuildBound
