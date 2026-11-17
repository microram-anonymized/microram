import RebuildBound.Spec.ApiGrouped
import RebuildBound.Proofs.ApiLowering

namespace RebuildBound.ApiGroupedProof
open Model Model.PublicApi

theorem chosen_descriptors {Row : Type} (choose : Chooser Row) (rows : List Row)
    (descriptors : List Descriptor) :
    (chosenLanes choose rows descriptors).map Lane.descriptor = descriptors := by
  simpa only [chosenLanes, List.map_map, Function.comp_def, chosenLane] using
    List.zipIdx_map_fst 0 descriptors

theorem groups_chosen {Row : Type} (choose : Chooser Row) (rows : List Row)
    (width entries position : Nat) (found : Bool) (descriptors : List Descriptor) :
    groups width entries position found (chosenLanes choose rows descriptors) =
      (indexedGroups width entries position found descriptors).map
        (Group.map (chosenLane choose rows)) := by
  unfold groups chosenLanes indexedGroups partition
  simp only [List.length_map]
  exact ApiLoweringProof.partition_map_aux width entries position _ _ _ _

/-- Different internal calls may receive unrelated suffixes, of arbitrary
length and contents. Agreement on the pre-batch prefix alone suffices. -/
theorem dispatch_eq {Row : Type} (choose : Chooser Row) (before : List Row)
    (observations : Nat → List Row) (j : Nat) (plan : List (PublicApi.Group (Descriptor × Nat)))
    (h : ∀ i, j ≤ i → i < j + plan.length →
      (observations i).take before.length = before) :
    dispatch choose before.length observations j plan =
      plan.map (Group.map (chosenLane choose before)) := by
  induction plan generalizing j with
  | nil => rfl
  | cons group rest ih =>
    simp only [dispatch, List.map_cons]
    rw [h j (by omega) (by simp)]
    rw [ih (j + 1) (by intro i hi hj; apply h i <;> simp_all <;> omega)]

theorem shape_width (group : PublicApi.Group Lane) : group.shape.2 = group.lanes.length := by
  cases group <;> rfl

theorem schedule_of_shape (emitted : List (PublicApi.Group Lane)) (shape : List (Bool × Nat))
    (h : emitted.map Group.shape = shape) (schedule : Online.Schedule) :
    groupSchedule emitted schedule = OnlineBatch.slotSchedule (shape.map Prod.snd) schedule := by
  rw [← h]
  simp only [groupSchedule, List.map_map, Function.comp_def, shape_width]

end RebuildBound.ApiGroupedProof

namespace RebuildBound
open Spec Model Model.PublicApi ApiGroupedProof

theorem ApiGroupedChoices : ApiGroupedChoices_statement := by
  intro Row choose width entries position found descriptors before observations h
  dsimp only
  have heq := dispatch_eq choose before observations 0
    (indexedGroups width entries position found descriptors) (by
      intro i _ hi
      exact h i (by simpa using hi))
  rw [← groups_chosen] at heq
  rw [heq]
  have hs := ApiLoweringStructure width entries position found
    (chosenLanes choose before descriptors)
  have hshape := hs.2.2.1
  rw [chosen_descriptors] at hshape
  exact ⟨rfl, hs.1, hshape, hs.2.2.2, fun schedule => schedule_of_shape _ _ hshape schedule⟩

end RebuildBound
