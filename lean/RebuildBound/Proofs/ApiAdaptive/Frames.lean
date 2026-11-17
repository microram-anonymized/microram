import RebuildBound.Spec.ApiAdaptive
import RebuildBound.Proofs.ApiGrouped.Choices

namespace RebuildBound.ApiAdaptiveProof
open Model Model.PublicApi Model.ApiAdaptive

@[simp] theorem frame_width (frame : Frame) : frame.kind.width = frame.group.lanes.length := by
  rcases frame with ⟨index, start, found, group⟩
  cases group <;> rfl

@[simp] theorem group_map_length {α β : Type} (f : α → β) (group : PublicApi.Group α) :
    (group.map f).lanes.length = group.lanes.length := by
  cases group <;> simp [Group.map, Group.lanes]

@[simp] theorem requests_width {m : Nat} (choose : ApiAdaptive.Chooser m)
    (rows : List (Fin m → Nat)) (frame : Frame) :
    (requests choose rows frame).lanes.length = frame.kind.width := by
  simp [requests]

theorem groupsFit_map {α β : Type} (entries : Nat) (f : α → β)
    (gs : List (PublicApi.Group α)) (offset : Nat) :
    GroupsFit entries offset (gs.map (Group.map f)) ↔ GroupsFit entries offset gs := by
  induction gs generalizing offset with
  | nil => rfl
  | cons group rest ih => simp only [List.map_cons, GroupsFit, group_map_length, ih]

theorem groupsFit_append {α : Type} (entries offset : Nat) (gs hs : List (PublicApi.Group α))
    (hgs : GroupsFit entries offset gs)
    (hhs : GroupsFit entries (offset + (gs.map fun group => group.lanes.length).sum) hs) :
    GroupsFit entries offset (gs ++ hs) := by
  induction gs generalizing offset with
  | nil => simpa using hhs
  | cons group rest ih =>
    obtain ⟨hpos, hfit, hrest⟩ := hgs
    refine ⟨hpos, hfit, ih _ hrest ?_⟩
    simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using hhs

theorem causal_append (offset : Nat) (fs gs : List Frame)
    (hf : Causal offset fs)
    (hg : Causal (offset + (fs.map fun frame => frame.kind.width).sum) gs) :
    Causal offset (fs ++ gs) := by
  induction fs generalizing offset with
  | nil => simpa using hg
  | cons frame rest ih =>
    obtain ⟨hstart, hpos, hrest⟩ := hf
    refine ⟨hstart, hpos, ih _ hrest ?_⟩
    simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using hg

theorem indexed_widths (width entries start : Nat) (found : Bool)
    (descriptors : List Descriptor) :
    ((indexedGroups width entries start found descriptors).map fun group => group.lanes.length).sum =
      descriptors.length := by
  have h := congrArg List.length (ApiLoweringProof.flatten_aux width entries start
    (fun indexed : Descriptor × Nat => probes found indexed.1)
    descriptors.length descriptors.zipIdx (by simp))
  simpa only [indexedGroups, partition, List.length_zipIdx, List.length_flatMap] using h

theorem causal_frames (entries index start offset : Nat) (found : Bool)
    (groups : List (PublicApi.Group (Descriptor × Nat))) (hle : start ≤ offset)
    (hfit : GroupsFit entries offset groups) :
    Causal offset (groups.map fun group => (⟨index, start, found, group⟩ : Frame)) := by
  induction groups generalizing offset with
  | nil => trivial
  | cons group rest ih =>
    obtain ⟨hpos, hwidth, hrest⟩ := hfit
    refine ⟨hle, ?_, ?_⟩
    · simpa only [frame_width] using hpos
    · apply ih
      · simp only [frame_width]; omega
      · simpa only [frame_width] using hrest

/-- Frames preserve the chosen batch's original lane indices and start. -/
theorem requestGroups_batch {m : Nat} (choose : ApiAdaptive.Chooser m) (rows : List (Fin m → Nat))
    (width entries index start : Nat) (batch : Batch) :
    requestGroups choose rows
      ((indexedGroups width entries start batch.found batch.descriptors).map
        fun group => ⟨index, start, batch.found, group⟩) =
      (groups width entries start batch.found
        (chosenLanes (choose index) (rows.take start) batch.descriptors)).map
          (Group.map (request batch.found)) := by
  rw [ApiGroupedProof.groups_chosen]
  simp only [requestGroups, List.map_map]
  apply List.map_congr_left
  intro group _
  cases group <;> simp [requests, Group.map, List.map_map]

/-- The lowering's validity and cut bound hold for every observation branch. -/
theorem requestGroups_batch_valid {m : Nat} (choose : ApiAdaptive.Chooser m) (rows : List (Fin m → Nat))
    (width entries index start : Nat) (batch : Batch) :
    let fs := (indexedGroups width entries start batch.found batch.descriptors).map
      fun group => (⟨index, start, batch.found, group⟩ : Frame)
    (∀ group ∈ requestGroups choose rows fs, ApiExecution.Valid group) ∧
      GroupsFit entries start (requestGroups choose rows fs) := by
  dsimp only
  rw [requestGroups_batch]
  have hl := ApiLoweringStructure width entries start batch.found
    (chosenLanes (choose index) (rows.take start) batch.descriptors)
  refine ⟨?_, (groupsFit_map _ _ _ _).mpr hl.2.2.2⟩
  intro group hgroup
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hgroup
  have hv := hl.2.1 source hsource
  cases source with
  | blind lane => exact hv
  | chunk lanes =>
    intro q hq
    obtain ⟨lane, hlane, rfl⟩ := List.mem_map.mp hq
    exact hv.2.2 lane hlane

@[simp] theorem requestGroups_widths {m : Nat} (choose : ApiAdaptive.Chooser m)
    (rows : List (Fin m → Nat)) (fs : List Frame) :
    ((requestGroups choose rows fs).map fun group => group.lanes.length) =
      fs.map fun frame => frame.kind.width := by
  simp only [requestGroups, List.map_map, Function.comp_def, requests_width]

/-- Generalized start/index invariant, including empty external batches. -/
theorem framesFrom_properties (width entries : Nat) (batches : List Batch)
    (index start : Nat) :
    Causal start (framesFrom width entries index start batches) ∧
    ((framesFrom width entries index start batches).map fun frame => frame.kind.width).sum =
      (batches.map fun batch => batch.descriptors.length).sum ∧
    ∀ m (choose : ApiAdaptive.Chooser m) rows,
      (∀ group ∈ requestGroups choose rows (framesFrom width entries index start batches),
        ApiExecution.Valid group) ∧
      GroupsFit entries start (requestGroups choose rows
        (framesFrom width entries index start batches)) := by
  induction batches generalizing index start with
  | nil => simp [framesFrom, Causal, requestGroups, GroupsFit]
  | cons batch batches ih =>
    have hrest := ih (index + 1) (start + batch.descriptors.length)
    let fs : List Frame := (indexedGroups width entries start batch.found batch.descriptors).map
      fun group => ⟨index, start, batch.found, group⟩
    have hwidth : (fs.map fun frame => frame.kind.width).sum = batch.descriptors.length := by
      simpa only [fs, List.map_map, Function.comp_def, frame_width] using
        indexed_widths width entries start batch.found batch.descriptors
    have hcausal : Causal start fs := causal_frames entries index start start batch.found _
      (Nat.le_refl _) (ApiLoweringProof.fits_aux width entries start _ _ _)
    refine ⟨?_, ?_, ?_⟩
    · exact causal_append start fs _ hcausal (hwidth ▸ hrest.1)
    · simp only [framesFrom, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      change (fs.map fun frame => frame.kind.width).sum + _ = _
      rw [hwidth, hrest.2.1]
    · intro m choose rows
      have hbatch := requestGroups_batch_valid choose rows width entries index start batch
      have hr := hrest.2.2 m choose rows
      change (∀ group ∈ requestGroups choose rows (fs ++ framesFrom width entries
        (index + 1) (start + batch.descriptors.length) batches), _) ∧
        GroupsFit entries start (requestGroups choose rows (fs ++ framesFrom width entries
          (index + 1) (start + batch.descriptors.length) batches))
      simp only [requestGroups, List.map_append]
      refine ⟨?_, ?_⟩
      · intro group hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hbatch.1 group hg
        · exact hr.1 group hg
      · apply groupsFit_append _ _ _ _ hbatch.2
        change GroupsFit entries
          (start + ((requestGroups choose rows fs).map fun group => group.lanes.length).sum)
          (requestGroups choose rows
            (framesFrom width entries (index + 1) (start + batch.descriptors.length) batches))
        rw [requestGroups_widths, hwidth]
        exact hr.2

end RebuildBound.ApiAdaptiveProof

namespace RebuildBound
open Spec Model Model.ApiAdaptive ApiAdaptiveProof

theorem ApiAdaptiveFrames : ApiAdaptiveFrames_statement := by
  intro width entries batches
  obtain ⟨hc, hw, hv⟩ := framesFrom_properties width entries batches 0 0
  exact ⟨hc, by simpa only [frames, shape, Adaptive.slotCount, Adaptive.shapeWidths,
    List.map_map, Function.comp_def] using hw, hv⟩

end RebuildBound
