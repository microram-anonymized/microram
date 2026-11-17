import RebuildBound.Proofs.ApiExecution.Construction
import RebuildBound.Proofs.HierarchyApi
import RebuildBound.Proofs.ApiLowering

/-! The physical constructor first establishes its local equations at zero
tapes by causality. Flags follow before applying any lookup theorem. Under the
existing explicit universe premises, flag soundness then derives the setting
that permits transfer to actual tapes and the independent logical API map. -/
namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online Model.PublicApi

theorem ApiExecutionFlags : ApiExecutionFlags_statement := by
  intro c cfg sh g S init groups m hg hE hv hS
  exact ApiFlagRule c cfg sh g (ApiExecution.run c cfg sh g S init groups) S
    (fun _ _ _ => 0) (fun _ _ => 0) (groups.flatMap Group.lanes) (fun _ => rfl)
    (ApiExecutionImplements c cfg sh g S init groups m hg hE hv hS)

theorem ApiExecutionTransfer : ApiExecutionTransfer_statement := by
  intro geo hgeo U c g S init groups m
  dsimp only
  intro hv hs words dummy
  have hi := ApiExecutionImplements c geo.cfg geo.shapes g S init groups m
    hs.2.2.2.1.geom.1 hs.2.2.2.1.geom.2 hv hs.2.2.2.2
  refine ⟨hi.length, ?_⟩
  intro t q s hq hslot
  obtain ⟨hk, hp, hr⟩ := hi.slot t q s hq hslot
  refine ⟨hk, hp, ?_⟩
  rw [HierarchyBatchFound geo hgeo U g _ S _ m hs words (fun _ _ _ => 0)
    dummy (fun _ _ => 0) t (List.getElem?_eq_some_iff.mp hq).1]
  exact hr

theorem ApiExecutionLowered : ApiExecutionLowered_statement := by
  intro c cfg sh g S init width found lanes m hg hE hS
  dsimp only
  let lowered := groups width g.unitEntries 0 found lanes
  let requests := lowered.map (Group.map (request found))
  have hl := ApiLoweringStructure width g.unitEntries 0 found lanes
  have hlanes : requests.flatMap Group.lanes = lanes.map (request found) := by
    change (lowered.map (Group.map (request found))).flatMap Group.lanes = _
    rw [List.flatMap_map]
    have hm : ∀ group : PublicApi.Group Lane,
        (group.map (request found)).lanes = group.lanes.map (request found) := by
      intro group
      cases group <;> rfl
    simp only [hm, ← List.map_flatMap]
    rw [hl.1]
  have hv : ∀ group ∈ requests, ApiExecution.Valid group := by
    intro group hgroup
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hgroup
    have hs := hl.2.1 source hsource
    cases source with
    | blind lane => exact hs
    | chunk ls =>
      intro q hq
      obtain ⟨lane, hmem, rfl⟩ := List.mem_map.mp hq
      exact hs.2.2 lane hmem
  have hn : (requests.flatMap Group.lanes).length = lanes.length := by
    rw [hlanes, List.length_map]
  have hi := ApiExecutionImplements c cfg sh g S init requests m hg hE hv (hn ▸ hS)
  refine ⟨hl.2.2.2, ?_, ?_⟩
  · rw [(ApiExecutionShape c cfg sh g S init requests hv).1, ← hl.2.2.1]
    change (lowered.map (Group.map (request found))).map (fun group => group.lanes.length) = _
    simp only [List.map_map]
    apply List.map_congr_left
    intro group _
    cases group <;> simp [Group.map, Group.lanes, Group.shape]
  · simpa only [hlanes] using hi

theorem ApiExecutionCorrectness : ApiExecutionCorrectness_statement := by
  intro geo hgeo U c g S init groups m hInit hU hcard hg hE hhor hnodup hinit hkeys hv hS
  dsimp only
  let run := ApiExecution.run c geo.cfg geo.shapes g S init groups
  have hi := ApiExecutionImplements c geo.cfg geo.shapes g S init groups m hg hE hv hS
  have hs : UniverseBatchSetting geo U g run S (OnlineBatch.slots run).length m :=
    HierarchyApiAdmissible geo hgeo U g run S m c (fun _ _ _ => 0) (fun _ _ => 0)
      (groups.flatMap Group.lanes) hInit hU hcard hg hE (hi.length ▸ hhor)
      hnodup hinit hkeys (hi.length ▸ hS) (fun _ => rfl) hi
  have hs' : UniverseBatchSetting geo U g run S (groups.flatMap Group.lanes).length m :=
    hi.length.symm ▸ hs
  refine ⟨hs', fun words dummy => ?_⟩
  have ht := ApiExecutionTransfer geo hgeo U c g S init groups m hv hs' words dummy
  exact ⟨ht, HierarchyBatchApiCorrectness geo hgeo U g run S m hs hInit c words dummy
    (groups.flatMap Group.lanes) ht⟩

end RebuildBound
