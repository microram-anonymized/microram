import RebuildBound.Spec.ApiAdaptiveCorrectness
import RebuildBound.Proofs.ApiAdaptive
import RebuildBound.Proofs.ApiExecution

namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online Model.ApiAdaptive

namespace ApiAdaptiveCorrectnessProof

theorem requests_length {m : Nat} (choose : Chooser m) rows (fs : List Frame) :
    ((requestGroups choose rows fs).flatMap PublicApi.Group.lanes).length =
      Adaptive.slotCount (shape fs) := by
  unfold requestGroups shape Adaptive.slotCount Adaptive.shapeWidths
  rw [List.length_flatMap, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro frame _
  cases h : frame.group <;>
    simp [requests, PublicApi.Group.map, PublicApi.Group.lanes, Frame.kind, h,
      Adaptive.Kind.width]

end ApiAdaptiveCorrectnessProof

theorem ApiAdaptiveCorrectness : ApiAdaptiveCorrectness_statement := by
  intro geo hgeo U c g S init m width batches choose
  dsimp only
  intro hInit hU hcard hg hE hhor hnodup hinit hkeys hS
  let fs := frames width g.unitEntries batches
  let n := Adaptive.slotCount (shape fs)
  have hf := ApiAdaptiveFrames width g.unitEntries batches
  have hall (t : Fin n → Fin m → Nat) :=
    ApiExecutionCorrectness geo hgeo U c g S init
      (requestGroups choose (Adaptive.rowsOf t n) fs) m hInit hU hcard hg hE
      (by simpa only [ApiAdaptiveCorrectnessProof.requests_length] using hhor)
      hnodup hinit (hkeys t) (hf.2.2 m choose (Adaptive.rowsOf t n)).1
      (by simpa only [ApiAdaptiveCorrectnessProof.requests_length] using hS)
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · intro t
    rw [ApiAdaptiveReplay c geo.cfg geo.shapes g S init m fs choose hf.1 t]
    simpa only [ApiAdaptiveCorrectnessProof.requests_length] using (hall t).1
  · intro words dummy
    rw [ApiAdaptiveInteraction c geo.cfg geo.shapes g S init m fs choose hf.1 words dummy]
    exact (hall _).2 words dummy

end RebuildBound
