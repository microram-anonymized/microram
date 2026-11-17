import RebuildBound.Spec.Model.ApiAdaptive
import RebuildBound.Spec.ApiExecution

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.ApiAdaptive

/-- Generated internal frames are nonempty and causal; their widths cover
exactly the external lanes. No key, payload or observation fixes the shape. -/
def ApiAdaptiveFrames_statement : Prop :=
  ∀ width entries batches,
    Causal 0 (frames width entries batches) ∧
    Adaptive.slotCount (shape (frames width entries batches)) =
      (batches.map fun batch => batch.descriptors.length).sum ∧
    ∀ m (choose : Chooser m) rows,
      (∀ group ∈ requestGroups choose rows (frames width entries batches),
        ApiExecution.Valid group) ∧
      PublicApi.GroupsFit entries 0 (requestGroups choose rows (frames width entries batches))

/-- A replay of the supplied-record client is exactly the physical execution
of API requests reconstructed from each public batch's own observation prefix.
This is structural: no key universe, schedule, or capacity-success premise. -/
def ApiAdaptiveReplay_statement : Prop :=
  ∀ (c : Api.Codec) cfg sh g S init m (fs : List Frame) (choose : Chooser m),
    Causal 0 fs →
    ∀ t : Fin (Adaptive.slotCount (shape fs)) → Fin m → Nat,
      Adaptive.replay (run c cfg sh g S init fs choose) t =
        ApiExecution.run c cfg sh g S init
          (requestGroups choose (Adaptive.rowsOf t (Adaptive.slotCount (shape fs))) fs)

/-- Actual interaction instantiates the same request reconstruction at its
actual transcript. Generated frames additionally share one start for every
public batch; arbitrary causal frames need not encode that grouping. -/
def ApiAdaptiveInteraction_statement : Prop :=
  ∀ (c : Api.Codec) cfg sh g S init m (fs : List Frame) (choose : Chooser m),
    Causal 0 fs → ∀ words dummy,
    let a := run c cfg sh g S init fs choose
    let n := Adaptive.slotCount (shape fs)
    let t := Adaptive.transcript cfg sh g S a n words dummy
    Adaptive.realized cfg sh g S a words dummy =
      ApiExecution.run c cfg sh g S init (requestGroups choose (Adaptive.rowsOf t n) fs)

end RebuildBound.Spec
