import RebuildBound.Spec.NativeMatch.Ring
import RebuildBound.Proofs.BatchFresh.Requester
import RebuildBound.Proofs.AdaptiveReplay
import RebuildBound.Proofs.AdaptiveCausal.Fold

namespace RebuildBound.NativeMatchRingProof
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive
open Spec Spec.NativeMatchPhysical Spec.NativeMatchProduction

lemma frozen_length (g : OnlineGeom) (hE : 0 < g.unitEntries) (run : BatchRun)
    {t : Nat} {slot : OnlineBatch.Slot} (hs : (slots run)[t]? = some slot) :
    (stateAt g run slot.op).frozen.length = chunkStart (widths run) t / g.unitEntries := by
  obtain ⟨op, hop, _, _⟩ := BatchFreshProof.slot_inv run hs
  have hbound := (List.getElem?_eq_some_iff.mp hop).1
  have hI := BatchFreshProof.inv_stateAt g run hE slot.op (Nat.le_of_lt hbound)
  rw [BatchFreshProof.chunkStart_slot run hs, ← hI.len,
    Nat.mul_comm _ g.unitEntries, Nat.mul_add_div hE,
    Nat.div_eq_of_lt hI.cur, Nat.add_zero]

lemma ready_shape {slots : Nat} (g : OnlineGeom) (hE : 0 < g.unitEntries)
    (run : BatchRun) (snapshots : Nat → Snapshot slots) (shape : List Kind) (n : Nat)
    (hw : widths run = shapeWidths shape) (hp : probePattern run = shapePattern shape) :
    ready g run snapshots n = publicReady g snapshots shape n := by
  unfold ready publicReady
  congr 1
  funext t
  rw [← hp, ← hw]
  cases hs : (OnlineBatch.slots run)[t]? with
  | none => simp [OnlineBatch.probePattern, hs]
  | some slot =>
    simp only [OnlineBatch.probePattern, hs, Option.map_some, Option.getD_some]
    rw [frozen_length g hE run hs]
    rfl

end RebuildBound.NativeMatchRingProof

namespace RebuildBound
open Model Model.Hierarchy Model.Online Model.Adaptive Spec Spec.NativeMatchPhysical
open Spec.NativeMatchProduction

theorem NativeMatchRingPublic : NativeMatchRingPublic_statement := by
  intro slots cfg sh g hE S m client snapshots n words dummy
  apply NativeMatchRingProof.ready_shape g hE
  · exact AdaptiveCausalProof.realized_widths cfg sh g S client words dummy
  · rw [AdaptiveReplayProof.realized_eq_replay cfg sh g S client (slotCount client.shape)
      rfl words dummy]
    exact (ReplayShape m client _ _).2.1

theorem NativeMatchRingCost : NativeMatchRingCost_statement := by
  intro member initialized h ctx
  have hready (tape : IdealKey.Tape) :
      NativeMatchHierarchy.ringStopped ctx.geo.cfg ctx.geo.shapes ctx.unit
        ctx.snapshots ctx.client ctx.accesses tape ↔
        publicReady ctx.unit ctx.snapshots ctx.client.shape ctx.accesses = false := by
    unfold NativeMatchHierarchy.ringStopped
    rw [NativeMatchRingPublic ctx.geo.cfg ctx.geo.shapes ctx.unit (by exact Nat.zero_lt_succ 63)
      _ ctx.client ctx.snapshots ctx.accesses]
  unfold NativeMatchCoded.ringCost
  simp only [hready]
  cases publicReady ctx.unit ctx.snapshots ctx.client.shape ctx.accesses <;> simp

end RebuildBound
