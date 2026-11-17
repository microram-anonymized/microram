import RebuildBound.Proofs.KeyRelabel.Jobs.SepFinish
import RebuildBound.Proofs.KeyRelabel.DirectDrain
import RebuildBound.Proofs.KeyRelabel.DirectPrepared

namespace RebuildBound.KeyRelabel
open Model Model.DirectJob

 theorem finishInitial_relabel (e : LogicalKey ≃ LogicalKey) (b : Table) (main : List Bucket) (leaves : List (List Rec)) :
    finishInitial (table e b) (buckets e main) (leaves.map (records e)) =
      sFin e (finishInitial b main leaves) := rfl
 theorem finishTransition_relabel (e : LogicalKey ≃ LogicalKey) (g : Geometry) (w : LogicalKey → Nat) (b : Table)
    (n : Nat) (st : SFin) (source : Nat) :
    finishTransition g (word e w) (table e b) n (sFin e st) source =
      (sFin e (finishTransition g w b n st source).1, (finishTransition g w b n st source).2) := by
  simp only [finishTransition, bLanes_table, sInsertBucket_relabel]
  simp [sFin]
 theorem insertBounded_relabel (e : LogicalKey ≃ LogicalKey) (g : Geometry) (w : LogicalKey → Nat) (b : Table)
    (main : List Bucket) (leaves : List (List Rec)) :
    insertBounded g (word e w) (table e b) (buckets e main) (leaves.map (records e)) =
      (insertBounded g w b main leaves).map (sFin e) := by
  simp only [insertBounded, finishInitial_relabel]
  exact stepsBounded_transport (sFin e) _ _ (finishTransition_relabel e g w b) _ _ _
 theorem finishChunks_relabel (e : LogicalKey ≃ LogicalKey) (st : SFin) :
    finishChunks (sFin e st) = (finishChunks st).map (List.map (tagged e)) := by
  simp [finishChunks, sFin, records, tagged, List.map_map, Function.comp_def]
 theorem finishDrainBounded_relabel (e : LogicalKey ≃ LogicalKey) (g : Geometry) (st : SFin) :
    finishDrainBounded g (sFin e st) = (finishDrainBounded g st).map (bucket e) := by
  simp only [finishDrainBounded, finishChunks_relabel]
  have hdmap := drainBounded_map (tagged e) Phase.drain Site.outputTier g.outputCapacity 0 [] (finishChunks st)
  simp only [List.map_nil] at hdmap
  rw [hdmap]
  cases hd : drainBounded Phase.drain Site.outputTier g.outputCapacity 0 [] (finishChunks st) with
  | error ev => rfl
  | ok first =>
    simp only [Except.map, List.length_map]
    have hm : (first.map (tagged e)).map some = taggedTier e (first.map some) := by
      simp [taggedTier, List.map_map, Function.comp_def]
    rw [hm]
    change (let last := finishDrainTransition g (finishChunks st).length (records e st.ins) (taggedTier e (first.map some));
      if last.2.passed then Except.ok last.1 else Except.error last.2) = _
    rw [finishDrainTransition_relabel]
    by_cases hp : (finishDrainTransition g (finishChunks st).length st.ins (first.map some)).2.passed = true
    · simp [hp]
    · simp [hp]
 theorem finishBounded_relabel (e : LogicalKey ≃ LogicalKey) (g : Geometry) (w : LogicalKey → Nat) (b : Table)
    (main : List Bucket) (leaves : List (List Rec)) :
    finishBounded g (word e w) (table e b) (buckets e main) (leaves.map (records e)) =
      (finishBounded g w b main leaves).map (output e) := by
  simp only [finishBounded, insertBounded_relabel]
  cases hi : insertBounded g w b main leaves with
  | error ev => rfl
  | ok st =>
    simp only [Except.map, finishDrainBounded_relabel]
    cases hd : finishDrainBounded g st with
    | error ev => rfl
    | ok tier =>
      change Except.ok (finishOutput g (buckets e st.main) (bucket e tier)) = _
      rw [finishOutput_map]

end RebuildBound.KeyRelabel
