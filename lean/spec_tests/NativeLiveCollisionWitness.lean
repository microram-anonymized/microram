import RebuildBound.Proofs.ApiCapacity
import RebuildBound.Spec.NativeMatch.ExactPairs

namespace NativeLinearCounterexample
open RebuildBound RebuildBound.Model RebuildBound.Model.Api RebuildBound.Model.ApiCapacity
open RebuildBound.ApiCapacityProof

def keyA : LogicalKey := List.replicate 17 0
def keyB : LogicalKey := 1 :: List.replicate 16 0

theorem distinct : keyA ≠ keyB := by decide

def initialRecord : Rec := ⟨keyA, 7, false⟩
def miss : Request := ⟨keyB, .read⟩

theorem initial_valid : InitialStateValid 1 true [initialRecord] := by
  simp [InitialStateValid, initialRecord]

theorem miss_preserves_capacity (codec : Codec) :
    LiveCapacity 1 (stateOf codec [initialRecord]) [keyA] [miss] := by
  have hs : Supports (stateOf codec [initialRecord]) [keyA] := by
    simpa [initialRecord] using records_support codec [initialRecord]
      (by simp [initialRecord]) (by simp [initialRecord])
  refine ⟨hs, ?_⟩
  intro t ht
  have hstate : stateAt (stateOf codec [initialRecord]) [miss] t =
      stateOf codec [initialRecord] := by
    simpa [miss] using read_state (stateOf codec [initialRecord]) [keyB] t
  have hsupport := ApiFiniteSupport (stateOf codec [initialRecord]) [keyA] [miss] hs t
  rw [hstate] at hsupport
  have hlen := supports_length hsupport hs
  simp only [List.length_singleton] at hlen
  omega

/-- This miss has one distinct live collision partner, although N-1 = 0. -/
theorem nonzero_collision_inventory :
    Spec.NativeMatchExactPairs.listPairs [initialRecord] miss.key = [(keyA,keyB)] := rfl

theorem proposed_numerator_zero : Nat.choose 1 2 + 1 * (1 - 1) = 0 := by decide

/-- Colliding the miss with the initialized key changes the decoded reply.
The complete finite probability calculation is separate from this witness. -/
theorem stored_alias_changes_reply (codec : Codec) :
    value codec (some initialRecord) ≠ stateOf codec [initialRecord] keyB := by
  simp [value, initialRecord, stateOf, DirectPrefix.latest, DirectPrefix.winners,
    Probe.decode, keyA, keyB]

/-- Initial uniqueness is not preserved by a noninjective key map. -/
theorem mapped_init_not_nodup :
    ¬ (([keyA,keyB].map (fun _ => keyA)).Nodup) := by simp

end NativeLinearCounterexample
