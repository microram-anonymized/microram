import RebuildBound.Spec.NativeRouting.Lanes

namespace RebuildBound
open Spec Spec.NativeRouting Spec.NativeRouting.Lanes

theorem NativeRoutingSharedLanes : NativeRoutingSharedLanes_statement := by
  intro f identity lo hi i
  match i with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩
  | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ =>
    simp only [sharedTags, permute, applyBlocks, register, block,
      interleaveLow, interleaveHigh, gather]
    rfl

theorem NativeRoutingInterleavedLanes : NativeRoutingInterleavedLanes_statement := by
  intro f a b i
  match i with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ =>
    simp only [interleaved, messageHalf, messageWords, permute, applyBlocks,
      register, block, firstBlocks, secondBlocks, gather, gather4]
    exact ⟨rfl, rfl, rfl, rfl⟩

end RebuildBound
