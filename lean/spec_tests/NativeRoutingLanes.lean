import RebuildBound.Proofs.NativeRouting

/-! Layout witnesses use arbitrary block operations, including operations that
expose word order directly. They assert no cryptographic property. -/
namespace RebuildBound.NativeRoutingLaneTests
open Spec Spec.NativeRouting Spec.NativeRouting.Lanes

/-- Narrow and dummy key blocks retain their zero high word in every lane. -/
example (f : Block → Block → Block) (identity : Word) (lo : Register) (i : Fin 8) :
    sharedTags f identity lo (fun _ => 0) i =
      (f (identity, label) (lo i, 0)).1 :=
  NativeRoutingSharedLanes f identity lo (fun _ => 0) i

/-- Direct composition with the existing complete routing-message encoding,
allowing different domains, identities and both key words in all four lanes. -/
example (f : Block → Block → Block) (d : Fin 4 → Bool) (c : Fin 4 → Counter)
    (l : Fin 4 → Level) (lo hi : Fin 4 → Word) (i : Fin 4) :
    block (interleaved f (fun j => message (d j) (c j) (l j) (lo j) (hi j))) i =
      f (packed (d i) (c i) (l i), label) (lo i, hi i) :=
  (NativeRoutingInterleavedLanes f
    (fun j => message (d j) (c j) (l j) (lo j) (hi j))
    (fun _ => ((0, 0), (0, 0))) i).1

/-- The two halves of an eight-tag gather may contain unrelated messages.
This also covers arbitrary padded messages; their contents need not be zero. -/
example (f : Block → Block → Block) (a padding : Fin 4 → Block × Block) (i : Fin 4) :
    permute (interleaved f a) (interleaved f padding) gather
        ⟨i.val + 4, by omega⟩ = (f (padding i).1 (padding i).2).1 :=
  (NativeRoutingInterleavedLanes f a padding i).2.2.1

private def laneWords : Register := fun i => ⟨i.val + 1, by omega⟩

/-- An operation exposing the high key word catches same-partner mistakes. -/
example (i : Fin 8) :
    sharedTags (fun _ key => (key.2, key.1)) 0 (fun _ => 0) laneWords i =
      laneWords i := NativeRoutingSharedLanes _ _ _ _ i

/-- Reusing selectors 8..11 for the high half combines the correct low words
of keys 4..7 with the high words of keys 0..3. -/
private def reusedHigh : Selectors := fun i =>
  if i.val % 2 = 0 then interleaveHigh i else interleaveLow i

example : block (permute laneWords laneWords reusedHigh) ⟨0, by decide⟩ =
    (5, 1) := by decide
example : block (permute laneWords laneWords reusedHigh) ⟨0, by decide⟩ ≠
    (laneWords ⟨4, by decide⟩, laneWords ⟨4, by decide⟩) := by decide

/-- Odd qwords are ciphertext high words, not the low-word tags. -/
private def oddGather : Selectors := fun i => ⟨2 * i.val + 1, by omega⟩

example : permute (register fun _ => (3, 9)) (register fun _ => (3, 9))
    oddGather ⟨0, by decide⟩ = 9 := by decide
example : permute (register fun _ => (3, 9)) (register fun _ => (3, 9))
    oddGather ⟨0, by decide⟩ ≠ 3 := by decide

/-- Tail gather's upper qwords are filler: the native store is only 256 bits.
Treating the result as eight valid tags would repeat the first result. -/
example : permute (register fun i => (⟨i.val + 1, by omega⟩, 0))
    (fun _ => 0) gather4 ⟨4, by decide⟩ = 1 := by decide

end RebuildBound.NativeRoutingLaneTests
