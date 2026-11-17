import RebuildBound.Proofs.NativeRouting

/-! Routing encoding regressions. These distinguish complete messages, not
their compressed CBC outputs or projected tags. -/
namespace RebuildBound.NativeRoutingTests
open Spec Spec.NativeRouting

example (d : Bool) (c : Counter) (l : Level) :
    (rawPacked (nonceLow d l) (BitVec.ofNat 64 c.val)).toNat =
      (packed d c l).val := NativeRoutingPacking.1 d c l

/-- Maximal fields fill the word without wrapping. -/
example : (packed true ⟨2^48 - 1, by decide⟩ ⟨2^15 - 1, by decide⟩).val =
    2^64 - 1 := by decide

/-- Ordinary ordinals and the empty-top ordinal cannot alias, even across
levels and complete stored keys. -/
example (c : Counter) (hc : 0 < c.val) (l l' : Level)
    (lo hi lo' hi' : Word) :
    message false c l lo hi ≠ message false 0 l' lo' hi' := by
  intro h
  have heq := (NativeRoutingMessage false false c 0 l l' lo hi lo' hi').1 h
  have := congrArg Fin.val heq.2.1
  simp at this
  omega

/-- Positive one-based levels separate the empty top from dense sentinel zero. -/
example (l : Level) (hl : 0 < l.val) : (packed false 0 l).val ≠ 0 := by
  simp [packed]
  omega

/-- Real and dummy messages remain separate even when every other field is
allowed to differ. -/
example (c c' : Counter) (l l' : Level) (lo hi lo' hi' : Word) :
    message false c l lo hi ≠ message true c' l' lo' hi' := by
  intro h
  have := (NativeRoutingMessage false true c c' l l' lo hi lo' hi').1 h
  exact Bool.noConfusion this.1

/-- Both stored words matter, including zero-valued narrow/dummy high words. -/
example : message false 1 1 0 0 ≠ message false 1 1 1 0 := by decide
example : message false 1 1 0 0 ≠ message false 1 1 0 1 := by decide

/-- The former XOR encoding aliases a changed high word with a changed level;
the complete two-block message distinguishes the same legal input pair. -/
example : ((0 : BitVec 64), (0 : BitVec 64) ^^^ 0) =
    ((0 : BitVec 64), (1 : BitVec 64) ^^^ 1) := by decide
example : message false 0 0 0 0 ≠ message false 0 1 0 1 := by decide

/-- Native masks discard out-of-range counter and level bits. The bounded
field premises are necessary; raw packing is not injective on arbitrary words. -/
example : rawPacked 0 0 = rawPacked 0 (BitVec.ofNat 64 (2^48)) := by decide
example : rawPacked 0 0 = rawPacked (BitVec.ofNat 64 (2^15)) 0 := by decide
example : (0 : BitVec 64) ≠ BitVec.ofNat 64 (2^48) := by decide
example : (0 : BitVec 64) ≠ BitVec.ofNat 64 (2^15) := by decide

/-- The fixed high word spells the native label in little-endian byte order. -/
example : (List.range 8).map (fun i => (label.val / 256^i) % 256) =
    [111, 114, 97, 109, 45, 114, 116, 49] := by decide

end RebuildBound.NativeRoutingTests
