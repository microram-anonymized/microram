import RebuildBound.Proofs.NativeKey

/-! Non-vacuity and boundary witnesses for the native byte encoding. These
check the encoding, not the native AES implementation or a CBC security law. -/
namespace RebuildBound.NativeKeyTests
open Model Spec Spec.NativeKey

private instance : DecidableEq Block := fun a b =>
  decidable_of_iff (∀ i, a i = b i) ⟨funext, congrFun⟩

/-- A concrete nonidentity block permutation witnesses the encryption premise. -/
def reverseBlock (block : Block) : Block := fun i => block i.rev

theorem reverseBlock_injective : Function.Injective reverseBlock := by
  intro a b h
  funext i
  simpa [reverseBlock] using congrFun h i.rev

example (width : Nat) (hlo : 1 ≤ width) (hhi : width ≤ 16)
    (a b : LogicalKey) (ha : a.length = width) (hb : b.length = width) :
    shortStored reverseBlock a = shortStored reverseBlock b ↔ a = b :=
  NativeKeyShort reverseBlock reverseBlock_injective width hlo hhi a b ha hb

/-- Every position of every supported short width retains its byte, including
zero at either end; this is independent of the numeric fixture key codec. -/
example : ∀ width : Fin 17, ∀ i : Fin 16, i.val < width.val →
    keyBlock (List.replicate i.val 0 ++ [1] ++
      List.replicate (width.val - i.val - 1) 0) 0 i = 1 := by decide

/-- The native length block is LE64(length) followed by zeros. Every allowed
length fits in its first byte, with all fifteen remaining bytes zero. -/
example : ∀ width : Fin 65, ∀ i : Fin 16,
    lengthBlock width.val i = if i.val = 0 then ⟨width.val, by omega⟩ else 0 := by decide

example : (longMessage (List.replicate 17 0)).length = 3 ∧
    (longMessage (List.replicate 31 0)).length = 3 ∧
    (longMessage (List.replicate 32 0)).length = 3 ∧
    (longMessage (List.replicate 33 0)).length = 4 ∧
    (longMessage (List.replicate 48 0)).length = 4 ∧
    (longMessage (List.replicate 49 0)).length = 5 ∧
    (longMessage (List.replicate 64 0)).length = 5 := by decide

def tailKey (byte : Fin 256) : LogicalKey := List.replicate 16 0 ++ [byte]

/-- Truncating to sixteen bytes would alias these keys. The actual long-key
message keeps the seventeenth byte in its second data block. -/
example : keyBlock (tailKey 0) = keyBlock (tailKey 1) := by decide
example : longMessage (tailKey 0) ≠ longMessage (tailKey 1) := by decide
example : ((longMessage (tailKey 1))[2]'(by decide)) (0 : Fin 16) = 1 := by decide

/-- All-zero long keys with different lengths have the same padded data but
distinct length headers. This is an encoding property, not a mixed-width PRF law. -/
example : (longMessage (List.replicate 17 0)).tail =
    (longMessage (List.replicate 18 0)).tail := by decide
example : longMessage (List.replicate 17 0) ≠
    longMessage (List.replicate 18 0) := by decide

/-- Verbatim widths need no encryption premise, at every width below sixteen. -/
example (encrypt : Block → Block) (width : Nat) (hw : width < 16)
    (a b : LogicalKey) (ha : a.length = width) (hb : b.length = width) :
    shortStored encrypt a = shortStored encrypt b ↔ a = b :=
  NativeKeyVerbatim encrypt width hw a b ha hb

/-- The stored-width boundary of native `StoredKeyBytes`: fifteen bytes stay
verbatim for any block operation, sixteen bytes are encrypted. -/
example : shortStored (fun _ _ => 0) (List.replicate 15 1) =
    keyBlock (List.replicate 15 1) := by decide
example : shortStored (fun _ _ => 0) (List.replicate 16 1) = fun _ => 0 := by decide

/-- Native alias keys: byte 0 is 0x37 and byte 8 is 0x91. -/
def nineKey : LogicalKey := [0x37, 0, 0, 0, 0, 0, 0, 0, 0x91]
def fifteenKey : LogicalKey := nineKey ++ List.replicate 6 0
def sixteenKey : LogicalKey := nineKey ++ List.replicate 7 0

/-- Without a fixed width, zero filling aliases distinct verbatim keys, in
the low word and in the high word. -/
example : ([1] : LogicalKey) ≠ [1, 0] := by decide
example : shortStored reverseBlock [1] = shortStored reverseBlock [1, 0] := by decide
example : nineKey ≠ fifteenKey := by decide
example (encrypt : Block → Block) :
    shortStored encrypt nineKey = shortStored encrypt fifteenKey := by
  change keyBlock nineKey = keyBlock fifteenKey
  decide

/-- The generic helper's one-block branch zero-pads too, so it aliases nine and
sixteen bytes; stored keys reach it only at exactly sixteen bytes. -/
example (encrypt : Block → Block) :
    encrypt (keyBlock nineKey) = encrypt (keyBlock sixteenKey) := by
  congr 1
  decide

/-- Across the verbatim/encrypted boundary even an injective block operation can
alias; the fixed-width premise is what excludes this. -/
example : shortStored reverseBlock (List.replicate 15 0) =
    shortStored reverseBlock (List.replicate 16 0) := by decide

/-- Nine and sixteen zero bytes do not alias under every encryption. -/
example : ¬ ∀ encrypt : Block → Block,
    shortStored encrypt (List.replicate 9 0) = shortStored encrypt (List.replicate 16 0) := by
  intro h
  have := h (fun b i => b i + 1)
  revert this
  decide

/-- Sixteen-byte keys can collide if block encryption is not injective; verbatim
nine-byte keys cannot, even under a constant block operation. -/
example : shortStored (fun _ _ => 0) (List.replicate 16 0) =
    shortStored (fun _ _ => 0) (List.replicate 16 1) := by decide
example : (List.replicate 16 (0 : Fin 256)) ≠ List.replicate 16 1 := by decide
example : shortStored (fun _ _ => 0) (List.replicate 9 0) ≠
    shortStored (fun _ _ => 0) (List.replicate 9 1) := by decide

end RebuildBound.NativeKeyTests
