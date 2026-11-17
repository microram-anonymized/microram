import RebuildBound.Spec.Model.Key

/-! Byte-level stored-key encoding used by the native hierarchy: keys of one to
fifteen bytes are stored verbatim, a sixteen-byte key is one encrypted block and
longer keys are length-prefixed CBC messages. AES is an explicit permutation
premise; no cryptographic law or C++ refinement is assumed. The long-key result
concerns CBC input messages, not their compressed outputs. -/
namespace RebuildBound.Spec.NativeKey
open Model

abbrev Block := Fin 16 → Fin 256

/-- The native zero-filled block at byte offset `offset`. -/
def keyBlock (key : LogicalKey) (offset : Nat := 0) : Block :=
  fun i => key.getD (offset + i.val) 0

/-- Little-endian length in a 128-bit block. For the native 17–64 byte
domain this agrees with LE64(length) followed by eight zero bytes. -/
def lengthBlock (length : Nat) : Block :=
  fun i => ⟨(length / 256 ^ i.val) % 256, Nat.mod_lt _ (by decide)⟩

/-- Both stored words. Keys below sixteen bytes are stored verbatim and
zero-filled, so the high word is zero only through eight bytes; a sixteen-byte
key is one encrypted block. This describes only widths at most sixteen. -/
def shortStored (encrypt : Block → Block) (key : LogicalKey) : Block :=
  if key.length < 16 then keyBlock key else encrypt (keyBlock key)

/-- The long-key branch: one length block and ceil(length/16) zero-padded
data blocks. This encoding is not the short-key branch of AesHashKey128. -/
def longMessage (key : LogicalKey) : List Block :=
  lengthBlock key.length ::
    (List.range ((key.length + 15) / 16)).map (fun i => keyBlock key (16 * i))

end RebuildBound.Spec.NativeKey

namespace RebuildBound.Spec
open Model NativeKey

/-- Fixed-width native short keys have no normalization collisions when the
block encryption is injective; only width sixteen uses that premise. The
fixed-width premise is essential. -/
def NativeKeyShort_statement : Prop :=
  ∀ (encrypt : Block → Block), Function.Injective encrypt →
    ∀ (width : Nat), 1 ≤ width → width ≤ 16 →
      ∀ a b : LogicalKey, a.length = width → b.length = width →
        (shortStored encrypt a = shortStored encrypt b ↔ a = b)

/-- Verbatim widths are injective for every block operation. Through the key
API these are the only stored keys a caller chooses directly; segment matching
never applies to them. -/
def NativeKeyVerbatim_statement : Prop :=
  ∀ (encrypt : Block → Block) (width : Nat), width < 16 →
    ∀ a b : LogicalKey, a.length = width → b.length = width →
      (shortStored encrypt a = shortStored encrypt b ↔ a = b)

/-- Long-key message encoding preserves every byte and the length, even across
different native widths. Its block count is exact. This does not assert that
CBC compression is injective or justify a mixed-width cryptographic bound. -/
def NativeKeyLong_statement : Prop :=
  (∀ a b : LogicalKey, 16 < a.length → a.length ≤ 64 →
    16 < b.length → b.length ≤ 64 → (longMessage a = longMessage b ↔ a = b)) ∧
  (∀ key : LogicalKey, 16 < key.length → key.length ≤ 64 →
    (longMessage key).length = 1 + (key.length + 15) / 16 ∧
      3 ≤ (longMessage key).length ∧ (longMessage key).length ≤ 5)

end RebuildBound.Spec
