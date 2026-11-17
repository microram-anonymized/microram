import RebuildBound.Spec.Model.Key

/-! Native routing-message encoding. The bounded fields expose the premises
under which the native masks lose no information. Blocks are pairs of low/high
words; AES, byte transposition and execution correspondence remain separate. -/
namespace RebuildBound.Spec.NativeRouting

abbrev Word := Model.Word64
abbrev Counter := Fin (2^48)
abbrev Level := Fin (2^15)
abbrev Block := Word × Word

/-- Arithmetic form of the native 1/48/15-bit identity. -/
def packed (dummy : Bool) (counter : Counter) (level : Level) : Word :=
  ⟨(if dummy then 2^63 else 0) + counter.val * 2^15 + level.val,
    by cases dummy <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩

/-- The actual masked/shifted unsigned-word operation in PackAesCtrHighWord. -/
def rawPacked (nonceLo nonceHi : BitVec 64) : BitVec 64 :=
  (nonceLo &&& 0x8000000000000000) |||
    ((nonceHi &&& 0x0000ffffffffffff) <<< (15 : Nat)) |||
    (nonceLo &&& 0x0000000000007fff)

/-- The low nonce word built by PackFamilyNonce for a bounded level. -/
def nonceLow (dummy : Bool) (level : Level) : BitVec 64 :=
  BitVec.ofNat 64 ((if dummy then 2^63 else 0) + level.val)

/-- ASCII `oram-rt1` in little-endian order in the high word of block zero. -/
def label : Word := ⟨0x3174722d6d61726f, by decide⟩

/-- Two complete CBC blocks: labeled identity, then the complete stored key.
Keys of at most eight bytes and dummy counters use a zero high key word;
verbatim keys of nine to fifteen bytes are zero above their width. -/
def message (dummy : Bool) (counter : Counter) (level : Level)
    (keyLow keyHigh : Word) : Block × Block :=
  ((packed dummy counter level, label), (keyLow, keyHigh))

end RebuildBound.Spec.NativeRouting

namespace RebuildBound.Spec
open NativeRouting

/-- Bounded native packing agrees with arithmetic packing and is injective.
The raw operation alone is not injective on unrestricted nonce words. -/
def NativeRoutingPacking_statement : Prop :=
  (∀ (d : Bool) (c : Counter) (l : Level),
    (rawPacked (nonceLow d l) (BitVec.ofNat 64 c.val)).toNat = (packed d c l).val) ∧
  (∀ (d e : Bool) (c c' : Counter) (l l' : Level),
    packed d c l = packed e c' l' ↔ d = e ∧ c = c' ∧ l = l')

/-- Routing messages preserve the domain, family and both stored key words.
This says nothing about injectivity or pseudorandomness of CBC outputs. -/
def NativeRoutingMessage_statement : Prop :=
  ∀ (d e : Bool) (c c' : Counter) (l l' : Level) (lo hi lo' hi' : Word),
    message d c l lo hi = message e c' l' lo' hi' ↔
      d = e ∧ c = c' ∧ l = l' ∧ lo = lo' ∧ hi = hi'

end RebuildBound.Spec
