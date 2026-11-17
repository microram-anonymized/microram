import RebuildBound.Spec.NativeRouting

/-! Qword permutations in AesBatch32Regs and AesTagsInterleaved. One register
has four independent 128-bit lanes. The block operation is arbitrary: this
checks assembly and output order, without modeling AES rounds or execution. -/
namespace RebuildBound.Spec.NativeRouting.Lanes

abbrev Register := Fin 8 → Word
abbrev Selectors := Fin 8 → Fin 16

/-- Two-source qword selection, with selectors in increasing lane order.
The native _mm512_set_epi64 argument lists are written in reverse order. -/
def permute (a b : Register) (s : Selectors) : Register := fun i =>
  if h : (s i).val < 8 then a ⟨(s i).val, h⟩
  else b ⟨(s i).val - 8, by have := (s i).isLt; omega⟩

def interleaveLow : Selectors := fun i =>
  match i.val with
  | 0 => ⟨0, by decide⟩ | 1 => ⟨8, by decide⟩ | 2 => ⟨1, by decide⟩ | 3 => ⟨9, by decide⟩
  | 4 => ⟨2, by decide⟩ | 5 => ⟨10, by decide⟩ | 6 => ⟨3, by decide⟩ | _ => ⟨11, by decide⟩

def interleaveHigh : Selectors := fun i =>
  match i.val with
  | 0 => ⟨4, by decide⟩ | 1 => ⟨12, by decide⟩ | 2 => ⟨5, by decide⟩ | 3 => ⟨13, by decide⟩
  | 4 => ⟨6, by decide⟩ | 5 => ⟨14, by decide⟩ | 6 => ⟨7, by decide⟩ | _ => ⟨15, by decide⟩

def firstBlocks : Selectors := fun i =>
  match i.val with
  | 0 => ⟨0, by decide⟩ | 1 => ⟨1, by decide⟩ | 2 => ⟨4, by decide⟩ | 3 => ⟨5, by decide⟩
  | 4 => ⟨8, by decide⟩ | 5 => ⟨9, by decide⟩ | 6 => ⟨12, by decide⟩ | _ => ⟨13, by decide⟩

def secondBlocks : Selectors := fun i =>
  match i.val with
  | 0 => ⟨2, by decide⟩ | 1 => ⟨3, by decide⟩ | 2 => ⟨6, by decide⟩ | 3 => ⟨7, by decide⟩
  | 4 => ⟨10, by decide⟩ | 5 => ⟨11, by decide⟩ | 6 => ⟨14, by decide⟩ | _ => ⟨15, by decide⟩

def gather : Selectors := fun i =>
  match i.val with
  | 0 => ⟨0, by decide⟩ | 1 => ⟨2, by decide⟩ | 2 => ⟨4, by decide⟩ | 3 => ⟨6, by decide⟩
  | 4 => ⟨8, by decide⟩ | 5 => ⟨10, by decide⟩ | 6 => ⟨12, by decide⟩ | _ => ⟨14, by decide⟩

/-- Only the low four qwords of the native tail gather are stored. -/
def gather4 : Selectors := fun i =>
  match i.val with
  | 0 => ⟨0, by decide⟩ | 1 => ⟨2, by decide⟩ | 2 => ⟨4, by decide⟩ | 3 => ⟨6, by decide⟩ | _ => ⟨0, by decide⟩

def block (v : Register) (i : Fin 4) : Block :=
  (v ⟨2 * i.val, by omega⟩, v ⟨2 * i.val + 1, by omega⟩)

def register (blocks : Fin 4 → Block) : Register := fun i =>
  if i.val % 2 = 0 then (blocks ⟨i.val / 2, by omega⟩).1
  else (blocks ⟨i.val / 2, by omega⟩).2

/-- Apply the same two-block operation independently in each AES lane. -/
def applyBlocks (f : Block → Block → Block) (a b : Register) : Register :=
  register fun i => f (block a i) (block b i)

/-- One eight-key group of AesBatch32Regs. Four such groups form a half bucket;
the 64-key wrapper repeats the half-bucket operation. A key of at most eight
bytes uses hi = 0. -/
def sharedTags (f : Block → Block → Block) (identity : Word)
    (lo hi : Register) : Register :=
  let first := register fun _ => (identity, label)
  permute (applyBlocks f first (permute lo hi interleaveLow))
    (applyBlocks f first (permute lo hi interleaveHigh)) gather

/-- Four consecutive messages in memory: [identity, label, keyLow, keyHigh].
Accepting arbitrary block pairs also covers arbitrary padding messages. -/
def messageWords (messages : Fin 4 → Block × Block) (i : Fin 16) : Word :=
  let m := messages ⟨i.val / 4, by omega⟩
  match i.val % 4 with
  | 0 => m.1.1 | 1 => m.1.2 | 2 => m.2.1 | _ => m.2.2

def messageHalf (messages : Fin 4 → Block × Block) (upper : Bool) : Register :=
  fun i => messageWords messages ⟨i.val + (if upper then 8 else 0),
    by cases upper <;> simp <;> omega⟩

/-- One four-message group of AesTagsInterleaved, before gathering low words. -/
def interleaved (f : Block → Block → Block)
    (messages : Fin 4 → Block × Block) : Register :=
  let a := messageHalf messages false
  let b := messageHalf messages true
  applyBlocks f (permute a b firstBlocks) (permute a b secondBlocks)

end RebuildBound.Spec.NativeRouting.Lanes

namespace RebuildBound.Spec
open NativeRouting NativeRouting.Lanes

/-- Shared-identity input interleaving and output gathering preserve each key
and return the low word of its own block result. No property of f is assumed. -/
def NativeRoutingSharedLanes_statement : Prop :=
  ∀ (f : Block → Block → Block) (identity : Word) (lo hi : Register) (i : Fin 8),
    sharedTags f identity lo hi i = (f (identity, label) (lo i, hi i)).1

/-- Variable-identity message loads preserve both blocks and their order.
Both the eight-tag gather and the four-tag tail return each result's low word;
the tail statement covers only the four qwords actually stored. -/
def NativeRoutingInterleavedLanes_statement : Prop :=
  ∀ (f : Block → Block → Block) (a b : Fin 4 → Block × Block) (i : Fin 4),
    block (interleaved f a) i = f (a i).1 (a i).2 ∧
    permute (interleaved f a) (interleaved f b) gather ⟨i.val, by omega⟩ =
      (f (a i).1 (a i).2).1 ∧
    permute (interleaved f a) (interleaved f b) gather ⟨i.val + 4, by omega⟩ =
      (f (b i).1 (b i).2).1 ∧
    permute (interleaved f a) (interleaved f a) gather4 ⟨i.val, by omega⟩ =
      (f (a i).1 (a i).2).1

end RebuildBound.Spec
