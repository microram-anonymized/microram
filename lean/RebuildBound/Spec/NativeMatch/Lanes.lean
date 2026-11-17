import RebuildBound.Spec.NativeMatch
import RebuildBound.Spec.Model.DirectMask64

/-! Finite instruction semantics for the default width-16 production rebuild
helpers. Byte unpacks, second-operand intersection masks, PDEP/PEXT positions,
zero repair and class selection are explicit. This is not a proof of C++ memory
layout, compilation, instruction timing or machine execution. -/
namespace RebuildBound.Spec.NativeMatch.Lanes
open Model NativeNormalize

abbrev Slot := Fin 64
abbrev Byte := Fin 256
abbrev Stored := Fingerprint 128
abbrev Word := Fingerprint 64
abbrev Dword := Fingerprint 32
abbrev Keys := Slot → Stored
abbrev Mask := BitVec 64
abbrev ByteVector := Slot → Byte
abbrev DRegister := Fin 16 → Dword
abbrev DRegisters := Fin 4 → DRegister

/-- The two stored words are packed in little-endian order. -/
def packWords (lo hi : Word) : Stored :=
  ⟨lo.val + 2 ^ 64 * hi.val, by have := lo.isLt; have := hi.isLt; omega⟩

/-- Four bytes of a dword, in increasing byte position. -/
def bytes (w : Dword) : Fin 4 → Byte := segments 4 8 w

def field (keys : Keys) (f : Fin 4) (i : Slot) : Dword :=
  keySegment (count := 4) (width := 32) (keys i) f

/-- Byte-line load. Only the set side zeros dummy lanes. -/
def loadLine (zeroDummies : Bool) (keys : Keys) (real : Mask)
    (f b : Fin 4) : ByteVector := fun i =>
  if zeroDummies && !real.getLsbD i.val then 0 else bytes (field keys f i) b

/-- VPUNPCKLBW/HBW: interleave bytes within each 128-bit lane. -/
def unpack8 (high : Bool) (a b : ByteVector) : ByteVector := fun i =>
  let source : Slot := ⟨16 * (i.val / 16) + (if high then 8 else 0) +
    (i.val % 16) / 2, by have := i.isLt; cases high <;> simp_all <;> omega⟩
  if i.val % 2 = 0 then a source else b source

/-- VPUNPCKLWD/HWD: interleave two-byte words within each 128-bit lane. -/
def unpack16 (high : Bool) (a b : ByteVector) : ByteVector := fun i =>
  let source : Slot := ⟨16 * (i.val / 16) + (if high then 8 else 0) +
    2 * ((i.val % 16) / 4) + i.val % 2,
    by have := i.isLt; cases high <;> simp_all <;> omega⟩
  if i.val % 4 < 2 then a source else b source

/-- The exact two-stage UnpackKeyLinesToDwords network. -/
def unpackLines (lines : Fin 4 → ByteVector) (j : Fin 4) : ByteVector :=
  let b0 := unpack8 false (lines 0) (lines 1)
  let b1 := unpack8 true (lines 0) (lines 1)
  let b2 := unpack8 false (lines 2) (lines 3)
  let b3 := unpack8 true (lines 2) (lines 3)
  match j.val with
  | 0 => unpack16 false b0 b2
  | 1 => unpack16 true b0 b2
  | 2 => unpack16 false b1 b3
  | _ => unpack16 true b1 b3

/-- Interpret each four consecutive register bytes as a little-endian dword. -/
def unpackDwords (lines : Fin 4 → ByteVector) : DRegisters := fun j t =>
  (segments 4 8).symm fun b => unpackLines lines j
    ⟨4 * t.val + b.val, by have := t.isLt; have := b.isLt; omega⟩

/-- Slot represented by an unpacked register/dword coordinate. -/
def unpackSlot (j : Fin 4) (t : Fin 16) : Slot :=
  ⟨16 * (t.val / 4) + 4 * j.val + t.val % 4,
    by have := j.isLt; have := t.isLt; omega⟩

/-- Set-bit positions of the native PDEP/PEXT constant 0x000F000F000F000F. -/
def depositPosition (t : Fin 16) : Slot :=
  ⟨16 * (t.val / 4) + t.val % 4, by have := t.isLt; omega⟩

def maskOfBits (bits : Slot → Bool) : Mask :=
  (BitVec.ofBoolListLE ((List.finRange 64).map bits)).setWidth 64

/-- PDEP into the sixteen selected positions of the fixed mask. -/
def deposit (bits : Fin 16 → Bool) : Mask := maskOfBits fun i =>
  (List.finRange 16).any fun t => bits t && decide (depositPosition t = i)

/-- Native PlaceMatchesD<true>. -/
def placeMatches (bits : Fin 16 → Bool) (j : Fin 4) : Mask :=
  deposit bits <<< (4 * j.val)

/-- PEXT(mask >> 4*j, 0x000F000F000F000F), used by the class selection. -/
def extractClass (real : Mask) (j : Fin 4) : Fin 16 → Bool := fun t =>
  (real >>> (4 * j.val)).getLsbD (depositPosition t).val

/-- VP2INTERSECTD's second output. Partner identity is discarded here. -/
def intersectSecond (a b : DRegister) : Fin 16 → Bool := fun t =>
  (List.finRange 16).any fun u => a u == b t

/-- b-register-major OR accumulation, followed by the native mask placement. -/
def allPairs (a b : DRegisters) : Mask :=
  (List.finRange 4).foldl (fun result j =>
    let bits := (List.finRange 4).foldl
      (fun acc i t => acc t || intersectSecond (a i) (b j) t) (fun _ => false)
    result ||| placeMatches bits j) 0

/-- The loader's zero mask uses the original four bytes and real occupancy,
regardless of whether its returned dummy bytes were zeroed. -/
def zeroMask (keys : Keys) (real : Mask) (f : Fin 4) : Mask :=
  maskOfBits fun i => real.getLsbD i.val &&
    (List.finRange 4).all (fun b => bytes (field keys f i) b == 0)

structure LoadedField where
  regs : DRegisters
  zero : Mask

/-- Concrete loader followed by the unpack network. -/
def loadField (zeroDummies : Bool) (keys : Keys) (real : Mask)
    (f : Fin 4) : LoadedField :=
  ⟨unpackDwords (loadLine zeroDummies keys real f), zeroMask keys real f⟩

/-- RepairZeroKeyMatches: override subject-zero bits with real source-zero
existence, then intersect with subject occupancy. -/
def repair (raw sourceZero subjectZero subjectReal : Mask) : Mask :=
  let zeroHit : Mask := if sourceZero = 0 then 0 else ~~~0
  ((raw &&& ~~~subjectZero) ||| (subjectZero &&& zeroHit)) &&& subjectReal

abbrev SourceCache := Fin 4 → LoadedField

def cacheSource (keys : Keys) (real : Mask) : SourceCache :=
  loadField true keys real

/-- Retained-source branch: destination occupancy is supplied at this comparison,
while source registers and zero masks were loaded once. -/
def retainedMatch (source : SourceCache) (subject : Keys) (real : Mask) : Mask :=
  (List.finRange 4).foldl (fun acc f =>
    let other := loadField false subject real f
    acc &&& repair (allPairs (source f).regs other.regs)
      (source f).zero other.zero real) real

/-- WideSegmentMatchMask and its width-16 CrossBucketDuplicateMaskAt dispatch. -/
def wideMatch (source : Keys) (sourceReal : Mask) (subject : Keys)
    (subjectReal : Mask) : Mask :=
  (List.finRange 4).foldl (fun acc f =>
    let a := loadField true source sourceReal f
    let b := loadField false subject subjectReal f
    acc &&& repair (allPairs a.regs b.regs) a.zero b.zero subjectReal) subjectReal

/-- Sequential destination-mask writes. Repeated destination IDs represent
aliased mask pointers; every iteration reads the updated occupancy. The source
cache is immutable even if an ID also names its original occupancy location. -/
def clearDestinations (source : Keys) (sourceReal : Mask)
    (data : Nat → Keys) (destinations : List Nat) (masks : Nat → Mask) : Nat → Mask :=
  let cache := cacheSource source sourceReal
  destinations.foldl (fun state dst =>
    Function.update state dst (state dst &&& ~~~retainedMatch cache (data dst) (state dst))) masks

/-- Register-only masked moves into zero using the actual PEXT lane order. -/
def selectTier (regs : DRegisters) (tier : Mask) : DRegisters := fun j t =>
  if extractClass tier j t then regs j t else 0

/-- Shared transposes for one field, with the source/subject directions used
by CrossBucketClassFieldMasks<false>. -/
def classField (first : Keys) (firstReal : Mask) (second : Keys)
    (carry tier : Mask) (f : Fin 4) : Mask × Mask :=
  let a := loadField true first firstReal f
  let b := loadField false second (carry ||| tier) f
  (repair (allPairs (selectTier b.regs tier) a.regs)
     (b.zero &&& tier) a.zero firstReal,
   repair (allPairs a.regs b.regs) a.zero (b.zero &&& carry) carry)

/-- Both directions remain separate through all four segment ANDs. -/
def classMatch (first : Keys) (firstReal : Mask) (second : Keys)
    (carry tier : Mask) : Mask × Mask :=
  (List.finRange 4).foldl (fun acc f =>
    let hit := classField first firstReal second carry tier f
    (acc.1 &&& hit.1, acc.2 &&& hit.2)) (firstReal, carry)

/-- Real partners in physical slot order; repeated keys remain repeated. -/
def realKeys {Key : Type} (keys : Slot → Key) (real : Mask) : List Key :=
  ((List.finRange 64).filter fun i => real.getLsbD i.val).map keys

def logicalKeys (data : DirectMask64.Payload) : Slot → LogicalKey :=
  fun i => (data i.val).key

def storedKeys (stored : LogicalKey → Stored) (data : DirectMask64.Payload) : Keys :=
  fun i => stored (data i.val).key

end RebuildBound.Spec.NativeMatch.Lanes

namespace RebuildBound.Spec
open Model NativeNormalize NativeMatch NativeMatch.Lanes

/-- Packed low/high words use precisely the four little-endian dword fields. -/
def NativeMatchPackedWords_statement : Prop :=
  ∀ (lo hi : Word) (f : Fin 4),
    (keySegment (count := 4) (width := 32) (packWords lo hi) f).val =
      (if f.val < 2 then lo.val / 2 ^ (32 * f.val) % 2 ^ 32
       else hi.val / 2 ^ (32 * (f.val - 2)) % 2 ^ 32)

/-- Decode the real unpack network and both fixed-mask directions. -/
def NativeMatchUnpack_statement : Prop :=
  deposit (fun _ => true) = (0x000F000F000F000F : Mask) ∧
  (∀ (keys : Keys) (real : Mask) (zero : Bool) (f j : Fin 4) (t : Fin 16),
    (loadField zero keys real f).regs j t =
      if zero && !real.getLsbD (unpackSlot j t).val then 0
      else field keys f (unpackSlot j t)) ∧
  (∀ (real : Mask) (j : Fin 4) (t : Fin 16),
    extractClass real j t = real.getLsbD (unpackSlot j t).val) ∧
  (∀ (bits : Fin 16 → Bool) (j : Fin 4) (i : Slot),
    (placeMatches bits j).getLsbD i.val = true ↔
      ∃ t, unpackSlot j t = i ∧ bits t = true)

/-- Native output bits, after four independent zero repairs, are segment
membership in the real partner list. Neither the output nor its raw masks were
defined as segment membership. -/
def NativeMatchLanes_statement : Prop :=
  ∀ (source subject : Keys) (sourceReal subjectReal : Mask) (i : Slot),
    (wideMatch source sourceReal subject subjectReal).getLsbD i.val = true ↔
      subjectReal.getLsbD i.val = true ∧
        segMatch (count := 4) (width := 32) (subject i) (realKeys source sourceReal)

/-- Source-cache reuse has the same per-destination mask; sequential clears
preserve a fresh read of destination occupancy, including repeated IDs. -/
def NativeMatchRetained_statement : Prop :=
  (∀ (source subject : Keys) (sourceReal subjectReal : Mask),
    retainedMatch (cacheSource source sourceReal) subject subjectReal =
      wideMatch source sourceReal subject subjectReal) ∧
  (∀ (source : Keys) (sourceReal : Mask) (data : Nat → Keys)
    (destinations : List Nat) (masks : Nat → Mask),
    clearDestinations source sourceReal data destinations masks =
      destinations.foldl (fun state dst => Function.update state dst
        (state dst &&& ~~~wideMatch source sourceReal (data dst) (state dst))) masks)

/-- First subjects use only tier partners; carry subjects use only first
partners. This holds for arbitrary masks, hence also the disjoint native classes. -/
def NativeMatchClassLanes_statement : Prop :=
  ∀ (first second : Keys) (firstReal carry tier : Mask) (i : Slot),
    ((classMatch first firstReal second carry tier).1.getLsbD i.val = true ↔
      firstReal.getLsbD i.val = true ∧
        segMatch (count := 4) (width := 32) (first i) (realKeys second tier)) ∧
    ((classMatch first firstReal second carry tier).2.getLsbD i.val = true ↔
      carry.getLsbD i.val = true ∧
        segMatch (count := 4) (width := 32) (second i) (realKeys first firstReal))

/-- Conditional bridge to the existing pairwise exact logical duplicate-mask
model. The explicit segment mask stays separate until its bad events are excluded. -/
def NativeMatchLanesBridge_statement : Prop :=
  ∀ (stored : LogicalKey → Stored) (freshData olderData : DirectMask64.Payload)
    (freshReal olderReal : Mask),
    (∀ i : Slot, olderReal.getLsbD i.val = true →
      ¬ falseMatch (count := 4) (width := 32) stored
        ((olderData i.val).key, realKeys (logicalKeys freshData) freshReal)) →
    wideMatch (storedKeys stored freshData) freshReal (storedKeys stored olderData) olderReal =
      DirectMask64.duplicateMask (fun a b => a == b) freshData freshReal olderData olderReal

/-- Conditional agreement in both class directions, including their different
logical subjects and eligible source masks. -/
def NativeMatchClassBridge_statement : Prop :=
  ∀ (stored : LogicalKey → Stored) (firstData secondData : DirectMask64.Payload)
    (firstReal carry tier : Mask),
    (∀ i : Slot, firstReal.getLsbD i.val = true →
      ¬ falseMatch (count := 4) (width := 32) stored
        ((firstData i.val).key, realKeys (logicalKeys secondData) tier)) →
    (∀ i : Slot, carry.getLsbD i.val = true →
      ¬ falseMatch (count := 4) (width := 32) stored
        ((secondData i.val).key, realKeys (logicalKeys firstData) firstReal)) →
    classMatch (storedKeys stored firstData) firstReal (storedKeys stored secondData) carry tier =
      (DirectMask64.duplicateMask (fun a b => a == b) secondData tier firstData firstReal,
       DirectMask64.duplicateMask (fun a b => a == b) firstData firstReal secondData carry)

end RebuildBound.Spec
