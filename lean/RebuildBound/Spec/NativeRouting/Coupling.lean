import RebuildBound.Spec.NativeNormalize
import RebuildBound.Spec.NativeMatch
import RebuildBound.Spec.NativeRouting

/-! Finite causal routing coupling. The two memoized replays reuse
NativeNormalize.conversions. Reference routing has no normalization input;
both marginals and the normalization charge are on an unconditional product
experiment. Coordinates below instantiate complete native messages, including
separate unnormalized dummy tokens. Actual production chooser, finite used-key
coverage/count and compiled execution remain separate obligations. -/
namespace RebuildBound.Spec.NativeRoutingCoupling
open Model NativeNormalize MeasureTheory

abbrev ReplyChooser (bits : Nat) := Nat → List (Fingerprint bits) → Option LogicalKey

def chooseCoordinates {bits : Nat} (choose : ReplyChooser bits) : ConversionChooser bits :=
  fun n past => choose n (past.map Prod.snd)

def chooseReindexed {bits : Nat} (encode : LogicalKey → LogicalKey)
    (choose : ReplyChooser bits) : ConversionChooser bits :=
  fun n past => (choose n (past.map Prod.snd)).map encode

def mapHistory {bits : Nat} (encode : LogicalKey → LogicalKey)
    (history : List (LogicalKey × Fingerprint bits)) : List (LogicalKey × Fingerprint bits) :=
  history.map fun e => (encode e.1, e.2)

def badReindex {bits : Nat} (encode : LogicalKey → LogicalKey)
    (history : List (LogicalKey × Fingerprint bits)) : Prop :=
  ∃ a ∈ history, ∃ b ∈ history, a.1 ≠ b.1 ∧ encode a.1 = encode b.1

/-- Reference routing is a causal chooser over reply history, with no stored-key
parameter. Families/domains are part of its encoded logical coordinate. -/
def reference {Env : Type} {bits queries : Nat} (choose : Env → ReplyChooser bits)
    (p : Env × Answers bits queries) : List (LogicalKey × Fingerprint bits) :=
  conversions (chooseCoordinates (choose p.1)) p.2

/-- Same iid answer slots, but cached under stored-key routing coordinates. -/
def native {Env : Type} {bits normBits queries : Nat}
    (encode : Tape normBits → LogicalKey → LogicalKey) (choose : Env → ReplyChooser bits)
    (p : (Env × Answers bits queries) × Tape normBits) : List (LogicalKey × Fingerprint bits) :=
  conversions (chooseReindexed (encode p.2) (choose p.1.1)) p.1.2

namespace Coordinates
open NativeMatch NativeRouting

inductive Query where
  | real : Counter → Level → LogicalKey → Query
  | dummy : Counter → Level → Word → Query
  deriving DecidableEq

/-- Four qwords of the complete two-block routing message, in byte order. -/
def messageWords (m : Block × Block) : Fin 4 → Word := ![m.1.1, m.1.2, m.2.1, m.2.2]
def messageBytes (m : Block × Block) : LogicalKey :=
  List.ofFn (segments 32 8 ((segments 4 64).symm (messageWords m)))

def nativeMessage (stored : Tape 128) : Query → Block × Block
  | .real counter level key => message false counter level
      (keySegment (count := 2) (width := 64) (stored key) 0)
      (keySegment (count := 2) (width := 64) (stored key) 1)
  | .dummy counter level token => message true counter level token 0

def nativeCode (stored : Tape 128) (query : Query) : LogicalKey :=
  messageBytes (nativeMessage stored query)

/-- Logical coordinates retain the entire user key. Dummy coordinates contain
only their unchanged bounded token, under the native dummy domain. -/
def referenceCode : Query → LogicalKey
  | .real counter level key => messageBytes (message false counter level 0 0) ++ key
  | .dummy counter level token => messageBytes (message true counter level token 0)

def userKey : Query → Option LogicalKey
  | .real _ _ key => some key
  | .dummy _ _ _ => none

instance : Nonempty Query := ⟨.dummy 0 0 0⟩
noncomputable def decode : LogicalKey → Query := Function.invFun referenceCode
noncomputable def reindex (stored : Tape 128) (coordinate : LogicalKey) : LogicalKey :=
  nativeCode stored (decode coordinate)
noncomputable def project (coordinate : LogicalKey) : Option LogicalKey :=
  userKey (decode coordinate)

abbrev TypedChooser (bits : Nat) := Nat → List (Fingerprint bits) → Option Query

def codedChooser {bits : Nat} (choose : TypedChooser bits) : ReplyChooser bits :=
  fun n replies => (choose n replies).map referenceCode

end Coordinates
end RebuildBound.Spec.NativeRoutingCoupling

namespace RebuildBound.Spec
open Model NativeNormalize NativeRoutingCoupling MeasureTheory

local instance {bits : Nat} : MeasurableSpace (List (LogicalKey × Fingerprint bits)) := ⊤
local instance {bits : Nat} : DiscreteMeasurableSpace (List (LogicalKey × Fingerprint bits)) :=
  ⟨fun _ => trivial⟩

def NativeRoutingReindex_statement : Prop :=
  ∀ {bits : Nat} (encode : LogicalKey → LogicalKey)
    (choose : ReplyChooser bits) {queries : Nat} (answers : Answers bits queries)
    (_hno : ¬ badReindex encode (conversions (chooseCoordinates choose) answers)),
    conversions (chooseReindexed encode choose) answers =
      mapHistory encode (conversions (chooseCoordinates choose) answers)

def NativeRoutingReplay_statement : Prop :=
  ∀ {Env : Type} [MeasurableSpace Env]
    (μ : Measure Env) [IsProbabilityMeasure μ] (bits width queries : Nat)
    (choose : Env → ConversionChooser bits)
    (_hmeas : ∀ n past, Measurable (fun env => choose env n past))
    (_hwidth : ∀ env n past key, choose env n past = some key → key.length ≤ width),
    (μ.prod (tapeLaw bits)).map (fun p =>
      (p.1, conversions (choose p.1) (sample (paddedChooser width (choose p.1)) p.2 queries))) =
    (μ.prod (answerLaw bits queries)).map (fun p => (p.1, conversions (choose p.1) p.2))

def NativeRoutingNativeLaw_statement : Prop :=
  ∀ {Env : Type} [MeasurableSpace Env]
    (μ : Measure Env) [IsProbabilityMeasure μ] (bits normBits queries width : Nat)
    (choose : Env → ReplyChooser bits)
    (_hmeas : ∀ n replies, Measurable (fun env => choose env n replies))
    (encode : Tape normBits → LogicalKey → LogicalKey)
    (_hencode : ∀ key, Measurable (fun stored => encode stored key))
    (_hwidth : ∀ stored env n replies key, choose env n replies = some key →
      (encode stored key).length ≤ width),
    ((μ.prod (answerLaw bits queries)).prod (tapeLaw normBits)).map
      (fun p => ((p.1.1, p.2), native encode choose p)) =
    ((μ.prod (tapeLaw normBits)).prod (tapeLaw bits)).map (fun p =>
      (p.1, conversions (chooseReindexed (encode p.1.2) (choose p.1.1))
        (sample (paddedChooser width (chooseReindexed (encode p.1.2) (choose p.1.1)))
          p.2 queries)))

def NativeRoutingReferenceLaw_statement : Prop :=
  ∀ {Env : Type} [MeasurableSpace Env]
    (μ : Measure Env) [IsProbabilityMeasure μ] (bits normBits queries width : Nat)
    (choose : Env → ReplyChooser bits)
    (_hmeas : ∀ n replies, Measurable (fun env => choose env n replies))
    (_hwidth : ∀ env n replies key, choose env n replies = some key → key.length ≤ width),
    ((μ.prod (answerLaw bits queries)).prod (tapeLaw normBits)).map
      (fun p => ((p.1.1, reference choose p.1), p.2)) =
    ((μ.prod (tapeLaw bits)).map (fun p =>
      (p.1, conversions (chooseCoordinates (choose p.1))
        (sample (paddedChooser width (chooseCoordinates (choose p.1))) p.2 queries)))).prod
      (tapeLaw normBits)

def NativeRoutingCouplingBound_statement : Prop :=
  ∀ {Env : Type} [MeasurableSpace Env]
    (μ : Measure Env) [IsProbabilityMeasure μ] (bits normBits queries width budget : Nat)
    (choose : Env → ReplyChooser bits) (project : LogicalKey → Option LogicalKey)
    (encode : Tape normBits → LogicalKey → LogicalKey)
    (used : Env × Answers bits queries → List LogicalKey)
    (_hmeas : ∀ n : Nat, Measurable (fun p => (used p)[n]?))
    (_hwidth : ∀ p key, key ∈ used p → key.length ≤ width)
    (_hbudget : ∀ p, (used p).length ≤ budget)
    (_hcover : ∀ p e key, e ∈ reference choose p → project e.1 = some key → key ∈ used p)
    (_hencode : ∀ stored (p : Env × Answers bits queries) a, a ∈ reference choose p → ∀ b, b ∈ reference choose p →
      encode stored a.1 = encode stored b.1 → a.1 = b.1 ∨
        (∃ ka kb, project a.1 = some ka ∧ project b.1 = some kb ∧ ka ≠ kb ∧ stored ka = stored kb)),
    ((μ.prod (answerLaw bits queries)).prod (tapeLaw normBits))
      {p | native encode choose p ≠ mapHistory (encode p.2) (reference choose p.1)} ≤
        birthday normBits budget

open NativeRoutingCoupling.Coordinates NativeRouting

/-- Actual complete message serialization, reference-coordinate injectivity,
finite word/family fields, real/dummy separation and collision reflection.
Dummy tokens are never normalized. These are semantic codecs, not a proof of
C++ memory or compiled execution. -/
def NativeRoutingCoordinateEncoding_statement : Prop :=
  Function.Injective messageBytes ∧
  (∀ m, (messageBytes m).length = 32) ∧
  Function.Injective referenceCode ∧
  (∀ (q : Query), (∀ key, userKey q = some key → key.length ≤ 64) →
    (referenceCode q).length ≤ 96) ∧
  (∀ (stored : Tape 128) (q : Query), (nativeCode stored q).length = 32) ∧
  (∀ (stored : Tape 128) (a b : Query), nativeCode stored a = nativeCode stored b →
    a = b ∨ ∃ ka kb, userKey a = some ka ∧ userKey b = some kb ∧
      ka ≠ kb ∧ stored ka = stored kb) ∧
  (∀ (a b : Tape 128) (c : Counter) (l : Level) (w : Word),
    nativeCode a (.dummy c l w) = nativeCode b (.dummy c l w) ∧
      project (referenceCode (.dummy c l w)) = none) ∧
  (∀ key, Measurable (fun stored => reindex stored key))

/-- Widths above sixteen: actual native-message coordinate reindexing can
fail only on a collision between reference-used real keys. The chooser is
causal, normalization-independent, and permits repeats and unused slots.
Production finite key coverage and its lifetime count remain explicit. -/
def NativeRoutingFiniteCouplingBound_statement : Prop :=
  ∀ {Env : Type} [MeasurableSpace Env]
    (μ : Measure Env) [IsProbabilityMeasure μ] (queries budget : Nat)
    (choose : Env → TypedChooser 64) (used : Env × Answers 64 queries → List LogicalKey)
    (_hmeas : ∀ n : Nat, Measurable (fun p => (used p)[n]?))
    (_hwidth : ∀ p key, key ∈ used p → key.length ≤ 64)
    (_hbudget : ∀ p, (used p).length ≤ budget)
    (_hcover : ∀ p e key, e ∈ reference (fun env => codedChooser (choose env)) p →
      project e.1 = some key → key ∈ used p),
    ((μ.prod (answerLaw 64 queries)).prod (tapeLaw 128))
      {p | native reindex (fun env => codedChooser (choose env)) p ≠
        mapHistory (reindex p.2) (reference (fun env => codedChooser (choose env)) p.1)} ≤
      birthday 128 budget

/-- The byte-coded oracle has exactly the independent routing law on complete
native messages, and the reference code has exactly the independent law on
logical/dummy query coordinates. Both follow from the proved codec injections. -/
def NativeRoutingCoordinateLaw_statement : Prop :=
  (tapeLaw 64).map (fun tape m => tape (messageBytes m)) =
    Measure.infinitePi (fun _ : Block × Block => wordLaw 64) ∧
  (tapeLaw 64).map (fun tape q => tape (referenceCode q)) =
    Measure.infinitePi (fun _ : Query => wordLaw 64)

end RebuildBound.Spec
